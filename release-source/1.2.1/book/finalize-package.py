"""Complete composite receipt bindings in a new copy of the rendered package."""
from pathlib import Path
import csv, hashlib, json, shutil, sys, zipfile
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'portable-3/Abschluss-1.2.1-book-master'
DEST=ROOT/'portable-final/Abschluss-1.2.1-book-master'
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def rows(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader(f,delimiter='\t'))
def write(p,data,fields):
    with p.open('w',encoding='utf-8',newline='') as f:
        w=csv.DictWriter(f,fields,delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(data)
shutil.copytree(SRC,DEST)
aliases=rows(DEST/'PATH-ALIASES.tsv');gaps=rows(DEST/'RECEIPT-PATH-GAPS.tsv');resolved=rows(DEST/'RECEIPT-RESOLUTIONS.tsv');remaining=[]
for row in gaps:
    p=Path(row['path'])
    pair=[p.with_name(p.stem+'-pmp.txt'),p.with_name(p.stem+'-rkt.txt')]
    if p.parent.name=='verdicts' and all(x.is_file() for x in pair):
        for x in pair:
            digest=sha(x);rel=f'receipts/{digest}.txt';dest=DEST/rel
            if not dest.exists():shutil.copyfile(x,dest)
            aliases.append({'original':str(x),'portable':rel,'sha256':digest,'kind':'receipts'})
            resolved.append({'historical_reference':str(p),'actual_receipt':str(x),'portable':rel,'sha256':digest,'reason':'Historical composite filename resolves to separate judge output files.'})
    else:remaining.append(row)
assert not remaining,remaining
write(DEST/'PATH-ALIASES.tsv',aliases,['original','portable','sha256','kind'])
write(DEST/'RECEIPT-PATH-GAPS.tsv',remaining,['path','kind','reason'])
write(DEST/'RECEIPT-RESOLUTIONS.tsv',resolved,['historical_reference','actual_receipt','portable','sha256','reason'])
counts=json.loads((DEST/'COUNTS.json').read_text(encoding='utf-8'));counts['receipt_path_gaps']=len(remaining);counts['composite_receipt_references_resolved']=len({r['historical_reference'] for r in resolved})
(DEST/'COUNTS.json').write_text(json.dumps(counts,indent=2)+'\n',encoding='utf-8')
boundary=DEST/'PAYLOAD-BOUNDARIES.md'
if boundary.exists():boundary.write_text(boundary.read_text(encoding='utf-8').replace('contains 3 unresolved historical receipt paths','contains 0 unresolved historical receipt paths').replace("Q96's historical composite receipt names","Q96 and Q114 historical composite receipt names"),encoding='utf-8')
for p in (ROOT/'code').glob('*'):
    if p.is_file():shutil.copyfile(p,DEST/'code'/p.name)
(DEST/'BUILD-CORRECTION.md').write_text('''# Receipt binding correction\n\nThe rendered predecessor is retained in portable-3. This new directory resolves Q114's three historical composite receipt filenames to the six existing separate judge output files. Q96's two historical composite names remain bound to four separate output files. Historical ledger and journal strings remain unchanged. All admitted certificate payloads and all 33 retained original journal segments keep their predecessor SHA-256 hashes.\n\nThis directory also carries the final packaging and independent payload-verification scripts. Its SHA256SUMS.txt and archive checksum were generated after these changes.\n''',encoding='utf-8')
with (DEST/'SHA256SUMS.txt').open('w',encoding='utf-8') as f:
    for p in sorted(DEST.rglob('*')):
        if p.is_file() and p.name!='SHA256SUMS.txt':f.write(f'{sha(p)} *{p.relative_to(DEST).as_posix()}\n')
archive=ROOT/'final-dist/Abschluss-1.2.1-book-master.zip';archive.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as z:
    for p in sorted(DEST.rglob('*')):
        if p.is_file():z.write(p,p.relative_to(DEST.parent).as_posix())
archive.with_suffix('.zip.sha256').write_text(f'{sha(archive)} *{archive.name}\n',encoding='utf-8')
print(json.dumps(counts,indent=2));print('FINAL ARCHIVE',archive,'bytes',archive.stat().st_size)
