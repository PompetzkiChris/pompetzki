"""Package admitted Book data with portable aliases and reproducible hash receipts."""
from pathlib import Path
import csv, hashlib, json, re, shutil, subprocess, sys, zipfile

ROOT=Path(__file__).resolve().parents[1]
OLD=Path(r'C:\ClaudeOutput\pompetzki\release-1.0\book-master')
HANDIN=Path(r'C:\ClaudeOutput\pompetzki\release-1.0\handin')
PKG=ROOT/(sys.argv[1] if len(sys.argv)>1 else 'portable')/'Abschluss-1.2.1-book-master'
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def tsv(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.DictReader((s for s in f if not s.startswith('#')),delimiter='\t'))
def write_tsv(p,rows,fields):
    with p.open('x',encoding='utf-8',newline='') as f:
        w=csv.DictWriter(f,fields,delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
def records(p):
    with p.open(encoding='utf-8') as f:
        for line in f:yield line.rstrip('\n').split('\t')
def canon(p):return str(p).replace('\\','/').lower()
aliases={};copied={};hashes={};missing=[]
def add(path,kind,want=None):
    path=Path(path)
    if not path.is_file():missing.append({'path':str(path),'kind':kind,'reason':'path absent'});return None
    digest=sha(path)
    if want and digest!=want:raise ValueError(f'Changed bytes: {path}: {digest} != {want}')
    if digest not in copied:
        suffix=path.suffix.lower()
        if suffix not in {'.jdg','.txt','.tsv','.ledger','.json','.rkt','.pmp','.asm','.md','.csv'}:suffix='.txt'
        rel=f'{kind}/{digest}{suffix}'
        dest=PKG/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,dest)
        copied[digest]=rel;hashes[rel]=digest
    aliases[canon(path)]={'original':str(path),'portable':copied[digest],'sha256':digest,'kind':kind}
    return copied[digest]

def verify_seal(folder,manifest):
    out=[]
    for line in (folder/manifest).read_text(encoding='utf-8').splitlines():
        m=re.match(r'^([0-9a-f]{64})\s+\*?(.+)$',line)
        if not m:continue
        p=folder/m[2].removeprefix('./').replace('\\','/')
        actual=sha(p)
        if actual!=m[1]:raise ValueError(f'Seal mismatch: {p}')
        out.append({'manifest':str(folder/manifest),'file':str(p),'sha256':actual,'result':'PASS'})
    return out

PKG.mkdir(parents=True,exist_ok=False)
seal=[]
seal+=verify_seal(HANDIN/'queue/CX-M3b','SHA256SUMS-2.txt')
seal+=verify_seal(HANDIN/'queue/SETMM-out7b','sha256.txt')
write_tsv(PKG/'SOURCE-SEAL-CHECKS.tsv',seal,['manifest','file','sha256','result'])
print('Final source seal files',len(seal),flush=True)

# Copy only named journal, source, certificate and receipt records; task folders and transcripts are excluded.
for p in sorted((ROOT/'book').glob('J*.txt')):
    dest=PKG/'book'/p.name;dest.parent.mkdir(exist_ok=True);shutil.copyfile(p,dest)
for p in ROOT.glob('DUPLICATES*.tsv'):shutil.copyfile(p,PKG/p.name)
for p in ROOT.glob('CONFLICTS*.tsv'):shutil.copyfile(p,PKG/p.name)
for name in ['SPEC.md','BUILD.md','inventory.tsv','inventory-extra.tsv','EXCLUDED-SELECTION.tsv','MERGE-PLAN.tsv','chainverify.tsv','ORIGINAL-JOURNAL-SHA256.json','FINAL-RECEIPT-CHECKS.tsv']:
    shutil.copyfile(ROOT/name,PKG/name)
for folder in ['code','runs','spot']:
    dest=PKG/folder;dest.mkdir()
    for p in (ROOT/folder).rglob('*'):
        if p.is_file() and 'compiled' not in p.parts and '__pycache__' not in p.parts:
            q=dest/p.relative_to(ROOT/folder);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)

certs={};source_files=[];receipts=set();counts={};stmts=set();pairkeys=set();statuses={};chain_head=None
def request_payload(f,master):
    kind=f[0][0]
    if kind=='F':path=f[1][5:];digest=f[2][7:];size=int(f[3][6:]);receipt=f[16] if master else (f[16] if len(f)>17 else '')
    else:path=f[2][5:];digest=f[3][7:];size=int(f[4][6:]);receipt=f[9] if master else (f[9] if len(f)>10 else '')
    certs.setdefault(digest,{'originals':set(),'bytes':size,'kind':set()})
    certs[digest]['originals'].add(path);certs[digest]['kind'].add(kind)
    if receipt.startswith('receipt '):
        # Receipt values may carry several bound paths separated by typed hash annotations.
        text=receipt[8:]
        for m in re.finditer(r'[A-Za-z]:[\\/][^\t;|\r\n]+?\.(?:txt|tsv|ledger|json|out)(?=\s+(?:sha256|sha)\s|\s*[;|]|$)',text):receipts.add(m[0])

for p in sorted((ROOT/'book').glob('J*.txt')):
    for f in records(p):
        kind=f[0][0];counts[kind]=counts.get(kind,0)+1
        chain_head=f[-1]
        if kind=='H':
            for field in f[7:9]:
                m=re.match(r'^(?:book|negative) (.+) sha256 ([0-9a-f]{64}) head ',field)
                if m:source_files.append((Path(m[1]),m[2]))
                elif field.startswith('book ') and ' segments ' in field:
                    folder=field[5:].split(' segments ')[0]
                    for j in range(1,6):source_files.append((Path(folder)/'book'/f'J{j:06}.txt',None))
        elif kind=='B':
            stmts.add(f[5]);pairkeys.add((f[5],f[6]));statuses[f[4]]=statuses.get(f[4],0)+1
        elif kind in 'FNS':request_payload(f,True)

sources_seen=set()
for p,digest in source_files:
    if canon(p) in sources_seen:continue
    sources_seen.add(canon(p));add(p,'sources',digest)
    for f in records(p):
        if f[0][0] in 'FNS':request_payload(f,False)

# Existing R13 hand-ins sometimes retain their original path. Locate the exact admitted bytes by SHA.
candidate_index=None
def locate(data,digest):
    global candidate_index
    for name in data['originals']:
        p=Path(name)
        if p.is_file() and p.stat().st_size==data['bytes'] and sha(p)==digest:return p
    if candidate_index is None:
        candidate_index={}
        for folder in [HANDIN,OLD/'r13-fetch']:
            for p in folder.rglob('*.jdg'):candidate_index.setdefault(p.name.lower(),[]).append(p)
    for name in data['originals']:
        for p in candidate_index.get(Path(name).name.lower(),[]):
            if p.stat().st_size==data['bytes'] and sha(p)==digest:return p
    return None

payload_rows=[];payload_gaps=[];total=0
for i,(digest,data) in enumerate(certs.items(),1):
    found=locate(data,digest)
    if found is None:
        if data['kind']!={'S'}:raise ValueError(f'Admitted certificate SHA absent: {digest}: {data}')
        for name in sorted(data['originals']):
            p=Path(name)
            payload_gaps.append({'kind':'S','original':name,'expected_sha256':digest,'expected_bytes':data['bytes'],'observed_sha256':sha(p) if p.is_file() else '-','observed_bytes':p.stat().st_size if p.is_file() else '-','status':'historical suspense payload not matched'})
        continue
    rel=add(found,'certificates',digest);total+=data['bytes']
    for name in data['originals']:aliases[canon(name)]={'original':name,'portable':rel,'sha256':digest,'kind':'certificates'}
    payload_rows.append({'sha256':digest,'bytes':data['bytes'],'kinds':','.join(sorted(data['kind'])),'portable':rel})
    if i%100==0:print('Payloads copied',i,'bytes',total,flush=True)
write_tsv(PKG/'CERTIFICATES.tsv',payload_rows,['sha256','bytes','kinds','portable'])
write_tsv(PKG/'CERTIFICATE-PAYLOAD-GAPS.tsv',payload_gaps,['kind','original','expected_sha256','expected_bytes','observed_sha256','observed_bytes','status'])

receipt_resolutions=[]
for p in sorted(receipts):
    path=Path(p)
    # Historical ledgers can name a composite receipt filename; retain that string
    # and bind the two actual judge output files beside it without inventing its bytes.
    if not path.is_file() and path.parent.name=='verdicts':
        actual=[path.with_name(path.stem+'-pmp.txt'),path.with_name(path.stem+'-rkt.txt')]
        if all(x.is_file() for x in actual):
            for x in actual:
                rel=add(x,'receipts')
                receipt_resolutions.append({'historical_reference':p,'actual_receipt':str(x),'portable':rel,'sha256':sha(x),'reason':'Historical composite filename resolves to separate judge output files.'})
            continue
    add(p,'receipts')
write_tsv(PKG/'RECEIPT-RESOLUTIONS.tsv',receipt_resolutions,['historical_reference','actual_receipt','portable','sha256','reason'])
# Bind full final source receipt summaries and source seals, including their direct judge output paths.
for p in [HANDIN/'queue/CX-M3b/STATUS-2.txt',HANDIN/'queue/CX-M3b/SHA256SUMS-2.txt',HANDIN/'queue/CX-M3b/book2/RECEIPTS-CX-M3b-01.tsv',HANDIN/'queue/CX-M3b/merged1/RESULTS1.tsv',HANDIN/'queue/CX-M3b/combined3/pairs.tsv',HANDIN/'queue/SETMM-out7b/STATUS.txt',HANDIN/'queue/SETMM-out7b/sha256.txt',HANDIN/'queue/SETMM-out7b/run/RECEIPTS.tsv',HANDIN/'queue/SETMM-out7b/run/judge-run-0033-12.tsv',HANDIN/'queue/SETMM-out7b/run/countcheck.txt']:
    add(p,'receipts')
for p in [HANDIN/'queue/CX-M3b/book2/RECEIPTS-CX-M3b-01.tsv']:
    for line in p.read_text(encoding='utf-8').splitlines():
        for m in re.finditer(r'([A-Za-z]:[\\/][^\t;\r\n]+?\.(?:txt|tsv|ledger|json)) sha256 ([0-9a-f]{64})',line):add(m[1],'receipts',m[2])
write_tsv(PKG/'PATH-ALIASES.tsv',list(aliases.values()),['original','portable','sha256','kind'])
write_tsv(PKG/'RECEIPT-PATH-GAPS.tsv',missing,['path','kind','reason'])

wrapper='''\n(require (file "portable-paths.rkt")\n         (only-in racket/base [call-with-input-file native-call-with-input-file]\n                  [open-input-file native-open-input-file]\n                  [file-exists? native-file-exists?] [file-size native-file-size]))\n(define (call-with-input-file p proc) (native-call-with-input-file (portable-path p) proc))\n(define (open-input-file p) (native-open-input-file (portable-path p)))\n(define (file-exists? p) (native-file-exists? (portable-path p)))\n(define (file-size p) (native-file-size (portable-path p)))\n'''
for filename in ['master-verify.rkt','master-verify-indep.rkt']:
    source=(ROOT/'code'/filename).read_text(encoding='utf-8')
    source=source.replace('#lang racket/base','#lang racket/base'+wrapper,1)
    (PKG/'code'/filename.replace('.rkt','-portable.rkt')).write_text(source,encoding='utf-8')

indexsource=(HANDIN/'queue/Q89/book-index.rkt').read_text(encoding='utf-8')
indexwrapper=wrapper+'\n(require (only-in racket/file [file->bytes native-file->bytes]))\n(define (file->bytes p) (native-file->bytes (portable-path p)))\n'
(PKG/'code/book-index-portable.rkt').write_text(indexsource.replace('#lang racket/base','#lang racket/base'+indexwrapper,1),encoding='utf-8')
shutil.copyfile(HANDIN/'queue/Q30/book-html.rkt',PKG/'code/book-html.rkt')
racket=r'C:\Program Files\Racket\racket.exe'
for args in [[racket,str(PKG/'code/book-index-portable.rkt'),str(PKG),str(PKG)],[racket,str(PKG/'code/book-html.rkt'),str(PKG),str(PKG/'html')]]:
    run=subprocess.run(args,capture_output=True,text=True,encoding='utf-8')
    print(run.stdout,flush=True)
    if run.returncode:raise ValueError(run.stderr or run.stdout)
    with (PKG/'runs/RENDER-BOOK.txt').open('a',encoding='utf-8') as f:f.write(' '.join(args)+'\n'+run.stdout+run.stderr+f'exit {run.returncode}\n')

duplicates={}
for p in ROOT.glob('DUPLICATES*.tsv'):
    for row in tsv(p):duplicates[row['kind']]=duplicates.get(row['kind'],0)+1
summary={'journal_records':counts,'posting_status':statuses,'distinct_statements':len(stmts),'distinct_statement_derivation_pairs':len(pairkeys),'duplicate_source_records':duplicates,'chain_head':chain_head,'original_segments_retained':33,'unique_certificate_payloads':len(payload_rows),'certificate_payload_bytes':total,'historical_suspense_payload_gaps':len(payload_gaps),'source_ledgers_and_shipped_segments':len(sources_seen),'receipt_path_gaps':len(missing)}
(PKG/'COUNTS.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary,indent=2),flush=True)
(PKG/'PAYLOAD-BOUNDARIES.md').write_text(f'''# Payload boundaries\n\nAll admitted F and N certificate payloads are bundled and checked against their recorded SHA-256 hashes and byte counts. Historical journal bytes, including the 17 suspense records, remain unchanged.\n\nCERTIFICATE-PAYLOAD-GAPS.tsv contains {len(payload_gaps)} historical suspense payload gap. The checked `lanes\\L6\\notes\\test-core.jdg` paths carried 305,155 bytes with SHA-256 `960bcdabca97ab9f84181f0b27a9fb8a63d01173f83d043269eacbf30c223314`; S's recorded payload is 369,409 bytes with SHA-256 `f33891de962998142bc3e74c283bc94bd6fe8c890d7df4342eaf97b20ccd96fd`. The S record and its source record remain in the journal and bundled source.\n\nRECEIPT-PATH-GAPS.tsv contains {len(missing)} unresolved historical receipt paths. RECEIPT-RESOLUTIONS.tsv binds Q96's historical composite receipt names to the separate pmp and Racket judge output files that were checked and bundled. The completed bounded rechecks are also bundled in spot/.\n''',encoding='utf-8')
(PKG/'README.md').write_text('''# Abschluss 1.2.1 master Book\n\nOpen search.html to search rendered theorem statements and hash prefixes. html/index.html gives the static Book view.\n\nThis archive retains journal segments J000001-J000033 byte for byte and appends the newly admitted segments. Historical absolute paths remain in the records. PATH-ALIASES.tsv maps them to bundled source ledgers, certificates and receipts.\n\nRun `python code/verify-portable.py .` to verify the full manifest, journal chain and admitted certificate payloads. With Racket installed, run `racket code/master-verify-portable.rkt .` and `racket code/master-verify-indep-portable.rkt .` for the two source-record checks. They use the bundled aliases on Windows and Linux.\n\nCOUNTS.json separates postings from distinct statement hashes. Proved and Qualified remain separate. Duplicate source postings remain in their bundled source ledgers and DUPLICATES tables; distinct derivations of one statement remain separate master postings. No GUI acceptance claim is made by this Book archive.\n\nMERGE-PLAN.tsv lists each held ledger and its reason. The bounded spot checks sample two records per ledger kind, reuse completed prior judge receipts, and rerun interrupted controls. SOURCE-SEAL-CHECKS.tsv checks the final CX-M3b and SETMM-out7b source seals. RECEIPT-PATH-GAPS.tsv records any historical receipt path not resolved while packaging.\n''',encoding='utf-8')
files=sorted(p for p in PKG.rglob('*') if p.is_file())
with (PKG/'SHA256SUMS.txt').open('x',encoding='utf-8') as f:
    for p in files:f.write(f'{sha(p)} *{p.relative_to(PKG).as_posix()}\n')
archive=ROOT/(sys.argv[2] if len(sys.argv)>2 else 'Abschluss-1.2.1-book-master.zip')
archive.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as z:
    for p in sorted(PKG.rglob('*')):
        if p.is_file():z.write(p,p.relative_to(PKG.parent).as_posix())
archive.with_suffix(archive.suffix+'.sha256').write_text(f'{sha(archive)} *{archive.name}\n',encoding='utf-8')
print('Archive',archive,'bytes',archive.stat().st_size,flush=True)
