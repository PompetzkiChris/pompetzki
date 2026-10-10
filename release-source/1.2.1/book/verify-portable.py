"""Independently verify manifest, journal chain, counters and certificate bytes."""
from pathlib import Path
import csv, hashlib, json, re, sys
root=Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parents[1]).resolve()
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
manifest=0
for line in (root/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    digest,name=line.split(' *',1)
    path=root/name
    if not path.resolve().is_relative_to(root):raise ValueError('Manifest leaves archive root')
    assert sha(path)==digest,('manifest mismatch',name)
    manifest+=1
original=json.loads((root/'ORIGINAL-JOURNAL-SHA256.json').read_text(encoding='utf-8'))
for name,digest in original.items():assert sha(root/'book'/name)==digest,('original segment changed',name)
head='0'*64;counts={};stmts=set();pairs=set();prev=None;record_count=0;required_payloads={}
for sn,p in enumerate(sorted((root/'book').glob('J*.txt')),1):
    assert p.name==f'J{sn:06}.txt'
    raw=p.read_bytes();assert raw.endswith(b'\n') and b'\r' not in raw
    segment_counts={};lines=raw.splitlines()
    for i,line in enumerate(lines):
        body,digest=line.rsplit(b'\t',1)
        head=hashlib.sha256(head.encode()+b'\n'+body).hexdigest()
        assert head.encode()==digest,('chain mismatch',p.name,i+1)
        f=body.decode('utf-8').split('\t');kind=f[0][0]
        counts[kind]=counts.get(kind,0)+1;segment_counts[kind]=segment_counts.get(kind,0)+1
        width=7 if kind=='B' else 6
        assert f[0]==kind+str(counts[kind]).zfill(width),('ID mismatch',f[0])
        if i==0:
            assert kind=='H'
            expected='previous - -' if prev is None else f'previous book/{prev.name} {sha(prev)}'
            assert f[2]==expected,('segment link',p.name)
        if kind=='B':
            assert f[17].startswith('pmp ACCEPT ') and f[18].startswith('racket ACCEPT ')
            assert (f[4]=='Proved')==(f[8]=='hyps -'),('status',f[0])
            key=(f[5],f[6]);assert key not in pairs,('duplicate master pair',f[0]);pairs.add(key);stmts.add(f[5])
        elif kind=='F':
            assert f[8].startswith('pmp ACCEPT ') and f[9].startswith('racket ACCEPT ')
            required_payloads[f[2][7:]]=int(f[3][6:])
        elif kind=='N':
            assert f[6].startswith('pmp REJECT ') and f[7].startswith('racket REJECT ')
            required_payloads[f[3][7:]]=int(f[4][6:])
        if i==len(lines)-1:assert kind=='E' and int(f[2][8:])==len(lines)-1
        record_count+=1
    prev=p
payloads=0;total=0;bundled={}
with (root/'CERTIFICATES.tsv').open(encoding='utf-8',newline='') as f:
    for row in csv.DictReader(f,delimiter='\t'):
        p=root/row['portable'];assert p.stat().st_size==int(row['bytes']);assert sha(p)==row['sha256']
        payloads+=1;total+=int(row['bytes']);bundled[row['sha256']]=int(row['bytes'])
for digest,size in required_payloads.items():assert bundled.get(digest)==size,('admitted payload not bundled',digest)
with (root/'PATH-ALIASES.tsv').open(encoding='utf-8',newline='') as f:
    for row in csv.DictReader(f,delimiter='\t'):assert sha(root/row['portable'])==row['sha256']
print(json.dumps({'manifest_files':manifest,'original_segments_unchanged':len(original),'journal_records':record_count,'counts':counts,'distinct_statements':len(stmts),'distinct_pairs':len(pairs),'chain_head':head,'certificate_payloads':payloads,'certificate_bytes':total},indent=2))
print('PORTABLE CHECK OK')
