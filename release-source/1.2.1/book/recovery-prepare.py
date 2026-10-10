"""Prepare fresh Book selection while retaining the earlier journal and decisions."""
from pathlib import Path
import csv, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
OLD=Path(r'C:\ClaudeOutput\pompetzki\release-1.0\book-master')
def read_tsv(p):
    with p.open(encoding='utf-8', newline='') as f:
        return list(csv.DictReader((s for s in f if not s.startswith('#')),delimiter='\t'))
def write_tsv(p,rows,fields):
    with p.open('x',encoding='utf-8',newline='') as f:
        w=csv.DictWriter(f,fields,delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
allrows=read_tsv(ROOT/'inventory-all.tsv')
excluded=[];selected=[]
for row in allrows:
    if row['pair']==r'queue\CX-M3b\book':
        excluded.append(dict(row,reason='Final sealed book2 replaces preliminary 308-posting pair in this continuation.'))
    else:selected.append(row)
write_tsv(ROOT/'inventory.tsv',selected,list(allrows[0]))
write_tsv(ROOT/'EXCLUDED-SELECTION.tsv',excluded,list(allrows[0])+['reason'])
old=read_tsv(OLD/'inventory.tsv')
oldbytes={(r['pair'],r['book_sha256'],r['neg_sha256']) for r in old}
fresh=[r for r in selected if (r['pair'],r['book_sha256'],r['neg_sha256']) not in oldbytes]
write_tsv(ROOT/'inventory-extra.tsv',fresh,list(allrows[0]))
originals={p.name:sha(p) for p in (OLD/'book').glob('J*.txt')}
(ROOT/'ORIGINAL-JOURNAL-SHA256.json').write_text(json.dumps(originals,indent=2)+'\n',encoding='utf-8')
print('Selected pairs',len(selected),'new or changed',len(fresh),'excluded',len(excluded))
for r in fresh:print(r['pair'])
