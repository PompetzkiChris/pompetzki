from pathlib import Path
import csv, hashlib, re
ROOT=Path(__file__).resolve().parents[1]
Q=Path(r'C:\ClaudeOutput\pompetzki\release-1.0\handin\queue')
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
result=[]
for name,path in [('CX-M3b',Q/'CX-M3b/book2/RECEIPTS-CX-M3b-01.tsv'),('SETMM-out7b',Q/'SETMM-out7b/run/RECEIPTS.tsv')]:
    accepted=0;rejected=0;postings=0
    with path.open(encoding='utf-8',newline='') as f:
        for row in csv.reader(f,delimiter='\t'):
            if row[0] in {'file','path'}:continue
            assert len(row)==15,(name,len(row))
            assert row[1]==row[2] and row[1] in {'ACCEPT','REJECT'},row
            expected='0' if row[1]=='ACCEPT' else '1'
            assert row[5]==row[10]==expected,row
            assert row[9].startswith(row[1]) and row[14].startswith(row[1]),row
            assert sha(Path(row[0]))==row[4],row[0]
            if expected=='0':
                pmp=[int(n) for n in re.findall(r'\d+',row[9])]
                rkt=[int(n) for n in re.findall(r'\d+',row[14])]
                assert len(pmp)==len(rkt)==4 and pmp==rkt,(name,pmp,rkt)
                assert pmp[0]+pmp[1]==pmp[3]
                accepted+=1;postings+=pmp[1]
            else:rejected+=1
            result.append({'batch':name,'file':row[0],'sha256':row[4],'pmp':row[1],'racket':row[2],'exit':expected,'result':'PASS'})
    print(name,'accepted',accepted,'postings',postings,'rejected',rejected)
    if name=='CX-M3b':assert (accepted,postings,rejected)==(40,3356,40)
    else:assert (accepted,postings,rejected)==(9,55938,68)
out=ROOT/'FINAL-RECEIPT-CHECKS.tsv'
with out.open('x',encoding='utf-8',newline='') as f:
    w=csv.DictWriter(f,list(result[0]),delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(result)
print('FINAL RECEIPT CHECK OK',len(result))
