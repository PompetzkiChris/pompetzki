from pathlib import Path
import csv
ROOT=Path(__file__).resolve().parents[1]
OLD=Path(r'C:\ClaudeOutput\pompetzki\release-1.0\book-master')
def rows(p):
    with p.open(encoding='utf-8',newline='') as f:return list(csv.reader((s for s in f if not s.startswith('#')),delimiter='\t'))
old=rows(OLD/'spot/PLAN-3.tsv');extra=rows(ROOT/'spot/PLAN-extra.tsv')
newpairs={r[0] for r in extra[1:] if r[0]!='SHIPPED'}
plan=old[:1]+[r for r in old[1:] if r[0]!=r'queue\CX-M3b\book' and r[0] not in newpairs]+[r for r in extra[1:] if r[0]!='SHIPPED']
with (ROOT/'spot/PLAN.tsv').open('x',encoding='utf-8',newline='') as f:
    csv.writer(f,delimiter='\t',lineterminator='\n').writerows(plan)
vs=[]
for p in [OLD/'spot/run-1-usable-VERDICTS.tsv',OLD/'spot/run-2/VERDICTS.tsv']:
    for r in rows(p):
        if r and r[0]=='V':vs.append(r)
latest={}
for r in vs:latest.setdefault(r[2],{})[r[4]]=r
good=[];rerun=[]
for sha,v in latest.items():
    if set(v)=={'pmp','racket'} and all(r[5] in {'ACCEPT','REJECT'} and r[6] in {'0','1'} for r in v.values()):good.extend(v.values())
    else:rerun.append(sha)
with (ROOT/'spot/PRIOR-VERDICTS.tsv').open('x',encoding='utf-8',newline='') as f:
    f.write('# Completed prior judge verdicts; interrupted process receipts excluded from reuse.\n')
    csv.writer(f,delimiter='\t',lineterminator='\n').writerows(good)
picked={r[7]:r for r in plan[1:] if r[3]!='0'}
remaining=[r for sha,r in picked.items() if sha not in {x[2] for x in good}]
print('Plan picks',len(plan)-1,'completed unique prior',len(good)//2,'remaining unique files',len(remaining))
print('Recorded total pmp milliseconds for remaining',sum(int(r[12]) for r in remaining))
for r in remaining:print(r[0],r[1],r[6],r[12])
