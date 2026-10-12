#!/usr/bin/env python3
"""Independent matrix batch harness. Exact Fraction oracle; no floats."""
import json, subprocess, sys
from pathlib import Path
from fractions import Fraction
from itertools import permutations
OUT=Path(sys.argv[1]); RAW=OUT/'raw'; IN=OUT/'inputs'; RAW.mkdir(parents=True,exist_ok=True); IN.mkdir(parents=True,exist_ok=True)
SRC=Path(sys.argv[2])
ENG={'corrected':['racket',str(SRC/'math-workbench-corrected/engine.rkt')],'v2-racket':['racket',str(SRC/'math-workbench-v2/engine.rkt')]}
if len(sys.argv)>3 and Path(sys.argv[3]).exists(): ENG['v2-compiled']=[sys.argv[3]]
def P(t): return [[Fraction(x.strip()) for x in r.split(',')] for r in t.strip()[1:-1].split(';')]
def S(M): return [[str(x) for x in r] for r in M]
def det(A):
    n=len(A); s=Fraction(0)
    for p in permutations(range(n)):
        inv=sum(1 for i in range(n) for j in range(i+1,n) if p[i]>p[j]); pr=Fraction(1)
        for i in range(n): pr*=A[i][p[i]]
        s+=pr if inv%2==0 else -pr
    return s
def rref(A):
    M=[r[:] for r in A]; R,C=len(M),len(M[0]); r=0
    for c in range(C):
        pv=next((i for i in range(r,R) if M[i][c]!=0),None)
        if pv is None: continue
        M[r],M[pv]=M[pv],M[r]; v=M[r][c]; M[r]=[x/v for x in M[r]]
        for i in range(R):
            if i!=r: f=M[i][c]; M[i]=[M[i][j]-f*M[r][j] for j in range(C)]
        r+=1
        if r==R: break
    return M
def oracle(op,a,b):
    A=P(a)
    if op=='det': return str(det(A))
    if op=='transpose': return S([list(c) for c in zip(*A)])
    if op=='mul': B=P(b); return S([[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))])
    if op=='rref': return S(rref(A))
    if op=='inv':
        n=len(A); R=rref([A[i]+[Fraction(int(i==j)) for j in range(n)] for i in range(n)]); return S([r[n:] for r in R])
    if op=='solve':
        B=P(b); n=len(A[0]); R=rref([A[i]+B[i] for i in range(len(A))]); x=[Fraction(0)]*n
        for r in R:
            nz=[j for j in range(n) if r[j]!=0]
            if nz: x[nz[0]]=r[n]
        return [str(v) for v in x]
def flat(v):
    # collect all rational strings in machine output for order-insensitive structural comparison
    out=[]
    if isinstance(v,dict):
        for k in sorted(v): out+=flat(v[k])
    elif isinstance(v,list):
        for x in v: out+=flat(x)
    elif isinstance(v,str): out.append(v)
    return out
def run(eng,name,content):
    p=IN/(name+'.json'); p.write_text(content if isinstance(content,str) else json.dumps(content))
    r=subprocess.run([*eng,'--batch',str(p)],capture_output=True,timeout=120)
    for s,b in (('stdout',r.stdout),('stderr',r.stderr)): (RAW/f'{name}.{s}').write_bytes(b)
    (RAW/f'{name}.exit').write_text(f'{r.returncode}\n'); return r
rows=[]
def rec(c,cmd,o,v): rows.append(dict(claim=c,command=cmd,output=o,outcome=v)); print(v,'|',c,'|',o[:200])
bad=[None,7,'bad',[],{},{'id':'missing-op','a':'[1]'},{'id':'missing-a','op':'det'},{'id':'unknown-op','op':'frobnicate','a':'[1]'},
     {'id':'wrong-dims','op':'mul','a':'[1,2]','b':'[1,2]'},{'id':'non-rational','op':'det','a':'[1.5]'},{'id':'numeric-a','op':'det','a':3}]
valid=[{'id':'det','op':'det','a':'[1,2;3,4]'},{'id':'det3','op':'det','a':'[2,1/3,0;1,1,1;0,5/7,3]'},
       {'id':'transpose','op':'transpose','a':'[1,2,3;4,5,6]'},{'id':'mul','op':'mul','a':'[1,2;3,4]','b':'[1/2,0;0,1/3]'},
       {'id':'rref','op':'rref','a':'[1,2,3;2,4,7]'},{'id':'inv','op':'inv','a':'[2,1;1,1]'},{'id':'solve','op':'solve','a':'[2,1;1,3]','b':'[3;5]'}]
mixed=[]
for i,v in enumerate(valid): mixed.append(v); mixed.append(bad[i%len(bad)])
mixed+=bad[len(valid):]
for label,eng in ENG.items():
    cmd=' '.join(eng)+' --batch'
    r=run(eng,f'{label}-mixed',mixed)
    if r.returncode!=0:
        rec(f'{label}: mixed valid+malformed batch','%s mixed.json'%cmd,f'exit={r.returncode} stdout={len(r.stdout)}B stderr={r.stderr.decode(errors="replace").strip()[:150]}',
            'WHOLE-BATCH FAILURE (defect)' if label=='corrected' else 'FAIL'); 
    else:
        data=json.loads(r.stdout); fails=[]
        if len(data)!=len(mixed): fails.append(f'len {len(data)}!={len(mixed)}')
        for job,d in zip(mixed,data):
            if job in valid:
                exp=oracle(job['op'],job['a'],job.get('b')); got=flat(d.get('machine',{}))
                expf=exp if isinstance(exp,str) else flat(exp)
                expl=[expf] if isinstance(expf,str) else expf
                if d.get('exit')!=0 or not all(x in got for x in expl): fails.append(f"{job['id']}: exp {expl} got {d.get('machine')}")
            else:
                eid=job.get('id') if isinstance(job,dict) else None
                if not(d.get('exit')==1 and d.get('id')==eid and d['machine'].get('status')=='rejected' and d['machine'].get('reason')): fails.append(f'bad {eid}: {d}')
        rec(f'{label}: mixed batch ({len(valid)} valid / {len(mixed)-len(valid)} malformed) per-item records + Fraction oracle',f'{cmd} mixed.json',
            f'exit=0 n={len(data)} '+('all exact/rejected as expected' if not fails else '; '.join(fails)[:400]),'PASS' if not fails else 'FAIL')
    r=run(eng,f'{label}-empty',[])
    rec(f'{label}: empty batch',f'{cmd} []',f'exit={r.returncode} out={r.stdout.strip()[:40]!r}','PASS' if r.returncode==0 and json.loads(r.stdout or b'null')==[] else 'FAIL')
    r=run(eng,f'{label}-allbad',bad)
    if r.returncode==0:
        d=json.loads(r.stdout); ok=len(d)==len(bad) and all(x['exit']==1 and x['machine']['status']=='rejected' for x in d)
        rec(f'{label}: all-malformed batch',f'{cmd} allbad.json',f'exit=0 n={len(d)} all rejected={ok}','PASS' if ok else 'FAIL')
    else: rec(f'{label}: all-malformed batch',f'{cmd} allbad.json',f'exit={r.returncode} {r.stderr.decode(errors="replace").strip()[:150]}','WHOLE-BATCH FAILURE (defect)' if label=='corrected' else 'FAIL')
(RAW/'rows.json').write_text(json.dumps(rows,indent=1))
