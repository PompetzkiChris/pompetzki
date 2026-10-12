#!/usr/bin/env python3
"""Independent judge resource/numeric attack harness. Each child: prlimit AS 2GiB, CPU 60s, timeout 90s."""
import subprocess, sys, json, re
from pathlib import Path
O=Path(sys.argv[1]); IN=O/'inputs'; RAW=O/'raw'/'res'; IN.mkdir(parents=True,exist_ok=True); RAW.mkdir(parents=True,exist_ok=True)
J=Path('/workspace/acct-5c0d/judge'); RT='/workspace/acct-v130/build-rt/pompetzki'
ROUTES={'v6-native':['/workspace/acct-5c0d-build/judge-v6-linux'],'v6-interp':[RT,str(J/'judge-v6.pmp')],'v6-racket':['racket',str(J/'judge-v6.rkt')],
        'v5-native':['/workspace/acct-v130/build-jn/judge-v5-linux'],'v5-interp':[RT,str(J/'judge-v5.pmp')],'v5-racket':['racket',str(J/'judge-v5.rkt')]}
ok=(J/'mut/ok-hyp.jdg').read_bytes()
i=ok.index(b'\nT 1\n'); head=ok[:i+3]; thm=b'a a i k p 671 2 1 2 p 671 2 0 2 q 1 0 1 0 1 U 699 1 0 1 22 \n'
assert ok[i+5:].strip()==thm.strip(), ok[i+5:]
canon=(J/'REG0-canonical.jdg').read_bytes()
C={}
C['ctl-ok-hyp']=ok
C['ctl-canonical-reg0']=canon
C['ctl-false-registry']=b'JDG1\nR 1\na n q 0 0 0\nT 0\n'
C['num-pad1024-T']=head+b'0'*1024+b'1\n'+thm
C['num-12sig-T']=head+b'999999999999\n'+thm
C['num-13sig-T']=head+b'1000000000000\n'+thm
C['num-pad-then-12sig-T']=head+b'0'*40+b'999999999999\n'+thm
C['huge-T']=head+b'999999999999\n'+thm
C['huge-T-empty']=head+b'999999999999\n'
C['huge-steps']=head+b'1\n'+thm.replace(b'q 1 0 1 0 1 U',b'q 1 0 1 0 999999999999 U')
C['huge-sig']=head+b'1\n'+thm.replace(b'q 1 0 1 0 1 U',b'q 1 0 999999999999 0 1 U')
C['huge-hyps']=head+b'1\n'+thm.replace(b'U 699 1 0 1 22',b'U 699 1 0 999999999999 22')
C['huge-step-list']=head+b'1\n'+thm.replace(b'U 699 1 0 1 22',b'U 699 999999999999 0 1 22')
C['trunc-mid-theorem']=head+b'1\n'+thm[:30]
C['trunc-after-T']=head
C['trunc-mid-registry']=ok[:len(ok)//2]
for name,k in (('T-eq-rem',0),('T-rem-minus1',-1),('T-rem-plus1',1)):
    body=b'\n'+thm; rem=len(body); C[name]=head+str(rem+k).encode()+body
for name,k in (('steps-eq-rem',0),('steps-rem-plus1',1)):
    pre=head+b'1\n'+b'a a i k p 671 2 1 2 p 671 2 0 2 q 1 0 1 0 '; post=b' U 699 1 0 1 22 \n'; rem=len(post)
    C[name]=pre+str(rem+k).encode()+post
rows=[]
for n,b in C.items():
    (IN/(n+'.jdg')).write_bytes(b)
    for r,cmd in ROUTES.items():
        if r.startswith('v5') and n.startswith('ctl'): pass
        p=subprocess.run(['prlimit','--as=2147483648','--cpu=60','timeout','90',*cmd,str(IN/(n+'.jdg'))],capture_output=True)
        tag=f'{r}--{n}'
        (RAW/(tag+'.stdout')).write_bytes(p.stdout); (RAW/(tag+'.stderr')).write_bytes(p.stderr); (RAW/(tag+'.exit')).write_text(f'{p.returncode}\n')
        txt=(p.stdout+p.stderr).decode('latin-1')
        v='ACCEPT' if re.search(r'^ACCEPT',txt,re.M) and not re.search(r'REJECT',txt) else 'REJECT' if 'REJECT' in txt else 'OTHER'
        rows.append(dict(case=n,route=r,exit=p.returncode,verdict=v,first=' '.join(txt.split())[:140]))
        print(f'{n:22} {r:10} exit={p.returncode:<4} {v:7} {rows[-1]["first"][:100]}',flush=True)
(O/'raw'/'res-rows.json').write_text(json.dumps(rows,indent=1))
