"""Independent exact Word64 expectations for rebuilt console/window interpreters."""
from pathlib import Path
import argparse,ctypes,hashlib,itertools,json,os,random,subprocess
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--runtime',type=Path,required=True)
parser.add_argument('--source',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
if os.name=='nt':ctypes.windll.kernel32.SetErrorMode(0x8003)
minimum,maximum=-(1<<63),(1<<63)-1;rng=random.Random(20261011)
pairs=list(itertools.product([minimum,minimum+1,maximum,-2,-1,0,1,2],repeat=2))
pairs += [(rng.randint(minimum,maximum),rng.randint(minimum,maximum)) for _ in range(120)]
rows=[]
def run(name,command):
    p=subprocess.run(list(map(str,command)),cwd=out,capture_output=True,timeout=20,creationflags=subprocess.CREATE_NO_WINDOW)
    (out/(name+'.stdout.txt')).write_bytes(p.stdout);(out/(name+'.stderr.txt')).write_bytes(p.stderr)
    return p
for mode in ['pompetzki.exe','pompetzki-w.exe']:
    for index,(a,b) in enumerate(pairs):
        for op in ['div','mod']:
            name=Path(mode).stem+'-'+str(index)+'-'+op;program=out/(name+'.pmp')
            program.write_text(f'trace off\nset X {op} {a} {b}\ntext S int X\nprint S\n')
            p=run(name,[args.runtime/mode,program])
            if b:
                q=(abs(a)//abs(b))*(-1 if (a<0)!=(b<0) else 1)
                value=q if op=='div' else a-q*b
                expected=str((value+(1<<63))%(1<<64)-(1<<63))
                passed=p.returncode==0 and p.stdout.strip()==expected.encode()
            else:expected='zero divisor rejected';passed=p.returncode==1
            rows.append({'mode':mode,'op':op,'a':str(a),'b':str(b),'expected':expected,'exit':p.returncode,
                         'stdout':p.stdout.decode(errors='replace'),'passed':passed})
            if (a,b)==(minimum,-1):
                emitted=out/(name+'.exe');built=run(name+'-emit',[args.runtime/mode,'emit',program,emitted])
                result=run(name+'-emitted',[emitted])
                rows.append({'mode':mode+'-emitted','op':op,'exit':result.returncode,'expected':expected,
                             'stdout':result.stdout.decode(errors='replace'),
                             'passed':built.returncode==0 and result.returncode==0 and result.stdout.strip()==expected.encode()})
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'cases':len(rows),'passed':sum(row['passed'] for row in rows),'failed':sum(not row['passed'] for row in rows),
        'source_sha256':sha(args.source),'binary_sha256':{name:sha(args.runtime/name) for name in ['pompetzki.exe','pompetzki-w.exe']},'rows':rows}
(out/'results.json').write_text(json.dumps(report,indent=2))
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in sorted(out.iterdir()) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(out),'cases':len(rows),'passed':report['passed'],'failed':report['failed']}))
raise SystemExit(0 if report['passed']==len(rows)==740 else 1)
