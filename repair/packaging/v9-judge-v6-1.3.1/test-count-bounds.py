"""Exercise installed judge-v6 routes on true/false and short huge-count inputs."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bundle',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
bundle=args.bundle.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
truth=b'JDG1 R 0 T 1 a q 0 0 0 2 Y q 0 0 G 0 0 0\n'
cases=[
 ('true',truth,'ACCEPT'),
 ('false-proof',truth.replace(b'T 1 a q',b'T 1 a n q',1),'REJECT'),
 ('forged-registry',b'JDG1 R 1 a n q 0 0 0 T 1 a n q 0 0 0 1 U 0 0 0\n','REJECT'),
 ('huge-registry',b'JDG1 R 100000000000 T 0\n','REJECT'),
 ('huge-theorems',b'JDG1 R 0 T 100000000000\n','REJECT'),
 ('huge-steps',b'JDG1 R 0 T 1 a q 0 0 0 100000000000\n','REJECT'),
 ('huge-hypotheses',b'JDG1 R 0 T 1 a q 0 0 100000000000\n','REJECT'),
 ('padded-true',b' '.join(t.zfill(5000) if t.isdigit() else t for t in truth.split())+b'\n','ACCEPT'),
 ('thirteenth-significant-digit',truth.replace(b'R 0',b'R 1000000000000',1),'REJECT'),
 ('trailing-nul',truth+b'\x00','REJECT'),
]
routes={'native':[bundle/'judge/judge-v6-windows.exe'],
        'interpreted':[bundle/'pompetzki.exe',bundle/'judge/judge-v6.pmp'],
        'racket':[bundle/'judge-rkt.exe'],
        'launcher':[bundle/'Abschluss Start.exe','--judge']}
results=[]
for name,data,want in cases:
    path=out/(name+'.jdg');path.write_bytes(data)
    for route,argv in routes.items():
        command=[*map(str,argv),str(path)]
        began=time.monotonic()
        try:
            process=subprocess.run(command,cwd=out,capture_output=True,timeout=10,
                creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' else 0)
            code,stdout,stderr=process.returncode,process.stdout,process.stderr
        except subprocess.TimeoutExpired as error:
            code,stdout,stderr='TIMEOUT',error.stdout or b'',error.stderr or b''
        stem=name+'-'+route
        stdout_path=out/(stem+'.stdout.txt');stderr_path=out/(stem+'.stderr.txt')
        stdout_path.write_bytes(stdout);stderr_path.write_bytes(stderr)
        if route=='launcher':
            try: verdict=json.loads(stdout)['verdict']
            except (ValueError,KeyError):verdict='OTHER'
        else:
            tokens=set(re.findall(rb'\b(?:ACCEPT|REJECT)\b',stdout))
            verdict=next(iter(tokens)).decode() if len(tokens)==1 else 'OTHER'
        passed=code==(0 if want=='ACCEPT' else 1) and verdict==want
        results.append({'case':name,'route':route,'expected':want,'verdict':verdict,
            'exit':code,'passed':passed,'command':command,'seconds':time.monotonic()-began,
            'input_sha256':sha(path),'stdout':stdout_path.name,'stdout_sha256':sha(stdout_path),
            'stderr':stderr_path.name,'stderr_sha256':sha(stderr_path)})
        (out/'progress.json').write_text(json.dumps(results,indent=2))
report={'cases':len(cases),'routes':len(routes),'runs':len(results),
        'passed':sum(row['passed'] for row in results),'failed':sum(not row['passed'] for row in results),
        'timeouts':sum(row['exit']=='TIMEOUT' for row in results),'results':results,
        'tools':{str(p.relative_to(bundle)):sha(p) for argv in routes.values() for p in argv if isinstance(p,Path)}}
(out/'results.json').write_text(json.dumps(report,indent=2))
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in sorted(out.iterdir()) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({k:v for k,v in report.items() if k not in {'results','tools'}}))
raise SystemExit(0 if not report['failed'] else 1)
