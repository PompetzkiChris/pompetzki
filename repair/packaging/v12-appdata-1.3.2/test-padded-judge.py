"""Compare exact equivalent integer spellings through the shipped judge routes."""
from pathlib import Path
import argparse,hashlib,json,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bundle',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--native',default='judge/judge-v6-windows.exe')
args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
body='JDG1 R 0 T 1 a q 0 0 0 2 Y q 0 0 G 0 0 0\n'
rows=[]
for width in [1,2,12,13,18,19,20,40,100]:
    file=out/('truth-width-'+str(width)+'.jdg')
    file.write_text(' '.join(token.zfill(width) if token.isdecimal() else token for token in body.split())+'\n')
    results={}
    for route,command in [('pmp-native',[args.bundle/args.native,file]),('racket',[args.bundle/'judge-rkt.exe',file]),
                          ('launcher',[args.bundle/'Abschluss Start.exe','--judge',file])]:
        began=time.monotonic();p=subprocess.run(list(map(str,command)),cwd=out,capture_output=True,timeout=60,
                                               creationflags=subprocess.CREATE_NO_WINDOW)
        (out/(str(width)+'-'+route+'.stdout.txt')).write_bytes(p.stdout)
        (out/(str(width)+'-'+route+'.stderr.txt')).write_bytes(p.stderr)
        results[route]={'command':list(map(str,command)),'exit':p.returncode,'seconds':time.monotonic()-began,
                        'stdout':p.stdout.decode(errors='replace'),'stderr':p.stderr.decode(errors='replace')}
    rows.append({'width':width,'integer_values':[0,1,2],'expected':'ACCEPT by each route',
                 'input_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'routes':results,
                 'passed':all(row['exit']==0 for row in results.values())})
report={'cases':len(rows),'passed':sum(row['passed'] for row in rows),'rows':rows}
(out/'results.json').write_text(json.dumps(report,indent=2))
(out/'SHA256SUMS.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(out.iterdir()) if p.is_file()))
print(json.dumps({'output':str(out),'cases':len(rows),'passed':report['passed']}))
raise SystemExit(0 if report['passed']==len(rows) else 1)
