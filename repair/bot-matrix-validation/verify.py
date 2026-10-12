"""Fresh independent exact matrix oracle and comparison with a supplied engine."""
import argparse, hashlib, json, os, shutil, subprocess, sys
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--engine',nargs='+',required=True,help='Executable and optional source arguments')
parser.add_argument('--output',type=Path,required=True,help='Fresh output directory')
args=parser.parse_args()
here=Path(__file__).resolve().parent
out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
for name in ['inputs','outputs','logs']:(out/name).mkdir()
shutil.copy2(here/'inputs/cases.json',out/'inputs/cases.json')
env=dict(os.environ,POMPETZKI_MATRIX_ENGINE_COMMAND=json.dumps(args.engine))
commands=[]
for name in ['negative_control.py','run_oracle.py','test_engine.py']:
 cmd=[sys.executable,str(here/name)]
 p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,timeout=300)
 (out/'logs'/(name+'.stdout.txt')).write_bytes(p.stdout)
 (out/'logs'/(name+'.stderr.txt')).write_bytes(p.stderr)
 commands.append({'command':cmd,'exit':p.returncode})
 assert p.returncode==0,(name,p.returncode,p.stderr)
oracle=json.loads((out/'outputs/oracle.json').read_text())
compare=json.loads((out/'outputs/engine-compare.json').read_text())
assert not oracle['identity_failures'],oracle['identity_failures']
assert compare['exit']==0 and not compare['failures'],compare['failures']
assert compare['jobs']==sum(v['pass_']+v['fail'] for v in compare['tally'].values())
receipt={'schema':'exact-matrix-bot-rerun-v1','cases':len(oracle['results']),
 'identity_checks':oracle['identity_checks'],'jobs':compare['jobs'],'failures':0,
 'engine_command':args.engine,'commands':commands,
 'engine_files':[{'name':Path(v).name,'sha256':hashlib.sha256(Path(v).read_bytes()).hexdigest()} for v in args.engine if Path(v).is_file()],
 'source_files':[{'name':p.relative_to(here).as_posix(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(here.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]}
(out/'RECEIPT.json').write_text(json.dumps(receipt,indent=2),encoding='utf-8')
(out/'SHA256SUMS.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file()),encoding='utf-8')
print(json.dumps({'output':str(out),'cases':receipt['cases'],'identity_checks':receipt['identity_checks'],'jobs':receipt['jobs'],'failures':0}))
