"""Fresh unchanged Grok count-model compilation and recursive kernel check."""
from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--coqc',default='coqc');parser.add_argument('--coqchk',default='coqchk');parser.add_argument('--output',type=Path);args=parser.parse_args()
out=args.output or root/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
out.mkdir(parents=True,exist_ok=False);tree=out/'tree'/'GrokRC';tree.mkdir(parents=True);logs=out/'logs';logs.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'GrokRecordCount.v':'16c51c1ba0869aedea59f0f04175f379c58449bcc5d8699c265452abace3bf61',
      'GrokRecordCountVerify.v':'9d50414d0db71eb58b05b33435562e4958bae409986b78b4d7ac45b67abd940c'}
for name,digest in pins.items():assert sha(root/'source'/name)==digest;shutil.copy2(root/'source'/name,tree/name)
commands=[]
def run(name,cmd):
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    flags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0
    p=subprocess.run(cmd,cwd=out/'tree',capture_output=True,timeout=180,creationflags=flags)
    (logs/(name+'.stdout.txt')).write_bytes(p.stdout);(logs/(name+'.stderr.txt')).write_bytes(p.stderr)
    commands.append({'name':name,'command':cmd,'cwd':str(out/'tree'),'started':start,
      'finished':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode})
    print(name,p.returncode,flush=True);return p.returncode==0
assert run('tool-version',[args.coqc,'--version'])
maps=['-Q',str(tree),'GrokRC']
okay=True
for name in pins:
    if not run(Path(name).stem,[args.coqc,*maps,str(tree/name)]):okay=False;break
if okay:okay=run('kernel-check',[args.coqchk,'-o',*maps,'GrokRC.GrokRecordCount','GrokRC.GrokRecordCountVerify'])
assumptions=(logs/'GrokRecordCountVerify.stdout.txt').read_text() if (logs/'GrokRecordCountVerify.stdout.txt').exists() else ''
if okay:
    assert assumptions.count('Closed under the global context')==8
    combined=(logs/'kernel-check.stdout.txt').read_text()+(logs/'kernel-check.stderr.txt').read_text()
    assert '* Axioms: <none>' in combined and '* Constants/Inductives relying on unsafe (co)fixpoints: <none>' in combined
receipt={'passed':okay,'commands':commands,'compiled_modules':list(pins),'source_sha256':pins,
         'selected_closed_proof_declarations':assumptions.count('Closed under the global context'),
         'delivered_object_files_used':False,'scope':'Arithmetic and list syntax model; no executable correspondence theorem.'}
(out/'results.json').write_text(json.dumps(receipt,indent=2)+'\n')
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(out),'passed':okay,'closed':receipt['selected_closed_proof_declarations']}))
raise SystemExit(0 if okay else 1)
