"""Fresh compilation and recursive kernel check, with preserved source inputs."""
from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--coqc',default='coqc');parser.add_argument('--coqchk',default='coqchk');parser.add_argument('--output',type=Path);args=parser.parse_args()
out=args.output or root/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
out.mkdir(parents=True,exist_ok=False);tree=out/'tree';tree.mkdir();logs=out/'logs';logs.mkdir()
for folder in ('Vendor','GrokRC','Proof'):shutil.copytree(root/folder,tree/folder)
maps=['-Q',str(tree/'Vendor/Groebner'),'Groebner','-Q',str(tree/'Vendor/C2Link'),'C2Link',
      '-Q',str(tree/'GrokRC'),'GrokRC','-Q',str(tree/'Proof'),'RecordCount']
modules=['Vendor/Groebner/ByteText.v','Vendor/C2Link/PmpCore.v','Vendor/C2Link/ExecStep.v',
         'Vendor/C2Link/ExecMono.v','Vendor/C2Link/ExecSim.v','Vendor/C2Link/RunKit.v',
         'GrokRC/GrokRecordCount.v','GrokRC/GrokRecordCountVerify.v']
order=['RecordCountSource','RecordCountStep','RecordCountMemory','RecordCountBounds','RecordCountReceipt']
modules += ['Proof/'+name+'.v' for name in order if (tree/'Proof'/(name+'.v')).exists()]
commands=[]
def run(name,cmd):
    start=datetime.datetime.now(datetime.timezone.utc).isoformat();flags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0
    p=subprocess.run(cmd,cwd=tree,capture_output=True,timeout=180,creationflags=flags)
    (logs/(name+'.stdout.txt')).write_bytes(p.stdout);(logs/(name+'.stderr.txt')).write_bytes(p.stderr)
    commands.append({'name':name,'command':cmd,'cwd':str(tree),'started':start,'finished':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode})
    print(name,p.returncode,flush=True);return p.returncode==0
okay=True
for name in modules:
    if not run(Path(name).stem,[args.coqc,*maps,str(tree/name)]):okay=False;break
selected=['RecordCount.'+Path(name).stem for name in modules if name.startswith('Proof/')]
if okay:okay=run('kernel-check',[args.coqchk,'-silent','-o',*maps,*selected])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result={'passed':okay,'modules':modules,'kernel_checked_modules':selected,'commands':commands,
        'source_sha256':{p.relative_to(tree).as_posix():sha(p) for p in sorted(tree.rglob('*.v'))},
        'scope':'Extracted RECORDCOUNT controller in unchanged PmpCore; trusted text-to-AST/native/compiler/OS boundaries explicit.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(out),'passed':okay,'modules':len(modules)}));raise SystemExit(0 if okay else 1)
