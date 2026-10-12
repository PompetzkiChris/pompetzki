"""Fresh compilation and recursive kernel check; every run uses a new directory."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,shutil,subprocess

root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--coqc',default='coqc');parser.add_argument('--coqchk',default='coqchk');parser.add_argument('--output',type=Path)
args=parser.parse_args();out=args.output or root/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S')
out.mkdir(parents=True,exist_ok=False);tree=out/'tree';tree.mkdir();logs=out/'logs';logs.mkdir()
for name in ['Vendor','Proof','NumericV5']:shutil.copytree(root/name,tree/name)
maps=['-Q',str(tree/'Vendor'/'Groebner'),'Groebner','-Q',str(tree/'Vendor'/'C2Link'),'C2Link','-Q',str(tree/'NumericV5'),'NumericV5','-Q',str(tree/'Proof'),'RDNUM']
commands=[]
modules=['Vendor/Groebner/ByteText.v','Vendor/C2Link/PmpCore.v','Vendor/C2Link/ExecStep.v','Vendor/C2Link/ExecMono.v','Vendor/C2Link/ExecSim.v','Vendor/C2Link/RunKit.v','NumericV5/DecimalSignificantV4.v',
         *['Proof/'+name for name in ['RDNUMSource.v','RDNUMTools.v','RDNUMCalls.v','RDNUMReaders.v','RDNUMNumber.v','RDNUMWordBounds.v','RDNUMPolicy.v','RDNUMReceipt.v'] if (tree/'Proof'/name).exists()]]
def run(name,cmd):
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    process=subprocess.run(list(map(str,cmd)),cwd=tree,capture_output=True,timeout=300,creationflags=subprocess.CREATE_NO_WINDOW)
    (logs/(name+'.stdout.txt')).write_bytes(process.stdout);(logs/(name+'.stderr.txt')).write_bytes(process.stderr)
    commands.append({'name':name,'command':list(map(str,cmd)),'cwd':str(tree),'started':started,'finished':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':process.returncode})
    (out/'commands.json').write_text(json.dumps(commands,indent=2))
    print(name,process.returncode,flush=True)
    if process.returncode:print(process.stdout.decode(errors='replace'),process.stderr.decode(errors='replace'));raise SystemExit(process.returncode)
for path in modules:run(Path(path).stem,[args.coqc,*maps,tree/path])
selected=['RDNUM.'+Path(path).stem for path in modules if path.startswith('Proof/')]
run('kernel-check',[args.coqchk,'-silent','-o',*maps,*selected])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'passed':True,'modules':modules,'kernel_checked_modules':selected,'commands':commands,'source_sha256':{str(p.relative_to(root)):sha(p) for name in ['Vendor','Proof','NumericV5'] for p in (root/name).rglob('*.v')}}
(out/'results.json').write_text(json.dumps(report,indent=2));(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(out),'passed':True,'modules':len(modules)}))
