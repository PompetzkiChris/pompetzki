"""Portable fresh source-word proof build; validate the explicit public payload first."""
from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--coqc',default='coqc');parser.add_argument('--coqchk',default='coqchk')
parser.add_argument('--output',type=Path);parser.add_argument('--check-only',action='store_true');args=parser.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'PUBLIC-SOURCE-MANIFEST.json').read_text())
for row in manifest['files']:
    path=root/row['path'];assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],row['path']
raw=(root/'source/judge-v6.pmp').read_bytes()
assert b''.join(raw.splitlines(keepends=True)[397:405])==(root/'source/recordcount-fragment.pmp').read_bytes()
assert len(json.loads((root/'source/source-extraction.json').read_text())['instructions'])==8
assert manifest['new_selected_closed_declarations']==36
if args.check_only:
    print(json.dumps({'passed':True,'verified_payload_rows':len(manifest['files']),'source_fragment_bytes':182,'new_selected_closed_declarations':36}));raise SystemExit(0)
out=args.output or root/'fresh-builds'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
out.mkdir(parents=True,exist_ok=False);tree=out/'source';tree.mkdir();logs=out/'logs';logs.mkdir()
for folder in ('Vendor','GrokRC','BorrowedRecordCount','Native','Proof'):shutil.copytree(root/folder,tree/folder)
mapping=[('Vendor/Groebner','Groebner'),('Vendor/C2Link','C2Link'),('GrokRC','GrokRC'),('BorrowedRecordCount','RecordCount'),('Native','Native'),('Proof','WordBridge')]
flags=[x for directory,logical in mapping for x in ['-Q',str(tree/directory),logical]]
modules=['Vendor/Groebner/ByteText.v','Vendor/C2Link/PmpCore.v','Vendor/C2Link/ExecStep.v','Vendor/C2Link/ExecMono.v',
 'Vendor/C2Link/ExecSim.v','Vendor/C2Link/RunKit.v','GrokRC/GrokRecordCount.v','GrokRC/GrokRecordCountVerify.v',
 'GrokRC/GrokSigned64.v','GrokRC/GrokSigned64Verify.v','GrokRC/GrokUnsigned64.v','GrokRC/GrokUnsigned64Verify.v',
 'BorrowedRecordCount/RecordCountSource.v','BorrowedRecordCount/RecordCountStep.v','BorrowedRecordCount/RecordCountMemory.v',
 'BorrowedRecordCount/RecordCountBounds.v','BorrowedRecordCount/RecordCountReceipt.v','Native/X86Native3.v',
 'Proof/PmpWordSub.v','Proof/NativeWordSub.v','Proof/AddressBridge.v','Proof/WordBridgeReceipt.v','Proof/WordBridgeReadableTypes.v']
commands=[]
def run(name,cmd):
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    flags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0
    result=subprocess.run(cmd,cwd=tree,capture_output=True,timeout=300,creationflags=flags)
    (logs/(name+'.stdout.txt')).write_bytes(result.stdout);(logs/(name+'.stderr.txt')).write_bytes(result.stderr)
    commands.append({'name':name,'argv':cmd,'started_utc':start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':result.returncode})
    print(name,result.returncode,flush=True);return result.returncode==0
okay=True
for name in modules:
    if not run('compile-'+Path(name).stem,[args.coqc,*flags,str(tree/name)]):okay=False;break
logical=dict(mapping);targets=[logical[Path(name).parent.as_posix()]+'.'+Path(name).stem for name in modules]
if okay:okay=run('kernel-all-modules',[args.coqchk,'-silent','-o',*flags,*targets])
result={'passed':okay,'fresh_compiled_modules':sum(c['name'].startswith('compile-') and c['exit_code']==0 for c in commands),
 'module_order':modules,'kernel_targets':targets,'kernel_ran':any(c['name']=='kernel-all-modules' for c in commands),'commands':commands,
 'source_sha256':{name:sha(tree/name) for name in modules},
 'scope':'Source-state, word arithmetic, primitive ALU/SF, and explicit address/permission bridges; emitted image/JS/OS/caller/final FAIL correspondence remains separate.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'),encoding='utf-8')
print(json.dumps({'output':str(out),'passed':okay,'fresh_modules':23}));raise SystemExit(0 if okay else 1)
