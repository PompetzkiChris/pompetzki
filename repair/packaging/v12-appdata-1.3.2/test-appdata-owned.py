"""Check Windows folder resolution and uninstall behavior on newly owned fixtures."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--recipe',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--racket',type=Path,required=True)
parser.add_argument('--powershell',type=Path,required=True)
args=parser.parse_args()
recipe=args.recipe.resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
if os.name!='nt':raise SystemExit('This driver requires Windows.')
logs=out/'logs';logs.mkdir();fixtures=out/'fixtures';fixtures.mkdir();snapshots=out/'input-snapshots';snapshots.mkdir()
sha=lambda data:hashlib.sha256(data).hexdigest()
def owned(path):
    path=path.resolve()
    if not path.is_relative_to(out):raise ValueError('Fixture leaves output root.')
    for item in [path,*path.parents]:
        if item.exists() and item.is_symlink():raise ValueError('Fixture is linked.')
    return path
def run(name,argv,env):
    began=time.monotonic()
    p=subprocess.run([str(x) for x in argv],cwd=out,env=env,capture_output=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
    for stream,data in [('stdout',p.stdout),('stderr',p.stderr)]:
        (logs/(name+'.'+stream+'.txt')).write_bytes(data)
    return {'name':name,'argv':[str(x) for x in argv],'exit':p.returncode,'seconds':time.monotonic()-began,
            'stdout':name+'.stdout.txt','stderr':name+'.stderr.txt','stdout_sha256':sha(p.stdout),'stderr_sha256':sha(p.stderr)}
def data_json(run_row):
    return json.loads((logs/run_row['stdout']).read_text(encoding='utf-8-sig'))
def env_for(appdata,localappdata=None):
    env=os.environ.copy()
    for key,value in [('APPDATA',appdata),('LOCALAPPDATA',localappdata)]:
        if value is None:env.pop(key,None)
        else:env[key]=str(value)
    return env
def norm(value):return os.path.normcase(os.path.normpath(value))
parent_before={key:os.environ.get(key) for key in ['APPDATA','LOCALAPPDATA']}
known=out/'known-folders.ps1'
known.write_text("[pscustomobject]@{programs=[Environment]::GetFolderPath([Environment+SpecialFolder]::Programs);local=[Environment]::GetFolderPath([Environment+SpecialFolder]::LocalApplicationData)} | ConvertTo-Json -Compress\n",encoding='utf-8')
ps_prefix=[args.powershell,'-NoProfile','-NonInteractive','-WindowStyle','Hidden','-ExecutionPolicy','Bypass','-File']
known_run=run('Windows-known-folders',[*ps_prefix,known],env_for(None,None))
if known_run['exit']!=0:raise RuntimeError('Windows known-folder query failed.')
known_paths=data_json(known_run)
probe=out/'corrected-path-probe.rkt'
probe.write_text('#lang racket/base\n(require json (file '+json.dumps(str(recipe/'package-utils.rkt'))+'))\n(write-json (hasheq \'programs (path->string (windows-programs-path)) \'local (path->string (windows-local-appdata-path))))\n(newline)\n',encoding='utf-8')
path_rows=[]
owned_roaming=owned(out/'path-only-roaming');owned_local=owned(out/'path-only-local')
path_cases=[('both-absent',None,None,True),('both-empty','','',True),('both-owned',owned_roaming,owned_local,True),
            ('APPDATA-absent-local-owned',None,owned_local,True),('APPDATA-empty-local-owned','',owned_local,True),
            ('APPDATA-owned-local-absent',owned_roaming,None,True),('APPDATA-owned-local-empty',owned_roaming,'',True),
            ('APPDATA-invalid',':',owned_local,False),('APPDATA-relative','relative-appdata',owned_local,False),
            ('APPDATA-drive-relative','C:relative-appdata',owned_local,False),('LOCALAPPDATA-invalid',owned_roaming,':',False)]
for name,app,local,valid in path_cases:
    result=run('path-'+name,[args.racket,probe],env_for(app,local));checks={'exit':result['exit']==(0 if valid else 1)}
    actual=None
    if valid and result['exit']==0:
        actual=data_json(result)
        expected_programs=str(Path(app)/'Microsoft/Windows/Start Menu/Programs') if app else known_paths['programs']
        expected_local=str(local) if local else known_paths['local']
        checks.update(programs=norm(actual['programs'])==norm(expected_programs),local=norm(actual['local'])==norm(expected_local))
    path_rows.append({'case':name,'valid':valid,'run':result,'actual':actual,'checks':checks,'passed':all(checks.values())})
creator=out/'create-owned-shortcut.ps1'
creator.write_text("""param([string]$OwnedRoot,[string]$Target,[string]$Shortcut)
$ErrorActionPreference='Stop'
$taskBase=[IO.Path]::GetFullPath($OwnedRoot).TrimEnd([IO.Path]::DirectorySeparatorChar)
foreach($taskFile in @($Target,$Shortcut)) {
  if(-not ([IO.Path]::GetFullPath($taskFile).StartsWith($taskBase+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase))) { throw 'Shortcut leaves owned fixture root.' }
}
[IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($Shortcut)) | Out-Null
$taskShell=New-Object -ComObject WScript.Shell
$taskLink=$taskShell.CreateShortcut($Shortcut)
$taskLink.TargetPath=$Target
$taskLink.WorkingDirectory=[IO.Path]::GetDirectoryName($Target)
$taskLink.Save()
[pscustomobject]@{Created=[IO.File]::Exists($Shortcut);Target=$taskLink.TargetPath;Shortcut=$Shortcut} | ConvertTo-Json -Compress
""",encoding='utf-8')
case_specs=[('APPDATA-absent-shortcut-present',None,True,'eligible',0,True),
            ('APPDATA-empty-shortcut-present','',True,'eligible',0,True),
            ('APPDATA-absent-no-shortcut',None,False,'eligible',0,False),
            ('APPDATA-owned-shortcut-present','OWNED',True,'eligible',0,False),
            ('APPDATA-owned-wrong-target','OWNED',True,'wrong-target',0,True),
            ('APPDATA-owned-wrong-hash','OWNED',True,'wrong-hash',0,True),
            ('APPDATA-owned-outside-Programs','OWNED',True,'outside-Programs',0,True),
            ('APPDATA-invalid-preflight',':',True,'eligible',1,True),
            ('APPDATA-relative-preflight','relative-appdata',True,'eligible',1,True),
            ('APPDATA-drive-relative-preflight','C:relative-appdata',True,'eligible',1,True)]
case_rows=[]
for name,app,has_shortcut,variant,want_exit,want_shortcut in case_specs:
    case=owned(fixtures/name);case.mkdir();install=owned(case/'install');install.mkdir();roaming=owned(case/'roaming')
    contents={'VERSION':b'1.3.2\n','data/unchanged.txt':b'owned unchanged payload\n','data/modified.txt':b'owned original payload\n',
              'Abschluss Start.exe':b'Owned fixture target; never executed.\n','Uninstall-Abschluss.ps1':(recipe/'Uninstall-Abschluss.ps1').read_bytes()}
    for rel,data in contents.items():
        p=owned(install/rel);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    manifest=''.join(sha(data)+'  '+rel+'\n' for rel,data in contents.items()).encode('ascii');(install/'MANIFEST.sha256').write_bytes(manifest)
    folder=roaming/'Microsoft/Windows/Start Menu/Programs' if variant!='outside-Programs' else roaming/'outside-Programs'
    shortcut=owned(folder/'Abschluss 1.3.2.lnk');creation=None
    if has_shortcut:
        target=install/'Abschluss Start.exe' if variant!='wrong-target' else owned(case/'other-owned-target.exe')
        if variant=='wrong-target':target.write_bytes(b'Other owned target; never executed.\n')
        creation=run(name+'-create-shortcut',[*ps_prefix,creator,'-OwnedRoot',case,'-Target',target,'-Shortcut',shortcut],os.environ.copy())
        if creation['exit']!=0 or not shortcut.is_file():raise RuntimeError('Owned shortcut creation failed.')
    recorded_hash=sha(shortcut.read_bytes()) if has_shortcut else False
    if variant=='wrong-hash':recorded_hash='0'*64
    file_rows=[{'path':rel,'sha256':sha(data)} for rel,data in contents.items()]+[{'path':'MANIFEST.sha256','sha256':sha(manifest)}]
    receipt={'version':'1.3.2','manifest_sha256':sha(manifest),'files':file_rows,'shortcut':str(shortcut) if has_shortcut else False,'shortcut_sha256':recorded_hash}
    (install/'INSTALLATION.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    (install/'data/modified.txt').write_bytes(b'owned modified payload retained\n');(install/'additional-owned.txt').write_bytes(b'owned additional payload retained\n')
    before={str(p.relative_to(case)):sha(p.read_bytes()) for p in case.rglob('*') if p.is_file()}
    snapshot=owned(snapshots/name);snapshot.mkdir()
    for p in case.rglob('*'):
        if p.is_file():copy=snapshot/p.relative_to(case);copy.parent.mkdir(parents=True,exist_ok=True);copy.write_bytes(p.read_bytes())
    for row in file_rows:owned(install/row['path'])
    owned(install/'INSTALLATION.json');owned(shortcut)
    app_value=roaming if app=='OWNED' else app
    result=run(name+'-uninstall',[*ps_prefix,install/'Uninstall-Abschluss.ps1','-InstallRoot',install],env_for(app_value,None))
    after={str(p.relative_to(case)):sha(p.read_bytes()) for p in case.rglob('*') if p.is_file()}
    checks={'exit':result['exit']==want_exit,'shortcut_state':shortcut.is_file()==want_shortcut,
            'receipt_state':(install/'INSTALLATION.json').is_file()==(want_exit!=0),
            'unchanged_payload_state':(install/'data/unchanged.txt').is_file()==(want_exit!=0),
            'modified_payload_preserved':(install/'data/modified.txt').read_bytes()==b'owned modified payload retained\n',
            'additional_payload_preserved':(install/'additional-owned.txt').read_bytes()==b'owned additional payload retained\n'}
    if want_exit!=0:checks['all_files_unchanged_before_preflight_error']=before==after
    removal_report=data_json(result) if result['exit']==0 else None
    if removal_report and has_shortcut:
        removed={norm(p) for p in removal_report['Removed']};preserved={norm(p) for p in removal_report['Preserved']}
        checks['shortcut_report']=norm(str(shortcut)) in (preserved if want_shortcut else removed)
    case_rows.append({'case':name,'variant':variant,'run':result,'shortcut_creation':creation,'checks':checks,'passed':all(checks.values()),
                      'shortcut_expected_action':'preserved' if want_shortcut else 'removed' if has_shortcut else 'none',
                      'before_files':before,'after_files':after,'removal_report':removal_report})
result={'recipe':str(recipe),'path_checks':path_rows,'uninstall_checks':case_rows,'Windows_known_folder_query':known_run,
        'parent_environment_unchanged':parent_before=={key:os.environ.get(key) for key in ['APPDATA','LOCALAPPDATA']},
        'source_hashes':{name:sha((recipe/name).read_bytes()) for name in ['installer.rkt','package-utils.rkt','Uninstall-Abschluss.ps1','uninstaller.rkt']},
        'scope':'Read-only actual Windows known-folder queries and new owned fixtures. Child-only environment. Actual user Programs folder is never written; out-of-known-folder shortcuts are counted as preserved.'}
result['passed']=sum(x['passed'] for x in path_rows+case_rows);result['failed']=sum(not x['passed'] for x in path_rows+case_rows)
(out/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
(out/'SHA256SUMS.txt').write_text(''.join(sha(p.read_bytes())+'  '+str(p.relative_to(out)).replace('\\','/')+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'),encoding='utf-8')
print(json.dumps({'passed':result['passed'],'failed':result['failed'],'path_checks':len(path_rows),'uninstall_checks':len(case_rows),'parent_environment_unchanged':result['parent_environment_unchanged'],'output':str(out)}))
raise SystemExit(0 if result['failed']==0 and result['parent_environment_unchanged'] else 1)
