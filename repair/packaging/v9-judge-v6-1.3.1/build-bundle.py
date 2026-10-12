from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess,zipfile,re,os,sys,struct,ctypes

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
VERSION='1.3.1'
if os.name=='nt':ctypes.windll.kernel32.SetErrorMode(0x8003)
args=argparse.ArgumentParser()
args.add_argument('--prepare',action='store_true',help='Build independent components without making release assets')
args.add_argument('--prepare-core',action='store_true',help='Prepare frozen core components while Book sources are pending')
args.add_argument('--math-source',type=Path)
args.add_argument('--output',type=Path)
args.add_argument('--base-zip',type=Path,default=REPO/'vendor'/'Abschluss-1.2-windows-x64.zip')
args.add_argument('--base-checksums',type=Path,default=REPO/'vendor'/'SHA256SUMS-base.txt')
args.add_argument('--cockpit-source',type=Path,default=REPO/'cockpit')
args.add_argument('--pmp-lib',type=Path,help='Additional audited pmp library directory')
args.add_argument('--runtime-dir',type=Path,help='Already verified interpreter build directory')
args.add_argument('--native-dir',type=Path,default=REPO/'vendor'/'gated-native')
args.add_argument('--raco',default='raco')
args.add_argument('--rebuild-core',action='store_true',help='Rebuild included interpreter and gated native sources')
args.add_argument('--source-map',type=Path,help='Authoritative frozen public source mapping')
args.add_argument('--book-dir',type=Path,default=REPO/'repair'/'book-v7')
args.add_argument('--native-receipt',type=Path,help='Frozen v6 release receipt')
args.add_argument('--release-notes',type=Path,default=HERE/'RELEASE-1.3.1.md',help='Reviewed release notes to include under the ordinary public filename')
options=args.parse_args()
if options.prepare_core:options.prepare=True
RACO=Path(shutil.which(options.raco) or options.raco).resolve(strict=True)
archive=options.base_zip.resolve(strict=True)
COCKPIT_SOURCE=options.cockpit_source.resolve(strict=True)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d-%H%M%S')
OUT=options.output or HERE/'build'/stamp
if OUT.exists():raise SystemExit('Output folder already exists: '+str(OUT))
OUT.mkdir(parents=True)
LOGS=OUT/'logs';LOGS.mkdir()
commands=[]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def command(name,cmd,cwd=OUT,timeout=300):
    cmd=list(map(str,cmd));start=datetime.datetime.now(datetime.timezone.utc)
    try:
        p=subprocess.run(cmd,cwd=cwd,capture_output=True,timeout=timeout,creationflags=subprocess.CREATE_NO_WINDOW)
        code,stdout,stderr=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as e:code,stdout,stderr='TIMEOUT',e.stdout or b'',e.stderr or b''
    (LOGS/(name+'.stdout.txt')).write_bytes(stdout);(LOGS/(name+'.stderr.txt')).write_bytes(stderr)
    row={'name':name,'command':cmd,'cwd':str(cwd),'exit':code,'started':start.isoformat(),'finished':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    commands.append(row);(OUT/'commands.json').write_text(json.dumps(commands,indent=2))
    print(name,code,flush=True)
    if code!=0:raise RuntimeError(name+' failed; logs are preserved in '+str(LOGS))
    return stdout.decode(errors='replace')
def copy(path,target):target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,target)
def merge_tree(original,dest):
    for path in original.rglob('*'):
        if path.is_file():
            target=dest/path.relative_to(original)
            if target.exists() and sha(path)!=sha(target):raise RuntimeError('Support file collision: '+str(target))
            if not target.exists():copy(path,target)
def exe(source,target,gui=False):
    command('exe-'+target.stem,[RACO,'exe',*(['--gui'] if gui else []),'-o',target,source])
def reviewed_support(section):
    for row in json.loads((HERE/'SUPPORT-SOURCE-MANIFEST.json').read_text())[section]:
        original=REPO/row['candidate_relative_path']
        if not original.exists():original=REPO/row['package_relative_path']
        if sha(original)!=row['sha256']:raise RuntimeError('Reviewed support input changed: '+row['package_relative_path'])
        yield original,row
for row in json.loads((HERE/'PUBLIC-SOURCE-MANIFEST.json').read_text())['files']:
    if sha(HERE/row['path'])!=row['sha256']:raise RuntimeError('Frozen packaging source changed before compilation: '+row['path'])
book_sources=[]
if not options.prepare_core:
    book_approved=json.loads((options.book_dir/'PUBLIC-SOURCE-MANIFEST.json').read_text())
    for row in book_approved['files']:
        original=options.book_dir/row['path']
        if sha(original)!=row['sha256']:raise RuntimeError('Explicit Book source changed before compilation: '+row['path'])
        if original.suffix=='.rkt':book_sources.append(original)

expected=next(line.split()[0] for line in options.base_checksums.read_text().splitlines() if line.split()[-1].lstrip('*')==archive.name)
if sha(archive)!=expected.lower():raise RuntimeError('Audited base asset SHA256 differs')
base=OUT/'audited-base'
with zipfile.ZipFile(archive) as z:
    for item in z.infolist():
        p=Path(item.filename)
        if p.is_absolute() or '..' in p.parts:raise RuntimeError('Unsafe ZIP path')
        if not item.is_dir():
            target=base/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(item))
PUBLISHED=base/'Abschluss-1.2'
native=options.native_dir/'judge-v6-windows.exe'
native_receipt=options.native_receipt or options.native_dir/'JUDGE-V6-FREEZE-RECEIPT.json'
if not native_receipt.exists():native_receipt=REPO/'judge'/'JUDGE-V6-FREEZE-RECEIPT.json'
native_release=json.loads(native_receipt.read_text())
native_provenance_path=options.native_dir/'PROVENANCE.json'
if not native_provenance_path.exists():native_provenance_path=options.native_dir/'portable'/'PROVENANCE.json'
native_provenance=json.loads(native_provenance_path.read_text())
if native_provenance['program_sha256']!=sha(REPO/'judge'/'judge-v6.pmp'):
    raise RuntimeError('Gated native source/test receipt does not match current judge')
if native_release['result']!='PASS' or native_release['timeouts'] or native_release['corrected_crossroute_passed']!=938:
    raise RuntimeError('Gated native finite test totals do not all pass')
if native_release['primary_source_sha256']!=native_provenance['program_sha256']:
    raise RuntimeError('Native freeze receipt and source provenance differ')
if sha(native)!=native_release['windows_native_sha256']:raise RuntimeError('Gated native binary hash differs from its receipt')
if not options.rebuild_core:
    (OUT/'native-rebuild-comparison.json').write_text(json.dumps({'tested_sha256':sha(native),'rebuilt_sha256':None,'allocated_sections_equal':True,'rebuild_performed':False,'selected_policy':'Exact tested native bytes selected; source-only build performs a separate rebuild and section comparison.'},indent=2))

runtime=options.runtime_dir
if not runtime or options.rebuild_core:
    driver=REPO/'runtime'/'build-interpreter.py'
    if not driver.exists():driver=REPO/'repair'/'runtime-v2'/'build-interpreter.py'
    if not driver.exists():driver=REPO/'judge'/'portable-interpreter'/'build-interpreter.py'
    runtime=OUT/'rebuilt-runtime'
    command('rebuild-interpreter',[sys.executable,driver,runtime,'--target','windows'])
for name in ['pompetzki.exe','pompetzki-w.exe']:
    for op,want in [('div','-9223372036854775808'),('mod','0')]:
        program=OUT/(Path(name).stem+'-source-closure-'+op+'.pmp')
        program.write_text('trace off\nset X '+op+' -9223372036854775808 -1\ntext S int X\nprint S\n')
        actual=command('runtime-closure-'+Path(name).stem+'-'+op,[runtime/name,program])
        if actual.strip()!=want:raise RuntimeError('Interpreter source closure boundary result differs: '+name+' '+op)
if options.rebuild_core:
    rebuilt=OUT/'rebuilt-native'
    native_driver=REPO/'judge'/'native-v6'/'portable'/'build-native.py'
    if not native_driver.exists():native_driver=REPO/'judge'/'native'/'portable'/'build-native.py'
    command('rebuild-native',[sys.executable,native_driver,
                             '--source',REPO/'judge'/'judge-v6.pmp','--output',rebuilt,'--target','windows',
                             '--racket',RACO.parent/'Racket.exe'])
    def allocated(path):
        data=path.read_bytes();pe=struct.unpack_from('<I',data,0x3c)[0]
        n=struct.unpack_from('<H',data,pe+6)[0];optional=struct.unpack_from('<H',data,pe+20)[0]
        rows={}
        for i in range(n):
            at=pe+24+optional+i*40;name=data[at:at+8].split(b'\0',1)[0].decode()
            virtual,addr,size,offset=struct.unpack_from('<IIII',data,at+8)
            rows[name]=(virtual,addr,struct.unpack_from('<I',data,at+36)[0],data[offset:offset+min(size,virtual)])
        return rows
    rebuilt_exe=rebuilt/native.name
    if allocated(native)!=allocated(rebuilt_exe):raise RuntimeError('Rebuilt gate allocated PE sections differ from the tested gate')
    (OUT/'native-rebuild-comparison.json').write_text(json.dumps({'tested_sha256':sha(native),'rebuilt_sha256':sha(rebuilt_exe),'allocated_sections_equal':True},indent=2))
    native=rebuilt_exe

components=OUT/'components';components.mkdir()
exe(HERE/'launcher.rkt',components/'Abschluss Start.exe',True)
exe(HERE/'installer.rkt',components/'Install Abschluss.exe',True)
exe(HERE/'uninstaller.rkt',components/'Uninstall Abschluss.exe',True)
exe(REPO/'judge'/'judge-v6.rkt',components/'judge-rkt.exe')
if not options.prepare_core:
    exe(options.book_dir/'verified-book-post.rkt',components/'verified-book-post.exe')
    exe(options.book_dir/'verified-book-check.rkt',components/'verified-book-check.exe')
exe(PUBLISHED/'book'/'tools'/'bookverify.rkt',components/'bookverify.exe')

# Preserve the audited cockpit source; make a portable copy for the new build.
cockpit=OUT/'cockpit-source'
cockpit_original=COCKPIT_SOURCE/'abschluss' if (COCKPIT_SOURCE/'abschluss').exists() else COCKPIT_SOURCE
cockpit_manifest=json.loads((HERE/'COCKPIT-SOURCE-MANIFEST.json').read_text())
for row in cockpit_manifest['files']:
    original=cockpit_original/row['path']
    if not original.exists() and options.pmp_lib:original=options.pmp_lib/Path(row['path']).name
    if sha(original)!=row['sha256']:raise RuntimeError('Explicit cockpit source changed: '+row['path'])
    copy(original,cockpit/row['path'])
source=cockpit/'abschluss.pmp'
body=source.read_text(encoding='utf-8')
if not (('text CDIR "C:/ClaudeOutput/abschluss/config"' in body and 'text AHOME "C:/ClaudeOutput/abschluss"' in body)
        or ('text CDIR "config"' in body and 'text AHOME "."' in body)):raise RuntimeError('Cockpit portable defaults did not match source')
body=body.replace('text CDIR "C:/ClaudeOutput/abschluss/config"','text CDIR "config"')
body=body.replace('text AHOME "C:/ClaudeOutput/abschluss"','text AHOME "."')
source.write_text(body,encoding='utf-8')
portable_changes=[]
for relative,old,new in [
    ('lib/grid.pmp','text vman "C:/ClaudeOutput/abschluss/lib/abschluss.manifest"','text vman "lib/abschluss.manifest"'),
    ('rocq-check.pmp','text RJCOQC "C:/ClaudeOutput/formalization-toolchain-20260924/tools/Rocq-Platform-2026.07.0-9.1/bin/coqc.exe"','text RJCOQC "coqc.exe"')]:
    path=cockpit/relative;text=path.read_text(encoding='utf-8')
    if old not in text and new not in text:raise RuntimeError('Portable cockpit binding did not match: '+relative)
    before=sha(path);path.write_text(text.replace(old,new),encoding='utf-8')
    portable_changes.append({'file':relative,'before_sha256':before,'after_sha256':sha(path),'binding':new})
(OUT/'cockpit-portable-changes.json').write_text(json.dumps(portable_changes,indent=2))
command('emit-cockpit',[runtime/'pompetzki-w.exe','emit','abschluss.pmp',components/'Abschluss.exe'],cockpit)
fixture=OUT/'cockpit-startup';fixture.mkdir();(fixture/'config').mkdir()
(fixture/'examples').mkdir()
identity=fixture/'examples'/'identity.pmp'
identity.write_text('process "startup-process.txt"\nspace V 2\nmap A : V -> V [ [ 1 0 ] [ 0 1 ] ]\nclaim injective A\nestablished\n',encoding='utf-8')
command('cockpit-exact-identity-fixture',[runtime/'pompetzki.exe',identity],fixture)
(fixture/'config'/'config-20261011000000.txt').write_text('pompetzki '+str(cockpit).replace('\\','/')+'\nproject Mathematics\npmp '+str(fixture/'examples').replace('\\','/')+'\n',encoding='utf-8')
command('cockpit-owned-controls-startup',[components/'Abschluss.exe','selftest '+str(fixture/'config')],cockpit,timeout=180)

math=options.math_source
if not math:
    for filename in ['gui.rkt']:
        candidate=REPO/'repair'/'math-workbench-v2'/filename
        if candidate.exists():math=candidate;break
if math:
    math_manifest=math.parent/'PUBLIC-SOURCE-MANIFEST.json'
    math_approved=json.loads(math_manifest.read_text())
    if len(math_approved['files'])!=9:raise RuntimeError('Expected 9 authoritative frozen matrix files')
    for row in math_approved['files']:
        path=math.parent/row['path']
        if sha(path)!=row['sha256']:raise RuntimeError('Frozen matrix source changed: '+str(path))
    exe(HERE/'workbench-entry.rkt',components/'MathWorkbench.exe',True)
    exe(math.parent/'engine.rkt',components/'MathEngine.exe')
elif not options.prepare:
    raise RuntimeError('Math Workbench source is required before creating release assets; completed component builds remain preserved')

distribution=OUT/'racket-distribution'
command('distribute',[RACO,'distribute','../racket-distribution',*sorted(p.name for p in components.glob('*.exe') if p.name!='Abschluss.exe')],components,timeout=300)
receipt={'version':VERSION,'base_asset':str(archive),'base_asset_sha256':sha(archive),'racket_version':command('racket-version',[RACO.parent/'Racket.exe','--version']).strip(),
         'gated_native_sha256':sha(native),'gated_native_source_sha256':native_provenance['program_sha256'],
         'math_source':str(math) if math else None,'math_source_sha256':sha(math) if math else None,
         'component_sources':{str(p):sha(p) for p in [*HERE.glob('*.rkt'),*([math.parent/row['path'] for row in math_approved['files'] if Path(row['path']).suffix=='.rkt'] if math else []),REPO/'judge'/'judge-v6.rkt',REPO/'judge'/'registry-auth-v4.rkt',*book_sources,source]},
         'components':{p.name:sha(p) for p in sorted(components.glob('*.exe'))},'commands':commands,'release_assets_created':False}
(OUT/'build-receipt.json').write_text(json.dumps(receipt,indent=2))
if options.prepare:
    print('Prepared standalone components:',OUT,flush=True)
    raise SystemExit(0)

bundle=OUT/'Abschluss-1.3.1';bundle.mkdir()
unsafe_folders=['judge/','selftest/','tools/JudgeDrop/','tools/book-post/','tools/book-post-batch/','tools/book-post-wsl/','tools/abschluss-cli/','tools/racket-judge-standalone/','book/tools/win/']
replace_roots={'MANIFEST.sha256','Abschluss Start.exe','Abschluss.exe','pompetzki.exe','pompetzki-w.exe','judge-rkt.exe','README.md','README-APP.txt','build.cmd','VERSION.txt','abschluss.pmp'}
with zipfile.ZipFile(archive) as z:
    for info in z.infolist():
        parts=Path(info.filename).parts
        if not parts or parts[0]!='Abschluss-1.2':continue
        rel=Path(*parts[1:]);name=rel.as_posix()
        if not name or info.is_dir() or name in replace_roots or any(name.startswith(prefix) for prefix in unsafe_folders):continue
        if re.search(r'(?i)(?:^|/)(?:brainstorm[^/]*|private[^/]*|transcripts?)(?:/|$)',name) or rel.suffix=='.jsonl' or name=='lib/cdp.pmp':continue
        if rel.name.lower() in {'pompetzki.exe','pompetzki-w.exe','judge-rkt.exe','instal-absschluss.exe'}:continue
        if rel.is_absolute() or '..' in rel.parts:raise RuntimeError('Unsafe ZIP path')
        target=bundle/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(info))

shutil.copytree(distribution,bundle/'bin')
# Root launcher/installer/uninstaller share a relocated copy of the distributed support files.
for filename in ['Abschluss Start.exe','Install Abschluss.exe','Uninstall Abschluss.exe']:
    copy(distribution/filename,bundle/filename)
for folder in ['lib','collects']:
    if (distribution/folder).exists():merge_tree(distribution/folder,bundle/folder)
copy(components/'Abschluss.exe',bundle/'Abschluss.exe')
copy(cockpit/'abschluss.pmp',bundle/'abschluss.pmp')
for p in (cockpit/'lib').glob('*'):
    if p.is_file() and p.suffix in {'.pmp','.manifest'}:copy(p,bundle/'lib'/p.name)
for name in ['pompetzki.exe','pompetzki-w.exe']:copy(runtime/name,bundle/name)
copy(distribution/'judge-rkt.exe',bundle/'judge-rkt.exe')
for folder in ['lib','collects']:
    # Root judge-rkt uses the same distributed support layout as the root launcher.
    if (distribution/folder).exists() and not (bundle/folder).exists():shutil.copytree(distribution/folder,bundle/folder)
for name in ['judge-v6.pmp','judge-v6.rkt','registry-auth-v4.rkt','REG0-canonical.jdg','REGISTRY-AUTH-v4.md']:
    copy(REPO/'judge'/name,bundle/'judge'/name)
for p,row in reviewed_support('judge_fixtures'):
    copy(p,bundle/row['package_relative_path'])
copy(native,bundle/'judge'/'judge-v6-windows.exe')
copy(native_receipt,bundle/'provenance'/'JUDGE-V6-FREEZE-RECEIPT.json')
copy(native_provenance_path,bundle/'provenance'/'native-v6-PROVENANCE.json')
for name in ['native-test-result.json','native-provenance.json']:
    if (options.native_dir/name).exists():copy(options.native_dir/name,bundle/'provenance'/name)
for name in ['native-rebuild-comparison.json','cockpit-portable-changes.json']:
    if (OUT/name).exists():copy(OUT/name,bundle/'provenance'/name)
(bundle/'provenance'/'package-components.json').write_text(json.dumps(receipt,indent=2))
for p,row in reviewed_support('certificates'):
    copy(p,bundle/row['package_relative_path'])
for p,row in reviewed_support('libraries'):
    relative=Path(row['package_relative_path']).relative_to('repair/libraries')
    if relative.parts[0]=='strx':copy(p,bundle/'tools'/relative)
copy(HERE/'Uninstall-Abschluss.ps1',bundle/'Uninstall-Abschluss.ps1')
(bundle/'VERSION').write_text(VERSION+'\n',encoding='utf-8')
(bundle/'VERSION.txt').write_text(VERSION+'\n',encoding='utf-8')
(bundle/'config').mkdir(exist_ok=True)
(bundle/'config'/'config-20261011000000.txt').write_text('; Portable Abschluss 1.3.1 configuration\npompetzki .\nproject Mathematics\npmp examples\n',encoding='utf-8')
guide='''# Abschluss 1.3.1\n\nDouble-click Abschluss Start.exe to open Math Workbench. Enter integer or rational matrix entries in A and B, choose the mathematical operation, and click Compute. The complete result appears in Answer. Decimal input is rejected.\n\nRun Abschluss Start.exe --menu to open the launcher controls. They open the cockpit, judge a certificate with the authenticated pmp judge and the independent Racket cross-check, verify the Book, create a verified posting, and check installed file hashes.\n\nRun Install Abschluss.exe to install into a new local folder. The CLI supports --target DIRECTORY and --no-shortcut. Existing targets and reparse directory parents are refused. Run Uninstall Abschluss.exe from the installation folder to remove unchanged recorded program files. Additional and modified files remain.\n\nThe Racket runtime and required DLLs are included. Racket is not required as a separate installation.\n'''
guide+='\nVerify a posting checks the new BOOK-1.0.ledger and NEGATIVE-1.0.ledger chains, their bound run metadata, copied inputs and outputs, and both current judge results. Verify historical Book checks the older book/J*.txt chains. These controls use separate checkers.\n'
(bundle/'docs'/'1.3.1').mkdir(parents=True,exist_ok=True);(bundle/'docs'/'1.3.1'/'USER-GUIDE.md').write_text(guide,encoding='utf-8')
for name in ['README.md','fresh-gate-proof-result.json','gate-types-and-assumptions.txt','kernel-check-context.txt','source-credit.json','run-output.txt']:
    copy(REPO/'repair'/'grok-proof-integrated'/'public'/name,bundle/'docs'/'proof-gate'/name)
(bundle/'README.md').write_text(guide,encoding='utf-8')
copy(options.release_notes,bundle/'docs'/'1.3.1'/'RELEASE-1.3.1.md')
(bundle/'book'/'verify-book.cmd').write_text('@echo off\n"%~dp0..\\bin\\bookverify.exe" "%~dp0."\nexit /b %ERRORLEVEL%\n',encoding='utf-8')
for p in (RACO.parent/'share').glob('LICENSE*.txt'):copy(p,bundle/'licenses'/'Racket'/p.name)
manifest=bundle/'MANIFEST.sha256'
files=sorted(p for p in bundle.rglob('*') if p.is_file())
manifest.write_text(''.join(sha(p)+'  '+p.relative_to(bundle).as_posix()+'\n' for p in files),encoding='utf-8')
command('bundle-version',[bundle/'Abschluss Start.exe','--version'],OUT)
command('bundle-manifest',[bundle/'Abschluss Start.exe','--verify-install'],OUT)

source_root=OUT/'Abschluss-1.3.1-source';source_root.mkdir()
whitelist=options.source_map or REPO/'PUBLIC-SOURCE-WHITELIST.json'
if not whitelist.exists():whitelist=REPO/'judge'/'PUBLIC-SOURCE-WHITELIST-v6-runtime-v2-coherent.json'
if not whitelist.exists():raise RuntimeError('--source-map is required for the candidate checkout')
approved=json.loads(whitelist.read_text())
if not any(item['package_relative_path']=='judge/judge-v6.pmp' for item in approved['files']):raise RuntimeError('Source map does not contain the selected v6 judge')
runtime_source=next(item for item in approved['files'] if item['package_relative_path']=='runtime/source/pompetzki.asm')
runtime_build=json.loads((runtime/'build-receipt.json').read_text())
if runtime_source['sha256']!=runtime_build['source_sha256']:raise RuntimeError('Mapped interpreter source differs from the actually built interpreter source')
for item in approved['files']:
    original=REPO/item['candidate_relative_path']
    if not original.exists():original=REPO/item['package_relative_path']
    if sha(original)!=item['sha256']:raise RuntimeError('Whitelisted source hash changed: '+str(original))
    copy(original,source_root/item['package_relative_path'])
copy(whitelist,source_root/'PUBLIC-SOURCE-WHITELIST.json')
copy(whitelist,source_root/'judge'/'PUBLIC-SOURCE-WHITELIST-v6-runtime-v2-coherent.json')
copy(REPO/'judge'/'REGISTRY-AUTH-v4.md',source_root/'judge'/'REGISTRY-AUTH-v4.md')
for p,row in reviewed_support('registry_fixtures'):
    copy(p,source_root/row['package_relative_path'])
shutil.copytree(cockpit,source_root/'cockpit')
for directory in [options.book_dir.name,'math-workbench-v2','packaging']:
    dest=source_root/'repair'/directory
    original=REPO/'repair'/directory
    if directory=='packaging':
        packaging_approved=json.loads((HERE/'PUBLIC-SOURCE-MANIFEST.json').read_text())
        packaging_sources=[HERE/row['path'] for row in packaging_approved['files']]
        for row,p in zip(packaging_approved['files'],packaging_sources):
            if sha(p)!=row['sha256']:raise RuntimeError('Frozen packaging source changed: '+row['path'])
        packaging_manifest={'version':VERSION,'status':'Frozen public packaging source','files':[
            {'path':p.name,'candidate_relative_path':p.relative_to(REPO).as_posix(),
             'package_relative_path':'repair/packaging/v9-judge-v6-1.3.1/'+p.name,'sha256':sha(p)}
            for p in packaging_sources]}
        manifest_bytes=(json.dumps(packaging_manifest,indent=2)+'\n').encode()
        (OUT/'PUBLIC-PACKAGING-SOURCE-MANIFEST.json').write_bytes(manifest_bytes)
        target=dest/'v9-judge-v6-1.3.1';target.mkdir(parents=True)
        (target/'PUBLIC-SOURCE-MANIFEST.json').write_bytes(manifest_bytes)
        for p in packaging_sources:copy(p,target/p.name)
    else:
        if directory==options.book_dir.name:
            original=options.book_dir
            book_manifest=original/'PUBLIC-SOURCE-MANIFEST.json'
            book_approved=json.loads(book_manifest.read_text())
            if not book_approved['files']:raise RuntimeError('Empty explicit Book source manifest')
            copy(book_manifest,dest/'PUBLIC-SOURCE-MANIFEST.json')
            for row in book_approved['files']:
                path=original/row['path']
                if sha(path)!=row['sha256']:raise RuntimeError('Frozen Book source changed: '+str(path))
                copy(path,dest/row['path'])
            for path in (original/'registry-tests').glob('*.jdg'):copy(path,dest/'registry-tests'/path.name)
        if directory=='math-workbench-v2':
            copy(math_manifest,dest/'PUBLIC-SOURCE-MANIFEST.json')
            copy(original/'SHA256SUMS-source.txt',dest/'SHA256SUMS-source.txt')
            for row in math_approved['files']:
                path=original/row['path']
                if sha(path)!=row['sha256']:raise RuntimeError('Frozen matrix source changed during archive assembly: '+str(path))
                copy(path,dest/row['path'])
for section in ['libraries','oracles','certificates','judge_fixtures']:
    for p,row in reviewed_support(section):copy(p,source_root/row['package_relative_path'])
copy(archive,source_root/'vendor'/archive.name)
(source_root/'vendor'/'SHA256SUMS-base.txt').write_text(sha(archive)+'  '+archive.name+'\n',encoding='utf-8')
copy(options.native_dir/'judge-v6-windows.exe',source_root/'vendor'/'gated-native'/'judge-v6-windows.exe')
copy(native_receipt,source_root/'vendor'/'gated-native'/'JUDGE-V6-FREEZE-RECEIPT.json')
copy(native_provenance_path,source_root/'vendor'/'gated-native'/'PROVENANCE.json')
for name in ['native-test-result.json','native-provenance.json']:
    if (options.native_dir/name).exists():copy(options.native_dir/name,source_root/'vendor'/'gated-native'/name)
copy(REPO/'LICENSE',source_root/'LICENSE')
copy(options.release_notes,source_root/'RELEASE-1.3.1.md')
(source_root/'repair'/options.book_dir.name/'tests').mkdir(exist_ok=True)
(source_root/'repair'/options.book_dir.name/'tests'/'.keep').write_text('Fresh test outputs are created beside the included test drivers.\n')
proof=REPO/'repair'/'grok-proof-integrated'/'public'
proof_whitelist=proof/'PUBLIC-WHITELIST.json'
proof_approved=json.loads(proof_whitelist.read_text())
if len(proof_approved['files'])!=31:raise RuntimeError('Expected 31 reviewed proof content files')
for row in proof_approved['files']:
    path=proof/row['path']
    if sha(path)!=row['sha256']:raise RuntimeError('Reviewed proof source changed: '+str(path))
    copy(path,source_root/'repair'/'grok-proof-integrated'/'public'/row['path'])
for name in ['PUBLIC-WHITELIST.json','SHA256SUMS.txt']:copy(proof/name,source_root/'repair'/'grok-proof-integrated'/'public'/name)
matrix_manifest=json.loads((HERE/'MATRIX-SOURCE-MANIFEST.json').read_text())
for row in matrix_manifest['files']:
    path=REPO/'repair'/'bot-matrix-validation'/row['path']
    if sha(path)!=row['sha256']:raise RuntimeError('Frozen matrix oracle source changed: '+str(path))
    copy(path,source_root/'repair'/'bot-matrix-validation'/row['path'])
validation=REPO/'judge'/'validation-v5'
validation_manifest=validation/'SOURCE-INPUTS.json'
validation_approved=json.loads(validation_manifest.read_text())
if validation_approved['file_count']!=1499 or len(validation_approved['files'])!=1499:raise RuntimeError('Expected 1499 reviewed validation payloads')
for row in validation_approved['files']:
    path=REPO/row['candidate_relative_path']
    if not path.exists():path=REPO/row['package_relative_path']
    if sha(path)!=row['sha256']:raise RuntimeError('Reviewed validation payload changed: '+str(path))
    copy(path,source_root/row['package_relative_path'])
for name in ['SOURCE-INPUTS.json','PUBLIC-AUDIT.json','SHA256SUMS.txt']:copy(validation/name,source_root/'judge'/'validation-v5'/name)
resource=REPO/'judge'/'validation-v6-resource'
resource_manifest=resource/'PUBLIC-SOURCE-MANIFEST.json'
resource_approved=json.loads(resource_manifest.read_text())
if len(resource_approved['files'])!=1932:raise RuntimeError('Expected 1932 reviewed v6 resource validation payloads')
for row in resource_approved['files']:
    path=resource/row['path']
    if sha(path)!=row['sha256']:raise RuntimeError('Reviewed v6 validation payload changed: '+row['path'])
    copy(path,source_root/'judge'/'validation-v6-resource'/row['path'])
for name in ['PUBLIC-SOURCE-MANIFEST.json','SHA256SUMS.txt']:
    copy(resource/name,source_root/'judge'/'validation-v6-resource'/name)
for p,row in reviewed_support('v6_resource_controls'):copy(p,source_root/row['package_relative_path'])

def zipped(root,name):
    output=OUT/name
    with zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in sorted(root.rglob('*')):
            if p.is_file():
                info=zipfile.ZipInfo((Path(root.name)/p.relative_to(root)).as_posix(),date_time=(2026,10,11,0,0,0))
                info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16;z.writestr(info,p.read_bytes())
    return output
assets=[zipped(bundle,'Abschluss-1.3.1-windows-x64.zip'),zipped(source_root,'Abschluss-1.3.1-source.zip')]
(OUT/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in assets),encoding='utf-8')
receipt.update(release_assets_created=True,bundle=str(bundle),manifest_files=len(files),assets={p.name:sha(p) for p in assets})
(OUT/'build-receipt.json').write_text(json.dumps(receipt,indent=2))
print('Release candidate assembled:',OUT,flush=True)
