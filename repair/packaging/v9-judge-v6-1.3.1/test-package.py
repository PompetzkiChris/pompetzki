"""Fresh-directory tests of distributed exact mathematics and installation."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, shutil, subprocess, time, zipfile

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--fixtures',type=Path,required=True)
    parser.add_argument('--jobs',type=Path,required=True)
    parser.add_argument('--expected',type=Path,required=True)
    options=parser.parse_args();out=options.output.resolve();out.mkdir(parents=True,exist_ok=False)
    logs=out/'logs';logs.mkdir();outside=out/'unrelated-working-directory';outside.mkdir()
    temp=out/'temp';temp.mkdir()
    env=os.environ.copy();windows=os.environ['SystemRoot'];env['PATH']=str(Path(windows)/'System32')+';'+windows
    env['TEMP']=env['TMP']=str(temp)
    appdata=out/'owned-appdata';appdata.mkdir();env['APPDATA']=str(appdata)
    empty=out/'empty-collects';empty.mkdir();env['PLTCOLLECTS']=env['PLTADDONDIR']=str(empty)
    results=[];commands=[]
    def check(name,condition,detail=None):
        results.append({'case':name,'pass':bool(condition),'detail':detail})
        (out/'results-progress.json').write_text(json.dumps(results,indent=2))
        if not condition:raise AssertionError(name+': '+str(detail))
    def run(name,command,expected=0,timeout=180):
        began=time.monotonic();p=subprocess.run(list(map(str,command)),cwd=outside,env=env,capture_output=True,
                                                timeout=timeout,creationflags=subprocess.CREATE_NO_WINDOW)
        (logs/(name+'.stdout.txt')).write_bytes(p.stdout);(logs/(name+'.stderr.txt')).write_bytes(p.stderr)
        commands.append({'name':name,'command':list(map(str,command)),'cwd':str(outside),'exit':p.returncode,
                         'seconds':time.monotonic()-began,'stdout_sha256':sha(logs/(name+'.stdout.txt')),
                         'stderr_sha256':sha(logs/(name+'.stderr.txt'))})
        (out/'commands.json').write_text(json.dumps(commands,indent=2))
        check(name+' exit',p.returncode==expected,{'exit':p.returncode,'expected':expected,'stderr':p.stderr.decode(errors='replace')[:500]})
        return p
    extracted=out/'fresh-unzip';extracted.mkdir()
    with zipfile.ZipFile(options.build/'Abschluss-1.3.1-windows-x64.zip') as z:
        for row in z.infolist():
            path=Path(row.filename)
            if path.is_absolute() or '..' in path.parts:raise AssertionError('Unsafe archive path')
        z.extractall(extracted)
    bundle=extracted/'Abschluss-1.3.1';launcher=bundle/'Abschluss Start.exe'
    original={p.relative_to(bundle).as_posix():sha(p) for p in bundle.rglob('*') if p.is_file()}
    check('version in fresh ZIP',(bundle/'VERSION').read_text(encoding='utf-8').strip()=='1.3.1')
    check('native cockpit has no author ClaudeOutput path',b'C:/ClaudeOutput' not in (bundle/'Abschluss.exe').read_bytes())
    version=run('unpacked-version',[launcher,'--version'])
    check('unpacked version output',version.stdout.strip()==b'1.3.1')
    manifest=json.loads(run('unpacked-manifest',[launcher,'--verify-install']).stdout)
    check('all unpacked manifest files match',all(row['match'] for row in manifest),{'files':len(manifest)})
    for mode in ['pompetzki.exe','pompetzki-w.exe']:
        for op,want in [('div','-9223372036854775808'),('mod','0')]:
            stem=Path(mode).stem+'-'+op
            program=out/(stem+'.pmp')
            program.write_text('trace off\nset X '+op+' -9223372036854775808 -1\ntext S int X\nprint S\n')
            result=run('word-boundary-'+stem,[bundle/mode,program])
            check('Word64 MIN/-1 '+stem,result.stdout.strip()==want.encode(),result.stdout.decode(errors='replace'))
            emitted=out/(stem+'.exe')
            run('word-emit-'+stem,[bundle/mode,'emit',program,emitted])
            emitted_result=run('word-emitted-'+stem,[emitted])
            check('emitted Word64 MIN/-1 '+stem,emitted_result.stdout.strip()==want.encode(),emitted_result.stdout.decode(errors='replace'))
    listing=run('unpacked-routes',[launcher,'--list']).stdout.decode()
    check('corrected default and v6 posting/judge routes','bin/MathWorkbench.exe' in listing.replace('\\','/') and 'judge/judge-v6.pmp' in listing.replace('\\','/') and 'verified-book-check.exe' in listing and 'JudgeDrop' not in listing,listing)
    fixture_dir=out/'fixtures';fixture_dir.mkdir()
    for name in ['prefix-0-truth.jdg','false-proof-empty-registry.jdg','forged-false-registry.jdg']:
        shutil.copy2(options.fixtures/name,fixture_dir/name)
        want=0 if name=='prefix-0-truth.jdg' else 1
        result=json.loads(run('judge-'+Path(name).stem,[launcher,'--judge',fixture_dir/name],want).stdout)
        check('both judges agree on '+name,result['verdict']==('ACCEPT' if want==0 else 'REJECT'),result)
    ui_receipt=out/'launcher-controls.json'
    run('launcher-owned-controls',[launcher,'--ui-selftest',ui_receipt,'--fixture',fixture_dir/'prefix-0-truth.jdg'])
    ui=json.loads(ui_receipt.read_text(encoding='utf-8'))
    check('launcher actual callbacks fill Answer',len(ui['runs'])==3 and all(row['answer']==row['callback_result'] for row in ui['runs']),ui)
    math_out=out/'math-owned-controls'
    run('math-owned-controls',[bundle/'bin'/'MathWorkbench.exe','--ui-selftest',math_out])
    math=json.loads((math_out/'results.json').read_text(encoding='utf-8'))
    check('eight distributed Math Workbench callbacks and overwrite refusal',math['cases']==8 and math['passed'],math)
    check('actual loaded Racket and GUI DLLs come from the fresh bundle',
          any('racket' in row['module'].lower() for row in math['runtime_modules'])
          and all(Path(row['path']).is_relative_to(bundle) for row in math['runtime_modules']),math['runtime_modules'])
    jobs=out/'jobs.json';expected=json.loads(options.expected.read_text(encoding='utf-8'));shutil.copy2(options.jobs,jobs)
    batch=run('exact-engine-849',[bundle/'bin'/'MathEngine.exe','--batch',jobs])
    actual=json.loads(batch.stdout);mismatches=[]
    for row in actual:
        for field,value in expected[row['id']].items():
            if row['machine'].get(field)!=value:mismatches.append({'id':row['id'],'field':field,'expected':value,'actual':row['machine'].get(field)})
    check('distributed engine independent Fraction oracle',len(actual)==len(expected)==849 and not mismatches,{'cases':len(actual),'mismatches':mismatches})
    posting=out/'verified-posting'
    run('book-post-standalone',[bundle/'bin'/'verified-book-post.exe','--bundle',bundle,posting,'2026-10-12',fixture_dir/'prefix-0-truth.jdg'])
    verification=run('book-check-standalone',[bundle/'bin'/'verified-book-check.exe','--bundle',bundle,posting])
    check('current posting verification output',b'CHECK OK' in verification.stdout)
    relocated=out/'posting-relocated';shutil.copytree(posting,relocated)
    run('book-check-relocated',[bundle/'bin'/'verified-book-check.exe','--bundle',bundle,relocated])
    installed=out/'installed-cli'
    install=run('install-cli',[bundle/'Install Abschluss.exe','--target',installed,'--no-shortcut'])
    record=json.loads((installed/'INSTALLATION.json').read_text(encoding='utf-8'))
    check('installation records exactly manifest plus manifest file',len(record['files'])==len(manifest)+1 and record['shortcut'] is False,{'recorded_files':len(record['files'])})
    run('installed-manifest',[installed/'Abschluss Start.exe','--verify-install'])
    run('installed-math-owned-controls',[installed/'bin'/'MathWorkbench.exe','--ui-selftest',out/'installed-math-controls'])
    installed_math=json.loads((out/'installed-math-controls'/'results.json').read_text(encoding='utf-8'))
    check('actual installed GUI runtime loads installed DLLs',
          any('racket' in row['module'].lower() for row in installed_math['runtime_modules'])
          and all(Path(row['path']).is_relative_to(installed) for row in installed_math['runtime_modules']),installed_math['runtime_modules'])
    sentinel=installed/'user-proof.txt';sentinel.write_bytes(b'user-owned exact mathematics\r\n')
    before=sha(sentinel)
    run('existing-target-refused',[bundle/'Install Abschluss.exe','--target',installed,'--no-shortcut'],2)
    check('existing target and user file preserved',sha(sentinel)==before)
    installed_ui=out/'installed-gui'
    installer_receipt=out/'installer-controls.json'
    run('installer-owned-controls',[bundle/'Install Abschluss.exe','--target',installed_ui,'--no-shortcut','--ui-selftest',installer_receipt])
    inst_ui=json.loads(installer_receipt.read_text(encoding='utf-8'))
    check('actual Install button fills Answer',inst_ui['result']['status']=='INSTALLED' and 'installed in' in inst_ui['answer'],inst_ui)
    run('gui-installed-manifest',[installed_ui/'Abschluss Start.exe','--verify-install'])
    junction_dest=out/'junction-destination';junction_dest.mkdir();junction=out/'junction-parent'
    ps=Path(windows)/'System32'/'WindowsPowerShell'/'v1.0'/'powershell.exe'
    script="New-Item -ItemType Junction -Path '"+str(junction).replace("'","''")+"' -Target '"+str(junction_dest).replace("'","''")+"' | Out-Null"
    run('create-owned-junction',[ps,'-NoProfile','-NonInteractive','-WindowStyle','Hidden','-Command',script])
    run('reparse-parent-refused',[bundle/'Install Abschluss.exe','--target',junction/'new-install','--no-shortcut'],2)
    check('reparse refusal creates no installation',not (junction_dest/'new-install').exists())
    dry=json.loads(run('uninstall-dry-run',[installed/'Uninstall Abschluss.exe','--dry-run']).stdout)
    check('dry run lists recorded files only',len(dry)==len(record['files']))
    modified=installed/'config'/'config-20261011000000.txt';modified.write_bytes(b'; user config\r\nproject Mine\r\n')
    modified_sha=sha(modified)
    removal=run('uninstall-recorded-cli',[installed/'Uninstall Abschluss.exe'])
    deadline=time.monotonic()+60
    while (installed/'INSTALLATION.json').exists() and time.monotonic()<deadline:time.sleep(0.25)
    check('native uninstall scheduled helper completed',not (installed/'INSTALLATION.json').exists(),removal.stdout.decode(errors='replace'))
    check('uninstall preserves user files and modified config',sha(sentinel)==before and sha(modified)==modified_sha)
    check('uninstall removes unchanged listed applications',not (installed/'Abschluss Start.exe').exists() and not (installed/'bin'/'MathWorkbench.exe').exists())
    extra=installed_ui/'user-extra';extra.mkdir();(extra/'theorem.txt').write_bytes(b'exact Q evidence\r\n')
    run('uninstall-helper-direct',[ps,'-NoProfile','-NonInteractive','-WindowStyle','Hidden','-ExecutionPolicy','Bypass','-File',installed_ui/'Uninstall-Abschluss.ps1','-InstallRoot',installed_ui])
    check('direct uninstall preserves extra nested file',(extra/'theorem.txt').read_bytes()==b'exact Q evidence\r\n')
    shortcut_install=out/'installed-shortcut'
    run('install-with-owned-shortcut',[bundle/'Install Abschluss.exe','--target',shortcut_install])
    shortcut_record=json.loads((shortcut_install/'INSTALLATION.json').read_text(encoding='utf-8'))
    link=Path(shortcut_record['shortcut'])
    check('shortcut created only in owned APPDATA',link.is_relative_to(appdata) and link.is_file() and sha(link)==shortcut_record['shortcut_sha256'])
    shortcut_script="$shortcut=(New-Object -ComObject WScript.Shell).CreateShortcut('"+str(link).replace("'","''")+"'); [pscustomobject]@{Target=$shortcut.TargetPath;Directory=$shortcut.WorkingDirectory} | ConvertTo-Json"
    link_data=json.loads(run('shortcut-target',[ps,'-NoProfile','-NonInteractive','-WindowStyle','Hidden','-Command',shortcut_script]).stdout)
    check('shortcut resolves relocated default launcher',Path(link_data['Target'])==shortcut_install/'Abschluss Start.exe' and Path(link_data['Directory'])==shortcut_install,link_data)
    run('uninstall-owned-shortcut',[ps,'-NoProfile','-NonInteractive','-WindowStyle','Hidden','-ExecutionPolicy','Bypass','-File',shortcut_install/'Uninstall-Abschluss.ps1','-InstallRoot',shortcut_install])
    check('recorded owned shortcut removed',not link.exists())
    after={p.relative_to(bundle).as_posix():sha(p) for p in bundle.rglob('*') if p.is_file()}
    check('unpacked source bundle remained byte identical',after==original,{'files':len(original)})
    source=out/'fresh-source';source.mkdir()
    with zipfile.ZipFile(options.build/'Abschluss-1.3.1-source.zip') as z:z.extractall(source)
    source_root=source/'Abschluss-1.3.1-source'
    check('complete interpreter and native assembly source included',(source_root/'runtime'/'source'/'pompetzki.asm').is_file() and (source_root/'judge'/'native-v6'/'portable'/'linux-runtime.asm').is_file())
    check('public active recipes avoid historical author-path drivers',not (source_root/'repair'/'runtime'/'build-monolithic.py').exists() and not (source_root/'judge'/'native'/'build-gated-native.py').exists())
    approved=json.loads((source_root/'PUBLIC-SOURCE-WHITELIST.json').read_text(encoding='utf-8'))
    check('all frozen source mappings match',len(approved['files'])>=81 and all(sha(source_root/row['package_relative_path'])==row['sha256'] for row in approved['files']),{'files':len(approved['files'])})
    report={'checks':len(results),'passed':sum(row['pass'] for row in results),'failures':[r for r in results if not r['pass']],
            'exact_engine_cases':len(actual),'math_gui_cases':8,'manifest_files':len(manifest),'results':results,'commands':commands,
            'environment':{'PATH':env['PATH'],'PLTCOLLECTS':env['PLTCOLLECTS'],'working_directory':str(outside)},
            'gui_test_scope':'Actual controls in owned hidden windows; no simulated keys, focus changes, or physical click claim'}
    (out/'results.json').write_text(json.dumps(report,indent=2))
    (out/'SHA256SUMS-evidence.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS-evidence.txt'))
    print(json.dumps({'output':str(out),'checks':len(results),'passed':report['passed'],'exact_cases':len(actual)}))

if __name__=='__main__':main()
