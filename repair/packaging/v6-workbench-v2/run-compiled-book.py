"""Snapshot the frozen Book tests and exercise the distributed executables."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,required=True)
parser.add_argument('--bundle',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--racket',default='racket')
args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
source_dir=out/'source'/'repair'/'book-v6';source_dir.mkdir(parents=True)
dependency=out/'source'/'judge';dependency.mkdir()
for name in ['registry-auth-v4.rkt','REG0-canonical.jdg']:shutil.copy2(args.bundle/'judge'/name,dependency/name)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((args.source/'PUBLIC-SOURCE-MANIFEST.json').read_text())
for row in manifest['files']:
    source=args.source/row['path'];assert sha(source)==row['sha256'],source
    shutil.copy2(source,source_dir/row['path'])
shutil.copytree(args.source/'registry-tests',source_dir/'registry-tests')
(source_dir/'tests').mkdir()
adaptations=[]
for name in ['test-review-v6.py','test-adversarial.py']:
    original=source_dir/name;text=original.read_text()
    for base in ['HERE','here']:
        for role in ['post','check']:
            before=f"args.racket,str({base}/'verified-book-{role}.rkt'),"
            after=f"str(args.bundle/'bin'/'verified-book-{role}.exe'),"
            text=text.replace(before,after)
    target=source_dir/(name.replace('.py','-compiled.py'));target.write_text(text)
    adaptations.append({'original':name,'original_sha256':sha(original),'variant':target.name,'variant_sha256':sha(target),
                        'change':'Poster/checker process entry points use the distributed .exe; fixture generator and expectations remain unchanged'})
commands=[]
for name,argv in [
    ('posting',[sys.executable,str(source_dir/'test-verified-book-v4.py'),'--bundle',str(args.bundle),'--poster',str(args.bundle/'bin/verified-book-post.exe')]),
    ('checking',[sys.executable,str(source_dir/'test-verified-check.py'),'--bundle',str(args.bundle),'--poster',str(args.bundle/'bin/verified-book-post.exe'),'--checker',str(args.bundle/'bin/verified-book-check.exe')]),
    ('review',[sys.executable,str(source_dir/'test-review-v6-compiled.py'),'--bundle',str(args.bundle),'--racket',args.racket]),
    ('adversarial',[sys.executable,str(source_dir/'test-adversarial-compiled.py'),'--bundle',str(args.bundle),'--racket',args.racket]),
    ('full-replay',[sys.executable,str(source_dir/'test-full-replay.py'),'--bundle',str(args.bundle),'--poster',str(args.bundle/'bin/verified-book-post.exe'),'--checker',str(args.bundle/'bin/verified-book-check.exe')])]:
    process=subprocess.run(argv,cwd=out,capture_output=True,timeout=300,creationflags=subprocess.CREATE_NO_WINDOW)
    (out/(name+'.stdout.txt')).write_bytes(process.stdout);(out/(name+'.stderr.txt')).write_bytes(process.stderr)
    commands.append({'case':name,'command':argv,'exit':process.returncode})
    (out/'progress.json').write_text(json.dumps({'commands':commands,'adaptations':adaptations},indent=2))
    assert process.returncode==0,(name,process.returncode,process.stderr)
    print(name,process.stdout.decode(errors='replace').strip(),flush=True)
(out/'results.json').write_text(json.dumps({'passed':True,'commands':commands,'adaptations':adaptations},indent=2))
(out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.relative_to(out).as_posix()+'\n' for p in sorted(out.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
