"""Post and independently rejudge the unchanged 4,551-theorem replay."""
import argparse,hashlib,json,pathlib,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--bundle',type=pathlib.Path,required=True);ap.add_argument('--racket',default='racket');ap.add_argument('--poster',type=pathlib.Path);ap.add_argument('--checker',type=pathlib.Path);args=ap.parse_args()
HERE=pathlib.Path(__file__).resolve().parent;OUT=HERE/'tests'/('full-replay-'+time.strftime('%Y%m%d-%H%M%S'));OUT.mkdir(parents=True,exist_ok=False)
expected='a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae'
inputs=[p for p in args.bundle.rglob('replay-all.jdg') if hashlib.sha256(p.read_bytes()).hexdigest()==expected];assert inputs,'unchanged released replay-all.jdg was not found'
poster=args.poster or HERE/'verified-book-post.rkt';checker=args.checker or HERE/'verified-book-check.rkt'
prefix=lambda path:[str(path)] if path.suffix.lower()=='.exe' else [args.racket,str(path)]
posting=OUT/'posting';results=[]
for name,command in [('post',prefix(poster)+['--bundle',str(args.bundle),'--timeout','30',str(posting),'2026-10-11 EDT',str(inputs[0])]),('check',prefix(checker)+['--bundle',str(args.bundle),'--timeout','30',str(posting)])]:
    start=time.monotonic_ns();p=subprocess.run(command,capture_output=True,timeout=180)
    (OUT/(name+'.stdout.txt')).write_bytes(p.stdout);(OUT/(name+'.stderr.txt')).write_bytes(p.stderr)
    assert p.returncode==0,(name,p.returncode,p.stderr)
    results.append({'case':name,'exit':p.returncode,'elapsed_ms':(time.monotonic_ns()-start)//1000000,'command':command})
report=json.loads((OUT/'check.stdout.txt').read_text());assert (report['files'],report['positive_files'],report['theorems'],report['negative_files'])==(1,1,4551,0)
book=(posting/'BOOK-1.0.ledger').read_text().splitlines();B=[r.split('\t') for r in book if r.startswith('B')]
assert len(B)==4551 and sum(r[4]=='Proved' for r in B)==4373 and sum(r[4]=='Qualified' for r in B)==178 and sum(int(r[7][6:]) for r in B)==139194
result={'passed':True,'files':1,'theorems':4551,'proved':4373,'qualified':178,'steps':139194,'input_sha256':expected,'results':results}
(OUT/'results.json').write_text(json.dumps(result,indent=2));(OUT/'SHA256SUMS.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+' *'+p.relative_to(OUT).as_posix()+'\n' for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(OUT),'passed':True,'theorems':4551,'proved':4373,'qualified':178,'steps':139194}))
