"""Reproduce the v4 evidence attacks against the correcting v5 verifier."""
import argparse,hashlib,json,pathlib,re,shutil,subprocess,time
ap=argparse.ArgumentParser();ap.add_argument('--bundle',type=pathlib.Path,required=True);ap.add_argument('--racket',default=r'C:\Program Files\Racket\racket.exe');args=ap.parse_args()
HERE=pathlib.Path(__file__).resolve().parent;OUT=HERE/'tests'/('review-v5-'+time.strftime('%Y%m%d-%H%M%S'));OUT.mkdir(parents=True,exist_ok=False)
REVIEW=OUT/'fixtures';REVIEW.mkdir();BASE=OUT/'original-posting';INPUTS=OUT/'inputs';INPUTS.mkdir();results=[]
for name,body in {'true.jdg':'JDG1 R 0 T 1 a q 0 0 0 2 Y q 0 0 G 0 0 0\n','true-leading-zeros.jdg':'JDG1 R 00 T 01 a q 00 00 00 02 Y q 00 00 G 00 00 00\n','false-step.jdg':'JDG1 R 0 T 1 a n q 0 0 0 1 Y a n q 0 0 0\n','false-registry.jdg':'JDG1 R 1 a n q 0 0 0 T 1 a n q 0 0 0 1 U 0 0 0\n'}.items():(INPUTS/name).write_text(body)
p=subprocess.run([args.racket,str(HERE/'verified-book-post.rkt'),'--bundle',str(args.bundle),str(BASE),'2026-10-11 EDT',str(INPUTS)],capture_output=True,timeout=60,creationflags=subprocess.CREATE_NO_WINDOW)
(OUT/'create-baseline.stdout.txt').write_bytes(p.stdout);(OUT/'create-baseline.stderr.txt').write_bytes(p.stderr);assert p.returncode==0,p.stderr
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def readrows(p):return [l.split('\t')[:-1] for l in p.read_text().splitlines()]
def rechain(path,rs):
    head='0'*64;lines=[]
    for row in rs:
        body='\t'.join(row);head=hashlib.sha256((head+'\n'+body).encode()).hexdigest();lines.append(body+'\t'+head)
    path.write_text('\n'.join(lines)+'\n')
def rebind(folder,meta):
    (folder/'run-metadata.json').write_text(json.dumps(meta));digest=sha(folder/'run-metadata.json')
    for filename in ['BOOK-1.0.ledger','NEGATIVE-1.0.ledger']:
        rs=readrows(folder/filename);i=next(i for i,v in enumerate(rs[0]) if v.startswith('run-metadata.json '));rs[0][i]='run-metadata.json '+digest;rechain(folder/filename,rs)
def portable_name(path):return str(path).replace('\\','/').split('/')[-1]
def change(folder,name):
    meta=json.loads((folder/'run-metadata.json').read_text());path=folder/'BOOK-1.0.ledger';rs=readrows(path)
    if name=='metadata-false-artifact-hash':meta['artifacts'][0]['sha256']='f'*64;rebind(folder,meta)
    elif name=='metadata-inexact-backwards-times':
        for run in meta['runs']:
            for judge in ['pmp','racket']:run[judge]['start_epoch_ms']=10.5;run[judge]['end_epoch_ms']=-999
        rebind(folder,meta)
    elif name=='metadata-ambiguous-output':
        run=next(r for r in meta['runs'] if r['pmp']['verdict']=='ACCEPT')
        for judge in ['pmp','racket']:
            p=folder/'judge-runs'/portable_name(run[judge]['stdout']);p.write_text('ACCEPT REJECT\n');run[judge]['stdout_sha256']=sha(p)
        rebind(folder,meta)
    elif name in ['duplicate-receipt-row','contradictory-receipts']:
        p=folder/'RECEIPTS.tsv';lines=p.read_text().splitlines();p.write_text(('\n'.join(lines+[lines[1]])+'\n') if name.startswith('duplicate') else '\n'.join(lines).replace('\tACCEPT\tACCEPT\t','\tREJECT\tREJECT\t')+'\n')
    elif name=='duplicate-theorem-id':
        bs=[r for r in rs if r[0].startswith('B')];bs[1][0]=bs[0][0];rechain(path,rs)
    elif name in ['fabricated-theorem-hypotheses','bad-file-byte-count','bad-file-theorem-count','bad-file-step-count']:
        prefix,value=('hyps ','999') if name.startswith('fabricated') else ({'bad-file-byte-count':('bytes ','999999'),'bad-file-theorem-count':('theorems ','999'),'bad-file-step-count':('steps ','999')}[name])
        row=next(r for r in rs if r[0].startswith('B' if name.startswith('fabricated') else 'F'));i=next(i for i,v in enumerate(row) if v.startswith(prefix));row[i]=prefix+value;rechain(path,rs)
    elif name=='fully-consistent-false-proof':
        run=next(r for r in meta['runs'] if r['pmp']['verdict']=='ACCEPT');p=folder/'judge-inputs'/portable_name(run['snapshot']);p.write_text('JDG1 R 0 T 1 a n q 0 0 0 1 Y a n q 0 0 0\n');run['input_sha256_before']=run['input_sha256_after']=sha(p);rebind(folder,meta)
    elif name=='posix-recorded-paths':
        for run in meta['runs']:
            run['snapshot']='/original/posting/judge-inputs/'+portable_name(run['snapshot'])
            for judge in ['pmp','racket']:
                for kind in ['stdout','stderr']:run[judge][kind]='/original/posting/judge-runs/'+portable_name(run[judge][kind])
        rebind(folder,meta)
    elif name=='duplicate-input-copy':shutil.copy2(next((folder/'judge-inputs').glob('*.jdg')),folder/'judge-inputs'/'unrecorded-duplicate.jdg')
    else:assert name=='relocated-control'
case_names=['relocated-control','fully-consistent-false-proof','metadata-false-artifact-hash','metadata-inexact-backwards-times','metadata-ambiguous-output','duplicate-receipt-row','contradictory-receipts','duplicate-theorem-id','fabricated-theorem-hypotheses','bad-file-byte-count','bad-file-theorem-count','bad-file-step-count','posix-recorded-paths','duplicate-input-copy']
for name in case_names:
    folder=REVIEW/name;shutil.copytree(BASE,folder);change(folder,name)
    expected=0 if name in ['relocated-control','posix-recorded-paths'] else 1
    command=[args.racket,str(HERE/'verified-book-check.rkt'),'--bundle',str(args.bundle),'--timeout','5',str(folder)]
    p=subprocess.run(command,capture_output=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
    (OUT/(name+'.stdout.txt')).write_bytes(p.stdout);(OUT/(name+'.stderr.txt')).write_bytes(p.stderr)
    results.append({'case':name,'exit':p.returncode,'expected':expected,'passed':p.returncode==expected,'command':command})
    print(name,p.returncode,'expected',expected,flush=True)
    assert p.returncode==expected,(name,p.stdout,p.stderr)

# Reconstruct complete F/B evidence from a deliberately forged ACCEPT receipt.
# The low-level unsigned writer can book it; the supported verifier must rejudge.
fake=OUT/'fully-consistent-library-forgery';(fake/'judge-inputs').mkdir(parents=True);(fake/'judge-runs').mkdir()
inputp=fake/'judge-inputs'/'1-false-proof.jdg';inputp.write_text('JDG1 R 0 T 1 a n q 0 0 0 1 Y a n q 0 0 0\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
version='v5' if (args.bundle/'judge'/'judge-v5.pmp').is_file() else 'v4'
commands={'pmp':[str(args.bundle/'judge'/('judge-'+version+'-windows.exe')),str(inputp)],'racket':[str(args.bundle/'judge-rkt.exe'),str(inputp)]}
run={'original':str(inputp),'snapshot':str(inputp),'input_sha256_before':sha(inputp),'input_sha256_after':sha(inputp),'unchanged':True}
text='ACCEPT registry 0 theorems 1 steps 1 final-registry 1\n'
for judge,begin in [('pmp',100),('racket',101)]:
    stdout=fake/'judge-runs'/(judge+'.stdout.txt');stderr=fake/'judge-runs'/(judge+'.stderr.txt');stdout.write_text(text);stderr.write_text('')
    run[judge]={'command':commands[judge],'verdict':'ACCEPT','exit_code':0,'start_epoch_ms':begin,'end_epoch_ms':begin+1,'stdout':str(stdout),'stderr':str(stderr),'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr)}
artifact_paths=[args.bundle/'judge'/('judge-'+version+'-windows.exe'),args.bundle/'judge'/('judge-'+version+'.pmp'),args.bundle/'judge'/'registry-auth-v4.rkt',args.bundle/'judge-rkt.exe']
meta={'schema':'verified-book-run-v1','time_unit':'milliseconds since Unix epoch','posting_date':'2026-10-11 EDT','timeout_seconds':5,'artifacts':[{'path':str(p),'sha256':sha(p)} for p in artifact_paths],'runs':[run]}
(fake/'run-metadata.json').write_text(json.dumps(meta))
header='path\tpmp\tracket\treceipt\tsha256\tpmp_exit\tpmp_start\tpmp_end\tpmp_ms\tpmp_out\trkt_exit\trkt_start\trkt_end\rkt_ms\trkt_out'
# Take the exact supported receipt header from the preserved baseline.
header=(REVIEW/'relocated-control'/'RECEIPTS.tsv').read_text().splitlines()[0]
clean_text=re.sub(r'[\t\r\n]+',' / ',text).strip()
columns=[str(inputp),'ACCEPT','ACCEPT',str(fake/'judge-runs'),sha(inputp),'0','100','101','1',clean_text,'0','101','102','1',clean_text]
(fake/'RECEIPTS.tsv').write_text(header+'\n'+'\t'.join(columns)+'\n')
driver=OUT/'make-forged-ledger.rkt'
quote=lambda p:json.dumps(str(p).replace('\\','/'))
driver.write_text('#lang racket/base\n(require (file '+quote(HERE/'book-post-v4.rkt')+'))\n(exit (post-receipts! '+quote(fake/'RECEIPTS.tsv')+' '+quote(fake)+' "2026-10-11 EDT" (list '+quote(inputp)+')))\n')
p=subprocess.run([args.racket,str(driver)],capture_output=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
(OUT/'forge-library.stdout.txt').write_bytes(p.stdout);(OUT/'forge-library.stderr.txt').write_bytes(p.stderr)
assert p.returncode==0 and any(l.startswith('F') for l in (fake/'BOOK-1.0.ledger').read_text().splitlines()),(p.returncode,p.stderr)
p=subprocess.run([args.racket,str(HERE/'verified-book-check.rkt'),'--bundle',str(args.bundle),str(fake)],capture_output=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
(OUT/'forge-rejudgment.stdout.txt').write_bytes(p.stdout);(OUT/'forge-rejudgment.stderr.txt').write_bytes(p.stderr)
assert p.returncode==1 and b'rerun differs from stored verdict' in p.stderr,p.stderr
results.append({'case':'complete-library-forgery-rejudged','exit':p.returncode,'expected':1,'passed':True,'low_level_booked_false_proof':True})

# Each theorem-derived field must match independently reconstructed JDG evidence.
base=REVIEW/'relocated-control'
def rechain(path,rs):
    head='0'*64;lines=[]
    for row in rs:
        body='\t'.join(row);head=hashlib.sha256((head+'\n'+body).encode()).hexdigest();lines.append(body+'\t'+head)
    path.write_text('\n'.join(lines)+'\n')
for prefix,value in [('thm ','99'),('entry ','99'),('first ','B9999999'),('cites ','R999'),('ax ','Inf'),('def ','1 8'),('hypent ','677'),('file ','f'*64),('registry ','f'*64)]:
    name='B-'+prefix.strip()+'-tamper';folder=OUT/name;shutil.copytree(base,folder);path=folder/'BOOK-1.0.ledger'
    rs=[line.split('\t')[:-1] for line in path.read_text().splitlines()];row=next(r for r in rs if r[0].startswith('B'));index=next(i for i,v in enumerate(row) if v.startswith(prefix));row[index]=prefix+value;rechain(path,rs)
    p=subprocess.run([args.racket,str(HERE/'verified-book-check.rkt'),'--bundle',str(args.bundle),str(folder)],capture_output=True,timeout=30,creationflags=subprocess.CREATE_NO_WINDOW)
    (OUT/(name+'.stdout.txt')).write_bytes(p.stdout);(OUT/(name+'.stderr.txt')).write_bytes(p.stderr);assert p.returncode==1,(name,p.stdout)
    results.append({'case':name,'exit':p.returncode,'expected':1,'passed':True})
(OUT/'results.json').write_text(json.dumps({'cases':len(results),'passed':sum(r['passed'] for r in results),'results':results},indent=2))
(OUT/'SHA256SUMS.txt').write_text(''.join(sha(p)+' *'+str(p.relative_to(OUT))+'\n' for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
print(json.dumps({'output':str(OUT),'cases':len(results),'passed':len(results)}))
