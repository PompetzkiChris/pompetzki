#!/usr/bin/env python3
"""Build the received decimal-model gap proofs from fresh source copies."""
import argparse,hashlib,json,pathlib,shutil,subprocess,tempfile,time
MODULES=(('NumericV5','DecimalSignificantV4'),('GrokNumeric','GrokNumericGaps'),('GrokNumeric','GrokNumericGapsVerify'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path);ap.add_argument('--coqc',default='coqc');ap.add_argument('--rocqchk',default='rocqchk');args=ap.parse_args()
    source=pathlib.Path(__file__).resolve().parent
    output=args.output.resolve() if args.output else pathlib.Path(tempfile.mkdtemp(prefix='numeric-gaps-'))
    if args.output:output.mkdir(parents=True,exist_ok=False)
    for group in ['NumericV5','GrokNumeric','logs']:(output/group).mkdir()
    inputs=[]
    for group,name in MODULES:
        rel=group+'/'+name+'.v';shutil.copy2(source/rel,output/rel);inputs.append({'path':rel,'sha256':sha(source/rel),'copy_sha256':sha(output/rel)})
    compiler=shutil.which(args.coqc) or args.coqc;checker=shutil.which(args.rocqchk) or args.rocqchk;commands=[];begin=time.perf_counter()
    def run(label,exe,argv):
        started=time.perf_counter();stdout=output/'logs'/(label+'.stdout.txt');stderr=output/'logs'/(label+'.stderr.txt')
        with stdout.open('wb') as so,stderr.open('wb') as se:p=subprocess.run([exe,*argv],cwd=output,stdout=so,stderr=se,timeout=600,creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0)
        commands.append({'label':label,'command':[pathlib.Path(exe).name,*argv],'exit_code':p.returncode,'seconds':round(time.perf_counter()-started,6),'stdout':'logs/'+stdout.name,'stderr':'logs/'+stderr.name});print(label,'exit',p.returncode,flush=True)
        if p.returncode:raise RuntimeError(label+' failed')
        return stdout.read_text(encoding='utf-8',errors='replace'),stderr.read_text(encoding='utf-8',errors='replace')
    version=run('compiler-version',compiler,['--version']);flags=['-Q','NumericV5','NumericV5','-Q','GrokNumeric','GrokNumeric']
    for group,name in MODULES:run('compile-'+name,compiler,[*flags,group+'/'+name+'.v'])
    ko,ke=run('recursive-kernel-check',checker,['-silent','-o',*flags,'GrokNumeric.GrokNumericGapsVerify']);kernel=ko+ke
    assert all(s in kernel for s in ['Axioms: <none>','type-in-type: <none>','unsafe (co)fixpoints: <none>','positivity is assumed: <none>'])
    receipt=(output/'logs'/'compile-GrokNumericGapsVerify.stdout.txt').read_text(encoding='utf-8',errors='replace');assert receipt.count('Closed under the global context')==10
    assert all(sha(source/r['path'])==r['sha256']==sha(output/r['path']) for r in inputs)
    result={'result':'PASS','fresh_project_module_count':3,'closed_checked_statements':10,'source_inputs':inputs,'source_bytes_unchanged':True,'commands':commands,'tool_version_stdout':version[0],'kernel_context':kernel,'whole_run_seconds':round(time.perf_counter()-begin,6),'scope':'Gallina list-Z decimal model only; no text/byte parser, executable, compiler or shipped-byte correspondence theorem.'}
    (output/'build-result.json').write_text(json.dumps(result,indent=2))
    (output/'SHA256SUMS.txt').write_text(''.join(sha(p)+' *'+p.relative_to(output).as_posix()+'\n' for p in sorted(output.rglob('*')) if p.is_file() and p.name!='SHA256SUMS.txt'))
    print('PASS fresh project modules3 closed statements10',flush=True)
if __name__=='__main__':main()
