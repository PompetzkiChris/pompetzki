#!/usr/bin/env python3
"""Build the reviewed Gallina composition from fresh source copies."""
import argparse,hashlib,json,pathlib,shutil,subprocess,tempfile,time
CORE=('Syn','Prov','Kal','Val','Inv','Parse','Data','Checks','Ax','Sub','Expand','Replay','ReplayT','Replay2','Replay3','RpInit','RpInitOk')
PROOF=('PrefixSoundness','CanonicalRegistryData','CanonicalPrefixSoundness','GrokAuthGate','GrokCompose47','GrokCompositionReceipt')
REQUIRED=('Axioms: <none>','type-in-type: <none>','unsafe (co)fixpoints: <none>','positivity is assumed: <none>')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path);ap.add_argument('--coqc',default='coqc');ap.add_argument('--rocqchk',default='rocqchk');args=ap.parse_args()
    source=pathlib.Path(__file__).resolve().parent
    output=args.output.resolve() if args.output else pathlib.Path(tempfile.mkdtemp(prefix='grok-composition-'))
    if args.output:output.mkdir(parents=True,exist_ok=False)
    for group in ['Cohen','NumericV5','PMPRepair','logs']:(output/group).mkdir()
    inputs=[]
    for group,names in [('Cohen',CORE),('NumericV5',('DecimalSignificantV4',)),('PMPRepair',PROOF)]:
        for name in names:
            rel=group+'/'+name+'.v';original=source/rel;target=output/rel;shutil.copy2(original,target)
            inputs.append({'path':rel,'sha256':sha(original),'copy_sha256':sha(target)})
    commands=[];began=time.perf_counter()
    compiler=shutil.which(args.coqc) or args.coqc;checker=shutil.which(args.rocqchk) or args.rocqchk
    def run(label,exe,argv):
        start=time.perf_counter();stdout=output/'logs'/(label+'.stdout.txt');stderr=output/'logs'/(label+'.stderr.txt')
        with stdout.open('wb') as so,stderr.open('wb') as se:
            process=subprocess.run([exe,*argv],cwd=output,stdout=so,stderr=se,timeout=600,check=False,creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0)
        commands.append({'label':label,'command':[pathlib.Path(exe).name,*argv],'exit_code':process.returncode,'seconds':round(time.perf_counter()-start,6),'stdout':'logs/'+stdout.name,'stderr':'logs/'+stderr.name})
        print(label,'exit',process.returncode,flush=True)
        if process.returncode:raise RuntimeError(label+' failed; see '+str(stderr))
        return stdout.read_text(encoding='utf-8',errors='replace'),stderr.read_text(encoding='utf-8',errors='replace')
    version=run('compiler-version',compiler,['--version'])
    flags=['-Q','Cohen','Cohen','-Q','PMPRepair','PMPRepair','-Q','NumericV5','NumericV5']
    for group,names in [('Cohen',CORE),('NumericV5',('DecimalSignificantV4',)),('PMPRepair',PROOF)]:
        for name in names:run('compile-'+name,compiler,[*flags,group+'/'+name+'.v'])
    ko,ke=run('recursive-kernel-check',checker,['-silent','-o',*flags,'PMPRepair.GrokCompositionReceipt'])
    kernel=ko+ke;assert all(fragment in kernel for fragment in REQUIRED),'kernel context not confirmed'
    receipt=(output/'logs'/'compile-GrokCompositionReceipt.stdout.txt').read_text(encoding='utf-8',errors='replace')
    assert receipt.count('Closed under the global context')==8,'composition closure count differs from eight'
    unchanged=all(sha(source/r['path'])==r['sha256']==sha(output/r['path']) for r in inputs);assert unchanged,'source changed during proof build'
    result={'result':'PASS','fresh_module_count':24,'compiled_core_modules':17,'compiled_numeric_modules':1,'compiled_proof_modules':6,'main_composition_results':5,'decoder_lemmas':2,'prefix_helper_lemmas':1,'closed_checked_statements':8,'source_bytes_unchanged':unchanged,'source_inputs':inputs,'commands':commands,'tool_version_stdout':version[0],'kernel_context':kernel,'whole_run_seconds':round(time.perf_counter()-began,6),'scope':'Gallina initial-registry number policy, zero padding and conditional source checker soundness. Text parsing, executable gate/checker correspondence, compiler preservation and executable byte correspondence remain separate obligations. Theorem bodies are outside this numeric-policy result.'}
    (output/'build-result.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    with (output/'SHA256SUMS.txt').open('w',encoding='utf-8') as f:
        for p in sorted(output.rglob('*')):
            if p.is_file() and p.name!='SHA256SUMS.txt':f.write(sha(p)+' *'+p.relative_to(output).as_posix()+'\n')
    print('PASS fresh modules24 main composition5 decoder2 helper1 closed8',flush=True)
if __name__=='__main__':main()
