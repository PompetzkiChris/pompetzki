#!/usr/bin/env python3
"""Build the reviewed Gallina authentication gate from fresh source copies."""
import argparse,hashlib,json,pathlib,shutil,subprocess,tempfile,time

CORE=('Syn','Prov','Kal','Val','Inv','Parse','Data','Checks','Ax','Sub','Expand','Replay','ReplayT','Replay2','Replay3','RpInit','RpInitOk')
PROOF=('PrefixSoundness','CanonicalRegistryData','CanonicalPrefixSoundness','GrokAuthGate','GrokAuthGateReceipt')
REQUIRED_KERNEL=('Axioms: <none>','type-in-type: <none>','unsafe (co)fixpoints: <none>','positivity is assumed: <none>')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=pathlib.Path)
    ap.add_argument('--coqc',default='coqc')
    ap.add_argument('--rocqchk',default='rocqchk')
    args=ap.parse_args()
    source=pathlib.Path(__file__).resolve().parent
    output=args.output.resolve() if args.output else pathlib.Path(tempfile.mkdtemp(prefix='grok-auth-gate-'))
    if args.output:output.mkdir(parents=True,exist_ok=False)
    (output/'Cohen').mkdir();(output/'PMPRepair').mkdir();(output/'logs').mkdir()
    inputs=[]
    for directory,names in [('Cohen',CORE),('PMPRepair',PROOF)]:
        for name in names:
            rel=directory+'/'+name+'.v';original=source/rel;copy=output/rel
            shutil.copy2(original,copy)
            inputs.append({'path':rel,'sha256':sha(original),'copy_sha256':sha(copy)})
    commands=[];began=time.perf_counter()
    coqc=shutil.which(args.coqc) or args.coqc
    checker=shutil.which(args.rocqchk) or args.rocqchk
    def run(label,exe,argv):
        begin=time.perf_counter()
        stdout=output/'logs'/(label+'.stdout.txt');stderr=output/'logs'/(label+'.stderr.txt')
        with stdout.open('wb') as so,stderr.open('wb') as se:
            proc=subprocess.run([exe,*argv],cwd=output,stdout=so,stderr=se,timeout=600,check=False,creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess,'CREATE_NO_WINDOW') else 0)
        row={'label':label,'command':[pathlib.Path(exe).name,*argv],'exit_code':proc.returncode,'seconds':round(time.perf_counter()-begin,6),'stdout':'logs/'+stdout.name,'stderr':'logs/'+stderr.name}
        commands.append(row)
        print(label,'exit',proc.returncode,'seconds',row['seconds'],flush=True)
        if proc.returncode:raise RuntimeError(label+' failed; see '+str(stderr))
        return stdout.read_text(encoding='utf-8',errors='replace'),stderr.read_text(encoding='utf-8',errors='replace')
    version=run('compiler-version',coqc,['--version'])
    flags=['-Q','Cohen','Cohen','-Q','PMPRepair','PMPRepair']
    for directory,names in [('Cohen',CORE),('PMPRepair',PROOF)]:
        for name in names:run('compile-'+name,coqc,[*flags,directory+'/'+name+'.v'])
    ko,ke=run('recursive-kernel-check',checker,['-silent','-o',*flags,'PMPRepair.GrokAuthGateReceipt'])
    kernel=ko+ke
    assert all(fragment in kernel for fragment in REQUIRED_KERNEL),'kernel context not confirmed'
    receipt=(output/'logs'/'compile-GrokAuthGateReceipt.stdout.txt').read_text(encoding='utf-8',errors='replace')
    assert receipt.count('Closed under the global context')==7,'gate assumption closure count differs from seven'
    unchanged=all(sha(source/row['path'])==row['sha256'] and sha(output/row['path'])==row['sha256'] for row in inputs)
    assert unchanged,'source changed during proof build'
    result={'result':'PASS','compiled_core_modules':len(CORE),'compiled_proof_modules':len(PROOF),'closed_gate_lemmas':7,'source_bytes_unchanged':unchanged,'source_inputs':inputs,'commands':commands,'tool_version_stdout':version[0],'kernel_context':kernel,'whole_run_seconds':round(time.perf_counter()-began,6),'scope':'Gallina prefix gate equivalence and conditional checker soundness; executable parser, gate and checker correspondence, compiler preservation and shipped-byte correspondence remain separate obligations.'}
    (output/'build-result.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    with (output/'SHA256SUMS.txt').open('w',encoding='utf-8') as f:
        for p in sorted(output.rglob('*')):
            if p.is_file() and p.name!='SHA256SUMS.txt':f.write(sha(p)+' *'+str(p.relative_to(output)).replace('\\','/')+'\n')
    print('PASS freshly compiled core',len(CORE),'proof',len(PROOF),'closed gate lemmas7',flush=True)

if __name__=='__main__':main()
