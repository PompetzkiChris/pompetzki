#!/usr/bin/env python3
"""Check additional finite boundary examples using a completed fresh core build."""
import argparse, hashlib, json, pathlib, shutil, subprocess, time

sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--core-build', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    parser.add_argument('--coqc', default='coqc')
    parser.add_argument('--rocqchk', default='rocqchk')
    args = parser.parse_args()
    source = pathlib.Path(__file__).resolve().parent
    core = args.core_build.resolve()
    prior = json.loads((core / 'build-result.json').read_text())
    assert prior['result'] == 'PASS' and prior['fresh_project_module_count'] == 4 and prior['closed_checked_statements'] == 27
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for group in ('NumericV5', 'GrokNumeric', 'logs'):
        (output / group).mkdir()
    dependencies = []
    for row in prior['source_inputs']:
        relative = row['path']
        assert sha(source / relative) == row['sha256'] == sha(core / relative)
        shutil.copy2(core / relative, output / relative)
        obj = pathlib.Path(relative).with_suffix('.vo')
        shutil.copy2(core / obj, output / obj)
        dependencies.append({'source': relative, 'source_sha256': sha(output / relative), 'fresh_core_object_sha256': sha(output / obj)})
    relative = 'GrokNumeric/AsciiBoundaryExamples.v'
    shutil.copy2(source / relative, output / relative)
    compiler = shutil.which(args.coqc) or args.coqc
    checker = shutil.which(args.rocqchk) or args.rocqchk
    flags = ['-Q', 'NumericV5', 'NumericV5', '-Q', 'GrokNumeric', 'GrokNumeric']
    commands = []
    begin = time.perf_counter()
    def run(label, exe, argv):
        stdout, stderr = output / 'logs' / (label + '.stdout.txt'), output / 'logs' / (label + '.stderr.txt')
        with stdout.open('wb') as so, stderr.open('wb') as se:
            process = subprocess.run([exe, *argv], cwd=output, stdout=so, stderr=se, timeout=600, creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, 'CREATE_NO_WINDOW') else 0)
        commands.append({'label': label, 'command': [pathlib.Path(exe).name, *argv], 'exit_code': process.returncode, 'stdout': 'logs/' + stdout.name, 'stderr': 'logs/' + stderr.name})
        assert process.returncode == 0, label
        print(label, 'exit 0', flush=True)
        return stdout.read_text(encoding='utf-8', errors='replace') + stderr.read_text(encoding='utf-8', errors='replace')
    receipt = run('compile-AsciiBoundaryExamples', compiler, [*flags, relative])
    kernel = run('recursive-boundary-kernel-check', checker, ['-silent', '-o', *flags, 'GrokNumeric.AsciiBoundaryExamples'])
    assert receipt.count('Closed under the global context') == 22
    assert all(text in kernel for text in ('Axioms: <none>', 'type-in-type: <none>', 'unsafe (co)fixpoints: <none>', 'positivity is assumed: <none>'))
    result = {'result': 'PASS', 'supplemental_finite_examples': 22, 'newly_compiled_project_modules': 1, 'dependencies_from_fresh_core_modules': 4, 'dependencies': dependencies, 'boundary_source': relative, 'boundary_source_sha256': sha(output / relative), 'commands': commands, 'kernel_context': kernel, 'whole_run_seconds': round(time.perf_counter() - begin, 6), 'scope': 'Concrete evaluations and proof checks of the Gallina model; no executable correspondence claim.'}
    (output / 'boundary-result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS 22 finite examples', flush=True)

if __name__ == '__main__':
    main()
