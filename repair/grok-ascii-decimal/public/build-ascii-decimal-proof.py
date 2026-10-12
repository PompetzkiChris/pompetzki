#!/usr/bin/env python3
"""Compile fresh copies of the received ASCII decimal proof and its dependencies."""
import argparse, hashlib, json, pathlib, shutil, subprocess, tempfile, time

MODULES = (('NumericV5', 'DecimalSignificantV4'), ('GrokNumeric', 'GrokNumericGaps'), ('GrokNumeric', 'GrokAsciiDecimal'), ('GrokNumeric', 'GrokAsciiDecimalVerify'))
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--coqc', default='coqc')
    parser.add_argument('--rocqchk', default='rocqchk')
    args = parser.parse_args()
    source = pathlib.Path(__file__).resolve().parent
    output = args.output.resolve() if args.output else pathlib.Path(tempfile.mkdtemp(prefix='ascii-decimal-'))
    if args.output:
        output.mkdir(parents=True, exist_ok=False)
    for group in ('NumericV5', 'GrokNumeric', 'logs'):
        (output / group).mkdir()
    inputs = []
    for group, name in MODULES:
        relative = group + '/' + name + '.v'
        shutil.copy2(source / relative, output / relative)
        inputs.append({'path': relative, 'sha256': sha(source / relative), 'copy_sha256': sha(output / relative)})
    compiler = shutil.which(args.coqc) or args.coqc
    checker = shutil.which(args.rocqchk) or args.rocqchk
    commands = []
    begin = time.perf_counter()
    def run(label, exe, argv):
        started = time.perf_counter()
        stdout = output / 'logs' / (label + '.stdout.txt')
        stderr = output / 'logs' / (label + '.stderr.txt')
        with stdout.open('wb') as so, stderr.open('wb') as se:
            process = subprocess.run([exe, *argv], cwd=output, stdout=so, stderr=se, timeout=600, creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, 'CREATE_NO_WINDOW') else 0)
        commands.append({'label': label, 'command': [pathlib.Path(exe).name, *argv], 'exit_code': process.returncode, 'seconds': round(time.perf_counter() - started, 6), 'stdout': 'logs/' + stdout.name, 'stderr': 'logs/' + stderr.name})
        print(label, 'exit', process.returncode, flush=True)
        if process.returncode:
            raise RuntimeError(label + ' failed')
        return stdout.read_text(encoding='utf-8', errors='replace'), stderr.read_text(encoding='utf-8', errors='replace')
    version = run('compiler-version', compiler, ['--version'])
    flags = ['-Q', 'NumericV5', 'NumericV5', '-Q', 'GrokNumeric', 'GrokNumeric']
    for group, name in MODULES:
        run('compile-' + name, compiler, [*flags, group + '/' + name + '.v'])
    ko, ke = run('recursive-kernel-check', checker, ['-silent', '-o', *flags, 'GrokNumeric.GrokAsciiDecimalVerify'])
    kernel = ko + ke
    assert all(text in kernel for text in ('Axioms: <none>', 'type-in-type: <none>', 'unsafe (co)fixpoints: <none>', 'positivity is assumed: <none>'))
    receipt = (output / 'logs/compile-GrokAsciiDecimalVerify.stdout.txt').read_text(encoding='utf-8', errors='replace')
    assert receipt.count('Closed under the global context') == 27
    assert all(sha(source / row['path']) == row['sha256'] == sha(output / row['path']) for row in inputs)
    result = {'result': 'PASS', 'fresh_project_module_count': 4, 'closed_checked_statements': 27, 'source_inputs': inputs, 'source_bytes_unchanged': True, 'commands': commands, 'tool_version_stdout': version[0], 'kernel_context': kernel, 'whole_run_seconds': round(time.perf_counter() - begin, 6), 'scope': 'Gallina ASCII decoder over list Z composed with the unchanged decimal model; no RDNUM, pmp/Racket tokenizer, compiler or executable correspondence theorem.'}
    (output / 'build-result.json').write_text(json.dumps(result, indent=2) + '\n')
    (output / 'SHA256SUMS.txt').write_text(''.join(sha(path) + ' *' + path.relative_to(output).as_posix() + '\n' for path in sorted(output.rglob('*')) if path.is_file() and path.name != 'SHA256SUMS.txt'))
    print('PASS fresh project modules 4; closed checked statements 27', flush=True)

if __name__ == '__main__':
    main()
