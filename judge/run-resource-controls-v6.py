"""Run the ten allocation and numeric-domain controls with bounded owned children."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

base = Path(__file__).resolve().parent
corpus = base / 'validation-v6-resource'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--native')
parser.add_argument('--interpreter')
parser.add_argument('--pmp-source', type=Path)
parser.add_argument('--racket-source', type=Path)
parser.add_argument('--racket-executable', default='racket')
parser.add_argument('--timeout', type=int, default=30)
args = parser.parse_args()
if bool(args.interpreter) != bool(args.pmp_source):
    parser.error('--interpreter and --pmp-source must be supplied together')
if args.timeout < 1:
    parser.error('--timeout must be positive')
def executable(value):
    found = shutil.which(value)
    if not found:
        raise FileNotFoundError(value)
    return Path(found).resolve(strict=True)
routes = {}
if args.native:
    routes['native'] = [executable(args.native)]
if args.interpreter:
    routes['interpreted'] = [executable(args.interpreter), args.pmp_source.resolve(strict=True)]
if args.racket_source:
    routes['racket'] = [executable(args.racket_executable), args.racket_source.resolve(strict=True)]
if not routes:
    parser.error('Supply at least one checker route')
cases = json.loads((corpus / 'cases.json').read_text(encoding='utf-8'))
assert len(cases) == 10 and len({r['case'] for r in cases}) == 10
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for case in cases:
    assert sha(corpus / case['file']) == case['sha256']
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=False)
if os.name == 'nt':
    spec = importlib.util.spec_from_file_location('owned_job', corpus / 'owned-job-runner.py')
    job = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(job)
else:
    import resource
    def set_limit():
        resource.setrlimit(resource.RLIMIT_AS, (2 * 1024 ** 3, 2 * 1024 ** 3))
rows = []
for route, command in routes.items():
    directory = output / route
    directory.mkdir()
    for index, case in enumerate(cases):
        argv = [*command, corpus / case['file']]
        limit = 256 if route == 'racket' else 2048
        if os.name == 'nt':
            actual = job.run_owned(argv, directory, str(index), memory_mib=limit, timeout_seconds=args.timeout)
            stdout = actual['stdout'].encode('utf-8')
            code, timeout = actual['exit_code'], actual['timeout']
            bounded = actual['assigned_to_job_before_resume']
            stdout_hash, stderr_hash = actual['stdout_sha256'], actual['stderr_sha256']
        else:
            try:
                process = subprocess.run(list(map(str, argv)), capture_output=True, timeout=args.timeout, preexec_fn=set_limit)
                stdout, stderr, code, timeout = process.stdout, process.stderr, process.returncode, False
            except subprocess.TimeoutExpired as error:
                stdout, stderr, code, timeout = error.stdout or b'', error.stderr or b'', 124, True
            for kind, raw in [('stdout', stdout), ('stderr', stderr)]:
                with (directory / (str(index) + '.' + kind + '.txt')).open('xb') as stream:
                    stream.write(raw)
            bounded = True
            limit = 2048
            stdout_hash, stderr_hash = hashlib.sha256(stdout).hexdigest(), hashlib.sha256(stderr).hexdigest()
        verdicts = re.findall(rb'^(ACCEPT|REJECT|LIMIT)\b', stdout, re.M)
        verdict = verdicts[0].decode('ascii') if len(verdicts) == 1 else 'UNKNOWN'
        passed = bounded and not timeout and verdict == case['expected_verdict'] and code == case['expected_exit']
        rows.append({'route': route, 'case': case['case'], 'input_sha256': case['sha256'],
                     'expected_verdict': case['expected_verdict'], 'verdict': verdict, 'exit_code': code,
                     'memory_limit_bytes': limit * 1024 ** 2, 'bounded_before_execution': bounded,
                     'timeout': timeout, 'stdout_sha256': stdout_hash, 'stderr_sha256': stderr_hash, 'passed': passed})
result = {'result': 'PASS' if all(r['passed'] for r in rows) else 'FAIL', 'runs': len(rows),
          'passed': sum(r['passed'] for r in rows), 'timeouts': sum(r['timeout'] for r in rows),
          'tools_and_sources': [{'route': route, 'filename': p.name, 'sha256': sha(p)} for route, command in routes.items() for p in command],
          'cases_sha256': sha(corpus / 'cases.json'), 'results': rows}
(output / 'results.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps({k: result[k] for k in ['result', 'runs', 'passed', 'timeouts']}))
raise SystemExit(0 if result['result'] == 'PASS' else 1)
