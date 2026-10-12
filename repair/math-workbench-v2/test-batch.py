"""Execute mixed matrix batches and verify recovery and exact answers."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--engine', nargs='+', required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=False)
good = {'id': 'before', 'op': 'det', 'a': '[1,2;3,4]'}
last = {'id': 'after', 'op': 'det', 'a': '[6/4]'}
bad = [None, 7, 'bad', [], {}, {'id': 'missing-op', 'a': '[1]'},
       {'id': 'missing-a', 'op': 'det'}, {'id': 'numeric-op', 'op': 3, 'a': '[1]'},
       {'id': 'numeric-a', 'op': 'det', 'a': 3},
       {'id': 'numeric-b', 'op': 'mul', 'a': '[1]', 'b': 3},
       {'id': 'bad-number', 'op': 'det', 'a': '[1.5]'},
       {'id': 'bad-op', 'op': 'other', 'a': '[1]'}]
checks = []

def run(name, content, extra=()):
    path = args.output / (name + '.json')
    path.write_text(content, encoding='utf-8')
    result = subprocess.run([*args.engine, '--batch', str(path), *extra], capture_output=True, timeout=30)
    (args.output / (name + '.stdout')).write_bytes(result.stdout)
    (args.output / (name + '.stderr')).write_bytes(result.stderr)
    return result

def check(label, condition):
    checks.append({'check': label, 'pass': bool(condition)})
    if not condition:
        raise AssertionError(label)

mixed = json.dumps([good, *bad, last])
r = run('mixed', mixed)
check('mixed envelope completes', r.returncode == 0)
data = json.loads(r.stdout)
check('one ordered result per item', len(data) == len(bad) + 2)
check('first exact determinant', data[0]['id'] == 'before' and data[0]['exit'] == 0 and data[0]['machine']['determinant'] == '-2')
check('last exact reduced determinant survives preceding errors', data[-1]['id'] == 'after' and data[-1]['exit'] == 0 and data[-1]['machine']['determinant'] == '3/2')
for i, item in enumerate(bad, 1):
    d = data[i]
    expected_id = item.get('id') if isinstance(item, dict) else None
    check('rejected item ' + str(i), d['exit'] == 1 and d['id'] == expected_id and d['machine']['status'] == 'rejected' and bool(d['machine']['reason']))
for name, content in [('malformed', '[{'), ('object', '{}'), ('null', 'null'),
                      ('trailing-value', mixed + '\n[]'), ('trailing-garbage', mixed + '\nx')]:
    r = run(name, content)
    check(name + ' envelope refusal', r.returncode == 1 and r.stdout == b'' and bool(r.stderr))
r = run('empty', '[]')
check('empty valid batch', r.returncode == 0 and json.loads(r.stdout) == [])
destination = args.output / 'saved-results.json'
r = run('save-new', mixed, ['--out', str(destination)])
check('new output equals complete stdout', r.returncode == 0 and destination.read_bytes() == r.stdout)
before = destination.read_bytes()
r = run('save-existing', mixed, ['--out', str(destination)])
check('existing output preserved', r.returncode == 1 and destination.read_bytes() == before)
files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in args.output.iterdir() if p.is_file()}
receipt = {'engine_command': args.engine, 'checks': checks, 'passed': len(checks), 'failed': 0, 'files': files}
(args.output / 'results.json').write_text(json.dumps(receipt, indent=2), encoding='utf-8')
print(json.dumps({'passed': len(checks), 'failed': 0, 'output': str(args.output)}))
