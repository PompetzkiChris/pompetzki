"""Verify recorded native/interpreted routes and reject malformed recorded paths."""
import argparse, hashlib, json, pathlib, shutil, subprocess, time

parser = argparse.ArgumentParser()
parser.add_argument('--bundle', type=pathlib.Path, required=True)
parser.add_argument('--historical-bundle', type=pathlib.Path, action='append', default=[])
parser.add_argument('--poster', type=pathlib.Path)
parser.add_argument('--checker', type=pathlib.Path)
parser.add_argument('--racket', default='racket')
args = parser.parse_args()
HERE = pathlib.Path(__file__).resolve().parent
OUT = HERE / 'tests' / ('route-path-v7-' + time.strftime('%Y%m%d-%H%M%S'))
OUT.mkdir(parents=True)
poster, checker = args.poster or HERE / 'verified-book-post.rkt', args.checker or HERE / 'verified-book-check.rkt'
prefix = lambda path: [str(path)] if path.suffix.lower() == '.exe' else [args.racket, str(path)]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
results = []

def run(name, command, expected):
    child = subprocess.run(command, capture_output=True, timeout=90, creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, 'CREATE_NO_WINDOW') else 0)
    (OUT / (name + '.stdout.txt')).write_bytes(child.stdout)
    (OUT / (name + '.stderr.txt')).write_bytes(child.stderr)
    assert child.returncode == expected, (name, child.returncode, child.stdout, child.stderr)
    return child

def rebind(folder, metadata):
    (folder / 'run-metadata.json').write_text(json.dumps(metadata))
    digest = sha(folder / 'run-metadata.json')
    for name in ('BOOK-1.0.ledger', 'NEGATIVE-1.0.ledger'):
        records = [line.split('\t')[:-1] for line in (folder / name).read_text().splitlines()]
        index = next(index for index, field in enumerate(records[0]) if field.startswith('run-metadata.json '))
        records[0][index] = 'run-metadata.json ' + digest
        head, output = '0' * 64, []
        for fields in records:
            body = '\t'.join(fields)
            head = hashlib.sha256((head + '\n' + body).encode()).hexdigest()
            output.append(body + '\t' + head)
        (folder / name).write_text('\n'.join(output) + '\n')

for bundle_index, bundle in enumerate([args.bundle, *args.historical_bundle]):
    version = next(v for v in ('v6', 'v5', 'v4') if (bundle / 'judge' / ('judge-' + v + '.pmp')).is_file())
    for route in ('native', 'interpreted'):
        name = f'bundle{bundle_index}-{version}-{route}'
        posting = OUT / name
        post = run(name + '-post', prefix(poster) + ['--bundle', str(bundle)] + (['--interpreted'] if route == 'interpreted' else []) + [str(posting), '2026-10-12 UTC', str(HERE / 'registry-tests/prefix-0-truth.jdg'), str(HERE / 'registry-tests/false-proof-empty-registry.jdg')], 0)
        check = run(name + '-check', prefix(checker) + ['--bundle', str(bundle), str(posting)], 0)
        metadata, report = json.loads((posting / 'run-metadata.json').read_text()), json.loads(check.stdout)
        assert report['status'] == 'CHECK OK' and report['positive_files'] == report['negative_files'] == report['theorems'] == 1
        for old, fresh in zip(metadata['runs'], report['reruns']):
            recorded, actual = old['pmp']['command'], fresh['pmp']['command']
            assert recorded == actual, (name, recorded, actual)
            if route == 'native':
                assert pathlib.Path(actual[0]).name == 'judge-' + version + '-windows.exe' and len(actual) == 2
            else:
                assert pathlib.Path(actual[0]).name == 'pompetzki.exe' and pathlib.Path(actual[1]).name == 'judge-' + version + '.pmp' and len(actual) == 3
        results.append({'case': name, 'route': route, 'selected_version': version, 'recorded_fresh_commands_identical': True, 'post_exit': 0, 'check_exit': 0, 'passed': True})
        if bundle_index:
            continue
        for category in ('artifact', 'command-program', 'command-input', 'snapshot', 'stdout', 'receipt-directory'):
            for separator, suffix in (('slash', '/'), ('backslash', '\\')):
                case = name + '-' + category + '-' + separator
                malformed = OUT / case
                shutil.copytree(posting, malformed)
                data = json.loads((malformed / 'run-metadata.json').read_text())
                record = data['runs'][0]
                if category == 'artifact':
                    data['artifacts'][0]['path'] += suffix
                elif category == 'command-program':
                    record['pmp']['command'][0] += suffix
                elif category == 'command-input':
                    record['pmp']['command'][-1] += suffix
                elif category == 'snapshot':
                    record['snapshot'] += suffix
                elif category == 'stdout':
                    record['pmp']['stdout'] += suffix
                else:
                    path = malformed / 'RECEIPTS.tsv'
                    rows = [line.split('\t') for line in path.read_text().splitlines()]
                    rows[1][3] += suffix
                    path.write_text('\n'.join('\t'.join(row) for row in rows) + '\n')
                rebind(malformed, data)
                rejection = run(case + '-check', prefix(checker) + ['--bundle', str(bundle), str(malformed)], 1)
                assert b'recorded path ends in slash or backslash' in rejection.stderr, (case, rejection.stderr)
                results.append({'case': case, 'route': route, 'path_category': category, 'separator': separator, 'check_exit': 1, 'passed': True})
summary = {'cases': len(results), 'passed': sum(row['passed'] for row in results), 'results': results, 'poster_sha256': sha(poster), 'checker_sha256': sha(checker), 'lowlevel_writer_sha256': sha(HERE / 'book-post-v4.rkt')}
(OUT / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')
(OUT / 'SHA256SUMS.txt').write_text(''.join(sha(path) + ' *' + path.relative_to(OUT).as_posix() + '\n' for path in sorted(OUT.rglob('*')) if path.is_file() and path.name != 'SHA256SUMS.txt'))
print(json.dumps({'output': str(OUT), 'cases': len(results), 'passed': summary['passed']}, indent=2))
