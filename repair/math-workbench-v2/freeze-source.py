"""Seal this version's explicit public source inputs."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
names = ['engine.rkt', 'exact.rkt', 'gui.rkt', 'build.py', 'README.md',
         'INITIAL-SOURCE-RECEIPT.json', 'test-gui.rkt', 'test-batch.py', 'freeze-source.py']
rows = [{'path': n, 'candidate_relative_path': 'repair/math-workbench-v2/' + n,
         'sha256': hashlib.sha256((root/n).read_bytes()).hexdigest()} for n in names]
old = root.parent / 'math-workbench-corrected'
unchanged = {n: (root/n).read_bytes() == (old/n).read_bytes() for n in ['exact.rkt', 'gui.rkt', 'test-gui.rkt', 'build.py', 'INITIAL-SOURCE-RECEIPT.json']}
assert all(unchanged.values())
(root/'PUBLIC-SOURCE-MANIFEST.json').write_text(json.dumps({'revision': 'Matrix batch recovery v2', 'files': rows, 'unchanged_from_previous': unchanged}, indent=2), encoding='utf-8')
(root/'SHA256SUMS-source.txt').write_text(''.join(r['sha256'] + ' *' + r['path'] + '\n' for r in rows), encoding='utf-8')
print(json.dumps({'files': len(rows), 'unchanged': unchanged}))
