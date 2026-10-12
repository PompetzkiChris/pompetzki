"""Compare a candidate bundle with a fresh source-archive-only rebuild."""
from pathlib import Path
import argparse, hashlib, json, struct

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--candidate', type=Path, required=True)
parser.add_argument('--rebuilt', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
if args.output.exists():
    raise SystemExit('Output already exists: ' + str(args.output))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
candidate, rebuilt = args.candidate.resolve(), args.rebuilt.resolve()
def files(root):
    return {p.relative_to(root).as_posix(): p for p in root.rglob('*') if p.is_file()}
a, b = files(candidate), files(rebuilt)
context = {'MANIFEST.sha256', 'provenance/package-components.json',
           'provenance/native-rebuild-comparison.json', 'provenance/cockpit-portable-changes.json'}
programs = sorted(k for k in a.keys() & b.keys() if Path(k).suffix.lower() == '.exe')
ordinary = sorted(k for k in a.keys() & b.keys() if k not in context and k not in programs)
different = [k for k in ordinary if sha(a[k]) != sha(b[k])]
def json_file(root, name):
    return json.loads((root / name).read_text())
def source_hashes(receipt):
    result = {}
    for path, digest in receipt['component_sources'].items():
        path = path.replace('\\', '/')
        markers = {'/cockpit-source/': 'cockpit/', '/repair/': 'repair/', '/judge/': 'judge/'}
        marker = max(markers, key=path.rfind)
        if path.rfind(marker) < 0: raise ValueError('Unclassified component source: ' + path)
        key = markers[marker] + path.rsplit(marker, 1)[1]
        if key in result: raise ValueError('Duplicate component source: ' + key)
        result[key] = digest
    return result
pa = json_file(candidate, 'provenance/package-components.json')
pb = json_file(rebuilt, 'provenance/package-components.json')
def portable_after(root):
    return [{k: row[k] for k in ['file', 'after_sha256', 'binding']}
            for row in json_file(root, 'provenance/cockpit-portable-changes.json')]
def pe_sections(path):
    data = path.read_bytes(); pe = struct.unpack_from('<I', data, 0x3c)[0]
    count = struct.unpack_from('<H', data, pe + 6)[0]
    optional = struct.unpack_from('<H', data, pe + 20)[0]
    rows = {}
    for i in range(count):
        at = pe + 24 + optional + i * 40
        name = data[at:at+8].split(b'\0', 1)[0].decode()
        virtual, address, size, offset = struct.unpack_from('<IIII', data, at + 8)
        rows[name] = (virtual, address, struct.unpack_from('<I', data, at + 36)[0],
                      hashlib.sha256(data[offset:offset+min(size, virtual)]).hexdigest())
    return rows
checks = {
    'same_bundle_paths': a.keys() == b.keys(),
    'all_ordinary_files_identical': not different,
    'all_embedded_component_source_hashes_identical': source_hashes(pa) == source_hashes(pb),
    'same_audited_base_sha256': pa['base_asset_sha256'] == pb['base_asset_sha256'],
    'same_judge_source_sha256': pa['gated_native_source_sha256'] == pb['gated_native_source_sha256'],
    'same_math_source_sha256': pa['math_source_sha256'] == pb['math_source_sha256'],
    'same_racket_tool_version': pa['racket_version'] == pb['racket_version'],
    'same_portable_cockpit_result_hashes': portable_after(candidate) == portable_after(rebuilt),
    'same_native_allocated_pe_sections': pe_sections(a['judge/judge-v6-windows.exe']) == pe_sections(b['judge/judge-v6-windows.exe']),
    'console_interpreter_bit_identical': sha(a['pompetzki.exe']) == sha(b['pompetzki.exe']),
    'window_interpreter_bit_identical': sha(a['pompetzki-w.exe']) == sha(b['pompetzki-w.exe']),
}
report = {'candidate': str(candidate), 'source_archive_only_rebuild': str(rebuilt),
          'candidate_file_count': len(a), 'source_rebuilt_file_count': len(b),
          'missing_from_source_rebuild': sorted(a.keys()-b.keys()),
          'extra_in_source_rebuild': sorted(b.keys()-a.keys()),
          'ordinary_files_compared': len(ordinary), 'ordinary_files_identical': len(ordinary)-len(different),
          'unexpected_content_differences': different,
          'build_context_metadata': sorted(context), 'executable_files_rebuilt_or_inherited': programs,
          'console_sha256': sha(b['pompetzki.exe']), 'window_sha256': sha(b['pompetzki-w.exe']),
          'component_source_sha256': source_hashes(pb), 'checks': checks,
          'passed': all(checks.values()),
          'reproducibility_scope': 'Interpreter bytes and allocated native sections match. Racket embedded source hashes match; executable bytes can contain build paths. Separate execution receipts establish the finite test results.'}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2))
print(json.dumps({'output': str(args.output), 'passed': report['passed'], 'checks': len(checks),
                  'candidate_files': len(a), 'rebuilt_files': len(b), 'ordinary_files': len(ordinary)}))
raise SystemExit(0 if report['passed'] else 1)
