"""Check release ZIP bytes, safe entry names and embedded source inventories."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import zipfile

parser = argparse.ArgumentParser()
parser.add_argument('--directory', type=Path, required=True)
parser.add_argument('--receipt', type=Path, required=True)
args = parser.parse_args()
if args.receipt.exists():
    raise FileExistsError(args.receipt)
expected = {}
for line in (args.directory/'SHA256SUMS.txt').read_text().splitlines():
    digest, name = line.split(maxsplit=1)
    expected[name.lstrip('*')] = digest
receipt = {'archives': [], 'source_inventories': []}
for name, digest in expected.items():
    path = args.directory/name
    actual = hashlib.file_digest(path.open('rb'), 'sha256').hexdigest()
    assert actual == digest, name
    if not name.endswith('.zip'):
        continue
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None, name
        entries = archive.infolist()
        folded = set()
        for entry in entries:
            p = PurePosixPath(entry.filename)
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in entry.filename, entry.filename
            assert not (p.parts and ':' in p.parts[0]), entry.filename
            assert stat.S_IFMT(entry.external_attr >> 16) != stat.S_IFLNK, entry.filename
            key = entry.filename.casefold()
            assert key not in folded, entry.filename
            folded.add(key)
        receipt['archives'].append({'file':name,'bytes':path.stat().st_size,'sha256':actual,'entries':len(entries),'crc_pass':True,'paths_pass':True})
        roots = {PurePosixPath(e.filename).parts[0] for e in entries}
        assert len(roots) == 1
        root = next(iter(roots)) + '/'
        if 'source' not in name:
            continue
        manifests = [('PUBLIC-SOURCE-WHITELIST.json', '', 'package_relative_path'),
                     ('repair/book-v6/PUBLIC-SOURCE-MANIFEST.json','repair/book-v6/','path'),
                     ('repair/math-workbench-v2/PUBLIC-SOURCE-MANIFEST.json','repair/math-workbench-v2/','path'),
                     ('repair/packaging/v6-workbench-v2/PUBLIC-SOURCE-MANIFEST.json','','package_relative_path')]
        for control, prefix, field in manifests:
            data = json.loads(archive.read(root+control))
            for row in data['files']:
                destination = prefix + row[field]
                assert hashlib.sha256(archive.read(root+destination)).hexdigest() == row['sha256'], destination
            receipt['source_inventories'].append({'manifest':control,'files':len(data['files']),'pass':True})
        asm = archive.read(root+'runtime/source/pompetzki.asm')
        asm_hash = hashlib.sha256(asm).hexdigest()
        assert asm_hash == '2329d3c993abfc5a89b979e6caae0b47aabdc12ec1858d752134a71a4e014f2e'
        builder = archive.read(root+'runtime/build-interpreter.py').decode()
        assert asm_hash in builder
        receipt['runtime_source_pin_pass'] = True
args.receipt.write_text(json.dumps(receipt, indent=2), encoding='utf-8')
print(json.dumps(receipt))
