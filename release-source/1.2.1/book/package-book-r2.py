"""Build a new portable Book stage with confined, manifest-bound checkers.

Usage: python package-book-r2.py BASE_STAGE NEW_STAGE NEW_ARCHIVE CHECKER_DIR
All output paths must be new. Input data and predecessor archives stay in place.
"""
from pathlib import Path
import hashlib, json, shutil, sys, zipfile

base, stage, archive, checker_dir = (Path(x).resolve() for x in sys.argv[1:5])
if stage.exists() or archive.exists():
    raise FileExistsError('The stage and archive must be new paths')

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

replaced = {'verify-portable.py', 'portable-paths.rkt',
            'master-verify-portable.rkt', 'master-verify-indep-portable.rkt',
            'book-index-portable.rkt'}
def excluded(folder, names):
    path = Path(folder)
    result = {'__pycache__', 'compiled'} & set(names)
    if path == base:
        result |= {'SHA256SUMS.txt', 'README.md'} & set(names)
    if path == base / 'code':
        result |= replaced & set(names)
    return result

shutil.copytree(base, stage, ignore=excluded)
code = stage / 'code'
for name in ['verify-portable-r2.py', 'portable-paths-r3.rkt']:
    shutil.copyfile(checker_dir / name, code / name)
shutil.copyfile(checker_dir / 'verify-portable-r2.py', code / 'verify-portable.py')
shutil.copyfile(checker_dir / 'portable-paths-r3.rkt', code / 'portable-paths.rkt')
shutil.copyfile(Path(__file__).resolve(), code / Path(__file__).name)
shutil.copyfile(Path(__file__).resolve().parent / 'verify-archive-r2.py',
                code / 'verify-archive-r2.py')
for name in ['master-verify-portable.rkt', 'master-verify-indep-portable.rkt',
             'book-index-portable.rkt']:
    text = (base / 'code' / name).read_text(encoding='utf-8')
    text = text.replace('(file "portable-paths.rkt")', '(file "portable-paths-r3.rkt")')
    (code / name).write_text(text, encoding='utf-8', newline='\n')
    (code / name.replace('.rkt', '-r3.rkt')).write_text(text, encoding='utf-8', newline='\n')

readme = (base / 'README.md').read_text(encoding='utf-8')
readme += '''
The portable checkers require every certificate and alias target to remain inside
the extracted archive root and to appear in SHA256SUMS.txt. Historical provenance
requires a bundled alias; it cannot fall through to a file on the execution host.
The conventional checker filenames contain Python r2 and Racket resolver r3.
The explicitly named revision files contain the same implementations.

To rebuild from an existing packaged Book data directory, run
`python code/package-book-r2.py BASE_STAGE NEW_STAGE NEW_ARCHIVE CHECKER_DIR`.
CHECKER_DIR contains verify-portable-r2.py and portable-paths-r3.rkt. NEW_STAGE
and NEW_ARCHIVE must be unused paths. The ZIP has a fixed file timestamp and
sorted entries; its manifest hashes the complete new stage before packaging.
'''
(stage / 'README.md').write_text(readme, encoding='utf-8', newline='\n')
(stage / 'PORTABLE-CHECKER-CORRECTION-R2.md').write_text('''# Portable path confinement

This package is a new copy of the completed Book data. Its portable Python
checker confines CERTIFICATES.tsv and PATH-ALIASES.tsv targets to the resolved
archive root and requires their manifest membership. Its Racket resolver
confines mapped paths and fails when a historical path has no bundled alias.
The journals, source ledgers, certificate payloads and bound judge receipts
retain their predecessor bytes. Earlier stages, checkers and archives remain
in their original local paths.

The conventional portable checker entry points use Python r2 and Racket resolver r3.
The fixed ZIP timestamp is 2026-10-10 00:00:00 and paths are sorted.
''', encoding='utf-8', newline='\n')
with (stage / 'SHA256SUMS.txt').open('x', encoding='utf-8', newline='\n') as out:
    for path in sorted(stage.rglob('*')):
        if path.is_file() and path.name != 'SHA256SUMS.txt':
            out.write(f'{sha(path)} *{path.relative_to(stage).as_posix()}\n')
archive.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED,
                     compresslevel=6, allowZip64=True) as zipped:
    for path in sorted(stage.rglob('*')):
        if path.is_file():
            name = path.relative_to(stage.parent).as_posix()
            info = zipfile.ZipInfo(name, (2026, 10, 10, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            info._compresslevel = 6
            with path.open('rb') as source, zipped.open(info, 'w', force_zip64=True) as target:
                shutil.copyfileobj(source, target, length=1024 * 1024)
digest = sha(archive)
archive.with_suffix('.zip.sha256').write_text(
    f'{digest} *{archive.name}\n', encoding='utf-8', newline='\n')
print(json.dumps({'stage':str(stage), 'archive':str(archive),
                  'bytes':archive.stat().st_size, 'sha256':digest}, indent=2))
