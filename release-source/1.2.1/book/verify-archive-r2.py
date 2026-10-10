"""Extract a Book ZIP into a new directory and run its three portable checks.

Usage: python verify-archive-r2.py ARCHIVE NEW_EXTRACT_DIR NEW_RECEIPT_DIR
Requires Python 3.11+ and Racket. All receipt and extraction paths must be new.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, os, re, shutil, subprocess, sys, zipfile

archive, extracted, receipts = (Path(x).resolve() for x in sys.argv[1:4])
if extracted.exists() or receipts.exists():
    raise FileExistsError('Extraction and receipt directories must be new')
extracted.mkdir(parents=True)
receipts.mkdir(parents=True)
with archive.open('rb') as stream:
    archive_sha = hashlib.file_digest(stream, 'sha256').hexdigest()
with zipfile.ZipFile(archive) as zipped:
    members = zipped.infolist()
    names = set()
    for member in members:
        name = member.filename
        path = PurePosixPath(name)
        if (not name or '\\' in name or path.is_absolute() or '..' in path.parts
                or re.match(r'^[A-Za-z]:', name) or name.casefold() in names
                or ((member.external_attr >> 16) & 0o170000) == 0o120000):
            raise ValueError(f'Unsafe or duplicate ZIP path: {name}')
        if not (extracted / name).resolve().is_relative_to(extracted):
            raise ValueError(f'ZIP path leaves extraction root: {name}')
        names.add(name.casefold())
    bad_crc = zipped.testzip()
    if bad_crc is not None:
        raise ValueError(f'ZIP CRC failed: {bad_crc}')
    zipped.extractall(extracted)
roots = list(extracted.iterdir())
if len(roots) != 1 or not roots[0].is_dir():
    raise ValueError('Expected one package directory in the ZIP')
root = roots[0]
racket = shutil.which('racket')
if not racket and os.name == 'nt':
    candidate = Path(r'C:\Program Files\Racket\racket.exe')
    if candidate.is_file():
        racket = str(candidate)
if not racket:
    raise FileNotFoundError('Racket executable was not found by PATH or the Windows installation path')
results = []
for name, command in [
    ('PYTHON-VERIFY', [sys.executable, str(root / 'code/verify-portable.py'), str(root)]),
    ('MASTER-VERIFY', [racket, str(root / 'code/master-verify-portable.rkt'), str(root)]),
    ('INDEPENDENT-VERIFY', [racket, str(root / 'code/master-verify-indep-portable.rkt'), str(root)])
]:
    print('RUN', name, flush=True)
    receipt = receipts / f'{name}.txt'
    with receipt.open('x', encoding='utf-8') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT,
                                text=True, check=False)
    results.append({'check':name, 'exit':result.returncode,
                    'receipt':str(receipt), 'command':command})
    if result.returncode:
        raise RuntimeError(f'{name} exited {result.returncode}: {receipt}')
    print('PASS', name, flush=True)
summary = {'archive':str(archive), 'archive_sha256':archive_sha,
           'archive_bytes':archive.stat().st_size, 'zip_crc':'PASS',
           'extracted_files':len(members), 'extracted_root':str(root),
           'checks':results}
(receipts / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
print(json.dumps(summary, indent=2), flush=True)
