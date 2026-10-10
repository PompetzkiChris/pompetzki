"""Verify portable Book bytes, journal chain, and archive-rooted payload bindings."""
from pathlib import Path, PureWindowsPath
import csv
import hashlib
import json
import re
import sys


root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]).resolve()


def require(condition, message, *details):
    if not condition:
        raise ValueError((message, *details))


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def canon(value):
    value = str(value).replace("\\", "/")
    drive = re.search(r"[A-Za-z]:/", value)
    return (value[drive.start():] if drive else value).lower()


manifest_paths = {}


def archive_path(name, label, listed=True):
    require(isinstance(name, str) and bool(name), "empty archive path", label)
    normalized = name.replace("\\", "/")
    require(not Path(normalized).is_absolute() and not PureWindowsPath(normalized).drive,
            "archive path must be relative", label, name)
    path = (root / normalized).resolve()
    require(path.is_relative_to(root), "archive path leaves root", label, name)
    require(path.is_file(), "archive file missing", label, name)
    if listed:
        require(path in manifest_paths, "archive file absent from manifest", label, name)
    return path


manifest = 0
for line in (root / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
    digest, name = line.split(" *", 1)
    require(re.fullmatch(r"[0-9a-f]{64}", digest), "invalid manifest digest", name)
    path = archive_path(name, "manifest", listed=False)
    require(path not in manifest_paths, "duplicate manifest file", name)
    require(sha(path) == digest, "manifest mismatch", name)
    manifest_paths[path] = digest
    manifest += 1

original = json.loads(archive_path("ORIGINAL-JOURNAL-SHA256.json", "original table").read_text(encoding="utf-8"))
for name, digest in original.items():
    require(sha(archive_path("book/" + name, "original segment")) == digest,
            "original segment changed", name)

head = "0" * 64
counts = {}
stmts = set()
pairs = set()
prev = None
record_count = 0
required_payloads = {}
record_payloads = []
for sn, p in enumerate(sorted((root / "book").glob("J*.txt")), 1):
    require(p.name == f"J{sn:06}.txt", "segment number", p.name)
    p = archive_path("book/" + p.name, "journal")
    raw = p.read_bytes()
    require(raw.endswith(b"\n") and b"\r" not in raw, "journal line endings", p.name)
    lines = raw.splitlines()
    for i, line in enumerate(lines):
        body, digest = line.rsplit(b"\t", 1)
        head = hashlib.sha256(head.encode() + b"\n" + body).hexdigest()
        require(head.encode() == digest, "chain mismatch", p.name, i + 1)
        f = body.decode("utf-8").split("\t")
        kind = f[0][0]
        counts[kind] = counts.get(kind, 0) + 1
        width = 7 if kind == "B" else 6
        require(f[0] == kind + str(counts[kind]).zfill(width), "ID mismatch", f[0])
        if i == 0:
            require(kind == "H", "segment header", p.name)
            expected = "previous - -" if prev is None else f"previous book/{prev.name} {sha(prev)}"
            require(f[2] == expected, "segment link", p.name)
        if kind == "B":
            require(f[17].startswith("pmp ACCEPT ") and f[18].startswith("racket ACCEPT "),
                    "master verdict", f[0])
            require((f[4] == "Proved") == (f[8] == "hyps -"), "status", f[0])
            key = (f[5], f[6])
            require(key not in pairs, "duplicate master pair", f[0])
            pairs.add(key)
            stmts.add(f[5])
        elif kind in ("F", "N"):
            if kind == "F":
                require(f[8].startswith("pmp ACCEPT ") and f[9].startswith("racket ACCEPT "),
                        "accepted verdict", f[0])
                file_field, digest_field, size_field = f[1], f[2], f[3]
            else:
                require(f[6].startswith("pmp REJECT ") and f[7].startswith("racket REJECT "),
                        "rejected verdict", f[0])
                file_field, digest_field, size_field = f[2], f[3], f[4]
            require(file_field.startswith("file ") and digest_field.startswith("sha256 ")
                    and size_field.startswith("bytes "), "payload fields", f[0])
            original_path, payload_digest, size = file_field[5:], digest_field[7:], int(size_field[6:])
            require(payload_digest not in required_payloads or required_payloads[payload_digest] == size,
                    "conflicting admitted payload size", f[0], payload_digest)
            required_payloads[payload_digest] = size
            record_payloads.append((f[0], original_path, payload_digest, size))
        if i == len(lines) - 1:
            require(kind == "E" and int(f[2][8:]) == len(lines) - 1, "segment end", p.name)
        record_count += 1
    prev = p

payloads = 0
total = 0
bundled = {}
certificate_paths = {}
with archive_path("CERTIFICATES.tsv", "certificate table").open(encoding="utf-8", newline="") as stream:
    for row in csv.DictReader(stream, delimiter="\t"):
        p = archive_path(row["portable"], "certificate payload")
        size = int(row["bytes"])
        digest = row["sha256"]
        require(p.stat().st_size == size and sha(p) == digest, "certificate bytes mismatch", row["portable"])
        require(manifest_paths[p] == digest, "certificate digest differs from manifest", row["portable"])
        require(digest not in bundled, "duplicate certificate digest", digest)
        payloads += 1
        total += size
        bundled[digest] = size
        certificate_paths[digest] = p
for digest, size in required_payloads.items():
    require(bundled.get(digest) == size, "admitted payload not bundled", digest)

aliases = {}
with archive_path("PATH-ALIASES.tsv", "alias table").open(encoding="utf-8", newline="") as stream:
    for row in csv.DictReader(stream, delimiter="\t"):
        p = archive_path(row["portable"], "alias payload")
        require(sha(p) == row["sha256"] and manifest_paths[p] == row["sha256"],
                "alias bytes mismatch", row["original"])
        key = canon(row["original"])
        require(key not in aliases, "duplicate historical alias", row["original"])
        aliases[key] = (p, row["sha256"])
for record, historical_path, digest, size in record_payloads:
    alias = aliases.get(canon(historical_path))
    require(alias is not None, "admitted historical path missing alias", record, historical_path)
    require(alias == (certificate_paths[digest], digest), "admitted historical alias mismatch", record, historical_path)
    require(alias[0].stat().st_size == size, "admitted historical alias size mismatch", record, historical_path)

print(json.dumps({"manifest_files": manifest, "original_segments_unchanged": len(original),
                  "journal_records": record_count, "counts": counts,
                  "distinct_statements": len(stmts), "distinct_pairs": len(pairs),
                  "chain_head": head, "certificate_payloads": payloads,
                  "certificate_bytes": total, "historical_aliases": len(aliases),
                  "admitted_alias_bindings": len(record_payloads)}, indent=2))
print("PORTABLE CHECK OK")
