"""Independent ledger-chain and subprocess regressions for verified Book posting."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_chain(path):
    head = "0" * 64
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        body, actual = "\t".join(fields[:-1]), fields[-1]
        expected = hashlib.sha256((head + "\n" + body).encode()).hexdigest()
        assert actual == expected, (path, fields[0], actual, expected)
        rows.append(fields)
        head = actual
    assert rows[0][0].startswith("H") and rows[-1][0].startswith("E")
    return rows


def verify_run(out):
    metadata = json.loads((out / "run-metadata.json").read_text())
    book = verify_chain(out / "BOOK-1.0.ledger")
    negative = verify_chain(out / "NEGATIVE-1.0.ledger")
    assert "run-metadata.json " + sha(out / "run-metadata.json") in book[0]
    assert "run-metadata.json " + sha(out / "run-metadata.json") in negative[0]
    for artifact in metadata["artifacts"]:
        assert sha(artifact["path"]) == artifact["sha256"]
    for run in metadata["runs"]:
        assert sha(run["snapshot"]) == run["input_sha256_before"] == run["input_sha256_after"]
        assert run["unchanged"]
        for name in ("pmp", "racket"):
            receipt = run[name]
            assert receipt["command"][-1] == run["snapshot"]
            assert sha(receipt["stdout"]) == receipt["stdout_sha256"]
            assert sha(receipt["stderr"]) == receipt["stderr_sha256"]
            assert receipt["end_epoch_ms"] >= receipt["start_epoch_ms"]
    return {
        "F": sum(row[0].startswith("F") for row in book),
        "B": sum(row[0].startswith("B") for row in book),
        "N": sum(row[0].startswith("N") for row in negative),
        "inputs": len(metadata["runs"]),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--racket", default=r"C:\Program Files\Racket\racket.exe")
    parser.add_argument("--poster", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    poster = args.poster or here / "verified-book-post.rkt"
    command = ([str(poster)] if poster.suffix.lower() == ".exe" else [args.racket, str(poster)])
    fixtures = args.bundle / "judge" / "registry-tests-v4b"
    dest = here / "tests" / ("regression-" + time.strftime("%Y%m%d-%H%M%S"))
    dest.mkdir(parents=True, exist_ok=False)
    results = []

    def run(name, files, expected, timeout="30", interpreted=False):
        out = dest / name
        argv = command + ["--bundle", str(args.bundle), "--timeout", timeout] + (["--interpreted"] if interpreted else []) + [str(out), "2026-10-12 UTC", *map(str, files)]
        p = subprocess.run(argv, capture_output=True, timeout=90)
        (dest / (name + ".stdout.txt")).write_bytes(p.stdout)
        (dest / (name + ".stderr.txt")).write_bytes(p.stderr)
        counts = verify_run(out)
        assert (p.returncode, counts) == expected, (name, p.returncode, counts, p.stderr)
        results.append({"case": name, "command": argv, "exit": p.returncode, "counts": counts, "pass": True})
        return out, argv

    mixed, argv = run("mixed", [fixtures / "prefix-0-truth.jdg", fixtures / "leading-zero-and-tab-prefix.jdg",
                               fixtures / "false-proof-empty-registry.jdg", fixtures / "forged-false-registry.jdg"],
                     (0, {"F": 2, "B": 2, "N": 2, "inputs": 4}))
    before = {str(p.relative_to(mixed)): sha(p) for p in mixed.rglob("*") if p.is_file()}
    refused = subprocess.run(argv, capture_output=True, timeout=20)
    after = {str(p.relative_to(mixed)): sha(p) for p in mixed.rglob("*") if p.is_file()}
    (dest / "refused.stdout.txt").write_bytes(refused.stdout)
    (dest / "refused.stderr.txt").write_bytes(refused.stderr)
    assert refused.returncode == 3 and b"output already exists" in refused.stderr and before == after
    results.append({"case": "existing-output-refused", "exit": refused.returncode, "files_unchanged": before == after, "pass": True})

    # A real interpreter deadline tests UNKNOWN -> SUSPENSE -> nonzero status.
    replay = args.bundle / "data" / "replay-all.jdg"
    if not replay.exists():
        candidates = list(args.bundle.rglob("replay-all.jdg"))
        replay = next(p for p in candidates if p.stat().st_size > 1000000)
    timeout_out, _ = run("timeout", [replay], (3, {"F": 0, "B": 0, "N": 0, "inputs": 1}), timeout="1", interpreted=True)
    assert b"SUSPENSE 1" in (dest / "timeout.stdout.txt").read_bytes()
    assert any(r["pmp"]["exit_code"] == 124 for r in json.loads((timeout_out / "run-metadata.json").read_text())["runs"])

    direct = subprocess.run([args.racket, str(here / "book-post-v3.rkt"), "forged-accept.tsv", str(dest / "forged-post")], capture_output=True, timeout=20)
    assert direct.returncode == 2 and not (dest / "forged-post").exists()
    results.append({"case": "direct-receipt-import-refused", "exit": direct.returncode, "pass": True})
    report = {"cases": len(results), "passed": len(results), "results": results, "source_sha256": sha(poster)}
    (dest / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    files = sorted(p for p in dest.rglob("*") if p.is_file())
    (dest / "SHA256SUMS.txt").write_text("".join(sha(p) + "  " + str(p.relative_to(dest)) + "\n" for p in files))
    print(json.dumps({"output": str(dest), "cases": len(results), "passed": len(results)}, indent=2))


if __name__ == "__main__":
    main()
