"""Rejudge positive/negative postings and detect separately preserved corrupt copies."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--bundle", type=Path, required=True)
parser.add_argument("--checker", type=Path)
parser.add_argument("--poster", type=Path)
parser.add_argument("--racket", default=r"C:\Program Files\Racket\racket.exe")
args = parser.parse_args()
base = Path(__file__).resolve().parent
checker = args.checker or base / "verified-book-check.rkt"
command = ([str(checker)] if checker.suffix == ".exe" else [args.racket, str(checker)])
out = base / "tests" / ("check-regression-" + time.strftime("%Y%m%d-%H%M%S"))
out.mkdir(exist_ok=False)
results = []
inputs = out / "inputs"
inputs.mkdir()
for name, body in {
    "true.jdg": "JDG1 R 0 T 1 a q 0 0 0 2 Y q 0 0 G 0 0 0\n",
    "true-leading-zeros.jdg": "JDG1\tR 00\tT 01\ta q 00 000 00 02 Y q 00 00 G 00 00 00\n",
    "false-step.jdg": "JDG1 R 0 T 1 a n q 0 0 0 1 Y a n q 0 0 0\n",
    "false-registry.jdg": "JDG1 R 1 a n q 0 0 0 T 1 a n q 0 0 0 1 U 0 0 0\n",
}.items():
    (inputs / name).write_text(body)
source = out / "original-posting"
poster = args.poster or base / "verified-book-post.rkt"
post_command = ([str(poster)] if poster.suffix == ".exe" else [args.racket, str(poster)])
post = subprocess.run(post_command + ["--bundle", str(args.bundle), str(source), "2026-10-12 UTC", str(inputs)], capture_output=True, timeout=60)
(out / "create-posting.stdout.txt").write_bytes(post.stdout)
(out / "create-posting.stderr.txt").write_bytes(post.stderr)
assert post.returncode == 0, post.stderr


def run(name, folder, expected):
    p = subprocess.run(command + ["--bundle", str(args.bundle), str(folder)], capture_output=True, timeout=60)
    (out / (name + ".stdout.json")).write_bytes(p.stdout)
    (out / (name + ".stderr.txt")).write_bytes(p.stderr)
    assert p.returncode == expected, (name, p.returncode, p.stderr)
    results.append({"case": name, "exit": p.returncode, "expected": expected, "passed": True})
    return p


valid = out / "relocated-valid"
shutil.copytree(source, valid)
p = run("relocated-valid", valid, 0)
report = json.loads(p.stdout)
assert (report["positive_files"], report["theorems"], report["negative_files"]) == (2, 2, 2)

for name in ["input-tamper", "output-tamper", "metadata-tamper", "theorem-tamper"]:
    target = out / name
    shutil.copytree(source, target)
    if name == "input-tamper":
        next((target / "judge-inputs").glob("*.jdg")).write_text("JDG1 R 0 T 0\n")
    elif name == "output-tamper":
        next((target / "judge-runs").glob("*.stdout.txt")).write_text("forged ACCEPT\n")
    elif name == "metadata-tamper":
        path = target / "run-metadata.json"
        meta = json.loads(path.read_text())
        meta["posting_date"] = "altered"
        path.write_text(json.dumps(meta))
    else:
        # Recompute the whole chain after replacing a theorem statement hash.
        # A chain-only verifier would accept this internally consistent rewrite.
        path = target / "BOOK-1.0.ledger"
        chain, output, changed = "0" * 64, [], False
        for line in path.read_text(encoding="utf-8").splitlines():
            fields = line.split("\t")[:-1]
            if fields[0].startswith("B") and not changed:
                index = next(i for i, value in enumerate(fields) if value.startswith("stmt "))
                fields[index] = "stmt " + "f" * 64
                changed = True
            body = "\t".join(fields)
            chain = hashlib.sha256((chain + "\n" + body).encode()).hexdigest()
            output.append(body + "\t" + chain)
        assert changed
        path.write_text("\n".join(output) + "\n", encoding="utf-8", newline="\n")
    run(name, target, 1)

(out / "results.json").write_text(json.dumps({"cases": len(results), "passed": len(results), "results": results}, indent=2) + "\n")
(out / "SHA256SUMS.txt").write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest() + "  " + str(p.relative_to(out)) + "\n" for p in sorted(out.rglob("*")) if p.is_file()))
print(json.dumps({"output": str(out), "cases": len(results), "passed": len(results)}))
