"""Build and recursively kernel-check the exact decimal policy model in a new directory."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

BASE = Path(__file__).resolve().parent
MODULE = "DecimalSignificantV4"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("output", type=Path)
    ap.add_argument("--coqc", default="coqc")
    ap.add_argument("--kernel", default="rocqchk")
    ap.add_argument("--timeout", type=int, default=180)
    args = ap.parse_args()
    output = args.output.resolve()
    source = BASE / (MODULE + ".v")
    manifest = json.loads((BASE / "SOURCE-INPUTS.json").read_text(encoding="utf-8"))
    expected = next(r["sha256"] for r in manifest["files"] if r["path"].endswith(MODULE + ".v"))
    if sha(source) != expected:
        raise ValueError("Proof source hash differs from source manifest")
    output.mkdir(parents=True, exist_ok=False)
    target = output / source.name
    target.write_bytes(source.read_bytes())
    rows = []
    for label, tool, rest in [
        ("compile", args.coqc, ["-Q", str(output), "PMPDecimal", str(target)]),
        ("recursive-kernel-check", args.kernel, ["-silent", "-o", "-Q", str(output), "PMPDecimal", "PMPDecimal." + MODULE]),
    ]:
        executable = shutil.which(tool)
        if executable is None:
            raise FileNotFoundError("Executable lookup failed: " + tool)
        argv = [executable] + rest
        before = time.perf_counter()
        p = subprocess.run(argv, cwd=output, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout)
        stdout = output / (label + ".stdout.txt")
        stderr = output / (label + ".stderr.txt")
        stdout.write_bytes(p.stdout)
        stderr.write_bytes(p.stderr)
        rows.append(dict(label=label, argv=argv, exit_code=p.returncode, timeout=False, seconds=time.perf_counter()-before, stdout=str(stdout), stderr=str(stderr), stdout_sha256=sha(stdout), stderr_sha256=sha(stderr)))
        if p.returncode:
            break
    assumptions = (output / "compile.stdout.txt").read_text(encoding="utf-8")
    result = dict(module="PMPDecimal." + MODULE, source_sha256=sha(target), steps=rows,
                  passed=(len(rows)==2 and all(r["exit_code"]==0 for r in rows)),
                  closed_assumption_receipts=assumptions.count("Closed under the global context"),
                  statement="Exact Gallina decimal model preserves leading-zero values, bounds accepted values by999999999999, and rejects a13th significant digit before arithmetic.",
                  executable_tokenization_and_bytes_correspondence="open")
    (output / "build-result.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    with (output / "SHA256SUMS.txt").open("x", encoding="utf-8") as f:
        for p in sorted(output.iterdir()):
            if p.is_file() and p.name != "SHA256SUMS.txt":
                f.write(sha(p) + " *" + p.name + "\n")
    print(json.dumps(result, indent=2))
    if not result["passed"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
