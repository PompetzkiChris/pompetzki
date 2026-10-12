python3 << 'PY'
import hashlib, json, re, resource, struct, subprocess, time
from pathlib import Path

ROOT = Path("/tmp/a131/src/Abschluss-1.3.1-source")
SCRIPT = ROOT / "repair/packaging/v9-judge-v6-1.3.1/test-count-bounds.py"
NATIVE = Path("/tmp/a131/native-linux/judge-v6-linux")
INTERP = Path("/tmp/a131/interpreter-linux/pompetzki")
JUDGE = ROOT / "judge/judge-v6.pmp"
OUT = Path("/tmp/a131/controls")
OUT.mkdir(exist_ok=True)
AS = 1280 * 1024 * 1024

def limits():
    resource.setrlimit(resource.RLIMIT_AS, (AS, AS))
    resource.setrlimit(resource.RLIMIT_DATA, (AS, AS))
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))

lines = SCRIPT.read_text().splitlines()
ns = {}
exec("\n".join(lines[10:23]), ns)
cases = ns["cases"]
assert len(cases) == 10
routes = {"native": [str(NATIVE)], "interpreted": [str(INTERP), str(JUDGE)]}
rows = []
for name, data, want in cases:
    path = OUT / (name + ".jdg")
    path.write_bytes(data)
    for route, argv in routes.items():
        command = [*argv, str(path)]
        began = time.monotonic()
        proc = subprocess.run(command, cwd=OUT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20, preexec_fn=limits)
        dt = time.monotonic() - began
        stem = f"{name}-{route}"
        (OUT / (stem + ".stdout.txt")).write_bytes(proc.stdout)
        (OUT / (stem + ".stderr.txt")).write_bytes(proc.stderr)
        (OUT / (stem + ".exit.txt")).write_text(str(proc.returncode) + "\n")
        tokens = set(re.findall(rb"\b(?:ACCEPT|REJECT|LIMIT)\b", proc.stdout))
        verdict = next(iter(tokens)).decode() if len(tokens) == 1 else "OTHER"
        passed = proc.returncode == (0 if want == "ACCEPT" else 1) and verdict == want
        rows.append({
            "case": name, "route": route, "expected": want, "verdict": verdict,
            "exit": proc.returncode, "passed": passed, "seconds": round(dt, 4),
            "command": command, "input_bytes": len(data),
            "input_sha256": hashlib.sha256(data).hexdigest(),
            "stdout_sha256": hashlib.sha256(proc.stdout).hexdigest(),
            "stdout_head": proc.stdout.decode("utf-8", "replace").splitlines()[:4],
        })
        print(f"{stem}\t{verdict}\texit {proc.returncode}\t{'OK' if passed else 'FAIL'}")
print("passed", sum(r["passed"] for r in rows), "failed", sum(not r["passed"] for r in rows))
(OUT / "results.json").write_text(json.dumps({
    "source_zip_sha256": "8db56c0cd336d84f3c4b6f867324683c28f33e8c390f773926a4c21ac225282a",
    "source_zip_bytes": 180990181,
    "tag_target": "c5253c0922f553b1ac8ef18240c1c372ff39657f",
    "rlimit_as": AS, "rlimit_data": AS, "rlimit_cpu_seconds": 30,
    "passed": sum(r["passed"] for r in rows),
    "failed": sum(not r["passed"] for r in rows),
    "runs": len(rows),
    "not_a_compiler_preservation_proof": True,
    "rows": rows,
}, indent=2) + "\n")
PY
