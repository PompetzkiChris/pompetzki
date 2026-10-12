"""Exact Word64 division/remainder cases, crash controls and emitted programs."""
import ctypes
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import time

root = Path(__file__).resolve().parent
if os.name == "nt":
    ctypes.windll.kernel32.SetErrorMode(0x8003)
out = root / ("tests-" + time.strftime("%Y%m%d-%H%M%S"))
out.mkdir(exist_ok=False)
minimum, maximum = -(1 << 63), (1 << 63) - 1
rng = random.Random(20261011)
pairs = list(__import__('itertools').product([minimum, minimum+1, maximum, -2, -1, 0, 1, 2], repeat=2))
pairs += [(rng.randint(minimum, maximum), rng.randint(minimum, maximum)) for _ in range(120)]
rows = []


def execute(exe, program, prefix):
    p = subprocess.run([str(exe), str(program)], capture_output=True, timeout=10,
                       creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)
    (out / (prefix + ".stdout.txt")).write_bytes(p.stdout)
    (out / (prefix + ".stderr.txt")).write_bytes(p.stderr)
    return p


for mode, exe in [("console", root / "build-windows-01/pompetzki.exe"), ("window", root / "build-windows-01/pompetzki-w.exe")]:
    for i, (a, b) in enumerate(pairs):
        for op in ["div", "mod"]:
            name = f"{mode}-{i}-{op}"
            program = out / (name + ".pmp")
            program.write_text(f"trace off\nset X {op} {a} {b}\ntext S int X\nprint S\n")
            p = execute(exe, program, name)
            if b:
                q = (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)
                value = q if op == "div" else a - q * b
                value = (value + (1 << 63)) % (1 << 64) - (1 << 63)
                passed = p.returncode == 0 and p.stdout.strip() == str(value).encode()
                expected = str(value)
            else:
                passed = p.returncode == 1
                expected = "zero divisor rejected"
            rows.append({"mode": mode, "op": op, "a": str(a), "b": str(b), "expected": expected,
                         "exit": p.returncode, "stdout": p.stdout.decode(errors="replace"), "passed": passed})
            if (a, b) == (minimum, -1):
                emitted = out / (name + ".exe")
                emit = subprocess.run([str(exe), "emit", str(program), str(emitted)], capture_output=True, timeout=20,
                                      creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)
                (out / (name + ".emit.stdout.txt")).write_bytes(emit.stdout)
                (out / (name + ".emit.stderr.txt")).write_bytes(emit.stderr)
                ep = subprocess.run([str(emitted)], capture_output=True, timeout=10, creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0)
                (out / (name + ".emitted.stdout.txt")).write_bytes(ep.stdout)
                (out / (name + ".emitted.stderr.txt")).write_bytes(ep.stderr)
                rows.append({"mode": mode+"-emitted", "op": op, "exit": ep.returncode,
                             "stdout": ep.stdout.decode(errors="replace"), "passed": emit.returncode == 0 and ep.returncode == 0 and ep.stdout.strip() == expected.encode()})

old = root.parent / "runtime/build/repaired/pompetzki.exe"
controls = []
for op in ["div", "mod"]:
    program = out / ("old-crash-"+op+".pmp")
    program.write_text(f"trace off\nset A sub -9223372036854775807 1\nset X {op} A -1\ntext S int X\nprint S\n")
    p = execute(old, program, "old-crash-"+op)
    controls.append({"op": op, "exit": p.returncode, "stdout": p.stdout.decode(errors="replace"), "crash_reproduced": p.returncode not in (0, 1)})
assert all(c["crash_reproduced"] for c in controls)
report = {"cases": len(rows), "passed": sum(r["passed"] for r in rows), "failed": sum(not r["passed"] for r in rows),
          "old_controls": controls, "rows": rows, "source_sha256": hashlib.sha256((root/"source/pompetzki.asm").read_bytes()).hexdigest()}
(out / "results.json").write_text(json.dumps(report, indent=2)+"\n")
(out / "SHA256SUMS.txt").write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest()+"  "+p.name+"\n" for p in sorted(out.iterdir()) if p.is_file()))
print(json.dumps({"output": str(out), "cases": report["cases"], "passed": report["passed"], "failed": report["failed"], "old_controls": controls}))
raise SystemExit(1 if report["failed"] else 0)
