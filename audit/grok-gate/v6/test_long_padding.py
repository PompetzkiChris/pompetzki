#!/usr/bin/env python3
"""4301- and 5000-digit padding, and the 12-significant-digit domain.

The default integer-string limit stays in force. This file does not call
sys.set_int_max_str_digits. v5 remains the previous parser and is only
observed: its Python route raises ValueError on these paddings.
"""
import importlib.util
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
V5 = HERE.parent / "v5"
V6 = HERE
POMP = os.environ.get("POMPETZKI") or (
    "/workspace/pmp-audit/linux-judge/bin/linux/pompetzki"
    if Path("/workspace/pmp-audit/linux-judge/bin/linux/pompetzki").is_file()
    else "pompetzki"
)
ENTRY0 = ["a", "a", "i", "a", "b", "e", "0", "2", "e", "0", "1", "q", "1", "0", "0"]
TWO = ENTRY0.index("2")
ZERO = ENTRY0.index("0")
HYP = len(ENTRY0) - 1


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def jdg(tokens):
    return f"JDG1\nR 1\n{' '.join(tokens)}\nT 0\n".encode("ascii")


def classify(text):
    lines = [ln for ln in text.splitlines() if "check zero failed" not in ln and ln.strip()]
    if not lines:
        return "EMPTY"
    if lines[0] == "GATE":
        return "GATE"
    if lines[0] == "REJECT registry" and len(lines) >= 2:
        if lines[1] in ("parse", "count", "embed"):
            return "REJECT:" + lines[1]
        if len(lines) >= 3:
            return "REJECT:" + lines[2]
    return "OTHER"


def run_pmp(directory, path):
    proc = subprocess.run(
        [POMP, str(directory / "reggate.pmp"), str(path)],
        capture_output=True, text=True, timeout=60,
    )
    return classify(proc.stdout + proc.stderr), proc.returncode


def run_py(directory, path):
    proc = subprocess.run(
        [sys.executable, str(directory / "gate.py"), str(path)],
        capture_output=True, text=True, timeout=60,
    )
    blob = proc.stdout + proc.stderr
    if proc.returncode != 0 and "Exceeds the limit" in blob:
        return "ValueError", proc.returncode
    return classify(blob), proc.returncode


def main():
    v6 = load("gate_v6", V6 / "gate_core.py")
    v5 = load("gate_v5", V5 / "gate_core.py")
    limit = sys.get_int_max_str_digits()
    log = []

    def say(s=""):
        log.append(s)
        print(s, flush=True)

    failed = 0

    def check(cond, label):
        nonlocal failed
        if cond:
            say(f"ok {label}")
        else:
            failed += 1
            say(f"FAIL {label}")

    check(limit == 4300, f"default digit limit is 4300, got {limit}")
    check("set_int_max_str_digits(" not in (V6 / "gate_core.py").read_text(encoding="utf-8"),
          "v6 source does not call set_int_max_str_digits")
    check(v6.parse_decimal("0" * 4301) == 0, "4301 zeros -> 0")
    check(v6.parse_decimal("0" * 5000) == 0, "5000 zeros -> 0")
    check(v6.parse_decimal(("0" * 4301) + "2") == 2, "4301 zeros then 2 -> 2")
    check(v6.parse_decimal(("0" * 5000) + "2") == 2, "5000 zeros then 2 -> 2")
    check(v6.parse_decimal("9" * 12) == 999999999999, "12 nines in domain")
    check(v6.parse_decimal("9" * 13) is None, "13 nines out of domain")
    check(v6.parse_decimal("1" + ("0" * 12)) is None, "10^12 out of domain")
    check(v6.parse_decimal("9" * 4301) is None, "4301 nines refused before int()")
    check(v6.parse_decimal("9" * 5000) is None, "5000 nines refused before int()")
    check(sys.get_int_max_str_digits() == 4300, "limit unchanged after parse_decimal")

    for n, label in ((4301, "4301"), (5000, "5000")):
        try:
            v5.Scan(b"0" * n).num()
            check(False, f"v5 Scan.num raises on {label} zeros")
        except ValueError as exc:
            check("Exceeds the limit" in str(exc), f"v5 Scan.num ValueError on {label} zeros")
        check(v6.Scan(b"0" * n).num() == 0, f"v6 Scan.num {label} zeros is 0")

    work = V6 / "tests" / "long-inputs"
    work.mkdir(parents=True, exist_ok=True)
    cases = []

    def add(name, tokens, spec):
        path = work / (name + ".jdg")
        path.write_bytes(jdg(tokens))
        cases.append((name, path, spec))

    def with_token(index, spelling):
        tok = list(ENTRY0)
        tok[index] = spelling
        return tok

    for n in (4301, 5000):
        add(f"zeros{n}-value0", with_token(ZERO, "0" * n), "GATE")
        add(f"zeros{n}-hypcount", with_token(HYP, "0" * n), "GATE")
        add(f"zeros{n}-then-2", with_token(TWO, ("0" * n) + "2"), "GATE")
    add("sig13", with_token(TWO, "1" + ("0" * 12)), "REJECT:parse")
    add("nines13", with_token(TWO, "9" * 13), "REJECT:parse")
    add("nines4301", with_token(TWO, "9" * 4301), "REJECT:parse")
    add("nines5000", with_token(TWO, "9" * 5000), "REJECT:parse")
    add("domain-max-not-2", with_token(TWO, "9" * 12), "REJECT:formula")

    say("name\tv5-py\tv5-pmp\tv6-py\tv6-pmp\tspec")
    for name, path, spec in cases:
        v5py, _ = run_py(V5, path)
        v5pmp, v5code = run_pmp(V5, path)
        v6py, v6pycode = run_py(V6, path)
        v6pmp, v6code = run_pmp(V6, path)
        say(f"{name}\t{v5py}\t{v5pmp}\t{v6py}\t{v6pmp}\t{spec}")
        if name.startswith("zeros"):
            check(v5py == "ValueError", f"v5 py {name} ValueError")
            check(v5pmp == "GATE" and v5code == 0, f"v5 pmp {name} GATE")
        check(v6py == spec and ((v6pycode == 0) == (spec == "GATE")), f"v6 py {name}")
        check(v6pmp == spec and ((v6code == 0) == (spec == "GATE")), f"v6 pmp {name}")

    check(sys.get_int_max_str_digits() == 4300, "limit unchanged after the suite")
    say("")
    say(f"failures {failed}")
    say("ALL LONG PADDING CHECKS PASSED" if failed == 0 else "LONG PADDING CHECKS FAILED")
    out = V6 / "tests" / "long-padding-output.txt"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(log) + "\n", encoding="utf-8")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
