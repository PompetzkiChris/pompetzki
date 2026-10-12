#!/usr/bin/env python3
"""Leading-zero and malformed-number tests for the capped gate and for v5.

Specification, the same rule as decimal 02 = 2:
a token of one or more digits denotes that integer. Leading zeros do not
change the value. A different integer is a formula or hypothesis mismatch.
A token that is not digits is a parse failure, before any proof check.

The 2026-10-12 capped gate uses v4's 12-digit RDNUM limit. Padding that makes
the token 13 digits or longer is a parse failure there, even when the integer
matches. That is the discrepancy. This script executes both gates.
"""
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
V5 = HERE
V4 = Path(os.environ.get("V4_GATE", ROOT / "v4cap"))
_default_pomp = Path("/workspace/pmp-audit/linux-judge/bin/linux/pompetzki")
POMP = os.environ.get("POMPETZKI") or (str(_default_pomp) if _default_pomp.is_file() else "pompetzki")
OLD_MUT = Path(os.environ.get("GATE_MUTANTS", ROOT / "mutants"))
FIX = Path(os.environ.get("GATE_FIXTURES", ROOT / "fixtures"))
OUT = V5 / "tests"
OUT.mkdir(exist_ok=True)

ENTRY0 = ["a", "a", "i", "a", "b", "e", "0", "2", "e", "0", "1", "q", "1", "0", "0"]
# index of the first value 2, and the hyp-count 0 at the end
TWO = ENTRY0.index("2")
HYP = len(ENTRY0) - 1


def jdg(tokens):
    body = " ".join(tokens)
    return f"JDG1\nR 1\n{body}\nT 0\n".encode("ascii")


def classify(text):
    lines = [ln for ln in text.splitlines() if "check zero failed" not in ln and ln.strip()]
    if not lines:
        return "EMPTY", ""
    if lines[0] == "GATE":
        return "GATE", ""
    if lines[0] == "REJECT registry" and len(lines) >= 2:
        if lines[1] in ("parse", "count", "embed"):
            return "REJECT", lines[1]
        if len(lines) >= 3:
            return "REJECT", lines[2]
    return "OTHER", " | ".join(lines[:4])


def run_pmp(gate_dir, path):
    proc = subprocess.run(
        [POMP, str(gate_dir / "reggate.pmp"), str(path)],
        capture_output=True, text=True, timeout=30,
    )
    return classify(proc.stdout + proc.stderr), proc.returncode


def run_py(gate_dir, path):
    proc = subprocess.run(
        [sys.executable, str(gate_dir / "gate.py"), str(path)],
        capture_output=True, text=True, timeout=30,
    )
    return classify(proc.stdout + proc.stderr), proc.returncode


def main():
    work = OUT / "padding-inputs"
    work.mkdir(exist_ok=True)
    log = []

    def say(s=""):
        log.append(s)
        print(s, flush=True)

    cases = []

    def add(name, tokens, spec):
        path = work / (name + ".jdg")
        path.write_bytes(jdg(tokens))
        cases.append((name, path, spec))

    def pad_two(nzeros):
        tok = list(ENTRY0)
        tok[TWO] = ("0" * nzeros) + "2"
        return tok

    def pad_zero_in_formula(nzeros):
        tok = list(ENTRY0)
        tok[ENTRY0.index("0")] = "0" * nzeros
        return tok

    def pad_hyp(nzeros):
        tok = list(ENTRY0)
        tok[HYP] = "0" * nzeros
        return tok

    # Specification for value-preserving padding is GATE.
    for n in (12, 13, 64, 1024):
        add(f"zeros{n}-then-2", pad_two(n), ("GATE", ""))
        add(f"zeros{n}-value0", pad_zero_in_formula(n), ("GATE", ""))
    add("digits12-value2", pad_two(11), ("GATE", ""))  # 11 zeros + 2 = 12 digits
    add("zeros12-hypcount", pad_hyp(12), ("GATE", ""))
    add("zeros13-hypcount", pad_hyp(13), ("GATE", ""))
    add("zeros1024-hypcount", pad_hyp(1024), ("GATE", ""))

    huge = list(ENTRY0)
    huge[TWO] = "9" * 64
    add("huge-64-nines", huge, ("REJECT", "formula"))
    huge = list(ENTRY0)
    huge[TWO] = "9" * 1024
    add("huge-1024-nines", huge, ("REJECT", "formula"))
    huge = list(ENTRY0)
    huge[TWO] = "2" + ("0" * 100)  # 2 * 10^100, not 2
    add("huge-2-then-100-zeros", huge, ("REJECT", "formula"))
    huge = list(ENTRY0)
    huge[TWO] = "9223372036854775807"  # 19 significant digits, not 2
    add("huge-int64-max", huge, ("REJECT", "formula"))
    huge = list(ENTRY0)
    huge[HYP] = "1" + ("0" * 64)  # hyp count 10^64, canon is 0
    add("huge-hypcount", huge, ("REJECT", "hypotheses"))

    def bad(name, spelling):
        tok = list(ENTRY0)
        tok[TWO] = spelling
        add(name, tok, ("REJECT", "parse"))

    bad("malformed-0.0", "0.0")
    bad("malformed-plus2", "+2")
    bad("malformed-minus1", "-1")
    bad("malformed-2a", "2a")
    bad("malformed-0x2", "0x2")
    bad("malformed-dot", ".")
    bad("malformed-2dot", "2.")

    # The capped gate rejects a digit token longer than 12, including padding
    # and huge integers. Twelve digits exactly still pass. Malformed stays parse.
    cap_parse = {
        "zeros12-then-2", "zeros13-then-2", "zeros64-then-2", "zeros1024-then-2",
        "zeros13-value0", "zeros64-value0", "zeros1024-value0",
        "zeros13-hypcount", "zeros1024-hypcount",
        "huge-64-nines", "huge-1024-nines", "huge-2-then-100-zeros",
        "huge-int64-max", "huge-hypcount",
    }

    say("specification is the integer value; v4-cap is the 12-digit gate; v5 drops that cap")
    say("name\tspec\tv4-cap pmp\tv4-cap py\tv5 pmp\tv5 py")
    failed = 0
    for name, path, spec in cases:
        cap_expected = ("REJECT", "parse") if name in cap_parse else spec
        results = {}
        for label, directory, expected in (
            ("v4cap-pmp", V4, cap_expected),
            ("v4cap-py", V4, cap_expected),
            ("v5-pmp", V5, spec),
            ("v5-py", V5, spec),
        ):
            got, code = (run_pmp if label.endswith("pmp") else run_py)(directory, path)
            results[label] = got
            ok = got == expected and ((code == 0) == (expected[0] == "GATE"))
            if not ok:
                failed += 1
                say(f"FAIL {label} {name} expected {expected} got {got} exit {code}")
        say(
            f"{name}\t{spec[0]}:{spec[1] or '-'}\t"
            f"{results['v4cap-pmp'][0]}:{results['v4cap-pmp'][1] or '-'}\t"
            f"{results['v4cap-py'][0]}:{results['v4cap-py'][1] or '-'}\t"
            f"{results['v5-pmp'][0]}:{results['v5-pmp'][1] or '-'}\t"
            f"{results['v5-py'][0]}:{results['v5-py'][1] or '-'}"
        )

    say("")
    say("v5 regression against preserved mutants and the public leading-zero fixture")
    regressions = [
        (OLD_MUT / "fail-false.jdg", ("REJECT", "formula")),
        (OLD_MUT / "fail-spell-0.jdg", ("GATE", "")),
        (OLD_MUT / "fail-hypcount-spell-0.jdg", ("GATE", "")),
        (OLD_MUT / "fail-hyp-spell-677.jdg", ("GATE", "")),
        (OLD_MUT / "pass-empty.jdg", ("GATE", "")),
        (OLD_MUT / "proof-reject-false-axiom.jdg", ("GATE", "")),
        (FIX / "leading-zero-and-tab-prefix.jdg", ("GATE", "")),
        (FIX / "forged-false-registry.jdg", ("REJECT", "formula")),
        (FIX / "altered-pure-hypotheses.jdg", ("REJECT", "hypotheses")),
        (FIX / "registry-707-entries.jdg", ("REJECT", "count")),
    ]
    for path, expected in regressions:
        for label, fn in (("v5-pmp", run_pmp), ("v5-py", run_py)):
            got, code = fn(V5, path)
            ok = got == expected and ((code == 0) == (expected[0] == "GATE"))
            if not ok:
                failed += 1
                say(f"FAIL {label} {path.name} expected {expected} got {got} exit {code}")
            else:
                say(f"ok {label} {path.name} {got[0]}:{got[1] or '-'}")

    say("")
    say(f"failures {failed}")
    if failed:
        say("PADDING CHECKS FAILED")
    else:
        say("ALL PADDING CHECKS PASSED")
    (OUT / "padding-output.txt").write_text("\n".join(log) + "\n", encoding="utf-8")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
