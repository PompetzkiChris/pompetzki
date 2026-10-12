#!/usr/bin/env python3
"""Full route: v6 gate, then judge-v5. The v5 wrapper still calls judge-v3.

A canonical proof whose numbers are written with 13 digits, and the same
proof with 4301-zero spellings of zero, must GATE and then ACCEPT.
The judge-v3 route GATEs and then REJECTS.
"""
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
V5 = HERE.parent / "v5"
POMP = os.environ.get("POMPETZKI") or (
    "/workspace/pmp-audit/linux-judge/bin/linux/pompetzki"
    if Path("/workspace/pmp-audit/linux-judge/bin/linux/pompetzki").is_file()
    else "pompetzki"
)
JUDGE_V3 = os.environ.get("JUDGE_V3") or (
    "/workspace/pmp-audit/linux-judge/judge/judge-v3.pmp"
    if Path("/workspace/pmp-audit/linux-judge/judge/judge-v3.pmp").is_file()
    else ""
)
JUDGE_V5 = os.environ.get("JUDGE_V5") or str(ROOT / "judge" / "judge-v5.pmp")
BASE = (HERE.parent / "fixtures" / "prefix-1-truth.jdg").read_text(encoding="ascii")


def pad_digits(text, spell):
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    padded = []
    for ln in lines:
        parts = []
        for raw in ln.split():
            parts.append(spell(int(raw)) if raw.isdigit() else raw)
        padded.append(" ".join(parts))
    return ("\n".join(padded) + "\n").encode("ascii")


def spell13(value):
    return f"{value:013d}"


def spell_long(value):
    if value == 0:
        return "0" * 4301
    return ("0" * 13) + str(value)


def run(cmd, env=None):
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120, env=env)
    return proc.returncode, proc.stdout + proc.stderr


def main():
    work = HERE / "tests" / "wrapper-inputs"
    work.mkdir(parents=True, exist_ok=True)
    pad13 = work / "prefix-1-digits13.jdg"
    longz = work / "prefix-1-zeros4301.jdg"
    pad13.write_bytes(pad_digits(BASE, spell13))
    longz.write_bytes(pad_digits(BASE, spell_long))
    log = []
    failed = 0

    def say(s=""):
        log.append(s)
        print(s, flush=True)

    def check(cond, label):
        nonlocal failed
        if cond:
            say(f"ok {label}")
        else:
            failed += 1
            say(f"FAIL {label}")

    env = os.environ.copy()
    env["POMPETZKI"] = POMP
    env["JUDGE_V5"] = JUDGE_V5
    env["JUDGE_V3"] = JUDGE_V3
    wrapper = str(HERE / "judge-gated-v5.sh")
    old = str(V5 / "judge-gated.sh")

    for name, path in (("digits13", pad13), ("zeros4301", longz)):
        code, text = run(["sh", wrapper, str(path)], env)
        first = [ln for ln in text.splitlines() if ln.strip()]
        say(f"--- v6+judge-v5 {name} exit {code}")
        say("\n".join(first[:8]))
        check(code == 0 and first and first[0] == "GATE" and "ACCEPT" in text,
              f"full v5-judge route {name}")
        code3, text3 = run(["sh", old, str(path)], env)
        lines3 = [ln for ln in text3.splitlines() if ln.strip()]
        say(f"--- v5 wrapper + judge-v3 {name} exit {code3}")
        say("\n".join(lines3[:8]))
        check(lines3 and lines3[0] == "GATE" and "REJECT" in text3 and code3 != 0,
              f"judge-v3 route rejects after GATE {name}")

    say("")
    say(f"failures {failed}")
    say("ALL WRAPPER CHECKS PASSED" if failed == 0 else "WRAPPER CHECKS FAILED")
    (HERE / "tests" / "wrapper-output.txt").write_text("\n".join(log) + "\n", encoding="utf-8")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
