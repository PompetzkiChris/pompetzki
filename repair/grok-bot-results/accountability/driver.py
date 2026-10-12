#!/usr/bin/env python3
"""Independent regression driver for three pompetzki defects. Exact string/integer comparison only.
usage: driver.py --interp PMP_INTERP --judge JUDGE --strx STRX_PMP [--rawdir DIR] [--label NAME]
  JUDGE: a native judge executable, or a .pmp judge run as `PMP_INTERP JUDGE FILE`.
Exit 0 iff every case matches its expected (correct) behaviour."""
import argparse, os, shutil, subprocess, sys, tempfile
H = os.path.dirname(os.path.abspath(__file__)); I = os.path.join(H, "inputs")
def run(cmd, cwd=None):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=600)
    return p.stdout.decode("latin-1"), p.stderr.decode("latin-1"), p.returncode
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--interp", required=True); ap.add_argument("--judge", required=True)
    ap.add_argument("--strx", required=True); ap.add_argument("--rawdir"); ap.add_argument("--label", default="run")
    a = ap.parse_args(); interp = os.path.abspath(a.interp); judge = os.path.abspath(a.judge)
    jcmd = (lambda f: [interp, judge, f]) if judge.endswith(".pmp") else (lambda f: [judge, f])
    first = lambda s: s.split("\n")[0].strip()
    lines = lambda s: [x.strip() for x in s.strip().split("\n")]
    # judge cases: verdict = the REJECT/ACCEPT line anywhere in stdout. (id, defect, command builder, check(stdout,exit) -> bool, expected description)
    cases = []
    for f, exp in [("a1-false-registry-only.jdg", "REJECT"), ("a2-false-registry-thm.jdg", "REJECT"), ("ctl-canonical-reg0.jdg", "ACCEPT")]:
        cases.append((f, "a", jcmd(os.path.join(I, f)), None, exp, 0 if exp == "ACCEPT" else 1))
    for f, out, ex in [("b1-literal-min.pmp", "-9223372036854775808", 0), ("b2-computed-min.pmp", "-9223372036854775808", 0),
                       ("b3-literal-max.pmp", "9223372036854775807", 0), ("b4-literal-overflow.pmp", "line 1: Menschenwerk: a value left the 64-bit integers. Nothing was rounded; the program stops.", 1),
                       ("b5-literal-underflow.pmp", "line 1: Menschenwerk: a value left the 64-bit integers. Nothing was rounded; the program stops.", 1)]:
        cases.append((f, "b", [interp, os.path.join(I, f)], None, out, ex))
    # strx: trim " a\0b " -> len 3, bytes 97 0 98; input bytes 0,2,3 preserved = 32 0 98.  pad-right [0 97] to 4 with '.' -> 0 97 46 46
    cases.append(("c1-trim-nul.pmp", "c", None, os.path.join(I, "c1-trim-nul.pmp"), "3 97 0 98 32 0 98", 0))
    cases.append(("c2-pad-nul.pmp", "c", None, os.path.join(I, "c2-pad-nul.pmp"), "4 0 97 46 46", 0))
    fails = 0; rows = []; cap = []
    for cid, d, cmd, src, exp, exexit in cases:
        if src:
            td = tempfile.mkdtemp(); shutil.copy(a.strx, os.path.join(td, "strx.pmp")); shutil.copy(src, os.path.join(td, cid))
            cmd = [interp, cid]; o, e, rc = run(cmd, cwd=td); got = " ".join(lines(o)); shutil.rmtree(td)
        else:
            o, e, rc = run(cmd); L = lines(o)
            got = ("REJECT" if "REJECT" in L else "ACCEPT" if "ACCEPT" in L else first(o)) if d == "a" else first(o)
        ok = (got == exp and rc == exexit); fails += not ok
        rows.append((d, cid, got, rc, exp, exexit, "PASS" if ok else "FAIL"))
        cap.append("=== case %s\n--- cmd\n%s\n--- exit\n%d\n--- stdout\n%s\n--- stderr\n%s\n" % (cid, " ".join(cmd), rc, o, e))
    print("label=%s interp=%s judge=%s strx=%s" % (a.label, interp, judge, a.strx))
    print("%-3s|%-28s|%-45s|%-4s|%-45s|%-4s|%s" % ("def", "case", "actual(first line/bytes)", "rc", "expected", "erc", "result"))
    for r in rows: print("%-3s|%-28s|%-45s|%-4d|%-45s|%-4d|%s" % (r[0], r[1], r[2][:45], r[3], r[4][:45], r[5], r[6]))
    if a.rawdir:
        os.makedirs(a.rawdir, exist_ok=True)
        open(os.path.join(a.rawdir, a.label + ".capture.txt"), "w", encoding="latin-1").write("".join(cap))
    print("FAILURES=%d of %d" % (fails, len(rows))); sys.exit(1 if fails else 0)
main()
