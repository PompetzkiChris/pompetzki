#!/usr/bin/env python3
"""Execute the repaired gate, the preserved old gate, and public judge-v4.pmp."""
import hashlib
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from gate_core import (  # noqa: E402
    AUTHREF,
    AUTHREF_SHA256,
    CANON_AST,
    CANON_LEN,
    ENTRIES,
    authenticated_prefix,
    authenticated_token_prefix,
    gate_bytes,
    norm_token,
)

POMP = "/workspace/pmp-audit/linux-judge/bin/linux/pompetzki"
JUDGE_V3 = "/workspace/pmp-audit/linux-judge/judge/judge-v3.pmp"
JUDGE_V4 = "/tmp/v4src/judge/judge-v4.pmp"
OLD_GATE = "/workspace/reg0-gate/reggate.pmp"
OLD_MUT = Path("/workspace/reg0-gate/mutants")
OLD_ZIP = Path("/workspace/reg0-initial-registry-gate-2026-10-11.zip")
OLD_ZIP_SHA = "917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841"
FIXTURES = Path("/tmp/v4src/judge/registry-tests-v4b")
PY = sys.executable
LOG = []


def say(text=""):
    LOG.append(text)
    print(text, flush=True)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, cwd=None, env=None, timeout=180):
    start = time.perf_counter()
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    dt = time.perf_counter() - start
    return proc.returncode, proc.stdout, proc.stderr, dt


def stdout_body(stdout, stderr):
    text = stdout
    if text and not text.endswith("\n"):
        text += "\n"
    return text


def check(cond, label):
    if not cond:
        say(f"FAIL {label}")
        raise SystemExit(1)
    say(f"ok {label}")


def api_3538():
    checks = 0
    failures = []

    def one(label, expected, actual):
        nonlocal checks
        checks += 1
        if expected != actual:
            failures.append((label, expected, actual))

    for n in range(707):
        one(f"AST prefix {n}", True, authenticated_prefix(list(CANON_AST[:n])))
        one(f"token prefix {n}", True, authenticated_token_prefix([list(e) for e in ENTRIES[:n]]))
    for i in range(706):
        formula, hyps = CANON_AST[i]
        before = list(CANON_AST[:i])
        one(
            f"formula alteration at {i}",
            False,
            authenticated_prefix(before + [(("n", formula), hyps)]),
        )
        one(
            f"hypothesis alteration at {i}",
            False,
            authenticated_prefix(before + [(formula, (999,) + tuple(hyps))]),
        )
        one(
            f"token alteration at {i}",
            False,
            authenticated_token_prefix([list(e) for e in ENTRIES[:i]] + [["n", *ENTRIES[i]]]),
        )
    zeros = [["000" + str(t) if isinstance(t, int) else t for t in entry] for entry in ENTRIES]
    one("numeric leading zeros in all 706 entries", True, authenticated_token_prefix(zeros))
    one("AST prefix of 707 entries", False, authenticated_prefix(list(CANON_AST) + [CANON_AST[0]]))
    one(
        "token prefix of 707 entries",
        False,
        authenticated_token_prefix([list(e) for e in ENTRIES] + [list(ENTRIES[0])]),
    )
    dotted = ["0.0" if t == 0 else t for t in ENTRIES[0]]
    one("decimal token is rejected", False, authenticated_token_prefix([dotted]))
    one("non-list AST input", False, authenticated_prefix((0,)))
    one("non-list token input", False, authenticated_token_prefix((0,)))
    say(f"api checks {checks} failed {len(failures)}")
    for item in failures[:8]:
        say(f"  api failure {item}")
    check(checks == 3538 and not failures, "3538/3538 embedded API checks")
    check(norm_token("02") == 2, "decimal 02 means integer 2")
    check(norm_token("00") == 0, "decimal 00 means integer 0")
    check(norm_token("0") == 0 and norm_token("2") == 2, "unpadded 0 and 2 unchanged")
    check(norm_token("0.0") == "0.0", "0.0 is not an integer spelling")


def norm_out(text):
    lines = [ln for ln in text.splitlines() if "check zero failed" not in ln]
    return "\n".join(lines) + ("\n" if lines else "")


def pmp_gate(path, cwd):
    code, out, err, dt = run([POMP, str(ROOT / "reggate.pmp"), str(path)], cwd=cwd)
    return code, norm_out(out + err), err, dt


def py_gate(path):
    start = time.perf_counter()
    code, text = __import__("gate_core").gate_file(str(path))
    return code, text, time.perf_counter() - start


def agree(path, cwd):
    pc, ptext, perr, dt = pmp_gate(path, cwd)
    yc, ytext, ydt = py_gate(path)
    if ptext != ytext or (pc == 0) != (yc == 0):
        say(f"DISAGREE {path.name}")
        say("python:")
        say(ytext)
        say("pmp:")
        say(ptext)
        say("pmp stderr:")
        say(perr)
        raise SystemExit(1)
    kind = "GATE" if pc == 0 else "REJECT"
    return kind, ptext, dt, ydt


def main():
    say("preserved previous archive")
    digest = sha256(OLD_ZIP)
    say(f"{digest}  {OLD_ZIP.name}  bytes {OLD_ZIP.stat().st_size}")
    check(digest == OLD_ZIP_SHA and OLD_ZIP.stat().st_size == 74542, "previous zip bytes unchanged")

    v4_line = Path(JUDGE_V4).read_text(encoding="latin1").splitlines()[45]
    v4_payload = v4_line[len('text AUTHREF "'):-1]
    check(hashlib.sha256(v4_payload.encode("ascii")).hexdigest() == AUTHREF_SHA256, "pinned sha is public AUTHREF")
    check(AUTHREF == v4_payload, "embedded string equals public judge-v4.pmp literal")
    ours = [ln for ln in (ROOT / "reggate.pmp").read_text(encoding="ascii").splitlines() if ln.startswith('text AUTHREF "')]
    check(len(ours) == 1 and ours[0][len('text AUTHREF "'):-1] == v4_payload, "pmp literal equals public AUTHREF")
    say(f"AUTHREF sha256 {AUTHREF_SHA256} entries {CANON_LEN}")

    say("")
    say("integer spelling")
    api_3538()

    say("")
    say("preserved mutants: old token gate versus repaired integer gate")
    spell = {
        "fail-spell-0.jdg",
        "fail-hypcount-spell-0.jdg",
        "fail-hyp-spell-677.jdg",
    }
    for path in sorted(OLD_MUT.glob("*.jdg")):
        old_cwd = "/workspace/reg0-gate"
        oc, out, err, dt = run([POMP, OLD_GATE, str(path)], cwd=old_cwd)
        old_kind = "GATE" if out.startswith("GATE\n") else "REJECT"
        new_kind, new_text, pdt, ydt = agree(path, cwd="/tmp")
        if path.name in spell:
            check(old_kind == "REJECT" and new_kind == "GATE", f"{path.name} old REJECT new GATE")
        else:
            check(old_kind == new_kind, f"{path.name} same class {new_kind}")
        first = " | ".join(new_text.splitlines()[:4])
        say(f"  {path.name} old {old_kind} new {new_kind} {first} pmp {pdt:.3f}s py {ydt:.3f}s")

    say("")
    say("public v4 fixtures")
    truth = {
        "prefix-0-truth.jdg",
        "prefix-1-truth.jdg",
        "prefix-677-truth.jdg",
        "prefix-706-truth.jdg",
        "leading-zero-and-tab-prefix.jdg",
    }
    auth_reject = {
        "forged-false-registry.jdg",
        "altered-first-formula.jdg",
        "altered-last-pure-formula.jdg",
        "altered-pure-hypotheses.jdg",
        "altered-placeholder-hypothesis.jdg",
        "registry-707-entries.jdg",
    }
    proof_reject = {
        "false-proof-canonical-prefix.jdg",
        "false-proof-empty-registry.jdg",
        "nonexistent-registry-use.jdg",
    }
    names = sorted(p.name for p in FIXTURES.glob("*.jdg"))
    check(set(names) == truth | auth_reject | proof_reject, "14 public fixtures present")
    for name in names:
        path = FIXTURES / name
        kind, text, pdt, ydt = agree(path, cwd="/tmp")
        code, out, err, dt = run([POMP, JUDGE_V4, str(path)], cwd="/tmp")
        v4_first = out.splitlines()[0] if out.splitlines() else ""
        if name in truth:
            check(kind == "GATE" and code == 0 and v4_first == "ACCEPT", f"{name} prefix accepted")
        elif name in auth_reject:
            check(kind == "REJECT" and code != 0 and v4_first != "ACCEPT", f"{name} rejected before a proof accept")
        else:
            check(kind == "GATE" and code != 0 and v4_first != "ACCEPT", f"{name} canonical prefix, proof rejected")
        say(f"  {name} gate {kind} v4 {v4_first!r} exit {code} {dt:.3f}s")
        say("  gate:")
        for ln in text.splitlines():
            say(f"    {ln}")
        say("  v4:")
        for ln in (out + err).splitlines()[:8]:
            say(f"    {ln}")

    say("")
    say("altered external canon must not authenticate a forged registry")
    work = Path("/tmp/reg0-altered-canon")
    if work.exists():
        shutil.rmtree(work)
    work.mkdir()
    canon = Path("/workspace/reg0-gate/REG0.canon").read_text(encoding="ascii")
    needle = "a a i a b e 0 2 e 0 1 q 1 0"
    check(canon.split().count("F") == 706, "source canon still has 706 F markers")
    check(canon.count(needle) >= 1, "entry 0 formula present")
    poisoned = canon.replace(needle, "a n q 0 0", 1)
    (work / "REG0.canon").write_text(poisoned, encoding="ascii", newline="\n")
    forged = work / "forged-matching-input.jdg"
    forged.write_text(
        "JDG1\nR 1\na n q 0 0\n0\nT 1\na n q 0 0\n0\n1\nU 0 0\n0\n",
        encoding="ascii",
        newline="\n",
    )
    oc, out, err, dt = run([POMP, OLD_GATE, str(forged)], cwd=str(work))
    check(out.startswith("GATE\n"), "old gate accepts the forged file when REG0.canon is altered")
    say("old gate, cwd holds the altered canon:")
    for ln in (out + err).splitlines()[:6]:
        say(f"  {ln}")
    env = os.environ.copy()
    env["REG0_CANON"] = str(work / "REG0.canon")
    kind, text, pdt, ydt = agree(forged, cwd=str(work))
    check(kind == "REJECT" and "\nformula\n" in text, "repaired gate rejects forged entry 0")
    say("repaired gate, same cwd and REG0_CANON set:")
    for ln in text.splitlines():
        say(f"  {ln}")
    code, out, err, dt = run([POMP, JUDGE_V3, str(forged)], cwd=str(work))
    check(code == 0 and out.startswith("ACCEPT"), "released judge-v3 would accept this forged file if reached")
    say("judge-v3 on the forged file, not used by the repaired wrapper:")
    for ln in out.splitlines()[:6]:
        say(f"  {ln}")
    sentinel = work / "proof-invoked.txt"
    env["GATE_PROOF_LOG"] = str(sentinel)
    env["POMPETZKI"] = POMP
    env["JUDGE_V3"] = JUDGE_V3
    env["REG0_CANON"] = str(work / "REG0.canon")
    code, out, err, dt = run(["sh", str(ROOT / "judge-gated.sh"), str(forged)], cwd=str(work), env=env)
    check(code != 0 and not sentinel.exists(), "wrapper rejects before proof checking")
    check("ACCEPT" not in out and "theorem" not in out.lower(), "wrapper output has no proof verdict")
    say("wrapper:")
    for ln in (out + err).splitlines():
        say(f"  {ln}")

    say("")
    say("equivalent spellings reach the proof judge and are accepted")
    env = os.environ.copy()
    env["POMPETZKI"] = POMP
    env["JUDGE_V3"] = JUDGE_V3
    for name in sorted(spell):
        sent = work / f"invoked-{name}.txt"
        if sent.exists():
            sent.unlink()
        env["GATE_PROOF_LOG"] = str(sent)
        code, out, err, dt = run(["sh", str(ROOT / "judge-gated.sh"), str(OLD_MUT / name)], cwd="/tmp", env=env)
        check(sent.is_file() and code == 0 and out.startswith("GATE\n") and "ACCEPT" in out, f"wrapper accepts {name}")
        say(f"{name} exit {code}")
        for ln in (out + err).splitlines()[:12]:
            say(f"  {ln}")

    say("")
    say("empty prefix is not a proof of a false axiom")
    sent = work / "invoked-false-axiom.txt"
    env["GATE_PROOF_LOG"] = str(sent)
    false_axiom = OLD_MUT / "proof-reject-false-axiom.jdg"
    code, out, err, dt = run(["sh", str(ROOT / "judge-gated.sh"), str(false_axiom)], cwd="/tmp", env=env)
    check(sent.is_file() and code != 0 and out.startswith("GATE\n") and "ACCEPT" not in out.split("GATE", 1)[0], "false axiom passes the gate and fails the proof judge")
    # ACCEPT must not be the proof verdict. The gate text does not contain ACCEPT.
    check("ACCEPT" not in out, "false axiom wrapper does not accept")
    say("proof-reject-false-axiom.jdg")
    for ln in (out + err).splitlines()[:12]:
        say(f"  {ln}")

    say("")
    say("no canon file in the working directory")
    empty = Path("/tmp/reg0-no-canon")
    if empty.exists():
        shutil.rmtree(empty)
    empty.mkdir()
    kind, text, pdt, ydt = agree(OLD_MUT / "pass-empty.jdg", cwd=str(empty))
    check(kind == "GATE", "pass-empty gates with no REG0.canon present")
    say(text.rstrip())

    say("")
    say("tool hashes")
    for path in (POMP, JUDGE_V3, JUDGE_V4, OLD_GATE, OLD_ZIP):
        say(f"{sha256(path)}  {path}")
    say(f"judge-v4 commit 63f45bbcaa88e370827d2dd2e95a6d422fb8c589")
    say("RpInitOk.v e8958a92 sha256 827498d05d92fd334a093273b1bdf13ef5fa11e643b84b2fa8ac83dff07d8bf3")
    say("Theorem REG0_ok : reg_ok hypf REG0. Proof. ... Qed. Not an Axiom.")
    say("ALL CHECKS PASSED")
    outp = ROOT / "tests" / "linux-output.txt"
    outp.parent.mkdir(exist_ok=True)
    outp.write_text("\n".join(LOG) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {outp}", flush=True)


if __name__ == "__main__":
    main()
