"""Unchanged upstream API test function, bound to the corrected local module."""
from gate_core import AUTHREF, AUTHREF_SHA256, CANON_AST, CANON_LEN, ENTRIES, authenticated_prefix, authenticated_token_prefix, gate_bytes, norm_token
LOG = []
def say(text=""):
    LOG.append(text)
    print(text, flush=True)

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

if __name__ == "__main__":
    api_3538()
