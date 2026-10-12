"""Embedded canonical-registry gate.

The reference string is judge-v4.pmp's AUTHREF literal at commit
63f45bbcaa88e370827d2dd2e95a6d422fb8c589, stored in embed_data.py.
Decimal digit strings of 1..12 digits mean their integer value, so 02 is 2
and 00 is 0. Space, tab, CR and LF are delimiters. This module does not
open a reference file and does not read REG0_CANON.

Parsing and this comparison are not a proof that any executable computes
Gallina check_thm or check_batch. That correspondence stays open.
Theorem REG0_ok in Cohen.RpInitOk is an established Proof/Qed, not an
axiom supplied by this gate.
"""

from embed_data import AUTHREF, AUTHREF_SHA256, ENTRIES

MAX_DIGITS = 12
MAX_ARITY = 1000000
MAX_HYPS = 100000
CANON_LEN = 706
WS = {32, 9, 10, 13}
UNARY = {"n", "a", "x"}
BINARY = {"i", "k", "d", "b"}
ATOM2 = {"e", "q"}


class GateFail(Exception):
    def __init__(self, text):
        super().__init__(text)
        self.text = text


def _formula(tokens, i):
    if i >= len(tokens) or not isinstance(tokens[i], str):
        raise ValueError("tag")
    tag = tokens[i]
    i += 1
    if tag in ATOM2:
        x, y = tokens[i], tokens[i + 1]
        if not isinstance(x, int) or not isinstance(y, int):
            raise ValueError("num")
        return (tag, x, y), i + 2
    if tag == "p":
        pred, arity = tokens[i], tokens[i + 1]
        if not isinstance(pred, int) or not isinstance(arity, int):
            raise ValueError("num")
        i += 2
        args = tuple(tokens[i:i + arity])
        if len(args) != arity or any(not isinstance(a, int) for a in args):
            raise ValueError("args")
        return (tag, pred, args), i + arity
    if tag in UNARY:
        sub, i = _formula(tokens, i)
        return (tag, sub), i
    if tag in BINARY:
        a, i = _formula(tokens, i)
        b, i = _formula(tokens, i)
        return (tag, a, b), i
    raise ValueError("tag")


def ast_of(tokens):
    formula, i = _formula(list(tokens), 0)
    if i >= len(tokens) or not isinstance(tokens[i], int):
        raise ValueError("hyp")
    count = tokens[i]
    i += 1
    hyps = tuple(tokens[i:i + count])
    i += count
    if i != len(tokens) or len(hyps) != count or any(not isinstance(h, int) for h in hyps):
        raise ValueError("hyp")
    return (formula, hyps)


CANON_AST = tuple(ast_of(e) for e in ENTRIES)
if len(CANON_AST) != CANON_LEN or AUTHREF.count("!") != CANON_LEN:
    raise SystemExit("embed shape")
if __import__("hashlib").sha256(AUTHREF.encode("ascii")).hexdigest() != AUTHREF_SHA256:
    raise SystemExit("embed hash")


def norm_token(tok):
    if isinstance(tok, bool):
        return tok
    if isinstance(tok, int):
        if tok < 0 or len(str(tok)) > MAX_DIGITS:
            return ("reject", tok)
        return tok
    if isinstance(tok, str) and tok.isascii() and tok.isdigit() and 1 <= len(tok) <= MAX_DIGITS:
        return int(tok)
    return tok


def authenticated_prefix(entries):
    if not isinstance(entries, list) or len(entries) > CANON_LEN:
        return False
    for i, ent in enumerate(entries):
        if ent != CANON_AST[i]:
            return False
    return True


def authenticated_token_prefix(entries):
    if not isinstance(entries, list) or len(entries) > CANON_LEN:
        return False
    for i, ent in enumerate(entries):
        if not isinstance(ent, list):
            return False
        if [norm_token(t) for t in ent] != list(ENTRIES[i]):
            return False
    return True


class Scan:
    def __init__(self, data):
        self.b = data
        self.pos = 0
        self.lim = len(data)

    def skip(self):
        b = self.b
        while self.pos < self.lim and b[self.pos] in WS:
            self.pos += 1

    def endtok(self):
        if self.pos < self.lim and self.b[self.pos] not in WS:
            raise GateFail("REJECT registry\nparse\n")

    def tag(self):
        self.skip()
        if self.pos >= self.lim:
            raise GateFail("REJECT registry\nparse\n")
        c = self.b[self.pos]
        self.pos += 1
        self.endtok()
        return chr(c)

    def num(self):
        self.skip()
        if self.pos >= self.lim:
            raise GateFail("REJECT registry\nparse\n")
        v = 0
        nd = 0
        b = self.b
        while self.pos < self.lim and b[self.pos] not in WS:
            d = b[self.pos] - 48
            if d < 0 or d > 9 or nd >= MAX_DIGITS:
                raise GateFail("REJECT registry\nparse\n")
            v = v * 10 + d
            nd += 1
            self.pos += 1
        if nd == 0:
            raise GateFail("REJECT registry\nparse\n")
        self.endtok()
        return v

    def literal(self, text):
        self.skip()
        raw = text.encode("ascii")
        if self.b[self.pos:self.pos + len(raw)] != raw:
            raise GateFail("REJECT registry\nparse\n")
        self.pos += len(raw)
        self.endtok()


def _cmp_entry(scan, tokens, index):
    i = 0
    n = len(tokens)

    def exp_tag():
        nonlocal i
        if i >= n or not isinstance(tokens[i], str):
            raise GateFail("REJECT registry\nembed\n")
        t = tokens[i]
        i += 1
        return t

    def exp_num():
        nonlocal i
        if i >= n or not isinstance(tokens[i], int):
            raise GateFail("REJECT registry\nembed\n")
        t = tokens[i]
        i += 1
        return t

    need = 1
    while need:
        want = exp_tag()
        got = scan.tag()
        if got != want:
            raise GateFail(f"REJECT registry\n{index}\nformula\n")
        if want in ATOM2:
            for _ in range(2):
                if scan.num() != exp_num():
                    raise GateFail(f"REJECT registry\n{index}\nformula\n")
            need -= 1
        elif want == "p":
            if scan.num() != exp_num():
                raise GateFail(f"REJECT registry\n{index}\nformula\n")
            arity = exp_num()
            if scan.num() != arity:
                raise GateFail(f"REJECT registry\n{index}\nformula\n")
            if arity > MAX_ARITY:
                raise GateFail("REJECT registry\nparse\n")
            for _ in range(arity):
                if scan.num() != exp_num():
                    raise GateFail(f"REJECT registry\n{index}\nformula\n")
            need -= 1
        elif want in UNARY:
            pass
        elif want in BINARY:
            need += 1
        else:
            raise GateFail(f"REJECT registry\n{index}\nformula\n")
    hc = exp_num()
    if scan.num() != hc:
        raise GateFail(f"REJECT registry\n{index}\nhypotheses\n")
    if hc > MAX_HYPS:
        raise GateFail("REJECT registry\nparse\n")
    for _ in range(hc):
        if scan.num() != exp_num():
            raise GateFail(f"REJECT registry\n{index}\nhypotheses\n")
    if i != n:
        raise GateFail("REJECT registry\nembed\n")


def gate_bytes(data):
    if not isinstance(data, (bytes, bytearray)):
        raise GateFail("REJECT registry\nparse\n")
    scan = Scan(bytes(data))
    try:
        scan.literal("JDG1")
        if scan.tag() != "R":
            raise GateFail("REJECT registry\nparse\n")
        n0 = scan.num()
        if n0 > CANON_LEN:
            raise GateFail(f"REJECT registry\ncount\n{n0}\n{CANON_LEN}\n")
        for i in range(n0):
            _cmp_entry(scan, ENTRIES[i], i)
        if scan.tag() != "T":
            raise GateFail("REJECT registry\nparse\n")
    except GateFail as exc:
        return 1, exc.text
    return 0, f"GATE\n{n0}\n{CANON_LEN}\n"


def gate_file(path):
    # Only this path is opened. REG0.canon and REG0_CANON are not consulted.
    with open(path, "rb") as handle:
        data = handle.read()
    return gate_bytes(data)
