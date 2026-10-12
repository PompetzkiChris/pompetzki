"""Independent exact linear-algebra oracle: int and fractions.Fraction only.
No floats, no tolerances; every zero test is an exact comparison with 0."""
from fractions import Fraction as F
from itertools import permutations

def M(rows): return [[F(x) for x in r] for r in rows]
def shape(A, cols=None):
    return (len(A), len(A[0]) if A else (cols or 0))
def zeros(m, n): return [[F(0)] * n for _ in range(m)]
def ident(n): return [[F(int(i == j)) for j in range(n)] for i in range(n)]
def transpose(A, n):  # n = column count (needed when A has 0 rows)
    return [[A[i][j] for i in range(len(A))] for j in range(n)]
def matmul(A, B, n, p):
    """A is m x n, B is n x p."""
    return [[sum((A[i][k] * B[k][j] for k in range(n)), F(0)) for j in range(p)] for i in range(len(A))]
def matvec(A, x): return [sum((a * b for a, b in zip(r, x)), F(0)) for r in A]

def rref(A, n):
    R = [r[:] for r in A]; m = len(R); piv = []; row = 0
    for c in range(n):
        p = next((i for i in range(row, m) if R[i][c] != 0), None)
        if p is None: continue
        R[row], R[p] = R[p], R[row]
        pv = R[row][c]; R[row] = [x / pv for x in R[row]]
        for i in range(m):
            if i != row and R[i][c] != 0:
                f = R[i][c]; R[i] = [a - f * b for a, b in zip(R[i], R[row])]
        piv.append(c); row += 1
        if row == m: break
    return R, piv

def rank(A, n): return len(rref(A, n)[1])

def kernel(A, n):
    R, piv = rref(A, n); basis = []
    for f in (c for c in range(n) if c not in piv):
        v = [F(0)] * n; v[f] = F(1)
        for i, pc in enumerate(piv): v[pc] = -R[i][f]
        basis.append(v)
    return basis

def image(A, n):
    _, piv = rref(A, n)
    return [[A[i][c] for i in range(len(A))] for c in piv]

def solve(A, b, n):
    """Returns ('ok', particular, homogeneous basis) or ('inconsistent', y)."""
    m = len(A)
    aug = [A[i] + [b[i]] + [F(int(i == j)) for j in range(m)] for i in range(m)]
    R, piv = rref(aug, n + 1 + m)
    for i in range(m):
        if all(R[i][j] == 0 for j in range(n)) and R[i][n] != 0:
            return ('inconsistent', R[i][n + 1:])
    x = [F(0)] * n
    for i, pc in enumerate(piv):
        if pc < n: x[pc] = R[i][n]
    return ('ok', x, kernel(A, n))

def det_gauss(A):
    n = len(A); R = [r[:] for r in A]; d = F(1)
    for c in range(n):
        p = next((i for i in range(c, n) if R[i][c] != 0), None)
        if p is None: return F(0)
        if p != c: R[c], R[p] = R[p], R[c]; d = -d
        d *= R[c][c]
        for i in range(c + 1, n):
            f = R[i][c] / R[c][c]
            R[i] = [a - f * b for a, b in zip(R[i], R[c])]
    return d

def det_bareiss(A):
    """Fraction-free Bareiss on the integer matrix obtained by clearing denominators."""
    n = len(A)
    if n == 0: return F(1)
    from math import lcm
    L = 1
    for r in A:
        for x in r: L = lcm(L, x.denominator)
    R = [[int(x * L) for x in r] for r in A]; sign = 1; prev = 1
    for k in range(n - 1):
        if R[k][k] == 0:
            p = next((i for i in range(k + 1, n) if R[i][k] != 0), None)
            if p is None: return F(0)
            R[k], R[p] = R[p], R[k]; sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = R[i][j] * R[k][k] - R[i][k] * R[k][j]
                assert num % prev == 0
                R[i][j] = num // prev
        prev = R[k][k]
    return F(sign * R[n - 1][n - 1], L ** n)

def det_perm(A):
    n = len(A); total = F(0)
    for p in permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])
        t = F(1)
        for i in range(n): t *= A[i][p[i]]
        total += -t if inv % 2 else t
    return total

def inverse(A):
    n = len(A)
    R, piv = rref([A[i] + ident(n)[i] for i in range(n)], 2 * n)
    if piv[:n] != list(range(n)) or len(piv) < n: return None
    return [r[n:] for r in R]

def is_rref(R, piv, n):
    lead = []
    for r in R:
        nz = [j for j in range(n) if r[j] != 0]
        lead.append(nz[0] if nz else None)
    k = len(piv)
    if any(l is None for l in lead[:k]) or any(l is not None for l in lead[k:]): return False
    if lead[:k] != piv or piv != sorted(piv): return False
    for i, c in enumerate(piv):
        if R[i][c] != 1 or any(R[t][c] != 0 for t in range(len(R)) if t != i): return False
    return True

def fs(x): return str(x)  # Fraction prints as a or a/b
def fparse(s): return F(s.strip())
