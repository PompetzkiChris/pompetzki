"""Compute oracle answers for every case and verify identities exactly. Writes outputs/oracle.json."""
import json, sys
from oracle import *
D = json.load(open('inputs/cases.json'))
dec = lambda X: None if X is None else [[fparse(v) for v in r] for r in X]
enc = lambda X: None if X is None else [[fs(v) for v in r] for r in X]
out = []; checks = 0; fails = []
def chk(cid, name, cond):
    global checks
    checks += 1
    if not cond: fails.append((cid, name))
for c in D['cases']:
    m, n, p = c['m'], c['n'], c['p']; A = dec(c['A']); B = dec(c['B']); C = dec(c['C'])
    if m > 0 and n == 0: A = [[] for _ in range(m)]
    cid = c['id']; r = {}
    R, piv = rref(A, n); K = kernel(A, n); I = image(A, n); rk = len(piv)
    chk(cid, 'rank+nullity', rk + len(K) == n)
    for k in K: chk(cid, 'A k = 0', all(v == 0 for v in matvec(A, k)))
    chk(cid, 'kernel independent', rank(K, n) == len(K))
    chk(cid, 'rref canonical', is_rref(R, piv, n))
    chk(cid, 'rref same row space', rank(R, n) == rk and rank(A + R, n) == rk)
    chk(cid, 'image rank r', len(I) == rk and rank(I, m) == rk)
    chk(cid, 'image in col space', rank(transpose(A, n) + I, m) == rk)
    AT = transpose(A, n)
    chk(cid, 'transpose involution', transpose(AT, m) == A)
    AB = matmul(A, B, n, p)
    BT = transpose(B, p)
    chk(cid, '(AB)^T = B^T A^T', transpose(AB, p) == matmul(BT, AT, n, m))
    bc = [fparse(v) for v in c['b_consistent']]
    s = solve(A, bc, n)
    chk(cid, 'consistent solvable', s[0] == 'ok')
    if s[0] == 'ok':
        chk(cid, 'A x = b', matvec(A, s[1]) == bc)
    r['solve_consistent'] = dict(status=s[0], x=[fs(v) for v in s[1]], hom=enc(s[2])) if s[0] == 'ok' else dict(status=s[0])
    if c['b_inconsistent'] is not None:
        bi = [fparse(v) for v in c['b_inconsistent']]
        s2 = solve(A, bi, n)
        chk(cid, 'inconsistent detected', s2[0] == 'inconsistent')
        if s2[0] == 'inconsistent':
            y = s2[1]
            chk(cid, 'y^T A = 0', all(sum((y[i] * A[i][j] for i in range(m)), F(0)) == 0 for j in range(n)))
            chk(cid, 'y^T b != 0', sum((y[i] * bi[i] for i in range(m)), F(0)) != 0)
            r['solve_inconsistent'] = dict(status='inconsistent', certificate=[fs(v) for v in y])
    if m == n:
        dg = det_gauss(A) if n else F(1); db = det_bareiss(A)
        chk(cid, 'det gauss = bareiss', dg == db)
        if n <= 6: chk(cid, 'det gauss = permutation', dg == det_perm(A))
        Ai = inverse(A) if n else []
        chk(cid, 'det=0 iff singular', (dg == 0) == (Ai is None))
        chk(cid, 'det=0 iff rank<n', (dg == 0) == (rk < n))
        if Ai is not None:
            chk(cid, 'A Ainv = I', matmul(A, Ai, n, n) == ident(n))
            chk(cid, 'Ainv A = I', matmul(Ai, A, n, n) == ident(n))
        chk(cid, 'det(AC)=det(A)det(C)', det_bareiss(matmul(A, C, n, n)) == dg * det_bareiss(C))
        chk(cid, 'det(A^T)=det(A)', det_bareiss(AT) == dg)
        r.update(det=fs(dg), inverse=enc(Ai), AC=enc(matmul(A, C, n, n)))
    r.update(id=cid, rref=enc(R), pivots=piv, rank=rk, nullity=len(K), kernel=enc(K), image=enc(I),
             transpose=enc(AT), AB=enc(AB))
    out.append(r)
json.dump(dict(seed=D['seed'], identity_checks=checks, identity_failures=fails, results=out),
          open('outputs/oracle.json', 'w'), indent=1)
print(f"oracle: {len(out)} cases, {checks} identity checks, {len(fails)} failures")
for f in fails: print("FAIL", f)
sys.exit(1 if fails else 0)
