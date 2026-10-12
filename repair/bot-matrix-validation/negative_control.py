"""Checks that the comparison predicates used in test_engine.py / test_pomp.py reject wrong answers."""
from oracle import *
A = M([[1, 2, 3], [2, 4, 6]]); n = 3
good = kernel(A, n); bad = [good[0], [F(1), F(0), F(0)]]
assert all(all(v == 0 for v in matvec(A, k)) for k in good) and rank(good, n) == 2
assert not all(all(v == 0 for v in matvec(A, k)) for k in bad)
dup = [good[0], [2 * v for v in good[0]]]; assert rank(dup, n) == 1   # dependent basis rejected
assert det_gauss(M([[1, 2], [3, 4]])) != F(-2) + F(1, 10**40)        # exact, no tolerance
x = solve(A, [F(1), F(2)], n)[1]; assert matvec(A, x) == [1, 2]; assert matvec(A, [F(0)] * 3) != [1, 2]
img = image(A, n); assert rank(transpose(A, n) + [[F(1), F(0)]], 2) > rank(A, n)  # vector outside col space detected
print("negative controls passed")
