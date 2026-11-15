"""Section 45: the algebra of Proposition 62 and of the two forms of M_n, checked on random integers and on bodies."""
import random
from fractions import Fraction
from gmin import *
from lin import lam
from chordM import data, M
rng = random.Random(1)
for _ in range(2000):
    n, d, n1, n2, a, b, r, m = (rng.randint(3, 60), rng.randint(1, 10**4), rng.randint(0, 500), rng.randint(0, 500), rng.randint(0, 900), rng.randint(0, 900), rng.randint(5, 60), rng.randint(1, 9))
    U = 2 * d - 6 * n1 - 9 * n2
    assert (4*n*n - 9*n + 3) * U + 18 * n1 - 9 * (n - 3) * n2 == 2 * (4*n*n - 9*n + 3) * d - 6 * n * ((2*n - 6) * (n1 + n2) + (2*n - 3) * (n1 + 2 * n2))      # (a)
    c = dict(boundary=d, nu1=a, nu2=b); p = d - 3 * a; q = d - 3 * b
    assert lam(c, n) == (2*n*n - 3*n) * (p + q) - 3 * n * p + 3 * d == (2*n*n - 6*n) * p + (2*n*n - 3*n) * q + 3 * d                                      # the forms of Lam_n
    assert 2 * lam(c, n) == 4 * (p + q) * n * n - 9 * 2 * (d - 2 * a - b) * n + 6 * d                                                                   # remark 2
    co = dict(boundary=12 * r * r, nu1=4 * r * r - 8 * r + 6, nu2=4 * r * r + 8 * r - 12); assert lam(co, n) == 36 * (n - r) ** 2                           # (b)
    assert 18 * (4*n*n - 9*n + 3) + 18 * (4*n*n - 24*n + 24) - 9 * (n - 3) * (16 * n - 18) == 0                                                        # (c)
    assert 4*n*n - 9*n + 3 >= Fraction(32, 10) * 9 * (n - 3)                                                                                           # remark 3
assert lam(dict(boundary=12, nu1=1, nu2=2), 7) == 30 * 49 - 72 * 7 + 36
print("Proposition 62: identities hold on 2000 random integer cases")
for name, S in (("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)})):
    c, oo = data(S); U = c['U']; p = c['boundary'] - 3 * c['nu1']; H = len(oo); delta = U + p - H
    assert 2 * delta == 3 * (c['n2'] + U) - 2 * H
    Hj = lambda j: sum(1 for L in oo if L <= j); kap = lambda j: Fraction(4 * U * j, 3) - Hj(j)
    for n in range(1, 14):
        assert M(c, oo, n) == 3 * (sum(kap(j) for j in range(1, n)) + kap(n) / 2) - 3 * n * delta
        assert M(c, oo, n) >= 0 or n * p > (Fraction(2 * n * n, 3) - n) * U + sum(min(L - Fraction(1, 2), n) for L in oo)
        assert M(c, oo, n) < 0 or n * p <= (Fraction(2 * n * n, 3) - n) * U + sum(min(L - Fraction(1, 2), n) for L in oo)
    print(f"{name}: the two other forms of M_n agree for n = 1..13; delta = {delta}, kappa_j for j = 1..7: {[str(kap(j)) for j in range(1, 8)]}")
