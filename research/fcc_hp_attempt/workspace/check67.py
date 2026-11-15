"""Section 46: checks of Lemma 66 and of the two forms of the increment (Proposition 67) on bodies.
    E = H - H2 - Pi/3;   M'_n = (2n^2 - 3n) U + n Pi - 9n def1 - 3 D_n + 3 sum_OB min(|C| - 1/4, n/2) + 3n H2;
    M'_(n+1) - M'_n = (4n - 1) U - 3p + (3/4)(N(n/2 + 1) + N((n + 1)/2))
                    = (4n - 1) U + Pi - 9 def1 - 3 H_n - (3/2) h_(n+1) + (3/2) #{OB: |C| > (n+1)/2} + (3/4) #{OB: |C| = (n+1)/2} + 3 H2
    python3 check67.py"""
from fractions import Fraction
from gmin import *
from chords import chords
from chordM3 import M1
from sharp import potential
from islands import island
Q = Fraction(1, 4)
bodies = [("O_6", octa(6)), ("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
          ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("O_9 with island 4 at (1,1)", octa(9) | island(9, 4, True, (1, 1))), ("tetrahedron 6", tetra(6)),
          ("rod of 10", {(i, -i, 0) for i in range(10)}), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("O_9 with a cavity O_3", octa(9) - octa(3)), ("single site", {(0, 0, 0)})]
for name, S in bodies:
    c = cost(S); ch = chords(S); oo = sorted(x[3] for x in ch if x[4] == 2); ob = sorted(x[3] for x in ch if x[4] == 1); bbn = sum(1 for x in ch if x[4] == 0)
    U = c['U']; d = c['boundary']; E = d - 3 * c['surface']; d1 = c['surface'] - c['nu1']; p = d - 3 * c['nu1']; Pi, by = potential(S)
    assert 3 * E == 3 * len(oo) - 3 * bbn - Pi                                     # Lemma 66 (a)
    ends = [Fraction(L, 2) for L in oo] * 2 + [Fraction(L) for L in ob]; N = lambda x: sum(1 for l in ends if l >= x)
    for n in range(1, max(oo + ob + [3]) + 4):
        Dn = sum(n + 2 * Q - L for L in oo if L <= n)
        assert M1(c, oo, ob, n) == (2 * n * n - 3 * n) * U + n * Pi - 9 * n * d1 - 3 * Dn + 3 * sum(min(L - Q, Fraction(n, 2)) for L in ob) + 3 * n * bbn
        inc = M1(c, oo, ob, n + 1) - M1(c, oo, ob, n)
        assert inc == (4 * n - 1) * U - 3 * p + 3 * Q * (N(Fraction(n, 2) + 1) + N(Fraction(n + 1, 2)))
        Hn = sum(1 for L in oo if L <= n); h1 = sum(1 for L in oo if L == n + 1)
        assert inc == (4 * n - 1) * U + Pi - 9 * d1 - 3 * Hn - Fraction(3, 2) * h1 + Fraction(3, 2) * sum(1 for L in ob if 2 * L > n + 1) + 3 * Q * sum(1 for L in ob if 2 * L == n + 1) + 3 * bbn
    print(f"{name}: E = {E}, H = {len(oo)}, H1 = {len(ob)}, H2 = {bbn}, Pi = {Pi}, def1 = {d1}: Lemma 66 and both forms of the increment hold for n = 1..{max(oo + ob + [3]) + 3}", flush=True)
