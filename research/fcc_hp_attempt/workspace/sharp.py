"""Section 46: the local potential.  For a surface site g: tau(g) = o/2 - deg + 3, bl(g) = number of chord ends blocked by g
(pairs (nu, d) with g + d nu-exposed and g in S not nu-exposed), pi(g) = 3 tau(g) - (3/2) bl(g), Pi = sum of pi.
(I0_n):  3 H_n + (3/2) h_(n+1) <= (4n - 1) U* + Pi - 9 def1     (silhouette runs only; stronger than (I_n))
    python3 sharp.py"""
import sys
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, dot, sub
from chordM3 import data3
def potential(S):
    F = {nu: {h for h in S if all(add(h, r) not in S for r in RNU[nu])} for nu in NUS}
    tot = Fraction(0); by = {}
    for g in S:
        emp = [r for r in ROOTS if add(g, r) not in S]
        if not emp: continue
        ex = [nu for nu in NUS if g in F[nu]]
        o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
        bl = sum(1 for nu in NUS if g not in F[nu] for d in ROOTS if dot(d, nu) == 0 and add(g, d) in F[nu])
        pi = 3 * (Fraction(o, 2) - len(emp) + 3) - Fraction(3 * bl, 2); tot += pi
        if pi != 0: by[(len(emp), len(ex), pi)] = by.get((len(emp), len(ex), pi), 0) + 1
    return tot, by
def i0(S):
    c, oo, ob, bb = data3(S); U = c['U']; d1 = c['surface'] - c['nu1']; Pi, by = potential(S)
    top = max(oo) + 2; out = []
    for n in range(3, top + 1):
        Hn = sum(1 for L in oo if L <= n); h1 = sum(1 for L in oo if L == n + 1)
        out.append(((4 * n - 1) * U + Pi - 9 * d1 - 3 * Hn - Fraction(3 * h1, 2), n))
    return min(out), Pi, by, c, d1
if __name__ == '__main__':
    from islands import island
    bodies = [(f"O_{r}", octa(r)) for r in (5, 7)] + [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}),
              ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))), ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))),
              ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)}),
              ("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 5 at (1,1)", octa(9) | island(9, 5, True, (1, 1))),
              ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
              ("tetrahedron 6", tetra(6)), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0)))]
    for name, S in bodies:
        (v, n), Pi, by, c, d1 = i0(S)
        print(f"{name}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; least slack of (I0_n) = {float(v):.1f} at n = {n}; sites with pi != 0 by (deg, e, pi): { {k: v for k, v in sorted(by.items())} }", flush=True)
