"""Section 47: the nearest-root charge of Lemma 71, site by site.  Each active run of length L is charged 1 in total:
1 to its nearest root if the nearest roots on its two lines are at different levels, 1/2 to each if they are at the
same level (twice 1/2 to the tip if both are the tip).  Prints, for a body, the charge of every shape-irregular site
that is charged, for each L, and the largest charge of a site over all L.      python3 charges.py"""
from fractions import Fraction
from gmin import *
from fans import REG, FANS, analyse, mul, APEX
from islands import island
def charges(S):
    S2, em, irr, fans, other_oo, ob = analyse(S); ch = {}
    for (nu, k, X), lev in fans.items():
        d = [dd for dd in FANS if dd[0] == nu and FANS[dd][0] == k][0]; _, a, b, Ma, Mb = FANS[d]
        for t, (e1, e2) in lev.items():
            ts = []
            for step, M in ((a, Ma), (b, Mb)):
                s = t - 1
                while em(add(X, mul(s, step))) == M: s -= 1
                ts.append(s)
            tau = max(ts); who = [add(X, mul(s, step)) for step, s in zip((a, b), ts) if s == tau]
            for z in who: ch[(t + 1, z)] = ch.get((t + 1, z), 0) + Fraction(1, len(who))
    return ch, em
def show(name, S):
    c = cost(S); ch, em = charges(S); sites = sorted({z for L, z in ch})
    print(f"{name}: U* = {c['U']}")
    for z in sites:
        row = {L: v for (L, zz), v in sorted(ch.items()) if zz == z}
        kind = 'vertex of an octahedron' if em(z) in APEX else f"{len(em(z))} empty neighbours"
        print(f"   {z} ({kind}): largest charge {max(row.values())}; by L: " + ", ".join(f"{L}: {v}" for L, v in row.items()))
if __name__ == '__main__':
    show("O_6", octa(6))
    show("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2)))
    show("O_9 with island 3 at (0,0)", octa(9) | island(9, 3, True, (0, 0)))
    show("O_6 without a vertex", octa(6) - {(5, 0, 0)})
