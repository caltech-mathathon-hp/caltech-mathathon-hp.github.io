"""Section 46: the runs-only form.  With Pi the sum of the local potential (sharp.py) and D_n the sum of (n + 1/2 - |C|)+ over
the silhouette runs,   M0_n = (2n^2 - 3n) U* + n Pi - 9n def1 - 3 D_n,   and   M'_n = M0_n + 3 sum_OB min(|C| - 1/4, n/2) + 3n H2.
For each body: the n >= 3 with M0_n < 0.     python3 m0.py island r k a b | islands r | unions a b | near r | bridge r | named"""
import sys
from fractions import Fraction
from gmin import *
from chordM3 import data3, M1
from sharp import potential
H = Fraction(1, 2)
def m0(S, check=True):
    c, oo, ob, bb = data3(S); U = c['U']; d1 = c['surface'] - c['nu1']; Pi, by = potential(S)
    top = max(oo) + 3; out = {}
    for n in range(3, top + 1):
        out[n] = (2 * n * n - 3 * n) * U + n * Pi - 9 * n * d1 - 3 * sum(n + H - L for L in oo if L <= n)
    if check:
        from chords import chords
        nbb = sum(1 for x in chords(S) if x[4] == 0)
        for n in (3, min(7, top)):
            assert M1(c, oo, ob, n) == out[n] + 3 * sum(min(L - Fraction(1, 4), Fraction(n, 2)) for L in ob) + 3 * n * nbb
    return [n for n in out if out[n] < 0], c, Pi, d1
def scan(name, bodies):
    cnt = 0; hist = {}; w = None
    for tag, S in bodies:
        bad, c, Pi, d1 = m0(S, cnt % 40 == 0); cnt += 1; k = max(bad) if bad else 0; hist[k] = hist.get(k, 0) + 1
        if w is None or k > w[0]: w = (k, tag, c['U'], Pi)
    print(f"{name}: {cnt} bodies; largest n with M0_n < 0, by number of bodies: {dict(sorted(hist.items()))}; worst {w}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    if mode == 'island':
        r, k, a, b = map(int, sys.argv[2:6]); O = octa(r); I = island(r, k, True, (a, b)); assert supported(O, I)
        bad, c, Pi, d1 = m0(O | I); print(f"O_{r} with island k = {k} at {(a, b)}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; M0_n < 0 for n in {bad}", flush=True)
    if mode == 'islands':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen())
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'bridge':
        r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A
        def gen():
            for x in range(0, 2 * r + 5):
                for y in range(0, x + 1):
                    for z in range(0, y + 1):
                        if (x + y + z) % 2: continue
                        B = octa(r, (x, y, z))
                        if A & B or coatA & B: continue
                        coatB = {add(h, s) for h in B for s in ROOTS} - B
                        for g in coatA & coatB: yield ((x, y, z), g), A | B | {g}
        scan(f"two O_{r} joined by one site", gen())
    if mode == 'named':
        named = [("pair", {(0, 0, 0), (1, 1, 0)}), ("single", {(0, 0, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        for nm, S in named:
            bad, c, Pi, d1 = m0(S); print(f"   {nm}: U* = {c['U']}, Pi = {Pi}, def1 = {d1}; M0_n < 0 for n in {bad}")
