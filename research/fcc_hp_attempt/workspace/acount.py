"""Section 47: the count (A).  a_L(S) = number of silhouette runs of exactly L sites whose two end sites are shape-regular
(then they are regular ridge sites and the run is the level L - 1 segment of a fan, fans.py);  a_max = max over L.
(A):  3 a_L <= 4 U* - 1 for every L, for every finite connected set that is not a regular octahedron.
Theorem 69 (a):  with I the set of shape-irregular surface sites and def1 = s - nu1,
    M'_n >= LA_n := (2n^2 - 3n) U* - 3 sum_L a_L (n + 1/2 - L)+ - 9n def1 - 99 n |I|,
and if (A) holds for S then LA_n >= (n - 1)^2 / 2 - 9n def1 - 99 n |I|.
The script asserts LA_n <= M'_n (chordM3.M1) for several n, and the facts used in the proof on each body it sees:
every chord end is blocked by a regular trough site or a shape-irregular site; a regular trough site blocks at most 4 chords;
a shape-irregular site blocks at most 16 chords.  (The bound of 48 open ends at a site and the constant 99 are in `local`.)
    python3 acount.py named | special | unions a b | near r | near2 r | islands r | pits r | bridge r | roof N n | local"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
from fans import REG, empties, neg, FANS, analyse
def acount(S):
    """dict L -> a_L, set of shape-irregular surface sites, and checks of the facts about blockers"""
    S2, em, irr, fans, other_oo, ob = analyse(S)
    a = {}
    for lev in fans.values():
        for t in lev: a[t + 1] = a.get(t + 1, 0) + 1
    for L, e1irr, e2irr in other_oo: assert e1irr or e2irr            # a run that is not active has a shape-irregular end site
    nb = {}
    for nu in NUS:                                                    # who blocks
        F = {h for h in S2 if all(add(h, r) not in S2 for r in RNU[nu])}
        for d in DNU[nu]:
            for dd in (d, neg(d)):
                for h in F:
                    g = add(h, dd)
                    if g in S2 and g not in F: nb[g] = nb.get(g, 0) + 1
    for g, k in nb.items():
        kind = REG.get(em(g), ('irregular',))[0]
        assert kind in ('trough', 'irregular') and k <= (4 if kind == 'trough' else 16), (g, kind, k)
    return a, irr
def check(S, c, a, irr, ns=(3, 8, 38, 200)):
    from chordM3 import data3, M1
    cc, oo, ob, bb = data3(S, c); U = c['U']; d1 = c['surface'] - c['nu1']; out = []
    for n in ns:
        LA = (2 * n * n - 3 * n) * U - 3 * sum(v * max(Fraction(0), n + Fraction(1, 2) - L) for L, v in a.items()) - 9 * n * d1 - 99 * n * len(irr)
        M = M1(c, oo, ob, n); assert LA <= M, (n, LA, M); out.append((n, LA, M))
    return out
def line(name, S):
    c = cost(S); a, irr = acount(S); chk = check(S, c, a, irr); am = max(a.values(), default=0)
    print(f"{name}: U* = {c['U']}, |I| = {len(irr)}, def1 = {c['surface'] - c['nu1']}, a_max = {am}, 4U* - 3 a_max = {4 * c['U'] - 3 * am}; a_L: {dict(sorted(a.items()))}", flush=True)
def scan(name, bodies):
    cnt = 0; worst = None; hist = {}; eq = []; maxI = 0
    for tag, S in bodies:
        if len(S) < 2: continue
        c = cost(S); a, irr = acount(S); cnt += 1; am = max(a.values(), default=0)
        if cnt % 20 == 1: check(S, c, a, irr, ns=(4, 38))
        sl = 4 * c['U'] - 3 * am; hist[min(sl, 12)] = hist.get(min(sl, 12), 0) + 1; maxI = max(maxI, Fraction(len(irr), c['U']))
        if sl <= 0: eq.append((tag, c['U'], am))
        if worst is None or sl < worst[0]: worst = (sl, tag, c['U'], am)
    print(f"{name}: {cnt} bodies; least 4U* - 3 a_max = {worst[0]} ({worst[1]}, U* = {worst[2]}, a_max = {worst[3]}); bodies with 4U* - 3 a_max <= 0: {len(eq)} {eq[:6]}; "
          f"number of bodies by 4U* - 3 a_max (12 = 12 or more): {dict(sorted(hist.items()))}; largest |I| / U* = {float(maxI):.2f}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    if mode == 'named':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        named += [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
                  ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))), ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))),
                  ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))),
                  ("O_9 with island 3 at (0,0)", octa(9) | island(9, 3, True, (0, 0))), ("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 5 at (1,1)", octa(9) | island(9, 5, True, (1, 1))),
                  ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
                  ("O_5 u O_8+(3,1,1)", octa(5) | octa(8, (3, 1, 1))),
                  ("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4)))]
        for nm, S in named: line(nm, S)
    if mode == 'special':
        sp = [("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
              ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
              ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
              ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
              ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
              ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}),
              ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})]
        for nm, S in sp: line(nm, S)
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'near2':
        r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
        def gen():
            for h, g in itertools.combinations(mv, 2):
                T = toggle(toggle(S, h), g)
                if connected(T): yield (h, g), T
        scan(f"bodies at two sites from O_{r}", gen())
    if mode in ('islands', 'pits'):
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if mode == 'islands':
                                if supported(O, I): yield (up, k, a, b), O | I
                            else:
                                P = {(x - 1, y - 1, z) for x, y, z in I}             # the same triangle one layer lower, in the face
                                if P <= O and all(x + y + z == r - 1 for x, y, z in P) and connected(O - P): yield (up, k, a, b), O - P
        scan(f"{'islands on' if mode == 'islands' else 'one-layer pits in'} a face of O_{r}", gen())
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
    if mode == 'roof':
        N, n = int(sys.argv[2]), int(sys.argv[3]); A = octa(N)
        def gen():
            for a in range(0, N + n + 1):
                for b in range(0, 3):
                    for c in range(0, N + n + 1):
                        if (a + b + c - (N - n)) % 2: continue
                        B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); T = A | B1 | B2
                        if not connected(T): continue
                        if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue
                        yield (a, b, c), T
        scan(f"roof O_{N} over two legs O_{n}", gen())
    if mode == 'local':
        # the enumerations behind Lemma 68 (a), (b) and the constant of Theorem 69: over the 4,096 sets E of steps to empty sites at a site g
        ok_block = {}; maxo = 0; maxbl = 0; worst = 0
        for mask in range(0, 1 << 12):
            E = frozenset(ROOTS[i] for i in range(12) if mask >> i & 1)
            kind = REG.get(E, ('irregular',))[0]
            # bl = number of pairs (nu, d) for which g can block the chord of nu that ends at g - d: g is not exposed for nu,
            # g - d is in S, and g + (r - d) is empty for the step r of R_nu with r.d = 1 (it is a neighbour of g - d in R_nu).
            bl = 0
            for nu in NUS:
                if all(r in E for r in RNU[nu]): continue                  # g exposed for nu: it does not block
                for d in ROOTS:
                    if dot(d, nu) != 0 or neg(d) in E: continue
                    rr = [r for r in RNU[nu] if dot(r, d) == 1]; assert len(rr) == 1
                    if sub(rr[0], d) in E: bl += 1
            ok_block.setdefault(kind, []).append(bl)
            ex = [nu for nu in NUS if all(r in E for r in RNU[nu])]
            o = sum(1 for nu in ex for r in E if dot(r, nu) == 0); maxo = max(maxo, o); maxbl = max(maxbl, bl)
            if kind == 'irregular': worst = max(worst, 3 * len(E) - 9 + 1.5 * o + 1.5 * bl)
            if kind in ('face', 'ridge', 'interior'): assert bl == 0, (kind, E)
            if kind == 'trough': assert bl == 4
            if ex and any(dot(r, nu) == 0 for nu in ex for r in E): assert kind in ('ridge', 'irregular')
        print("largest possible number of chords blocked by a site, by shape:", {k: max(v) for k, v in ok_block.items()})
        print("largest number of open ends at a site:", maxo, "; largest number of chords blocked by a site:", maxbl)
        print("largest value of 3 deg - 9 + (3/2) o + (3/2) bl at a shape-irregular site (the constant of Theorem 69):", worst)
        print("face, ridge and interior sites block no chord; a trough site blocks at most 4; an exposed site with an open end is a ridge site or shape-irregular: checked on all 4,096 sets")
