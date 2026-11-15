"""Section 47: checks of Lemma 68 (d), Lemma 70 and Lemma 71 on bodies; `tips`: Lemma 68 (d) and Proposition 72 by enumeration.
(1) The two neighbours of a regular ridge site on the line of its ridge are in S, and each is a regular ridge site of
    the same ridge or shape-irregular.  (So a ridge segment ends at shape-irregular sites on both sides.)
(2) A silhouette run C such that all sites of C, and all sites of S on the line before it that are adjacent to C, are
    shape-regular has, on the line before it, a silhouette run P whose shadow is exactly C (so |C| = |P| + 1).
(3) For an active run C (level t of the fan (nu, k, X)) let t1 be the largest level s < t at which X + s a is not a
    regular ridge site of the ridge of the a-line, and t2 the same for the b-line.  Then all sites X + s a, t1 <= s <= t,
    are in S, likewise on the b-line, and max(t1, t2) >= 0.
(4) Charge C to the sites at level max(t1, t2) on the line or lines where it is attained (the nearest roots).  For
    fixed length, nu, k and line, no site is charged twice.
    python3 structure.py named | tips | unions a b | near r | islands r | bridge r | roof N n"""
import sys, itertools
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
from fans import REG, empties, neg, FANS, analyse, mul
from sources import runs
def checks(S):
    S2, em, irr, fans, other_oo, ob = analyse(S)
    n1 = n2 = n3 = n4 = 0
    # (1)
    for h in S2:
        t = REG.get(em(h))
        if t is None or t[0] != 'ridge': continue
        nu, nu2 = tuple(t[1]); r0 = [r for r in RNU[nu] if r in RNU[nu2]][0]; r1, r2 = [r for r in RNU[nu] if r != r0]; dr = sub(r1, r2)
        for g in (add(h, dr), sub(h, dr)):
            assert g in S2 and (g in irr or REG[em(g)] == t), (h, g)
            n1 += 1
    # (2)
    R = runs(S2)
    for (nu, k, pl, phi), chi in R.items():
        par = R.get((nu, k, pl, phi - 3), [])
        for psi, L, h, dd in chi:
            k2, a, b, Ma, Mb = FANS[(nu, dd)]
            C = [add(h, mul(t, dd)) for t in range(L)]
            near = set(C) | {x for x in ({sub(y, a) for y in C} | {sub(y, b) for y in C}) if x in S2}
            if any(x in irr for x in near): continue
            assert any(pp == psi + 1 and Lp == L - 1 for pp, Lp, *_ in par), (nu, k, h, L)
            n2 += 1
    # (3), (4)
    charged = {}
    for (nu, k, X), lev in fans.items():
        d = [dd for dd in FANS if dd[0] == nu and FANS[dd][0] == k][0]; _, a, b, Ma, Mb = FANS[d]
        for t, (e1, e2) in lev.items():
            ts = []
            for step, M in ((a, Ma), (b, Mb)):
                s = t - 1
                while em(add(X, mul(s, step))) == M: s -= 1
                assert all(add(X, mul(u, step)) in S2 for u in range(s, t + 1))
                assert add(X, mul(s, step)) in irr
                ts.append(s)
            tau = max(ts); assert tau >= 0, (nu, k, X, t, ts); n3 += 1
            for role, (step, s) in enumerate(zip((a, b), ts)):
                if s == tau:
                    key = (t, nu, k, role, add(X, mul(s, step)))
                    assert key not in charged, key
                    charged[key] = 1; n4 += 1
    return n1, n2, n3, n4
def scan(name, bodies):
    tot = [0, 0, 0, 0]; cnt = 0
    for tag, S in bodies:
        if len(S) < 2: continue
        r = checks(S); cnt += 1
        for i in range(4): tot[i] += r[i]
    print(f"{name}: {cnt} bodies; (1) holds at {tot[0]} ends of ridge sites, (2) for {tot[1]} runs, (3) for {tot[2]} active runs, (4) for {tot[3]} charges", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    if mode == 'named':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
                  ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))), ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))),
                  ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))),
                  ("O_9 with island 3 at (0,0)", octa(9) | island(9, 3, True, (0, 0))), ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
                  ("O_5 u O_8+(3,1,1)", octa(5) | octa(8, (3, 1, 1))), ("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
                  ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0)))]
        scan("named bodies", named)
    if mode == 'tips':
        # Lemma 68 (d): next to a regular ridge site h on the line of its ridge
        nchk = 0
        for M, t in REG.items():
            if t[0] != 'ridge': continue
            nu, nu2 = tuple(t[1]); r0 = [r for r in RNU[nu] if r in RNU[nu2]][0]; r1, r2 = [r for r in RNU[nu] if r != r0]
            for d in (sub(r1, r2), sub(r2, r1)):
                assert d not in M and neg(d) not in M                       # both neighbours on the line are in S
                emp = {sub(r, d) for r in M if dot(r, d) == 1}; occ = {sub(r, d) for r in ROOTS if dot(r, d) == 1 and r not in M} | {neg(d)}
                fits = [M2 for M2 in REG if emp <= M2 and not (occ & M2)]
                assert fits == [M], (M, d, fits); nchk += 1
        print(f"Lemma 68 (d): for each of the 12 ridges and both directions ({nchk} cases) the only shape-regular set that the next site of the line can have is that of the same ridge.")
        # Proposition 72: what an active run of 2 sites (level 1 of a fan with tip X) forces at X
        res = {}
        for (nu, c), (k, a, b, Ma, Mb) in FANS.items():
            must_empty = set(); must_occ = {a, b}
            for step, M in ((a, Ma), (b, Mb)):
                assert neg(step) not in M                                   # X itself is in S
                for p in ROOTS:
                    if dot(p, step) == 1:
                        (must_empty if sub(p, step) in M else must_occ).add(p)
            assert not (must_empty & must_occ)
            tip = [i for i in range(3) if all(p[i] == 0 for p in must_empty)]; assert len(tip) == 1 and len(must_empty) == 3
            ax = tip[0]; s = -a[ax]; assert all(p[ax] == -s for p in must_occ) and len(must_occ) == 4 and b[ax] == -s
            res.setdefault((ax, s), []).append((nu, frozenset(must_empty)))
        for (ax, s), lst in sorted(res.items()):
            hor = frozenset(p for p in ROOTS if p[ax] == 0)
            assert len(lst) == 4 and all(me <= hor for nu, me in lst) and len({me for nu, me in lst}) == 4
        print("for each of the 24 pairs (nu, k): an active run of 2 sites with tip X forces the four neighbours of X on the side away from the tip to be in S")
        print("and three of the four neighbours of X in the plane orthogonal to the axis to be empty; the four faces around one axis direction leave out four different ones.")
        print("So X is the tip of 4 such fans of one axis direction if all four are empty, and of at most 1 if exactly three are.")
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
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
