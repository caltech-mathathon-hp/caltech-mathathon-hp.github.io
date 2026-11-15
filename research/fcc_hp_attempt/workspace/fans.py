"""Section 47: fans.  A site h of S with set E(h) of steps to empty sites is shape-regular if E(h) is empty (interior),
R_nu (face), R_nu u R_nu' for two octants that differ in one sign (ridge), or R_nu n R_nu' (trough); otherwise it is
shape-irregular.  Write R_nu = {r_1, r_2, r_3}.  For k in {1,2,3} and {i, j} the other two indices, the chords of nu with
direction r_i - r_j belong to fans: for a lattice point X of a plane nu.x = const,
    fan (nu, k, X):  the segments from X + t a to X + t b, t >= 0,  a = r_k - r_j,  b = r_k - r_i   (level t, t + 1 sites).
A chord with two open ends is ACTIVE if its two end sites are regular ridge sites; then they lie on the a-line and the
b-line of one fan and the chord is the level-t segment of that fan (asserted).  A fan with an active chord is counted.
ROOT of a fan: at its first active level t0, the sites z1 = X + (t0-1) a and z2 = X + (t0-1) b (equal to X for t0 = 1).
Kinds of root: 'tip, apex' (t0 = 1 and X is a vertex of an octahedron: 8 empty neighbours), 'tip, other' (t0 = 1),
'two roots' / 'one root' (t0 >= 2 and both / one of z1, z2 shape-irregular), 'inner root' (neither, but a shape-irregular
site on the first active run or on the level before it).  Reported for a body: U*, number of shape-irregular sites,
number of fans and fans by kind of root, 4 U* - 3 (number of fans), and the fans weighted by (1 - t0/n)^2.
The statement 3 (number of fans) <= 4 U* is FALSE (Section 47.5); the count that survives is per length (acount.py).
    python3 fans.py named | unions a b | near r | near2 r | islands r | bridge r | roof N n"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
neg = lambda a: (-a[0], -a[1], -a[2])
mul = lambda t, a: (t * a[0], t * a[1], t * a[2])
REG = {frozenset(): ('interior',)}
for nu in NUS:
    REG[frozenset(RNU[nu])] = ('face', nu)
    for i in range(3):
        nu2 = tuple(-nu[x] if x == i else nu[x] for x in range(3))
        REG[frozenset(RNU[nu]) | frozenset(RNU[nu2])] = ('ridge', frozenset((nu, nu2)))
        REG[frozenset(RNU[nu]) & frozenset(RNU[nu2])] = ('trough', frozenset((nu, nu2)))
assert len(REG) == 1 + 8 + 12 + 12
def nbr(nu, r):
    """the octant that shares the step r of R_nu with nu"""
    i = [x for x in range(3) if r[x] == 0][0]
    return tuple(-nu[x] if x == i else nu[x] for x in range(3))
FANS = {}       # (nu, d) with d a chord direction  ->  (k index, a, b, ridge set at the a-end, ridge set at the b-end)
for nu in NUS:
    R = RNU[nu]
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        a = sub(R[k], R[j]); b = sub(R[k], R[i])
        Ma = frozenset(R) | frozenset(RNU[nbr(nu, R[i])]); Mb = frozenset(R) | frozenset(RNU[nbr(nu, R[j])])
        assert dot(a, b) == 1 and neg(a) not in Ma and a not in Ma and sub(R[i], R[j]) in Ma and sub(R[j], R[i]) in Mb
        FANS[(nu, sub(b, a))] = (k, a, b, Ma, Mb)          # the chord runs from the a-end in direction b - a
def empties(S, h): return frozenset(r for r in ROOTS if add(h, r) not in S)
def analyse(S):
    S = set(S); E = {}
    def em(h):
        if h not in E: E[h] = empties(S, h)
        return E[h]
    irr = {h for h in S if em(h) not in REG}
    fans = {}; other_oo = []; ob = []
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        for d in DNU[nu]:
            for h in F:
                if sub(h, d) in F: continue
                L = 1; g = add(h, d)
                while g in F: L += 1; g = add(g, d)
                last = sub(g, d); o1 = sub(h, d) not in S; o2 = g not in S
                if o1 and o2:
                    if (nu, d) in FANS: k, a, b, Ma, Mb = FANS[(nu, d)]; e1, e2 = h, last
                    else: k, a, b, Ma, Mb = FANS[(nu, neg(d))]; e1, e2 = last, h
                    if em(e1) == Ma and em(e2) == Mb:
                        t = L - 1; X = sub(e1, mul(t, a)); assert add(X, mul(t, b)) == e2 and t >= 1
                        fans.setdefault((nu, k, X), {})[t] = (e1, e2)
                    else: other_oo.append((L, e1 in irr, e2 in irr))
                elif o1 or o2:
                    blocker = g if o1 else sub(h, d); end = h if o1 else last
                    ob.append((L, REG.get(em(blocker), ('irregular',))[0], end in irr))
    return S, em, irr, fans, other_oo, ob
APEX = {frozenset(r for r in ROOTS if r[ax] != -s) for ax in range(3) for s in (1, -1)}      # the 8 steps of a vertex of an octahedron
assert all(len(E) == 8 for E in APEX)
def kinds(S, em, irr, fans):
    """for each fan: (first active level, kind of root)"""
    out = {}
    for (nu, k, X), lev in fans.items():
        t0 = min(lev); e1, e2 = lev[t0]
        d = [dd for dd in FANS if dd[0] == nu and FANS[dd][0] == k][0]; _, a, b, Ma, Mb = FANS[d]
        z1 = sub(e1, a); z2 = sub(e2, b)
        i1 = z1 in irr; i2 = z2 in irr
        if t0 == 1:
            assert z1 == z2 == X
            kind = 'tip, apex' if em(X) in APEX else ('tip, other' if X in irr else 'tip, not irregular')
        elif i1 and i2: kind = 'two roots'
        elif i1 or i2: kind = 'one root'
        else:
            # both ridges go on towards the apex: an irregular site must lie on the first chord or on the level before
            c = sub(b, a); row0 = [add(e1, mul(s, c)) for s in range(t0 + 1)]; row1 = [add(z1, mul(s, c)) for s in range(t0)]
            kind = 'inner root' if any(x in irr for x in row0 + row1) else 'NO ROOT'
        out[(nu, k, X)] = (t0, kind)
    return out
def report(S, c=None, ns=(6, 12, 24, 48)):
    if c is None: c = cost(S)
    S, em, irr, fans, other_oo, ob = analyse(S); kd = kinds(S, em, irr, fans)
    hist = {}
    for t0, kind in kd.values(): hist[kind] = hist.get(kind, 0) + 1
    w = {n: sum(Fraction(max(0, n - t0), n) ** 2 for t0, kind in kd.values()) for n in ns}
    return dict(U=c['U'], irr=len(irr), fans=len(fans), kinds=hist, w=w, other_oo=len(other_oo), ob=len(ob),
                levels=sum(len(v) for v in fans.values()))
def line(name, S):
    t = report(S)
    print(f"{name}: U* = {t['U']}, shape-irregular sites {t['irr']}, fans {t['fans']} {dict(sorted(t['kinds'].items()))}, "
          f"4U* - 3 fans = {4 * t['U'] - 3 * t['fans']}, weighted fans (n = 6, 12, 24, 48): {', '.join(f'{float(v):.2f}' for v in t['w'].values())}", flush=True)
def scan(name, bodies):
    cnt = 0; worst = None; noroot = 0; allk = {}; worstw = None
    for tag, S in bodies:
        if len(S) < 2: continue
        t = report(S); cnt += 1
        for k, v in t['kinds'].items(): allk[k] = allk.get(k, 0) + v
        noroot += t['kinds'].get('NO ROOT', 0)
        sl = 4 * t['U'] - 3 * t['fans']
        if worst is None or sl < worst[0]: worst = (sl, tag, t['U'], t['fans'])
        slw = min(4 * t['U'] - 3 * v for v in t['w'].values())
        if worstw is None or slw < worstw[0]: worstw = (slw, tag, t['U'])
    print(f"{name}: {cnt} bodies; fans by root {dict(sorted(allk.items()))}; fans without a root: {noroot}; least 4U* - 3 fans = {worst[0]} ({worst[1]}, U* = {worst[2]}, fans {worst[3]}); "
          f"least 4U* - 3 (weighted fans) = {float(worstw[0]):.2f} ({worstw[1]}, U* = {worstw[2]})", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    if mode == 'named':
        named = [("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        named += [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
                  ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))), ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))),
                  ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))),
                  ("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 5 at (1,1)", octa(9) | island(9, 5, True, (1, 1))),
                  ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
                  ("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4)))]
        for nm, S in named: line(nm, S)
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
