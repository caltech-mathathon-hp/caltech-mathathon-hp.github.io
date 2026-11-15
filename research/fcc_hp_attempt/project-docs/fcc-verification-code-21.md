# FCC HP folding: verification code, part 21 (twenty-fourth pass, 15 Nov 2026)

Scripts for Section 47 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): shape-regular sites and fans (Lemma 68); the count (A) of active runs of one length against units, and the inequality of Theorem 69; roots and charges (Lemmas 70, 71); tips (Proposition 72); three counts that are false (fans, sources of runs, end-sources). They import `gmin.py`, `psi.py` (part 16), `chords.py` (part 19) and `islands.py`, `chordM3.py` (part 20). `acount.py local` and `structure.py tips` are the enumerations behind Lemma 68 and Proposition 72, and `acount.py` checks the inequality of Theorem 69(a) on bodies; the scans are evidence for (A), not a proof.

| Script | What it does | Run |
|---|---|---|
| `fans.py` | shape-regular sites, fans, active runs, the kind of root of each fan; the number of fans against units (false) | `python3 fans.py named`, `unions a b`, `near r`, `near2 r`, `islands r`, `bridge r`, `roof N n` |
| `acount.py` | a_L, the count (A), the inequality of Theorem 69(a) against M'_n; `local`: the enumerations of Lemma 68 and the constant 99 | `python3 acount.py local`, `named`, `special`, `unions a b`, `near r`, `near2 r`, `islands r`, `pits r`, `bridge r`, `roof N n` |
| `structure.py` | Lemma 68(d), Lemma 70, Lemma 71 and the parent of a run with regular surroundings, on bodies; `tips`: Lemma 68(d) and Proposition 72 by enumeration | `python3 structure.py tips`, `named`, `unions a b`, `near r`, `islands r`, `bridge r`, `roof N n` |
| `charges.py` | the nearest-root charge site by site | `python3 charges.py` |
| `asearch.py` | annealing against (A) | `python3 asearch.py seed steps T0 kind` |
| `sources.py` | sources of runs by matching on neighbouring lines, with the telescoping bound; the count of sources against units (false) | `python3 sources.py named` |
| `endsrc.py` | end-sources along ridge segments, with the telescoping bound; the count against units (false) | `python3 endsrc.py named` |

## `fans.py`

```python
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
```

## `acount.py`

```python
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
```

## `structure.py`

```python
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
```

## `charges.py`

```python
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
```

## `asearch.py`

```python
"""Section 47: search for a finite connected set, not a regular octahedron, with 3 a_max >= 4 U* (a violation of (A)).
Score 4 U* - 3 a_max (acount.py); annealing by single sites of the boundary.  A body with score <= 0 that is not a
regular octahedron is printed.
    python3 asearch.py seed steps T0 kind        kind: octa | near | islands | unions | steps"""
import sys, random, math
from gmin import *
from acount import acount
from psi import boundary_moves, toggle, unions
from islands import island
def is_octa(S):
    S = set(S); n = len(S)
    xs = [h[0] for h in S]; ys = [h[1] for h in S]; zs = [h[2] for h in S]
    c = ((min(xs) + max(xs)) // 2, (min(ys) + max(ys)) // 2, (min(zs) + max(zs)) // 2); r = (max(xs) - min(xs)) // 2 + 1
    return S == octa(r, c)
def score(S):
    c = cost(S); a, irr = acount(S); am = max(a.values(), default=0)
    return 4 * c['U'] - 3 * am, c['U'], am
seed = int(sys.argv[1]); steps = int(sys.argv[2]); T0 = float(sys.argv[3]); kind = sys.argv[4]; rng = random.Random(seed)
if kind == 'octa': starts = [(f"O_{r}", octa(r)) for r in (5, 6, 7)]
if kind == 'near': starts = [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 without two vertices", octa(7) - {(6, 0, 0), (0, 6, 0)})]
if kind == 'islands': starts = [("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 3 at (0,2)", octa(9) | island(9, 3, True, (0, 2))), ("O_7 with island 3 at (0,1)", octa(7) | island(7, 3, True, (0, 1)))]
if kind == 'unions':
    U = list(unions(6, 6)); rng.shuffle(U); starts = [(f"O_6 u O_6+{v}", S) for v, ov, S in U[:6]]
if kind == 'steps': starts = [("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))), ("O_5 u O_8+(2,2,1)", octa(5) | octa(8, (2, 2, 1)))]
for name, S in starts:
    cur = score(S); s0 = cur; best = (cur, set(S)); mv = boundary_moves(S); found = 0
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.05
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = score(S2)
        if u[0] <= 0 and not is_octa(S2): found += 1; print("   VIOLATION", u, sorted(S2), flush=True)
        if u[0] <= cur[0] or rng.random() < math.exp((cur[0] - u[0]) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if not is_octa(S) and (is_octa(best[1]) or cur[0] < best[0][0]): best = (cur, set(S))
    b = best[0]
    print(f"{name}: start 4U* - 3 a_max = {s0[0]}; least value reached on a body that is not a regular octahedron: {b[0]} (N = {len(best[1])}, U* = {b[1]}, a_max = {b[2]}); violations found: {found}", flush=True)
```

## `sources.py`

```python
"""Section 47: sources of silhouette runs.
Fix nu and k as in fans.py: chord direction c = b - a, lines of a plane nu.x = const ordered by phi(x) = x.(a + b)
(neighbouring lines differ by 3; phi grows away from the apex of the triangle), position on a line psi(x) = x.(b - a)
(steps of 2).  For a silhouette run P on the line phi - 3 and a silhouette run C on the line phi:
    P and C are ADJACENT if a site of C is a neighbour of a site of P (C meets the shadow of P, the |P| + 1 sites
    of the line phi that have a neighbour in P);  they are LINKED (J) if adjacent and |C| >= |P| + 1 - J.
A matching takes each run at most once as parent and at most once as child, in linked pairs only.
sigma_J(S) = least number of runs that are not a child, over all matchings (a maximum matching for each pair of lines).
Telescoping (Section 47.5, item 2), with Gam(L) = (n + 1 - L)+^2 / 2, so that (n + 1/2 - L)+ = Gam(L) - Gam(L + 1):
    sum over silhouette runs of (n + 1/2 - |C|)+  <=  sum over the unmatched children of Gam(|C|)
                                                      + sum over matched pairs of (Gam(|C|) - Gam(|P| + 1))+
The script asserts this for the matching it finds, and reports 4 U* - 3 sigma_J.
    python3 sources.py named | unions a b | near r | near2 r | islands r | bridge r | roof N n | special | pits r"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
from fans import FANS, REG, empties, neg
def runs(S):
    """silhouette runs: dict (nu, k, plane, phi) -> list of (psi of first site, length, first site, direction of the run)"""
    out = {}
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        for d in DNU[nu]:
            dd = d if (nu, d) in FANS else neg(d); k, a, b, Ma, Mb = FANS[(nu, dd)]; ab = add(a, b)
            for h in F:
                if add(h, dd) in F and sub(h, dd) in F: continue
                if sub(h, dd) in F: continue                      # h is the first site in direction dd
                L = 1; g = add(h, dd)
                while g in F: L += 1; g = add(g, dd)
                if sub(h, dd) in S or g in S: continue            # a blocked end
                out.setdefault((nu, k, dot(nu, h), dot(h, ab)), []).append((dot(h, dd), L, h, dd))
    return out
def matching(par, chi, J):
    """maximum matching between parents and children (lists of (psi, L, ...)), linked pairs only; returns child index -> parent index"""
    adj = []
    for (pc, Lc, *_) in chi:
        adj.append([i for i, (pp, Lp, *_) in enumerate(par) if pc <= pp + 2 * Lp - 1 and pp - 1 <= pc + 2 * (Lc - 1) and Lc >= Lp + 1 - J])
    mp = {}; mc = {}
    def aug(c, seen):
        for p in adj[c]:
            if p in seen: continue
            seen.add(p)
            if p not in mp or aug(mp[p], seen): mp[p] = c; mc[c] = p; return True
        return False
    for c in range(len(chi)): aug(c, set())
    return mc
def sigma(S, J=2, ns=(), want_sources=False):
    R = runs(S); unmatched = []; pairs = []
    for key, chi in R.items():
        nu, k, pl, phi = key; par = R.get((nu, k, pl, phi - 3), [])
        mc = matching(par, chi, J)
        for c, x in enumerate(chi):
            if c in mc: pairs.append((par[mc[c]][1], x[1]))
            else: unmatched.append((key, x))
    for n in ns:                                                  # the telescoping inequality
        Gam = lambda L: Fraction(max(0, n + 1 - L) ** 2, 2)
        lhs = sum(max(Fraction(0), n + Fraction(1, 2) - x[1]) for chi in R.values() for x in chi)
        rhs = sum(Gam(x[1]) for key, x in unmatched) + sum(max(Fraction(0), Gam(Lc) - Gam(Lp + 1)) for Lp, Lc in pairs)
        assert lhs <= rhs, (n, lhs, rhs)
    jog = sum(max(0, Lp + 1 - Lc) for Lp, Lc in pairs)
    if want_sources: return unmatched, pairs
    return len(unmatched), jog, sum(len(v) for v in R.values())
def rooted(S, unmatched):
    """number of unmatched children with no shape-irregular site in C or among the sites of the line before that are adjacent to C"""
    S = set(S); bad = 0
    for (nu, k, pl, phi), (psi, L, h, dd) in unmatched:
        k2, a, b, Ma, Mb = FANS[(nu, dd)]
        C = [add(h, (t * dd[0], t * dd[1], t * dd[2])) for t in range(L)]
        near = set(C) | {sub(x, a) for x in C} | {sub(x, b) for x in C}
        if not any(x in S and empties(S, x) not in REG for x in near): bad += 1
    return bad
def line(name, S):
    c = cost(S); out = []
    for J in (1, 2, 3):
        s, jog, tot = sigma(S, J, ns=(3, 7, 20, 60)); out.append(f"sigma_{J} = {s} (4U* - 3 sigma = {4 * c['U'] - 3 * s}, jogs {jog})")
    un, pairs = sigma(S, 2, want_sources=True)
    print(f"{name}: U* = {c['U']}, runs {tot}; " + "; ".join(out) + f"; sources without an irregular site next to them: {rooted(S, un)}; lengths of the sources (J = 2): {sorted(x[1][1] for x in un)}", flush=True)
def scan(name, bodies, J=2):
    cnt = 0; worst = None; hist = {}; noroot = 0; eq = []
    for tag, S in bodies:
        if len(S) < 2: continue
        c = cost(S); un, pairs = sigma(S, J, want_sources=True); s = len(un); cnt += 1
        if cnt % 25 == 1: sigma(S, J, ns=(4, 11, 38)); noroot += rooted(S, un)
        sl = 4 * c['U'] - 3 * s; hist[min(sl, 12)] = hist.get(min(sl, 12), 0) + 1
        if sl <= 0: eq.append((tag, c['U'], s))
        if worst is None or sl < worst[0]: worst = (sl, tag, c['U'], s)
    print(f"{name}: {cnt} bodies, J = {J}; least 4U* - 3 sigma = {worst[0]} ({worst[1]}, U* = {worst[2]}, sigma = {worst[3]}); bodies with 4U* - 3 sigma <= 0: {len(eq)} {eq[:6]}; "
          f"number of bodies by 4U* - 3 sigma (12 = 12 or more): {dict(sorted(hist.items()))}; sources without an irregular site next to them (every 25th body): {noroot}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    J = 2
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
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)), J)
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))), J)
    if mode == 'near2':
        r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
        def gen():
            for h, g in itertools.combinations(mv, 2):
                T = toggle(toggle(S, h), g)
                if connected(T): yield (h, g), T
        scan(f"bodies at two sites from O_{r}", gen(), J)
    if mode == 'islands':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen(), J)
    if mode == 'pits':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = {(x - 1, y - 1, z) for x, y, z in island(r, k, up, (a, b))}      # the same triangle in the face layer
                            if I <= O and connected(O - I): yield (up, k, a, b), O - I
        scan(f"one-layer pits in a face of O_{r}", gen(), J)
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
        scan(f"two O_{r} joined by one site", gen(), J)
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
        scan(f"roof O_{N} over two legs O_{n}", gen(), J)
    if mode == 'special':
        sp = [("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
              ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
              ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
              ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
              ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
              ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
              ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}), ("O_7 with twin tops (2,0,0)", octa(7) | octa(7, (2, 0, 0))),
              ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})]
        for nm, S in sp: line(nm, S)
```

## `endsrc.py`

```python
"""Section 47: end-sources.  A regular ridge site h (E(h) = R_nu u R_nu', the two octants sharing the step r0) has on
each of its two faces mu two open ends: with R_mu = {r0, r1, r2} the chords of mu that start at h run in the
directions c1 = r1 - r0 and c2 = r2 - r0, and h - c1, h - c2 are empty.  A ridge segment is a maximal run of regular
ridge sites of one ridge on a line (direction c1 - c2).  For (segment, face mu, direction c) order the sites of the
segment from the tip side: for c = c1 by increasing position in direction c2 - c1 (the chords of a fan grow that way).
Going through the sites in this order, an end whose chord has two open ends (length L) is
    COVERED   if the last such end before it on the segment had a chord of at most L - 1 sites,
    an END-SOURCE otherwise (the first one of the segment, or one whose chord did not grow).
Sigma(S) = number of end-sources.  Telescoping per end (Section 47.5, item 3):
    sum over the ends at regular ridge sites with two-open-ended chords of (n/2 + 1/4 - L/2)+
        <=  sum over the end-sources of (n + 1 - L)+^2 / 4.
The script asserts this, and the lower bound LB_n <= M'_n obtained from it:
    LB_n = (2n^2 - 3n) U* - 9n def1 + n sum_h c(h) - (3/4) sum_{end-sources} (n + 1 - L)+^2
           - 3 sum over the other open ends of their deficits,          c(h) = 9 - 3 deg(h) + (3/2) o(h).
Reported: U*, Sigma, 8 U* - 3 Sigma, the lengths L of the end-sources, and Sigma split into first ends and breaks.
    python3 endsrc.py named | special | unions a b | near r | near2 r | islands r | pits r | bridge r | roof N n"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, dot, sub, chords
from fans import REG, empties, neg, nbr
Q = Fraction(1, 4)
def end_sources(S):
    """returns (list of (L, kind) for the end-sources, list of L for all two-open-ended chord ends at regular ridge sites,
    number of open ends of every kind at regular ridge sites)"""
    S = set(S); E = {}
    def em(h):
        if h not in E: E[h] = empties(S, h)
        return E[h]
    F = {nu: {h for h in S if all(add(h, r) not in S for r in RNU[nu])} for nu in NUS}
    ridge = {h: REG[em(h)][1] for h in S if em(h) in REG and REG[em(h)][0] == 'ridge'}
    src = []; allL = []; nopen = 0
    done = set()
    for h, pair in ridge.items():
        if (h, pair) in done: continue
        nu, nu2 = tuple(pair); r0 = [r for r in RNU[nu] if r in RNU[nu2]][0]
        r1, r2 = [r for r in RNU[nu] if r != r0]; dr = sub(r1, r2)            # ridge direction
        g = h
        while ridge.get(sub(g, dr)) == pair: g = sub(g, dr)
        seg = [g]; done.add((g, pair))
        while ridge.get(add(seg[-1], dr)) == pair: seg.append(add(seg[-1], dr)); done.add((seg[-1], pair))
        for mu in (nu, nu2):
            q1, q2 = [r for r in RNU[mu] if r != r0]
            for c, other in ((sub(q1, r0), sub(q2, r0)), (sub(q2, r0), sub(q1, r0))):
                away = sub(other, c)                                         # the chords of direction c grow in this direction
                assert away in (dr, neg(dr))
                order = seg if away == dr else seg[::-1]
                last = None
                for x in order:
                    assert sub(x, c) not in S
                    L = 1; y = add(x, c)
                    while y in F[mu]: L += 1; y = add(y, c)
                    nopen += 1
                    if y in S: continue                                      # blocked at the far end
                    allL.append(L)
                    if last is None: src.append((L, 'first'))
                    elif L < last + 1: src.append((L, 'break'))
                    last = L
    return src, allL, nopen
def bound(S, c, n, src=None, allL=None):
    """LB_n and M'_n"""
    from chordM3 import data3, M1
    if src is None: src, allL, nopen = end_sources(S)
    cc, oo, ob, bb = data3(S, c); U = c['U']; d1 = c['surface'] - c['nu1']
    sumc = 9 * c['surface'] - 3 * c['boundary'] + Fraction(3, 2) * (2 * len(oo) + len(ob))
    tele = sum(Fraction(max(0, n + 1 - L) ** 2, 4) for L, kind in src)
    reg = sum(max(Fraction(0), Fraction(n, 2) + Q - Fraction(L, 2)) for L in allL)
    assert reg <= tele, (n, reg, tele)
    total = sum(2 * max(Fraction(0), Fraction(n, 2) + Q - Fraction(L, 2)) for L in oo) + sum(max(Fraction(0), Fraction(n, 2) + Q - L) for L in ob)
    LB = (2 * n * n - 3 * n) * U - 9 * n * d1 + n * sumc - 3 * tele - 3 * (total - reg)
    M = M1(c, oo, ob, n); assert LB <= M, (n, LB, M)
    return LB, M
def line(name, S):
    c = cost(S); src, allL, nopen = end_sources(S); s = len(src)
    for n in (4, 9, 38, 150): bound(S, c, n, src, allL)
    fb = (sum(1 for L, k in src if k == 'first'), sum(1 for L, k in src if k == 'break'))
    hist = {}
    for L, k in src: hist[L] = hist.get(L, 0) + 1
    print(f"{name}: U* = {c['U']}, Sigma = {s} (first ends {fb[0]}, breaks {fb[1]}), 8U* - 3 Sigma = {8 * c['U'] - 3 * s}; end-sources by length of chord: {dict(sorted(hist.items()))}", flush=True)
def scan(name, bodies):
    cnt = 0; worst = None; hist = {}; eq = []; nb = 0
    for tag, S in bodies:
        if len(S) < 2: continue
        c = cost(S); src, allL, nopen = end_sources(S); s = len(src); cnt += 1; nb += sum(1 for L, k in src if k == 'break')
        if cnt % 20 == 1:
            for n in (5, 38): bound(S, c, n, src, allL)
        sl = 8 * c['U'] - 3 * s; hist[min(sl, 24)] = hist.get(min(sl, 24), 0) + 1
        if sl <= 0: eq.append((tag, c['U'], s))
        if worst is None or sl < worst[0]: worst = (sl, tag, c['U'], s)
    print(f"{name}: {cnt} bodies; least 8U* - 3 Sigma = {worst[0]} ({worst[1]}, U* = {worst[2]}, Sigma = {worst[3]}); bodies with 8U* - 3 Sigma <= 0: {len(eq)} {eq[:6]}; "
          f"breaks in all bodies together: {nb}; number of bodies by 8U* - 3 Sigma (24 = 24 or more): {dict(sorted(hist.items()))}", flush=True)
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
```

## Output of `python3 acount.py local`

```
largest possible number of chords blocked by a site, by shape: {'interior': 0, 'trough': 4, 'irregular': 16, 'face': 0, 'ridge': 0}
largest number of open ends at a site: 48 ; largest number of chords blocked by a site: 16
largest value of 3 deg - 9 + (3/2) o + (3/2) bl at a shape-irregular site (the constant of Theorem 69): 99.0
face, ridge and interior sites block no chord; a trough site blocks at most 4; an exposed site with an open end is a ridge site or shape-irregular: checked on all 4,096 sets
```

## Output of `python3 structure.py tips`

```
Lemma 68 (d): for each of the 12 ridges and both directions (24 cases) the only shape-regular set that the next site of the line can have is that of the same ridge.
for each of the 24 pairs (nu, k): an active run of 2 sites with tip X forces the four neighbours of X on the side away from the tip to be in S
and three of the four neighbours of X in the plane orthogonal to the axis to be empty; the four faces around one axis direction leave out four different ones.
So X is the tip of 4 such fans of one axis direction if all four are empty, and of at most 1 if exactly three are.
```

## Output of `python3 acount.py named` and `special`

```
single site: U* = 15, |I| = 1, def1 = 0, a_max = 0, 4U* - 3 a_max = 60; a_L: {}
pair: U* = 26, |I| = 2, def1 = 0, a_max = 0, 4U* - 3 a_max = 104; a_L: {}
O_2: U* = 42, |I| = 6, def1 = 0, a_max = 0, 4U* - 3 a_max = 168; a_L: {}
O_3: U* = 54, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 144; a_L: {2: 24}
O_4: U* = 42, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 96; a_L: {2: 24, 3: 24}
O_5: U* = 18, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 0; a_L: {2: 24, 3: 24, 4: 24}
O_6: U* = 18, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 0; a_L: {2: 24, 3: 24, 4: 24, 5: 24}
O_7: U* = 18, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 0; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24}
O_8: U* = 18, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 0; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24, 7: 24}
O_9: U* = 18, |I| = 6, def1 = 0, a_max = 24, 4U* - 3 a_max = 0; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24, 7: 24, 8: 24}
tetra 4: U* = 60, |I| = 16, def1 = 0, a_max = 0, 4U* - 3 a_max = 240; a_L: {}
tetra 6: U* = 60, |I| = 28, def1 = 0, a_max = 0, 4U* - 3 a_max = 240; a_L: {}
tetra 9: U* = 78, |I| = 46, def1 = 0, a_max = 0, 4U* - 3 a_max = 312; a_L: {}
rod: U* = 114, |I| = 10, def1 = 0, a_max = 0, 4U* - 3 a_max = 456; a_L: {}
layer: U* = 195, |I| = 37, def1 = 0, a_max = 0, 4U* - 3 a_max = 780; a_L: {}
O_6 without a vertex: U* = 19, |I| = 9, def1 = 0, a_max = 24, 4U* - 3 a_max = 4; a_L: {2: 20, 3: 24, 4: 24, 5: 16}
O_6 with a site on a face: U* = 24, |I| = 10, def1 = 0, a_max = 24, 4U* - 3 a_max = 24; a_L: {2: 24, 3: 23, 4: 21, 5: 22}
O_7 u O_7+(2,2,2): U* = 24, |I| = 18, def1 = 0, a_max = 30, 4U* - 3 a_max = 6; a_L: {2: 30, 3: 24, 4: 24, 5: 24, 6: 24}
O_7 u O_7+(1,1,0): U* = 20, |I| = 8, def1 = 0, a_max = 24, 4U* - 3 a_max = 8; a_L: {2: 20, 3: 24, 4: 24, 5: 24, 6: 24, 7: 4}
O_7 u O_7+(2,0,0): U* = 42, |I| = 14, def1 = 0, a_max = 24, 4U* - 3 a_max = 96; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24}
O_7 u O_7+(4,0,0): U* = 54, |I| = 14, def1 = 0, a_max = 40, 4U* - 3 a_max = 96; a_L: {2: 40, 3: 24, 4: 24, 5: 24, 6: 32}
two O_5 and a site: U* = 43, |I| = 13, def1 = 0, a_max = 48, 4U* - 3 a_max = 28; a_L: {2: 48, 3: 48, 4: 48}
two O_6 vertex to vertex: U* = 44, |I| = 12, def1 = 0, a_max = 48, 4U* - 3 a_max = 32; a_L: {2: 48, 3: 48, 4: 48, 5: 48}
two O_7 tip to tip: U* = 51, |I| = 11, def1 = 0, a_max = 48, 4U* - 3 a_max = 60; a_L: {2: 48, 3: 48, 4: 48, 5: 48, 6: 48}
O_9 with island 3 at (0,0): U* = 21, |I| = 11, def1 = 0, a_max = 24, 4U* - 3 a_max = 12; a_L: {2: 24, 3: 23, 4: 21, 5: 24, 6: 20, 7: 20, 8: 22}
O_9 with island 3 at (1,2): U* = 21, |I| = 12, def1 = 0, a_max = 27, 4U* - 3 a_max = 3; a_L: {2: 27, 3: 24, 4: 22, 5: 21, 6: 21, 7: 21, 8: 23}
O_9 with island 5 at (1,1): U* = 21, |I| = 12, def1 = 0, a_max = 27, 4U* - 3 a_max = 3; a_L: {2: 27, 3: 24, 4: 24, 5: 21, 6: 21, 7: 21, 8: 21}
O_13 with island 6 at (2,2): U* = 21, |I| = 12, def1 = 0, a_max = 27, 4U* - 3 a_max = 3; a_L: {2: 27, 3: 27, 4: 27, 5: 24, 6: 21, 7: 21, 8: 21, 9: 21, 10: 21, 11: 21, 12: 24}
O_9 with reversed island 3: U* = 33, |I| = 21, def1 = 0, a_max = 24, 4U* - 3 a_max = 60; a_L: {2: 24, 3: 24, 4: 24, 5: 21, 6: 21, 7: 21, 8: 21}
O_5 u O_8+(3,1,1): U* = 21, |I| = 11, def1 = 0, a_max = 24, 4U* - 3 a_max = 12; a_L: {2: 24, 3: 22, 4: 22, 5: 21, 6: 19, 7: 22}
O_9 with a cavity O_3: U* = 126, |I| = 6, def1 = 42, a_max = 24, 4U* - 3 a_max = 432; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24, 7: 24, 8: 24}
O_8 and O_4 on a vertex: U* = 54, |I| = 14, def1 = 0, a_max = 40, 4U* - 3 a_max = 96; a_L: {2: 40, 3: 40, 4: 24, 5: 24, 6: 24, 7: 16}
O_8 and O_4 on a face: U* = 60, |I| = 30, def1 = 3, a_max = 39, 4U* - 3 a_max = 123; a_L: {2: 39, 3: 39, 4: 15, 5: 15, 6: 21, 7: 21}
O_7 with a one-site cavity: U* = 36, |I| = 6, def1 = 11, a_max = 24, 4U* - 3 a_max = 72; a_L: {2: 24, 3: 24, 4: 24, 5: 24, 6: 24}
ring of four O_5: U* = 141, |I| = 32, def1 = 0, a_max = 96, 4U* - 3 a_max = 276; a_L: {2: 64, 3: 96, 4: 40}
three O_6 in a row, vertex to vertex: U* = 70, |I| = 18, def1 = 0, a_max = 72, 4U* - 3 a_max = 64; a_L: {2: 72, 3: 72, 4: 72, 5: 72}
three O_6 at a right angle: U* = 70, |I| = 18, def1 = 0, a_max = 72, 4U* - 3 a_max = 64; a_L: {2: 72, 3: 72, 4: 72, 5: 72}
two O_7 along an axis, offset 6: U* = 54, |I| = 14, def1 = 0, a_max = 40, 4U* - 3 a_max = 96; a_L: {2: 40, 3: 40, 4: 24, 5: 32, 6: 32}
two O_6 joined by a zigzag: U* = 54, |I| = 14, def1 = 0, a_max = 48, 4U* - 3 a_max = 72; a_L: {2: 48, 3: 48, 4: 48, 5: 48}
two O_6 and a site: U* = 43, |I| = 13, def1 = 0, a_max = 48, 4U* - 3 a_max = 28; a_L: {2: 48, 3: 48, 4: 48, 5: 48}
```

## Output of `python3 acount.py`: `unions 7 7`, `unions 9 9`, `unions 5 8`, `unions 6 9`, `near 5` to `near 8`, `islands 9`, `islands 13`, `pits 9`, `pits 13`, `bridge 5`, `bridge 6`, `roof 6 5`, `roof 6 6`, `roof 7 5`, `roof 7 6`, `roof 8 4`; then `near2 5`

```
unions O_7, O_7+v: 79 bodies; least 4U* - 3 a_max = 6 ((2, 2, 2), U* = 24, a_max = 30); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {6: 1, 8: 1, 12: 77}; largest |I| / U* = 0.75
unions O_9, O_9+v: 146 bodies; least 4U* - 3 a_max = 6 ((2, 2, 2), U* = 24, a_max = 30); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {6: 1, 8: 1, 12: 144}; largest |I| / U* = 0.75
unions O_5, O_8+v: 61 bodies; least 4U* - 3 a_max = 12 ((2, 2, 1), U* = 21, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 61}; largest |I| / U* = 0.63
unions O_6, O_9+v: 88 bodies; least 4U* - 3 a_max = 12 ((2, 2, 1), U* = 21, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 88}; largest |I| / U* = 0.65
bodies at one site from O_5: 206 bodies; least 4U* - 3 a_max = 4 ((-4, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 6, 12: 200}; largest |I| / U* = 0.55
bodies at one site from O_6: 294 bodies; least 4U* - 3 a_max = 4 ((-5, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 6, 12: 288}; largest |I| / U* = 0.55
bodies at one site from O_7: 398 bodies; least 4U* - 3 a_max = 4 ((-6, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 6, 12: 392}; largest |I| / U* = 0.55
bodies at one site from O_8: 518 bodies; least 4U* - 3 a_max = 4 ((-7, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 6, 12: 512}; largest |I| / U* = 0.55
islands on a face of O_9: 110 bodies; least 4U* - 3 a_max = 3 ((True, 3, 0, 2), U* = 21, a_max = 27); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {3: 12, 6: 4, 9: 9, 12: 85}; largest |I| / U* = 0.69
islands on a face of O_13: 315 bodies; least 4U* - 3 a_max = 3 ((True, 3, 0, 2), U* = 21, a_max = 27); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {3: 83, 6: 21, 9: 12, 12: 199}; largest |I| / U* = 0.76
one-layer pits in a face of O_9: 149 bodies; least 4U* - 3 a_max = 4 ((True, 1, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 4, 12: 145}; largest |I| / U* = 0.74
one-layer pits in a face of O_13: 391 bodies; least 4U* - 3 a_max = 4 ((True, 1, 0, 0), U* = 19, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {4: 4, 12: 387}; largest |I| / U* = 0.81
two O_5 joined by one site: 146 bodies; least 4U* - 3 a_max = 28 (((10, 1, 1), (5, 1, 0)), U* = 43, a_max = 48); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 146}; largest |I| / U* = 0.38
two O_6 joined by one site: 233 bodies; least 4U* - 3 a_max = 28 (((12, 1, 1), (6, 0, 1)), U* = 43, a_max = 48); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 233}; largest |I| / U* = 0.38
roof O_6 over two legs O_5: 92 bodies; least 4U* - 3 a_max = 64 ((10, 0, 1), U* = 70, a_max = 72); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 92}; largest |I| / U* = 0.70
roof O_6 over two legs O_6: 116 bodies; least 4U* - 3 a_max = 48 ((1, 1, 2), U* = 30, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 116}; largest |I| / U* = 0.69
roof O_7 over two legs O_5: 104 bodies; least 4U* - 3 a_max = 64 ((11, 0, 1), U* = 70, a_max = 72); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 104}; largest |I| / U* = 0.68
roof O_7 over two legs O_6: 130 bodies; least 4U* - 3 a_max = 64 ((12, 0, 1), U* = 70, a_max = 72); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 130}; largest |I| / U* = 0.70
roof O_8 over two legs O_4: 96 bodies; least 4U* - 3 a_max = 40 ((5, 0, 1), U* = 34, a_max = 32); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {12: 96}; largest |I| / U* = 0.61
bodies at two sites from O_5: 21055 bodies; least 4U* - 3 a_max = 8 (((-4, 0, 0), (0, -4, 0)), U* = 20, a_max = 24); bodies with 4U* - 3 a_max <= 0: 0 []; number of bodies by 4U* - 3 a_max (12 = 12 or more): {8: 15, 12: 21040}; largest |I| / U* = 0.69
```

## Output of `python3 structure.py`: `named`, `unions 7 7`, `unions 5 8`, `near 6`, `islands 9`, `bridge 5`, `roof 6 5`

```
named bodies: 28 bodies; (1) holds at 3200 ends of ridge sites, (2) for 2233 runs, (3) for 2953 active runs, (4) for 5876 charges
unions O_7, O_7+v: 79 bodies; (1) holds at 15572 ends of ridge sites, (2) for 10356 runs, (3) for 13768 active runs, (4) for 26810 charges
unions O_5, O_8+v: 61 bodies; (1) holds at 11120 ends of ridge sites, (2) for 7444 runs, (3) for 10013 active runs, (4) for 19513 charges
bodies at one site from O_6: 294 bodies; (1) holds at 27072 ends of ridge sites, (2) for 18360 runs, (3) for 25824 active runs, (4) for 50448 charges
islands on a face of O_9: 110 bodies; (1) holds at 18320 ends of ridge sites, (2) for 14293 runs, (3) for 17279 active runs, (4) for 33892 charges
two O_5 joined by one site: 146 bodies; (1) holds at 20392 ends of ridge sites, (2) for 12506 runs, (3) for 19650 active runs, (4) for 38604 charges
roof O_6 over two legs O_5: 92 bodies; (1) holds at 16308 ends of ridge sites, (2) for 8312 runs, (3) for 13558 active runs, (4) for 26258 charges
```

## Output of `python3 charges.py`

```
O_6: U* = 18
   (-5, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (0, -5, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (0, 0, -5) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (0, 0, 5) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (0, 5, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (5, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
O_9 with island 3 at (1,2): U* = 21
   (-8, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, -8, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, 0, -8) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, 0, 8) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 3, 5: 3, 6: 3, 7: 3, 8: 4
   (0, 8, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 3, 5: 3, 6: 3, 7: 3, 8: 4
   (2, 3, 5) (7 empty neighbours): largest charge 1; by L: 2: 1
   (2, 5, 3) (7 empty neighbours): largest charge 1; by L: 2: 1
   (4, 3, 3) (7 empty neighbours): largest charge 1; by L: 2: 1
   (8, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 3, 6: 3, 7: 3, 8: 3
O_9 with island 3 at (0,0): U* = 21
   (-8, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, -8, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, 0, -8) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 4, 7: 4, 8: 4
   (0, 0, 8) (7 empty neighbours): largest charge 2; by L: 2: 1, 3: 2, 4: 1, 5: 1, 6: 1, 7: 1, 8: 1
   (0, 3, 5) (4 empty neighbours): largest charge 3/2; by L: 5: 3/2, 6: 3/2, 7: 3/2, 8: 3/2
   (0, 8, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 2, 7: 2, 8: 2
   (1, 1, 8) (7 empty neighbours): largest charge 1; by L: 2: 1, 3: 1
   (1, 3, 6) (7 empty neighbours): largest charge 1; by L: 2: 1, 8: 1
   (3, 0, 5) (4 empty neighbours): largest charge 3/2; by L: 5: 3/2, 6: 3/2, 7: 3/2, 8: 3/2
   (3, 1, 6) (7 empty neighbours): largest charge 1; by L: 2: 1, 8: 1
   (8, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4, 6: 2, 7: 2, 8: 2
O_6 without a vertex: U* = 19
   (-5, 0, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 4
   (0, -5, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 2
   (0, 0, -5) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 2
   (0, 0, 5) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 2
   (0, 5, 0) (vertex of an octahedron): largest charge 4; by L: 2: 4, 3: 4, 4: 4, 5: 2
   (4, -1, 0) (6 empty neighbours): largest charge 1; by L: 3: 1, 4: 1, 5: 1
   (4, 0, -1) (6 empty neighbours): largest charge 1; by L: 3: 1, 4: 1, 5: 1
   (4, 0, 1) (6 empty neighbours): largest charge 1; by L: 3: 1, 4: 1, 5: 1
   (4, 1, 0) (6 empty neighbours): largest charge 1; by L: 3: 1, 4: 1, 5: 1
```

## Output of `python3 asearch.py`: `1 1200 3 octa`, `2 1200 3 near`, `3 900 3 islands`, `4 900 4 unions`, `5 1000 3 steps`, `6 1200 8 octa`, `7 900 6 islands`

```
O_5: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 4 (N = 84, U* = 19, a_max = 24); violations found: 0
O_6: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 4 (N = 145, U* = 19, a_max = 24); violations found: 0
O_7: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 4 (N = 230, U* = 19, a_max = 24); violations found: 0
O_6 without a vertex: start 4U* - 3 a_max = 4; least value reached on a body that is not a regular octahedron: 4 (N = 145, U* = 19, a_max = 24); violations found: 0
O_6 with a site on a face: start 4U* - 3 a_max = 24; least value reached on a body that is not a regular octahedron: 4 (N = 145, U* = 19, a_max = 24); violations found: 0
O_7 without two vertices: start 4U* - 3 a_max = 8; least value reached on a body that is not a regular octahedron: 4 (N = 230, U* = 19, a_max = 24); violations found: 0
O_9 with island 3 at (1,2): start 4U* - 3 a_max = 3; least value reached on a body that is not a regular octahedron: 3 (N = 495, U* = 21, a_max = 27); violations found: 0
O_9 with island 3 at (0,2): start 4U* - 3 a_max = 3; least value reached on a body that is not a regular octahedron: 3 (N = 495, U* = 21, a_max = 27); violations found: 0
O_7 with island 3 at (0,1): start 4U* - 3 a_max = 9; least value reached on a body that is not a regular octahedron: 9 (N = 237, U* = 21, a_max = 25); violations found: 0
O_6 u O_6+(7, 3, 2): start 4U* - 3 a_max = 82; least value reached on a body that is not a regular octahedron: 82 (N = 292, U* = 52, a_max = 42); violations found: 0
O_6 u O_6+(7, 2, 1): start 4U* - 3 a_max = 72; least value reached on a body that is not a regular octahedron: 72 (N = 286, U* = 48, a_max = 40); violations found: 0
O_6 u O_6+(6, 4, 0): start 4U* - 3 a_max = 104; least value reached on a body that is not a regular octahedron: 92 (N = 286, U* = 53, a_max = 40); violations found: 0
O_6 u O_6+(7, 1, 0): start 4U* - 3 a_max = 80; least value reached on a body that is not a regular octahedron: 80 (N = 282, U* = 50, a_max = 40); violations found: 0
O_6 u O_6+(5, 5, 0): start 4U* - 3 a_max = 88; least value reached on a body that is not a regular octahedron: 88 (N = 286, U* = 52, a_max = 40); violations found: 0
O_6 u O_6+(5, 3, 2): start 4U* - 3 a_max = 106; least value reached on a body that is not a regular octahedron: 69 (N = 280, U* = 42, a_max = 33); violations found: 0
O_7 u O_7+(2,2,2): start 4U* - 3 a_max = 6; least value reached on a body that is not a regular octahedron: 6 (N = 358, U* = 24, a_max = 30); violations found: 0
O_7 u O_7+(1,1,0): start 4U* - 3 a_max = 8; least value reached on a body that is not a regular octahedron: 8 (N = 280, U* = 20, a_max = 24); violations found: 0
O_5 u O_8+(2,2,1): start 4U* - 3 a_max = 12; least value reached on a body that is not a regular octahedron: 12 (N = 359, U* = 21, a_max = 24); violations found: 0
O_5: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 4 (N = 84, U* = 19, a_max = 24); violations found: 0
O_6: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 4 (N = 145, U* = 19, a_max = 24); violations found: 0
O_7: start 4U* - 3 a_max = 0; least value reached on a body that is not a regular octahedron: 24 (N = 232, U* = 24, a_max = 24); violations found: 0
O_9 with island 3 at (1,2): start 4U* - 3 a_max = 3; least value reached on a body that is not a regular octahedron: 3 (N = 495, U* = 21, a_max = 27); violations found: 0
O_9 with island 3 at (0,2): start 4U* - 3 a_max = 3; least value reached on a body that is not a regular octahedron: 3 (N = 495, U* = 21, a_max = 27); violations found: 0
O_7 with island 3 at (0,1): start 4U* - 3 a_max = 9; least value reached on a body that is not a regular octahedron: 9 (N = 237, U* = 21, a_max = 25); violations found: 0
```

## Output of `python3 fans.py named`

```
pair: U* = 26, shape-irregular sites 2, fans 0 {}, 4U* - 3 fans = 104, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
O_2: U* = 42, shape-irregular sites 6, fans 0 {}, 4U* - 3 fans = 168, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
O_3: U* = 54, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 144, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_4: U* = 42, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 96, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_5: U* = 18, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 0, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_6: U* = 18, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 0, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_7: U* = 18, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 0, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_8: U* = 18, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 0, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_9: U* = 18, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 0, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
tetra 4: U* = 60, shape-irregular sites 16, fans 0 {}, 4U* - 3 fans = 240, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
tetra 6: U* = 60, shape-irregular sites 28, fans 0 {}, 4U* - 3 fans = 240, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
tetra 9: U* = 78, shape-irregular sites 46, fans 0 {}, 4U* - 3 fans = 312, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
rod: U* = 114, shape-irregular sites 10, fans 0 {}, 4U* - 3 fans = 456, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
layer: U* = 195, shape-irregular sites 37, fans 0 {}, 4U* - 3 fans = 780, weighted fans (n = 6, 12, 24, 48): 0.00, 0.00, 0.00, 0.00
O_6 without a vertex: U* = 19, shape-irregular sites 9, fans 24 {'tip, apex': 20, 'two roots': 4}, 4U* - 3 fans = 4, weighted fans (n = 6, 12, 24, 48): 15.67, 19.58, 21.73, 22.85
O_6 with a site on a face: U* = 24, shape-irregular sites 10, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 24, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_7 u O_7+(2,2,2): U* = 24, shape-irregular sites 18, fans 30 {'tip, apex': 24, 'tip, other': 6}, 4U* - 3 fans = 6, weighted fans (n = 6, 12, 24, 48): 20.83, 25.21, 27.55, 28.76
O_7 u O_7+(1,1,0): U* = 20, shape-irregular sites 8, fans 24 {'tip, apex': 16, 'tip, other': 4, 'two roots': 4}, 4U* - 3 fans = 8, weighted fans (n = 6, 12, 24, 48): 15.67, 19.58, 21.73, 22.85
O_7 u O_7+(2,0,0): U* = 42, shape-irregular sites 14, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 96, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_7 u O_7+(4,0,0): U* = 54, shape-irregular sites 14, fans 48 {'tip, apex': 40, 'two roots': 8}, 4U* - 3 fans = 72, weighted fans (n = 6, 12, 24, 48): 28.00, 36.33, 41.75, 44.77
two O_5 and a site: U* = 43, shape-irregular sites 13, fans 48 {'tip, apex': 40, 'tip, other': 8}, 4U* - 3 fans = 28, weighted fans (n = 6, 12, 24, 48): 33.33, 40.33, 44.08, 46.02
two O_6 vertex to vertex: U* = 44, shape-irregular sites 12, fans 48 {'tip, apex': 40, 'tip, other': 8}, 4U* - 3 fans = 32, weighted fans (n = 6, 12, 24, 48): 33.33, 40.33, 44.08, 46.02
two O_7 tip to tip: U* = 51, shape-irregular sites 11, fans 48 {'tip, apex': 40, 'tip, other': 8}, 4U* - 3 fans = 60, weighted fans (n = 6, 12, 24, 48): 33.33, 40.33, 44.08, 46.02
O_9 with island 3 at (1,2): U* = 21, shape-irregular sites 12, fans 27 {'tip, apex': 24, 'tip, other': 3}, 4U* - 3 fans = 3, weighted fans (n = 6, 12, 24, 48): 18.75, 22.69, 24.80, 25.89
O_9 with island 5 at (1,1): U* = 21, shape-irregular sites 12, fans 27 {'tip, apex': 24, 'tip, other': 3}, 4U* - 3 fans = 3, weighted fans (n = 6, 12, 24, 48): 18.75, 22.69, 24.80, 25.89
O_13 with island 6 at (2,2): U* = 21, shape-irregular sites 12, fans 27 {'tip, apex': 24, 'tip, other': 3}, 4U* - 3 fans = 3, weighted fans (n = 6, 12, 24, 48): 18.75, 22.69, 24.80, 25.89
O_9 with reversed island 3: U* = 33, shape-irregular sites 21, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 60, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_9 with a cavity O_3: U* = 126, shape-irregular sites 6, fans 24 {'tip, apex': 24}, 4U* - 3 fans = 432, weighted fans (n = 6, 12, 24, 48): 16.67, 20.17, 22.04, 23.01
O_8 and O_4 on a vertex: U* = 54, shape-irregular sites 14, fans 48 {'tip, apex': 40, 'two roots': 8}, 4U* - 3 fans = 72, weighted fans (n = 6, 12, 24, 48): 31.33, 39.17, 43.46, 45.70
O_8 and O_4 on a face: U* = 60, shape-irregular sites 30, fans 39 {'tip, apex': 36, 'tip, other': 3}, 4U* - 3 fans = 123, weighted fans (n = 6, 12, 24, 48): 27.08, 32.77, 35.82, 37.39
```

## Output of `python3 fans.py`: `unions 7 7`, `unions 5 8`, `near 5`, `near 6`, `near 7`, `islands 9`, `bridge 5`, `roof 6 5`

```
unions O_7, O_7+v: 79 bodies; fans by root {'inner root': 36, 'one root': 300, 'tip, apex': 2812, 'tip, other': 116, 'two roots': 106}; fans without a root: 0; least 4U* - 3 fans = 6 ((2, 2, 2), U* = 24, fans 30); least 4U* - 3 (weighted fans) = 9.71 ((2, 2, 2), U* = 24)
unions O_5, O_8+v: 61 bodies; fans by root {'inner root': 26, 'one root': 198, 'tip, apex': 2127, 'tip, other': 99, 'two roots': 76}; fans without a root: 0; least 4U* - 3 fans = -9 ((3, 1, 1), U* = 21, fans 31); least 4U* - 3 (weighted fans) = -2.47 ((3, 1, 1), U* = 21)
bodies at one site from O_5: 206 bodies; fans by root {'one root': 336, 'tip, apex': 4368, 'tip, other': 120, 'two roots': 72}; fans without a root: 0; least 4U* - 3 fans = 4 ((-4, 0, 0), U* = 19, fans 24); least 4U* - 3 (weighted fans) = 7.45 ((-4, 0, 0), U* = 19)
bodies at one site from O_6: 294 bodies; fans by root {'one root': 384, 'tip, apex': 6480, 'tip, other': 120, 'two roots': 72}; fans without a root: 0; least 4U* - 3 fans = 4 ((-5, 0, 0), U* = 19, fans 24); least 4U* - 3 (weighted fans) = 7.45 ((-5, 0, 0), U* = 19)
bodies at one site from O_7: 398 bodies; fans by root {'one root': 384, 'tip, apex': 8976, 'tip, other': 120, 'two roots': 72}; fans without a root: 0; least 4U* - 3 fans = 4 ((-6, 0, 0), U* = 19, fans 24); least 4U* - 3 (weighted fans) = 7.45 ((-6, 0, 0), U* = 19)
islands on a face of O_9: 110 bodies; fans by root {'inner root': 2, 'one root': 120, 'tip, apex': 2506, 'tip, other': 121, 'two roots': 40}; fans without a root: 0; least 4U* - 3 fans = -9 ((True, 3, 0, 0), U* = 21, fans 31); least 4U* - 3 (weighted fans) = -2.48 ((True, 3, 0, 0), U* = 21)
two O_5 joined by one site: 146 bodies; fans by root {'one root': 352, 'tip, apex': 6308, 'tip, other': 314, 'two roots': 34}; fans without a root: 0; least 4U* - 3 fans = 28 (((10, 1, 1), (5, 1, 0)), U* = 43, fans 48); least 4U* - 3 (weighted fans) = 33.94 (((10, 1, 1), (5, 1, 0)), U* = 43)
roof O_6 over two legs O_5: 92 bodies; fans by root {'inner root': 36, 'one root': 504, 'tip, apex': 4176, 'tip, other': 240, 'two roots': 252}; fans without a root: 0; least 4U* - 3 fans = 64 ((10, 0, 1), U* = 70, fans 72); least 4U* - 3 (weighted fans) = 72.91 ((10, 0, 1), U* = 70)
```

## Output of `python3 sources.py named`

```
single site: U* = 15, runs 24; sigma_1 = 24 (4U* - 3 sigma = -12, jogs 0); sigma_2 = 24 (4U* - 3 sigma = -12, jogs 0); sigma_3 = 24 (4U* - 3 sigma = -12, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
pair: U* = 26, runs 32; sigma_1 = 24 (4U* - 3 sigma = 32, jogs 8); sigma_2 = 24 (4U* - 3 sigma = 32, jogs 8); sigma_3 = 24 (4U* - 3 sigma = 32, jogs 8); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
O_2: U* = 42, runs 48; sigma_1 = 24 (4U* - 3 sigma = 96, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 96, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 96, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_3: U* = 54, runs 72; sigma_1 = 24 (4U* - 3 sigma = 144, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 144, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 144, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_4: U* = 42, runs 96; sigma_1 = 24 (4U* - 3 sigma = 96, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 96, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 96, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_5: U* = 18, runs 120; sigma_1 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 0, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_6: U* = 18, runs 144; sigma_1 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 0, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_7: U* = 18, runs 168; sigma_1 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 0, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_8: U* = 18, runs 192; sigma_1 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 0, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_9: U* = 18, runs 216; sigma_1 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 0, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 0, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
tetra 4: U* = 60, runs 60; sigma_1 = 60 (4U* - 3 sigma = 60, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 168, jogs 72); sigma_3 = 24 (4U* - 3 sigma = 168, jogs 72); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]
tetra 6: U* = 60, runs 84; sigma_1 = 84 (4U* - 3 sigma = -12, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 168, jogs 120); sigma_3 = 24 (4U* - 3 sigma = 168, jogs 120); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]
tetra 9: U* = 78, runs 120; sigma_1 = 120 (4U* - 3 sigma = -48, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 240, jogs 192); sigma_3 = 24 (4U* - 3 sigma = 240, jogs 192); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]
rod: U* = 114, runs 96; sigma_1 = 24 (4U* - 3 sigma = 384, jogs 72); sigma_2 = 24 (4U* - 3 sigma = 384, jogs 72); sigma_3 = 24 (4U* - 3 sigma = 384, jogs 72); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 10, 10, 10]
layer: U* = 195, runs 96; sigma_1 = 42 (4U* - 3 sigma = 654, jogs 36); sigma_2 = 24 (4U* - 3 sigma = 708, jogs 72); sigma_3 = 24 (4U* - 3 sigma = 708, jogs 72); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]
O_6 without a vertex: U* = 19, runs 140; sigma_1 = 24 (4U* - 3 sigma = 4, jogs 8); sigma_2 = 24 (4U* - 3 sigma = 4, jogs 8); sigma_3 = 24 (4U* - 3 sigma = 4, jogs 8); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
O_6 with a site on a face: U* = 24, runs 144; sigma_1 = 33 (4U* - 3 sigma = -3, jogs 0); sigma_2 = 33 (4U* - 3 sigma = -3, jogs 0); sigma_3 = 33 (4U* - 3 sigma = -3, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 6]
O_7 u O_7+(2,2,2): U* = 24, runs 192; sigma_1 = 42 (4U* - 3 sigma = -30, jogs 0); sigma_2 = 42 (4U* - 3 sigma = -30, jogs 0); sigma_3 = 42 (4U* - 3 sigma = -30, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]
O_7 u O_7+(1,1,0): U* = 20, runs 176; sigma_1 = 24 (4U* - 3 sigma = 8, jogs 8); sigma_2 = 24 (4U* - 3 sigma = 8, jogs 8); sigma_3 = 24 (4U* - 3 sigma = 8, jogs 8); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
O_7 u O_7+(2,0,0): U* = 42, runs 192; sigma_1 = 48 (4U* - 3 sigma = 24, jogs 0); sigma_2 = 48 (4U* - 3 sigma = 24, jogs 0); sigma_3 = 48 (4U* - 3 sigma = 24, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7]
O_7 u O_7+(4,0,0): U* = 54, runs 216; sigma_1 = 48 (4U* - 3 sigma = 72, jogs 0); sigma_2 = 48 (4U* - 3 sigma = 72, jogs 0); sigma_3 = 48 (4U* - 3 sigma = 72, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6]
two O_5 and a site: U* = 43, runs 232; sigma_1 = 52 (4U* - 3 sigma = 16, jogs 2); sigma_2 = 52 (4U* - 3 sigma = 16, jogs 2); sigma_3 = 52 (4U* - 3 sigma = 16, jogs 2); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
two O_6 vertex to vertex: U* = 44, runs 272; sigma_1 = 48 (4U* - 3 sigma = 32, jogs 0); sigma_2 = 48 (4U* - 3 sigma = 32, jogs 0); sigma_3 = 48 (4U* - 3 sigma = 32, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
two O_7 tip to tip: U* = 51, runs 312; sigma_1 = 48 (4U* - 3 sigma = 60, jogs 0); sigma_2 = 48 (4U* - 3 sigma = 60, jogs 0); sigma_3 = 48 (4U* - 3 sigma = 60, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]
O_9 with island 3 at (0,0): U* = 21, runs 216; sigma_1 = 30 (4U* - 3 sigma = -6, jogs 4); sigma_2 = 30 (4U* - 3 sigma = -6, jogs 4); sigma_3 = 30 (4U* - 3 sigma = -6, jogs 4); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5]
O_9 with island 3 at (1,2): U* = 21, runs 216; sigma_1 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_2 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_3 = 33 (4U* - 3 sigma = -15, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8, 8, 9]
O_9 with island 5 at (1,1): U* = 21, runs 216; sigma_1 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_2 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_3 = 33 (4U* - 3 sigma = -15, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5, 9, 9, 9]
O_13 with island 6 at (2,2): U* = 21, runs 312; sigma_1 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_2 = 33 (4U* - 3 sigma = -15, jogs 0); sigma_3 = 33 (4U* - 3 sigma = -15, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 12, 12, 12]
O_9 with reversed island 3: U* = 33, runs 216; sigma_1 = 39 (4U* - 3 sigma = 15, jogs 0); sigma_2 = 33 (4U* - 3 sigma = 33, jogs 12); sigma_3 = 33 (4U* - 3 sigma = 33, jogs 12); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 9, 9, 9]
O_5 u O_8+(3,1,1): U* = 21, runs 192; sigma_1 = 30 (4U* - 3 sigma = -6, jogs 4); sigma_2 = 30 (4U* - 3 sigma = -6, jogs 4); sigma_3 = 30 (4U* - 3 sigma = -6, jogs 4); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 5, 7]
O_9 with a cavity O_3: U* = 126, runs 216; sigma_1 = 24 (4U* - 3 sigma = 432, jogs 0); sigma_2 = 24 (4U* - 3 sigma = 432, jogs 0); sigma_3 = 24 (4U* - 3 sigma = 432, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
O_8 and O_4 on a vertex: U* = 54, runs 240; sigma_1 = 48 (4U* - 3 sigma = 72, jogs 0); sigma_2 = 48 (4U* - 3 sigma = 72, jogs 0); sigma_3 = 48 (4U* - 3 sigma = 72, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3]
O_8 and O_4 on a face: U* = 60, runs 228; sigma_1 = 45 (4U* - 3 sigma = 105, jogs 0); sigma_2 = 45 (4U* - 3 sigma = 105, jogs 0); sigma_3 = 45 (4U* - 3 sigma = 105, jogs 0); sources without an irregular site next to them: 0; lengths of the sources (J = 2): [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 5]
```

## Output of `python3 endsrc.py named`

```
single site: U* = 15, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 120; end-sources by length of chord: {}
pair: U* = 26, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 208; end-sources by length of chord: {}
O_2: U* = 42, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 336; end-sources by length of chord: {}
O_3: U* = 54, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 288; end-sources by length of chord: {2: 48}
O_4: U* = 42, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 192; end-sources by length of chord: {2: 48}
O_5: U* = 18, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 0; end-sources by length of chord: {2: 48}
O_6: U* = 18, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 0; end-sources by length of chord: {2: 48}
O_7: U* = 18, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 0; end-sources by length of chord: {2: 48}
O_8: U* = 18, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 0; end-sources by length of chord: {2: 48}
O_9: U* = 18, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 0; end-sources by length of chord: {2: 48}
tetra 4: U* = 60, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 480; end-sources by length of chord: {}
tetra 6: U* = 60, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 480; end-sources by length of chord: {}
tetra 9: U* = 78, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 624; end-sources by length of chord: {}
rod: U* = 114, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 912; end-sources by length of chord: {}
layer: U* = 195, Sigma = 0 (first ends 0, breaks 0), 8U* - 3 Sigma = 1560; end-sources by length of chord: {}
O_6 without a vertex: U* = 19, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 8; end-sources by length of chord: {2: 40, 3: 8}
O_6 with a site on a face: U* = 24, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 48; end-sources by length of chord: {2: 48}
O_7 u O_7+(2,2,2): U* = 24, Sigma = 60 (first ends 60, breaks 0), 8U* - 3 Sigma = 12; end-sources by length of chord: {2: 60}
O_7 u O_7+(1,1,0): U* = 20, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 16; end-sources by length of chord: {2: 40, 3: 8}
O_7 u O_7+(2,0,0): U* = 42, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 192; end-sources by length of chord: {2: 48}
O_7 u O_7+(4,0,0): U* = 54, Sigma = 96 (first ends 96, breaks 0), 8U* - 3 Sigma = 144; end-sources by length of chord: {2: 80, 6: 16}
two O_5 and a site: U* = 43, Sigma = 96 (first ends 96, breaks 0), 8U* - 3 Sigma = 56; end-sources by length of chord: {2: 96}
two O_6 vertex to vertex: U* = 44, Sigma = 96 (first ends 96, breaks 0), 8U* - 3 Sigma = 64; end-sources by length of chord: {2: 96}
two O_7 tip to tip: U* = 51, Sigma = 96 (first ends 96, breaks 0), 8U* - 3 Sigma = 120; end-sources by length of chord: {2: 96}
O_9 with island 3 at (0,0): U* = 21, Sigma = 60 (first ends 58, breaks 2), 8U* - 3 Sigma = -12; end-sources by length of chord: {2: 48, 3: 4, 4: 2, 5: 4, 8: 2}
O_9 with island 3 at (1,2): U* = 21, Sigma = 54 (first ends 54, breaks 0), 8U* - 3 Sigma = 6; end-sources by length of chord: {2: 54}
O_9 with island 5 at (1,1): U* = 21, Sigma = 54 (first ends 54, breaks 0), 8U* - 3 Sigma = 6; end-sources by length of chord: {2: 54}
O_13 with island 6 at (2,2): U* = 21, Sigma = 54 (first ends 54, breaks 0), 8U* - 3 Sigma = 6; end-sources by length of chord: {2: 54}
O_9 with reversed island 3: U* = 33, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 120; end-sources by length of chord: {2: 48}
O_5 u O_8+(3,1,1): U* = 21, Sigma = 60 (first ends 58, breaks 2), 8U* - 3 Sigma = -12; end-sources by length of chord: {2: 48, 3: 4, 5: 2, 6: 2, 7: 4}
O_9 with a cavity O_3: U* = 126, Sigma = 48 (first ends 48, breaks 0), 8U* - 3 Sigma = 864; end-sources by length of chord: {2: 48}
O_8 and O_4 on a vertex: U* = 54, Sigma = 96 (first ends 96, breaks 0), 8U* - 3 Sigma = 144; end-sources by length of chord: {2: 80, 3: 16}
O_8 and O_4 on a face: U* = 60, Sigma = 90 (first ends 84, breaks 6), 8U* - 3 Sigma = 210; end-sources by length of chord: {2: 78, 5: 6, 6: 6}
```
