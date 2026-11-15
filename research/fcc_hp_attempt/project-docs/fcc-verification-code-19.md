# FCC HP folding: verification code, part 19 (twenty-second pass, 15 Nov 2026)

Scripts for Section 45 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the linear inequality (L_n), which implies soundness (Proposition 62); silhouette runs, the pointwise inequality of Lemma 63 and the identity of Proposition 64; the counts (M_n) and (K); statements that turned out false; and the smallest violators of G_chi. They import `gmin.py`, `psi.py` (part 16), `tops.py` (part 17) and `euler.py` (part 18). Apart from `chordB.py` (the enumeration behind Lemma 63) and `algebra62.py` (the arithmetic of Proposition 62), nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `lin.py` | Lam_n, its least value over n, the discriminant D; octahedra, unions, bodies at one site, bridged pairs | `python3 lin.py families`, `near r`, `bridge r` |
| `lintest.py` | Lam_n and the largest n with M_n < 0 on special bodies, roofs, pairs joined by two sites, bodies at two sites | `python3 lintest.py special`, `roof N n`, `bridge2 r`, `near2 r` |
| `linsearch.py` | annealing against (L_n) | `python3 linsearch.py seed steps T0 kind` |
| `dscan.py` | the discriminant form on 1,790 bodies | `python3 dscan.py` |
| `algebra62.py` | the identities of Proposition 62 and the two other forms of M_n | `python3 algebra62.py` |
| `chords.py` | chords and silhouette runs; three statements of which (A) is false | `python3 chords.py` |
| `chordB.py` | Lemma 63: 12 e - 4 deg <= o for all 4,096 neighbourhoods | `python3 chordB.py` |
| `chordM.py` | M_n and the identity Lam_n = M_n + 3B + 3D_n+ | `python3 chordM.py families` |
| `chordM2.py` | the largest n with M_n < 0, by family | `python3 chordM2.py families`, `unions a b`, `near r`, `bridge r` |
| `steps.py` | (M_n) for O_9 with small translates | `python3 steps.py 9` |
| `slopes.py` | the count of slopes (false, Section 45.6) | `python3 slopes.py families` |
| `msearch.py` | (K) on unions and bodies at one site; annealing against (M_n), n >= 6 | `python3 msearch.py K`, `python3 msearch.py anneal seed steps T0` |
| `minviol.py` | smallest violators of G_chi | `python3 minviol.py 1 0.5 3000 6` |

## `lin.py`

```python
"""Section 45 of the note: the linear inequality (L_n).
For a finite set S with boundary d, matching numbers nu1, nu2 (gmin.cost) put
    U* = 2d - 3(nu1 + nu2),   Y = 2(d - 2 nu1 - nu2)  (= n2* + U*),
    Lam_n(S) = (4n^2 - 9n + 3) d - 3n((2n - 6) nu1 + (2n - 3) nu2) = 2 U* n^2 - (9/2) Y n + 3 d.
Lam_n is the least value, over the decorations of S, of ((4n^2 - 9n + 3) U + 18 n1 - 9 (n - 3) n2) / 2.
(L_n): Lam_n(S) >= 0 for every finite S.  For O_r it is 36 (n - r)^2.
D(S) = 32 U* d - 27 Y^2 >= 0 is the same for all real n at once.
    python3 lin.py families          octahedra, tetrahedra, the unions of two octahedra of Section 42
    python3 lin.py near n            bodies at one site from O_n
    python3 lin.py bridge n          two copies of O_n joined by one site
"""
import sys, math
from gmin import *

def parts(c):
    d, a, b = c['boundary'], c['nu1'], c['nu2']
    return d, 2 * d - 3 * (a + b), 2 * (d - 2 * a - b)

def lam(c, n):
    d, a, b = c['boundary'], c['nu1'], c['nu2']
    return (4 * n * n - 9 * n + 3) * d - 3 * n * ((2 * n - 6) * a + (2 * n - 3) * b)

def disc(c):
    d, U, Y = parts(c); return 32 * U * d - 27 * Y * Y

def minlam(c, nmin=3):
    """least Lam_n over integers n >= nmin, and the n"""
    d, U, Y = parts(c)
    v = 9 * Y / (8 * U) if U > 0 else nmin
    cand = {nmin, max(nmin, math.floor(v)), max(nmin, math.ceil(v))}
    return min((lam(c, n), n) for n in cand)

def report(name, S):
    c = cost(S); d, U, Y = parts(c); m, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {U}, n2* = {c['n2']}, boundary = {d}, D = {disc(c)}, least Lam_n = {m} at n = {n}")
    return m

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'families':
        for r in range(5, 11):
            c = cost(octa(r)); assert all(lam(c, n) == 36 * (n - r) ** 2 for n in range(3, 40)), r
        print("O_r, r = 5..10: Lam_n = 36 (n - r)^2 for n = 3..39")
        for r in (2, 3, 4): report(f"O_{r}", octa(r))
        report("single site", {(0, 0, 0)}); report("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for k in (4, 6, 9, 12): report(f"tetrahedron {k}", tetra(k))
        from psi import unions
        for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
            worst = None; cnt = 0; neg = 0
            for v, ov, S in unions(a, b):
                c = cost(S); m, n = minlam(c); cnt += 1; neg += m < 0
                if worst is None or m < worst[0]: worst = (m, n, v, parts(c)[1], disc(c))
            print(f"unions O_{a}, O_{b}+v: {cnt} bodies, with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (v = {worst[2]}, U* = {worst[3]}, D = {worst[4]})")
    if mode == 'near':
        from psi import boundary_moves, toggle
        r = int(sys.argv[2]); S = octa(r); worst = None; cnt = 0; neg = 0
        for h in sorted(boundary_moves(S)):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            c = cost(T); m, n = minlam(c); cnt += 1; neg += m < 0
            if worst is None or m < worst[0]: worst = (m, n, h, parts(c)[1], c['n2'], disc(c))
        print(f"O_{r}: {cnt} bodies at one site; with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (site {worst[2]}, U* = {worst[3]}, n2* = {worst[4]}, D = {worst[5]})")
    if mode == 'bridge':
        r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A; worst = None; cnt = 0; neg = 0
        for x in range(0, 2 * r + 5):
            for y in range(0, x + 1):
                for z in range(0, y + 1):
                    if (x + y + z) % 2: continue
                    B = octa(r, (x, y, z))
                    if A & B or coatA & B: continue
                    coatB = {add(h, s) for h in B for s in ROOTS} - B
                    for g in coatA & coatB:
                        S = A | B | {g}; c = cost(S); m, n = minlam(c); cnt += 1; neg += m < 0
                        if worst is None or m < worst[0]: worst = (m, n, (x, y, z), g, parts(c)[1], c['n2'], disc(c))
        print(f"two O_{r} joined by one site: {cnt} bodies; with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (v = {worst[2]}, site {worst[3]}, U* = {worst[4]}, n2* = {worst[5]}, D = {worst[6]})")
```

## `lintest.py`

```python
"""Section 45: (L_n) and (M_n) on the remaining families of Sections 42 to 44.
For every body: the least Lam_n over n >= 3 (lin.py) and the largest n with M_n < 0 (chordM.py).
    python3 lintest.py special | roof N n | bridge2 r | near2 r"""
import sys, itertools
from gmin import *
from lin import minlam
from chordM import data, M
from psi import boundary_moves, toggle
def both(S):
    c, oo = data(S); top = (max(oo) if oo else 3) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    return minlam(c), (max(bad) if bad else 0), c
def scan(name, bodies, verbose=False):
    cnt = 0; neg = 0; low = None; hist = {}
    for tag, S in bodies:
        (m, n), b, c = both(S); cnt += 1; neg += m < 0; hist[b] = hist.get(b, 0) + 1
        if verbose: print(f"   {tag}: N = {len(S)}, U* = {c['U']}, least Lam_n = {m} at n = {n}; largest n with M_n < 0: {b}")
        if low is None or m < low[0]: low = (m, n, tag, c['U'])
    print(f"{name}: {cnt} bodies; with Lam_n < 0: {neg}; least Lam_n = {low[0]} at n = {low[1]} ({low[2]}, U* = {low[3]}); largest n with M_n < 0, by number of bodies: {dict(sorted(hist.items()))}", flush=True)
mode = sys.argv[1]
if mode == 'special':
    sp = [("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
          ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
          ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
          ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
          ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
          ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
          ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}),
          ("O_7 with twin tops (2,0,0)", octa(7) | octa(7, (2, 0, 0)))]
    scan("special bodies", sp, True)
if mode == 'roof':
    N, n = int(sys.argv[2]), int(sys.argv[3]); A = octa(N)
    def gen():
        for a in range(0, N + n + 1):
            for b in range(0, 3):
                for c in range(0, N + n + 1):
                    if (a + b + c - (N - n)) % 2: continue
                    B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); S = A | B1 | B2
                    if not connected(S): continue
                    if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue
                    yield (a, b, c), S
    scan(f"roof O_{N} over two legs O_{n}", gen())
if mode == 'bridge2':
    r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A
    def gen():
        for x in range(0, 2 * r + 5):
            for y in range(0, x + 1):
                for z in range(0, y + 1):
                    if (x + y + z) % 2: continue
                    B = octa(r, (x, y, z))
                    if A & B or coatA & B: continue
                    coatB = {add(h, s) for h in B for s in ROOTS} - B; one = coatA & coatB
                    for c1 in coatA - B:
                        for s in ROOTS:
                            c2 = add(c1, s)
                            if c2 in coatB - A and c1 not in one and c2 not in one: yield ((x, y, z), c1, c2), A | B | {c1, c2}
    scan(f"two O_{r} joined by two sites", gen())
if mode == 'near2':
    r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
    def gen():
        for h, g in itertools.combinations(mv, 2):
            T = toggle(toggle(S, h), g)
            if connected(T): yield (h, g), T
    scan(f"bodies at two sites from O_{r}", gen())
```

## `linsearch.py`

```python
"""Section 45 of the note: search for a finite set with Lam_n < 0 (see lin.py).
Score g(S) = (least Lam_n(S) over integers n >= 3) / boundary(S); g = 0 for the regular octahedra O_r, r >= 5.
Annealing by single sites (any surface site may go, any coat site may come, the body stays connected), then descent.
    python3 linsearch.py seed steps T0 kind      kind: octa | unions a | blobs | twin | bridge"""
import sys, random, math
from gmin import *
from lin import minlam, parts, disc
from psi import boundary_moves, toggle, unions
def g(S):
    c = cost(S); return minlam(c)[0] / c['boundary']
def run(S, steps, T0, rng):
    cur = g(S); best = (cur, set(S)); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.005
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = g(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur < best[0]: best = (cur, set(S))
    S = best[1]; cur = best[0]
    while True:                                   # descent
        mv = boundary_moves(S); rng.shuffle(mv); done = True
        for h in mv:
            S2 = toggle(S, h)
            if len(S2) < 2 or (h in S and not connected(S2)): continue
            u = g(S2)
            if u < cur - 1e-12: S, cur, done = S2, u, False; break
        if done: break
    return cur, S
seed = int(sys.argv[1]); steps = int(sys.argv[2]); T0 = float(sys.argv[3]); kind = sys.argv[4]; rng = random.Random(seed)
starts = []
if kind == 'octa': starts = [(f"O_{r}", octa(r)) for r in (5, 6, 7)]
if kind == 'unions':
    a = int(sys.argv[5]); U = list(unions(a, a)); rng.shuffle(U); starts = [(f"O_{a} u O_{a}+{v}", S) for v, ov, S in U[:int(sys.argv[6])]]
if kind == 'twin': starts = [("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_6 u O_6+(1,1,0)", octa(6) | octa(6, (1, 1, 0))), ("O_6 u O_6+(2,2,2)", octa(6) | octa(6, (2, 2, 2)))]
if kind == 'bridge': starts = [("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)}), ("two O_5 vertex to vertex", octa(5) | octa(5, (9, 1, 0)))]
if kind == 'blobs':
    for t in range(int(sys.argv[5])):
        S = {(0, 0, 0)}
        while len(S) < rng.choice((40, 80, 150)):
            h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
        starts.append((f"blob {t}", S))
low = None
for name, S in starts:
    g0 = g(S); val, B = run(S, steps, T0, rng); c = cost(B); d, U, Y = parts(c); m, n = minlam(c)
    print(f"{name}: g {g0:.4f} -> {val:.4f}; end N = {len(B)}, U* = {U}, n2* = {c['n2']}, least Lam_n = {m} at n = {n}, D = {disc(c)}", flush=True)
    if low is None or val < low[0]: low = (val, name, sorted(B))
print("LEAST g", low[0], low[1])
if low[0] < 0: print("VIOLATION", low[2])
```

## `dscan.py`

```python
"""Section 45: the discriminant D = 32 U* d - 27 (n2* + U*)^2 (lin.py) on the unions of two octahedra and the bodies at one site from O_r."""
from gmin import *
from lin import disc, parts
from psi import unions, boundary_moves, toggle
low = None; cnt = 0; neg = 0
def take(tag, S):
    global low, cnt, neg
    c = cost(S); D = disc(c); cnt += 1; neg += D < 0
    if D > 0 and (low is None or D < low[0]): low = (D, tag, parts(c)[1])
for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
    for v, ov, S in unions(a, b): take((a, b, v), S)
for r in (5, 6, 7, 8):
    S = octa(r)
    for h in sorted(boundary_moves(S)):
        T = toggle(S, h)
        if h in S and not connected(T): continue
        take((r, h), T)
print(f"{cnt} bodies; with D < 0: {neg}; least D = {low[0]} ({low[1]}, U* = {low[2]})")
```

## `algebra62.py`

```python
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
```

## `chords.py`

```python
"""Section 45 of the note: chords of faces.
For nu in {+1,-1}^3 let R_nu be the three roots r with r.nu = 2.  A site h of S is nu-exposed if h + r is empty for the
three r in R_nu.  A chord is a maximal run of nu-exposed sites on a lattice line with direction d, d.nu = 0 (three
directions for each nu).  An end of a chord is open if the next site of the line is empty, and blocked if it is in S.
H = number of chords with two open ends, H_j = number of those with at most j sites, kappa = max_j H_j / j,
Len = their total number of sites.  Statements tested (U*, nu1, nu2, boundary d from gmin.cost):
    (A)  d - 3 nu2 + H >= (3/2) kappa        (K)  U* >= (3/4) kappa        (B)  Len - H/2 <= d
(A) and (K) together would give Lam_n >= 0 for n >= 3, but (A) is false (Section 45.6).  (B) is Lemma 63 (chordB.py).
(K) is open.     python3 chords.py"""
import sys, itertools
from fractions import Fraction
from gmin import *
NUS = list(itertools.product((1, -1), repeat=3))
dot = lambda a, b: a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
RNU = {nu: [r for r in ROOTS if dot(r, nu) == 2] for nu in NUS}
DNU = {nu: [r for r in ROOTS if dot(r, nu) == 0 and r > (0, 0, 0)] for nu in NUS}
sub = lambda a, b: (a[0] - b[0], a[1] - b[1], a[2] - b[2])

def chords(S):
    """list of (nu, d, first site, length, open ends)"""
    out = []
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        for d in DNU[nu]:
            for h in F:
                if sub(h, d) in F: continue
                L = 1; g = add(h, d)
                while g in F: L += 1; g = add(g, d)
                out.append((nu, d, h, L, (sub(h, d) not in S) + (g not in S)))
    return out

def stats(S, c=None):
    if c is None: c = cost(S)
    ch = chords(S); oo = sorted(x[3] for x in ch if x[4] == 2)
    H = len(oo); Len = sum(oo)
    kappa = max((Fraction(i + 1, L) for i, L in enumerate(oo) if i + 1 == H or oo[i + 1] > L), default=Fraction(0))
    d = c['boundary']
    return dict(H=H, Len=Len, kappa=kappa, A=d - 3 * c['nu2'] + H - Fraction(3, 2) * kappa, K=c['U'] - Fraction(3, 4) * kappa, B=d - Len + Fraction(H, 2),
                bb=sum(1 for x in ch if x[4] == 0), ob=sum(1 for x in ch if x[4] == 1), U=c['U'], d=d)

def show(name, S):
    t = stats(S); print(f"{name}: N = {len(S)}, U* = {t['U']}, chords oo/ob/bb = {t['H']}/{t['ob']}/{t['bb']}, kappa = {float(t['kappa']):.2f}, "
                        f"slack of (A) = {float(t['A']):.2f}, of (K) = {float(t['K']):.2f}, of (B) = {float(t['B']):.1f}")
    return t

if __name__ == '__main__':
    show("single site", {(0, 0, 0)}); show("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
    for r in range(2, 10): show(f"O_{r}", octa(r))
    for k in (4, 6, 9): show(f"tetrahedron {k}", tetra(k))
    show("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))); show("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0)))
    show("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))); show("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2)))
    show("O_6 u O_6+(11,1,0)", octa(6) | octa(6, (11, 1, 0))); show("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
    show("O_6 without a vertex", octa(6) - {(5, 0, 0)}); show("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
    show("rod of 10", {(i, -i, 0) for i in range(10)}); show("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
```

## `chordB.py`

```python
"""Section 45: the pointwise inequality behind (B).  For a site h with a given set of empty neighbours let
deg = their number, e = number of nu with the three roots of R_nu empty (exposures), o = number of pairs (nu, r) with
nu an exposure and r an empty root with r.nu = 0 (open ends at h).  Claim: 12 e - 4 deg <= o for all 4096 sets."""
import itertools
from gmin import ROOTS
from chords import NUS, RNU, dot
worst = None; bad = 0; table = {}
for mask in range(1 << 12):
    emp = [ROOTS[i] for i in range(12) if mask >> i & 1]; es = set(emp)
    ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
    o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
    v = o - 12 * len(ex) + 4 * len(emp)
    if v < 0: bad += 1
    key = (len(emp), len(ex)); table[key] = min(table.get(key, 99), v)
print("sets with 12 e - 4 deg > o:", bad)
print("least o - 12 e + 4 deg by (deg, e):", dict(sorted(table.items())))
```

## `chordM.py`

```python
"""Section 45: the chord count (M_n).  With H, Len of chords.py, p = d - 3 nu1, U = U*, and
    Dn = sum over the chords C with two open ends and at most n sites of (n + 1/2 - |C|),
    Dn+ = sum over those with more than n sites of (|C| - n - 1/2),      B = d - Len + H/2  (>= 0, proved),
the identity   Lam_n = M_n + 3 B + 3 Dn+,   M_n = (2n^2 - 3n) U + 3n (H - p) - 3 Dn   holds for every finite set.
(M_n): M_n >= 0.     python3 chordM.py families | near r | small N"""
import sys
from fractions import Fraction
from gmin import *
from chords import chords
from lin import lam
HALF = Fraction(1, 2)
def data(S, c=None):
    if c is None: c = cost(S)
    oo = sorted(x[3] for x in chords(S) if x[4] == 2)
    return c, oo
def M(c, oo, n):
    U = c['U']; p = c['boundary'] - 3 * c['nu1']; H = len(oo)
    Dn = sum(n + HALF - L for L in oo if L <= n)
    return (2 * n * n - 3 * n) * U + 3 * n * (H - p) - 3 * Dn
def check_identity(c, oo, n):
    H = len(oo); B = c['boundary'] - sum(oo) + HALF * H; Dp = sum(L - n - HALF for L in oo if L > n)
    assert lam(c, n) == M(c, oo, n) + 3 * B + 3 * Dp
def minM(S, c=None, nmax=None, n0=3):
    c, oo = data(S, c); top = (max(oo) if oo else 3) + 3
    best = min((M(c, oo, n), n) for n in range(n0, max(top, n0 + 1) + 1))
    for n in (3, 5, 8): check_identity(c, oo, n)
    return best, c, oo
def line(name, S):
    (m, n), c, oo = minM(S); H = len(oo); p = c['boundary'] - 3 * c['nu1']
    print(f"{name}: N = {len(S)}, U* = {c['U']}, H = {H}, U + p - H = {c['U'] + p - H}, least M_n = {float(m):.1f} at n = {n}")
    return m
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'families':
        line("single site", {(0, 0, 0)}); line("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for r in range(2, 10): line(f"O_{r}", octa(r))
        for k in (4, 6, 9): line(f"tetrahedron {k}", tetra(k))
        for v in ((2, 0, 0), (4, 0, 0), (1, 1, 0), (2, 2, 2), (2, 2, 0), (13, 1, 0)): line(f"O_7 u O_7+{v}", octa(7) | octa(7, v))
        line("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
        line("O_6 without a vertex", octa(6) - {(5, 0, 0)}); line("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
        line("rod of 10", {(i, -i, 0) for i in range(10)}); line("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
        from psi import unions
        for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
            worst = None; cnt = 0; neg = 0
            for v, ov, S in unions(a, b):
                (m, n), c, oo = minM(S); cnt += 1; neg += m < 0
                if worst is None or m < worst[0]: worst = (m, n, v, c['U'])
            print(f"unions O_{a}, O_{b}+v: {cnt} bodies, with M_n < 0: {neg}; least M_n = {float(worst[0]):.1f} at n = {worst[1]} (v = {worst[2]}, U* = {worst[3]})")
    if mode == 'near':
        from psi import boundary_moves, toggle
        r = int(sys.argv[2]); S = octa(r); worst = None; cnt = 0; neg = 0
        for h in sorted(boundary_moves(S)):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            (m, n), c, oo = minM(T); cnt += 1; neg += m < 0
            if worst is None or m < worst[0]: worst = (m, n, h, c['U'])
        print(f"O_{r}: {cnt} bodies at one site; with M_n < 0: {neg}; least M_n = {float(worst[0]):.1f} at n = {worst[1]} (site {worst[2]}, U* = {worst[3]})")
    if mode == 'small':
        NMAX = int(sys.argv[2]); level = {frozenset({(0, 0, 0)})}; tot = 0; neg = 0; worst = None
        def norm(S):
            m = min(S); return frozenset((h[0] - m[0], h[1] - m[1], h[2] - m[2]) for h in S)
        for N in range(1, NMAX + 1):
            w = None
            for S in level:
                (m, n), c, oo = minM(set(S), n0=2); tot += 1; neg += m < 0
                if w is None or m < w[0]: w = (m, n, sorted(S))
            print(f"N = {N}: {len(level)} connected sets, least M_n (n >= 2) = {float(w[0]):.1f} at n = {w[1]}", flush=True)
            if N < NMAX: level = {norm(set(S) | {add(h, r)}) for S in level for h in S for r in ROOTS if add(h, r) not in S}
        print("sets:", tot, "with M_n < 0:", neg)
```

## `chordM2.py`

```python
"""Section 45: for which n does (M_n) fail?  For each body: the largest n with M_n < 0 (0 if none), n = 2, ..., longest chord + 3.
    python3 chordM2.py families | near r | bridge r | unions a b"""
import sys
from gmin import *
from chordM import data, M
def last_bad(S):
    c, oo = data(S); top = (max(oo) if oo else 3) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    return (max(bad) if bad else 0), c
def scan(name, bodies):
    worst = (0, None); cnt = 0; hist = {}
    for tag, S in bodies:
        b, c = last_bad(S); cnt += 1; hist[b] = hist.get(b, 0) + 1
        if b > worst[0]: worst = (b, tag, c['U'])
    print(f"{name}: {cnt} bodies; largest n with M_n < 0, by number of bodies: {dict(sorted(hist.items()))}; worst {worst}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    if mode == 'families':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        scan("named bodies", named)
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
```

## `steps.py`

```python
"""Section 45: (M_n) for O_r with small translates.  Does the range of n in which M_n < 0 grow with the height of the step?
    python3 steps.py r"""
import sys
from gmin import *
from chordM import data, M
from lin import lam, minlam
def row(name, S):
    c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    m, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, H = {len(oo)}, (M_n) fails for n in {bad}; least Lam_n = {m} at n = {n}", flush=True)
r = int(sys.argv[1])
for t in (2, 4, 6):
    row(f"O_{r} u O_{r}+({t},{t},{t})", octa(r) | octa(r, (t, t, t)))
for v in ((2, 2, 0), (4, 4, 0), (3, 3, 0), (1, 1, 2), (2, 2, 4), (3, 1, 0), (4, 2, 0), (6, 2, 0)):
    row(f"O_{r} u O_{r}+{v}", octa(r) | octa(r, v))
```

## `slopes.py`

```python
"""Section 45: slopes of silhouette runs.
A chord with two open ends (chords.py) is a whole run of S on its line, exposed for one nu; call it a silhouette run.
For a silhouette run C with L sites in the plane of nu and one of the two neighbouring parallel lines of that plane, the
line has L + 1 sites next to C; the L - 1 of them that touch two sites of C are the inner ones.  C has a predecessor on
that side if L >= 2 and the inner sites are exactly a silhouette run, and a successor if the L + 1 sites are exactly one.
A start is a silhouette run without predecessor; it is the least run of max(1, number of its successors) slopes.
(S): 3 * slopes <= 4 U*, which is false (Section 45.6).      python3 slopes.py families | unions a b | near r"""
import sys
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
def slopes(S):
    """returns (number of slopes, number of starts, number of silhouette runs, list of start lengths with multiplicity = slopes)"""
    nsl = 0; nst = 0; H = 0; mins = []
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        ds = DNU[nu]
        for d in ds:
            others = [r for r in ROOTS if dot(r, nu) == 0 and r != d and r != (-d[0], -d[1], -d[2])]
            # the two sides: d2 with d2 + d also a root of the plane; side A uses a_k = h0 + d2 + k d, side B uses h0 - d2 - d + k d
            d2 = next(r for r in others if add(r, d) in others)
            runs = {}
            for h in F:
                if sub(h, d) in F: continue
                L = 1; g = add(h, d)
                while g in F: L += 1; g = add(g, d)
                if sub(h, d) not in S and g not in S: runs[h] = L
            H += len(runs)
            def side(h0, L, base):
                """base = first of the L + 1 neighbouring sites; returns (has predecessor, has successor)"""
                a = [base]
                for k in range(L): a.append(add(a[-1], d))
                pred = L >= 2 and a[1] in runs and runs[a[1]] == L - 1
                succ = a[0] in runs and runs[a[0]] == L + 1
                return pred, succ
            for h0, L in runs.items():
                pA, sA = side(h0, L, add(h0, d2)); pB, sB = side(h0, L, sub(sub(h0, d2), d))
                if not pA and not pB:
                    k = max(1, sA + sB); nst += 1; nsl += k; mins += [L] * k
    return nsl, nst, H, mins
def row(name, S, c=None):
    if c is None: c = cost(S)
    nsl, nst, H, mins = slopes(S)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, runs {H}, starts {nst}, slopes {nsl}, 4 U* - 3 slopes = {4 * c['U'] - 3 * nsl}, start lengths {sorted(set(mins))[:8]}")
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    def scan(name, bodies):
        cnt = 0; neg = 0; low = None
        for tag, S in bodies:
            c = cost(S); nsl = slopes(S)[0]; v = 4 * c['U'] - 3 * nsl; cnt += 1; neg += v < 0
            if low is None or v < low[0]: low = (v, tag, c['U'], nsl)
        print(f"{name}: {cnt} bodies; with 3 slopes > 4 U*: {neg}; least 4 U* - 3 slopes = {low[0]} ({low[1]}, U* = {low[2]}, slopes {low[3]})", flush=True)
    if mode == 'families':
        row("single site", {(0, 0, 0)}); row("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for r in range(2, 9): row(f"O_{r}", octa(r))
        for k in (4, 6, 9): row(f"tetrahedron {k}", tetra(k))
        for v in ((2, 0, 0), (4, 0, 0), (1, 1, 0), (2, 2, 2), (2, 2, 0), (13, 1, 0), (12, 0, 0)): row(f"O_7 u O_7+{v}", octa(7) | octa(7, v))
        row("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
        row("O_6 without a vertex", octa(6) - {(5, 0, 0)}); row("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
        row("rod of 10", {(i, -i, 0) for i in range(10)}); row("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
        row("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0)))
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
```

## `msearch.py`

```python
"""Section 45: search for a finite set with M_n < 0 for some n >= 6 (chordM.py), and scan of (K): 3 H_j <= 4 U* j for all j.
    python3 msearch.py anneal seed steps T0        python3 msearch.py K"""
import sys, random, math
from fractions import Fraction
from gmin import *
from chordM import data, M
from psi import boundary_moves, toggle, unions
def gM(S):
    c, oo = data(S); top = (max(oo) if oo else 6) + 3
    return float(min(M(c, oo, n) for n in range(6, max(top, 7) + 1))) / c['boundary']
def kslack(S):
    c, oo = data(S); U = c['U']; worst = None
    for i, L in enumerate(oo):
        if i + 1 == len(oo) or oo[i + 1] > L:
            v = Fraction(4 * U * L - 3 * (i + 1), 3)
            if worst is None or v < worst[0]: worst = (v, L)
    return worst, U
mode = sys.argv[1]
if mode == 'anneal':
    seed, steps, T0 = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]); rng = random.Random(seed)
    starts = [("O_6", octa(6)), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))), ("O_6 u O_6+(1,1,0)", octa(6) | octa(6, (1, 1, 0))),
              ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 u O_6+(11,1,0)", octa(6) | octa(6, (11, 1, 0)))]
    for name, S in starts:
        cur = gM(S); g0 = cur; best = (cur, set(S)); mv = boundary_moves(S)
        for i in range(steps):
            T = T0 * (1 - i / steps) + 0.005
            h = rng.choice(mv); S2 = toggle(S, h)
            if len(S2) < 2 or (h in S and not connected(S2)): continue
            u = gM(S2)
            if u <= cur or rng.random() < math.exp((cur - u) / T):
                S, cur = S2, u; mv = boundary_moves(S)
                if cur < best[0]: best = (cur, set(S))
        c = cost(best[1]); print(f"{name}: least M_n (n >= 6) / boundary: {g0:.4f} -> {best[0]:.4f}; N = {len(best[1])}, U* = {c['U']}", flush=True)
        if best[0] < 0: print("   NEGATIVE", sorted(best[1]), flush=True)
if mode == 'K':
    def scan(name, bodies):
        cnt = 0; neg = 0; low = None
        for tag, S in bodies:
            if len(S) < 2: continue
            (v, L), U = kslack(S); cnt += 1; neg += v < 0
            if low is None or v < low[0]: low = (v, L, tag, U)
        print(f"{name}: {cnt} bodies; with 3 H_j > 4 U* j for some j: {neg}; least (4/3) U* j - H_j = {float(low[0]):.2f} at j = {low[1]} ({low[2]}, U* = {low[3]})", flush=True)
    for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)): scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    for r in (5, 6, 7, 8):
        S = octa(r); scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
```

## `minviol.py`

```python
"""Section 45: small bodies that violate G_chi (U* >= 6T - 9 chi, pinch points resolved).  Annealing on slack + lam * size."""
import sys, random, math
from gmin import *
from tops import tops
from euler import chi_v
from psi import boundary_moves, toggle
def slack(S): return cost(S)["U"] - 6 * tops(S)[0] + 9 * chi_v(S, True)
seed = int(sys.argv[1]); lam = float(sys.argv[2]); steps = int(sys.argv[3]); rng = random.Random(seed)
best_all = None
for trial in range(int(sys.argv[4])):
    S = {(0, 0, 0)}
    while len(S) < rng.choice((12, 20, 30)):
        h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
    f = lambda X: slack(X) + lam * len(X)
    cur = f(S); mv = boundary_moves(S); small = None
    for i in range(steps):
        T = 3.0 * (1 - i / steps) + 0.05
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = f(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            sl = cur - lam * len(S)
            if sl < 0 and (small is None or len(S) < len(small[1])): small = (sl, set(S))
    if small and (best_all is None or len(small[1]) < len(best_all[1])): best_all = small
    print(trial, 'smallest violator in this run:', (len(small[1]), small[0]) if small else None, flush=True)
if best_all:
    B = best_all[1]; print('SMALLEST', len(B), 'slack', slack(B), 'U*', cost(B)['U'], 'T', tops(B)[0], 'chi', chi_v(B, True)); print(sorted(B))
```

## Output of `python3 lin.py families`

```
O_r, r = 5..10: Lam_n = 36 (n - r)^2 for n = 3..39
O_2: N = 6, U* = 42, n2* = 6, boundary = 48, D = 2304, least Lam_n = 252 at n = 3
O_3: N = 19, U* = 54, n2* = 18, boundary = 108, D = 46656, least Lam_n = 324 at n = 3
O_4: N = 44, U* = 42, n2* = 38, boundary = 192, D = 85248, least Lam_n = 252 at n = 3
single site: N = 1, U* = 15, n2* = 1, boundary = 12, D = -1152, least Lam_n = 90 at n = 3
two adjacent sites: N = 2, U* = 26, n2* = 2, boundary = 22, D = -2864, least Lam_n = 156 at n = 3
tetrahedron 4: N = 20, U* = 60, n2* = 20, boundary = 120, D = 57600, least Lam_n = 360 at n = 3
tetrahedron 6: N = 56, U* = 60, n2* = 44, boundary = 252, D = 191808, least Lam_n = 432 at n = 3
tetrahedron 9: N = 165, U* = 78, n2* = 74, boundary = 540, D = 724032, least Lam_n = 972 at n = 3
tetrahedron 12: N = 364, U* = 96, n2* = 104, boundary = 936, D = 1795392, least Lam_n = 1836 at n = 3
unions O_7, O_7+v: 79 bodies, with Lam_n < 0: 0; least Lam_n = 190 at n = 7 (v = (1, 1, 0), U* = 20, D = 40000)
unions O_9, O_9+v: 146 bodies, with Lam_n < 0: 0; least Lam_n = 318 at n = 9 (v = (1, 1, 0), U* = 20, D = 66112)
unions O_5, O_8+v: 61 bodies, with Lam_n < 0: 0; least Lam_n = 294 at n = 7 (v = (2, 2, 1), U* = 21, D = 65808)
unions O_6, O_9+v: 88 bodies, with Lam_n < 0: 0; least Lam_n = 384 at n = 8 (v = (2, 2, 1), U* = 21, D = 85968)
```

## Output of `python3 lin.py near r`, r = 5, 6, 7, 8

```
O_5: 206 bodies at one site; with Lam_n < 0: 0; least Lam_n = 38 at n = 5 (site (-4, 0, 0), U* = 19, n2* = 61, D = 7168)
O_6: 294 bodies at one site; with Lam_n < 0: 0; least Lam_n = 60 at n = 6 (site (-5, 0, 0), U* = 19, n2* = 77, D = 11392)
O_7: 398 bodies at one site; with Lam_n < 0: 0; least Lam_n = 86 at n = 7 (site (-6, 0, 0), U* = 19, n2* = 93, D = 16384)
O_8: 518 bodies at one site; with Lam_n < 0: 0; least Lam_n = 116 at n = 8 (site (-7, 0, 0), U* = 19, n2* = 109, D = 22144)
```

## Output of `python3 lin.py bridge 5` and `bridge 6`

```
two O_5 joined by one site: 146 bodies; with Lam_n < 0: 0; least Lam_n = 176 at n = 4 (v = (10, 1, 1), site (5, 1, 0), U* = 43, n2* = 125, D = 74560)
two O_6 joined by one site: 233 bodies; with Lam_n < 0: 0; least Lam_n = 266 at n = 5 (v = (12, 1, 1), site (6, 0, 1), U* = 43, n2* = 157, D = 119872)
```

## Output of `python3 lintest.py special`

```
   O_9 with a cavity O_3: N = 470, U* = 126, least Lam_n = 2106 at n = 3; largest n with M_n < 0: 2
   O_7 with a one-site cavity: N = 230, U* = 36, least Lam_n = 612 at n = 4; largest n with M_n < 0: 2
   ring of four O_5: N = 316, U* = 141, least Lam_n = 1701 at n = 3; largest n with M_n < 0: 2
   three O_6 in a row, vertex to vertex: N = 438, U* = 70, least Lam_n = 716 at n = 5; largest n with M_n < 0: 3
   three O_6 at a right angle: N = 438, U* = 70, least Lam_n = 716 at n = 5; largest n with M_n < 0: 3
   two O_7 tip to tip: N = 461, U* = 51, least Lam_n = 912 at n = 5; largest n with M_n < 0: 2
   two O_7 along an axis, offset 6: N = 418, U* = 54, least Lam_n = 1368 at n = 4; largest n with M_n < 0: 2
   O_8 and O_4 on a vertex: N = 382, U* = 54, least Lam_n = 1152 at n = 4; largest n with M_n < 0: 2
   O_8 and O_4 on a face: N = 388, U* = 60, least Lam_n = 1236 at n = 4; largest n with M_n < 0: 2
   two O_6 joined by a zigzag: N = 294, U* = 54, least Lam_n = 558 at n = 4; largest n with M_n < 0: 3
   O_7 with twin tops (2,0,0): N = 316, U* = 42, least Lam_n = 984 at n = 4; largest n with M_n < 0: 2
special bodies: 11 bodies; with Lam_n < 0: 0; least Lam_n = 558 at n = 4 (two O_6 joined by a zigzag, U* = 54); largest n with M_n < 0, by number of bodies: {2: 8, 3: 3}
```

## Output of `python3 lintest.py roof N n` for (N, n) = (6, 5), (6, 6), (7, 5), (7, 6), (8, 4); `bridge2 5`; `near2 5`

```
roof O_6 over two legs O_5: 92 bodies; with Lam_n < 0: 0; least Lam_n = 572 at n = 4 ((10, 0, 1), U* = 70); largest n with M_n < 0, by number of bodies: {2: 86, 3: 6}
roof O_6 over two legs O_6: 116 bodies; with Lam_n < 0: 0; least Lam_n = 609 at n = 5 ((1, 1, 2), U* = 30); largest n with M_n < 0, by number of bodies: {2: 107, 3: 9}
roof O_7 over two legs O_5: 104 bodies; with Lam_n < 0: 0; least Lam_n = 752 at n = 4 ((11, 0, 1), U* = 70); largest n with M_n < 0, by number of bodies: {2: 96, 3: 8}
roof O_7 over two legs O_6: 130 bodies; with Lam_n < 0: 0; least Lam_n = 824 at n = 5 ((12, 0, 1), U* = 70); largest n with M_n < 0, by number of bodies: {2: 124, 3: 6}
roof O_8 over two legs O_4: 96 bodies; with Lam_n < 0: 0; least Lam_n = 860 at n = 5 ((5, 0, 1), U* = 34); largest n with M_n < 0, by number of bodies: {0: 1, 2: 89, 3: 6}
two O_5 joined by two sites: 623 bodies; with Lam_n < 0: 0; least Lam_n = 214 at n = 4 (((6, 5, 3), (4, 1, 1), (5, 1, 2)), U* = 44); largest n with M_n < 0, by number of bodies: {0: 26, 2: 428, 3: 162, 4: 7}
bodies at two sites from O_5: 21055 bodies; with Lam_n < 0: 0; least Lam_n = 76 at n = 4 (((-4, 0, 0), (0, -4, 0)), U* = 20); largest n with M_n < 0, by number of bodies: {0: 135, 2: 18156, 3: 2764}
```

## Output of `python3 linsearch.py`: `1 4000 0.3 octa`, `2 3000 0.2 twin`, `3 3000 0.2 bridge`, `4 2500 0.3 unions 5 12`, `5 2500 0.3 unions 6 10`, `6 4000 0.5 blobs 6`, `7 4000 0.05 octa`

```
O_5: g 0.0000 -> 0.0000; end N = 85, U* = 18, n2* = 62, least Lam_n = 0 at n = 5, D = 0
O_6: g 0.0000 -> 0.0000; end N = 146, U* = 18, n2* = 78, least Lam_n = 0 at n = 6, D = 0
O_7: g 0.0000 -> 0.0000; end N = 231, U* = 18, n2* = 94, least Lam_n = 0 at n = 7, D = 0
LEAST g 0.0 O_5
O_7 u O_7+(2,0,0): g 1.3226 -> 1.0040; end N = 321, U* = 32, n2* = 106, least Lam_n = 757 at n = 5, D = 257908
O_6 u O_6+(1,1,0): g 0.2749 -> 0.2749; end N = 182, U* = 20, n2* = 84, least Lam_n = 138 at n = 6, D = 29248
O_6 u O_6+(2,2,2): g 0.5769 -> 0.5769; end N = 237, U* = 24, n2* = 96, least Lam_n = 360 at n = 6, D = 90432
LEAST g 0.2749003984063745 O_6 u O_6+(1,1,0)
two O_5 and a site: g 0.2895 -> 0.2895; end N = 171, U* = 43, n2* = 125, least Lam_n = 176 at n = 4, D = 74560
two O_6 and a site: g 0.3050 -> 0.3050; end N = 293, U* = 43, n2* = 157, least Lam_n = 266 at n = 5, D = 119872
two O_5 vertex to vertex: g 0.4181 -> 0.4181; end N = 170, U* = 44, n2* = 120, least Lam_n = 250 at n = 4, D = 115792
LEAST g 0.2894736842105263 two O_5 and a site
O_5 u O_5+(6, 1, 1): g 0.9783 -> 0.9783; end N = 166, U* = 46, n2* = 98, least Lam_n = 542 at n = 4, D = 255616
O_5 u O_5+(6, 0, 0): g 1.0435 -> 0.8438; end N = 150, U* = 75, n2* = 117, least Lam_n = 486 at n = 3, D = 387072
O_5 u O_5+(5, 5, 0): g 0.9254 -> 0.9254; end N = 170, U* = 58, n2* = 110, least Lam_n = 546 at n = 3, D = 332992
O_5 u O_5+(4, 3, 1): g 0.8833 -> 0.8833; end N = 162, U* = 38, n2* = 90, least Lam_n = 454 at n = 4, D = 182656
O_5 u O_5+(8, 1, 1): g 0.6136 -> 0.6136; end N = 170, U* = 46, n2* = 114, least Lam_n = 362 at n = 4, D = 177280
O_5 u O_5+(5, 3, 2): g 1.0830 -> 0.8917; end N = 172, U* = 40, n2* = 96, least Lam_n = 494 at n = 4, D = 209728
O_5 u O_5+(9, 1, 0): g 0.4181 -> 0.4181; end N = 170, U* = 44, n2* = 120, least Lam_n = 250 at n = 4, D = 115792
O_5 u O_5+(6, 2, 2): g 0.9718 -> 0.9545; end N = 168, U* = 52, n2* = 104, least Lam_n = 546 at n = 3, D = 294736
O_5 u O_5+(6, 4, 0): g 0.9628 -> 0.8116; end N = 164, U* = 58, n2* = 114, least Lam_n = 474 at n = 3, D = 285136
O_5 u O_5+(4, 3, 3): g 1.1402 -> 0.6015; end N = 174, U* = 28, n2* = 92, least Lam_n = 326 at n = 5, D = 96832
O_5 u O_5+(8, 2, 0): g 0.7181 -> 0.5556; end N = 169, U* = 48, n2* = 118, least Lam_n = 330 at n = 4, D = 168372
O_5 u O_5+(7, 3, 0): g 0.9091 -> 0.6757; end N = 162, U* = 56, n2* = 120, least Lam_n = 400 at n = 4, D = 224512
LEAST g 0.4180602006688963 O_5 u O_5+(9, 1, 0)
O_6 u O_6+(4, 2, 0): g 1.2471 -> 1.1754; end N = 257, U* = 42, n2* = 102, least Lam_n = 804 at n = 4, D = 359424
O_6 u O_6+(5, 1, 0): g 1.3175 -> 1.2682; end N = 262, U* = 49, n2* = 107, least Lam_n = 908 at n = 4, D = 465616
O_6 u O_6+(4, 0, 0): g 1.3929 -> 1.2927; end N = 244, U* = 46, n2* = 98, least Lam_n = 848 at n = 4, D = 405760
O_6 u O_6+(11, 1, 0): g 0.4362 -> 0.4362; end N = 292, U* = 44, n2* = 152, least Lam_n = 376 at n = 5, D = 176464
O_6 u O_6+(9, 2, 1): g 0.8156 -> 0.8156; end N = 292, U* = 48, n2* = 140, least Lam_n = 690 at n = 4, D = 345168
O_6 u O_6+(6, 1, 1): g 1.1425 -> 1.1425; end N = 276, U* = 46, n2* = 114, least Lam_n = 866 at n = 4, D = 424576
O_6 u O_6+(8, 2, 2): g 0.9423 -> 0.9423; end N = 292, U* = 50, n2* = 134, least Lam_n = 784 at n = 4, D = 417088
O_6 u O_6+(7, 2, 1): g 1.0451 -> 1.0451; end N = 286, U* = 48, n2* = 124, least Lam_n = 834 at n = 4, D = 426960
O_6 u O_6+(10, 2, 0): g 0.7488 -> 0.6049; end N = 291, U* = 48, n2* = 150, least Lam_n = 519 at n = 5, D = 259380
O_6 u O_6+(7, 4, 1): g 1.1590 -> 1.0719; end N = 285, U* = 60, n2* = 136, least Lam_n = 894 at n = 4, D = 564048
LEAST g 0.4361948955916473 O_6 u O_6+(11, 1, 0)
blob 0: g 4.2574 -> 1.0541; end N = 52, U* = 36, n2* = 44, least Lam_n = 234 at n = 3, D = 82944
blob 1: g 3.9403 -> 0.9628; end N = 76, U* = 34, n2* = 56, least Lam_n = 285 at n = 3, D = 103348
blob 2: g 4.5203 -> 1.0714; end N = 89, U* = 48, n2* = 64, least Lam_n = 360 at n = 3, D = 177408
blob 3: g 4.0588 -> 0.9474; end N = 89, U* = 39, n2* = 65, least Lam_n = 324 at n = 3, D = 134784
blob 4: g 4.7171 -> 0.9485; end N = 105, U* = 42, n2* = 76, least Lam_n = 387 at n = 3, D = 172404
blob 5: g 4.6200 -> 1.2000; end N = 84, U* = 55, n2* = 65, least Lam_n = 420 at n = 3, D = 227200
LEAST g 0.9473684210526315 blob 3
O_5: g 0.0000 -> 0.0000; end N = 85, U* = 18, n2* = 62, least Lam_n = 0 at n = 5, D = 0
O_6: g 0.0000 -> 0.0000; end N = 146, U* = 18, n2* = 78, least Lam_n = 0 at n = 6, D = 0
O_7: g 0.0000 -> 0.0000; end N = 231, U* = 18, n2* = 94, least Lam_n = 0 at n = 7, D = 0
LEAST g 0.0 O_5
```

## Output of `python3 dscan.py`

```
1790 bodies; with D < 0: 0; least D = 7168 ((5, (-4, 0, 0)), U* = 19)
```

## Output of `python3 algebra62.py`

```
Proposition 62: identities hold on 2000 random integer cases
O_6 without a vertex: the two other forms of M_n agree for n = 1..13; delta = 4, kappa_j for j = 1..7: ['16/3', '20/3', '8', '28/3', '8/3', '12', '112/3']
O_7 u O_7+(2,2,2): the two other forms of M_n agree for n = 1..13; delta = 12, kappa_j for j = 1..7: ['2', '4', '12', '20', '28', '36', '32']
two O_5 and a site: the two other forms of M_n agree for n = 1..13; delta = 20, kappa_j for j = 1..7: ['22/3', '50/3', '26', '106/3', '170/3', '112', '508/3']
```

## Output of `python3 chords.py`

```
single site: N = 1, U* = 15, chords oo/ob/bb = 24/0/0, kappa = 24.00, slack of (A) = -6.00, of (K) = -3.00, of (B) = 0.0
two adjacent sites: N = 2, U* = 26, chords oo/ob/bb = 32/0/0, kappa = 28.00, slack of (A) = 0.00, of (K) = 5.00, of (B) = 2.0
O_2: N = 6, U* = 42, chords oo/ob/bb = 48/0/0, kappa = 24.00, slack of (A) = 24.00, of (K) = 24.00, of (B) = 0.0
O_3: N = 19, U* = 54, chords oo/ob/bb = 72/0/0, kappa = 24.00, slack of (A) = 36.00, of (K) = 36.00, of (B) = 0.0
O_4: N = 44, U* = 42, chords oo/ob/bb = 96/0/0, kappa = 24.00, slack of (A) = 24.00, of (K) = 24.00, of (B) = 0.0
O_5: N = 85, U* = 18, chords oo/ob/bb = 120/0/0, kappa = 24.00, slack of (A) = 0.00, of (K) = 0.00, of (B) = 0.0
O_6: N = 146, U* = 18, chords oo/ob/bb = 144/0/0, kappa = 24.00, slack of (A) = 0.00, of (K) = 0.00, of (B) = 0.0
O_7: N = 231, U* = 18, chords oo/ob/bb = 168/0/0, kappa = 24.00, slack of (A) = 0.00, of (K) = 0.00, of (B) = 0.0
O_8: N = 344, U* = 18, chords oo/ob/bb = 192/0/0, kappa = 24.00, slack of (A) = 0.00, of (K) = 0.00, of (B) = 0.0
O_9: N = 489, U* = 18, chords oo/ob/bb = 216/0/0, kappa = 24.00, slack of (A) = 0.00, of (K) = 0.00, of (B) = 0.0
tetrahedron 4: N = 20, U* = 60, chords oo/ob/bb = 60/0/0, kappa = 24.00, slack of (A) = 24.00, of (K) = 42.00, of (B) = 18.0
tetrahedron 6: N = 56, U* = 60, chords oo/ob/bb = 84/0/0, kappa = 24.00, slack of (A) = 12.00, of (K) = 42.00, of (B) = 30.0
tetrahedron 9: N = 165, U* = 78, chords oo/ob/bb = 120/0/0, kappa = 24.00, slack of (A) = 12.00, of (K) = 60.00, of (B) = 48.0
O_7 u O_7+(2,0,0): N = 316, U* = 42, chords oo/ob/bb = 192/96/0, kappa = 40.00, slack of (A) = 0.00, of (K) = 12.00, of (B) = 96.0
O_7 u O_7+(4,0,0): N = 377, U* = 54, chords oo/ob/bb = 216/80/0, kappa = 40.00, slack of (A) = 12.00, of (K) = 24.00, of (B) = 160.0
O_7 u O_7+(1,1,0): N = 280, U* = 20, chords oo/ob/bb = 176/0/0, kappa = 24.57, slack of (A) = -0.86, of (K) = 1.57, of (B) = 2.0
O_7 u O_7+(2,2,2): N = 358, U* = 24, chords oo/ob/bb = 192/132/0, kappa = 30.00, slack of (A) = -9.00, of (K) = 1.50, of (B) = 138.0
O_6 u O_6+(11,1,0): N = 292, U* = 44, chords oo/ob/bb = 272/12/0, kappa = 47.20, slack of (A) = -4.80, of (K) = 8.60, of (B) = 66.0
two O_6 and a site: N = 293, U* = 43, chords oo/ob/bb = 280/14/0, kappa = 50.00, slack of (A) = -9.00, of (K) = 5.50, of (B) = 60.0
O_6 without a vertex: N = 145, U* = 19, chords oo/ob/bb = 140/0/0, kappa = 24.80, slack of (A) = -3.20, of (K) = 0.40, of (B) = 6.0
O_6 with a site on a face: N = 147, U* = 24, chords oo/ob/bb = 144/18/0, kappa = 30.00, slack of (A) = -6.00, of (K) = 1.50, of (B) = 25.0
rod of 10: N = 10, U* = 114, chords oo/ob/bb = 96/0/0, kappa = 92.00, slack of (A) = 0.00, of (K) = 45.00, of (B) = 18.0
(111) layer: N = 37, U* = 195, chords oo/ob/bb = 96/0/0, kappa = 48.00, slack of (A) = 66.00, of (K) = 159.00, of (B) = 18.0
```

## Output of `python3 chordB.py`

```
sets with 12 e - 4 deg > o: 0
least o - 12 e + 4 deg by (deg, e): {(0, 0): 0, (1, 0): 4, (2, 0): 8, (3, 0): 12, (3, 1): 0, (4, 0): 16, (4, 1): 4, (5, 0): 20, (5, 1): 8, (5, 2): 0, (6, 0): 24, (6, 1): 13, (6, 2): 0, (7, 0): 28, (7, 1): 18, (7, 2): 6, (7, 3): 2, (8, 0): 32, (8, 1): 23, (8, 2): 12, (8, 3): 4, (8, 4): 0, (9, 2): 18, (9, 3): 10, (9, 4): 4, (10, 4): 8, (10, 5): 4, (11, 6): 4, (12, 8): 0}
```

## Output of `python3 chordM.py families`

```
single site: N = 1, U* = 15, H = 24, U + p - H = 0, least M_n = 90.0 at n = 3
two adjacent sites: N = 2, U* = 26, H = 32, U + p - H = 10, least M_n = 150.0 at n = 3
O_2: N = 6, U* = 42, H = 48, U + p - H = 24, least M_n = 252.0 at n = 3
O_3: N = 19, U* = 54, H = 72, U + p - H = 36, least M_n = 324.0 at n = 3
O_4: N = 44, U* = 42, H = 96, U + p - H = 24, least M_n = 216.0 at n = 3
O_5: N = 85, U* = 18, H = 120, U + p - H = 0, least M_n = 0.0 at n = 3
O_6: N = 146, U* = 18, H = 144, U + p - H = 0, least M_n = 0.0 at n = 3
O_7: N = 231, U* = 18, H = 168, U + p - H = 0, least M_n = 0.0 at n = 3
O_8: N = 344, U* = 18, H = 192, U + p - H = 0, least M_n = 0.0 at n = 3
O_9: N = 489, U* = 18, H = 216, U + p - H = 0, least M_n = 0.0 at n = 3
tetrahedron 4: N = 20, U* = 60, H = 60, U + p - H = 60, least M_n = 288.0 at n = 3
tetrahedron 6: N = 56, U* = 60, H = 84, U + p - H = 72, least M_n = 180.0 at n = 3
tetrahedron 9: N = 165, U* = 78, H = 120, U + p - H = 108, least M_n = 180.0 at n = 3
O_7 u O_7+(2, 0, 0): N = 316, U* = 42, H = 192, U + p - H = 24, least M_n = 96.0 at n = 3
O_7 u O_7+(4, 0, 0): N = 377, U* = 54, H = 216, U + p - H = 36, least M_n = 132.0 at n = 3
O_7 u O_7+(1, 1, 0): N = 280, U* = 20, H = 176, U + p - H = 4, least M_n = 30.0 at n = 3
O_7 u O_7+(2, 2, 2): N = 358, U* = 24, H = 192, U + p - H = 12, least M_n = -72.0 at n = 3
O_7 u O_7+(2, 2, 0): N = 327, U* = 34, H = 192, U + p - H = 18, least M_n = 90.0 at n = 3
O_7 u O_7+(13, 1, 0): N = 462, U* = 44, H = 320, U + p - H = 22, least M_n = -24.0 at n = 3
two O_6 and a site: N = 293, U* = 43, H = 280, U + p - H = 20, least M_n = -69.0 at n = 3
O_6 without a vertex: N = 145, U* = 19, H = 140, U + p - H = 4, least M_n = 12.0 at n = 3
O_6 with a site on a face: N = 147, U* = 24, H = 144, U + p - H = 9, least M_n = -16.5 at n = 3
rod of 10: N = 10, U* = 114, H = 96, U + p - H = 90, least M_n = 552.0 at n = 3
(111) layer: N = 37, U* = 195, H = 96, U + p - H = 252, least M_n = 882.0 at n = 3
unions O_7, O_7+v: 79 bodies, with M_n < 0: 9; least M_n = -72.0 at n = 3 (v = (2, 2, 2), U* = 24)
unions O_9, O_9+v: 146 bodies, with M_n < 0: 9; least M_n = -72.0 at n = 3 (v = (2, 2, 2), U* = 24)
unions O_5, O_8+v: 61 bodies, with M_n < 0: 10; least M_n = -54.0 at n = 3 (v = (11, 1, 1), U* = 46)
unions O_6, O_9+v: 88 bodies, with M_n < 0: 9; least M_n = -54.0 at n = 3 (v = (13, 1, 1), U* = 46)
```

## Output of `python3 chordM2.py`: `families`, `unions 7 7`, `unions 5 8`, `near 5`, `near 7`, `bridge 5`, then `unions 9 9`, `unions 6 9`, `near 6`, `near 8`

```
named bodies: 15 bodies; largest n with M_n < 0, by number of bodies: {0: 10, 2: 5}; worst (2, 'tetra 4', 60)
unions O_7, O_7+v: 79 bodies; largest n with M_n < 0, by number of bodies: {0: 1, 2: 69, 3: 8, 5: 1}; worst (5, (2, 2, 2), 24)
unions O_5, O_8+v: 61 bodies; largest n with M_n < 0, by number of bodies: {2: 51, 3: 10}; worst (3, (2, 2, 1), 21)
bodies at one site from O_5: 206 bodies; largest n with M_n < 0, by number of bodies: {0: 6, 2: 144, 3: 56}; worst (3, (-3, -2, -1), 24)
bodies at one site from O_7: 398 bodies; largest n with M_n < 0, by number of bodies: {0: 42, 2: 212, 3: 144}; worst (3, (-5, -2, -1), 24)
two O_5 joined by one site: 146 bodies; largest n with M_n < 0, by number of bodies: {0: 51, 2: 81, 3: 11, 4: 3}; worst (4, ((10, 1, 1), (5, 1, 0)), 43)
unions O_9, O_9+v: 146 bodies; largest n with M_n < 0, by number of bodies: {0: 1, 2: 136, 3: 8, 5: 1}; worst (5, (2, 2, 2), 24)
unions O_6, O_9+v: 88 bodies; largest n with M_n < 0, by number of bodies: {2: 79, 3: 9}; worst (3, (2, 2, 1), 21)
bodies at one site from O_6: 294 bodies; largest n with M_n < 0, by number of bodies: {0: 30, 2: 168, 3: 96}; worst (3, (-4, -2, -1), 24)
bodies at one site from O_8: 518 bodies; largest n with M_n < 0, by number of bodies: {0: 54, 2: 264, 3: 200}; worst (3, (-6, -2, -1), 24)
```

## Output of `python3 steps.py 9`

```
O_9 u O_9+(2,2,2): N = 706, U* = 24, H = 240, (M_n) fails for n in [2, 3, 4, 5]; least Lam_n = 840 at n = 8
O_9 u O_9+(4,4,4): N = 869, U* = 66, H = 288, (M_n) fails for n in [2]; least Lam_n = 2616 at n = 4
O_9 u O_9+(6,6,6): N = 978, U* = 72, H = 336, (M_n) fails for n in [2]; least Lam_n = 2844 at n = 4
O_9 u O_9+(2, 2, 0): N = 649, U* = 34, H = 240, (M_n) fails for n in [2]; least Lam_n = 1356 at n = 6
O_9 u O_9+(4, 4, 0): N = 793, U* = 44, H = 272, (M_n) fails for n in [2]; least Lam_n = 1798 at n = 5
O_9 u O_9+(3, 3, 0): N = 724, U* = 36, H = 256, (M_n) fails for n in [2]; least Lam_n = 1494 at n = 6
O_9 u O_9+(1, 1, 2): N = 642, U* = 22, H = 232, (M_n) fails for n in [2, 3]; least Lam_n = 590 at n = 8
O_9 u O_9+(2, 2, 4): N = 773, U* = 50, H = 264, (M_n) fails for n in [2]; least Lam_n = 2116 at n = 4
O_9 u O_9+(3, 1, 0): N = 698, U* = 44, H = 248, (M_n) fails for n in [2]; least Lam_n = 1870 at n = 5
O_9 u O_9+(4, 2, 0): N = 760, U* = 46, H = 264, (M_n) fails for n in [2]; least Lam_n = 1982 at n = 5
O_9 u O_9+(6, 2, 0): N = 843, U* = 52, H = 288, (M_n) fails for n in [2]; least Lam_n = 2300 at n = 5
```

## Output of `python3 slopes.py families`

```
single site: N = 1, U* = 15, runs 24, starts 24, slopes 24, 4 U* - 3 slopes = -12, start lengths [1]
two adjacent sites: N = 2, U* = 26, runs 32, starts 32, slopes 32, 4 U* - 3 slopes = 8, start lengths [1, 2]
O_2: N = 6, U* = 42, runs 48, starts 24, slopes 24, 4 U* - 3 slopes = 96, start lengths [1]
O_3: N = 19, U* = 54, runs 72, starts 24, slopes 24, 4 U* - 3 slopes = 144, start lengths [1]
O_4: N = 44, U* = 42, runs 96, starts 24, slopes 24, 4 U* - 3 slopes = 96, start lengths [1]
O_5: N = 85, U* = 18, runs 120, starts 24, slopes 24, 4 U* - 3 slopes = 0, start lengths [1]
O_6: N = 146, U* = 18, runs 144, starts 24, slopes 24, 4 U* - 3 slopes = 0, start lengths [1]
O_7: N = 231, U* = 18, runs 168, starts 24, slopes 24, 4 U* - 3 slopes = 0, start lengths [1]
O_8: N = 344, U* = 18, runs 192, starts 24, slopes 24, 4 U* - 3 slopes = 0, start lengths [1]
tetrahedron 4: N = 20, U* = 60, runs 60, starts 24, slopes 24, 4 U* - 3 slopes = 168, start lengths [1]
tetrahedron 6: N = 56, U* = 60, runs 84, starts 24, slopes 24, 4 U* - 3 slopes = 168, start lengths [1]
tetrahedron 9: N = 165, U* = 78, runs 120, starts 24, slopes 24, 4 U* - 3 slopes = 240, start lengths [1]
O_7 u O_7+(2, 0, 0): N = 316, U* = 42, runs 192, starts 48, slopes 48, 4 U* - 3 slopes = 24, start lengths [1, 7]
O_7 u O_7+(4, 0, 0): N = 377, U* = 54, runs 216, starts 48, slopes 48, 4 U* - 3 slopes = 72, start lengths [1, 6]
O_7 u O_7+(1, 1, 0): N = 280, U* = 20, runs 176, starts 32, slopes 32, 4 U* - 3 slopes = -16, start lengths [1, 2, 7]
O_7 u O_7+(2, 2, 2): N = 358, U* = 24, runs 192, starts 42, slopes 42, 4 U* - 3 slopes = -30, start lengths [1, 7]
O_7 u O_7+(2, 2, 0): N = 327, U* = 34, runs 192, starts 44, slopes 44, 4 U* - 3 slopes = 4, start lengths [1, 4, 6]
O_7 u O_7+(13, 1, 0): N = 462, U* = 44, runs 320, starts 48, slopes 48, 4 U* - 3 slopes = 32, start lengths [1, 2]
O_7 u O_7+(12, 0, 0): N = 461, U* = 51, runs 312, starts 48, slopes 48, 4 U* - 3 slopes = 60, start lengths [1, 2]
two O_6 and a site: N = 293, U* = 43, runs 280, starts 56, slopes 56, 4 U* - 3 slopes = 4, start lengths [1, 2, 7]
O_6 without a vertex: N = 145, U* = 19, runs 140, starts 32, slopes 32, 4 U* - 3 slopes = -20, start lengths [1, 2, 5]
O_6 with a site on a face: N = 147, U* = 24, runs 144, starts 33, slopes 33, 4 U* - 3 slopes = -3, start lengths [1, 5, 6]
rod of 10: N = 10, U* = 114, runs 96, starts 96, slopes 96, 4 U* - 3 slopes = 168, start lengths [1, 10]
(111) layer: N = 37, U* = 195, runs 96, starts 66, slopes 66, 4 U* - 3 slopes = 582, start lengths [1, 4]
ring of four O_5: N = 316, U* = 141, runs 304, starts 96, slopes 96, 4 U* - 3 slopes = 276, start lengths [1, 3]
```

## Output of `python3 msearch.py K`

```
unions O_7, O_7+v: 79 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 1.33 at j = 1 ((2, 1, 1), U* = 22)
unions O_9, O_9+v: 146 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 1.33 at j = 1 ((2, 1, 1), U* = 22)
unions O_5, O_8+v: 61 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 1.00 at j = 1 ((2, 2, 1), U* = 21)
unions O_6, O_9+v: 88 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 1.00 at j = 1 ((2, 2, 1), U* = 21)
bodies at one site from O_5: 206 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 1.33 at j = 4 ((-4, 0, 0), U* = 19)
bodies at one site from O_6: 294 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 2.00 at j = 1 ((-4, -2, -1), U* = 24)
bodies at one site from O_7: 398 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 2.00 at j = 1 ((-5, -2, -1), U* = 24)
bodies at one site from O_8: 518 bodies; with 3 H_j > 4 U* j for some j: 0; least (4/3) U* j - H_j = 2.00 at j = 1 ((-6, -2, -1), U* = 24)
```

## Output of `python3 msearch.py anneal 1 1500 0.2` (seed 2 gives the same lines)

```
O_6: least M_n (n >= 6) / boundary: 0.0000 -> 0.0000; N = 146, U* = 18
O_7 u O_7+(2,2,2): least M_n (n >= 6) / boundary: 0.0441 -> 0.0441; N = 358, U* = 24
O_6 u O_6+(1,1,0): least M_n (n >= 6) / boundary: 0.2510 -> 0.2510; N = 182, U* = 20
two O_5 and a site: least M_n (n >= 6) / boundary: 0.3849 -> 0.3849; N = 171, U* = 43
O_6 without a vertex: least M_n (n >= 6) / boundary: 0.0981 -> 0.0981; N = 145, U* = 19
O_6 u O_6+(11,1,0): least M_n (n >= 6) / boundary: 0.3063 -> 0.3063; N = 292, U* = 44
```

## Output of `python3 minviol.py 1 0.5 3000 6` (site list cut)

```
0 smallest violator in this run: (137, -1.0)
1 smallest violator in this run: (133, -2.0)
2 smallest violator in this run: (181, -37.0)
3 smallest violator in this run: (148, -6.0)
4 smallest violator in this run: (195, -2.0)
5 smallest violator in this run: (162, -2.0)
SMALLEST 133 slack -2 U* 850 T 49 chi -62
[(-4, -2, -4), (-4, 0, -4), (-4, 1, -5), (-3, -1, -4), (-3, -1, -2), (-3, -1, 2), (-3, 0, -5), (-3, 0, -3), (-3, 0, 1), (-3, 1, 2), (-3, 3, 0), (-2, -2, -4), (-2, -1, -3), (-2, -1, -1), (-2, 0, -2), (-2, 0, 0), (-2, 1, -5), (-2, 2, -4), (-2, 2, -2), (-2, 2, 0), (-2, 2, 2), (-2, 3, 1), (-2, 4, 0), (-2, 5, 1), (-1, -3, 2), (-1, -2, -3), (-1, -1, -4), (-1, -1, 0), (-1, 0, -5), (-1, 0, 1), (-1, 1, -2) ... (133 sites)
```
