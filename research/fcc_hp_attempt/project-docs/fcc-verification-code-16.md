# FCC HP folding: verification code, part 16 (nineteenth pass, 14 Nov 2026)

Scripts for Section 42 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): a search for a counterexample to Conjecture R. Nothing here proves anything; the scripts compute the least number of defect units of finite bodies exactly and compare it with what the bodies hold. They are self-contained (none imports a script of an earlier pass). Python 3 with numpy and scipy.

| Script | What it does | Run |
|---|---|---|
| `gmin.py` | U* and n2* of a finite set by two bipartite matchings; reproduces the values of Section 8 | `python3 gmin.py` |
| `scan2.py` | all connected unions of two regular octahedra: U*, n2* against the capacity of one octahedron | `python3 scan2.py a b` |
| `psi.py` | X3, K, Psi; the same unions; local search on Psi over the whole boundary | `python3 psi.py scan a b`, `python3 psi.py search a b steps [f]` |
| `lgeo.py`, `lscan.py` | long geometric chains; on every union | `python3 lgeo.py`, `python3 lscan.py` |
| `price.py` | units paid per pyramid beyond six | `python3 price.py` |
| `near.py` | bodies at one or two sites from a regular octahedron | `python3 near.py n [2]` |
| `junction.py` | local search around the contact of two lumps, with a guard on what the body holds | `python3 junction.py a b r [steps]` |
| `roof.py` | a roof over two legs (three octahedra) | `python3 roof.py N n J` |

The searches use fixed random seeds. The first version of `junction.py`, without the guard, is described in Section 42; its two low results (U* = 28 and 30) are bodies fused into one lump.

## `gmin.py`

```python
"""Exact cost of a shape (Section 4 of the note): G(S) = boundary(S) - (3/2)(nu_1 + nu_2), where nu_1 is the size of a
maximum matching between surface sites and coat sites and nu_2 the largest number of coat sites that can be assigned
with every surface site used at most twice.  U*(S) = 2 G(S) is the least number of defect units of any decoration of S,
and n2*(S) = nu_2 - nu_1 the number of doubly decorated sites in a decoration that attains it.
main: the values of Section 8 that are used as a test."""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching
ROOTS = [(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]
add = lambda a, b: (a[0] + b[0], a[1] + b[1], a[2] + b[2])

def octa(n, c=(0, 0, 0)):
    """regular octahedron with n sites per edge centred at c; c must have the parity that makes the vertices lattice sites"""
    m = n - 1
    return {(c[0] + x, c[1] + y, c[2] + z) for x in range(-m, m + 1) for y in range(-m + abs(x), m - abs(x) + 1)
            for z in range(-m + abs(x) + abs(y), m - abs(x) - abs(y) + 1, 2)}

def tetra(k):
    return {(b + c, a + c, a + b) for a in range(k) for b in range(k - a) for c in range(k - a - b)}

def cost(S):
    """returns dict with U (= 2G), n2, nu1, nu2, boundary, surface, coat"""
    surf = []; coat = {}; rows = []; cols = []; bd = 0
    for h in S:
        nb = [g for g in (add(h, r) for r in ROOTS) if g not in S]
        if not nb: continue
        i = len(surf); surf.append(h); bd += len(nb)
        for g in nb:
            j = coat.setdefault(g, len(coat)); rows.append(i); cols.append(j)
    ns, nc = len(surf), len(coat)
    rows = np.array(rows); cols = np.array(cols); data = np.ones(len(rows), dtype=np.int8)
    m1 = maximum_bipartite_matching(csr_matrix((data, (rows, cols)), shape=(ns, nc)), perm_type='column')
    nu1 = int((m1 >= 0).sum())
    m2 = maximum_bipartite_matching(csr_matrix((np.concatenate([data, data]), (np.concatenate([rows, rows + ns]), np.concatenate([cols, cols]))), shape=(2 * ns, nc)), perm_type='column')
    nu2 = int((m2 >= 0).sum())
    return dict(U=2 * bd - 3 * (nu1 + nu2), n2=nu2 - nu1, nu1=nu1, nu2=nu2, boundary=bd, surface=ns, coat=nc, size=len(S))

def connected(S):
    S = set(S); start = next(iter(S)); seen = {start}; stack = [start]
    while stack:
        h = stack.pop()
        for r in ROOTS:
            g = add(h, r)
            if g in S and g not in seen: seen.add(g); stack.append(g)
    return len(seen) == len(S)

if __name__ == '__main__':
    show = lambda name, S, want: print(f"{name}: cost G = {cost(S)['U'] / 2} (note: {want})")
    show("single site", {(0, 0, 0)}, 7.5)
    for n, w in ((3, 27), (4, 21), (5, 9), (6, 9), (8, 9)): show(f"O_{n}", octa(n), w)
    for k in (5, 9): show(f"tetrahedron, {k} per edge", tetra(k), 3 * k + 12)
    for v, w in (((1, 1, 0), 10), ((2, 2, 2), 12), ((1, 1, 2), 11), ((2, 2, 0), 17)): show(f"O_7 with its translate by {v}", octa(7) | octa(7, v), w)
    for k in (2, 3, 4, 5): show(f"two O_7 at offset {2*k} along an axis", octa(7) | octa(7, (2 * k, 0, 0)), '27 for offsets 4..10')
    show("two O_7 tip to tip (offset 12)", octa(7) | octa(7, (12, 0, 0)), 25.5)
    show("two O_7 at offset 2", octa(7) | octa(7, (2, 0, 0)), 21)
```

## `scan2.py`

```python
"""Section 42 of the note: all unions of two regular octahedra O_a and O_b + v that are connected (overlapping or with
adjacent sites), v up to symmetry.  For each: overlap, U* = 2G, n2*, and n2* against the capacity 16 (3N/2)^(1/3) of
one octahedron of the same size.  Conjecture R (sharp form) forbids U* <= 36 for a body made of two large lumps."""
import sys
from gmin import *
a, b = int(sys.argv[1]), int(sys.argv[2]); A = octa(a); rows = []
R = a + b
for x in range(0, R + 1):
    for y in range(0, x + 1):
        for z in range(0, y + 1):
            if (x + y + z - (a - b)) % 2: continue
            B = octa(b, (x, y, z)); S = A | B
            if len(A & B) == min(len(A), len(B)): continue          # one inside the other
            if not connected(S): continue
            c = cost(S); N = len(S)
            rows.append((c['U'], len(A & B), (x, y, z), c['n2'], N, c['n2'] / (16 * (1.5 * N) ** (1 / 3))))
rows.sort()
small = min(len(A), len(B))
print(f"O_{a} and O_{b}: {len(rows)} connected unions up to symmetry")
for frac, name in ((0.0, 'no overlap (touching)'), (0.1, 'overlap at most 10% of the smaller'), (0.5, 'overlap at most 50%'), (1.0, 'any overlap')):
    sel = [r for r in rows if r[1] <= frac * small]
    if sel:
        best = sel[0]
        print(f"  {name}: {len(sel)} unions, least U* = {best[0]} at v = {best[2]} (overlap {best[1]}, n2* = {best[3]}, ratio to one-octahedron capacity {best[5]:.2f})")
print("  all unions with U* <= 36:")
for r in rows:
    if r[0] <= 36: print(f"    v = {r[2]}: U* = {r[0]}, overlap {r[1]} of {small}, n2* = {r[3]}, N = {r[4]}, ratio {r[5]:.2f}")
viol = [r for r in rows if r[0] <= 36 and r[5] > 1.0]
print(f"  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: {len(viol)}; largest ratio among U* <= 36: {max(r[5] for r in rows if r[0] <= 36):.3f}")
```

## `psi.py`

```python
"""Section 42 of the note: search for a body that breaks Conjecture R, in the form in which soundness uses it.

For a finite set S: U*(S) = least number of defect units (gmin.cost), X3(S) = sum over the three coordinate axes of
the Euler characteristics of the slices of S (Section 9), and

      K(S) = sqrt( (X3 + 3)^3 / (9 |S|) ),          Psi(S) = U*(S) / 3 - K(S).

K is the number of pyramids, over the six directions, that S is worth: for k_a equal pyramids along axis a,
X_a = (3 k_a^2 |S|)^(1/3) to leading order, and K is the sum of the k_a when they are equal; unequal pyramids give
less (Hoelder).  For O_n: X3 + 3 = 6n and K = 6 (1 + 1/(2 n^2))^(-1/2), so Psi is just above 0.
Conjecture R (A1 and A2) with Proposition 29 gives K <= (U - 1)/3 up to lower order terms for every body that is not
a regular octahedron, that is Psi >= 1/3.  A family with Psi < 0 that persists as the bodies grow would refute it.

  python3 psi.py scan a b            all connected unions O_a | (O_b + v): Psi, least values
  python3 psi.py search a b steps [f]   from O_a alone and from every such union whose overlap is at most the fraction f
                                     (default 1) of the smaller octahedron: descent on Psi by single sites (any site
                                     of the surface may go, any site of the coat may come), then annealing
"""
import sys, math, random
from gmin import *

def x3(S):
    tot = 0
    for ax in range(3):
        o = [i for i in range(3) if i != ax]; sl = {}
        for h in S: sl.setdefault(h[ax], set()).add((h[o[0]], h[o[1]]))
        for sq in sl.values():
            e = sum(1 for u, v in sq for d in ((1, 1), (1, -1)) if (u + d[0], v + d[1]) in sq)
            f = sum(1 for u, v in sq if (u + 1, v + 1) in sq and (u + 1, v - 1) in sq and (u + 2, v) in sq)
            tot += len(sq) - e + f
    return tot

def K(S): return math.sqrt((x3(S) + 3) ** 3 / (9 * len(S)))

def psi(S, c=None):
    if c is None: c = cost(S)
    return c['U'] / 3 - K(S)

def unions(a, b):
    A = octa(a)
    for x in range(0, a + b + 1):
        for y in range(0, x + 1):
            for z in range(0, y + 1):
                if (x + y + z - (a - b)) % 2: continue
                B = octa(b, (x, y, z)); S = A | B
                if len(A & B) == min(len(A), len(B)) or not connected(S): continue
                yield (x, y, z), len(A & B), S

def boundary_moves(S):
    out = set()
    for h in S:
        for s in ROOTS:
            g = add(h, s)
            if g not in S: out.add(g); out.add(h)
    return list(out)

def toggle(S, h):
    T = set(S); T.symmetric_difference_update({h}); return T

def descend(S, rng, cap=400):
    """first-improvement descent on Psi over single sites, in random order"""
    cur = psi(S); n = 0
    while n < cap:
        mv = boundary_moves(S); rng.shuffle(mv); done = True
        for h in mv:
            T = toggle(S, h)
            if len(T) < 2 or (h in S and not connected(T)): continue
            u = psi(T)
            if u < cur - 1e-9: S, cur, done = T, u, False; n += 1; break
        if done: break
    return S, cur

def anneal(S, steps, rng, T0=0.5):
    cur = psi(S); best = (cur, S); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.02
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = psi(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur < best[0]: best = (cur, S)
    return best

def is_octa(S):
    for n in range(1, 40):
        if len(octa(n)) == len(S):
            c = tuple(sum(h[i] for h in S) / len(S) for i in range(3))
            if all(abs(v - round(v)) < 1e-9 for v in c): return octa(n, tuple(int(round(v)) for v in c)) == set(S)
        if len(octa(n)) > len(S): return False

def line(S):
    c = cost(S); return f"N = {len(S)}, U* = {c['U']}, X3 = {x3(S)}, K = {K(S):.3f}, Psi = {psi(S, c):+.3f}"

if __name__ == '__main__':
    mode, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if mode == 'scan':
        for n in sorted({a, b}): print(f"O_{n}: {line(octa(n))}")
        rows = []
        for v, ov, S in unions(a, b):
            c = cost(S); rows.append((psi(S, c), c['U'], v, ov, len(S), x3(S)))
        rows.sort()
        print(f"O_{a} and O_{b}: {len(rows)} connected unions up to symmetry; least Psi {rows[0][0]:+.3f}; unions with Psi < 1/3: {sum(1 for r in rows if r[0] < 1 / 3)}; with Psi < 0: {sum(1 for r in rows if r[0] < 0)}")
        for r in rows[:8]: print(f"   v = {r[2]}: overlap {r[3]}, N = {r[4]}, U* = {r[1]}, X3 = {r[5]}, K = {r[1] / 3 - r[0]:.3f}, Psi = {r[0]:+.3f}")
        t = [r for r in rows if r[3] == 0]
        if t: print(f"   touching only: least Psi {t[0][0]:+.3f} at v = {t[0][2]} (U* = {t[0][1]}, K = {t[0][1] / 3 - t[0][0]:.3f})")
    else:
        steps = int(sys.argv[4]); rng = random.Random(5); res = []; frac = float(sys.argv[5]) if len(sys.argv) > 5 else 1.0
        small = min(len(octa(a)), len(octa(b)))
        starts = [('O_%d alone' % a, octa(a))] + [(f"v = {v}, overlap {ov}", S) for v, ov, S in unions(a, b) if ov <= frac * small]
        for name, S in starts:
            p0 = psi(S); S1, p1 = descend(S, rng)
            if steps:
                p2, S2 = anneal(S1, steps, rng); S2, p2 = descend(S2, rng)
                if p2 < p1: S1, p1 = S2, p2
            oc = is_octa(S1); res.append((p1, name, oc, S1))
            print(f"{name}: Psi at start {p0:+.3f}; after search {p1:+.3f} ({line(S1)}; added {len(S1 - S)}, removed {len(S - S1)}{'; a regular octahedron' if oc else ''})", flush=True)
        non = [r for r in res if not r[2]]
        print(f"O_{a}, O_{b}, {steps} annealing steps: {len(res)} starts; ended at a regular octahedron: {len(res) - len(non)}; "
              f"least Psi among the others: {min(r[0] for r in non):+.3f}; ends with Psi < 1/3 that are not regular octahedra: {sum(1 for r in non if r[0] < 1 / 3)}; with Psi < 0: {sum(1 for r in non if r[0] < 0)}")
        import pickle; pickle.dump([(r[0], r[1], r[2], sorted(r[3])) for r in res], open(f"out/psi_{a}_{b}_{steps}.pkl", 'wb'))
```

## `lgeo.py`

```python
"""Section 42 of the note: a geometric count of long chains, for the search for a counterexample to Conjecture R.

Fix an axis direction.  The slice of the body S at level l splits into pieces (components under the four in-plane
steps).  For a piece p, D(p) is the set of the lower neighbours of its sites (four per site).  Write p -> p' if
p' = D(p) and p' is a whole piece of the next slice: p' grows out of p exactly as the slices of the upper half of a
regular octahedron do.  A geometric chain is a maximal sequence p_1 -> p_2 -> ... -> p_k; it is long if k - 1 > J.
L(S, J) = number of long geometric chains over the six directions.  For O_n and J < n - 1 this is 6.
(This is a stand-in for the chains of Section 12, which need a decoration: an exact dilation step is what a regular
growing piece with one parent looks like.  A body with 3 L(S, J) > U*(S) for J large would contradict Conjecture R.
Chains whose first piece is not a local top are the ones Theorem 36 does not pay for.)"""
from gmin import *

def chains(S, J):
    """list of (axis, sign, top level, steps, top) of the long geometric chains; top says whether the first piece is a
    local top (no site of it has an occupied neighbour in the slice above)"""
    out = []
    for ax in range(3):
        o = [i for i in range(3) if i != ax]
        for sg in (1, -1):
            sl = {}
            for h in S: sl.setdefault(sg * h[ax], set()).add((h[o[0]], h[o[1]]))
            comp = {}                                              # level -> list of pieces (frozensets)
            for l, sq in sl.items():
                seen = set(); ps = []
                for s in sq:
                    if s in seen: continue
                    c = {s}; st = [s]; seen.add(s)
                    while st:
                        u, v = st.pop()
                        for du, dv in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                            t = (u + du, v + dv)
                            if t in sq and t not in seen: seen.add(t); c.add(t); st.append(t)
                    ps.append(frozenset(c))
                comp[l] = ps
            nxt = {}; has_pred = set()
            for l, ps in comp.items():
                below = set(comp.get(l - 1, []))
                for p in ps:
                    d = frozenset(t for u, v in p for t in ((u + 1, v), (u - 1, v), (u, v + 1), (u, v - 1)))
                    if d in below: nxt[(l, p)] = (l - 1, d); has_pred.add((l - 1, d))
            for l, ps in comp.items():
                for p in ps:
                    if (l, p) in has_pred or (l, p) not in nxt: continue
                    k = 0; cur = (l, p)
                    while cur in nxt: cur = nxt[cur]; k += 1
                    if k > J:
                        up = sl.get(l + 1, ())
                        top = not any(t in up for u, v in p for t in ((u + 1, v), (u - 1, v), (u, v + 1), (u, v - 1)))
                        out.append((ax, sg, l, k, top))
    return out

def L(S, J): return len(chains(S, J))

if __name__ == '__main__':
    import time
    for n in (5, 6, 7, 8):
        S = octa(n); t = time.time(); c = chains(S, 3)
        print(f"O_{n}: U* = {cost(S)['U']}, long geometric chains (J = 3): {len(c)}, steps {sorted(x[3] for x in c)}  [{time.time() - t:.3f} s]")
    for n, v in ((7, (13, 1, 0)), (7, (12, 2, 0)), (7, (8, 3, 3)), (7, (5, 4, 3)), (7, (2, 2, 2)), (7, (1, 1, 0)), (7, (3, 3, 0)), (7, (6, 0, 0)), (7, (12, 0, 0)),
                 (9, (2, 2, 2)), (9, (17, 1, 0))):
        S = octa(n) | octa(n, v); c = chains(S, 3); u = cost(S)['U']
        print(f"O_{n} + translate by {v}: U* = {u}, long geometric chains (J = 3): {len(c)}, of which not from a local top {sum(1 for x in c if not x[4])}, U* - 3 L = {u - 3 * len(c)}, steps {sorted(x[3] for x in c)}")
    for k in (6, 9):
        S = tetra(k); print(f"tetrahedron of side {k}: U* = {cost(S)['U']}, long geometric chains (J = 3): {L(S, 3)}")
```

## `lscan.py`

```python
"""Section 42 of the note: long geometric chains (lgeo.py) against U* on every connected union of two regular octahedra."""
from gmin import *
from psi import unions
from lgeo import chains
for a, b, J in ((7, 7, 2), (9, 9, 3), (5, 8, 2), (6, 9, 2)):
    rows = []
    for v, ov, S in unions(a, b):
        ch = chains(S, J); rows.append((cost(S)['U'] - 3 * len(ch), v, ov, sum(1 for x in ch if not x[4])))
    m = min(rows); nt = [r for r in rows if r[3] > 0]
    print(f"O_{a}, O_{b}, J = {J}: {len(rows)} unions; least U* - 3 L = {m[0]} at v = {m[1]} (overlap {m[2]}); unions with 3 L > U*: {sum(1 for r in rows if r[0] < 0)}; "
          f"unions with a long chain that does not start at a local top: {len(nt)}" + (f", among them least U* - 3 L = {min(nt)[0]} at v = {min(nt)[1]}" if nt else ""))
```

## `price.py`

```python
"""Section 42 of the note: the price of a pyramid.  Over all connected unions of two regular octahedra with K > 6.1,
the least value of (U* - 18) / (K - 6): units paid per pyramid beyond the six of one octahedron.  Conjecture R needs 3."""
from gmin import *
from psi import unions, K
for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
    rows = []
    for v, ov, S in unions(a, b):
        k = K(S); u = cost(S)['U']
        if k > 6.1: rows.append(((u - 18) / (k - 6), u, k, v, ov))
    rows.sort(); ovl = [r for r in rows if r[4] > 0]
    print(f"O_{a}, O_{b}: {len(rows)} unions with K > 6.1; least price {rows[0][0]:.2f} at v = {rows[0][3]} (overlap {rows[0][4]}, U* = {rows[0][1]}, K = {rows[0][2]:.2f}); "
          f"least price among overlapping unions {ovl[0][0]:.2f} at v = {ovl[0][3]} (overlap {ovl[0][4]}, U* = {ovl[0][1]}, K = {ovl[0][2]:.2f})")
```

## `near.py`

```python
"""Section 42 of the note: bodies next to a regular octahedron.  All bodies that differ from O_n in one site, and (with
argument 2) in two sites: least U*, least Psi.  The sharp case A2 of Conjecture R asks for U* >= 19 and, to leading
order, Psi >= 1/3 for every body that is not a regular octahedron.     python3 near.py n [2]"""
import sys, itertools
from gmin import *
from psi import psi, boundary_moves, toggle, K, x3
n = int(sys.argv[1]); two = len(sys.argv) > 2
S = octa(n); mv = sorted(boundary_moves(S)); rows = []
for h in mv:
    T = toggle(S, h)
    if h in S and not connected(T): continue
    c = cost(T); rows.append((psi(T, c), c['U'], 'removed' if h in S else 'added', h))
rows.sort()
print(f"O_{n}: {len(rows)} bodies at one site from it; least U* = {min(r[1] for r in rows)}; least Psi = {rows[0][0]:+.3f} "
      f"({rows[0][2]} {rows[0][3]}, U* = {rows[0][1]}); bodies with U* <= 18: {sum(1 for r in rows if r[1] <= 18)}; with Psi < 1/3: {sum(1 for r in rows if r[0] < 1/3)}")
if two:
    best = None; cnt = 0; low = 0; umin = 99
    for h, g in itertools.combinations(mv, 2):
        T = toggle(toggle(S, h), g)
        if not connected(T): continue
        c = cost(T); p = psi(T, c); cnt += 1; umin = min(umin, c['U'])
        if p < 1/3: low += 1
        if best is None or p < best[0]: best = (p, c['U'], h, g)
    print(f"O_{n}: {cnt} connected bodies at two sites from it; least U* = {umin}; least Psi = {best[0]:+.3f} (sites {best[2]}, {best[3]}, U* = {best[1]}); with Psi < 1/3: {low}")
```

## `junction.py`

```python
"""Section 42 of the note: search for a cheap junction between two lumps.
Start: O_a and O_b + v, touching or overlapping in at most 10% of the smaller one.  Only sites within graph distance r
of the contact (sites of one octahedron that lie in, or next to, the other) may be added or removed; the body must stay
connected.  Steepest descent on U* = 2G (gmin.cost), then simulated annealing from the result and a second descent.
The excess of a body is n2* - 16 (3N/2)^(1/3): what it holds beyond one octahedron of its size.  Without a guard the
search wins by filling the gap until the two lumps are one (U* 28 and 30 for O_6, O_6, with negative excess), so the
score adds a penalty when the excess falls below 0.4 times the excess of the two lumps apart.
The sharp form of the capacity bound L4 says: no connected body has U* <= 36 and an excess that grows with its size.
    python3 junction.py a b r [annealing steps]"""
import sys, random, math
from gmin import *

def region(A, B, r):
    K = {h for h in A if h in B or any(add(h, s) in B for s in ROOTS)} | {h for h in B if any(add(h, s) in A for s in ROOTS)}
    M = set(K); front = set(K)
    for _ in range(r):
        front = {add(h, s) for h in front for s in ROOTS} - M; M |= front
    return M

def moves(S, M):
    out = []
    for h in M:
        if h in S: out.append(h)
        elif any(add(h, s) in S for s in ROOTS): out.append(h)
    return out

def toggle(S, h):
    T = set(S); T.symmetric_difference_update({h}); return T

EMIN = 0.0
def excess(c):
    """doubly decorated sites beyond the capacity 16 (3N/2)^(1/3) of one octahedron with as many sites"""
    return c['n2'] - 16 * (1.5 * c['size']) ** (1 / 3)

def score(S):
    """U*, plus a penalty when the excess falls below EMIN (so that the search cannot win by fusing the two lumps)"""
    c = cost(S); return c['U'] + 2 * max(0.0, EMIN - excess(c))

def descend(S, M):
    cur = score(S)
    while True:
        best = None
        for h in moves(S, M):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            u = score(T)
            if u < cur and (best is None or u < best[0]): best = (u, T)
        if best is None: return S, cur
        cur, S = best

def anneal(S, M, steps, rng, T0=2.0):
    cur = score(S); best = (cur, S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.05
        h = rng.choice(moves(S, M)); S2 = toggle(S, h)
        if h in S and not connected(S2): continue
        u = score(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u
            if cur < best[0]: best = (cur, S)
    return best

if __name__ == '__main__':
    a, b, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); steps = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = random.Random(11); A = octa(a); B0 = octa(b); small = min(len(A), len(B0)); res = []
    sep = cost(A)['n2'] + cost(B0)['n2'] - 16 * (1.5 * (len(A) + len(B0))) ** (1 / 3)      # excess of the two lumps apart
    import junction; junction.EMIN = 0.4 * sep
    print(f"O_{a}, O_{b}: apart, the two lumps have U* = 36 and excess {sep:.1f}; the search keeps the excess above {0.4 * sep:.1f}", flush=True)
    for x in range(0, a + b + 1):
        for y in range(0, x + 1):
            for z in range(0, y + 1):
                if (x + y + z - (a - b)) % 2: continue
                B = octa(b, (x, y, z)); S = A | B
                if len(A & B) > 0.1 * small or not connected(S): continue
                M = region(A, B, r); c0 = cost(S)
                S1, f1 = junction.descend(S, M)
                if steps:
                    f2, S2 = junction.anneal(S1, M, steps, rng); S2, f2 = junction.descend(S2, M)
                    if f2 < f1: S1, f1 = S2, f2
                c = cost(S1)
                res.append((c['U'], excess(c), (x, y, z), len(A & B), len(S1 - S), len(S - S1), c0['U'], excess(c0)))
                print(f"v = {(x, y, z)}: overlap {len(A & B)}; start U* {c0['U']}, excess {excess(c0):.1f}; after search U* {c['U']}, excess {excess(c):.1f} (added {len(S1 - S)}, removed {len(S - S1)})", flush=True)
    res.sort()
    bad = [x for x in res if x[0] <= 36 and x[1] > 0]
    print(f"O_{a}, O_{b}, radius {r}, annealing steps {steps}: {len(res)} starts; least U* with excess above the bound: {min(x[0] for x in res if x[1] >= 0.4 * sep - 1e-9) if any(x[1] >= 0.4 * sep - 1e-9 for x in res) else None}; "
          f"bodies with U* <= 36 and positive excess: {len(bad)}")
    for x in bad: print("   ALARM", x)
```

## `roof.py`

```python
"""Section 42 of the note: bodies with a roof.  O_N at the origin and two legs O_n + (a, b, -c), O_n + (-a, -b, -c) below it.
Seen from above, the slices of the roof shrink and those of the legs grow: where the legs come apart below the roof,
two growing sequences start that do not start at a local top.  This is the case of Conjecture R without an argument.
For every connected body of the family: U*, K and Psi (psi.py), and L = number of long geometric chains (lgeo.py).
Alarm: Psi < 0, or 3 L > U*.        python3 roof.py N n J"""
import sys
from gmin import *
from psi import x3, K, psi
from lgeo import chains

N, n, J = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
A = octa(N); rows = []
for a in range(0, N + n + 1):
    for b in range(0, 3):
        for c in range(0, N + n + 1):
            if (a + b + c - (N - n)) % 2: continue
            B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); S = A | B1 | B2
            if not connected(S): continue
            if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue      # a leg mostly swallowed
            co = cost(S); ch = chains(S, J)
            below = [x for x in ch if x[0] == 2 and x[1] == 1]                          # chains seen from above
            rows.append((psi(S, co), co['U'], len(ch), len(below), (a, b, c), len(S), K(S), sum(1 for x in ch if not x[4]), sum(1 for x in below if not x[4])))
rows.sort()
print(f"roof O_{N}, legs O_{n}, J = {J}: {len(rows)} connected bodies")
print(f"   least Psi: {rows[0][0]:+.3f} at (a, b, c) = {rows[0][4]} (U* = {rows[0][1]}, K = {rows[0][6]:.2f}, long chains {rows[0][2]})")
m = max(rows, key=lambda r: 3 * r[2] - r[1])
print(f"   largest 3 L - U*: {3 * m[2] - m[1]} at (a, b, c) = {m[4]} (U* = {m[1]}, long chains {m[2]}, of which seen from above {m[3]}, Psi = {m[0]:+.3f})")
sp = [r for r in rows if r[3] >= 3]
print(f"   bodies with three long chains seen from above (roof and both legs): {len(sp)}" + (f"; among them least U* = {min(r[1] for r in sp)}, least U* - 3 L = {min(r[1] - 3 * r[2] for r in sp)}, least Psi = {min(r[0] for r in sp):+.3f}" if sp else ""))
nt = [r for r in rows if r[7] > 0]
print(f"   bodies with a long chain that does not start at a local top: {len(nt)}" + (f"; among them least U* - 3 L = {min(r[1] - 3 * r[2] for r in nt)}, largest number of such chains {max(r[7] for r in nt)}" if nt else ""))
u2 = [r for r in rows if r[8] >= 2]
print(f"   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): {len(u2)}" + (f"; among them least U* = {min(r[1] for r in u2)}, least U* - 3 L = {min(r[1] - 3 * r[2] for r in u2)}" if u2 else ""))
for r in sorted(u2, key=lambda r: r[1] - 3 * r[2])[:3]:
    print(f"      under the roof: (a, b, c) = {r[4]}: N = {r[5]}, U* = {r[1]}, long chains {r[2]} ({r[7]} not from a top), U* - 3 L = {r[1] - 3 * r[2]}, Psi = {r[0]:+.3f}")
print(f"   alarms (Psi < 0 or 3 L > U*): {sum(1 for r in rows if r[0] < 0 or 3 * r[2] > r[1])}")
for r in sorted(rows, key=lambda r: r[1] - 3 * r[2])[:5]:
    print(f"      (a, b, c) = {r[4]}: N = {r[5]}, U* = {r[1]}, long chains {r[2]} ({r[3]} from above), U* - 3 L = {r[1] - 3 * r[2]}, K = {r[6]:.2f}, Psi = {r[0]:+.3f}")
```

## Output of `python3 gmin.py`

```
single site: cost G = 7.5 (note: 7.5)
O_3: cost G = 27.0 (note: 27)
O_4: cost G = 21.0 (note: 21)
O_5: cost G = 9.0 (note: 9)
O_6: cost G = 9.0 (note: 9)
O_8: cost G = 9.0 (note: 9)
tetrahedron, 5 per edge: cost G = 27.0 (note: 27)
tetrahedron, 9 per edge: cost G = 39.0 (note: 39)
O_7 with its translate by (1, 1, 0): cost G = 10.0 (note: 10)
O_7 with its translate by (2, 2, 2): cost G = 12.0 (note: 12)
O_7 with its translate by (1, 1, 2): cost G = 11.0 (note: 11)
O_7 with its translate by (2, 2, 0): cost G = 17.0 (note: 17)
two O_7 at offset 4 along an axis: cost G = 27.0 (note: 27 for offsets 4..10)
two O_7 at offset 6 along an axis: cost G = 27.0 (note: 27 for offsets 4..10)
two O_7 at offset 8 along an axis: cost G = 27.0 (note: 27 for offsets 4..10)
two O_7 at offset 10 along an axis: cost G = 27.0 (note: 27 for offsets 4..10)
two O_7 tip to tip (offset 12): cost G = 25.5 (note: 25.5)
two O_7 at offset 2: cost G = 21.0 (note: 21)
```

## Output of `python3 scan2.py 7 7`

```
O_7 and O_7: 79 connected unions up to symmetry
  no overlap (touching): 23 unions, least U* = 44 at v = (13, 1, 0) (overlap 0, n2* = 184, ratio to one-octahedron capacity 1.30)
  overlap at most 10% of the smaller: 50 unions, least U* = 44 at v = (13, 1, 0) (overlap 0, n2* = 184, ratio to one-octahedron capacity 1.30)
  overlap at most 50%: 75 unions, least U* = 24 at v = (2, 2, 2) (overlap 104, n2* = 112, ratio to one-octahedron capacity 0.86)
  any overlap: 79 unions, least U* = 20 at v = (1, 1, 0) (overlap 182, n2* = 100, ratio to one-octahedron capacity 0.83)
  all unions with U* <= 36:
    v = (1, 1, 0): U* = 20, overlap 182 of 231, n2* = 100, N = 280, ratio 0.83
    v = (2, 1, 1): U* = 22, overlap 140 of 231, n2* = 106, N = 322, ratio 0.84
    v = (2, 2, 2): U* = 24, overlap 104 of 231, n2* = 112, N = 358, ratio 0.86
    v = (2, 2, 0): U* = 34, overlap 135 of 231, n2* = 106, N = 327, ratio 0.84
    v = (3, 3, 0): U* = 36, overlap 92 of 231, n2* = 116, N = 370, ratio 0.88
    v = (3, 2, 1): U* = 36, overlap 100 of 231, n2* = 112, N = 362, ratio 0.86
  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: 0; largest ratio among U* <= 36: 0.882
```

## Output of `python3 scan2.py 9 9`

```
O_9 and O_9: 146 connected unions up to symmetry
  no overlap (touching): 36 unions, least U* = 44 at v = (17, 1, 0) (overlap 0, n2* = 248, ratio to one-octahedron capacity 1.36)
  overlap at most 10% of the smaller: 90 unions, least U* = 44 at v = (17, 1, 0) (overlap 0, n2* = 248, ratio to one-octahedron capacity 1.36)
  overlap at most 50%: 138 unions, least U* = 38 at v = (4, 3, 1) (overlap 200, n2* = 154, ratio to one-octahedron capacity 0.91)
  any overlap: 146 unions, least U* = 20 at v = (1, 1, 0) (overlap 408, n2* = 132, ratio to one-octahedron capacity 0.87)
  all unions with U* <= 36:
    v = (1, 1, 0): U* = 20, overlap 408 of 489, n2* = 132, N = 570, ratio 0.87
    v = (2, 1, 1): U* = 22, overlap 336 of 489, n2* = 138, N = 642, ratio 0.87
    v = (2, 2, 2): U* = 24, overlap 272 of 489, n2* = 144, N = 706, ratio 0.88
    v = (2, 2, 0): U* = 34, overlap 329 of 489, n2* = 138, N = 649, ratio 0.87
    v = (3, 3, 0): U* = 36, overlap 254 of 489, n2* = 148, N = 724, ratio 0.90
    v = (3, 2, 1): U* = 36, overlap 266 of 489, n2* = 144, N = 712, ratio 0.88
  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: 0; largest ratio among U* <= 36: 0.900
```

## Output of `python3 scan2.py 5 8`

```
O_5 and O_8: 61 connected unions up to symmetry
  no overlap (touching): 20 unions, least U* = 44 at v = (12, 1, 0) (overlap 0, n2* = 168, ratio to one-octahedron capacity 1.22)
  overlap at most 10% of the smaller: 30 unions, least U* = 44 at v = (12, 1, 0) (overlap 0, n2* = 168, ratio to one-octahedron capacity 1.22)
  overlap at most 50%: 53 unions, least U* = 34 at v = (5, 1, 1) (overlap 40, n2* = 118, ratio to one-octahedron capacity 0.88)
  any overlap: 61 unions, least U* = 21 at v = (2, 2, 1) (overlap 70, n2* = 111, ratio to one-octahedron capacity 0.85)
  all unions with U* <= 36:
    v = (2, 2, 1): U* = 21, overlap 70 of 85, n2* = 111, N = 359, ratio 0.85
    v = (3, 1, 1): U* = 21, overlap 70 of 85, n2* = 111, N = 359, ratio 0.85
    v = (4, 1, 0): U* = 26, overlap 60 of 85, n2* = 114, N = 369, ratio 0.87
    v = (3, 2, 0): U* = 32, overlap 60 of 85, n2* = 112, N = 369, ratio 0.85
    v = (5, 1, 1): U* = 34, overlap 40 of 85, n2* = 118, N = 389, ratio 0.88
    v = (4, 2, 1): U* = 35, overlap 46 of 85, n2* = 115, N = 383, ratio 0.86
  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: 0; largest ratio among U* <= 36: 0.883
```

## Output of `python3 scan2.py 6 9`

```
O_6 and O_9: 88 connected unions up to symmetry
  no overlap (touching): 26 unions, least U* = 44 at v = (14, 1, 0) (overlap 0, n2* = 200, ratio to one-octahedron capacity 1.27)
  overlap at most 10% of the smaller: 45 unions, least U* = 44 at v = (14, 1, 0) (overlap 0, n2* = 200, ratio to one-octahedron capacity 1.27)
  overlap at most 50%: 77 unions, least U* = 37 at v = (5, 2, 2) (overlap 61, n2* = 139, ratio to one-octahedron capacity 0.91)
  any overlap: 88 unions, least U* = 21 at v = (2, 2, 1) (overlap 125, n2* = 127, ratio to one-octahedron capacity 0.87)
  all unions with U* <= 36:
    v = (2, 2, 1): U* = 21, overlap 125 of 146, n2* = 127, N = 510, ratio 0.87
    v = (3, 1, 1): U* = 21, overlap 125 of 146, n2* = 127, N = 510, ratio 0.87
    v = (4, 1, 0): U* = 26, overlap 110 of 146, n2* = 130, N = 525, ratio 0.88
    v = (3, 2, 0): U* = 32, overlap 110 of 146, n2* = 128, N = 525, ratio 0.87
    v = (5, 1, 1): U* = 34, overlap 80 of 146, n2* = 134, N = 555, ratio 0.89
    v = (4, 2, 1): U* = 35, overlap 90 of 146, n2* = 131, N = 545, ratio 0.88
  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: 0; largest ratio among U* <= 36: 0.890
```

## Output of `python3 psi.py scan 7 7`

```
O_7: N = 231, U* = 18, X3 = 39, K = 5.970, Psi = +0.030
O_7 and O_7: 79 connected unions up to symmetry; least Psi +0.853; unions with Psi < 1/3: 0; with Psi < 0: 0
   v = (1, 1, 0): overlap 182, N = 280, U* = 20, X3 = 41, K = 5.814, Psi = +0.853
   v = (2, 1, 1): overlap 140, N = 322, U* = 22, X3 = 43, K = 5.795, Psi = +1.538
   v = (2, 2, 2): overlap 104, N = 358, U* = 24, X3 = 45, K = 5.859, Psi = +2.141
   v = (13, 1, 0): overlap 0, N = 462, U* = 44, X3 = 77, K = 11.097, Psi = +3.570
   v = (12, 1, 1): overlap 0, N = 462, U* = 46, X3 = 73, K = 10.275, Psi = +5.058
   v = (2, 2, 0): overlap 135, N = 327, U* = 34, X3 = 45, K = 6.130, Psi = +5.203
   v = (3, 3, 0): overlap 92, N = 370, U* = 36, X3 = 49, K = 6.498, Psi = +5.502
   v = (3, 2, 1): overlap 100, N = 362, U* = 36, X3 = 47, K = 6.194, Psi = +5.806
   touching only: least Psi +3.570 at v = (13, 1, 0) (U* = 44, K = 11.097)
```

## Output of `python3 psi.py scan 9 9`

```
O_9: N = 489, U* = 18, X3 = 51, K = 5.982, Psi = +0.018
O_9 and O_9: 146 connected unions up to symmetry; least Psi +0.816; unions with Psi < 1/3: 0; with Psi < 0: 0
   v = (1, 1, 0): overlap 408, N = 570, U* = 20, X3 = 53, K = 5.851, Psi = +0.816
   v = (2, 1, 1): overlap 336, N = 642, U* = 22, X3 = 55, K = 5.811, Psi = +1.522
   v = (2, 2, 2): overlap 272, N = 706, U* = 24, X3 = 57, K = 5.830, Psi = +2.170
   v = (17, 1, 0): overlap 0, N = 978, U* = 44, X3 = 101, K = 11.305, Psi = +3.362
   v = (16, 1, 1): overlap 0, N = 978, U* = 46, X3 = 97, K = 10.659, Psi = +4.675
   v = (2, 2, 0): overlap 329, N = 649, U* = 34, X3 = 57, K = 6.081, Psi = +5.252
   v = (14, 1, 1): overlap 4, N = 974, U* = 46, X3 = 91, K = 9.734, Psi = +5.599
   v = (3, 3, 0): overlap 254, N = 724, U* = 36, X3 = 61, K = 6.343, Psi = +5.657
   touching only: least Psi +3.362 at v = (17, 1, 0) (U* = 44, K = 11.305)
```

## Output of `python3 psi.py scan 5 8`

```
O_5: N = 85, U* = 18, X3 = 27, K = 5.941, Psi = +0.059
O_8: N = 344, U* = 18, X3 = 45, K = 5.977, Psi = +0.023
O_5 and O_8: 61 connected unions up to symmetry; least Psi +1.149; unions with Psi < 1/3: 0; with Psi < 0: 0
   v = (2, 2, 1): overlap 70, N = 359, U* = 21, X3 = 45, K = 5.851, Psi = +1.149
   v = (3, 1, 1): overlap 70, N = 359, U* = 21, X3 = 45, K = 5.851, Psi = +1.149
   v = (4, 1, 0): overlap 60, N = 369, U* = 26, X3 = 47, K = 6.135, Psi = +2.532
   v = (12, 1, 0): overlap 0, N = 429, U* = 44, X3 = 71, K = 10.245, Psi = +4.422
   v = (3, 2, 0): overlap 60, N = 369, U* = 32, X3 = 47, K = 6.135, Psi = +4.532
   v = (5, 1, 1): overlap 40, N = 389, U* = 34, X3 = 49, K = 6.337, Psi = +4.996
   v = (4, 2, 1): overlap 46, N = 383, U* = 35, X3 = 48, K = 6.203, Psi = +5.463
   v = (5, 2, 2): overlap 27, N = 402, U* = 37, X3 = 51, K = 6.597, Psi = +5.736
   touching only: least Psi +4.422 at v = (12, 1, 0) (U* = 44, K = 10.245)
```

## Output of `python3 psi.py scan 6 9`

```
O_6: N = 146, U* = 18, X3 = 33, K = 5.959, Psi = +0.041
O_9: N = 489, U* = 18, X3 = 51, K = 5.982, Psi = +0.018
O_6 and O_9: 88 connected unions up to symmetry; least Psi +1.143; unions with Psi < 1/3: 0; with Psi < 0: 0
   v = (2, 2, 1): overlap 125, N = 510, U* = 21, X3 = 51, K = 5.857, Psi = +1.143
   v = (3, 1, 1): overlap 125, N = 510, U* = 21, X3 = 51, K = 5.857, Psi = +1.143
   v = (4, 1, 0): overlap 110, N = 525, U* = 26, X3 = 53, K = 6.097, Psi = +2.570
   v = (14, 1, 0): overlap 0, N = 635, U* = 44, X3 = 83, K = 10.550, Psi = +4.117
   v = (3, 2, 0): overlap 110, N = 525, U* = 32, X3 = 53, K = 6.097, Psi = +4.570
   v = (5, 1, 1): overlap 80, N = 555, U* = 34, X3 = 55, K = 6.250, Psi = +5.083
   v = (13, 1, 1): overlap 0, N = 635, U* = 46, X3 = 79, K = 9.822, Psi = +5.511
   v = (4, 2, 1): overlap 90, N = 545, U* = 35, X3 = 54, K = 6.145, Psi = +5.522
   touching only: least Psi +4.117 at v = (14, 1, 0) (U* = 44, K = 10.550)
```

## Output of `python3 lgeo.py`

```
O_5: U* = 18, long geometric chains (J = 3): 6, steps [4, 4, 4, 4, 4, 4]  [0.002 s]
O_6: U* = 18, long geometric chains (J = 3): 6, steps [5, 5, 5, 5, 5, 5]  [0.002 s]
O_7: U* = 18, long geometric chains (J = 3): 6, steps [6, 6, 6, 6, 6, 6]  [0.002 s]
O_8: U* = 18, long geometric chains (J = 3): 6, steps [7, 7, 7, 7, 7, 7]  [0.003 s]
O_7 + translate by (13, 1, 0): U* = 44, long geometric chains (J = 3): 12, of which not from a local top 2, U* - 3 L = 8, steps [5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6]
O_7 + translate by (12, 2, 0): U* = 52, long geometric chains (J = 3): 12, of which not from a local top 2, U* - 3 L = 16, steps [5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6]
O_7 + translate by (8, 3, 3): U* = 54, long geometric chains (J = 3): 6, of which not from a local top 0, U* - 3 L = 36, steps [5, 5, 5, 5, 6, 6]
O_7 + translate by (5, 4, 3): U* = 54, long geometric chains (J = 3): 6, of which not from a local top 0, U* - 3 L = 36, steps [4, 4, 4, 4, 4, 4]
O_7 + translate by (2, 2, 2): U* = 24, long geometric chains (J = 3): 6, of which not from a local top 6, U* - 3 L = 6, steps [4, 4, 4, 4, 4, 4]
O_7 + translate by (1, 1, 0): U* = 20, long geometric chains (J = 3): 6, of which not from a local top 0, U* - 3 L = 2, steps [6, 6, 6, 6, 6, 6]
O_7 + translate by (3, 3, 0): U* = 36, long geometric chains (J = 3): 6, of which not from a local top 2, U* - 3 L = 18, steps [4, 4, 6, 6, 6, 6]
O_7 + translate by (6, 0, 0): U* = 54, long geometric chains (J = 3): 2, of which not from a local top 0, U* - 3 L = 48, steps [6, 6]
O_7 + translate by (12, 0, 0): U* = 51, long geometric chains (J = 3): 12, of which not from a local top 2, U* - 3 L = 15, steps [5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6]
O_9 + translate by (2, 2, 2): U* = 24, long geometric chains (J = 3): 6, of which not from a local top 6, U* - 3 L = 6, steps [6, 6, 6, 6, 6, 6]
O_9 + translate by (17, 1, 0): U* = 44, long geometric chains (J = 3): 12, of which not from a local top 2, U* - 3 L = 8, steps [7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8]
tetrahedron of side 6: U* = 60, long geometric chains (J = 3): 0
tetrahedron of side 9: U* = 78, long geometric chains (J = 3): 0
```

## Output of `python3 lscan.py`

```
O_7, O_7, J = 2: 79 unions; least U* - 3 L = 2 at v = (1, 1, 0) (overlap 182); unions with 3 L > U*: 0; unions with a long chain that does not start at a local top: 43, among them least U* - 3 L = 4 at v = (2, 1, 1)
O_9, O_9, J = 3: 146 unions; least U* - 3 L = 2 at v = (1, 1, 0) (overlap 408); unions with 3 L > U*: 0; unions with a long chain that does not start at a local top: 70, among them least U* - 3 L = 4 at v = (2, 1, 1)
O_5, O_8, J = 2: 61 unions; least U* - 3 L = 3 at v = (2, 2, 1) (overlap 70); unions with 3 L > U*: 0; unions with a long chain that does not start at a local top: 40, among them least U* - 3 L = 3 at v = (2, 2, 1)
O_6, O_9, J = 2: 88 unions; least U* - 3 L = 3 at v = (2, 2, 1) (overlap 125); unions with 3 L > U*: 0; unions with a long chain that does not start at a local top: 62, among them least U* - 3 L = 3 at v = (2, 2, 1)
```

## Output of `python3 price.py`

```
O_7, O_7: 76 unions with K > 6.1; least price 5.10 at v = (13, 1, 0) (overlap 0, U* = 44, K = 11.10); least price among overlapping unions 7.03 at v = (12, 0, 0) (overlap 1, U* = 51, K = 10.69)
O_9, O_9: 141 unions with K > 6.1; least price 4.90 at v = (17, 1, 0) (overlap 0, U* = 44, K = 11.30); least price among overlapping unions 6.62 at v = (16, 0, 0) (overlap 1, U* = 51, K = 10.99)
O_5, O_8: 59 unions with K > 6.1; least price 6.13 at v = (12, 1, 0) (overlap 0, U* = 44, K = 10.24); least price among overlapping unions 8.59 at v = (11, 0, 0) (overlap 1, U* = 51, K = 9.84)
O_6, O_9: 84 unions with K > 6.1; least price 5.71 at v = (14, 1, 0) (overlap 0, U* = 44, K = 10.55); least price among overlapping unions 7.87 at v = (13, 0, 0) (overlap 1, U* = 51, K = 10.19)
```

## Output of `python3 near.py n` for n = 5, 6, 7, 8 and `python3 near.py 5 2` (last line)

```
O_5: 206 bodies at one site from it; least U* = 19; least Psi = +0.653 (removed (-4, 0, 0), U* = 19); bodies with U* <= 18: 0; with Psi < 1/3: 0
O_6: 294 bodies at one site from it; least U* = 19; least Psi = +0.601 (removed (-5, 0, 0), U* = 19); bodies with U* <= 18: 0; with Psi < 1/3: 0
O_7: 398 bodies at one site from it; least U* = 19; least Psi = +0.563 (removed (-6, 0, 0), U* = 19); bodies with U* <= 18: 0; with Psi < 1/3: 0
O_8: 518 bodies at one site from it; least U* = 19; least Psi = +0.534 (removed (-7, 0, 0), U* = 19); bodies with U* <= 18: 0; with Psi < 1/3: 0
O_5: 21055 connected bodies at two sites from it; least U* = 20; least Psi = +1.246 (sites (-4, 0, 0), (0, -4, 0), U* = 20); with Psi < 1/3: 0
```

## Output of `python3 psi.py search 5 5 1500` (abridged: the five lowest of 37 starts and the summary line)

```
O_5 alone: Psi at start +0.059; after search +0.059 (N = 85, U* = 18, X3 = 27, K = 5.941, Psi = +0.059; added 0, removed 0; a regular octahedron)
v = (1, 1, 0), overlap 60: Psi at start +0.913; after search +0.913 (N = 110, U* = 20, X3 = 29, K = 5.753, Psi = +0.913; added 0, removed 0)
v = (2, 1, 1), overlap 40: Psi at start +1.537; after search +1.537 (N = 130, U* = 22, X3 = 31, K = 5.796, Psi = +1.537; added 0, removed 0)
v = (2, 2, 2), overlap 24: Psi at start +2.041; after search +2.041 (N = 146, U* = 24, X3 = 33, K = 5.959, Psi = +2.041; added 0, removed 0)
v = (3, 3, 2), overlap 10: Psi at start +6.000; after search +2.532 (N = 162, U* = 26, X3 = 35, K = 6.135, Psi = +2.532; added 2, removed 0)
...
O_5, O_5, 1500 annealing steps: 37 starts; ended at a regular octahedron: 1; least Psi among the others: +0.913; ends with Psi < 1/3 that are not regular octahedra: 0; with Psi < 0: 0
```

## Output of `python3 psi.py search 6 6 800 0.5` (abridged: the five lowest of 52 starts and the summary line)

```
O_6 alone: Psi at start +0.041; after search +0.041 (N = 146, U* = 18, X3 = 33, K = 5.959, Psi = +0.041; added 0, removed 0; a regular octahedron)
v = (2, 2, 2), overlap 55: Psi at start +2.106; after search +2.106 (N = 237, U* = 24, X3 = 39, K = 5.894, Psi = +2.106; added 0, removed 0)
v = (4, 2, 2), overlap 30: Psi at start +9.818; after search +2.702 (N = 266, U* = 26, X3 = 41, K = 5.965, Psi = +2.702; added 4, removed 0)
v = (3, 2, 1), overlap 52: Psi at start +5.720; after search +2.785 (N = 238, U* = 26, X3 = 39, K = 5.881, Psi = +2.785; added 2, removed 4)
v = (11, 1, 0), overlap 0: Psi at start +3.728; after search +3.728 (N = 292, U* = 44, X3 = 65, K = 10.938, Psi = +3.728; added 0, removed 0)
...
O_6, O_6, 800 annealing steps: 52 starts; ended at a regular octahedron: 1; least Psi among the others: +2.106; ends with Psi < 1/3 that are not regular octahedra: 0; with Psi < 0: 0
```

## Output of `python3 junction.py 6 6 2` (abridged: the five lowest of 35 starts and the summary line)

```
O_6, O_6: apart, the two lumps have U* = 36 and excess 34.5; the search keeps the excess above 13.8
v = (4, 3, 3): overlap 14; start U* 52, excess -11.5; after search U* 28, excess -12.1 (added 4, removed 0)
v = (4, 4, 4): overlap 0; start U* 66, excess -7.5; after search U* 30, excess -8.3 (added 6, removed 0)
v = (4, 4, 2): overlap 13; start U* 40, excess -7.7; after search U* 40, excess -7.7 (added 0, removed 0)
v = (5, 3, 2): overlap 12; start U* 52, excess -7.8; after search U* 40, excess -8.1 (added 2, removed 0)
v = (5, 4, 3): overlap 0; start U* 54, excess -3.5; after search U* 42, excess -3.8 (added 2, removed 0)
...
O_6, O_6, radius 2, annealing steps 0: 35 starts; least U* with excess above the bound: 44; bodies with U* <= 36 and positive excess: 0
```

## Output of `python3 junction.py 6 6 3 1500` (abridged: the five lowest of 35 starts and the summary line)

```
O_6, O_6: apart, the two lumps have U* = 36 and excess 34.5; the search keeps the excess above 13.8
v = (4, 3, 3): overlap 14; start U* 52, excess -11.5; after search U* 28, excess -12.1 (added 4, removed 0)
v = (4, 4, 4): overlap 0; start U* 66, excess -7.5; after search U* 30, excess -8.3 (added 6, removed 0)
v = (4, 4, 2): overlap 13; start U* 40, excess -7.7; after search U* 40, excess -7.7 (added 0, removed 0)
v = (5, 3, 2): overlap 12; start U* 52, excess -7.8; after search U* 40, excess -8.1 (added 2, removed 0)
v = (5, 4, 3): overlap 0; start U* 54, excess -3.5; after search U* 42, excess -3.8 (added 2, removed 0)
...
O_6, O_6, radius 3, annealing steps 1500: 35 starts; least U* with excess above the bound: 44; bodies with U* <= 36 and positive excess: 0
```

## Output of `python3 junction.py 7 7 2 1000` (abridged: the five lowest of 50 starts and the summary line)

```
O_7, O_7: apart, the two lumps have U* = 36 and excess 46.4; the search keeps the excess above 18.6
v = (4, 4, 4): overlap 19; start U* 66, excess -9.6; after search U* 30, excess -10.2 (added 6, removed 0)
v = (5, 4, 3): overlap 18; start U* 54, excess -5.7; after search U* 42, excess -5.9 (added 2, removed 0)
v = (5, 5, 4): overlap 0; start U* 68, excess -1.6; after search U* 44, excess -2.0 (added 4, removed 0)
v = (13, 1, 0): overlap 0; start U* 44, excess 42.4; after search U* 44, excess 42.4 (added 0, removed 0)
v = (8, 1, 1): overlap 16; start U* 46, excess 6.1; after search U* 46, excess 6.1 (added 0, removed 0)
...
O_7, O_7, radius 2, annealing steps 1000: 50 starts; least U* with excess above the bound: 44; bodies with U* <= 36 and positive excess: 0
```

## Output of `python3 roof.py N n J` for (N, n, J) = (6, 5, 2), (7, 5, 2), (7, 6, 3), (6, 6, 2), (8, 4, 2)

```
roof O_6, legs O_5, J = 2: 92 connected bodies
   least Psi: +7.271 at (a, b, c) = (2, 2, 1) (U* = 40, K = 6.06, long chains 6)
   largest 3 L - U*: -16 at (a, b, c) = (10, 0, 1) (U* = 70, long chains 18, of which seen from above 3, Psi = +7.854)
   bodies with three long chains seen from above (roof and both legs): 10; among them least U* = 70, least U* - 3 L = 16, least Psi = +7.854
   bodies with a long chain that does not start at a local top: 52; among them least U* - 3 L = 16, largest number of such chains 6
   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): 3; among them least U* = 110, least U* - 3 L = 56
      under the roof: (a, b, c) = (6, 0, 5): N = 316, U* = 110, long chains 18 (6 not from a top), U* - 3 L = 56, Psi = +21.187
      under the roof: (a, b, c) = (5, 0, 6): N = 316, U* = 119, long chains 18 (5 not from a top), U* - 3 L = 65, Psi = +24.187
      under the roof: (a, b, c) = (4, 0, 7): N = 315, U* = 124, long chains 18 (5 not from a top), U* - 3 L = 70, Psi = +26.355
   alarms (Psi < 0 or 3 L > U*): 0
      (a, b, c) = (10, 0, 1): N = 316, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.48, Psi = +7.854
      (a, b, c) = (10, 1, 0): N = 316, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.48, Psi = +7.854
      (a, b, c) = (1, 1, 9): N = 279, U* = 57, long chains 12 (2 from above), U* - 3 L = 21, K = 9.51, Psi = +9.492
      (a, b, c) = (2, 2, 1): N = 224, U* = 40, long chains 6 (1 from above), U* - 3 L = 22, K = 6.06, Psi = +7.271
      (a, b, c) = (9, 0, 0): N = 314, U* = 84, long chains 18 (3 from above), U* - 3 L = 30, K = 14.48, Psi = +13.518
roof O_7, legs O_5, J = 2: 104 connected bodies
   least Psi: +8.163 at (a, b, c) = (11, 0, 1) (U* = 70, K = 15.17, long chains 18)
   largest 3 L - U*: -16 at (a, b, c) = (11, 0, 1) (U* = 70, long chains 18, of which seen from above 3, Psi = +8.163)
   bodies with three long chains seen from above (roof and both legs): 11; among them least U* = 70, least U* - 3 L = 16, least Psi = +8.163
   bodies with a long chain that does not start at a local top: 71; among them least U* - 3 L = 16, largest number of such chains 6
   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): 4; among them least U* = 116, least U* - 3 L = 62
      under the roof: (a, b, c) = (7, 0, 5): N = 401, U* = 116, long chains 18 (6 not from a top), U* - 3 L = 62, Psi = +23.496
      under the roof: (a, b, c) = (6, 0, 6): N = 401, U* = 122, long chains 18 (4 not from a top), U* - 3 L = 68, Psi = +25.496
      under the roof: (a, b, c) = (4, 0, 8): N = 400, U* = 124, long chains 18 (5 not from a top), U* - 3 L = 70, Psi = +26.626
   alarms (Psi < 0 or 3 L > U*): 0
      (a, b, c) = (11, 0, 1): N = 401, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.17, Psi = +8.163
      (a, b, c) = (11, 1, 0): N = 401, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.17, Psi = +8.163
      (a, b, c) = (1, 1, 10): N = 364, U* = 57, long chains 12 (2 from above), U* - 3 L = 21, K = 9.58, Psi = +9.418
      (a, b, c) = (1, 1, 8): N = 357, U* = 54, long chains 8 (2 from above), U* - 3 L = 30, K = 8.41, Psi = +9.595
      (a, b, c) = (10, 0, 0): N = 399, U* = 84, long chains 18 (3 from above), U* - 3 L = 30, K = 14.25, Psi = +13.752
roof O_7, legs O_6, J = 3: 130 connected bodies
   least Psi: +7.348 at (a, b, c) = (2, 2, 1) (U* = 40, K = 5.99, long chains 6)
   largest 3 L - U*: -16 at (a, b, c) = (12, 0, 1) (U* = 70, long chains 18, of which seen from above 3, Psi = +7.426)
   bodies with three long chains seen from above (roof and both legs): 11; among them least U* = 70, least U* - 3 L = 16, least Psi = +7.426
   bodies with a long chain that does not start at a local top: 57; among them least U* - 3 L = 16, largest number of such chains 6
   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): 3; among them least U* = 126, least U* - 3 L = 72
      under the roof: (a, b, c) = (7, 0, 6): N = 523, U* = 126, long chains 18 (6 not from a top), U* - 3 L = 72, Psi = +26.093
      under the roof: (a, b, c) = (6, 0, 7): N = 523, U* = 135, long chains 18 (5 not from a top), U* - 3 L = 81, Psi = +29.093
      under the roof: (a, b, c) = (5, 0, 8): N = 522, U* = 140, long chains 18 (5 not from a top), U* - 3 L = 86, Psi = +31.193
   alarms (Psi < 0 or 3 L > U*): 0
      (a, b, c) = (12, 0, 1): N = 523, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.91, Psi = +7.426
      (a, b, c) = (12, 1, 0): N = 523, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.91, Psi = +7.426
      (a, b, c) = (1, 1, 11): N = 447, U* = 57, long chains 12 (2 from above), U* - 3 L = 21, K = 9.83, Psi = +9.166
      (a, b, c) = (2, 2, 1): N = 343, U* = 40, long chains 6 (1 from above), U* - 3 L = 22, K = 5.99, Psi = +7.348
      (a, b, c) = (11, 0, 0): N = 521, U* = 84, long chains 18 (3 from above), U* - 3 L = 30, K = 15.04, Psi = +12.956
roof O_6, legs O_6, J = 2: 116 connected bodies
   least Psi: +4.148 at (a, b, c) = (1, 1, 2) (U* = 30, K = 5.85, long chains 6)
   largest 3 L - U*: -12 at (a, b, c) = (1, 1, 2) (U* = 30, long chains 6, of which seen from above 1, Psi = +4.148)
   bodies with three long chains seen from above (roof and both legs): 17; among them least U* = 70, least U* - 3 L = 16, least Psi = +7.406
   bodies with a long chain that does not start at a local top: 77; among them least U* - 3 L = 12, largest number of such chains 7
   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): 3; among them least U* = 123, least U* - 3 L = 69
      under the roof: (a, b, c) = (6, 0, 6): N = 438, U* = 123, long chains 18 (7 not from a top), U* - 3 L = 69, Psi = +25.073
      under the roof: (a, b, c) = (4, 0, 8): N = 432, U* = 127, long chains 18 (5 not from a top), U* - 3 L = 73, Psi = +28.181
      under the roof: (a, b, c) = (5, 0, 7): N = 437, U* = 134, long chains 18 (5 not from a top), U* - 3 L = 80, Psi = +29.197
   alarms (Psi < 0 or 3 L > U*): 0
      (a, b, c) = (1, 1, 2): N = 258, U* = 30, long chains 6 (1 from above), U* - 3 L = 12, K = 5.85, Psi = +4.148
      (a, b, c) = (1, 2, 1): N = 278, U* = 32, long chains 6 (1 from above), U* - 3 L = 14, K = 5.83, Psi = +4.832
      (a, b, c) = (2, 1, 1): N = 278, U* = 32, long chains 6 (1 from above), U* - 3 L = 14, K = 5.83, Psi = +4.832
      (a, b, c) = (11, 0, 1): N = 438, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.93, Psi = +7.406
      (a, b, c) = (11, 1, 0): N = 438, U* = 70, long chains 18 (3 from above), U* - 3 L = 16, K = 15.93, Psi = +7.406
roof O_8, legs O_4, J = 2: 96 connected bodies
   least Psi: +4.887 at (a, b, c) = (5, 0, 1) (U* = 34, K = 6.45, long chains 10)
   largest 3 L - U*: -4 at (a, b, c) = (5, 0, 1) (U* = 34, long chains 10, of which seen from above 1, Psi = +4.887)
   bodies with three long chains seen from above (roof and both legs): 8; among them least U* = 94, least U* - 3 L = 52, least Psi = +18.094
   bodies with a long chain that does not start at a local top: 79; among them least U* - 3 L = 4, largest number of such chains 6
   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): 5; among them least U* = 118, least U* - 3 L = 76
      under the roof: (a, b, c) = (8, 0, 4): N = 432, U* = 118, long chains 14 (6 not from a top), U* - 3 L = 76, Psi = +26.094
      under the roof: (a, b, c) = (4, 0, 8): N = 432, U* = 121, long chains 14 (5 not from a top), U* - 3 L = 79, Psi = +27.094
      under the roof: (a, b, c) = (5, 0, 7): N = 432, U* = 124, long chains 14 (4 not from a top), U* - 3 L = 82, Psi = +28.094
   alarms (Psi < 0 or 3 L > U*): 0
      (a, b, c) = (5, 0, 1): N = 376, U* = 34, long chains 10 (1 from above), U* - 3 L = 4, K = 6.45, Psi = +4.887
      (a, b, c) = (5, 1, 0): N = 376, U* = 34, long chains 10 (2 from above), U* - 3 L = 4, K = 6.45, Psi = +4.887
      (a, b, c) = (0, 1, 5): N = 376, U* = 40, long chains 8 (1 from above), U* - 3 L = 16, K = 6.45, Psi = +6.887
      (a, b, c) = (1, 0, 5): N = 376, U* = 40, long chains 8 (1 from above), U* - 3 L = 16, K = 6.45, Psi = +6.887
      (a, b, c) = (4, 0, 2): N = 376, U* = 46, long chains 7 (1 from above), U* - 3 L = 25, K = 6.45, Psi = +8.887
```
