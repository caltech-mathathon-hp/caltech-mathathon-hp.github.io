# FCC HP folding: verification code, part 18 (twenty-first pass, 15 Nov 2026)

Scripts for Section 44 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the Euler characteristic of the boundary surface, the statement G_chi (U* >= 6T - 9 chi), which is false, the change of W when one site is added, and W split by axis. They import `gmin.py`, `psi.py` (part 16) and `wdef.py`, `tops.py`, `morse.py` (part 17). Nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `euler.py` | chi of the boundary of the union of Voronoi cells, with or without pinch points resolved | `python3 euler.py` |
| `gchi.py` | G_chi on all small connected sets, and a search against it; the argument `res` resolves pinch points | `python3 gchi.py small 7 res`, `python3 gchi.py search 1 2500 3.0 res` |
| `addsite.py` | the formula for W(S + g) - W(S) | `python3 addsite.py` |
| `waxis.py` | W by axis against tops by axis | `python3 waxis.py` |

## `euler.py`

```python
"""Section 44 of the note: Euler characteristic of the boundary of the union of the Voronoi cells of S: chi = (mixed tetrahedra) + (mixed octahedra) - (boundary edges).
Tetrahedra: the four lattice points around a cube centre in (Z + 1/2)^3.  Octahedra: c +- e_i around an integer point c of odd coordinate sum.
With resolved=True the surface is made a manifold first: at the centre of an octahedron where it pinches (the cells of S around the centre and
the empty cells around it form k + 1 > 2 groups), the centre is counted k times.  This is the Euler characteristic of the normalised surface."""
from gmin import *
import itertools
SG = list(itertools.product((0, 1), repeat=3))
def chi_v(S, resolved=False):
    S = set(S); par = sum(next(iter(S))) % 2
    tets = set(); octs = set(); bd = 0
    for h in S:
        for r in ROOTS:
            if add(h, r) not in S: bd += 1
        # cube cells containing h: lower corner k with h in k + {0,1}^3
        for d in SG:
            k = (h[0] - d[0], h[1] - d[1], h[2] - d[2]); tets.add(k)
        for i in range(3):
            for s in (1, -1):
                c = list(h); c[i] += s; octs.add(tuple(c))
    mt = 0
    for k in tets:
        v = [(k[0] + d[0], k[1] + d[1], k[2] + d[2]) for d in SG if (k[0] + d[0] + k[1] + d[1] + k[2] + d[2]) % 2 == par]
        n = sum(1 for x in v if x in S)
        if 0 < n < 4: mt += 1
    mo = 0; pinch = 0
    for c in octs:
        occ = []
        for i in range(3):
            for s in (1, -1):
                x = list(c); x[i] += s
                occ.append(tuple(x) in S)
        n = sum(occ)
        if 0 < n < 6:
            mo += 1
            # faces of the cube around c: index 2i (+e_i), 2i+1 (-e_i); two faces are adjacent unless opposite
            def comps(val):
                idx = [j for j in range(6) if occ[j] == val]; seen = set(); k = 0
                for j in idx:
                    if j in seen: continue
                    k += 1; st = [j]; seen.add(j)
                    while st:
                        a_ = st.pop()
                        for b_ in idx:
                            if b_ not in seen and b_ // 2 != a_ // 2: seen.add(b_); st.append(b_)
                return k
            pinch += comps(True) + comps(False) - 2
    return (mt + mo - bd + pinch) if resolved else (mt + mo - bd)
if __name__ == '__main__':
    from tops import tops
    from morse import morse
    def show(name, S):
        u = cost(S)['U']; T, sig, b1 = morse(S); x = chi_v(S)
        print(f"{name}: N={len(S)} U*={u} T={T} b1={b1} chi={x}  U*-6T+18={u-6*T+18}  U*-6T+9chi={u-6*T+9*x}")
    show('site', {(0,0,0)}); show('pair', {(0,0,0),(1,1,0)})
    for n in (2, 3, 5, 6): show(f'O_{n}', octa(n))
    n = 6
    show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('tips coincide', octa(n) | octa(n, (2*n-2, 0, 0)))
    show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0))); show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    show('ring of four', octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0)))
    S = octa(9); show('O_9 with a tunnel along z', {h for h in S if not (abs(h[0]) + abs(h[1]) <= 2)})
    show('O_9 with cavity O_3', octa(9) - octa(3)); show('rod 10', {(i,i,0) for i in range(10)}); show('tetra 6', tetra(6))
    show('twin tops', octa(7) | octa(7, (2, 0, 0)))
```

## `gchi.py`

```python
"""Section 44 of the note.  Statement G_chi: U* >= 6T - 9 chi for every connected set with at least two sites, chi = Euler characteristic of
the boundary of the union of Voronoi cells (euler.py).  For one boundary sphere this is Conjecture G.
  python3 gchi.py small NMAX       all connected sets with 2..NMAX sites
  python3 gchi.py search seed steps T0   annealing on U* - 6T + 9 chi"""
import sys, random, math
from gmin import *
from tops import tops
from euler import chi_v
from psi import boundary_moves, toggle, unions
RES = "res" in sys.argv
def slack(S): return cost(S)["U"] - 6 * tops(S)[0] + 9 * chi_v(S, RES)
def norm(S):
    m = min(S); return frozenset((x - m[0], y - m[1], z - m[2]) for x, y, z in S)
if sys.argv[1] == 'small':
    level = {frozenset({(0, 0, 0)})}; tot = 0
    for n in range(1, int(sys.argv[2]) + 1):
        if n >= 2:
            best = None; chis = {}
            for S in level:
                x = chi_v(S, RES); v = cost(set(S))['U'] - 6 * tops(set(S))[0] + 9 * x; chis[x] = chis.get(x, 0) + 1
                if best is None or v < best[0]: best = (v, x, sorted(S))
            tot += len(level)
            print(f"{n} sites: {len(level)} sets; values of chi: {sorted(chis.items())}; least U* - 6T + 9 chi = {best[0]} (chi = {best[1]})", flush=True)
        if n == int(sys.argv[2]): break
        nxt = set()
        for S in level:
            for h in S:
                for r in ROOTS:
                    g = add(h, r)
                    if g not in S: nxt.add(norm(S | {g}))
        level = nxt
    print(f"{tot} sets in all")
else:
    seed, steps, T0 = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]); rng = random.Random(seed); n = 5
    def blob(k):
        S = {(0, 0, 0)}
        while len(S) < k:
            h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
        return S
    starts = [(f'O_{k}', octa(k)) for k in (3, 4, 5, 6)]
    starts += [('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))), ('one-site bridge', octa(n) | {(n, 1, 0)} | octa(n, (2*n, 2, 0))),
               ('zig bridge', octa(n) | {(n, 1, 0), (n+1, 0, 0)} | octa(n, (2*n+1, 1, 0))), ('twin tops', octa(n) | octa(n, (2, 0, 0))),
               ('ring of four', octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0))),
               ('O_7 with a tunnel', {h for h in octa(7) if not (abs(h[0]) + abs(h[1]) <= 1)}), ('O_7 with cavity', octa(7) - octa(2))]
    starts += [(f'O_5+{v}', S) for v, ov, S in unions(5, 5)][::6]
    starts += [(f'blob{k}_{i}', blob(k)) for k in (10, 25, 50) for i in range(3)]
    worst = None
    for name, S in starts:
        cur = slack(S); s0 = cur; best = (cur, set(S)); mv = boundary_moves(S)
        for i in range(steps):
            T = T0 * (1 - i / steps) + 0.05
            h = rng.choice(mv); S2 = toggle(S, h)
            if len(S2) < 2 or (h in S and not connected(S2)): continue
            u = slack(S2)
            if u <= cur or rng.random() < math.exp((cur - u) / T):
                S, cur = S2, u; mv = boundary_moves(S)
                if cur < best[0]: best = (cur, set(S))
        B = best[1]
        if worst is None or best[0] < worst[0]: worst = (best[0], name, sorted(B))
        print(f"{name}: slack at start {s0}, least met {best[0]} (N = {len(B)}, U* = {cost(B)['U']}, T = {tops(B)[0]}, chi = {chi_v(B, RES)})", flush=True)
    print(f"seed {seed}, {steps} steps, T0 = {T0}, {len(starts)} starts: least U* - 6T + 9 chi = {worst[0]} (from {worst[1]})")
    if worst[0] < 0: print("VIOLATION", worst[2])
```

## `addsite.py`

```python
"""Section 44 of the note: adding one site g to a set S'.  With a = number of neighbours of g in S', c = number of empty neighbours of g that are
adjacent to S', and i = number of neighbours of g that become interior:  W(S' + g) - W(S') = -12 - a + 3c + 3i.  Checked on random cases."""
import random
from gmin import *
from wdef import parts
from psi import boundary_moves
rng = random.Random(3); bad = 0; n = 0
for trial in range(400):
    S = {(0, 0, 0)}
    for _ in range(rng.randint(2, 60)):
        h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
    if trial % 4 == 0: S |= octa(4)
    cand = [g for g in boundary_moves(S) if g not in S]
    for g in rng.sample(cand, min(5, len(cand))):
        a = sum(1 for r in ROOTS if add(g, r) in S)
        c = sum(1 for r in ROOTS if add(g, r) not in S and any(add(add(g, r), q) in S for q in ROOTS))
        T = S | {g}
        i = sum(1 for r in ROOTS if add(g, r) in S and all(add(add(g, r), q) in T for q in ROOTS))
        i += 1 if a == 12 else 0
        dW = parts(T)['W'] - parts(S)['W']; n += 1
        if dW != -12 - a + 3 * c + 3 * i: bad += 1
print(f"{n} additions of one site: the formula for the change of W fails in {bad}")
```

## `waxis.py`

```python
"""Section 44 of the note: W split by axis: W_a = sum over surface sites of (empty in-plane neighbours in the a-slice - 1) + sum over coat sites of (occupied in-plane neighbours - 1).
Also per level: corners, e, f."""
from gmin import *
from morse import axis_data
from wdef import parts
def w_axes(S):
    S = set(S); out = []
    surf = [h for h in S if any(add(h, r) not in S for r in ROOTS)]
    coat = {add(h, r) for h in S for r in ROOTS} - S
    for ax in range(3):
        inpl = [r for r in ROOTS if r[ax] == 0]
        w = sum(sum(1 for r in inpl if add(h, r) not in S) - 1 for h in surf) + sum(sum(1 for r in inpl if add(p, r) in S) - 1 for p in coat)
        out.append(w)
    return out
if __name__ == '__main__':
    def show(name, S):
        w = w_axes(S); p = parts(S); T = [axis_data(S, a)[0] for a in range(3)]
        assert sum(w) == p['W']
        print(f"{name}: U*={p['U']} W={p['W']} = {w}  def2={p['d2']} def1={p['d1']}  T by axis {T}   6(T_a-1) = {[6*(t-1) for t in T]}")
    n = 6
    show('O_6', octa(n)); show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('tips coincide', octa(n) | octa(n, (2*n-2, 0, 0)))
    show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0))); show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    show('twin tops', octa(n) | octa(n, (2, 0, 0))); show('O_6 + cell', octa(n) | {(n,1,0)}); show('O_6 + site over an edge', octa(n) | {(4, 3, 0)})
    show('O_6+(1,1,0)', octa(n) | octa(n,(1,1,0))); show('O_6+(2,2,2)', octa(n) | octa(n,(2,2,2))); show('O_6 minus vertex', octa(n) - {(5,0,0)})
    show('pair', {(0,0,0),(1,1,0)}); show('rod 6', {(i,i,0) for i in range(6)}); show('tetra 6', tetra(6))
    show('O_6+(4,0,0)', octa(n) | octa(n,(4,0,0))); show('O_6+(4,4,4)', octa(n) | octa(n,(4,4,4)))
```

## Output of `python3 euler.py` (the last column uses chi without resolving pinch points)

```
site: N=1 U*=15 T=6 b1=0 chi=2  U*-6T+18=-3  U*-6T+9chi=-3
pair: N=2 U*=26 T=6 b1=0 chi=2  U*-6T+18=8  U*-6T+9chi=8
O_2: N=6 U*=42 T=6 b1=0 chi=2  U*-6T+18=24  U*-6T+9chi=24
O_3: N=19 U*=54 T=6 b1=0 chi=2  U*-6T+18=36  U*-6T+9chi=36
O_5: N=85 U*=18 T=6 b1=0 chi=2  U*-6T+18=0  U*-6T+9chi=0
O_6: N=146 U*=18 T=6 b1=0 chi=2  U*-6T+18=0  U*-6T+9chi=0
tip next to tip: N=292 U*=44 T=10 b1=0 chi=2  U*-6T+18=2  U*-6T+9chi=2
tips coincide: N=291 U*=51 T=10 b1=0 chi=2  U*-6T+18=9  U*-6T+9chi=9
one-site bridge: N=293 U*=43 T=10 b1=0 chi=2  U*-6T+18=1  U*-6T+9chi=1
zig bridge: N=294 U*=54 T=12 b1=0 chi=2  U*-6T+18=0  U*-6T+9chi=0
ring of four: N=584 U*=104 T=16 b1=2 chi=0  U*-6T+18=26  U*-6T+9chi=8
O_9 with a tunnel along z: N=392 U*=300 T=6 b1=2 chi=0  U*-6T+18=282  U*-6T+9chi=264
O_9 with cavity O_3: N=470 U*=126 T=6 b1=0 chi=4  U*-6T+18=108  U*-6T+9chi=126
rod 10: N=10 U*=114 T=6 b1=0 chi=2  U*-6T+18=96  U*-6T+9chi=96
tetra 6: N=56 U*=60 T=6 b1=0 chi=2  U*-6T+18=42  U*-6T+9chi=42
twin tops: N=316 U*=42 T=10 b1=0 chi=2  U*-6T+18=0  U*-6T+9chi=0
```

## Output of `python3 gchi.py small 7 res`

```
2 sites: 6 sets; values of chi: [(2, 6)]; least U* - 6T + 9 chi = 8 (chi = 2)
3 sites: 50 sets; values of chi: [(2, 50)]; least U* - 6T + 9 chi = 13 (chi = 2)
4 sites: 475 sets; values of chi: [(2, 475)]; least U* - 6T + 9 chi = 18 (chi = 2)
5 sites: 4881 sets; values of chi: [(2, 4881)]; least U* - 6T + 9 chi = 17 (chi = 2)
6 sites: 52835 sets; values of chi: [(0, 28), (2, 52807)]; least U* - 6T + 9 chi = 24 (chi = 2)
7 sites: 593382 sets; values of chi: [(0, 1008), (2, 592374)]; least U* - 6T + 9 chi = 27 (chi = 2)
651629 sets in all
```

## Output of `python3 gchi.py search 1 2500 3.0 res` (abridged: the six lowest of 26 starts and the summary; G_chi is violated)

```
blob10_2: slack at start 44, least met -113 (N = 186, U* = 1135, T = 52, chi = -104)
blob10_0: slack at start 70, least met -102 (N = 142, U* = 876, T = 49, chi = -76)
blob25_2: slack at start 119, least met -88 (N = 190, U* = 1208, T = 54, chi = -108)
blob25_1: slack at start 87, least met -85 (N = 237, U* = 1499, T = 81, chi = -122)
blob50_0: slack at start 119, least met -61 (N = 188, U* = 929, T = 57, chi = -72)
O_3: slack at start 36, least met -60 (N = 155, U* = 936, T = 52, chi = -76)
...
seed 1, 2500 steps, T0 = 3.0, 26 starts: least U* - 6T + 9 chi = -113 (from blob10_2)
```

## Output of `python3 gchi.py search 1 2500 3.0` (pinch points not resolved; abridged)

```
blob50_2: slack at start 127, least met -875 (N = 285, U* = 2236, T = 112, chi = -271)
blob50_1: slack at start 103, least met -865 (N = 302, U* = 2420, T = 129, chi = -279)
blob25_2: slack at start 119, least met -851 (N = 301, U* = 2386, T = 142, chi = -265)
O_5+(5, 2, 1): slack at start 6, least met -849 (N = 388, U* = 2736, T = 134, chi = -309)
...
seed 1, 2500 steps, T0 = 3.0, 26 starts: least U* - 6T + 9 chi = -875 (from blob50_2)
```

## Output of `python3 addsite.py`

```
2000 additions of one site: the formula for the change of W fails in 0
```

## Output of `python3 waxis.py`

```
O_6: U*=18 W=-18 = [-6, -6, -6]  def2=12 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
tip next to tip: U*=44 W=-16 = [-4, -4, -8]  def2=20 def1=0  T by axis [2, 4, 4]   6(T_a-1) = [6, 18, 18]
tips coincide: U*=51 W=-9 = [-3, -3, -3]  def2=20 def1=0  T by axis [2, 4, 4]   6(T_a-1) = [6, 18, 18]
one-site bridge: U*=43 W=-17 = [-3, -3, -11]  def2=20 def1=0  T by axis [2, 4, 4]   6(T_a-1) = [6, 18, 18]
zig bridge: U*=54 W=-12 = [0, 0, -12]  def2=22 def1=0  T by axis [2, 6, 4]   6(T_a-1) = [6, 30, 18]
twin tops: U*=42 W=-6 = [-2, -2, -2]  def2=16 def1=0  T by axis [2, 4, 4]   6(T_a-1) = [6, 18, 18]
O_6 + cell: U*=29 W=-16 = [-4, -4, -8]  def2=15 def1=0  T by axis [2, 3, 2]   6(T_a-1) = [6, 12, 6]
O_6 + site over an edge: U*=32 W=-13 = [-3, -3, -7]  def2=15 def1=0  T by axis [3, 3, 2]   6(T_a-1) = [12, 12, 6]
O_6+(1,1,0): U*=20 W=-16 = [-4, -4, -8]  def2=12 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
O_6+(2,2,2): U*=24 W=-12 = [-4, -4, -4]  def2=12 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
O_6 minus vertex: U*=19 W=-14 = [-10, -2, -2]  def2=11 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
pair: U*=26 W=-16 = [-4, -4, -8]  def2=14 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
rod 6: U*=70 W=-20 = [0, 0, -20]  def2=30 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
tetra 6: U*=60 W=12 = [4, 4, 4]  def2=16 def1=0  T by axis [2, 2, 2]   6(T_a-1) = [6, 6, 6]
O_6+(4,0,0): U*=54 W=-6 = [-2, -2, -2]  def2=20 def1=0  T by axis [2, 4, 4]   6(T_a-1) = [6, 18, 18]
O_6+(4,4,4): U*=66 W=-6 = [-2, -2, -2]  def2=24 def1=0  T by axis [4, 4, 4]   6(T_a-1) = [18, 18, 18]
```
