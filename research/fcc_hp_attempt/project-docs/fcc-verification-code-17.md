# FCC HP folding: verification code, part 17 (twentieth pass, 14 Nov 2026)

Scripts for Section 43 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the formula U* = W + 3 def1 + 3 def2, local tops, splits and merges of slice pieces, Conjecture G (U* >= 6T - 18), and the cheapest connection between two octahedra. They import `gmin.py` and `psi.py` of part 16 (`claude/fcc-verification-code-16.md`). Python 3 with numpy and scipy. Nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `wdef.py` | W, def1, def2 and the identity of Lemma 56(a) on examples | `python3 wdef.py` |
| `tops.py` | local tops in the six directions; U* against 3T, 4T - 6, 6T - 18 on examples | `python3 tops.py` |
| `morse.py` | piece graphs: T, sigma, cycle rank; checks Lemma 57 on every body it is given | `python3 morse.py` |
| `bridge.py` | two octahedra that are not adjacent, joined by one or two sites (Section 43.5) | `python3 bridge.py n` |
| `gcheck.py` | Conjecture G on the families of Section 42 | `python3 gcheck.py` |
| `gprime.py` | Conjecture G and the false extension G' on all small connected sets; search against G' | `python3 gprime.py small 7`, `python3 gprime.py search 1 2500` |
| `gsearch.py` | search against Conjecture G | `python3 gsearch.py seed steps [temperature]` |

`gsearch.py` was run with seeds 1 and 2 (3000 steps, temperature 3) before the five bodies with equality or near equality were added to its starts (42 starts each), and with seeds 3 and 4 (4000 steps, temperatures 1 and 0.4) after (47 starts each).

## `wdef.py`

```python
"""Section 43 of the note: U* = W + 3 def1 + 3 def2 with W = 2 bd - 3 s - 3 c (a sum over the boundary graph of degree - 3),
def1 = s - nu1 and def2 = c - nu2 (the shortfalls of the two matchings)."""
from gmin import *
def parts(S):
    c = cost(S); W = 2 * c['boundary'] - 3 * c['surface'] - 3 * c['coat']
    return dict(U=c['U'], W=W, d1=c['surface'] - c['nu1'], d2=c['coat'] - c['nu2'], s=c['surface'], c=c['coat'], n2=c['n2'], N=c['size'])
def show(name, S):
    p = parts(S); assert p['U'] == p['W'] + 3 * p['d1'] + 3 * p['d2']
    print(f"{name}: N={p['N']} U*={p['U']} W={p['W']} def1={p['d1']} def2={p['d2']} kappa={p['c']-p['s']} n2*={p['n2']}")
if __name__ == '__main__':
    show('site', {(0,0,0)}); show('pair', {(0,0,0),(1,1,0)})
    for n in (2,3,4,5,6,8): show(f'O_{n}', octa(n))
    for k in (4,6,9): show(f'tetra {k}', tetra(k))
    for v in ((1,1,0),(2,2,0),(3,3,0),(2,2,2),(2,1,1),(4,0,0),(6,0,0),(12,0,0),(13,1,0),(12,1,1),(12,2,0),(8,3,3),(4,4,4),(5,4,3)):
        show(f'O_7+{v}', octa(7) | octa(7, v))
    S = octa(7); S.discard((6,0,0)); show('O_7 minus a vertex', S)
    S = octa(7); S.add((7,1,0)); show('O_7 plus a cell', S)
    # plate, rod, cube-ish block
    show('plate 6x6 (z=0)', {(x,y,0) for x in range(-6,7) for y in range(-6,7) if (x+y)%2==0 and abs(x)+abs(y)<=6})
    show('rod 10', {(i,i,0) for i in range(10)})
    show('block', {(x,y,z) for x in range(6) for y in range(6) for z in range(6) if (x+y+z)%2==0})
    # torus-like: O_9 with an axial tunnel
    S = octa(9); T = {h for h in S if not (abs(h[0])+abs(h[1])<=2)}; show('O_9 with tunnel along z', T) if connected(T) else None
    S = octa(9); T = S - octa(3); show('O_9 with cavity O_3', T)
```

## `tops.py`

```python
"""Section 43 of the note: local tops in the six directions (pieces of slices with no occupied upper neighbour), against U*."""
from gmin import *
from wdef import parts
def slices(S, ax, sg):
    o = [i for i in range(3) if i != ax]; sl = {}
    for h in S: sl.setdefault(sg * h[ax], set()).add((h[o[0]], h[o[1]]))
    return sl
def pieces(sq):
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
    return ps
UP = ((1, 0), (-1, 0), (0, 1), (0, -1))
def tops(S):
    """returns (number of local tops over six directions, number of them that are single sites, number of distinct sites that are one-site tops)"""
    T = 0; one = 0; sites = set()
    for ax in range(3):
        o = [i for i in range(3) if i != ax]
        for sg in (1, -1):
            sl = slices(S, ax, sg)
            for l, sq in sl.items():
                up = sl.get(l + 1, ())
                for p in pieces(sq):
                    if not any((u + a, v + b) in up for u, v in p for a, b in UP):
                        T += 1
                        if len(p) == 1:
                            one += 1; u, v = next(iter(p)); h = [0, 0, 0]; h[ax] = sg * l; h[o[0]] = u; h[o[1]] = v; sites.add(tuple(h))
    return T, one, len(sites)
def show(name, S):
    p = parts(S); T, one, ns = tops(S)
    print(f"{name}: N={p['N']} U*={p['U']} W={p['W']} def2={p['d2']} def1={p['d1']}  tops T={T} (one-site {one}, at {ns} sites)  U*-3T={p['U']-3*T}  U*-(4T-6)={p['U']-4*T+6}  U*-(6T-18)={p['U']-6*T+18}")
if __name__ == '__main__':
    show('O_7', octa(7))
    S = octa(7); S.add((7, 1, 0)); show('O_7 + cell of a vertex', S)
    S = octa(7); S.add((3, 3, 2)); show('O_7 + site on a face', S)      # norm 8 = n+1, face coat site
    S = octa(7); S.add((4, 4, 0)); show('O_7 + site over an edge', S)
    S = octa(7) | octa(2, (8, 0, 0)) if False else octa(7) | {(7,1,0),(7,-1,0),(7,0,1),(7,0,-1),(8,0,0)}; show('O_7 + 5 sites on a vertex', S)
    for v in ((13,1,0),(12,0,0),(4,0,0),(2,2,2),(1,1,0),(4,4,4),(8,3,3),(3,3,0),(5,4,3),(12,2,0)): show(f'O_7+{v}', octa(7) | octa(7, v))
    show('three in a row', octa(6) | octa(6,(11,1,0)) | octa(6,(-11,-1,0)))
    for b, v in ((3,(4,3,3)),(4,(4,4,3)),(3,(8,0,0)),(3,(9,1,0)),(4,(10,1,0)),(5,(11,1,0))): show(f'O_7 + O_{b}+{v}', octa(7) | octa(b, v))
```

## `morse.py`

```python
"""Section 43 of the note: tops, splits and merges of the slice pieces in the three axes.
For an axis, the pieces of all slices form a graph (piece - child).  T_a = pieces without parent + pieces without child,
sigma_a = sum over pieces of (children - 1)_+ + (parents - 1)_+, b1_a = cycle rank.  For a connected body
T_a = 2 - 2 b1_a + sigma_a.          Conjecture G': U* >= 3 T + 3 sigma   (T, sigma summed over the three axes)."""
from gmin import *
from tops import slices, pieces
LOW = ((1, 0), (-1, 0), (0, 1), (0, -1))
def axis_data(S, ax):
    sl = slices(S, ax, 1); pcs = {l: pieces(sq) for l, sq in sl.items()}
    idx = {}
    for l, ps in pcs.items():
        for i, p in enumerate(ps):
            for s in p: idx[(l, s)] = (l, i)
    kids = {}; pars = {}; V = 0; E = 0
    for l, ps in pcs.items():
        for i, p in enumerate(ps):
            V += 1
            ch = {idx[(l - 1, (u + a, v + b))] for u, v in p for a, b in LOW if (l - 1, (u + a, v + b)) in idx}
            kids[(l, i)] = ch; E += len(ch)
            for c in ch: pars.setdefault(c, set()).add((l, i))
    T = sum(1 for k in kids if not kids[k]) + sum(1 for k in kids if k not in pars)
    sig = sum(max(0, len(kids[k]) - 1) for k in kids) + sum(max(0, len(v) - 1) for v in pars.values())
    return T, sig, E - V + 1
def morse(S):
    T = sig = b1 = 0
    for ax in range(3):
        t, s, b = axis_data(S, ax); T += t; sig += s; b1 += b
    return T, sig, b1
def gslack(S):
    T, sig, b1 = morse(S); return cost(S)['U'] - 3 * T - 3 * sig
if __name__ == '__main__':
    from tops import tops
    def show(name, S):
        T, sig, b1 = morse(S); u = cost(S)['U']; assert T == tops(S)[0]; assert not connected(S) or T == 6 - 2 * b1 + sig
        print(f"{name}: N={len(S)} U*={u} T={T} sigma={sig} b1={b1}  U*-3T-3sigma={u - 3*T - 3*sig}")
    n = 6
    show('O_6', octa(n)); show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0)))
    show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    ring = octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0)); show('ring of four (connected: %s)' % connected(ring), ring)
    S = octa(9); T = {h for h in S if not (abs(h[0]) + abs(h[1]) <= 2)}; show('O_9 with a tunnel along z', T)
    show('O_9 with cavity O_3', octa(9) - octa(3))
    S = octa(9) - {h for h in octa(9) if h[2] >= 5 and abs(h[0]) + abs(h[1]) <= 1}; show('O_9 with a pit from above', S)
    show('lambda: bar with two O_5', octa(5) | octa(5, (12, 0, 0)) | {(i, 0, 4) for i in range(0, 13, 2)} | {(i, 1, 4) for i in range(1, 12, 2)})
    for v in ((4,0,0),(2,2,2),(4,4,4),(8,3,3),(3,3,0),(5,4,3)): show(f'O_7+{v}', octa(7) | octa(7, v))
```

## `bridge.py`

```python
"""Section 43 of the note: two regular octahedra O_n and O_n + v that are not adjacent, joined by a connector of one or two sites.
For every such body: U*.  The sharp case of Conjecture R needs U* >= 37.     python3 bridge.py n"""
import sys
from gmin import *
from tops import tops
n = int(sys.argv[1]); A = octa(n); res = []
coatA = {add(h, r) for h in A for r in ROOTS} - A
R = 2 * n + 4
for x in range(0, R + 1):
    for y in range(0, x + 1):
        for z in range(0, y + 1):
            if (x + y + z) % 2: continue
            B = octa(n, (x, y, z))
            if A & B: continue
            coatB = {add(h, r) for h in B for r in ROOTS} - B
            if coatA & B: continue                                   # adjacent: covered by the union scans
            one = coatA & coatB
            for c in one:
                S = A | B | {c}; res.append((cost(S)['U'], (x, y, z), (c,)))
            cb = coatB - A
            for c1 in coatA - B:
                for r in ROOTS:
                    c2 = add(c1, r)
                    if c2 in cb and c1 not in one and c2 not in one:
                        S = A | B | {c1, c2}; res.append((cost(S)['U'], (x, y, z), (c1, c2)))
res.sort()
print(f"O_{n}, two copies not adjacent, connectors of one or two sites: {len(res)} bodies; least U* = {res[0][0]}; bodies with U* <= 36: {sum(1 for r in res if r[0] <= 36)}")
seen = set()
for u, v, c in res:
    if (u, v) in seen: continue
    seen.add((u, v))
    if len(seen) > 12: break
    S = A | octa(n, v) | set(c); print(f"   U* = {u}: v = {v}, connector {c}, tops {tops(S)[0]}")
```

## `gcheck.py`

```python
"""Section 43 of the note: Conjecture G (U* >= 6T - 18 for connected bodies with at least two sites) on the families of Section 42 and on the
bridged pairs of bridge.py."""
from gmin import *
from tops import tops
from psi import unions, boundary_moves, toggle
def slack(S): return cost(S)['U'] - 6 * tops(S)[0] + 18
tot = 0
for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
    v = [(slack(S), w) for w, ov, S in unions(a, b)]; tot += len(v)
    print(f"unions O_{a}, O_{b}: {len(v)} bodies, least slack {min(v)[0]} at v = {min(v)[1]}, with slack 0: {sum(1 for x in v if x[0] == 0)}", flush=True)
for n in (5, 6, 7, 8):
    S = octa(n); v = []
    for h in sorted(boundary_moves(S)):
        T = toggle(S, h)
        if h in S and not connected(T): continue
        v.append((slack(T), h))
    tot += len(v); print(f"one site from O_{n}: {len(v)} bodies, least slack {min(v)[0]}, with slack 0: {sum(1 for x in v if x[0] == 0)}", flush=True)
for N, n in ((6, 5), (7, 5), (7, 6), (6, 6), (8, 4)):
    A = octa(N); v = []
    for a in range(0, N + n + 1):
        for b in range(0, 3):
            for c in range(0, N + n + 1):
                if (a + b + c - (N - n)) % 2: continue
                B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); S = A | B1 | B2
                if not connected(S): continue
                if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue
                v.append((slack(S), (a, b, c)))
    tot += len(v); print(f"roof O_{N}, legs O_{n}: {len(v)} bodies, least slack {min(v)[0]} at {min(v)[1]}", flush=True)
print(f"{tot} bodies; G holds on all of them" )
```

## `gprime.py`

```python
"""Section 43 of the note.  Conjecture G: U* >= 6T - 18 for every connected body with at least two sites.
The stronger statement G': U* >= 3 T + 3 sigma (morse.py; the same as G when the three piece graphs are trees) is FALSE:
the search finds porous bodies that violate it.
  python3 gprime.py small NMAX        all connected sets with 2..NMAX sites up to translation
  python3 gprime.py search seed steps  annealing on U* - 3T - 3 sigma by single sites, from octahedra, unions, bridges, a ring, blobs"""
import sys, random, math
from gmin import *
from morse import morse, gslack
from psi import boundary_moves, toggle, unions
def norm(S):
    m = min(S); return frozenset((x - m[0], y - m[1], z - m[2]) for x, y, z in S)
if sys.argv[1] == 'small':
    level = {frozenset({(0, 0, 0)})}; tot = 0
    for n in range(1, int(sys.argv[2]) + 1):
        if n >= 2:
            best = None; g = None; hand = 0
            for S in level:
                T, sig, b1 = morse(set(S)); u = cost(set(S))['U']; v = u - 3 * T - 3 * sig; hand += b1 > 0
                if best is None or v < best[0]: best = (v, u, T, sig, b1)
                if g is None or u - 6 * T + 18 < g[0]: g = (u - 6 * T + 18, u, T)
            tot += len(level)
            print(f"{n} sites: {len(level)} sets ({hand} with a cycle in a piece graph); least U* - 6T + 18 = {g[0]} (U* = {g[1]}, T = {g[2]}); "
                  f"least U* - 3T - 3 sigma = {best[0]} (U* = {best[1]}, T = {best[2]}, sigma = {best[3]}, b1 = {best[4]})", flush=True)
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
    seed, steps = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); n = 5
    def blob(k):
        S = {(0, 0, 0)}
        while len(S) < k:
            h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
        return S
    starts = [(f'O_{k}', octa(k)) for k in (3, 4, 5, 6)]
    starts += [('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))), ('one-site bridge', octa(n) | {(n, 1, 0)} | octa(n, (2*n, 2, 0))),
               ('zig bridge', octa(n) | {(n, 1, 0), (n+1, 0, 0)} | octa(n, (2*n+1, 1, 0))),
               ('ring of four', octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0))),
               ('three in a row', octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (-(2*n-1), -1, 0)))]
    starts += [(f'O_5+{v}', S) for v, ov, S in unions(5, 5)][::4]
    starts += [(f'blob{k}_{i}', blob(k)) for k in (10, 25, 50) for i in range(3)]
    worst = None
    for name, S in starts:
        cur = gslack(S); s0 = cur; best = (cur, set(S)); mv = boundary_moves(S)
        for i in range(steps):
            T = 3.0 * (1 - i / steps) + 0.05
            h = rng.choice(mv); S2 = toggle(S, h)
            if len(S2) < 2 or (h in S and not connected(S2)): continue
            u = gslack(S2)
            if u <= cur or rng.random() < math.exp((cur - u) / T):
                S, cur = S2, u; mv = boundary_moves(S)
                if cur < best[0]: best = (cur, set(S))
        T_, sig, b1 = morse(best[1])
        if worst is None or best[0] < worst[0]: worst = (best[0], name)
        print(f"{name}: slack at start {s0}, least met {best[0]} (N = {len(best[1])}, U* = {cost(best[1])['U']}, T = {T_}, sigma = {sig}, b1 = {b1})", flush=True)
    print(f"seed {seed}, {steps} steps, {len(starts)} starts: least U* - 3T - 3 sigma = {worst[0]} (from {worst[1]}); violations of G': {'none' if worst[0] >= 0 else 'YES'}")
```

## `gsearch.py`

```python
"""Section 43 of the note: search for a connected body (at least two sites) with U* < 6 T - 18, T = number of local tops over the six directions.
python3 gsearch.py seed steps [starting temperature, default 3]"""
import sys, random, math
from gmin import *
from tops import tops
from psi import boundary_moves, toggle, unions
def slack(S):
    return cost(S)['U'] - 6 * tops(S)[0] + 18
def anneal(S, steps, rng, T0=3.0):
    cur = slack(S); best = (cur, set(S)); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.05
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = slack(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur < best[0]: best = (cur, set(S))
    return best
def blob(rng, n):
    S = {(0, 0, 0)}
    while len(S) < n:
        h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
    return S
if __name__ == '__main__':
    seed, steps = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); worst = None; T0 = float(sys.argv[3]) if len(sys.argv) > 3 else 3.0
    starts = [(f'O_{n}', octa(n)) for n in (2, 3, 4, 5, 6)]
    k = 5
    starts += [('tip next to tip', octa(k) | octa(k, (2*k-1, 1, 0))), ('one-site bridge', octa(k) | {(k, 1, 0)} | octa(k, (2*k, 2, 0))),
               ('zig bridge', octa(k) | {(k, 1, 0), (k+1, 0, 0)} | octa(k, (2*k+1, 1, 0))), ('twin tops', octa(k) | octa(k, (2, 0, 0))),
               ('three in a row', octa(k) | octa(k, (2*k-1, 1, 0)) | octa(k, (-(2*k-1), -1, 0)))]
    starts += [(f'O_5+{v}', S) for v, ov, S in unions(5, 5)][::3]
    starts += [(f'O_4+O_6+{v}', S) for v, ov, S in unions(4, 6)][::4]
    starts += [(f'blob{n}_{i}', blob(rng, n)) for n in (8, 15, 30, 60) for i in range(4)]
    for name, S in starts:
        s0 = slack(S); b, B = anneal(S, steps, rng, T0)
        if worst is None or b < worst[0]: worst = (b, name, sorted(B))
        print(f"{name}: slack at start {s0}, least slack met {b} (N = {len(B)}, U* = {cost(B)['U']}, T = {tops(B)[0]})", flush=True)
    print(f"seed {seed}, {steps} steps, {len(starts)} starts: least slack U* - 6T + 18 = {worst[0]} (from {worst[1]}); bodies with negative slack: {'none' if worst[0] >= 0 else worst[2]}")
```

## Output of `python3 wdef.py`

```
site: N=1 U*=15 W=-15 def1=0 def2=10 kappa=11 n2*=1
pair: N=2 U*=26 W=-16 def1=0 def2=14 kappa=16 n2*=2
O_2: N=6 U*=42 W=-18 def1=0 def2=20 kappa=26 n2*=6
O_3: N=19 U*=54 W=-18 def1=0 def2=24 kappa=42 n2*=18
O_4: N=44 U*=42 W=-18 def1=0 def2=20 kappa=58 n2*=38
O_5: N=85 U*=18 W=-18 def1=0 def2=12 kappa=74 n2*=62
O_6: N=146 U*=18 W=-18 def1=0 def2=12 kappa=90 n2*=78
O_8: N=344 U*=18 W=-18 def1=0 def2=12 kappa=122 n2*=110
tetra 4: N=20 U*=60 W=0 def1=0 def2=20 kappa=40 n2*=20
tetra 6: N=56 U*=60 W=12 def1=0 def2=16 kappa=60 n2*=44
tetra 9: N=165 U*=78 W=30 def1=0 def2=16 kappa=90 n2*=74
O_7+(1, 1, 0): N=280 U*=20 W=-16 def1=0 def2=12 kappa=112 n2*=100
O_7+(2, 2, 0): N=327 U*=34 W=-14 def1=0 def2=16 kappa=122 n2*=106
O_7+(3, 3, 0): N=370 U*=36 W=-12 def1=0 def2=16 kappa=132 n2*=116
O_7+(2, 2, 2): N=358 U*=24 W=-12 def1=0 def2=12 kappa=124 n2*=112
O_7+(2, 1, 1): N=322 U*=22 W=-14 def1=0 def2=12 kappa=118 n2*=106
O_7+(4, 0, 0): N=377 U*=54 W=-6 def1=0 def2=20 kappa=134 n2*=114
O_7+(6, 0, 0): N=418 U*=54 W=-6 def1=0 def2=20 kappa=150 n2*=130
O_7+(12, 0, 0): N=461 U*=51 W=-9 def1=0 def2=20 kappa=197 n2*=177
O_7+(13, 1, 0): N=462 U*=44 W=-16 def1=0 def2=20 kappa=204 n2*=184
O_7+(12, 1, 1): N=462 U*=46 W=-14 def1=0 def2=20 kappa=198 n2*=178
O_7+(12, 2, 0): N=462 U*=52 W=-8 def1=0 def2=20 kappa=200 n2*=180
O_7+(8, 3, 3): N=462 U*=54 W=-6 def1=0 def2=20 kappa=174 n2*=154
O_7+(4, 4, 4): N=443 U*=66 W=-6 def1=0 def2=24 kappa=154 n2*=130
O_7+(5, 4, 3): N=444 U*=54 W=-6 def1=0 def2=20 kappa=154 n2*=134
O_7 minus a vertex: N=230 U*=19 W=-14 def1=0 def2=11 kappa=104 n2*=93
O_7 plus a cell: N=232 U*=29 W=-16 def1=0 def2=15 kappa=110 n2*=95
plate 6x6 (z=0): N=49 U*=399 W=225 def1=0 def2=58 kappa=107 n2*=49
rod 10: N=10 U*=114 W=-24 def1=0 def2=46 kappa=56 n2*=10
block: N=108 U*=144 W=132 def1=0 def2=4 kappa=68 n2*=64
O_9 with tunnel along z: N=392 U*=300 W=168 def1=28 def2=16 kappa=112 n2*=124
O_9 with cavity O_3: N=470 U*=126 W=-36 def1=42 def2=12 kappa=96 n2*=126
```

## Output of `python3 tops.py`

```
O_7: N=231 U*=18 W=-18 def2=12 def1=0  tops T=6 (one-site 6, at 6 sites)  U*-3T=0  U*-(4T-6)=0  U*-(6T-18)=0
O_7 + cell of a vertex: N=232 U*=29 W=-16 def2=15 def1=0  tops T=7 (one-site 7, at 6 sites)  U*-3T=8  U*-(4T-6)=7  U*-(6T-18)=5
O_7 + site on a face: N=232 U*=24 W=-15 def2=13 def1=0  tops T=6 (one-site 6, at 6 sites)  U*-3T=6  U*-(4T-6)=6  U*-(6T-18)=6
O_7 + site over an edge: N=232 U*=32 W=-13 def2=15 def1=0  tops T=8 (one-site 8, at 7 sites)  U*-3T=8  U*-(4T-6)=6  U*-(6T-18)=2
O_7 + 5 sites on a vertex: N=236 U*=51 W=-9 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=21  U*-(4T-6)=17  U*-(6T-18)=9
O_7+(13, 1, 0): N=462 U*=44 W=-16 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=14  U*-(4T-6)=10  U*-(6T-18)=2
O_7+(12, 0, 0): N=461 U*=51 W=-9 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=21  U*-(4T-6)=17  U*-(6T-18)=9
O_7+(4, 0, 0): N=377 U*=54 W=-6 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=24  U*-(4T-6)=20  U*-(6T-18)=12
O_7+(2, 2, 2): N=358 U*=24 W=-12 def2=12 def1=0  tops T=6 (one-site 6, at 6 sites)  U*-3T=6  U*-(4T-6)=6  U*-(6T-18)=6
O_7+(1, 1, 0): N=280 U*=20 W=-16 def2=12 def1=0  tops T=6 (one-site 4, at 4 sites)  U*-3T=2  U*-(4T-6)=2  U*-(6T-18)=2
O_7+(4, 4, 4): N=443 U*=66 W=-6 def2=24 def1=0  tops T=12 (one-site 12, at 12 sites)  U*-3T=30  U*-(4T-6)=24  U*-(6T-18)=12
O_7+(8, 3, 3): N=462 U*=54 W=-6 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=24  U*-(4T-6)=20  U*-(6T-18)=12
O_7+(3, 3, 0): N=370 U*=36 W=-12 def2=16 def1=0  tops T=8 (one-site 8, at 8 sites)  U*-3T=12  U*-(4T-6)=10  U*-(6T-18)=6
O_7+(5, 4, 3): N=444 U*=54 W=-6 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=24  U*-(4T-6)=20  U*-(6T-18)=12
O_7+(12, 2, 0): N=462 U*=52 W=-8 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=22  U*-(4T-6)=18  U*-(6T-18)=10
three in a row: N=438 U*=70 W=-14 def2=28 def1=0  tops T=14 (one-site 14, at 14 sites)  U*-3T=28  U*-(4T-6)=20  U*-(6T-18)=4
O_7 + O_3+(4, 3, 3): N=250 U*=54 W=-9 def2=21 def1=0  tops T=9 (one-site 9, at 9 sites)  U*-3T=27  U*-(4T-6)=24  U*-(6T-18)=18
O_7 + O_4+(4, 4, 3): N=275 U*=53 W=-7 def2=19 def1=1  tops T=9 (one-site 9, at 9 sites)  U*-3T=26  U*-(4T-6)=23  U*-(6T-18)=17
O_7 + O_3+(8, 0, 0): N=249 U*=63 W=-9 def2=24 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=33  U*-(4T-6)=29  U*-(6T-18)=21
O_7 + O_3+(9, 1, 0): N=250 U*=68 W=-16 def2=28 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=38  U*-(4T-6)=34  U*-(6T-18)=26
O_7 + O_4+(10, 1, 0): N=275 U*=56 W=-16 def2=24 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=26  U*-(4T-6)=22  U*-(6T-18)=14
O_7 + O_5+(11, 1, 0): N=316 U*=44 W=-16 def2=20 def1=0  tops T=10 (one-site 10, at 10 sites)  U*-3T=14  U*-(4T-6)=10  U*-(6T-18)=2
```

## Output of `python3 morse.py`

```
O_6: N=146 U*=18 T=6 sigma=0 b1=0  U*-3T-3sigma=0
tip next to tip: N=292 U*=44 T=10 sigma=4 b1=0  U*-3T-3sigma=2
one-site bridge: N=293 U*=43 T=10 sigma=4 b1=0  U*-3T-3sigma=1
zig bridge: N=294 U*=54 T=12 sigma=6 b1=0  U*-3T-3sigma=0
ring of four (connected: True): N=584 U*=104 T=16 sigma=14 b1=2  U*-3T-3sigma=14
O_9 with a tunnel along z: N=392 U*=300 T=6 sigma=4 b1=2  U*-3T-3sigma=270
O_9 with cavity O_3: N=470 U*=126 T=6 sigma=0 b1=0  U*-3T-3sigma=108
O_9 with a pit from above: N=479 U*=75 T=6 sigma=0 b1=0  U*-3T-3sigma=57
lambda: bar with two O_5: N=181 U*=141 T=18 sigma=12 b1=0  U*-3T-3sigma=51
O_7+(4, 0, 0): N=377 U*=54 T=10 sigma=4 b1=0  U*-3T-3sigma=12
O_7+(2, 2, 2): N=358 U*=24 T=6 sigma=0 b1=0  U*-3T-3sigma=6
O_7+(4, 4, 4): N=443 U*=66 T=12 sigma=6 b1=0  U*-3T-3sigma=12
O_7+(8, 3, 3): N=462 U*=54 T=10 sigma=4 b1=0  U*-3T-3sigma=12
O_7+(3, 3, 0): N=370 U*=36 T=8 sigma=2 b1=0  U*-3T-3sigma=6
O_7+(5, 4, 3): N=444 U*=54 T=10 sigma=4 b1=0  U*-3T-3sigma=12
```

## Output of `python3 bridge.py 5` and `python3 bridge.py 6`

```
O_5, two copies not adjacent, connectors of one or two sites: 769 bodies; least U* = 43; bodies with U* <= 36: 0
   U* = 43: v = (10, 1, 1), connector ((5, 0, 1),), tops 10
   U* = 43: v = (10, 2, 0), connector ((5, 1, 0),), tops 10
   U* = 44: v = (6, 5, 3), connector ((1, 4, 1), (2, 4, 2)), tops 10
   U* = 44: v = (6, 6, 2), connector ((1, 4, 1), (2, 5, 1)), tops 10
   U* = 44: v = (8, 3, 3), connector ((4, 1, 1), (4, 2, 2)), tops 10
   U* = 44: v = (9, 2, 1), connector ((4, 1, 1),), tops 10
   U* = 44: v = (9, 3, 0), connector ((4, 1, -1), (5, 2, -1)), tops 10
   U* = 44: v = (9, 3, 2), connector ((4, 1, 1), (5, 2, 1)), tops 10
   U* = 45: v = (8, 2, 2), connector ((4, 1, 1),), tops 10
   U* = 46: v = (10, 0, 0), connector ((5, -1, 0),), tops 11
   U* = 49: v = (6, 5, 3), connector ((1, 4, 1), (1, 5, 2)), tops 10
   U* = 49: v = (6, 6, 2), connector ((1, 4, 1), (1, 5, 2)), tops 10
O_6, two copies not adjacent, connectors of one or two sites: 1226 bodies; least U* = 43; bodies with U* <= 36: 0
   U* = 43: v = (12, 1, 1), connector ((6, 0, 1),), tops 10
   U* = 43: v = (12, 2, 0), connector ((6, 1, 0),), tops 10
   U* = 44: v = (7, 6, 3), connector ((1, 5, 1), (2, 5, 2)), tops 10
   U* = 44: v = (7, 7, 2), connector ((1, 5, 1), (2, 6, 1)), tops 10
   U* = 44: v = (10, 3, 3), connector ((5, 1, 1), (5, 2, 2)), tops 10
   U* = 44: v = (11, 2, 1), connector ((5, 1, 1),), tops 10
   U* = 44: v = (11, 3, 0), connector ((5, 1, -1), (6, 2, -1)), tops 10
   U* = 44: v = (11, 3, 2), connector ((5, 1, 1), (6, 2, 1)), tops 10
   U* = 45: v = (10, 2, 2), connector ((5, 1, 1),), tops 10
   U* = 46: v = (12, 0, 0), connector ((6, -1, 0),), tops 11
   U* = 49: v = (7, 6, 3), connector ((1, 5, 1), (1, 6, 2)), tops 10
   U* = 49: v = (7, 7, 2), connector ((1, 5, 1), (1, 6, 2)), tops 10
```

## Output of `python3 gcheck.py`

```
unions O_7, O_7: 79 bodies, least slack 0 at v = (2, 0, 0), with slack 0: 1
unions O_9, O_9: 146 bodies, least slack 0 at v = (2, 0, 0), with slack 0: 1
unions O_5, O_8: 61 bodies, least slack 0 at v = (5, 0, 0), with slack 0: 1
unions O_6, O_9: 88 bodies, least slack 0 at v = (5, 0, 0), with slack 0: 1
one site from O_5: 206 bodies, least slack 1, with slack 0: 0
one site from O_6: 294 bodies, least slack 1, with slack 0: 0
one site from O_7: 398 bodies, least slack 1, with slack 0: 0
one site from O_8: 518 bodies, least slack 1, with slack 0: 0
roof O_6, legs O_5: 92 bodies, least slack 0 at (3, 0, 0)
roof O_7, legs O_5: 104 bodies, least slack 0 at (4, 0, 0)
roof O_7, legs O_6: 130 bodies, least slack 0 at (3, 0, 0)
roof O_6, legs O_6: 116 bodies, least slack 0 at (0, 2, 0)
roof O_8, legs O_4: 96 bodies, least slack 0 at (6, 0, 0)
2328 bodies; G holds on all of them
```

## Output of `python3 gprime.py small 7`

```
2 sites: 6 sets (0 with a cycle in a piece graph); least U* - 6T + 18 = 8 (U* = 26, T = 6); least U* - 3T - 3 sigma = 8 (U* = 26, T = 6, sigma = 0, b1 = 0)
3 sites: 50 sets (0 with a cycle in a piece graph); least U* - 6T + 18 = 13 (U* = 37, T = 7); least U* - 3T - 3 sigma = 13 (U* = 37, T = 7, sigma = 1, b1 = 0)
4 sites: 475 sets (3 with a cycle in a piece graph); least U* - 6T + 18 = 18 (U* = 48, T = 8); least U* - 3T - 3 sigma = 14 (U* = 44, T = 6, sigma = 4, b1 = 2)
5 sites: 4881 sets (72 with a cycle in a piece graph); least U* - 6T + 18 = 17 (U* = 59, T = 10); least U* - 3T - 3 sigma = 17 (U* = 59, T = 10, sigma = 4, b1 = 0)
6 sites: 52835 sets (1282 with a cycle in a piece graph); least U* - 6T + 18 = 24 (U* = 42, T = 6); least U* - 3T - 3 sigma = 18 (U* = 66, T = 9, sigma = 7, b1 = 2)
7 sites: 593382 sets (20508 with a cycle in a piece graph); least U* - 6T + 18 = 27 (U* = 45, T = 6); least U* - 3T - 3 sigma = 19 (U* = 73, T = 8, sigma = 10, b1 = 4)
651629 sets in all
```

## Output of `python3 gprime.py search 1 2500` (abridged: the six lowest of 27 starts and the summary; G' is violated)

```
blob25_0: slack at start 99, least met -268 (N = 245, U* = 1592, T = 69, sigma = 551, b1 = 244)
blob10_0: slack at start 70, least met -230 (N = 236, U* = 1486, T = 69, sigma = 503, b1 = 220)
blob25_2: slack at start 119, least met -229 (N = 281, U* = 1793, T = 78, sigma = 596, b1 = 262)
O_3: slack at start 36, least met -228 (N = 246, U* = 1524, T = 68, sigma = 516, b1 = 227)
blob10_1: slack at start 62, least met -228 (N = 242, U* = 1494, T = 80, sigma = 494, b1 = 210)
blob50_2: slack at start 127, least met -216 (N = 302, U* = 1980, T = 96, sigma = 636, b1 = 273)
...
seed 1, 2500 steps, 27 starts: least U* - 3T - 3 sigma = -268 (from blob25_0); violations of G': YES
```

## Output of `python3 gsearch.py 1 3000` (abridged: the six lowest of 42 starts and the summary)

```
O_5: slack at start 0, least slack met 0 (N = 85, U* = 18, T = 6)
O_6: slack at start 0, least slack met 0 (N = 146, U* = 18, T = 6)
O_5+(1, 1, 0): slack at start 2, least slack met 2 (N = 110, U* = 20, T = 6)
O_4+O_6+(2, 1, 1): slack at start 3, least slack met 3 (N = 156, U* = 21, T = 6)
O_5+(2, 2, 0): slack at start 4, least slack met 4 (N = 133, U* = 34, T = 8)
O_5+(6, 1, 1): slack at start 4, least slack met 4 (N = 166, U* = 46, T = 10)
...
seed 1, 3000 steps, 42 starts: least slack U* - 6T + 18 = 0 (from O_5); bodies with negative slack: none
```

## Output of `python3 gsearch.py 2 3000` (abridged)

```
O_5: slack at start 0, least slack met 0 (N = 85, U* = 18, T = 6)
O_6: slack at start 0, least slack met 0 (N = 146, U* = 18, T = 6)
O_5+(1, 1, 0): slack at start 2, least slack met 2 (N = 110, U* = 20, T = 6)
O_4+O_6+(2, 1, 1): slack at start 3, least slack met 3 (N = 156, U* = 21, T = 6)
O_5+(2, 2, 0): slack at start 4, least slack met 4 (N = 133, U* = 34, T = 8)
O_5+(6, 1, 1): slack at start 4, least slack met 4 (N = 166, U* = 46, T = 10)
...
seed 2, 3000 steps, 42 starts: least slack U* - 6T + 18 = 0 (from O_5); bodies with negative slack: none
```

## Output of `python3 gsearch.py 3 4000 1.0` (abridged: the six lowest of 47 starts)

```
O_5: slack at start 0, least slack met 0 (N = 85, U* = 18, T = 6)
O_6: slack at start 0, least slack met 0 (N = 146, U* = 18, T = 6)
zig bridge: slack at start 0, least slack met 0 (N = 172, U* = 54, T = 12)
twin tops: slack at start 0, least slack met 0 (N = 126, U* = 42, T = 10)
one-site bridge: slack at start 1, least slack met 1 (N = 171, U* = 43, T = 10)
tip next to tip: slack at start 2, least slack met 2 (N = 170, U* = 44, T = 10)
...
seed 3, 4000 steps, 47 starts: least slack U* - 6T + 18 = 0 (from O_5); bodies with negative slack: none
```

## Output of `python3 gsearch.py 4 4000 0.4` (abridged)

```
O_5: slack at start 0, least slack met 0 (N = 85, U* = 18, T = 6)
O_6: slack at start 0, least slack met 0 (N = 146, U* = 18, T = 6)
zig bridge: slack at start 0, least slack met 0 (N = 172, U* = 54, T = 12)
twin tops: slack at start 0, least slack met 0 (N = 126, U* = 42, T = 10)
one-site bridge: slack at start 1, least slack met 1 (N = 171, U* = 43, T = 10)
tip next to tip: slack at start 2, least slack met 2 (N = 170, U* = 44, T = 10)
...
seed 4, 4000 steps, 47 starts: least slack U* - 6T + 18 = 0 (from O_5); bodies with negative slack: none
```
