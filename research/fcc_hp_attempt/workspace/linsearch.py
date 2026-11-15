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
