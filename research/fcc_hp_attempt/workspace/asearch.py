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
