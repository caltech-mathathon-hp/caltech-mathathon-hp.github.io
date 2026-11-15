"""Section 46: search for a finite set with a negative increment M'_(n+1) - M'_n (n >= 3), or with M'_n < 0 for some n >= 4.
Score: min(least increment over n >= 3, least M'_n over n >= 4) / boundary.  Annealing by single sites, then nothing else.
    python3 isearch.py seed steps T0 kind      kind: octa | near | islands | unions | bridge | blobs"""
import sys, random, math
from fractions import Fraction
from gmin import *
from chordM3 import data3, M1
from ends import ends
from psi import boundary_moves, toggle, unions
from islands import island
def score(S):
    c, oo, ob, bb = data3(S); U = c['U']; p = c['boundary'] - 3 * c['nu1']; E = ends(oo, ob)
    top = int(2 * max(E)) + 3 if E else 4
    Ms = [M1(c, oo, ob, n) for n in range(3, top + 2)]
    inc = min(Ms[i + 1] - Ms[i] for i in range(len(Ms) - 1)); mm = min(Ms[1:])
    return float(min(inc, mm)) / c['boundary'], float(inc), float(mm), U
seed = int(sys.argv[1]); steps = int(sys.argv[2]); T0 = float(sys.argv[3]); kind = sys.argv[4]; rng = random.Random(seed)
if kind == 'octa': starts = [(f"O_{r}", octa(r)) for r in (5, 6, 7)]
if kind == 'near': starts = [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 without two vertices", octa(7) - {(6, 0, 0), (0, 6, 0)})]
if kind == 'islands': starts = [("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 4 at (1,1)", octa(9) | island(9, 4, True, (1, 1))), ("O_7 with island 3 at (0,1)", octa(7) | island(7, 3, True, (0, 1)))]
if kind == 'unions':
    U = list(unions(6, 6)); rng.shuffle(U); starts = [(f"O_6 u O_6+{v}", S) for v, ov, S in U[:8]]
if kind == 'bridge': starts = [("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_5 and a site (10,2,0)", octa(5) | octa(5, (10, 2, 0)) | {(5, 1, 0)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2)))]
if kind == 'blobs':
    starts = []
    for t in range(5):
        S = {(0, 0, 0)}
        while len(S) < rng.choice((40, 80, 120)):
            h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
        starts.append((f"blob {t}", S))
for name, S in starts:
    cur = score(S); s0 = cur; best = (cur, set(S)); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.003
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = score(S2)
        if u[0] <= cur[0] or rng.random() < math.exp((cur[0] - u[0]) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur[0] < best[0][0]: best = (cur, set(S))
    b = best[0]
    print(f"{name}: score {s0[0]:.4f} -> {b[0]:.4f}; at the end N = {len(best[1])}, U* = {b[3]}, least increment {b[1]:.1f}, least M'_n (n >= 4) {b[2]:.1f}", flush=True)
    if b[0] < 0: print("   NEGATIVE", sorted(best[1]), flush=True)
