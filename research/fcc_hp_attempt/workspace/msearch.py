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
