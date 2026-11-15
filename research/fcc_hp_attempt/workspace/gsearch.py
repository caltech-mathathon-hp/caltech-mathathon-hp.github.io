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
