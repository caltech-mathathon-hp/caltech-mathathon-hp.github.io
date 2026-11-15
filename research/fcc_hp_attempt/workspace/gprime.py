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
