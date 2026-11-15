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
