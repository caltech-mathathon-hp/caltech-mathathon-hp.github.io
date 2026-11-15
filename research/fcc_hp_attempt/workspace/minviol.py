"""Section 45: small bodies that violate G_chi (U* >= 6T - 9 chi, pinch points resolved).  Annealing on slack + lam * size."""
import sys, random, math
from gmin import *
from tops import tops
from euler import chi_v
from psi import boundary_moves, toggle
def slack(S): return cost(S)["U"] - 6 * tops(S)[0] + 9 * chi_v(S, True)
seed = int(sys.argv[1]); lam = float(sys.argv[2]); steps = int(sys.argv[3]); rng = random.Random(seed)
best_all = None
for trial in range(int(sys.argv[4])):
    S = {(0, 0, 0)}
    while len(S) < rng.choice((12, 20, 30)):
        h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
    f = lambda X: slack(X) + lam * len(X)
    cur = f(S); mv = boundary_moves(S); small = None
    for i in range(steps):
        T = 3.0 * (1 - i / steps) + 0.05
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = f(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            sl = cur - lam * len(S)
            if sl < 0 and (small is None or len(S) < len(small[1])): small = (sl, set(S))
    if small and (best_all is None or len(small[1]) < len(best_all[1])): best_all = small
    print(trial, 'smallest violator in this run:', (len(small[1]), small[0]) if small else None, flush=True)
if best_all:
    B = best_all[1]; print('SMALLEST', len(B), 'slack', slack(B), 'U*', cost(B)['U'], 'T', tops(B)[0], 'chi', chi_v(B, True)); print(sorted(B))
