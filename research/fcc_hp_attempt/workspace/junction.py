"""Section 42 of the note: search for a cheap junction between two lumps.
Start: O_a and O_b + v, touching or overlapping in at most 10% of the smaller one.  Only sites within graph distance r
of the contact (sites of one octahedron that lie in, or next to, the other) may be added or removed; the body must stay
connected.  Steepest descent on U* = 2G (gmin.cost), then simulated annealing from the result and a second descent.
The excess of a body is n2* - 16 (3N/2)^(1/3): what it holds beyond one octahedron of its size.  Without a guard the
search wins by filling the gap until the two lumps are one (U* 28 and 30 for O_6, O_6, with negative excess), so the
score adds a penalty when the excess falls below 0.4 times the excess of the two lumps apart.
The sharp form of the capacity bound L4 says: no connected body has U* <= 36 and an excess that grows with its size.
    python3 junction.py a b r [annealing steps]"""
import sys, random, math
from gmin import *

def region(A, B, r):
    K = {h for h in A if h in B or any(add(h, s) in B for s in ROOTS)} | {h for h in B if any(add(h, s) in A for s in ROOTS)}
    M = set(K); front = set(K)
    for _ in range(r):
        front = {add(h, s) for h in front for s in ROOTS} - M; M |= front
    return M

def moves(S, M):
    out = []
    for h in M:
        if h in S: out.append(h)
        elif any(add(h, s) in S for s in ROOTS): out.append(h)
    return out

def toggle(S, h):
    T = set(S); T.symmetric_difference_update({h}); return T

EMIN = 0.0
def excess(c):
    """doubly decorated sites beyond the capacity 16 (3N/2)^(1/3) of one octahedron with as many sites"""
    return c['n2'] - 16 * (1.5 * c['size']) ** (1 / 3)

def score(S):
    """U*, plus a penalty when the excess falls below EMIN (so that the search cannot win by fusing the two lumps)"""
    c = cost(S); return c['U'] + 2 * max(0.0, EMIN - excess(c))

def descend(S, M):
    cur = score(S)
    while True:
        best = None
        for h in moves(S, M):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            u = score(T)
            if u < cur and (best is None or u < best[0]): best = (u, T)
        if best is None: return S, cur
        cur, S = best

def anneal(S, M, steps, rng, T0=2.0):
    cur = score(S); best = (cur, S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.05
        h = rng.choice(moves(S, M)); S2 = toggle(S, h)
        if h in S and not connected(S2): continue
        u = score(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u
            if cur < best[0]: best = (cur, S)
    return best

if __name__ == '__main__':
    a, b, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); steps = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = random.Random(11); A = octa(a); B0 = octa(b); small = min(len(A), len(B0)); res = []
    sep = cost(A)['n2'] + cost(B0)['n2'] - 16 * (1.5 * (len(A) + len(B0))) ** (1 / 3)      # excess of the two lumps apart
    import junction; junction.EMIN = 0.4 * sep
    print(f"O_{a}, O_{b}: apart, the two lumps have U* = 36 and excess {sep:.1f}; the search keeps the excess above {0.4 * sep:.1f}", flush=True)
    for x in range(0, a + b + 1):
        for y in range(0, x + 1):
            for z in range(0, y + 1):
                if (x + y + z - (a - b)) % 2: continue
                B = octa(b, (x, y, z)); S = A | B
                if len(A & B) > 0.1 * small or not connected(S): continue
                M = region(A, B, r); c0 = cost(S)
                S1, f1 = junction.descend(S, M)
                if steps:
                    f2, S2 = junction.anneal(S1, M, steps, rng); S2, f2 = junction.descend(S2, M)
                    if f2 < f1: S1, f1 = S2, f2
                c = cost(S1)
                res.append((c['U'], excess(c), (x, y, z), len(A & B), len(S1 - S), len(S - S1), c0['U'], excess(c0)))
                print(f"v = {(x, y, z)}: overlap {len(A & B)}; start U* {c0['U']}, excess {excess(c0):.1f}; after search U* {c['U']}, excess {excess(c):.1f} (added {len(S1 - S)}, removed {len(S - S1)})", flush=True)
    res.sort()
    bad = [x for x in res if x[0] <= 36 and x[1] > 0]
    print(f"O_{a}, O_{b}, radius {r}, annealing steps {steps}: {len(res)} starts; least U* with excess above the bound: {min(x[0] for x in res if x[1] >= 0.4 * sep - 1e-9) if any(x[1] >= 0.4 * sep - 1e-9 for x in res) else None}; "
          f"bodies with U* <= 36 and positive excess: {len(bad)}")
    for x in bad: print("   ALARM", x)
