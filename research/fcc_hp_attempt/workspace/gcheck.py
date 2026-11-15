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
