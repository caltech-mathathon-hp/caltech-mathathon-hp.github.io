"""Section 43 of the note: two regular octahedra O_n and O_n + v that are not adjacent, joined by a connector of one or two sites.
For every such body: U*.  The sharp case of Conjecture R needs U* >= 37.     python3 bridge.py n"""
import sys
from gmin import *
from tops import tops
n = int(sys.argv[1]); A = octa(n); res = []
coatA = {add(h, r) for h in A for r in ROOTS} - A
R = 2 * n + 4
for x in range(0, R + 1):
    for y in range(0, x + 1):
        for z in range(0, y + 1):
            if (x + y + z) % 2: continue
            B = octa(n, (x, y, z))
            if A & B: continue
            coatB = {add(h, r) for h in B for r in ROOTS} - B
            if coatA & B: continue                                   # adjacent: covered by the union scans
            one = coatA & coatB
            for c in one:
                S = A | B | {c}; res.append((cost(S)['U'], (x, y, z), (c,)))
            cb = coatB - A
            for c1 in coatA - B:
                for r in ROOTS:
                    c2 = add(c1, r)
                    if c2 in cb and c1 not in one and c2 not in one:
                        S = A | B | {c1, c2}; res.append((cost(S)['U'], (x, y, z), (c1, c2)))
res.sort()
print(f"O_{n}, two copies not adjacent, connectors of one or two sites: {len(res)} bodies; least U* = {res[0][0]}; bodies with U* <= 36: {sum(1 for r in res if r[0] <= 36)}")
seen = set()
for u, v, c in res:
    if (u, v) in seen: continue
    seen.add((u, v))
    if len(seen) > 12: break
    S = A | octa(n, v) | set(c); print(f"   U* = {u}: v = {v}, connector {c}, tops {tops(S)[0]}")
