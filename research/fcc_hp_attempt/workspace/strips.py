import sys
import surface as sv
from surface import *
from pairtest import defects
def hamilton_cost(rows, R):
    T = len(rows); best = [dict() for _ in range(T + 1)]; best[0][None] = 0
    for i in range(T):
        for last, cost in list(best[i].items()):
            if all(h in R for h in rows[i]):
                best[i+1][last] = min(best[i+1].get(last, 99), cost); continue
            for width in (1, 2):
                if i + width > T: continue
                for t in band_traversals(rows, i, width, R):
                    if last is not None and not adj(last, t[0]): continue
                    best[i+width][t[-1]] = min(best[i+width].get(t[-1], 99), cost + (width == 2))
    return min(best[T].values()) if best[T] else None
for n in (14, 16, 18):
    sf = Surface(n)
    for key in [(1,1), (-1,1)]:
        rows = sf.rows(key); tips = {rows[0][0], rows[-1][0]} if key == (1,1) else set()
        up = defects(sf, key, 1, 4, 9); dn = defects(sf, key, -1, 4, 9); hist = {}
        for u in up + [None]:
            for d in dn + [None]:
                R = set(tips)
                for x in (u, d):
                    if x: R |= set(x[2])
                c = hamilton_cost(rows, R); hist[c] = hist.get(c, 0) + 1
        print(n, key, 'defects per half', len(up), 'strips used -> cases', dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0]))))
