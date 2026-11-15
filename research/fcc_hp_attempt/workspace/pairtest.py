"""Lemma 50, test of the pairing over all defects.  For a piece (the piece x, y > 0 without its two tips, and the piece
x < 0 < y), every defect of kind 'a' (two neighbouring sites of a row) and of kind 'b' (the right ends of two
consecutive rows) in the rows zmin <= z <= n - ztop is combined with nothing, and with every (or 6000 random) mirror
defects in the lower half; surface.pairing must return a perfect matching of the rest into adjacent pairs."""
import sys, random
from surface import *
def defects(sf, key, half, zmin, ztop):
    rows = sf.pieces[key]; out = []
    for z in [z for z in rows if zmin <= half * z <= sf.n - ztop]:
        r = rows[z]
        for i in range(len(r) - 1): out.append(('a', abs(z), (r[i], r[i + 1])))
        z2 = z + half
        if z2 in rows and half * z2 <= sf.n - ztop and sf.eta(r[-1]) == 1 and sf.eta(rows[z2][-1]) == 1 and adj(r[-1], rows[z2][-1]): out.append(('b', abs(z), (r[-1], rows[z2][-1])))
    return out
if __name__ == '__main__':
    rng = random.Random(4); zmin, ztop = int(sys.argv[3]), int(sys.argv[4])
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
        sf = Surface(n); res = {}
        for key in [(1, 1), (-1, 1)]:
            rows = sf.rows(key); tips = {rows[0][0], rows[-1][0]} if key == (1, 1) else set()
            up = defects(sf, key, 1, zmin, ztop); dn = defects(sf, key, -1, zmin, ztop)
            combos = [(u, None) for u in up] + [(None, d) for d in dn] + [(None, None)]
            allpairs = [(u, d) for u in up for d in dn]
            combos += allpairs if len(allpairs) <= 6000 else rng.sample(allpairs, 6000)
            fails = 0
            for u, d in combos:
                R = set(tips)
                for x in (u, d):
                    if x: R |= set(x[2])
                m = pairing(rows, R)
                if m is None: fails += 1
                else: assert len(m) * 2 == sum(len(r) for r in rows) - len(R) and all(adj(a, b) for a, b in m) and len({h for p in m for h in p}) == 2 * len(m)
            res[key] = (len(up), len(combos), fails)
        print(f"n = {n}, defects in rows {zmin} <= |z| <= {n - ztop}: " + "; ".join(f"piece {k}: {v[0]} defects in each half, {v[1]} combinations, no pairing in {v[2]}" for k, v in res.items()), flush=True)
