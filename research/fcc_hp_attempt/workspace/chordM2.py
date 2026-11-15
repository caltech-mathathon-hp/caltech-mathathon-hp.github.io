"""Section 45: for which n does (M_n) fail?  For each body: the largest n with M_n < 0 (0 if none), n = 2, ..., longest chord + 3.
    python3 chordM2.py families | near r | bridge r | unions a b"""
import sys
from gmin import *
from chordM import data, M
def last_bad(S):
    c, oo = data(S); top = (max(oo) if oo else 3) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    return (max(bad) if bad else 0), c
def scan(name, bodies):
    worst = (0, None); cnt = 0; hist = {}
    for tag, S in bodies:
        b, c = last_bad(S); cnt += 1; hist[b] = hist.get(b, 0) + 1
        if b > worst[0]: worst = (b, tag, c['U'])
    print(f"{name}: {cnt} bodies; largest n with M_n < 0, by number of bodies: {dict(sorted(hist.items()))}; worst {worst}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    if mode == 'families':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        scan("named bodies", named)
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'bridge':
        r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A
        def gen():
            for x in range(0, 2 * r + 5):
                for y in range(0, x + 1):
                    for z in range(0, y + 1):
                        if (x + y + z) % 2: continue
                        B = octa(r, (x, y, z))
                        if A & B or coatA & B: continue
                        coatB = {add(h, s) for h in B for s in ROOTS} - B
                        for g in coatA & coatB: yield ((x, y, z), g), A | B | {g}
        scan(f"two O_{r} joined by one site", gen())
