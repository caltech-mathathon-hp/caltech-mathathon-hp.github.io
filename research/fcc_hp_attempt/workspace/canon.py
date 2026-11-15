"""Check of the remark after Lemma 51: the run ends chosen by surface.run_ends are the path ends shifted by (sign x, sign y, 0) of their piece, whenever the cut pair is in slices |z| >= 2."""
import sys
from surface import *
import interior3
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
    N = n - 2; sf = Surface(n); size = N * (2 * N * N + 1) // 3; cnt = bad = 0
    for c1 in range(size // 4 + 1, (size - 1) // 2 + 1):
        cuts = [c1, size - c1]
        if min(min(abs(z), abs(z + 1)) if o == 0 else abs(z) for z, o in (interior3.slice_of(N, c) for c in cuts)) < 2: continue
        sites, info = interior3.build(N, cuts, lambda p, q: sf.run_ends(p, q) is not None)
        for c in cuts:
            p, q = sites[c - 1], sites[c]; e, f, kind = sf.run_ends(p, q); s = sf.piece_of(e); cnt += 1
            if e != (p[0] + s[0], p[1] + s[1], p[2]) or f != (q[0] + s[0], q[1] + s[1], q[2]): bad += 1
            if kind == 'a' and e[2] != p[2]: bad += 1
    print(f"n = {n}: cut pairs {cnt}, run ends not of the form path end + (sign x, sign y, 0): {bad}")
