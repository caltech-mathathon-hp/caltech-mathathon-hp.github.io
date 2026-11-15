"""Section 46: islands of the cheap orientation on a face of O_r, all sizes and positions (up to the symmetry of the face not used).
Reports the largest n with M_n < 0, the least slack of (K), the least Lam_n, by island size.
    python3 islands2.py r"""
import sys
from gmin import *
from lin import minlam
from chordM import data, M
from islands import island, supported
r = int(sys.argv[1]); O = octa(r)
for k in range(1, r):
    best = None; cnt = 0
    for a in range(0, r):
        for b in range(a, r):
            I = island(r, k, True, (a, b))
            if not supported(O, I): continue
            S = O | I; c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(3, top + 1) if M(c, oo, n) < 0]
            U = c['U']; ks = min((4 * U * L - 3 * sum(1 for x in oo if x <= L)) / 3 for L in set(oo)); m, n = minlam(c); cnt += 1
            rec = (max(bad) if bad else 0, ks, m, n, (a, b), U)
            if best is None: best = [rec, rec, rec]
            if rec[0] > best[0][0]: best[0] = rec
            if rec[1] < best[1][1]: best[1] = rec
            if rec[2] < best[2][2]: best[2] = rec
    if best:
        print(f"k = {k}: {cnt} positions; largest n with M_n < 0: {best[0][0]} (shift {best[0][4]}, U* = {best[0][5]}); least slack of (K): {best[1][1]:.2f} (shift {best[1][4]}, U* = {best[1][5]}); least Lam_n = {best[2][2]} at n = {best[2][3]} (shift {best[2][4]})", flush=True)
