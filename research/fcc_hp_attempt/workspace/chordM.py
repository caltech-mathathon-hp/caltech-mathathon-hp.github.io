"""Section 45: the chord count (M_n).  With H, Len of chords.py, p = d - 3 nu1, U = U*, and
    Dn = sum over the chords C with two open ends and at most n sites of (n + 1/2 - |C|),
    Dn+ = sum over those with more than n sites of (|C| - n - 1/2),      B = d - Len + H/2  (>= 0, proved),
the identity   Lam_n = M_n + 3 B + 3 Dn+,   M_n = (2n^2 - 3n) U + 3n (H - p) - 3 Dn   holds for every finite set.
(M_n): M_n >= 0.     python3 chordM.py families | near r | small N"""
import sys
from fractions import Fraction
from gmin import *
from chords import chords
from lin import lam
HALF = Fraction(1, 2)
def data(S, c=None):
    if c is None: c = cost(S)
    oo = sorted(x[3] for x in chords(S) if x[4] == 2)
    return c, oo
def M(c, oo, n):
    U = c['U']; p = c['boundary'] - 3 * c['nu1']; H = len(oo)
    Dn = sum(n + HALF - L for L in oo if L <= n)
    return (2 * n * n - 3 * n) * U + 3 * n * (H - p) - 3 * Dn
def check_identity(c, oo, n):
    H = len(oo); B = c['boundary'] - sum(oo) + HALF * H; Dp = sum(L - n - HALF for L in oo if L > n)
    assert lam(c, n) == M(c, oo, n) + 3 * B + 3 * Dp
def minM(S, c=None, nmax=None, n0=3):
    c, oo = data(S, c); top = (max(oo) if oo else 3) + 3
    best = min((M(c, oo, n), n) for n in range(n0, max(top, n0 + 1) + 1))
    for n in (3, 5, 8): check_identity(c, oo, n)
    return best, c, oo
def line(name, S):
    (m, n), c, oo = minM(S); H = len(oo); p = c['boundary'] - 3 * c['nu1']
    print(f"{name}: N = {len(S)}, U* = {c['U']}, H = {H}, U + p - H = {c['U'] + p - H}, least M_n = {float(m):.1f} at n = {n}")
    return m
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'families':
        line("single site", {(0, 0, 0)}); line("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for r in range(2, 10): line(f"O_{r}", octa(r))
        for k in (4, 6, 9): line(f"tetrahedron {k}", tetra(k))
        for v in ((2, 0, 0), (4, 0, 0), (1, 1, 0), (2, 2, 2), (2, 2, 0), (13, 1, 0)): line(f"O_7 u O_7+{v}", octa(7) | octa(7, v))
        line("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
        line("O_6 without a vertex", octa(6) - {(5, 0, 0)}); line("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
        line("rod of 10", {(i, -i, 0) for i in range(10)}); line("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
        from psi import unions
        for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
            worst = None; cnt = 0; neg = 0
            for v, ov, S in unions(a, b):
                (m, n), c, oo = minM(S); cnt += 1; neg += m < 0
                if worst is None or m < worst[0]: worst = (m, n, v, c['U'])
            print(f"unions O_{a}, O_{b}+v: {cnt} bodies, with M_n < 0: {neg}; least M_n = {float(worst[0]):.1f} at n = {worst[1]} (v = {worst[2]}, U* = {worst[3]})")
    if mode == 'near':
        from psi import boundary_moves, toggle
        r = int(sys.argv[2]); S = octa(r); worst = None; cnt = 0; neg = 0
        for h in sorted(boundary_moves(S)):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            (m, n), c, oo = minM(T); cnt += 1; neg += m < 0
            if worst is None or m < worst[0]: worst = (m, n, h, c['U'])
        print(f"O_{r}: {cnt} bodies at one site; with M_n < 0: {neg}; least M_n = {float(worst[0]):.1f} at n = {worst[1]} (site {worst[2]}, U* = {worst[3]})")
    if mode == 'small':
        NMAX = int(sys.argv[2]); level = {frozenset({(0, 0, 0)})}; tot = 0; neg = 0; worst = None
        def norm(S):
            m = min(S); return frozenset((h[0] - m[0], h[1] - m[1], h[2] - m[2]) for h in S)
        for N in range(1, NMAX + 1):
            w = None
            for S in level:
                (m, n), c, oo = minM(set(S), n0=2); tot += 1; neg += m < 0
                if w is None or m < w[0]: w = (m, n, sorted(S))
            print(f"N = {N}: {len(level)} connected sets, least M_n (n >= 2) = {float(w[0]):.1f} at n = {w[1]}", flush=True)
            if N < NMAX: level = {norm(set(S) | {add(h, r)}) for S in level for h in S for r in ROOTS if add(h, r) not in S}
        print("sets:", tot, "with M_n < 0:", neg)
