"""Section 45: slopes of silhouette runs.
A chord with two open ends (chords.py) is a whole run of S on its line, exposed for one nu; call it a silhouette run.
For a silhouette run C with L sites in the plane of nu and one of the two neighbouring parallel lines of that plane, the
line has L + 1 sites next to C; the L - 1 of them that touch two sites of C are the inner ones.  C has a predecessor on
that side if L >= 2 and the inner sites are exactly a silhouette run, and a successor if the L + 1 sites are exactly one.
A start is a silhouette run without predecessor; it is the least run of max(1, number of its successors) slopes.
(S): 3 * slopes <= 4 U*, which is false (Section 45.6).      python3 slopes.py families | unions a b | near r"""
import sys
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
def slopes(S):
    """returns (number of slopes, number of starts, number of silhouette runs, list of start lengths with multiplicity = slopes)"""
    nsl = 0; nst = 0; H = 0; mins = []
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        ds = DNU[nu]
        for d in ds:
            others = [r for r in ROOTS if dot(r, nu) == 0 and r != d and r != (-d[0], -d[1], -d[2])]
            # the two sides: d2 with d2 + d also a root of the plane; side A uses a_k = h0 + d2 + k d, side B uses h0 - d2 - d + k d
            d2 = next(r for r in others if add(r, d) in others)
            runs = {}
            for h in F:
                if sub(h, d) in F: continue
                L = 1; g = add(h, d)
                while g in F: L += 1; g = add(g, d)
                if sub(h, d) not in S and g not in S: runs[h] = L
            H += len(runs)
            def side(h0, L, base):
                """base = first of the L + 1 neighbouring sites; returns (has predecessor, has successor)"""
                a = [base]
                for k in range(L): a.append(add(a[-1], d))
                pred = L >= 2 and a[1] in runs and runs[a[1]] == L - 1
                succ = a[0] in runs and runs[a[0]] == L + 1
                return pred, succ
            for h0, L in runs.items():
                pA, sA = side(h0, L, add(h0, d2)); pB, sB = side(h0, L, sub(sub(h0, d2), d))
                if not pA and not pB:
                    k = max(1, sA + sB); nst += 1; nsl += k; mins += [L] * k
    return nsl, nst, H, mins
def row(name, S, c=None):
    if c is None: c = cost(S)
    nsl, nst, H, mins = slopes(S)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, runs {H}, starts {nst}, slopes {nsl}, 4 U* - 3 slopes = {4 * c['U'] - 3 * nsl}, start lengths {sorted(set(mins))[:8]}")
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    def scan(name, bodies):
        cnt = 0; neg = 0; low = None
        for tag, S in bodies:
            c = cost(S); nsl = slopes(S)[0]; v = 4 * c['U'] - 3 * nsl; cnt += 1; neg += v < 0
            if low is None or v < low[0]: low = (v, tag, c['U'], nsl)
        print(f"{name}: {cnt} bodies; with 3 slopes > 4 U*: {neg}; least 4 U* - 3 slopes = {low[0]} ({low[1]}, U* = {low[2]}, slopes {low[3]})", flush=True)
    if mode == 'families':
        row("single site", {(0, 0, 0)}); row("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for r in range(2, 9): row(f"O_{r}", octa(r))
        for k in (4, 6, 9): row(f"tetrahedron {k}", tetra(k))
        for v in ((2, 0, 0), (4, 0, 0), (1, 1, 0), (2, 2, 2), (2, 2, 0), (13, 1, 0), (12, 0, 0)): row(f"O_7 u O_7+{v}", octa(7) | octa(7, v))
        row("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
        row("O_6 without a vertex", octa(6) - {(5, 0, 0)}); row("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
        row("rod of 10", {(i, -i, 0) for i in range(10)}); row("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
        row("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0)))
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
