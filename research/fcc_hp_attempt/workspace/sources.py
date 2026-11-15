"""Section 47: sources of silhouette runs.
Fix nu and k as in fans.py: chord direction c = b - a, lines of a plane nu.x = const ordered by phi(x) = x.(a + b)
(neighbouring lines differ by 3; phi grows away from the apex of the triangle), position on a line psi(x) = x.(b - a)
(steps of 2).  For a silhouette run P on the line phi - 3 and a silhouette run C on the line phi:
    P and C are ADJACENT if a site of C is a neighbour of a site of P (C meets the shadow of P, the |P| + 1 sites
    of the line phi that have a neighbour in P);  they are LINKED (J) if adjacent and |C| >= |P| + 1 - J.
A matching takes each run at most once as parent and at most once as child, in linked pairs only.
sigma_J(S) = least number of runs that are not a child, over all matchings (a maximum matching for each pair of lines).
Telescoping (Section 47.5, item 2), with Gam(L) = (n + 1 - L)+^2 / 2, so that (n + 1/2 - L)+ = Gam(L) - Gam(L + 1):
    sum over silhouette runs of (n + 1/2 - |C|)+  <=  sum over the unmatched children of Gam(|C|)
                                                      + sum over matched pairs of (Gam(|C|) - Gam(|P| + 1))+
The script asserts this for the matching it finds, and reports 4 U* - 3 sigma_J.
    python3 sources.py named | unions a b | near r | near2 r | islands r | bridge r | roof N n | special | pits r"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, DNU, dot, sub
from fans import FANS, REG, empties, neg
def runs(S):
    """silhouette runs: dict (nu, k, plane, phi) -> list of (psi of first site, length, first site, direction of the run)"""
    out = {}
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        for d in DNU[nu]:
            dd = d if (nu, d) in FANS else neg(d); k, a, b, Ma, Mb = FANS[(nu, dd)]; ab = add(a, b)
            for h in F:
                if add(h, dd) in F and sub(h, dd) in F: continue
                if sub(h, dd) in F: continue                      # h is the first site in direction dd
                L = 1; g = add(h, dd)
                while g in F: L += 1; g = add(g, dd)
                if sub(h, dd) in S or g in S: continue            # a blocked end
                out.setdefault((nu, k, dot(nu, h), dot(h, ab)), []).append((dot(h, dd), L, h, dd))
    return out
def matching(par, chi, J):
    """maximum matching between parents and children (lists of (psi, L, ...)), linked pairs only; returns child index -> parent index"""
    adj = []
    for (pc, Lc, *_) in chi:
        adj.append([i for i, (pp, Lp, *_) in enumerate(par) if pc <= pp + 2 * Lp - 1 and pp - 1 <= pc + 2 * (Lc - 1) and Lc >= Lp + 1 - J])
    mp = {}; mc = {}
    def aug(c, seen):
        for p in adj[c]:
            if p in seen: continue
            seen.add(p)
            if p not in mp or aug(mp[p], seen): mp[p] = c; mc[c] = p; return True
        return False
    for c in range(len(chi)): aug(c, set())
    return mc
def sigma(S, J=2, ns=(), want_sources=False):
    R = runs(S); unmatched = []; pairs = []
    for key, chi in R.items():
        nu, k, pl, phi = key; par = R.get((nu, k, pl, phi - 3), [])
        mc = matching(par, chi, J)
        for c, x in enumerate(chi):
            if c in mc: pairs.append((par[mc[c]][1], x[1]))
            else: unmatched.append((key, x))
    for n in ns:                                                  # the telescoping inequality
        Gam = lambda L: Fraction(max(0, n + 1 - L) ** 2, 2)
        lhs = sum(max(Fraction(0), n + Fraction(1, 2) - x[1]) for chi in R.values() for x in chi)
        rhs = sum(Gam(x[1]) for key, x in unmatched) + sum(max(Fraction(0), Gam(Lc) - Gam(Lp + 1)) for Lp, Lc in pairs)
        assert lhs <= rhs, (n, lhs, rhs)
    jog = sum(max(0, Lp + 1 - Lc) for Lp, Lc in pairs)
    if want_sources: return unmatched, pairs
    return len(unmatched), jog, sum(len(v) for v in R.values())
def rooted(S, unmatched):
    """number of unmatched children with no shape-irregular site in C or among the sites of the line before that are adjacent to C"""
    S = set(S); bad = 0
    for (nu, k, pl, phi), (psi, L, h, dd) in unmatched:
        k2, a, b, Ma, Mb = FANS[(nu, dd)]
        C = [add(h, (t * dd[0], t * dd[1], t * dd[2])) for t in range(L)]
        near = set(C) | {sub(x, a) for x in C} | {sub(x, b) for x in C}
        if not any(x in S and empties(S, x) not in REG for x in near): bad += 1
    return bad
def line(name, S):
    c = cost(S); out = []
    for J in (1, 2, 3):
        s, jog, tot = sigma(S, J, ns=(3, 7, 20, 60)); out.append(f"sigma_{J} = {s} (4U* - 3 sigma = {4 * c['U'] - 3 * s}, jogs {jog})")
    un, pairs = sigma(S, 2, want_sources=True)
    print(f"{name}: U* = {c['U']}, runs {tot}; " + "; ".join(out) + f"; sources without an irregular site next to them: {rooted(S, un)}; lengths of the sources (J = 2): {sorted(x[1][1] for x in un)}", flush=True)
def scan(name, bodies, J=2):
    cnt = 0; worst = None; hist = {}; noroot = 0; eq = []
    for tag, S in bodies:
        if len(S) < 2: continue
        c = cost(S); un, pairs = sigma(S, J, want_sources=True); s = len(un); cnt += 1
        if cnt % 25 == 1: sigma(S, J, ns=(4, 11, 38)); noroot += rooted(S, un)
        sl = 4 * c['U'] - 3 * s; hist[min(sl, 12)] = hist.get(min(sl, 12), 0) + 1
        if sl <= 0: eq.append((tag, c['U'], s))
        if worst is None or sl < worst[0]: worst = (sl, tag, c['U'], s)
    print(f"{name}: {cnt} bodies, J = {J}; least 4U* - 3 sigma = {worst[0]} ({worst[1]}, U* = {worst[2]}, sigma = {worst[3]}); bodies with 4U* - 3 sigma <= 0: {len(eq)} {eq[:6]}; "
          f"number of bodies by 4U* - 3 sigma (12 = 12 or more): {dict(sorted(hist.items()))}; sources without an irregular site next to them (every 25th body): {noroot}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
    J = 2
    if mode == 'named':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        named += [("O_6 without a vertex", octa(6) - {(5, 0, 0)}), ("O_6 with a site on a face", octa(6) | {(2, 2, 3)}), ("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2))),
                  ("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))), ("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))), ("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0))),
                  ("two O_5 and a site", octa(5) | octa(5, (10, 1, 1)) | {(5, 1, 0)}), ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))),
                  ("O_9 with island 3 at (0,0)", octa(9) | island(9, 3, True, (0, 0))), ("O_9 with island 3 at (1,2)", octa(9) | island(9, 3, True, (1, 2))), ("O_9 with island 5 at (1,1)", octa(9) | island(9, 5, True, (1, 1))),
                  ("O_13 with island 6 at (2,2)", octa(13) | island(13, 6, True, (2, 2))), ("O_9 with reversed island 3", octa(9) | island(9, 3, False, (1, 1))),
                  ("O_5 u O_8+(3,1,1)", octa(5) | octa(8, (3, 1, 1))),
                  ("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4)))]
        for nm, S in named: line(nm, S)
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)), J)
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))), J)
    if mode == 'near2':
        r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
        def gen():
            for h, g in itertools.combinations(mv, 2):
                T = toggle(toggle(S, h), g)
                if connected(T): yield (h, g), T
        scan(f"bodies at two sites from O_{r}", gen(), J)
    if mode == 'islands':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen(), J)
    if mode == 'pits':
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = {(x - 1, y - 1, z) for x, y, z in island(r, k, up, (a, b))}      # the same triangle in the face layer
                            if I <= O and connected(O - I): yield (up, k, a, b), O - I
        scan(f"one-layer pits in a face of O_{r}", gen(), J)
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
        scan(f"two O_{r} joined by one site", gen(), J)
    if mode == 'roof':
        N, n = int(sys.argv[2]), int(sys.argv[3]); A = octa(N)
        def gen():
            for a in range(0, N + n + 1):
                for b in range(0, 3):
                    for c in range(0, N + n + 1):
                        if (a + b + c - (N - n)) % 2: continue
                        B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); T = A | B1 | B2
                        if not connected(T): continue
                        if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue
                        yield (a, b, c), T
        scan(f"roof O_{N} over two legs O_{n}", gen(), J)
    if mode == 'special':
        sp = [("O_9 with a cavity O_3", octa(9) - octa(3)), ("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
              ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
              ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
              ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
              ("two O_7 tip to tip", octa(7) | octa(7, (12, 0, 0))), ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
              ("O_8 and O_4 on a vertex", octa(8) | octa(4, (8, 0, 0))), ("O_8 and O_4 on a face", octa(8) | octa(4, (4, 4, 4))),
              ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}), ("O_7 with twin tops (2,0,0)", octa(7) | octa(7, (2, 0, 0))),
              ("two O_6 vertex to vertex", octa(6) | octa(6, (11, 1, 0))), ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})]
        for nm, S in sp: line(nm, S)
