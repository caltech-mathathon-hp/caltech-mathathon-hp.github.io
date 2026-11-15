"""Section 47: end-sources.  A regular ridge site h (E(h) = R_nu u R_nu', the two octants sharing the step r0) has on
each of its two faces mu two open ends: with R_mu = {r0, r1, r2} the chords of mu that start at h run in the
directions c1 = r1 - r0 and c2 = r2 - r0, and h - c1, h - c2 are empty.  A ridge segment is a maximal run of regular
ridge sites of one ridge on a line (direction c1 - c2).  For (segment, face mu, direction c) order the sites of the
segment from the tip side: for c = c1 by increasing position in direction c2 - c1 (the chords of a fan grow that way).
Going through the sites in this order, an end whose chord has two open ends (length L) is
    COVERED   if the last such end before it on the segment had a chord of at most L - 1 sites,
    an END-SOURCE otherwise (the first one of the segment, or one whose chord did not grow).
Sigma(S) = number of end-sources.  Telescoping per end (Section 47.5, item 3):
    sum over the ends at regular ridge sites with two-open-ended chords of (n/2 + 1/4 - L/2)+
        <=  sum over the end-sources of (n + 1 - L)+^2 / 4.
The script asserts this, and the lower bound LB_n <= M'_n obtained from it:
    LB_n = (2n^2 - 3n) U* - 9n def1 + n sum_h c(h) - (3/4) sum_{end-sources} (n + 1 - L)+^2
           - 3 sum over the other open ends of their deficits,          c(h) = 9 - 3 deg(h) + (3/2) o(h).
Reported: U*, Sigma, 8 U* - 3 Sigma, the lengths L of the end-sources, and Sigma split into first ends and breaks.
    python3 endsrc.py named | special | unions a b | near r | near2 r | islands r | pits r | bridge r | roof N n"""
import sys, itertools
from fractions import Fraction
from gmin import *
from chords import NUS, RNU, dot, sub, chords
from fans import REG, empties, neg, nbr
Q = Fraction(1, 4)
def end_sources(S):
    """returns (list of (L, kind) for the end-sources, list of L for all two-open-ended chord ends at regular ridge sites,
    number of open ends of every kind at regular ridge sites)"""
    S = set(S); E = {}
    def em(h):
        if h not in E: E[h] = empties(S, h)
        return E[h]
    F = {nu: {h for h in S if all(add(h, r) not in S for r in RNU[nu])} for nu in NUS}
    ridge = {h: REG[em(h)][1] for h in S if em(h) in REG and REG[em(h)][0] == 'ridge'}
    src = []; allL = []; nopen = 0
    done = set()
    for h, pair in ridge.items():
        if (h, pair) in done: continue
        nu, nu2 = tuple(pair); r0 = [r for r in RNU[nu] if r in RNU[nu2]][0]
        r1, r2 = [r for r in RNU[nu] if r != r0]; dr = sub(r1, r2)            # ridge direction
        g = h
        while ridge.get(sub(g, dr)) == pair: g = sub(g, dr)
        seg = [g]; done.add((g, pair))
        while ridge.get(add(seg[-1], dr)) == pair: seg.append(add(seg[-1], dr)); done.add((seg[-1], pair))
        for mu in (nu, nu2):
            q1, q2 = [r for r in RNU[mu] if r != r0]
            for c, other in ((sub(q1, r0), sub(q2, r0)), (sub(q2, r0), sub(q1, r0))):
                away = sub(other, c)                                         # the chords of direction c grow in this direction
                assert away in (dr, neg(dr))
                order = seg if away == dr else seg[::-1]
                last = None
                for x in order:
                    assert sub(x, c) not in S
                    L = 1; y = add(x, c)
                    while y in F[mu]: L += 1; y = add(y, c)
                    nopen += 1
                    if y in S: continue                                      # blocked at the far end
                    allL.append(L)
                    if last is None: src.append((L, 'first'))
                    elif L < last + 1: src.append((L, 'break'))
                    last = L
    return src, allL, nopen
def bound(S, c, n, src=None, allL=None):
    """LB_n and M'_n"""
    from chordM3 import data3, M1
    if src is None: src, allL, nopen = end_sources(S)
    cc, oo, ob, bb = data3(S, c); U = c['U']; d1 = c['surface'] - c['nu1']
    sumc = 9 * c['surface'] - 3 * c['boundary'] + Fraction(3, 2) * (2 * len(oo) + len(ob))
    tele = sum(Fraction(max(0, n + 1 - L) ** 2, 4) for L, kind in src)
    reg = sum(max(Fraction(0), Fraction(n, 2) + Q - Fraction(L, 2)) for L in allL)
    assert reg <= tele, (n, reg, tele)
    total = sum(2 * max(Fraction(0), Fraction(n, 2) + Q - Fraction(L, 2)) for L in oo) + sum(max(Fraction(0), Fraction(n, 2) + Q - L) for L in ob)
    LB = (2 * n * n - 3 * n) * U - 9 * n * d1 + n * sumc - 3 * tele - 3 * (total - reg)
    M = M1(c, oo, ob, n); assert LB <= M, (n, LB, M)
    return LB, M
def line(name, S):
    c = cost(S); src, allL, nopen = end_sources(S); s = len(src)
    for n in (4, 9, 38, 150): bound(S, c, n, src, allL)
    fb = (sum(1 for L, k in src if k == 'first'), sum(1 for L, k in src if k == 'break'))
    hist = {}
    for L, k in src: hist[L] = hist.get(L, 0) + 1
    print(f"{name}: U* = {c['U']}, Sigma = {s} (first ends {fb[0]}, breaks {fb[1]}), 8U* - 3 Sigma = {8 * c['U'] - 3 * s}; end-sources by length of chord: {dict(sorted(hist.items()))}", flush=True)
def scan(name, bodies):
    cnt = 0; worst = None; hist = {}; eq = []; nb = 0
    for tag, S in bodies:
        if len(S) < 2: continue
        c = cost(S); src, allL, nopen = end_sources(S); s = len(src); cnt += 1; nb += sum(1 for L, k in src if k == 'break')
        if cnt % 20 == 1:
            for n in (5, 38): bound(S, c, n, src, allL)
        sl = 8 * c['U'] - 3 * s; hist[min(sl, 24)] = hist.get(min(sl, 24), 0) + 1
        if sl <= 0: eq.append((tag, c['U'], s))
        if worst is None or sl < worst[0]: worst = (sl, tag, c['U'], s)
    print(f"{name}: {cnt} bodies; least 8U* - 3 Sigma = {worst[0]} ({worst[1]}, U* = {worst[2]}, Sigma = {worst[3]}); bodies with 8U* - 3 Sigma <= 0: {len(eq)} {eq[:6]}; "
          f"breaks in all bodies together: {nb}; number of bodies by 8U* - 3 Sigma (24 = 24 or more): {dict(sorted(hist.items()))}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    from islands import island, supported
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
    if mode == 'special':
        sp = [("O_7 with a one-site cavity", octa(7) - {(0, 0, 0)}),
              ("ring of four O_5", octa(5) | octa(5, (6, 0, 0)) | octa(5, (6, 6, 0)) | octa(5, (0, 6, 0))),
              ("three O_6 in a row, vertex to vertex", octa(6) | octa(6, (11, 1, 0)) | octa(6, (22, 2, 0))),
              ("three O_6 at a right angle", octa(6) | octa(6, (11, 1, 0)) | octa(6, (1, 11, 0))),
              ("two O_7 along an axis, offset 6", octa(7) | octa(7, (6, 0, 0))),
              ("two O_6 joined by a zigzag", octa(6) | octa(6, (13, 1, 0)) | {(6, 1, 0), (7, 0, 0)}),
              ("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})]
        for nm, S in sp: line(nm, S)
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'near2':
        r = int(sys.argv[2]); S = octa(r); mv = sorted(boundary_moves(S))
        def gen():
            for h, g in itertools.combinations(mv, 2):
                T = toggle(toggle(S, h), g)
                if connected(T): yield (h, g), T
        scan(f"bodies at two sites from O_{r}", gen())
    if mode in ('islands', 'pits'):
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if mode == 'islands':
                                if supported(O, I): yield (up, k, a, b), O | I
                            else:
                                P = {(x - 1, y - 1, z) for x, y, z in I}             # the same triangle one layer lower, in the face
                                if P <= O and all(x + y + z == r - 1 for x, y, z in P) and connected(O - P): yield (up, k, a, b), O - P
        scan(f"{'islands on' if mode == 'islands' else 'one-layer pits in'} a face of O_{r}", gen())
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
        scan(f"roof O_{N} over two legs O_{n}", gen())
