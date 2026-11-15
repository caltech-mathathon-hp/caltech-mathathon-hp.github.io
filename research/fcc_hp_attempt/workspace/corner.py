"""Section 46: units at a site against the corners of faces at that site.
For a site h with set E of non-H neighbours and chain P's P (a subset of E with at most two elements), Theorem 5 gives
    alpha = number of x in E \\ P not adjacent to any element of P,
    beta >= beta- = number of x in E \\ P all of whose four common neighbours with h are in E (such an x cannot be a
                    chain P of an H-neighbour of h),
    gamma = 0 for |P| <= 1, and |K_a u K_b minus {a, b}| - 5 + (number of H's in K_a n K_b) for P = {a, b}.
u-(E) = min over P of alpha + beta- + gamma is a lower bound for the units located at h that depends on E only.
c1(E) = number of pairs (nu, line d) with h exposed for nu and both neighbours of h on the line empty: the silhouette runs
of one site at h.  Question: is 4 u-(E) >= 3 c1(E) for all E?"""
import itertools
from gmin import ROOTS
from chords import NUS, RNU, dot
K = {r: [q for q in ROOTS if dot(q, r) == 1] for r in ROOTS}
neg = lambda a: (-a[0], -a[1], -a[2])
def uminus(es):
    best = None
    E = sorted(es)
    for k in range(0, 3):
        for P in itertools.combinations(E, k):
            rest = [x for x in E if x not in P]
            alpha = sum(1 for x in rest if not any(dot(x, a) == 1 for a in P))
            beta = sum(1 for x in rest if all(q in es for q in K[x]))
            gamma = 0
            if k == 2:
                a, b = P; Ua = (set(K[a]) | set(K[b])) - {a, b}
                gamma = len(Ua) - 5 + sum(1 for q in set(K[a]) & set(K[b]) if q not in es)
            v = alpha + beta + gamma
            if best is None or v < best[0]: best = (v, P, alpha, beta, gamma)
    return best
def c1(es):
    n = 0
    for nu in NUS:
        if not all(r in es for r in RNU[nu]): continue
        for d in ROOTS:
            if d > (0, 0, 0) and dot(d, nu) == 0 and d in es and neg(d) in es: n += 1
    return n
bad = {}; tab = {}; tight = {}
for mask in range(1, 1 << 12):
    es = {ROOTS[i] for i in range(12) if mask >> i & 1}
    c = c1(es)
    if c == 0: continue
    u = uminus(es)[0]; key = (len(es), c)
    t = tab.setdefault(key, [10**9, 0]); t[0] = min(t[0], u); t[1] += 1
    if 4 * u < 3 * c: bad[key] = bad.get(key, 0) + 1
    if 4 * u == 3 * c: tight[key] = tight.get(key, 0) + 1
print("(number of empty neighbours, corners c1): least u-, number of sets")
for key in sorted(tab): print("  ", key, tab[key][0], tab[key][1], "  4u- < 3c1 in", bad.get(key, 0), "sets; equality in", tight.get(key, 0))
print("sets with 4 u- < 3 c1:", sum(bad.values()), "of", sum(t[1] for t in tab.values()), "sets with a corner")
