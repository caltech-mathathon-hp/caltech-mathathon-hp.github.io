"""Exact cost of a shape (Section 4 of the note): G(S) = boundary(S) - (3/2)(nu_1 + nu_2), where nu_1 is the size of a
maximum matching between surface sites and coat sites and nu_2 the largest number of coat sites that can be assigned
with every surface site used at most twice.  U*(S) = 2 G(S) is the least number of defect units of any decoration of S,
and n2*(S) = nu_2 - nu_1 the number of doubly decorated sites in a decoration that attains it.
main: the values of Section 8 that are used as a test."""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching
ROOTS = [(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0), (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]
add = lambda a, b: (a[0] + b[0], a[1] + b[1], a[2] + b[2])

def octa(n, c=(0, 0, 0)):
    """regular octahedron with n sites per edge centred at c; c must have the parity that makes the vertices lattice sites"""
    m = n - 1
    return {(c[0] + x, c[1] + y, c[2] + z) for x in range(-m, m + 1) for y in range(-m + abs(x), m - abs(x) + 1)
            for z in range(-m + abs(x) + abs(y), m - abs(x) - abs(y) + 1, 2)}

def tetra(k):
    return {(b + c, a + c, a + b) for a in range(k) for b in range(k - a) for c in range(k - a - b)}

def cost(S):
    """returns dict with U (= 2G), n2, nu1, nu2, boundary, surface, coat"""
    surf = []; coat = {}; rows = []; cols = []; bd = 0
    for h in S:
        nb = [g for g in (add(h, r) for r in ROOTS) if g not in S]
        if not nb: continue
        i = len(surf); surf.append(h); bd += len(nb)
        for g in nb:
            j = coat.setdefault(g, len(coat)); rows.append(i); cols.append(j)
    ns, nc = len(surf), len(coat)
    rows = np.array(rows); cols = np.array(cols); data = np.ones(len(rows), dtype=np.int8)
    m1 = maximum_bipartite_matching(csr_matrix((data, (rows, cols)), shape=(ns, nc)), perm_type='column')
    nu1 = int((m1 >= 0).sum())
    m2 = maximum_bipartite_matching(csr_matrix((np.concatenate([data, data]), (np.concatenate([rows, rows + ns]), np.concatenate([cols, cols]))), shape=(2 * ns, nc)), perm_type='column')
    nu2 = int((m2 >= 0).sum())
    return dict(U=2 * bd - 3 * (nu1 + nu2), n2=nu2 - nu1, nu1=nu1, nu2=nu2, boundary=bd, surface=ns, coat=nc, size=len(S))

def connected(S):
    S = set(S); start = next(iter(S)); seen = {start}; stack = [start]
    while stack:
        h = stack.pop()
        for r in ROOTS:
            g = add(h, r)
            if g in S and g not in seen: seen.add(g); stack.append(g)
    return len(seen) == len(S)

if __name__ == '__main__':
    show = lambda name, S, want: print(f"{name}: cost G = {cost(S)['U'] / 2} (note: {want})")
    show("single site", {(0, 0, 0)}, 7.5)
    for n, w in ((3, 27), (4, 21), (5, 9), (6, 9), (8, 9)): show(f"O_{n}", octa(n), w)
    for k in (5, 9): show(f"tetrahedron, {k} per edge", tetra(k), 3 * k + 12)
    for v, w in (((1, 1, 0), 10), ((2, 2, 2), 12), ((1, 1, 2), 11), ((2, 2, 0), 17)): show(f"O_7 with its translate by {v}", octa(7) | octa(7, v), w)
    for k in (2, 3, 4, 5): show(f"two O_7 at offset {2*k} along an axis", octa(7) | octa(7, (2 * k, 0, 0)), '27 for offsets 4..10')
    show("two O_7 tip to tip (offset 12)", octa(7) | octa(7, (12, 0, 0)), 25.5)
    show("two O_7 at offset 2", octa(7) | octa(7, (2, 0, 0)), 21)
