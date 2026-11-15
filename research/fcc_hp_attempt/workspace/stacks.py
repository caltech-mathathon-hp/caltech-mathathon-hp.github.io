"""Section 46: octahedra with islands on all eight faces, and with islands stacked on one face.
For each: U*, least Lam_n, least increment of M'_n (n >= 3), least M'_n (n >= 4).     python3 stacks.py r"""
import sys, itertools
from gmin import *
from lin import minlam
from ends import tests
from islands import island
def all_faces(r, k, a, b):
    I = island(r, k, True, (a, b)); out = set()
    for s in itertools.product((1, -1), repeat=3):
        out |= {(s[0] * x, s[1] * y, s[2] * z) for x, y, z in I}
    return out
def stacked(r, ks, a, b):
    """islands with ks[0], ks[1], ... sites per side, each one layer above the one before, each shifted by (1, 1)"""
    out = set()
    for j, k in enumerate(ks):
        for i in range(k):
            for l in range(k - i):
                x, y = 1 + a + j + i, 1 + b + j + l; z = r + 1 + 2 * j - x - y
                out.add((x, y, z))
    return out
def row(name, S):
    k, i, m, c, m4 = tests(S); mm, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, least Lam_n = {mm} at n = {n}; least increment {float(i[0]):.1f} at n = {i[1]}; M'_3 = {float(m):.1f}; least M'_n, n >= 4: {float(m4):.1f}", flush=True)
r = int(sys.argv[1]); O = octa(r)
for k, a, b in ((3, 1, 1), (3, 0, 0), (4, 1, 1), (r - 3, 0, 0), (r - 4, 1, 1), (2, 1, 1), (1, 1, 1)):
    row(f"O_{r} with islands k = {k} at ({a},{b}) on all eight faces", O | all_faces(r, k, a, b))
for ks, a, b in (((5, 2), 0, 0), ((6, 3), 0, 0), ((6, 3), 1, 0), ((4, 1), 1, 1), ((7, 4, 1), 0, 0)):
    St = stacked(r, ks, a, b)
    if any(sum(abs(t) for t in h) > r + 1 + 2 * len(ks) for h in St): continue
    row(f"O_{r} with stacked islands {ks} at ({a},{b})", O | St)
