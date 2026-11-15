"""Section 42 of the note: bodies next to a regular octahedron.  All bodies that differ from O_n in one site, and (with
argument 2) in two sites: least U*, least Psi.  The sharp case A2 of Conjecture R asks for U* >= 19 and, to leading
order, Psi >= 1/3 for every body that is not a regular octahedron.     python3 near.py n [2]"""
import sys, itertools
from gmin import *
from psi import psi, boundary_moves, toggle, K, x3
n = int(sys.argv[1]); two = len(sys.argv) > 2
S = octa(n); mv = sorted(boundary_moves(S)); rows = []
for h in mv:
    T = toggle(S, h)
    if h in S and not connected(T): continue
    c = cost(T); rows.append((psi(T, c), c['U'], 'removed' if h in S else 'added', h))
rows.sort()
print(f"O_{n}: {len(rows)} bodies at one site from it; least U* = {min(r[1] for r in rows)}; least Psi = {rows[0][0]:+.3f} "
      f"({rows[0][2]} {rows[0][3]}, U* = {rows[0][1]}); bodies with U* <= 18: {sum(1 for r in rows if r[1] <= 18)}; with Psi < 1/3: {sum(1 for r in rows if r[0] < 1/3)}")
if two:
    best = None; cnt = 0; low = 0; umin = 99
    for h, g in itertools.combinations(mv, 2):
        T = toggle(toggle(S, h), g)
        if not connected(T): continue
        c = cost(T); p = psi(T, c); cnt += 1; umin = min(umin, c['U'])
        if p < 1/3: low += 1
        if best is None or p < best[0]: best = (p, c['U'], h, g)
    print(f"O_{n}: {cnt} connected bodies at two sites from it; least U* = {umin}; least Psi = {best[0]:+.3f} (sites {best[2]}, {best[3]}, U* = {best[1]}); with Psi < 1/3: {low}")
