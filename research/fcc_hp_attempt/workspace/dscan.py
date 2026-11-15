"""Section 45: the discriminant D = 32 U* d - 27 (n2* + U*)^2 (lin.py) on the unions of two octahedra and the bodies at one site from O_r."""
from gmin import *
from lin import disc, parts
from psi import unions, boundary_moves, toggle
low = None; cnt = 0; neg = 0
def take(tag, S):
    global low, cnt, neg
    c = cost(S); D = disc(c); cnt += 1; neg += D < 0
    if D > 0 and (low is None or D < low[0]): low = (D, tag, parts(c)[1])
for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
    for v, ov, S in unions(a, b): take((a, b, v), S)
for r in (5, 6, 7, 8):
    S = octa(r)
    for h in sorted(boundary_moves(S)):
        T = toggle(S, h)
        if h in S and not connected(T): continue
        take((r, h), T)
print(f"{cnt} bodies; with D < 0: {neg}; least D = {low[0]} ({low[1]}, U* = {low[2]})")
