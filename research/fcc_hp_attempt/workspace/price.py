"""Section 42 of the note: the price of a pyramid.  Over all connected unions of two regular octahedra with K > 6.1,
the least value of (U* - 18) / (K - 6): units paid per pyramid beyond the six of one octahedron.  Conjecture R needs 3."""
from gmin import *
from psi import unions, K
for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
    rows = []
    for v, ov, S in unions(a, b):
        k = K(S); u = cost(S)['U']
        if k > 6.1: rows.append(((u - 18) / (k - 6), u, k, v, ov))
    rows.sort(); ovl = [r for r in rows if r[4] > 0]
    print(f"O_{a}, O_{b}: {len(rows)} unions with K > 6.1; least price {rows[0][0]:.2f} at v = {rows[0][3]} (overlap {rows[0][4]}, U* = {rows[0][1]}, K = {rows[0][2]:.2f}); "
          f"least price among overlapping unions {ovl[0][0]:.2f} at v = {ovl[0][3]} (overlap {ovl[0][4]}, U* = {ovl[0][1]}, K = {ovl[0][2]:.2f})")
