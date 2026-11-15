"""Section 42 of the note: long geometric chains (lgeo.py) against U* on every connected union of two regular octahedra."""
from gmin import *
from psi import unions
from lgeo import chains
for a, b, J in ((7, 7, 2), (9, 9, 3), (5, 8, 2), (6, 9, 2)):
    rows = []
    for v, ov, S in unions(a, b):
        ch = chains(S, J); rows.append((cost(S)['U'] - 3 * len(ch), v, ov, sum(1 for x in ch if not x[4])))
    m = min(rows); nt = [r for r in rows if r[3] > 0]
    print(f"O_{a}, O_{b}, J = {J}: {len(rows)} unions; least U* - 3 L = {m[0]} at v = {m[1]} (overlap {m[2]}); unions with 3 L > U*: {sum(1 for r in rows if r[0] < 0)}; "
          f"unions with a long chain that does not start at a local top: {len(nt)}" + (f", among them least U* - 3 L = {min(nt)[0]} at v = {min(nt)[1]}" if nt else ""))
