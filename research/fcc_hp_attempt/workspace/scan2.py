"""Section 42 of the note: all unions of two regular octahedra O_a and O_b + v that are connected (overlapping or with
adjacent sites), v up to symmetry.  For each: overlap, U* = 2G, n2*, and n2* against the capacity 16 (3N/2)^(1/3) of
one octahedron of the same size.  Conjecture R (sharp form) forbids U* <= 36 for a body made of two large lumps."""
import sys
from gmin import *
a, b = int(sys.argv[1]), int(sys.argv[2]); A = octa(a); rows = []
R = a + b
for x in range(0, R + 1):
    for y in range(0, x + 1):
        for z in range(0, y + 1):
            if (x + y + z - (a - b)) % 2: continue
            B = octa(b, (x, y, z)); S = A | B
            if len(A & B) == min(len(A), len(B)): continue          # one inside the other
            if not connected(S): continue
            c = cost(S); N = len(S)
            rows.append((c['U'], len(A & B), (x, y, z), c['n2'], N, c['n2'] / (16 * (1.5 * N) ** (1 / 3))))
rows.sort()
small = min(len(A), len(B))
print(f"O_{a} and O_{b}: {len(rows)} connected unions up to symmetry")
for frac, name in ((0.0, 'no overlap (touching)'), (0.1, 'overlap at most 10% of the smaller'), (0.5, 'overlap at most 50%'), (1.0, 'any overlap')):
    sel = [r for r in rows if r[1] <= frac * small]
    if sel:
        best = sel[0]
        print(f"  {name}: {len(sel)} unions, least U* = {best[0]} at v = {best[2]} (overlap {best[1]}, n2* = {best[3]}, ratio to one-octahedron capacity {best[5]:.2f})")
print("  all unions with U* <= 36:")
for r in rows:
    if r[0] <= 36: print(f"    v = {r[2]}: U* = {r[0]}, overlap {r[1]} of {small}, n2* = {r[3]}, N = {r[4]}, ratio {r[5]:.2f}")
viol = [r for r in rows if r[0] <= 36 and r[5] > 1.0]
print(f"  unions with U* <= 36 and n2* above the capacity of one octahedron of that size: {len(viol)}; largest ratio among U* <= 36: {max(r[5] for r in rows if r[0] <= 36):.3f}")
