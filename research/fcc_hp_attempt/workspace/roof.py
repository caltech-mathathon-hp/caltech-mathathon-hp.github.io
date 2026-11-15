"""Section 42 of the note: bodies with a roof.  O_N at the origin and two legs O_n + (a, b, -c), O_n + (-a, -b, -c) below it.
Seen from above, the slices of the roof shrink and those of the legs grow: where the legs come apart below the roof,
two growing sequences start that do not start at a local top.  This is the case of Conjecture R without an argument.
For every connected body of the family: U*, K and Psi (psi.py), and L = number of long geometric chains (lgeo.py).
Alarm: Psi < 0, or 3 L > U*.        python3 roof.py N n J"""
import sys
from gmin import *
from psi import x3, K, psi
from lgeo import chains

N, n, J = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
A = octa(N); rows = []
for a in range(0, N + n + 1):
    for b in range(0, 3):
        for c in range(0, N + n + 1):
            if (a + b + c - (N - n)) % 2: continue
            B1 = octa(n, (a, b, -c)); B2 = octa(n, (-a, -b, -c)); S = A | B1 | B2
            if not connected(S): continue
            if len(B1 - A) < len(B1) // 3 or len(B1 - B2) < len(B1) // 3: continue      # a leg mostly swallowed
            co = cost(S); ch = chains(S, J)
            below = [x for x in ch if x[0] == 2 and x[1] == 1]                          # chains seen from above
            rows.append((psi(S, co), co['U'], len(ch), len(below), (a, b, c), len(S), K(S), sum(1 for x in ch if not x[4]), sum(1 for x in below if not x[4])))
rows.sort()
print(f"roof O_{N}, legs O_{n}, J = {J}: {len(rows)} connected bodies")
print(f"   least Psi: {rows[0][0]:+.3f} at (a, b, c) = {rows[0][4]} (U* = {rows[0][1]}, K = {rows[0][6]:.2f}, long chains {rows[0][2]})")
m = max(rows, key=lambda r: 3 * r[2] - r[1])
print(f"   largest 3 L - U*: {3 * m[2] - m[1]} at (a, b, c) = {m[4]} (U* = {m[1]}, long chains {m[2]}, of which seen from above {m[3]}, Psi = {m[0]:+.3f})")
sp = [r for r in rows if r[3] >= 3]
print(f"   bodies with three long chains seen from above (roof and both legs): {len(sp)}" + (f"; among them least U* = {min(r[1] for r in sp)}, least U* - 3 L = {min(r[1] - 3 * r[2] for r in sp)}, least Psi = {min(r[0] for r in sp):+.3f}" if sp else ""))
nt = [r for r in rows if r[7] > 0]
print(f"   bodies with a long chain that does not start at a local top: {len(nt)}" + (f"; among them least U* - 3 L = {min(r[1] - 3 * r[2] for r in nt)}, largest number of such chains {max(r[7] for r in nt)}" if nt else ""))
u2 = [r for r in rows if r[8] >= 2]
print(f"   bodies with two long chains seen from above that do not start at a local top (both legs start under the roof): {len(u2)}" + (f"; among them least U* = {min(r[1] for r in u2)}, least U* - 3 L = {min(r[1] - 3 * r[2] for r in u2)}" if u2 else ""))
for r in sorted(u2, key=lambda r: r[1] - 3 * r[2])[:3]:
    print(f"      under the roof: (a, b, c) = {r[4]}: N = {r[5]}, U* = {r[1]}, long chains {r[2]} ({r[7]} not from a top), U* - 3 L = {r[1] - 3 * r[2]}, Psi = {r[0]:+.3f}")
print(f"   alarms (Psi < 0 or 3 L > U*): {sum(1 for r in rows if r[0] < 0 or 3 * r[2] > r[1])}")
for r in sorted(rows, key=lambda r: r[1] - 3 * r[2])[:5]:
    print(f"      (a, b, c) = {r[4]}: N = {r[5]}, U* = {r[1]}, long chains {r[2]} ({r[3]} from above), U* - 3 L = {r[1] - 3 * r[2]}, K = {r[6]:.2f}, Psi = {r[0]:+.3f}")
