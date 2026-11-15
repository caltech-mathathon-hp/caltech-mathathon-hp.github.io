"""Section 46: one-layer triangular islands and pits on the face x + y + z = r - 1 of O_r.
For each island the least Lam_n (lin.py), the n at which M_n < 0 (chordM.py), U* and the slack of (K).
    python3 islands.py r"""
import sys
from gmin import *
from lin import minlam, lam
from chordM import data, M
def island(r, k, up, shift=(0, 0)):
    """sites of the layer x + y + z = r + 1 over the face, a triangle with k sites per side; up: orientation"""
    out = set()
    a0, b0 = shift
    for i in range(k):
        for j in range(k - i):
            if up: x, y = 1 + a0 + i, 1 + b0 + j
            else: x, y = 1 + a0 + k - 1 - i, 1 + b0 + k - 1 - j
            z = r + 1 - x - y
            out.add((x, y, z))
    return out
def supported(S, I):
    low = [(-1, -1, 0), (-1, 0, -1), (0, -1, -1)]
    return all(all(add(h, d) in S for d in low) for h in I)
def row(name, S):
    c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(3, top + 1) if M(c, oo, n) < 0]
    m, n = minlam(c); U = c['U']; H = len(oo)
    ks = min((4 * U * L - 3 * sum(1 for x in oo if x <= L)) / 3 for L in set(oo))
    print(f"{name}: N = {len(S)}, U* = {U}, n2* = {c['n2']}, least Lam_n = {m} at n = {n}; M_n < 0 for n in {bad}; least slack of (K) = {ks:.2f}", flush=True)
if __name__ == '__main__':
  r = int(sys.argv[1]); O = octa(r)
  for up in (True, False):
      for k in range(1, r):
          for shift in ((0, 0), (1, 1), (2, 1)):
              I = island(r, k, up, shift)
              if not supported(O, I): continue
              row(f"island k = {k}, {'same' if up else 'reversed'} orientation, shift {shift}", O | I)
