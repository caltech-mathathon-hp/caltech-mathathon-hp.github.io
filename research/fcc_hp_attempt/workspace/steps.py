"""Section 45: (M_n) for O_r with small translates.  Does the range of n in which M_n < 0 grow with the height of the step?
    python3 steps.py r"""
import sys
from gmin import *
from chordM import data, M
from lin import lam, minlam
def row(name, S):
    c, oo = data(S); top = max(oo) + 3; bad = [n for n in range(2, top + 1) if M(c, oo, n) < 0]
    m, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {c['U']}, H = {len(oo)}, (M_n) fails for n in {bad}; least Lam_n = {m} at n = {n}", flush=True)
r = int(sys.argv[1])
for t in (2, 4, 6):
    row(f"O_{r} u O_{r}+({t},{t},{t})", octa(r) | octa(r, (t, t, t)))
for v in ((2, 2, 0), (4, 4, 0), (3, 3, 0), (1, 1, 2), (2, 2, 4), (3, 1, 0), (4, 2, 0), (6, 2, 0)):
    row(f"O_{r} u O_{r}+{v}", octa(r) | octa(r, v))
