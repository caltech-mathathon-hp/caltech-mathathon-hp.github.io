"""Section 45: the pointwise inequality behind (B).  For a site h with a given set of empty neighbours let
deg = their number, e = number of nu with the three roots of R_nu empty (exposures), o = number of pairs (nu, r) with
nu an exposure and r an empty root with r.nu = 0 (open ends at h).  Claim: 12 e - 4 deg <= o for all 4096 sets."""
import itertools
from gmin import ROOTS
from chords import NUS, RNU, dot
worst = None; bad = 0; table = {}
for mask in range(1 << 12):
    emp = [ROOTS[i] for i in range(12) if mask >> i & 1]; es = set(emp)
    ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
    o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
    v = o - 12 * len(ex) + 4 * len(emp)
    if v < 0: bad += 1
    key = (len(emp), len(ex)); table[key] = min(table.get(key, 99), v)
print("sets with 12 e - 4 deg > o:", bad)
print("least o - 12 e + 4 deg by (deg, e):", dict(sorted(table.items())))
