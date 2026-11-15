"""Section 46: blocked ends, seen from the blocking site.  For a site g with set E of empty neighbours:
tau(g) = o/2 - deg + 3 (o = open ends at g);  bl+(g) = number of pairs (nu, d), d a root with d.nu = 0, such that g + d is
occupied, g is not nu-exposed, and the neighbour g + d + r of g is empty for the r in R_nu with r.d = -1
(necessary for g + d to be nu-exposed, so bl+ bounds the number of chord ends blocked by g).
Prints, by (deg, exposures), the least value of 3 tau - (3/2) bl+ over the 4096 sets, and the sets where it is negative."""
import itertools
from gmin import ROOTS, add
from chords import NUS, RNU, dot
neg = lambda a: (-a[0], -a[1], -a[2])
tab = {}; worst = []
for mask in range(1, 1 << 12):
    emp = [ROOTS[i] for i in range(12) if mask >> i & 1]; es = set(emp)
    ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
    o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
    tau2 = o - 2 * len(emp) + 6                      # 2 tau
    bl = 0
    for nu in NUS:
        if nu in ex: continue
        for d in ROOTS:
            if dot(d, nu) != 0 or d in es: continue
            rm = [r for r in RNU[nu] if dot(r, d) == -1]
            assert len(rm) == 1
            if add(d, rm[0]) in es: bl += 1
    v = 3 * tau2 - 3 * bl                              # 2 * (3 tau - (3/2) bl)
    key = (len(emp), len(ex)); t = tab.setdefault(key, [10**9, None, 0])
    t[2] += 1
    if v < t[0]: t[0], t[1] = v, (tau2 / 2, bl)
print("(deg, e): least 3 tau - (3/2) bl+, attained with (tau, bl+), number of sets")
for key in sorted(tab): print("  ", key, tab[key][0] / 2, tab[key][1], tab[key][2])
