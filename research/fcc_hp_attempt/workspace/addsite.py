"""Section 44 of the note: adding one site g to a set S'.  With a = number of neighbours of g in S', c = number of empty neighbours of g that are
adjacent to S', and i = number of neighbours of g that become interior:  W(S' + g) - W(S') = -12 - a + 3c + 3i.  Checked on random cases."""
import random
from gmin import *
from wdef import parts
from psi import boundary_moves
rng = random.Random(3); bad = 0; n = 0
for trial in range(400):
    S = {(0, 0, 0)}
    for _ in range(rng.randint(2, 60)):
        h = rng.choice(sorted(S)); S.add(add(h, rng.choice(ROOTS)))
    if trial % 4 == 0: S |= octa(4)
    cand = [g for g in boundary_moves(S) if g not in S]
    for g in rng.sample(cand, min(5, len(cand))):
        a = sum(1 for r in ROOTS if add(g, r) in S)
        c = sum(1 for r in ROOTS if add(g, r) not in S and any(add(add(g, r), q) in S for q in ROOTS))
        T = S | {g}
        i = sum(1 for r in ROOTS if add(g, r) in S and all(add(add(g, r), q) in T for q in ROOTS))
        i += 1 if a == 12 else 0
        dW = parts(T)['W'] - parts(S)['W']; n += 1
        if dW != -12 - a + 3 * c + 3 * i: bad += 1
print(f"{n} additions of one site: the formula for the change of W fails in {bad}")
