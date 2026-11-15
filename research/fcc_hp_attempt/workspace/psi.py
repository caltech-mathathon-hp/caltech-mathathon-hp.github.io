"""Section 42 of the note: search for a body that breaks Conjecture R, in the form in which soundness uses it.

For a finite set S: U*(S) = least number of defect units (gmin.cost), X3(S) = sum over the three coordinate axes of
the Euler characteristics of the slices of S (Section 9), and

      K(S) = sqrt( (X3 + 3)^3 / (9 |S|) ),          Psi(S) = U*(S) / 3 - K(S).

K is the number of pyramids, over the six directions, that S is worth: for k_a equal pyramids along axis a,
X_a = (3 k_a^2 |S|)^(1/3) to leading order, and K is the sum of the k_a when they are equal; unequal pyramids give
less (Hoelder).  For O_n: X3 + 3 = 6n and K = 6 (1 + 1/(2 n^2))^(-1/2), so Psi is just above 0.
Conjecture R (A1 and A2) with Proposition 29 gives K <= (U - 1)/3 up to lower order terms for every body that is not
a regular octahedron, that is Psi >= 1/3.  A family with Psi < 0 that persists as the bodies grow would refute it.

  python3 psi.py scan a b            all connected unions O_a | (O_b + v): Psi, least values
  python3 psi.py search a b steps [f]   from O_a alone and from every such union whose overlap is at most the fraction f
                                     (default 1) of the smaller octahedron: descent on Psi by single sites (any site
                                     of the surface may go, any site of the coat may come), then annealing
"""
import sys, math, random
from gmin import *

def x3(S):
    tot = 0
    for ax in range(3):
        o = [i for i in range(3) if i != ax]; sl = {}
        for h in S: sl.setdefault(h[ax], set()).add((h[o[0]], h[o[1]]))
        for sq in sl.values():
            e = sum(1 for u, v in sq for d in ((1, 1), (1, -1)) if (u + d[0], v + d[1]) in sq)
            f = sum(1 for u, v in sq if (u + 1, v + 1) in sq and (u + 1, v - 1) in sq and (u + 2, v) in sq)
            tot += len(sq) - e + f
    return tot

def K(S): return math.sqrt((x3(S) + 3) ** 3 / (9 * len(S)))

def psi(S, c=None):
    if c is None: c = cost(S)
    return c['U'] / 3 - K(S)

def unions(a, b):
    A = octa(a)
    for x in range(0, a + b + 1):
        for y in range(0, x + 1):
            for z in range(0, y + 1):
                if (x + y + z - (a - b)) % 2: continue
                B = octa(b, (x, y, z)); S = A | B
                if len(A & B) == min(len(A), len(B)) or not connected(S): continue
                yield (x, y, z), len(A & B), S

def boundary_moves(S):
    out = set()
    for h in S:
        for s in ROOTS:
            g = add(h, s)
            if g not in S: out.add(g); out.add(h)
    return list(out)

def toggle(S, h):
    T = set(S); T.symmetric_difference_update({h}); return T

def descend(S, rng, cap=400):
    """first-improvement descent on Psi over single sites, in random order"""
    cur = psi(S); n = 0
    while n < cap:
        mv = boundary_moves(S); rng.shuffle(mv); done = True
        for h in mv:
            T = toggle(S, h)
            if len(T) < 2 or (h in S and not connected(T)): continue
            u = psi(T)
            if u < cur - 1e-9: S, cur, done = T, u, False; n += 1; break
        if done: break
    return S, cur

def anneal(S, steps, rng, T0=0.5):
    cur = psi(S); best = (cur, S); mv = boundary_moves(S)
    for i in range(steps):
        T = T0 * (1 - i / steps) + 0.02
        h = rng.choice(mv); S2 = toggle(S, h)
        if len(S2) < 2 or (h in S and not connected(S2)): continue
        u = psi(S2)
        if u <= cur or rng.random() < math.exp((cur - u) / T):
            S, cur = S2, u; mv = boundary_moves(S)
            if cur < best[0]: best = (cur, S)
    return best

def is_octa(S):
    for n in range(1, 40):
        if len(octa(n)) == len(S):
            c = tuple(sum(h[i] for h in S) / len(S) for i in range(3))
            if all(abs(v - round(v)) < 1e-9 for v in c): return octa(n, tuple(int(round(v)) for v in c)) == set(S)
        if len(octa(n)) > len(S): return False

def line(S):
    c = cost(S); return f"N = {len(S)}, U* = {c['U']}, X3 = {x3(S)}, K = {K(S):.3f}, Psi = {psi(S, c):+.3f}"

if __name__ == '__main__':
    mode, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    if mode == 'scan':
        for n in sorted({a, b}): print(f"O_{n}: {line(octa(n))}")
        rows = []
        for v, ov, S in unions(a, b):
            c = cost(S); rows.append((psi(S, c), c['U'], v, ov, len(S), x3(S)))
        rows.sort()
        print(f"O_{a} and O_{b}: {len(rows)} connected unions up to symmetry; least Psi {rows[0][0]:+.3f}; unions with Psi < 1/3: {sum(1 for r in rows if r[0] < 1 / 3)}; with Psi < 0: {sum(1 for r in rows if r[0] < 0)}")
        for r in rows[:8]: print(f"   v = {r[2]}: overlap {r[3]}, N = {r[4]}, U* = {r[1]}, X3 = {r[5]}, K = {r[1] / 3 - r[0]:.3f}, Psi = {r[0]:+.3f}")
        t = [r for r in rows if r[3] == 0]
        if t: print(f"   touching only: least Psi {t[0][0]:+.3f} at v = {t[0][2]} (U* = {t[0][1]}, K = {t[0][1] / 3 - t[0][0]:.3f})")
    else:
        steps = int(sys.argv[4]); rng = random.Random(5); res = []; frac = float(sys.argv[5]) if len(sys.argv) > 5 else 1.0
        small = min(len(octa(a)), len(octa(b)))
        starts = [('O_%d alone' % a, octa(a))] + [(f"v = {v}, overlap {ov}", S) for v, ov, S in unions(a, b) if ov <= frac * small]
        for name, S in starts:
            p0 = psi(S); S1, p1 = descend(S, rng)
            if steps:
                p2, S2 = anneal(S1, steps, rng); S2, p2 = descend(S2, rng)
                if p2 < p1: S1, p1 = S2, p2
            oc = is_octa(S1); res.append((p1, name, oc, S1))
            print(f"{name}: Psi at start {p0:+.3f}; after search {p1:+.3f} ({line(S1)}; added {len(S1 - S)}, removed {len(S - S1)}{'; a regular octahedron' if oc else ''})", flush=True)
        non = [r for r in res if not r[2]]
        print(f"O_{a}, O_{b}, {steps} annealing steps: {len(res)} starts; ended at a regular octahedron: {len(res) - len(non)}; "
              f"least Psi among the others: {min(r[0] for r in non):+.3f}; ends with Psi < 1/3 that are not regular octahedra: {sum(1 for r in non if r[0] < 1 / 3)}; with Psi < 0: {sum(1 for r in non if r[0] < 0)}")
        import pickle; pickle.dump([(r[0], r[1], r[2], sorted(r[3])) for r in res], open(f"out/psi_{a}_{b}_{steps}.pkl", 'wb'))
