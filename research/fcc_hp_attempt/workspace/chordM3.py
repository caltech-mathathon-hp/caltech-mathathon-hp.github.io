"""Section 46: the count with half-open chords.  For a finite set S (chords.py; U*, p, d from gmin.cost):
    A_n = sum over chords with two open ends of (n + 1/2 - |C|)+  +  sum over chords with one open end of (n/2 + 1/4 - |C|)+,
    M'_n = (2n^2 - 3n) U* + 3n (H + H1/2 - p) - 3 A_n,      H, H1 = numbers of chords with two and with one open end.
Identity:  Lam_n = M'_n + 3 sum_OO (|C| - n - 1/2)+ + 3 sum_OB (|C| - n/2 - 1/4)+ + 3 sum_BB |C| + 3 sum_h beta(h),
beta(h) = deg - 3e + o/4 >= 0 (Lemma 63).  So Lam_n >= M'_n >= M_n.
    python3 chordM3.py island r k a b | families | unions a b | near r | islands r"""
import sys
from fractions import Fraction
from gmin import *
from chords import chords, NUS, RNU, dot
from lin import lam, minlam
Q = Fraction(1, 4)
def data3(S, c=None):
    if c is None: c = cost(S)
    ch = chords(S)
    return c, sorted(x[3] for x in ch if x[4] == 2), sorted(x[3] for x in ch if x[4] == 1), sum(x[3] for x in ch if x[4] == 0)
def M1(c, oo, ob, n):
    """M'_n"""
    U = c['U']; p = c['boundary'] - 3 * c['nu1']
    A = sum(n + 2 * Q - L for L in oo if L <= n) + sum(Fraction(n, 2) + Q - L for L in ob if L < Fraction(n, 2) + Q)
    return (2 * n * n - 3 * n) * U + 3 * n * (len(oo) + Fraction(len(ob), 2) - p) - 3 * A
def M0(c, oo, n):
    U = c['U']; p = c['boundary'] - 3 * c['nu1']
    return (2 * n * n - 3 * n) * U + 3 * n * (len(oo) - p) - 3 * sum(n + 2 * Q - L for L in oo if L <= n)
def beta_sum(S):
    tot = Fraction(0)
    for h in S:
        emp = [r for r in ROOTS if add(h, r) not in S]
        if not emp: continue
        es = set(emp); ex = [nu for nu in NUS if all(r in es for r in RNU[nu])]
        o = sum(1 for nu in ex for r in emp if dot(r, nu) == 0)
        tot += len(emp) - 3 * len(ex) + Fraction(o, 4)
    return tot
def check(S, c, oo, ob, bb, n):
    rest = 3 * sum(L - n - 2 * Q for L in oo if L > n) + 3 * sum(L - Fraction(n, 2) - Q for L in ob if L > Fraction(n, 2) + Q) + 3 * bb + 3 * beta_sum(S)
    assert lam(c, n) == M1(c, oo, ob, n) + rest, (lam(c, n), M1(c, oo, ob, n), rest)
def bad_ranges(S, verify=False):
    c, oo, ob, bb = data3(S); top = max(oo + ob) + 3
    if verify:
        for n in (3, 6, 11): check(S, c, oo, ob, bb, n)
    b0 = [n for n in range(3, top + 1) if M0(c, oo, n) < 0]; b1 = [n for n in range(3, top + 1) if M1(c, oo, ob, n) < 0]
    return c, b0, b1
def scan(name, bodies):
    cnt = 0; h0 = {}; h1 = {}; w = None
    for tag, S in bodies:
        c, b0, b1 = bad_ranges(S, cnt % 50 == 0); cnt += 1
        k0 = max(b0) if b0 else 0; k1 = max(b1) if b1 else 0; h0[k0] = h0.get(k0, 0) + 1; h1[k1] = h1.get(k1, 0) + 1
        if w is None or k1 > w[0]: w = (k1, tag, c['U'])
    print(f"{name}: {cnt} bodies; largest n with M_n < 0: {dict(sorted(h0.items()))}; largest n with M'_n < 0: {dict(sorted(h1.items()))}; worst for M': {w}", flush=True)
if __name__ == '__main__':
    mode = sys.argv[1]
    from psi import unions, boundary_moves, toggle
    if mode == 'island':
        from islands import island, supported
        r, k, a, b = map(int, sys.argv[2:6]); O = octa(r); I = island(r, k, True, (a, b)); assert supported(O, I)
        S = O | I; c, b0, b1 = bad_ranges(S, True); m, n = minlam(c)
        print(f"O_{r} with island k = {k} at {(a, b)}: N = {len(S)}, U* = {c['U']}, least Lam_n = {m} at n = {n}; M_n < 0 for n in {b0}; M'_n < 0 for n in {b1}", flush=True)
    if mode == 'families':
        named = [("single site", {(0, 0, 0)}), ("pair", {(0, 0, 0), (1, 1, 0)})] + [(f"O_{r}", octa(r)) for r in range(2, 10)] + [(f"tetra {k}", tetra(k)) for k in (4, 6, 9)]
        named += [("rod", {(i, -i, 0) for i in range(10)}), ("layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})]
        scan("named bodies", named)
    if mode == 'unions':
        a, b = int(sys.argv[2]), int(sys.argv[3]); scan(f"unions O_{a}, O_{b}+v", ((v, S) for v, ov, S in unions(a, b)))
    if mode == 'near':
        r = int(sys.argv[2]); S = octa(r)
        scan(f"bodies at one site from O_{r}", ((h, toggle(S, h)) for h in sorted(boundary_moves(S)) if not (h in S and not connected(toggle(S, h)))))
    if mode == 'islands':
        from islands import island, supported
        r = int(sys.argv[2]); O = octa(r)
        def gen():
            for up in (True, False):
                for k in range(1, r):
                    for a in range(0, r):
                        for b in range(a, r):
                            I = island(r, k, up, (a, b))
                            if supported(O, I): yield (up, k, a, b), O | I
        scan(f"islands on a face of O_{r}", gen())
