"""Section 45 of the note: chords of faces.
For nu in {+1,-1}^3 let R_nu be the three roots r with r.nu = 2.  A site h of S is nu-exposed if h + r is empty for the
three r in R_nu.  A chord is a maximal run of nu-exposed sites on a lattice line with direction d, d.nu = 0 (three
directions for each nu).  An end of a chord is open if the next site of the line is empty, and blocked if it is in S.
H = number of chords with two open ends, H_j = number of those with at most j sites, kappa = max_j H_j / j,
Len = their total number of sites.  Statements tested (U*, nu1, nu2, boundary d from gmin.cost):
    (A)  d - 3 nu2 + H >= (3/2) kappa        (K)  U* >= (3/4) kappa        (B)  Len - H/2 <= d
(A) and (K) together would give Lam_n >= 0 for n >= 3, but (A) is false (Section 45.6).  (B) is Lemma 63 (chordB.py).
(K) is open.     python3 chords.py"""
import sys, itertools
from fractions import Fraction
from gmin import *
NUS = list(itertools.product((1, -1), repeat=3))
dot = lambda a, b: a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
RNU = {nu: [r for r in ROOTS if dot(r, nu) == 2] for nu in NUS}
DNU = {nu: [r for r in ROOTS if dot(r, nu) == 0 and r > (0, 0, 0)] for nu in NUS}
sub = lambda a, b: (a[0] - b[0], a[1] - b[1], a[2] - b[2])

def chords(S):
    """list of (nu, d, first site, length, open ends)"""
    out = []
    for nu in NUS:
        F = {h for h in S if all(add(h, r) not in S for r in RNU[nu])}
        for d in DNU[nu]:
            for h in F:
                if sub(h, d) in F: continue
                L = 1; g = add(h, d)
                while g in F: L += 1; g = add(g, d)
                out.append((nu, d, h, L, (sub(h, d) not in S) + (g not in S)))
    return out

def stats(S, c=None):
    if c is None: c = cost(S)
    ch = chords(S); oo = sorted(x[3] for x in ch if x[4] == 2)
    H = len(oo); Len = sum(oo)
    kappa = max((Fraction(i + 1, L) for i, L in enumerate(oo) if i + 1 == H or oo[i + 1] > L), default=Fraction(0))
    d = c['boundary']
    return dict(H=H, Len=Len, kappa=kappa, A=d - 3 * c['nu2'] + H - Fraction(3, 2) * kappa, K=c['U'] - Fraction(3, 4) * kappa, B=d - Len + Fraction(H, 2),
                bb=sum(1 for x in ch if x[4] == 0), ob=sum(1 for x in ch if x[4] == 1), U=c['U'], d=d)

def show(name, S):
    t = stats(S); print(f"{name}: N = {len(S)}, U* = {t['U']}, chords oo/ob/bb = {t['H']}/{t['ob']}/{t['bb']}, kappa = {float(t['kappa']):.2f}, "
                        f"slack of (A) = {float(t['A']):.2f}, of (K) = {float(t['K']):.2f}, of (B) = {float(t['B']):.1f}")
    return t

if __name__ == '__main__':
    show("single site", {(0, 0, 0)}); show("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
    for r in range(2, 10): show(f"O_{r}", octa(r))
    for k in (4, 6, 9): show(f"tetrahedron {k}", tetra(k))
    show("O_7 u O_7+(2,0,0)", octa(7) | octa(7, (2, 0, 0))); show("O_7 u O_7+(4,0,0)", octa(7) | octa(7, (4, 0, 0)))
    show("O_7 u O_7+(1,1,0)", octa(7) | octa(7, (1, 1, 0))); show("O_7 u O_7+(2,2,2)", octa(7) | octa(7, (2, 2, 2)))
    show("O_6 u O_6+(11,1,0)", octa(6) | octa(6, (11, 1, 0))); show("two O_6 and a site", octa(6) | octa(6, (12, 1, 1)) | {(6, 0, 1)})
    show("O_6 without a vertex", octa(6) - {(5, 0, 0)}); show("O_6 with a site on a face", octa(6) | {(2, 2, 3)})
    show("rod of 10", {(i, -i, 0) for i in range(10)}); show("(111) layer", {(a - b, b - c, c - a) for a in range(4) for b in range(4) for c in range(4)})
