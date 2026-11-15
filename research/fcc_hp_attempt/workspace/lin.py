"""Section 45 of the note: the linear inequality (L_n).
For a finite set S with boundary d, matching numbers nu1, nu2 (gmin.cost) put
    U* = 2d - 3(nu1 + nu2),   Y = 2(d - 2 nu1 - nu2)  (= n2* + U*),
    Lam_n(S) = (4n^2 - 9n + 3) d - 3n((2n - 6) nu1 + (2n - 3) nu2) = 2 U* n^2 - (9/2) Y n + 3 d.
Lam_n is the least value, over the decorations of S, of ((4n^2 - 9n + 3) U + 18 n1 - 9 (n - 3) n2) / 2.
(L_n): Lam_n(S) >= 0 for every finite S.  For O_r it is 36 (n - r)^2.
D(S) = 32 U* d - 27 Y^2 >= 0 is the same for all real n at once.
    python3 lin.py families          octahedra, tetrahedra, the unions of two octahedra of Section 42
    python3 lin.py near n            bodies at one site from O_n
    python3 lin.py bridge n          two copies of O_n joined by one site
"""
import sys, math
from gmin import *

def parts(c):
    d, a, b = c['boundary'], c['nu1'], c['nu2']
    return d, 2 * d - 3 * (a + b), 2 * (d - 2 * a - b)

def lam(c, n):
    d, a, b = c['boundary'], c['nu1'], c['nu2']
    return (4 * n * n - 9 * n + 3) * d - 3 * n * ((2 * n - 6) * a + (2 * n - 3) * b)

def disc(c):
    d, U, Y = parts(c); return 32 * U * d - 27 * Y * Y

def minlam(c, nmin=3):
    """least Lam_n over integers n >= nmin, and the n"""
    d, U, Y = parts(c)
    v = 9 * Y / (8 * U) if U > 0 else nmin
    cand = {nmin, max(nmin, math.floor(v)), max(nmin, math.ceil(v))}
    return min((lam(c, n), n) for n in cand)

def report(name, S):
    c = cost(S); d, U, Y = parts(c); m, n = minlam(c)
    print(f"{name}: N = {len(S)}, U* = {U}, n2* = {c['n2']}, boundary = {d}, D = {disc(c)}, least Lam_n = {m} at n = {n}")
    return m

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'families':
        for r in range(5, 11):
            c = cost(octa(r)); assert all(lam(c, n) == 36 * (n - r) ** 2 for n in range(3, 40)), r
        print("O_r, r = 5..10: Lam_n = 36 (n - r)^2 for n = 3..39")
        for r in (2, 3, 4): report(f"O_{r}", octa(r))
        report("single site", {(0, 0, 0)}); report("two adjacent sites", {(0, 0, 0), (1, 1, 0)})
        for k in (4, 6, 9, 12): report(f"tetrahedron {k}", tetra(k))
        from psi import unions
        for a, b in ((7, 7), (9, 9), (5, 8), (6, 9)):
            worst = None; cnt = 0; neg = 0
            for v, ov, S in unions(a, b):
                c = cost(S); m, n = minlam(c); cnt += 1; neg += m < 0
                if worst is None or m < worst[0]: worst = (m, n, v, parts(c)[1], disc(c))
            print(f"unions O_{a}, O_{b}+v: {cnt} bodies, with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (v = {worst[2]}, U* = {worst[3]}, D = {worst[4]})")
    if mode == 'near':
        from psi import boundary_moves, toggle
        r = int(sys.argv[2]); S = octa(r); worst = None; cnt = 0; neg = 0
        for h in sorted(boundary_moves(S)):
            T = toggle(S, h)
            if h in S and not connected(T): continue
            c = cost(T); m, n = minlam(c); cnt += 1; neg += m < 0
            if worst is None or m < worst[0]: worst = (m, n, h, parts(c)[1], c['n2'], disc(c))
        print(f"O_{r}: {cnt} bodies at one site; with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (site {worst[2]}, U* = {worst[3]}, n2* = {worst[4]}, D = {worst[5]})")
    if mode == 'bridge':
        r = int(sys.argv[2]); A = octa(r); coatA = {add(h, s) for h in A for s in ROOTS} - A; worst = None; cnt = 0; neg = 0
        for x in range(0, 2 * r + 5):
            for y in range(0, x + 1):
                for z in range(0, y + 1):
                    if (x + y + z) % 2: continue
                    B = octa(r, (x, y, z))
                    if A & B or coatA & B: continue
                    coatB = {add(h, s) for h in B for s in ROOTS} - B
                    for g in coatA & coatB:
                        S = A | B | {g}; c = cost(S); m, n = minlam(c); cnt += 1; neg += m < 0
                        if worst is None or m < worst[0]: worst = (m, n, (x, y, z), g, parts(c)[1], c['n2'], disc(c))
        print(f"two O_{r} joined by one site: {cnt} bodies; with Lam_n < 0: {neg}; least Lam_n = {worst[0]} at n = {worst[1]} (v = {worst[2]}, site {worst[3]}, U* = {worst[4]}, n2* = {worst[5]}, D = {worst[6]})")
