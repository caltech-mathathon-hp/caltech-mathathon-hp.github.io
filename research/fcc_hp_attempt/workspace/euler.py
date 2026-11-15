"""Section 44 of the note: Euler characteristic of the boundary of the union of the Voronoi cells of S: chi = (mixed tetrahedra) + (mixed octahedra) - (boundary edges).
Tetrahedra: the four lattice points around a cube centre in (Z + 1/2)^3.  Octahedra: c +- e_i around an integer point c of odd coordinate sum.
With resolved=True the surface is made a manifold first: at the centre of an octahedron where it pinches (the cells of S around the centre and
the empty cells around it form k + 1 > 2 groups), the centre is counted k times.  This is the Euler characteristic of the normalised surface."""
from gmin import *
import itertools
SG = list(itertools.product((0, 1), repeat=3))
def chi_v(S, resolved=False):
    S = set(S); par = sum(next(iter(S))) % 2
    tets = set(); octs = set(); bd = 0
    for h in S:
        for r in ROOTS:
            if add(h, r) not in S: bd += 1
        # cube cells containing h: lower corner k with h in k + {0,1}^3
        for d in SG:
            k = (h[0] - d[0], h[1] - d[1], h[2] - d[2]); tets.add(k)
        for i in range(3):
            for s in (1, -1):
                c = list(h); c[i] += s; octs.add(tuple(c))
    mt = 0
    for k in tets:
        v = [(k[0] + d[0], k[1] + d[1], k[2] + d[2]) for d in SG if (k[0] + d[0] + k[1] + d[1] + k[2] + d[2]) % 2 == par]
        n = sum(1 for x in v if x in S)
        if 0 < n < 4: mt += 1
    mo = 0; pinch = 0
    for c in octs:
        occ = []
        for i in range(3):
            for s in (1, -1):
                x = list(c); x[i] += s
                occ.append(tuple(x) in S)
        n = sum(occ)
        if 0 < n < 6:
            mo += 1
            # faces of the cube around c: index 2i (+e_i), 2i+1 (-e_i); two faces are adjacent unless opposite
            def comps(val):
                idx = [j for j in range(6) if occ[j] == val]; seen = set(); k = 0
                for j in idx:
                    if j in seen: continue
                    k += 1; st = [j]; seen.add(j)
                    while st:
                        a_ = st.pop()
                        for b_ in idx:
                            if b_ not in seen and b_ // 2 != a_ // 2: seen.add(b_); st.append(b_)
                return k
            pinch += comps(True) + comps(False) - 2
    return (mt + mo - bd + pinch) if resolved else (mt + mo - bd)
if __name__ == '__main__':
    from tops import tops
    from morse import morse
    def show(name, S):
        u = cost(S)['U']; T, sig, b1 = morse(S); x = chi_v(S)
        print(f"{name}: N={len(S)} U*={u} T={T} b1={b1} chi={x}  U*-6T+18={u-6*T+18}  U*-6T+9chi={u-6*T+9*x}")
    show('site', {(0,0,0)}); show('pair', {(0,0,0),(1,1,0)})
    for n in (2, 3, 5, 6): show(f'O_{n}', octa(n))
    n = 6
    show('tip next to tip', octa(n) | octa(n, (2*n-1, 1, 0))); show('tips coincide', octa(n) | octa(n, (2*n-2, 0, 0)))
    show('one-site bridge', octa(n) | {(n,1,0)} | octa(n, (2*n, 2, 0))); show('zig bridge', octa(n) | {(n,1,0),(n+1,0,0)} | octa(n, (2*n+1, 1, 0)))
    show('ring of four', octa(n) | octa(n, (2*n-1, 1, 0)) | octa(n, (2*n-2, 2*n, 0)) | octa(n, (-1, 2*n-1, 0)))
    S = octa(9); show('O_9 with a tunnel along z', {h for h in S if not (abs(h[0]) + abs(h[1]) <= 2)})
    show('O_9 with cavity O_3', octa(9) - octa(3)); show('rod 10', {(i,i,0) for i in range(10)}); show('tetra 6', tetra(6))
    show('twin tops', octa(7) | octa(7, (2, 0, 0)))
