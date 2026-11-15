"""Section 43 of the note: local tops in the six directions (pieces of slices with no occupied upper neighbour), against U*."""
from gmin import *
from wdef import parts
def slices(S, ax, sg):
    o = [i for i in range(3) if i != ax]; sl = {}
    for h in S: sl.setdefault(sg * h[ax], set()).add((h[o[0]], h[o[1]]))
    return sl
def pieces(sq):
    seen = set(); ps = []
    for s in sq:
        if s in seen: continue
        c = {s}; st = [s]; seen.add(s)
        while st:
            u, v = st.pop()
            for du, dv in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                t = (u + du, v + dv)
                if t in sq and t not in seen: seen.add(t); c.add(t); st.append(t)
        ps.append(frozenset(c))
    return ps
UP = ((1, 0), (-1, 0), (0, 1), (0, -1))
def tops(S):
    """returns (number of local tops over six directions, number of them that are single sites, number of distinct sites that are one-site tops)"""
    T = 0; one = 0; sites = set()
    for ax in range(3):
        o = [i for i in range(3) if i != ax]
        for sg in (1, -1):
            sl = slices(S, ax, sg)
            for l, sq in sl.items():
                up = sl.get(l + 1, ())
                for p in pieces(sq):
                    if not any((u + a, v + b) in up for u, v in p for a, b in UP):
                        T += 1
                        if len(p) == 1:
                            one += 1; u, v = next(iter(p)); h = [0, 0, 0]; h[ax] = sg * l; h[o[0]] = u; h[o[1]] = v; sites.add(tuple(h))
    return T, one, len(sites)
def show(name, S):
    p = parts(S); T, one, ns = tops(S)
    print(f"{name}: N={p['N']} U*={p['U']} W={p['W']} def2={p['d2']} def1={p['d1']}  tops T={T} (one-site {one}, at {ns} sites)  U*-3T={p['U']-3*T}  U*-(4T-6)={p['U']-4*T+6}  U*-(6T-18)={p['U']-6*T+18}")
if __name__ == '__main__':
    show('O_7', octa(7))
    S = octa(7); S.add((7, 1, 0)); show('O_7 + cell of a vertex', S)
    S = octa(7); S.add((3, 3, 2)); show('O_7 + site on a face', S)      # norm 8 = n+1, face coat site
    S = octa(7); S.add((4, 4, 0)); show('O_7 + site over an edge', S)
    S = octa(7) | octa(2, (8, 0, 0)) if False else octa(7) | {(7,1,0),(7,-1,0),(7,0,1),(7,0,-1),(8,0,0)}; show('O_7 + 5 sites on a vertex', S)
    for v in ((13,1,0),(12,0,0),(4,0,0),(2,2,2),(1,1,0),(4,4,4),(8,3,3),(3,3,0),(5,4,3),(12,2,0)): show(f'O_7+{v}', octa(7) | octa(7, v))
    show('three in a row', octa(6) | octa(6,(11,1,0)) | octa(6,(-11,-1,0)))
    for b, v in ((3,(4,3,3)),(4,(4,4,3)),(3,(8,0,0)),(3,(9,1,0)),(4,(10,1,0)),(5,(11,1,0))): show(f'O_7 + O_{b}+{v}', octa(7) | octa(b, v))
