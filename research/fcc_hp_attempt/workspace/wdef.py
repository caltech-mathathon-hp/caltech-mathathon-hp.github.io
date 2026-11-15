"""Section 43 of the note: U* = W + 3 def1 + 3 def2 with W = 2 bd - 3 s - 3 c (a sum over the boundary graph of degree - 3),
def1 = s - nu1 and def2 = c - nu2 (the shortfalls of the two matchings)."""
from gmin import *
def parts(S):
    c = cost(S); W = 2 * c['boundary'] - 3 * c['surface'] - 3 * c['coat']
    return dict(U=c['U'], W=W, d1=c['surface'] - c['nu1'], d2=c['coat'] - c['nu2'], s=c['surface'], c=c['coat'], n2=c['n2'], N=c['size'])
def show(name, S):
    p = parts(S); assert p['U'] == p['W'] + 3 * p['d1'] + 3 * p['d2']
    print(f"{name}: N={p['N']} U*={p['U']} W={p['W']} def1={p['d1']} def2={p['d2']} kappa={p['c']-p['s']} n2*={p['n2']}")
if __name__ == '__main__':
    show('site', {(0,0,0)}); show('pair', {(0,0,0),(1,1,0)})
    for n in (2,3,4,5,6,8): show(f'O_{n}', octa(n))
    for k in (4,6,9): show(f'tetra {k}', tetra(k))
    for v in ((1,1,0),(2,2,0),(3,3,0),(2,2,2),(2,1,1),(4,0,0),(6,0,0),(12,0,0),(13,1,0),(12,1,1),(12,2,0),(8,3,3),(4,4,4),(5,4,3)):
        show(f'O_7+{v}', octa(7) | octa(7, v))
    S = octa(7); S.discard((6,0,0)); show('O_7 minus a vertex', S)
    S = octa(7); S.add((7,1,0)); show('O_7 plus a cell', S)
    # plate, rod, cube-ish block
    show('plate 6x6 (z=0)', {(x,y,0) for x in range(-6,7) for y in range(-6,7) if (x+y)%2==0 and abs(x)+abs(y)<=6})
    show('rod 10', {(i,i,0) for i in range(10)})
    show('block', {(x,y,z) for x in range(6) for y in range(6) for z in range(6) if (x+y+z)%2==0})
    # torus-like: O_9 with an axial tunnel
    S = octa(9); T = {h for h in S if not (abs(h[0])+abs(h[1])<=2)}; show('O_9 with tunnel along z', T) if connected(T) else None
    S = octa(9); T = S - octa(3); show('O_9 with cavity O_3', T)
