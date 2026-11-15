"""Diamond (tetrahedral) lattice utilities.
Sites: integer triples (x,y,z), all coords same parity, x+y+z = 0 (mod 4) [sublattice A] or 3 (mod 4) [sublattice B].
A-site neighbours: v + t_k ; B-site neighbours: v - t_k, t in T.
"""
T = [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]

def is_site(v):
    x,y,z = v
    if (x-y)%2 or (y-z)%2: return False
    return (x+y+z)%4 in (0,3)

def sub(v):
    return 'A' if sum(v)%4==0 else 'B'

def nbrs(v):
    x,y,z = v
    if (x+y+z)%4==0:
        return [(x+a,y+b,z+c) for a,b,c in T]
    else:
        return [(x-a,y-b,z-c) for a,b,c in T]

def boundary(S):
    S=set(S)
    return sum(1 for v in S for w in nbrs(v) if w not in S)

def edges(S):
    S=set(S)
    return sum(1 for v in S for w in nbrs(v) if w in S)//2
