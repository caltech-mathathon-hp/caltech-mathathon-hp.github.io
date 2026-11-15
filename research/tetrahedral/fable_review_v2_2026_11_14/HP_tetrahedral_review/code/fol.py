"""Common setup for the bent foliation analysis."""
import itertools
from collections import Counter, defaultdict, deque
from geom import *
def setup(m):
    G=Geo(m); S=G.S
    ys=[v[1] for v in S]; zs=[v[2] for v in S]
    cy=(min(ys)+max(ys))//2; cz=(min(zs)+max(zs))//2
    if (cy-cz)%2==0: cz+=1
    Y=lambda v: v[1]-cy; Z=lambda v: v[2]-cz
    rho=lambda v: abs(Y(v))+abs(Z(v)); alpha=lambda v: abs(Y(v))-abs(Z(v))
    nb={v:[w for w in nbrs(v) if w in S and rho(w)!=rho(v)] for v in S}      # foliation: bonds along which rho changes
    edges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    E=set(v for e in edges for v in e); X=S-E
    return G,S,E,X,nb,Y,Z,rho,alpha,edges,(cy,cz)
