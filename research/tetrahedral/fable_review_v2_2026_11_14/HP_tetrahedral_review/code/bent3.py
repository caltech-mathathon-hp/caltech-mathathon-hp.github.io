import sys, itertools
from collections import Counter
from geom import *
from bent import foliation
m=int(sys.argv[1])
G=Geo(m); S=G.S; nb=foliation(S)
alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
E=set(v for e in alledges for v in e); X=S-E
adj={v:[w for w in nb[v] if w in X] for v in X}
legit=lambda v: bool(G.dang[v])
bad=[v for v in X if (not legit(v) and len(adj[v])<2) or len(adj[v])==0]
dv=lambda v: min(max(abs(v[i]-V[i]) for i in range(3)) for V in G.vertices)
print("m=%d bad ends %d ; by (distance to nearest vertex): %s"%(m,len(bad),dict(sorted(Counter(dv(v) for v in bad).items()))))
hard=[]
for v in bad:
    c=[w for w in nbrs(v) if w in X and w not in adj[v]]
    info=[("legit" if legit(w) else "int",len(adj[w])) for w in c]
    if not any(l=="legit" and d<=1 for l,d in info): hard.append((v,info))
print("bad ends with no free legit end next to them: %d"%len(hard))
for v,info in hard[:14]:
    V=min(G.vertices,key=lambda V:max(abs(v[i]-V[i]) for i in range(3)))
    print("  site rel. to nearest vertex %s (dist %d), own degree %d, E-neighbours %d, other neighbours %s"%(tuple(v[i]-V[i] for i in range(3)),dv(v),len(adj[v]),sum(1 for w in nbrs(v) if w in E),info))
