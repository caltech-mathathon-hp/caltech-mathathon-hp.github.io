# Top bilayer of each face after removing the 12 edge zigzags: counts of sigma (surface sites of the face) and tau (layer below).
import sys, itertools
from collections import Counter
from geom import *
for m in (8,9,10,11,12,13):
    G=Geo(m); S=G.S
    alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    E=set(v for e in alledges for v in e)
    out=[]
    for n in G.big[:1]+G.small[:1]:
        sig_all=[v for v in G.surf if any(G.face_of[d]==n for d in G.dang[v])]
        sig=[v for v in sig_all if v not in E]
        tau=set(w for v in sig_all for w in nbrs(v) if w in S and w not in E)
        # degree of tau towards non-E sigma
        sg=set(sig); deg=Counter(sum(1 for w in nbrs(t) if w in sg) for t in tau)
        out.append("%s face: sigma %d, tau %d (tau-sigma = %d), tau by number of free sigma-neighbours %s"%("big" if n in G.big else "small",len(sig),len(tau),len(tau)-len(sig),dict(sorted(deg.items()))))
    print("m=%d: "%m+" | ".join(out))
