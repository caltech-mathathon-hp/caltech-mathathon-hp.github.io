"""Extent of the vertex-zone configurations of the bulk cover: all sites of segments that have a joint within RV of a vertex,
   together with the segments they are joined to (two steps), measured by the distance to that vertex."""
import sys
from canon import *
from canon_patches import PATCH
RV=16
for m in [int(a) for a in sys.argv[1:]]:
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    msg,paths=validate(X,adj,legit); assert msg=="valid"
    fol=lambda v,w: rho(v)!=rho(w)
    segs=[]
    for p in paths:
        cur=[p[0]]
        for a,b in zip(p,p[1:]):
            if fol(a,b): cur.append(b)
            else: segs.append(cur); cur=[b]
        segs.append(cur)
    segof={v:i for i,s in enumerate(segs) for v in s}
    def joints(s): return [(v,w) for v in set((s[0],s[-1])) for w in adj[v] if not fol(v,w)]
    ext=0; n=0
    for V in G.vertices:
        dv=lambda v: max(abs(v[i]-V[i]) for i in range(3))
        zone=[i for i,s in enumerate(segs) if any(dv(v)<=RV for v,w in joints(s))]
        grow=set(zone)
        for _ in range(6):
            grow|={segof[w] for i in list(grow) for v,w in joints(segs[i])}
        n+=len(grow)
        ext=max(ext,max(dv(v) for i in grow for v in segs[i]))
    print("m=%d: vertex zones (joint within %d of a vertex, plus six further segments along the paths): %d segments, all within distance %d of their vertex"%(m,RV,n,ext))
