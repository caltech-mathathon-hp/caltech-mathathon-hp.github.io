"""Transfer principle, checked by computer: the final bonds at a site are a function of its local 'signature'
   (which sites of the 7x7x7 box around it lie in X_m, on an edge, or outside; the signs of Y and Z there; and, within
   Chebyshev distance 12 of a vertex, the position relative to that vertex), and no new signature appears as m grows."""
import sys, itertools, time
from canon import *
from canon_patches import PATCH
OFF=[(a,b,c) for a in range(-3,4) for b in range(-3,4) for c in range(-3,4)]
seen={}; table={}
for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
    t0=time.time()
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    cy=next(iter(S))[1]-Y(next(iter(S))); cz=next(iter(S))[2]-Z(next(iter(S)))
    new=0; clash=0
    for v in X:
        par=(v[0]%2, sum(v)%4)
        lab=[]
        for o in OFF:
            w=(v[0]+o[0],v[1]+o[1],v[2]+o[2])
            if (w[0]-w[1])%2 or (w[1]-w[2])%2 or (sum(w)%4 not in (0,3)): continue
            st=2 if w in X else (1 if w in E else 0)
            lab.append((st,sg(w[1]-cy),sg(w[2]-cz)))
        V=nearest_vertex(G,v); d=max(abs(v[i]-V[i]) for i in range(3))
        tag=(G.vertices.index(V),tuple(v[i]-V[i] for i in range(3))) if d<=12 else None
        sig=hash((par,tuple(lab),tag))
        out=frozenset(tuple(w[i]-v[i] for i in range(3)) for w in adj[v])
        if sig not in table: table[sig]=out
        elif table[sig]!=out: clash+=1
        if sig not in seen: seen[sig]=m; new+=1
    print("m=%2d: %6d sites ; signatures seen so far %5d ; new at this m: %4d ; same signature but different bonds: %d ; %.0fs"%(m,len(X),len(seen),new,clash,time.time()-t0),flush=True)
