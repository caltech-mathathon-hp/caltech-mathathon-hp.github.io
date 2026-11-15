"""Cover of section 8.3 near the edges: periodicity along every edge (confirmation of Lemma K + Lemma E).
   For each of the 12 edge zigzags e[0..L] and each index i: signature(i) = the cover inside the box of max-norm RB around
   e[i]: all cover bonds, all path ends, relative to e[i].  Reports the smallest I such that signature(i) = signature(i+2)
   for all I <= i <= L-I-2, for several m; and that the signatures in the periodic range are the same for all m."""
import sys
from canon import *
from canon_patches import PATCH
RB=6
def run(m):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    ends=set(v for v in X if len(adj[v])==1)
    out={}
    V=G.vertices
    for a in range(6):
        for b in range(a+1,6):
            e=G.edge(V[a],V[b])
            if not e: continue
            Lg=len(e)-1; sig=[]
            for i in range(Lg+1):
                o=e[i]; s=set()
                for dx in range(-RB,RB+1):
                    for dy in range(-RB,RB+1):
                        for dz in range(-RB,RB+1):
                            v=(o[0]+dx,o[1]+dy,o[2]+dz)
                            if v in X:
                                s.add(((dx,dy,dz),v in ends,tuple(sorted(tuple(w[t]-o[t] for t in range(3)) for w in adj[v]))))
                            elif v in S: s.add(((dx,dy,dz),'edge'))
                sig.append(frozenset(s))
            I=next(I for I in range(1,Lg//2) if all(sig[i]==sig[i+2] for i in range(I,Lg-I-1)))
            out[(a,b)]=(I,sig[Lg//2],sig[Lg//2+1])
    return out
ref=None
for m in map(int,sys.argv[1:]):
    o=run(m)
    if ref is None: ref=o
    print("m=%d: 12 edges ; cover within max-norm %d of e[i] is 2-periodic for I <= i <= 2m-2-I with I = %d (max over edges) ; periodic pattern same as m=%s: %s"%(m,RB,max(v[0] for v in o.values()),sys.argv[1],all(o[k][1:]==ref[k][1:] or o[k][1:]==ref[k][1:][::-1] for k in o)),flush=True)
