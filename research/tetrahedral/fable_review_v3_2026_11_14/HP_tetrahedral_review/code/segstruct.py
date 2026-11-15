"""Structure of the segments used in part (a) of Claim 2 (sanity check of the geometric statements G1-G4 of the proof).
   For every segment with two joints, both farther than 12 (max-norm) from all vertices:
     each joint site lies within max-norm 2 of a zigzag site of a damaged edge; classify the joint as X (X-plane edge)
     or Z (Z-plane edge);  claims: both joints have the same class;
     class X: every site of the segment has |X| <= 4, and the segment is a complete piece of its foliation line;
     class Z: at most 9 sites, alpha > 0, and the segment is a row segment."""
import sys
from canon import *
from canon_patches import PATCH
AX=[0,1,2,2,1,0]                                           # axis of vertex number i (order -x,-y,-z,+z,+y,+x)
for m in map(int,sys.argv[1:]):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    xs=[v[0] for v in S]; cx=(min(xs)+max(xs))//2
    etype={}
    for a in range(6):
        for b in range(a+1,6):
            e=G.edge(G.vertices[a],G.vertices[b])
            if not e: continue
            t={0,1,2}-{AX[a],AX[b]}; t="XYZ"[t.pop()]          # the plane of the edge
            for v in e: etype[v]=t
    seg={}; segs=[]
    for v in sorted(X):
        if v in seg: continue
        comp=[v]; seg[v]=len(segs); st=[v]
        while st:
            x=st.pop()
            for w in adj[x]:
                if w not in seg and alpha(w)==alpha(x): seg[w]=len(segs); comp.append(w); st.append(w)
        segs.append(comp)
    far=lambda v: all(max(abs(v[t]-V[t]) for t in range(3))>12 for V in G.vertices)
    joints=defaultdict(list)
    for v in X:
        for w in adj[v]:
            if seg[w]!=seg[v]: joints[seg[v]].append((v,w))
    def cls(v):
        c=set()
        for dx in range(-2,3):
            for dy in range(-2,3):
                for dz in range(-2,3):
                    t=etype.get((v[0]+dx,v[1]+dy,v[2]+dz))
                    if t: c.add(t)
        return c
    nX=nZ=0; maxZ=0; maxabsX=0
    for i,js in joints.items():
        if len(js)!=2 or not all(far(v) for v,w in js): continue
        c=[cls(v)|cls(w) for v,w in js]
        assert all(len(x)==1 for x in c) and c[0]==c[1],("mixed or unclassified joints",m,segs[i][:3],c)
        P=segs[i]; al=alpha(P[0]); isrow=any(Z(v)==0 and any(w in E for w in nb[v]) for v in P)
        full=all(sum(1 for w in nb[v] if w in X and rho(w)!=rho(v) and alpha(w)==al and seg.get(w)==i)==sum(1 for w in nb[v] if w in X and rho(w)!=rho(v)) for v in P)
        if c[0]=={'X'}:
            nX+=1; maxabsX=max(maxabsX,max(abs(v[0]-cx) for v in P)); assert max(abs(v[0]-cx) for v in P)<=4 and full and not isrow
        else:
            assert c[0]=={'Z'}; nZ+=1; maxZ=max(maxZ,len(P)); assert len(P)<=9 and al>0 and isrow,("Z-type",m,len(P),al,isrow)
    print("m=%d: far two-joint segments: %d of class X (max |X| = %d, all complete foliation pieces, none a row), %d of class Z (all rows, alpha > 0, at most %d sites) ; no mixed segment"%(m,nX,maxabsX,nZ,maxZ),flush=True)
