"""Structure of the canonical cover used in the acyclicity proof (notes 10.4.1, 'Part 3'):
   segments = maximal pieces of cover paths made of foliation bonds; joints = cover bonds that are not foliation bonds.
   Claims checked: (1) a segment with a joint near a Z-plane edge or within RV of a vertex is short;
   (2) every other segment with a joint is 'long-generic': all its joints lie next to X-plane edges, in the slabs |X| <= 5;
   (3) for long-generic segments with two joints the two neighbours are as in the hand analysis:
       bend at Z=0 : alpha+2 at one end and alpha-2 at the other (ladder);  bend at Y=0 : X-pairs on opposite sides."""
import sys
from canon import *
from canon_patches import PATCH
RV=16
def analyse(m):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    msg,paths=validate(X,adj,legit); assert msg=="valid"
    fol=lambda v,w: rho(v)!=rho(w)
    edges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    def kind(e):
        if max(abs(v[0]) for v in e)<=1: return 'X'
        if max(abs(Y(v)) for v in e)<=1: return 'Y'
        return 'Z'
    near={}                                   # site -> kind of edge within 2 bonds
    for e in edges:
        k=kind(e)
        for v in e:
            for w in nbrs(v):
                near.setdefault(w,k)
                for u in nbrs(w): near.setdefault(u,k)
    dv=lambda v: min(max(abs(v[i]-V[i]) for i in range(3)) for V in G.vertices)
    segs=[]
    for p in paths:
        cur=[p[0]]
        for a,b in zip(p,p[1:]):
            if fol(a,b): cur.append(b)
            else: segs.append(cur); cur=[b]
        segs.append(cur)
    segof={v:i for i,s in enumerate(segs) for v in s}
    stats=Counter(); maxshort=0; table={}; bad=0
    for i,s in enumerate(segs):
        joints=[(v,w) for v in (s[0],s[-1]) for w in adj[v] if not fol(v,w)]
        if len(s)==1: joints=[(s[0],w) for w in adj[s[0]] if not fol(s[0],w)]
        if not joints: continue
        nearZ=any(near.get(v)=='Z' for v,w in joints); nearV=any(dv(v)<=RV for v,w in joints)
        if nearZ or nearV:
            stats['short-type']+=1; maxshort=max(maxshort,len(s)); continue
        stats['long-generic']+=1
        if not all(near.get(v)=='X' and abs(v[0])<=5 for v,w in joints): bad+=1; continue
        if len(joints)==2:
            a0=alpha(s[0]); xs=(min(v[0] for v in s),max(v[0] for v in s))
            nbd=[]
            for v,w in joints:
                t=segs[segof[w]]; nbd.append((alpha(w)-a0,min(u[0] for u in t)+max(u[0] for u in t)-(xs[0]+xs[1])))
            da=sorted(d for d,_ in nbd); dx=sorted(d for _,d in nbd)
            if a0>0: ok=(da==[-2,2])
            else: ok=(dx[0]<0<dx[1]) or any(alpha(w)>0 for v,w in joints)
            stats['two-joint ok' if ok else 'two-joint BAD']+=1
    return len(segs),dict(stats),maxshort,bad
for m in [int(a) for a in sys.argv[1:]] or [24,31,40]:
    n,st,ms,bad=analyse(m)
    print("m=%d: %d segments ; %s ; longest short-type segment %d sites ; long-generic with a joint away from X-plane edges: %d"%(m,n,st,ms,bad))
