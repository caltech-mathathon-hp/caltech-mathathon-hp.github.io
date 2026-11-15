"""Pinning lemma for the dimer-anchor design: where can a separator HH PPP HH sit, given its two tethers?
Necessary conditions only: outside distance (obstacle = S only) and perfect matchability of the remaining free zigzag sites."""
import sys, itertools
from collections import deque
from geom import *
m=int(sys.argv[1]); K=int(sys.argv[2]); CAP=int(sys.argv[3]); SL=int(sys.argv[4]) if len(sys.argv)>4 else 2
J1=max(CAP+3,3*(K+1)); JS=[J1+k*(CAP+2) for k in range(K+1)]; R=(m-2)-(JS[-1]+1)
assert R>=max(CAP+3,5*K+3),("track too short",R)
SL1=[3*(k+1) for k in range(K+1)]; SL2=[5*k+3 for k in range(K+1)]
G=Geo(m,margin=400); S=G.S
small=[t for t in G.small_face_triples() if t[3]=='small']
Va,Vb,Vc=small[0][0],small[0][1],small[0][2]
e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc); e2c=e2[::-1]
# free zigzag sites: extended track (path) and three rings (cycles)
track=[e1[2],e1[1]]+[e3[i] for i in range(2,2*m-2)]
rings=[]
for (A_,B_,C_,kind,n_) in small[1:]:
    ring=[]
    for V,W in ((A_,B_),(B_,C_),(C_,A_)): ring+=G.edge(V,W)[1:2*m-3]
    rings.append(ring)
comp={}                                  # site -> (component id, index)
for i,v in enumerate(track): comp[v]=(0,i)
for r,ring in enumerate(rings):
    for i,v in enumerate(ring): comp[v]=(r+1,i)
free=set(comp)
def matchable(used):
    """remaining free zigzag sites must still have a perfect matching"""
    u0=sorted(comp[v][1] for v in used if comp[v][0]==0)
    prev=-1
    for i in u0+[len(track)]:
        if (i-prev-1)%2: return False
        prev=i
    for r,ring in enumerate(rings):
        ur=sorted(comp[v][1] for v in used if comp[v][0]==r+1)
        if not ur: continue
        L=len(ring)
        for a,b in zip(ur,ur[1:]+[ur[0]+L]):
            if (b-a-1)%2: return False
    return True
bonded={v:[w for w in nbrs(v) if w in free] for v in free}
def ppp_partners(v):
    res=set()
    for d in G.dang[v]:
        for x in nbrs(d):
            if x in S: continue
            for d2 in nbrs(x):
                if d2!=d and d2 in G.owner and G.owner[d2] in free and G.owner[d2]!=v: res.add((G.owner[d2],d,d2))
    return res
place=[]
for w1 in free:
    for w2 in bonded[w1]:
        for (w3,dd2,dd3) in ppp_partners(w2):
            if w3 in (w1,w2): continue
            for w4 in bonded[w3]:
                if w4 in (w1,w2,w3): continue
                if not matchable({w1,w2,w3,w4}): continue
                for d1 in G.dang[w1]:
                    if d1==dd2: continue
                    for d4 in G.dang[w4]:
                        if d4==dd3: continue
                        place.append((w1,w2,w3,w4,d1,d4))
print("m=%d K=%d CAP=%d slack=%d: %d free zigzag sites, %d matchable placements of HH PPP HH"%(m,K,CAP,SL,len(free),len(place)))
# anchors: any end of a dimer chain filling a slot, any dangling site of it
ent=[(e1[2*s+i]) for s in SL1 for i in (0,1)]
ext=[e2c[2*s+i] for s in SL2 for i in (0,1,4,5)]
gmax=2*(m-2)+4
def outd(src,lim):
    dist={src:0}; dq=deque([src])
    while dq:
        v=dq.popleft()
        if dist[v]>=lim: continue
        for w in nbrs(v):
            if w in dist or w in S: continue
            dist[w]=dist[v]+1; dq.append(w)
    return dist
dE=[outd(d,gmax) for q in ent for d in G.dang[q]]; dX=[outd(d,gmax) for q in ext for d in G.dang[q]]
tidx={v:i for i,v in enumerate(track)}
allok=True
for k,j in enumerate(JS):
    g=2*j+1+SL; gp=2*(m-3-j)+1+SL
    ok=set()
    for (w1,w2,w3,w4,d1,d4) in place:
        if not any(d1 in d and d[d1]<=g-1 and (g-1-d[d1])%2==0 for d in dE): continue
        if not any(d4 in d and d[d4]<=gp-1 and (gp-1-d[d4])%2==0 for d in dX): continue
        if all(w in tidx for w in (w1,w2,w3,w4)):
            idx=sorted(tidx[w] for w in (w1,w2,w3,w4)); ok.add(("track dimers %d,%d"%(idx[0]//2,idx[2]//2), "ends "+"".join("b" if tidx[w]%2 else "a" for w in (w1,w4))))
        else: ok.add(("ELSEWHERE",str(sorted(comp[w] for w in (w1,w2,w3,w4)))))
    exp={"track dimers %d,%d"%(i,i+1) for i in range(j-SL//2,j+SL//2+1)}
    good=set(o[0] for o in ok)<=exp and len(ok)>0
    allok&=good
    print("  separator %d (intended dimers %d,%d; tethers P^%d, P^%d): feasible: %s  %s"%(k+1,j,j+1,g,gp,sorted(ok),"OK" if good else "UNEXPECTED"))
print("all separators pinned to within +-%d dimer of their place:"%(SL//2),allok)
