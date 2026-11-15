"""Outward foliation arms ('columns') from dangling sites: disjointness, and conflicts with P^3 links along the edges
   and with the run ends of the canonical bulk cover."""
import sys
from canon import *
from canon_patches import PATCH
m=int(sys.argv[1]) if len(sys.argv)>1 else 20
G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
msg,paths=validate(X,adj,legit); assert msg=="valid"
sg=lambda t:(t>0)-(t<0)
def arm(p,n):
    """outward arm from outside site p: straight zigzag in direction (0,sgnY,sgnZ) of its quadrant (at a bend: quadrant of its owner face)"""
    out=[p]; cur=p
    sy,sz=sg(Y(p)),sg(Z(p))
    if sy==0 or sz==0:
        f=G.face_of[p]; sy=sy or sg(f[1]); sz=sz or sg(f[2])
    for _ in range(n):
        nx=[w for w in nbrs(cur) if (Y(w)-Y(cur),Z(w)-Z(cur))==(sy,sz)]
        assert len(nx)==1; cur=nx[0]; out.append(cur)
    return out
dang=list(G.owner)                       # all dangling sites
quad_ok=sum(1 for p in dang if sg(Y(p))==sg(G.face_of[p][1]) and (sg(Z(p))==sg(G.face_of[p][2]) or Z(p)==0))
print("m=%d: dangling sites %d ; in the closed quadrant of their face: %d"%(m,len(dang),quad_ok))
A={p:arm(p,30) for p in dang}
occ={}
clash=0; inS=0; hitd=0
dset=set(dang)
for p,a in A.items():
    for s in a:
        if s in S: inS+=1
        if s in occ: clash+=1
        occ[s]=p
    hitd+=sum(1 for s in a[1:] if s in dset)
print("arms of all dangling sites: sites in Oct %d, pairwise clashes %d, arms through another dangling site %d"%(inS,clash,hitd))
# rho strictly increasing by 2 along arms
assert all(rho(a[i+1])==rho(a[i])+2 for a in A.values() for i in range(len(a)-1))
# P^3 link middle sites along all edges
def ppp(u,w):
    r=[]
    for du in G.dang[u]:
        for x in nbrs(du):
            if x in S: continue
            for dw in G.dang[w]:
                if dw!=du and dw in nbrs(x): r.append((du,x,dw))
    return r
edges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
mid={}
for ei,e in enumerate(edges):
    for i in range(0,len(e)-2):
        for l in ppp(e[i],e[i+2]): mid[l[1]]=(ei,i)
blocked={}
for q,(ei,i) in mid.items():
    if q in occ:
        p=occ[q]; e=edges[ei]
        if G.owner[p] not in (e[i],e[i+2]): blocked.setdefault(ei,[]).append((G.owner[p],i))
ends=set(v for pth in paths for v in (pth[0],pth[-1]))
print("edges whose links block arms of third sites:",{ei:len(v) for ei,v in blocked.items()})
for ei,lst in blocked.items():
    e=edges[ei]
    xs=sorted(set(v[0] for v in e)); ys=sorted(set(Y(v) for v in e)); zs=sorted(set(Z(v) for v in e))
    nend=sum(1 for v,i in lst if v in ends)
    print("  edge %d: X in %s..%s Y %s..%s Z %s..%s ; blocked third sites %d, of which bulk-run ends %d ; in X_m: %d"%(ei,xs[0],xs[-1],ys[0],ys[-1],zs[0],zs[-1],len(lst),nend,sum(1 for v,i in lst if v in X)))
print("bulk paths %d ; run ends %d ; ends on big faces %d, small %d"%(len(paths),len(ends),sum(1 for v in ends if G.face_of[G.dang[v][0]] in G.big),sum(1 for v in ends if G.face_of[G.dang[v][0]] in G.small)))
