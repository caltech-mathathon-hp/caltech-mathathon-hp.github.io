import sys
from fol import *
m=int(sys.argv[1])
G,S,E,X,nb,Y,Z,rho,alpha,edges,c=setup(m)
xs=[v[0] for v in S]; cx=(min(xs)+max(xs))//2
print("m=%d centre (cx,cy,cz)=(%d,%d,%d)  x-range %d..%d"%(m,cx,c[0],c[1],min(xs),max(xs)))
adj={v:[w for w in nb[v] if w in X] for v in X}
legit=lambda v: bool(G.dang[v])
for k,e in enumerate(edges):
    mid=e[len(e)//2-4:len(e)//2+4]
    Ys=sorted(set(Y(v) for v in e)); Zs=sorted(set(Z(v) for v in e)); Xs=sorted(set(v[0]-cx for v in e))
    cls="X-plane" if len(Xs)<=3 else ("Y-plane" if len(Ys)<=3 else "Z-plane")
    # foliation pieces through edge sites
    inE=Counter(); dam=0
    for z in e[1:-1]:
        inE[tuple(sorted(("E" if w in E else "X") for w in nb[z]))]+=1
    # damaged ends caused by this edge: X-sites with a foliation neighbour on this edge
    es=set(e)
    dmg=[v for v in X if any(w in es for w in nb[v])]
    npart=Counter()
    for v in dmg:
        cand=[w for w in nbrs(v) if w in X and w not in adj[v] and len(adj[w])<=1 and legit(w)]
        npart[len(cand)]+=1
    print("edge %2d %-8s X in %s Y in %s Z in %s | foliation nbrs of edge sites: %s | damaged ends %d, by #free legit-end neighbours %s"%(k,cls,Xs if len(Xs)<=3 else "..",Ys if len(Ys)<=3 else "..",Zs if len(Zs)<=3 else "..",dict(inE),len(dmg),dict(sorted(npart.items()))))
