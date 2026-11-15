import sys
from fol import *
def run(m,verbose=True):
    G,S,E,X,nb,Y,Z,rho,alpha,edges,c=setup(m)
    adj={v:set(w for w in nb[v] if w in X) for v in X}
    legit=lambda v: bool(G.dang[v])
    sg=lambda t: (t>0)-(t<0)
    damaged=[v for v in X if any(w in E for w in nb[v])]
    isolated=[v for v in X if not adj[v]]
    # clockwise rule: partner = neighbour with (dY,dZ) = (sZ,-sY) where (sY,sZ) = signs of (Y,Z) ; on the planes use the unique candidate
    used={}; left=[]; how=Counter()
    for d in sorted(damaged):
        sy,sz=sg(Y(d)),sg(Z(d))
        cands=[w for w in nbrs(d) if w in X and w not in adj[d] and len(adj[w])<=1 and legit(w)]
        if sy!=0 and sz!=0:
            pick=[w for w in cands if (Y(w)-Y(d),Z(w)-Z(d))==(sz,-sy)]; tag='clockwise'
        else:
            pick=cands if len(cands)==1 else []; tag='plane'
        if pick and pick[0] not in used: used[pick[0]]=d; how[tag]+=1
        else: left.append(d)
    for w,d in used.items(): adj[d].add(w); adj[w].add(d)
    # cycles?
    seen=set(); npath=0
    for v in X:
        if v in seen or len(adj[v])==2: continue
        cur=v; seen.add(v)
        while True:
            nx=[w for w in adj[cur] if w not in seen]
            if not nx: break
            cur=nx[0]; seen.add(cur)
        npath+=1
    ncyc=len(X)-len(seen)
    dv=lambda v: min((max(abs(v[i]-V[i]) for i in range(3)),V) for V in G.vertices)
    if verbose:
        print("m=%d: damaged ends %d, isolated %d ; repaired by rule: %s ; left over %d ; sites on cycles %d"%(m,len(damaged),len(isolated),dict(how),len(left),ncyc))
        for d in left:
            dist,V=dv(d)
            print("   leftover: rel. to vertex %s -> %s (Y,Z)=(%d,%d) alpha %d, deg %d, non-path nbrs: %s"%(V,tuple(d[i]-V[i] for i in range(3)),Y(d),Z(d),alpha(d),len(adj[d]),
                  [("E" if w in E else "out" if w not in S else ("legit" if legit(w) else "int",len(adj[w]),(Y(w)-Y(d),Z(w)-Z(d)))) for w in nbrs(d) if w not in adj[d]]))
        for v in isolated:
            dist,V=dv(v); print("   isolated: rel. to vertex %s -> %s (Y,Z)=(%d,%d) legit %s"%(V,tuple(v[i]-V[i] for i in range(3)),Y(v),Z(v),legit(v)))
    return len(left),ncyc
if __name__=="__main__":
    for m in [int(x) for x in sys.argv[1:]]: run(m)
