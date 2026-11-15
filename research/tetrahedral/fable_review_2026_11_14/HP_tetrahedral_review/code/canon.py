"""Canonical bulk cover of X_m = Oct(m) minus the 12 edge zigzags.
   1. bent foliation (bonds along which rho=|Y|+|Z| changes), restricted to X_m;
   2. rule merges: a damaged end d (its foliation partner was an edge site) is joined to the neighbour w with
        (dY,dZ) = (sgn Z, -sgn Y)        if Y,Z != 0   ("clockwise" rule)
        (dY,dZ) = (-sgn Y, +1)           if Z = 0      ("row" rule)
      provided w is in X_m, is a path end with a free bond, and is claimed by no other damaged end;
   3. six fixed vertex patches (explicit lists of bonds to add/remove, in coordinates relative to the vertex).
   PATCH is produced by make_patches(m0) and then frozen (file canon_patches.py)."""
import sys, time
from fol import *
sg=lambda t:(t>0)-(t<0)
def base(m):
    G,S,E,X,nb,Y,Z,rho,alpha,edges,c=setup(m)
    adj={v:set(w for w in nb[v] if w in X) for v in X}
    legit=lambda v: bool(G.dang[v])
    damaged=[v for v in X if any(w in E for w in nb[v])]
    target={}
    for d in damaged:
        sy,sz=sg(Y(d)),sg(Z(d))
        if sy!=0 and sz!=0: want=(sz,-sy)
        elif sz==0 and sy!=0: want=(-sy,1)
        else: continue
        for w in nbrs(d):
            if (Y(w)-Y(d),Z(w)-Z(d))==want and w in X and w not in adj[d] and len(adj[w])<=1 and legit(w): target[d]=w
    claims=Counter(target.values())
    merges=[(d,w) for d,w in target.items() if claims[w]==1]
    for d,w in merges: adj[d].add(w); adj[w].add(d)
    return G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges
def defects(X,adj,legit):
    return sorted(v for v in X if len(adj[v])<(1 if legit(v) else 2))
def nearest_vertex(G,v):
    return min(G.vertices,key=lambda V:(max(abs(v[i]-V[i]) for i in range(3)),V))
def make_patches(m,radius=9):
    """local repair near each vertex by alternating add/remove paths confined to a ball; returns {vertex index: (adds, removes)} in relative coordinates"""
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=base(m)
    lo=lambda v: 1 if legit(v) else 2
    patches={}
    for iv,V in enumerate(G.vertices):
        ball=set(v for v in X if max(abs(v[i]-V[i]) for i in range(3))<=radius)
        before={v:set(adj[v]) for v in ball}
        rel=lambda v: tuple(v[i]-V[i] for i in range(3))
        def cycle_through(v):
            for first in sorted(adj[v]):
                prevs=v; cur=first
                while True:
                    if cur==v: return True
                    nxt=[w for w in adj[cur] if w!=prevs]
                    if not nxt: break
                    prevs,cur=cur,nxt[0]
            return False
        def augment(v0):
            start=(v0,'+'); prev={start:None}; dq=deque([start])
            while dq:
                u,mode=dq.popleft(); goals=[]
                if mode=='+':
                    for w in sorted(nbrs(u),key=rel):
                        if w not in ball or w in adj[u]: continue
                        if len(adj[w])<=1: goals.append((w,'end+'))
                        elif (w,'-') not in prev: prev[(w,'-')]=(u,mode); dq.append((w,'-'))
                else:
                    pu=prev[(u,mode)][0]
                    for z in sorted(adj[u],key=rel):
                        if z==pu or z not in ball: continue
                        if len(adj[z])-1>=lo(z): goals.append((z,'end-'))
                        elif (z,'+') not in prev: prev[(z,'+')]=(u,mode); dq.append((z,'+'))
                for goal in goals:
                    chain=[goal,(u,mode)]
                    while prev[chain[-1]] is not None: chain.append(prev[chain[-1]])
                    chain=chain[::-1]
                    ops=[('+' if ma=='+' else '-',a_,b_) for (a_,ma),(b_,mb) in zip(chain,chain[1:])]
                    for op,a_,b_ in ops:
                        if op=='+': adj[a_].add(b_); adj[b_].add(a_)
                        else: adj[a_].discard(b_); adj[b_].discard(a_)
                    touched=set(x for _,a_,b_ in ops for x in (a_,b_))
                    if not any(cycle_through(x) for x in touched): return True
                    for op,a_,b_ in reversed(ops):
                        if op=='+': adj[a_].discard(b_); adj[b_].discard(a_)
                        else: adj[a_].add(b_); adj[b_].add(a_)
            return False
        todo=[v for v in sorted(ball,key=rel) if len(adj[v])<lo(v)]
        for v in todo:
            while len(adj[v])<lo(v):
                if not augment(v): raise Exception("patch search failed at vertex %s, site %s"%(V,rel(v)))
        adds=set(); rems=set()
        for v in ball:
            for w in adj[v]-before[v]: adds.add(tuple(sorted((rel(v),rel(w)))))
            for w in before[v]-adj[v]: rems.add(tuple(sorted((rel(v),rel(w)))))
        patches[iv]=(sorted(adds),sorted(rems))
    return patches
def cover(m,patches):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=base(m)
    for iv,V in enumerate(G.vertices):
        adds,rems=patches[iv]
        ab=lambda r: tuple(r[i]+V[i] for i in range(3))
        for a,b in rems:
            a,b=ab(a),ab(b); assert a in X and b in X and b in adj[a],("patch remove mismatch",m,iv); adj[a].discard(b); adj[b].discard(a)
        for a,b in adds:
            a,b=ab(a),ab(b); assert a in X and b in X and b in nbrs(a) and b not in adj[a],("patch add mismatch",m,iv); adj[a].add(b); adj[b].add(a)
    return G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges
def validate(X,adj,legit):
    if any(len(adj[v])>2 for v in X): return "degree > 2",None
    bad=[v for v in X if len(adj[v])<(1 if legit(v) else 2)]
    if bad: return "%d sites with too few partners"%len(bad),None
    seen=set(); paths=[]
    for v in X:
        if v in seen or len(adj[v])==2: continue
        p=[v]; seen.add(v)
        while True:
            nx=[w for w in adj[p[-1]] if w not in seen]
            if not nx: break
            p.append(nx[0]); seen.add(nx[0])
        paths.append(p)
    if len(seen)!=len(X): return "%d sites on cycles"%(len(X)-len(seen)),None
    if not all(len(p)>=3 for p in paths): return "a path with fewer than 3 sites",None
    if not all(legit(p[0]) and legit(p[-1]) for p in paths): return "an end without free bond",None
    return "valid",paths
if __name__=="__main__":
    if sys.argv[1]=="make":
        m0=int(sys.argv[2]); P=make_patches(m0)
        G=Geo(m0)
        with open("canon_patches.py","w") as f:
            f.write("# vertex patches found for m=%d; vertices in the order of Geo(m).vertices; coordinates relative to the vertex\n"%m0)
            f.write("PATCH=%r\n"%P)
        for iv,(a,r) in P.items(): print("vertex %d %s: %d bonds added, %d removed"%(iv,G.vertices[iv],len(a),len(r)))
    else:
        from canon_patches import PATCH
        for m in range(int(sys.argv[1]),int(sys.argv[2])+1,int(sys.argv[3]) if len(sys.argv)>3 else 1):
            t0=time.time()
            try:
                G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
                msg,paths=validate(X,adj,legit)
                extra="" if paths is None else " ; %d paths, lengths %d..%d ; %d rule merges"%(len(paths),min(map(len,paths)),max(map(len,paths)),len(merges))
            except AssertionError as ex: msg,extra="FAILED %r"%(ex.args,),""
            print("m=%2d: %s%s ; %.0fs"%(m,msg,extra,time.time()-t0),flush=True)
