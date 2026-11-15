"""Bulk cover = bent foliation minus the edge zigzags + local repair by matching (each damaged end is joined to an
adjacent free path end).  Verifies the result: disjoint paths covering X, >=3 sites each, both ends surface sites."""
import sys, itertools
from collections import Counter, defaultdict
from geom import *
from bent import foliation
def cover(m,verbose=False):
    G=Geo(m); S=G.S
    nb=foliation(S)
    alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    E=set(v for e in alledges for v in e)
    X=S-E
    adj={v:[w for w in nb[v] if w in X] for v in X}
    legit=lambda v: bool(G.dang[v])
    need={v:(2-len(adj[v]) if not legit(v) else (1 if len(adj[v])==0 else 0)) for v in X}     # extra bonds required
    bad=[v for v in X if need[v]>0]
    # candidate partners: neighbours in X, not already path-neighbours, with degree <=1
    cand={v:[w for w in nbrs(v) if w in X and w not in adj[v] and len(adj[w])<=1] for v in bad}
    # bipartite matching: copies of bad sites (one per needed bond) -> partner sites (capacity: 2-deg, but a legit end stays usable once)
    left=[(v,i) for v in bad for i in range(need[v])]
    capacity=lambda w: (2-len(adj[w])) - need.get(w,0) if not legit(w) else 1 if len(adj[w])==1 else 2
    match={}                                                    # partner site -> list of left nodes
    def try_aug(u,seen):
        v=u[0]
        for w in cand[v]:
            if w in seen: continue
            if w in bad and not legit(w): continue            # keep it simple: partners are legit ends only
            seen.add(w)
            cur=match.setdefault(w,[])
            if any(x[0]==v for x in cur): continue
            if len(cur)<capacity(w): cur.append(u); return True
            for j,x in enumerate(cur):
                if try_aug(x,seen): cur[j]=u; return True
        return False
    unm=0
    for u in left:
        if not try_aug(u,set()): unm+=1
    if unm: return None,"%d damaged ends could not be matched"%unm,None
    for w,us in match.items():
        for (v,i) in us: adj[v].append(w); adj[w].append(v)
    # verify
    if any(len(adj[v])>2 for v in X): return None,"degree >2",None
    seen=set(); paths=[]
    for v in X:
        if v in seen or len(adj[v])==2: continue
        p=[v]; seen.add(v)
        while True:
            nx=[w for w in adj[p[-1]] if w not in seen]
            if not nx: break
            p.append(nx[0]); seen.add(nx[0])
        paths.append(p)
    if len(seen)!=len(X): return None,"%d sites lie on cycles"%(len(X)-len(seen)),None
    okends=all(legit(p[0]) and legit(p[-1]) for p in paths); oklen=all(len(p)>=3 for p in paths)
    okwalk=all(p[i+1] in nbrs(p[i]) for p in paths for i in range(len(p)-1))
    return paths,("valid" if okends and oklen and okwalk else "INVALID ends=%s len=%s"%(okends,oklen)),(len(bad),G)
if __name__=="__main__":
    for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
        paths,msg,info=cover(m)
        if paths is None: print("m=%2d: FAILED (%s)"%(m,msg)); continue
        L=Counter(len(p) for p in paths)
        print("m=%2d: %s ; %d paths, lengths %d..%d ; %d damaged ends repaired"%(m,msg,len(paths),min(L),max(L),info[0]),flush=True)
