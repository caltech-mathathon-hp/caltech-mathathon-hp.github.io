"""Bulk cover of X_m = Oct(m) minus the 12 edge zigzags:
   bent foliation, delete the edges, repair the damaged ends by alternating add/remove paths (degree-constrained subgraph).
   The result is validated explicitly.  Also reports how far from the edges the repair reaches."""
import sys, itertools, time
from collections import Counter, deque
from geom import *
from bent import foliation
def cover(m):
    G=Geo(m); S=G.S
    nb=foliation(S)
    alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    E=set(v for e in alledges for v in e); X=S-E
    adj={v:set(w for w in nb[v] if w in X) for v in X}
    legit=lambda v: bool(G.dang[v])
    lo=lambda v: 1 if legit(v) else 2
    changed=set(); naug=0
    def cycle_through(v):
        for first in list(adj[v]):
            prevs=v; cur=first; walk=[v]
            while True:
                if cur==v: return walk
                walk.append(cur)
                nxt=[w for w in adj[cur] if w!=prevs]
                if not nxt: break
                prevs,cur=cur,nxt[0]
        return None
    def apply(ops):
        for op,a_,b_ in ops:
            if op=='+': adj[a_].add(b_); adj[b_].add(a_)
            else: adj[a_].discard(b_); adj[b_].discard(a_)
    def undo(ops):
        for op,a_,b_ in reversed(ops):
            if op=='+': adj[a_].discard(b_); adj[b_].discard(a_)
            else: adj[a_].add(b_); adj[b_].add(a_)
    def augment(v0,depth=3):
        start=(v0,'+'); prev={start:None}; dq=deque([start]); ntry=0
        while dq:
            u,mode=dq.popleft()
            goals=[]
            if mode=='+':
                for w in nbrs(u):
                    if w not in X or w in adj[u]: continue
                    if len(adj[w])<=1: goals.append((w,'end+'))
                    else:
                        st=(w,'-')
                        if st not in prev: prev[st]=(u,mode); dq.append(st)
            else:
                pu=prev[(u,mode)][0]
                for z in adj[u]:
                    if z==pu: continue
                    if len(adj[z])-1>=lo(z): goals.append((z,'end-'))
                    else:
                        st=(z,'+')
                        if st not in prev: prev[st]=(u,mode); dq.append(st)
            for goal in goals:
                chain=[goal,(u,mode)]
                while prev[chain[-1]] is not None: chain.append(prev[chain[-1]])
                chain=chain[::-1]
                ops=[('+' if ma=='+' else '-',a_,b_) for (a_,ma),(b_,mb) in zip(chain,chain[1:])]
                apply(ops)
                touched=set(x for _,a_,b_ in ops for x in (a_,b_))
                cyc=None
                for x in touched:
                    cyc=cycle_through(x)
                    if cyc: break
                if cyc is None:
                    changed.update(touched); return True
                if depth>0:                                         # break the cycle at a bond next to a surface site
                    L=len(cyc)
                    for i in range(L):
                        x,y=cyc[i],cyc[(i+1)%L]
                        for (p_,q_) in ((x,y),(y,x)):
                            if not legit(q_) or p_==v0: continue
                            adj[p_].discard(q_); adj[q_].discard(p_)
                            ok=True
                            if len(adj[p_])<lo(p_): ok=augment(p_,depth-1)
                            if ok and not any(cycle_through(t) for t in touched|{p_,q_}):
                                changed.update(touched|{p_,q_}); return True
                            if ok and len(adj[p_])>=lo(p_): pass
                            # undo is only safe if the nested augment failed (it leaves no trace)
                            if not ok: adj[p_].add(q_); adj[q_].add(p_)
                            else: return True
                undo(ops); ntry+=1
                if ntry>3000: return False
        return False
    for v in sorted(X):
        while len(adj[v])<lo(v):
            if not augment(v):
                V=min(G.vertices,key=lambda V:max(abs(v[i]-V[i]) for i in range(3)))
                return None,"augmentation failed at site %s rel. to nearest vertex (dist %d), degree %d, legit %s, after %d repairs; neighbours: %s"%(tuple(v[i]-V[i] for i in range(3)),max(abs(v[i]-V[i]) for i in range(3)),len(adj[v]),legit(v),naug,[("E" if w in E else "out" if w not in S else ("legit" if legit(w) else "int",len(adj[w]),w in adj[v])) for w in nbrs(v)]),None
            naug+=1
    if any(len(adj[v])>2 or len(adj[v])<lo(v) for v in X): return None,"degree error",None
    seen=set(); paths=[]
    for v in X:
        if v in seen or len(adj[v])==2: continue
        p=[v]; seen.add(v)
        while True:
            nx=[w for w in adj[p[-1]] if w not in seen]
            if not nx: break
            p.append(nx[0]); seen.add(nx[0])
        paths.append(p)
    ncyc=len(X)-len(seen)
    ok=ncyc==0 and all(legit(p[0]) and legit(p[-1]) and len(p)>=3 for p in paths) and all(p[i+1] in nbrs(p[i]) for p in paths for i in range(len(p)-1))
    # locality: distance of modified sites from the nearest edge site (in bonds, inside S)
    dist={e:0 for e in E}; dq=deque(E)
    while dq:
        x=dq.popleft()
        for w in nbrs(x):
            if w in S and w not in dist: dist[w]=dist[x]+1; dq.append(w)
    # all bonds that differ from the plain foliation
    diff=set(v for v in X if adj[v]!=set(w for w in nb[v] if w in X))
    reach=max((dist[v] for v in diff),default=0)
    D=set()
    for v in X:
        base=set(w for w in nb[v] if w in X)
        for w in adj[v]-base: D.add(('+',)+tuple(sorted((v,w))))
        for w in base-adj[v]: D.add(('-',)+tuple(sorted((v,w))))
    cover.last=(G,E,D,alledges)
    return paths,("valid" if ok else "INVALID (sites on cycles: %d)"%ncyc),(naug,len(diff),reach)
if __name__=="__main__":
    for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
        t0=time.time(); paths,msg,info=cover(m)
        if paths is None: print("m=%2d: FAILED (%s)"%(m,msg),flush=True); continue
        L=[len(p) for p in paths] or [0]
        print("m=%2d: %s ; %d paths (lengths %d..%d) ; %d repairs, %d sites differ from the foliation, all within %d bonds of an edge ; %.0fs"%(m,msg,len(paths),min(L),max(L),info[0],info[1],info[2],time.time()-t0),flush=True)
