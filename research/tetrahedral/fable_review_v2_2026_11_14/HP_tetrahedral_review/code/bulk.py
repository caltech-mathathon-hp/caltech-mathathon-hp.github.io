"""Bulk cover: partition a site set X (bipartite Maj/Min) into nP odd paths whose ends are 'eligible' Maj sites.
Method: degree-constrained subgraph by max-flow (two stages), then removal of cycles by hexagon flips."""
import sys, random
from collections import deque, defaultdict
from diamond import *

def dinic(n, adj, cap, to, s, t):
    flow=0
    while True:
        level=[-1]*n; level[s]=0; dq=deque([s])
        while dq:
            u=dq.popleft()
            for e in adj[u]:
                if cap[e]>0 and level[to[e]]<0:
                    level[to[e]]=level[u]+1; dq.append(to[e])
        if level[t]<0: return flow
        it=[0]*n
        # iterative DFS blocking flow
        while True:
            # find augmenting path
            stack=[s]; path=[]
            found=False
            while stack:
                u=stack[-1]
                if u==t: found=True; break
                advanced=False
                while it[u]<len(adj[u]):
                    e=adj[u][it[u]]
                    v=to[e]
                    if cap[e]>0 and level[v]==level[u]+1:
                        stack.append(v); path.append(e); advanced=True; break
                    it[u]+=1
                if not advanced:
                    stack.pop()
                    if path: path.pop()
                    if stack: it[stack[-1]]+=1
            if not found: break
            f=min(cap[e] for e in path)
            for e in path:
                cap[e]-=f; cap[e^1]+=f
            flow+=f

def bulk_cover(X, is_maj, eligible, nP, seed=0, verbose=True):
    rnd=random.Random(seed)
    X=set(X)
    maj=[v for v in X if is_maj(v)]; mn=[v for v in X if not is_maj(v)]
    assert len(maj)-len(mn)==nP, ("imbalance",len(maj)-len(mn),nP)
    idx={}
    for v in mn: idx[v]=len(idx)+2
    for v in maj: idx[v]=len(idx)+2
    n=len(idx)+2; s=0; t=1
    adj=[[] for _ in range(n)]; cap=[]; to=[]
    def add(u,v,c):
        adj[u].append(len(cap)); to.append(v); cap.append(c)
        adj[v].append(len(cap)); to.append(u); cap.append(0)
    for v in mn: add(s,idx[v],2)
    mm_edges=[]
    for v in mn:
        for w in nbrs(v):
            if w in X:
                mm_edges.append((v,w,len(cap))); add(idx[v],idx[w],1)
    sink_e={}
    for v in maj:
        sink_e[v]=len(cap); add(idx[v],t,1 if v in eligible else 2)
    f1=dinic(n,adj,cap,to,s,t)
    need1=sum(1 if v in eligible else 2 for v in maj)
    if f1!=need1:
        if verbose: print("  stage 1 flow",f1,"needed",need1); 
        return None
    for v in maj:
        if v in eligible: cap[sink_e[v]]+=1
    f2=dinic(n,adj,cap,to,s,t)
    if f1+f2!=2*len(mn):
        if verbose: print("  stage 2 total",f1+f2,"needed",2*len(mn))
        return None
    sel=defaultdict(set)
    for v,w,e in mm_edges:
        if cap[e]==0: sel[v].add(w); sel[w].add(v)
    ends=[v for v in maj if len(sel[v])==1]
    assert len(ends)==2*nP and all(len(sel[v])==2 for v in X if v not in ends)
    # components
    def components():
        comp={}; kinds=[]
        for v in ends:
            if v in comp: continue
            c=len(kinds); kinds.append('path'); prev=None; cur=v
            while cur is not None:
                comp[cur]=c
                nx=[w for w in sel[cur] if w!=prev]
                prev,cur=cur,(nx[0] if nx else None)
        for v in X:
            if v in comp: continue
            c=len(kinds); kinds.append('cycle'); prev=None; cur=v
            while cur not in comp:
                comp[cur]=c
                nx=[w for w in sel[cur] if w!=prev]
                prev,cur=cur,nx[0]
        return comp,kinds
    comp,kinds=components()
    ncyc=kinds.count('cycle')
    if verbose: print("  after flow: %d paths, %d cycles"%(kinds.count('path'),ncyc))
    # hexagons
    hexes=set()
    for v in maj if sum(next(iter(X)))%4!=0 else X:
        pass
    Tm=T
    for v in X:
        if sum(v)%4!=0: continue
        for a in range(4):
            for b in range(4):
                if b==a: continue
                for c in range(4):
                    if c==a or c==b: continue
                    p0=v; p1=tuple(p0[i]+Tm[a][i] for i in range(3)); p2=tuple(p1[i]-Tm[b][i] for i in range(3))
                    p3=tuple(p2[i]+Tm[c][i] for i in range(3)); p4=tuple(p3[i]-Tm[a][i] for i in range(3)); p5=tuple(p4[i]+Tm[b][i] for i in range(3))
                    h=(p0,p1,p2,p3,p4,p5)
                    if all(p in X for p in h):
                        key=frozenset(h)
                        if key not in hexes: hexes.add(key); 
    hexlist=[]
    seen=set()
    for v in X:
        if sum(v)%4!=0: continue
        for a in range(4):
            for b in range(4):
                if b==a: continue
                for c in range(4):
                    if c==a or c==b: continue
                    p0=v; p1=tuple(p0[i]+Tm[a][i] for i in range(3)); p2=tuple(p1[i]-Tm[b][i] for i in range(3))
                    p3=tuple(p2[i]+Tm[c][i] for i in range(3)); p4=tuple(p3[i]-Tm[a][i] for i in range(3)); p5=tuple(p4[i]+Tm[b][i] for i in range(3))
                    h=(p0,p1,p2,p3,p4,p5); key=frozenset(h)
                    if key in hexes and key not in seen: seen.add(key); hexlist.append(h)
    by_site=defaultdict(list)
    for i,h in enumerate(hexlist):
        for p in h: by_site[p].append(i)
    def pattern(h):
        e=[(h[i],h[(i+1)%6]) for i in range(6)]
        s_=[b in sel[a] for a,b in e]
        if s_==[True,False,True,False,True,False]: return 0
        if s_==[False,True,False,True,False,True]: return 1
        return None
    def flip(h,off):
        for i in range(6):
            a,b=h[i],h[(i+1)%6]
            if i%2==off: sel[a].discard(b); sel[b].discard(a)
            else: sel[a].add(b); sel[b].add(a)
    def count_cycles_local(sites):
        """number of cycles among the components containing the given sites"""
        seen_=set(); cyc=0
        for v in sites:
            if v in seen_: continue
            # walk
            prev=None; cur=v; iscyc=True; stack=[v]; seen_.add(v)
            # traverse both directions
            nb=list(sel[v])
            for start in nb:
                prev=v; cur=start
                while cur is not None and cur not in seen_:
                    seen_.add(cur)
                    nx=[w for w in sel[cur] if w!=prev]
                    prev,cur=cur,(nx[0] if nx else None)
                if cur is None: iscyc=False
            if len(nb)<2: iscyc=False
            if iscyc: cyc+=1
        return cyc
    stall=0; it=0
    while ncyc>0 and it<400000:
        it+=1
        # pick a site on a cycle
        comp,kinds=components() if it%200==1 else (comp,kinds)
        cyc_sites=[v for v in X if kinds[comp[v]]=='cycle'] if it%200==1 else cyc_sites
        if not cyc_sites: break
        v=rnd.choice(cyc_sites)
        cand=[hi for hi in by_site[v] if pattern(hexlist[hi]) is not None]
        if not cand: continue
        hi=rnd.choice(cand); h=hexlist[hi]; off=pattern(h)
        before=count_cycles_local(h)
        flip(h,off)
        after=count_cycles_local(h)
        if after<before or (after==before and rnd.random()<0.3):
            ncyc+=after-before
            if after<before: stall=0; comp,kinds=components(); cyc_sites=[v for v in X if kinds[comp[v]]=='cycle']
        else:
            flip(h,1-off)
    comp,kinds=components()
    if verbose: print("  after flips: %d paths, %d cycles (iterations %d)"%(kinds.count('path'),kinds.count('cycle'),it))
    if kinds.count('cycle')>0: return None
    paths=[]
    done=set()
    for v in ends:
        if v in done: continue
        p=[v]; prev=None; cur=v
        while True:
            nx=[w for w in sel[cur] if w!=prev]
            if not nx: break
            prev,cur=cur,nx[0]; p.append(cur)
        done.add(p[0]); done.add(p[-1]); paths.append(p)
    assert sum(len(p) for p in paths)==len(X)
    return paths
