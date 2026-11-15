# Bar decomposition of Oct(m) and an explicit perfect fold of an explicit HP string.
import sys
from collections import deque, Counter
from diamond import *
from oct import octa

def bars_of(S):
    """components of S under t1/t2 bonds only (zigzag chains in direction (0,1,1))"""
    S=set(S); seen=set(); bars=[]
    def zn(v):  # neighbours along t1,t2
        x,y,z=v
        if (x+y+z)%4==0: c=[(x+1,y+1,z+1),(x+1,y-1,z-1)]
        else: c=[(x-1,y-1,z-1),(x-1,y+1,z+1)]
        return c
    for v in sorted(S):
        if v in seen: continue
        # walk to one end
        comp=[v]; seen.add(v)
        ends=[w for w in zn(v) if w in S]
        # extend both directions
        path=deque([v])
        for d,start in enumerate(ends):
            prev=v; cur=start
            while cur is not None and cur not in seen:
                seen.add(cur)
                if d==0: path.append(cur)
                else: path.appendleft(cur)
                nx=[w for w in zn(cur) if w in S and w!=prev]
                prev,cur=cur,(nx[0] if nx else None)
        bars.append(list(path))
    return bars,zn

def build_fold(m,verbose=True):
    S=octa(m); bars,zn=bars_of(S)
    N=len(S); assert N==m*(4*m*m-1)//3
    cnt=Counter(len(b) for b in bars)
    ok=all(cnt[2*a-1]==2*a-1 for a in range(1,m+1)) and sum(cnt.values())==m*m
    # exit sites: continuation of the zigzag beyond each end
    def exits(b):
        e0=[w for w in zn(b[0]) if w not in S]; e1=[w for w in zn(b[-1]) if w not in S]
        if len(b)==1: return e0[0],e0[1]
        return e0[0],e1[0]
    ex={i:exits(b) for i,b in enumerate(bars)}
    reserved=set(p for pq in ex.values() for p in pq)
    assert len(reserved)==2*len(bars)
    # order bars: by layer pair (x of first even layer), then row, snake
    def key(b):
        xs=sorted(set(v[0] for v in b)); 
        return (min(xs), b[0][1]-b[0][2])
    order=sorted(range(len(bars)),key=lambda i:key(bars[i]))
    used=set(); chain=[]; seq=[]
    lo=min(min(v) for v in S)-8; hi=max(max(v) for v in S)+8
    def inbox(v): return all(lo<=c<=hi for c in v)
    def route(p,q):
        if p==q: return [p]
        prev={p:None}; dq=deque([p])
        while dq:
            v=dq.popleft()
            for w in nbrs(v):
                if w in prev or w in S or w in used or not inbox(w): continue
                if w in reserved and w!=q: continue
                prev[w]=v
                if w==q:
                    path=[w]
                    while prev[path[-1]] is not None: path.append(prev[path[-1]])
                    return path[::-1]
                dq.append(w)
        return None
    flip=False; last_exit=None; linkers=[]
    for n,i in enumerate(order):
        b=bars[i]; a,c=ex[i]
        cand=[(b,a,c),(b[::-1],c,a)]
        best=None
        for bb,ein,eout in cand:
            if last_exit is None: best=(bb,ein,eout,[ein]); break
            r=route(last_exit,ein)
            if r is not None and (best is None or len(r)<len(best[3])): best=(bb,ein,eout,r)
        assert best is not None,"routing failed"
        bb,ein,eout,r=best
        for s in r: used.add(s); chain.append(s); seq.append('P')
        if last_exit is not None: linkers.append(len(r))
        for s in bb: chain.append(s); seq.append('H')
        last_exit=eout
    chain.append(last_exit); seq.append('P'); used.add(last_exit)
    # verification
    assert len(set(chain))==len(chain),"not self-avoiding"
    assert all(chain[i+1] in nbrs(chain[i]) for i in range(len(chain)-1)),"not a walk"
    H=set(v for v,c in zip(chain,seq) if c=='H'); assert H==S
    e=edges(H); bound=2*N-2*m*m
    s=''.join(seq)
    if verbose:
        print("m=%d  N_m=%d  bars: %s  bar-count law (2a-1 bars of length 2a-1): %s"%(m,N,dict(sorted(cnt.items())),ok))
        print("     chain length %d, #P=%d, linker lengths used: %s"%(len(s),s.count('P'),dict(sorted(Counter(linkers).items()))))
        print("     H-H bonds in fold = %d ; Corollary-4 upper bound = %d ; optimal: %s"%(e,bound,e==bound))
    return s,chain

if __name__=="__main__":
    for m in range(1,8):
        s,chain=build_fold(m)
        if m<=3: print("     string:",s)
