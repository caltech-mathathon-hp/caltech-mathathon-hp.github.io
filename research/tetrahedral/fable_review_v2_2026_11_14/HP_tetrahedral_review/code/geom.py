"""Geometry of Oct(m): vertices, faces, edges (zigzags), outside distances."""
from collections import deque, defaultdict
from diamond import *
from oct import octa

class Geo:
    def __init__(self,m,margin=10):
        self.m=m; S=self.S=octa(m)
        self.dang={v:[w for w in nbrs(v) if w not in S] for v in S}
        self.surf=[v for v in S if self.dang[v]]
        self.vertices=sorted(v for v in S if len(self.dang[v])==2)
        self.face_of={}                      # dangling site -> normal (t-vector or its negative)
        self.owner={}                        # dangling site -> surface atom
        for v in self.surf:
            for w in self.dang[v]:
                self.owner[w]=v; self.face_of[w]=(w[0]-v[0],w[1]-v[1],w[2]-v[2])
        cnt=defaultdict(int)
        for w,n in self.face_of.items(): cnt[n]+=1
        self.big=[n for n,c in cnt.items() if c==m*(m+1)//2]; self.small=[n for n,c in cnt.items() if c==m*(m-1)//2]
        lo=min(min(v) for v in S)-margin; hi=max(max(v) for v in S)+margin
        self.lo,self.hi=lo,hi
    def inbox(self,v): return all(self.lo<=c<=self.hi for c in v)
    def edge(self,V,W):
        """zigzag from vertex V to adjacent vertex W (list of sites) or None"""
        m=self.m; d=tuple((W[i]-V[i]) for i in range(3))
        for a in range(4):
            for b in range(4):
                if a==b: continue
                u=tuple(T[a][i]-T[b][i] for i in range(3))
                if tuple((m-1)*c for c in u)==d:
                    path=[V]; cur=V
                    for j in range(m-1):
                        cur=tuple(cur[i]+T[a][i] for i in range(3)); path.append(cur)
                        cur=tuple(cur[i]-T[b][i] for i in range(3)); path.append(cur)
                    assert all(p in self.S for p in path)
                    return path
        return None
    def out_dist(self,src,blocked=()):
        """BFS distances in the complement of S (inside the box) from site src"""
        S=self.S; dist={src:0}; dq=deque([src]); blocked=set(blocked)
        while dq:
            v=dq.popleft()
            for w in nbrs(v):
                if w in dist or w in S or w in blocked or not self.inbox(w): continue
                dist[w]=dist[v]+1; dq.append(w)
        return dist
    def small_face_triples(self):
        """triples of mutually adjacent vertices spanning a small face"""
        res=[]
        Vs=self.vertices
        for i in range(6):
            for j in range(i+1,6):
                for k in range(j+1,6):
                    A,B,C=Vs[i],Vs[j],Vs[k]
                    if self.edge(A,B) and self.edge(B,C) and self.edge(A,C):
                        # face type: the b-sites of the edge AB have their dangling bond on this face iff small
                        cen=[sum(x[t] for x in (A,B,C))/3 for t in range(3)]
                        ctr=[sum(v[t] for v in self.S)/len(self.S) for t in range(3)]
                        n=tuple((1 if cen[t]>ctr[t] else -1) for t in range(3))
                        res.append((A,B,C,'small' if n in self.small else 'big',n))
        return res

if __name__=="__main__":
    import sys
    m=int(sys.argv[1]) if len(sys.argv)>1 else 8
    G=Geo(m)
    print("vertices:",G.vertices)
    tr=G.small_face_triples()
    for t in tr: print(t)
