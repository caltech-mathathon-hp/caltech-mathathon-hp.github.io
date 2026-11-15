# Max advance of a P^k link along an edge direction; which pairs attain it.  (tautness of longer frame links)
import sys
from geom import *
m=int(sys.argv[1]) if len(sys.argv)>1 else 8
G=Geo(m,margin=10); S=G.S
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
e1=G.edge(Va,Vb); idx={z:i for i,z in enumerate(e1)}
u=tuple((Vb[i]-Va[i])//(m-1) for i in range(3))
pi=lambda v: sum(v[i]*u[i] for i in range(3))//4
p0=pi(Va)
surf=G.surf
# global: for every surface site v1 and each k, max advance
import collections
best=collections.defaultdict(lambda:-99); arg=collections.defaultdict(list)
KMAX=int(sys.argv[2]) if len(sys.argv)>2 else 9
for v1 in surf:
    for d1 in G.dang[v1]:
        dist={d1:0}; dq=collections.deque([d1])
        while dq:
            x=dq.popleft()
            if dist[x]>=KMAX-1: continue
            for w in nbrs(x):
                if w in S or w in dist: continue
                dist[w]=dist[x]+1; dq.append(w)
        for w,dd in dist.items():
            if w in G.owner and w!=d1:
                v2=G.owner[w]
                if v2==v1: continue
                for k in range(dd+1,KMAX+1,2):
                    a=pi(v2)-pi(v1)
                    if a>best[k]: best[k]=a; arg[k]=[]
                    if a==best[k]: arg[k].append((v1,v2,d1,w))
for k in range(2,KMAX+1):
    if best[k]==-99: print("k=%d: no pair"%k); continue
    onedge=sum(1 for (v1,v2,_,_) in arg[k] if v1 in idx and v2 in idx)
    print("k=%d: max advance %d ; maximising pairs %d, of which both on e1: %d"%(k,best[k],len(arg[k]),onedge))
    # where are the others?
    oth=[(v1,v2) for (v1,v2,_,_) in arg[k] if not(v1 in idx and v2 in idx)]
    # pairs starting on e1
    st=[(idx[v1],idx.get(v2,None),v2) for (v1,v2,_,_) in arg[k] if v1 in idx]
    print("    starting on e1 (index pairs):",sorted(set((a,b) for a,b,_ in st))[:14])
