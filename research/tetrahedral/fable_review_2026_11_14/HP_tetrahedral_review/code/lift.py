# Can tethers avoid the first hover bilayer over the small face F' (which is full of caps of bulk runs)?
# Outside distance between the dangling sites of b_s(e1) and b_t(e3) when all sites at distance < L from Oct(m) are forbidden,
# except the two end sites and their neighbours.  Compare with the free distance 2*max(s,t).
import sys
from collections import deque
from geom import *
m=int(sys.argv[1])
G=Geo(m); S=G.S
small=[t for t in G.small_face_triples() if t[3]=='small']
Va,Vb,Vc=small[0][0],small[0][1],small[0][2]
e1=G.edge(Va,Vb); e3=G.edge(Va,Vc); e2c=G.edge(Vb,Vc)[::-1]
dS={}; dq=deque()
for v in S:
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=1; dq.append(w)
while dq:
    v=dq.popleft()
    if dS[v]>=14: continue
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=dS[v]+1; dq.append(w)
def dist(src,dst,L):
    ok=lambda w: w in dS and (dS[w]>=L or w in near)
    near={src,dst}
    for a in (src,dst):
        fr=[a]
        for step in range(L-1):
            nf=[]
            for x in fr:
                for w in nbrs(x):
                    if w in dS and dS[w]==dS[x]+1 and w not in near: near.add(w); nf.append(w)
            fr=nf
    d={src:0}; q=deque([src])
    while q:
        v=q.popleft()
        if v==dst: return d[v]
        for w in nbrs(v):
            if w not in d and ok(w): d[w]=d[v]+1; q.append(w)
    return None
print("m=%d ; entries: free distance, distance avoiding levels 1-2, avoiding levels 1-4"%m)
for (s,t) in ((3,9),(3,10),(6,9),(6,14),(9,9),(9,12)):
    a=G.dang[e1[2*s+1]][0]; b=G.dang[e3[2*t+1]][0]
    print("  entry tether b_%d(e1) -> b_%d(e3): %s, %s, %s   (2*max = %d)"%(s,t,dist(a,b,1),dist(a,b,3),dist(a,b,5),2*max(s,t)))
for (s,t) in ((3,9),(8,9),(5,12)):
    a=G.dang[e2c[2*s+1]][0]; b=G.dang[e3[2*t+1]][0]
    print("  exit tether b'_%d(e2) -> b_%d(e3): %s, %s, %s   (2*max(s, m-2-t) = %d)"%(s,t,dist(a,b,1),dist(a,b,3),dist(a,b,5),2*max(s,m-2-t)))
