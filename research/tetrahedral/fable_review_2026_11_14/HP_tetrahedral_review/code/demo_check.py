import sys
from collections import deque
from geom import *
m=int(sys.argv[1]) if len(sys.argv)>1 else 20
G=Geo(m,margin=3); S=G.S
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc)
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MAJ='A' if sum(1 for v in S if sub(v)=='A')>len(S)/2 else 'B'
# all edge sites
import itertools
edges=[]
for V,W in itertools.combinations(G.vertices,2):
    e=G.edge(V,W)
    if e: edges.append(e)
E=set(v for e in edges for v in e)
print("m",m,"|S|",len(S),"edges",len(edges),"edge sites",len(E))
# stuck corner check
Ub=e1[-2]; assert Ub==e2[1]
print("corner U_b neighbours in S:",[ ('edge' if w in E else 'inner') for w in nbrs(Ub) if w in S])
def sp(a,b,forbid):
    prev={a:None}; dq=deque([a])
    while dq:
        v=dq.popleft()
        if v==b: break
        for w in nbrs(v):
            if w in S and w not in prev and (w==b or w not in forbid):
                prev[w]=v; dq.append(w)
    if b not in prev: return None
    p=[b]
    while prev[p[-1]] is not None: p.append(prev[p[-1]])
    return p[::-1]
def bsite(e,s): return e[2*s+1]
for (lab,e,pairs) in (("e1",e1,[(4,6),(10,12)]),("e2 (from Vc)",e2[::-1],[(4,7),(11,14)])):
    for (s,t) in pairs:
        p=sp(bsite(e,s),bsite(e,t),E)
        print(lab,"ports",s,t,"shortest staple (sites):",len(p),"sublattices:","".join('M' if sub(v)==MAJ else 'm' for v in p))
    # cross-pair reach
    p=sp(bsite(e,pairs[0][1]),bsite(e,pairs[1][0]),E)
    print("   between different pairs (",pairs[0][1],pairs[1][0],"):",len(p),"sites")
# 7-site reach from an e2 port pair at distance 3?
p=sp(bsite(e2[::-1],4),bsite(e2[::-1],7),E); print("e2 pair at distance 3 needs",len(p),"sites (a 7-staple cannot do it:",len(p)>7,")")
# distance from ports to any track b-site
tr=[e3[i] for i in range(3,len(e3)-2,2)]
best=min(len(sp(bsite(e1,4),t,E)) for t in tr)
print("min staple length from e1 port b_4 to any interior track b-site:",best,"sites")
