# Brute-force check of the tether pinning lemma on Oct(m).
import sys, itertools
from geom import *
m=int(sys.argv[1]) if len(sys.argv)>1 else 9
G=Geo(m,margin=8); S=G.S
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
e1=G.edge(Va,Vb); e2=G.edge(Vc,Vb); e3=G.edge(Va,Vc)
L=len(e1)
frame=set(e1)|set(e2)                     # all sites of the two framed edges (incl. Va,Vb,Vc)
# surface bond graph
surf=set(G.surf)
bonded={v:[w for w in nbrs(v) if w in surf] for v in surf}
# T-adjacency (PPP): same face, second neighbours, i.e. dangling sites at distance 2 through an outside site
def ppp_partners(v):
    res=set()
    for d in G.dang[v]:
        for x in nbrs(d):
            if x in S: continue
            for d2 in nbrs(x):
                if d2!=d and d2 in G.owner: res.add((G.owner[d2],d,d2))
    return res
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MIN='B' if sum(1 for v in S if sub(v)=='B')<len(S)/2 else 'A'
# all placements of HH PPP HH on free bonded pairs, entry w1 on the minority sublattice
free=[v for v in surf if v not in frame and bonded[v]]
place=[]
for w1 in free:
    if sub(w1)!=MIN: continue
    for w2 in bonded[w1]:
        if w2 in frame: continue
        for (w3,dd2,dd3) in ppp_partners(w2):
            if w3 in frame or w3 in (w1,w2): continue
            for w4 in bonded[w3]:
                if w4 in frame or w4 in (w1,w2,w3): continue
                for d1 in G.dang[w1]:
                    if d1==dd2: continue
                    for d4 in G.dang[w4]:
                        if d4==dd3: continue
                        place.append((w1,w2,w3,w4,d1,d4))
print("m=%d  #placements of the separator HH PPP HH on free bonded pairs: %d"%(m,len(place)))
idx3={z:i for i,z in enumerate(e3)}
def desc(w):
    return "e3[%d]"%idx3[w] if w in idx3 else str(w)
def test(P1,P2,g,gp):
    d1=[G.out_dist(G.dang[e1[2*s+1]][0]) for s in P1]          # e1 b-ports
    d2=[G.out_dist(G.dang[e2[2*s]][0]) for s in P2]            # e2 a-ports (index from Vc)
    ok=[]
    for (w1,w2,w3,w4,dd1,dd4) in place:
        if not any(dd1 in d and d[dd1]<=g-1 and (g-1-d[dd1])%2==0 for d in d1): continue
        if not any(dd4 in d and d[dd4]<=gp-1 and (gp-1-d[dd4])%2==0 for d in d2): continue
        ok.append((w1,w2,w3,w4))
    return ok
P1=list(range(0,3)); P2=list(range(1,4))
print("e1 b-ports at s in",P1,"; e2 a-ports at s in",P2,"; e3 has b_t for t=0..%d"%(m-2))
for G1 in range(2,m-4):
    G2=m-2-G1
    g=2*G1+1; gp=2*G2+2
    ok=test(P1,P2,g,gp)
    out=[]
    for o in ok:
        used=set(o)
        iso=[v for v in free if v not in used and all((w in used or w in frame) for w in bonded[v])]
        out.append((tuple(desc(w) for w in o),'ISOLATES %d site(s)'%len(iso) if iso else 'clean'))
    print(" G1=%d G2=%d (tethers P^%d, P^%d):"%(G1,G2,g,gp))
    for x in out: print("      ",x)
