# Pinning lemma, fuller test: all e1-side Min ports allowed in a range + the forced corner port U_b;
# both possible geometries of the second frame; any m.
import sys
from geom import *
m=int(sys.argv[1]) if len(sys.argv)>1 else 10
sig=int(sys.argv[2]) if len(sys.argv)>2 else 3            # ports live within sig steps of the far ends
G=Geo(m,margin=8); S=G.S
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
surf=set(G.surf); bonded={v:[w for w in nbrs(v) if w in surf] for v in surf}
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MIN='B' if sum(1 for v in S if sub(v)=='B')<len(S)/2 else 'A'
def ppp_partners(v):
    res=set()
    for d in G.dang[v]:
        for x in nbrs(d):
            if x in S: continue
            for d2 in nbrs(x):
                if d2!=d and d2 in G.owner: res.add((G.owner[d2],d,d2))
    return res
def run(W,label):
    e1=G.edge(Va,Vb); e2=G.edge(W,Vb); e3=G.edge(Va,Vc)
    frame=set(e1)|set(e2)
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
    idx3={z:i for i,z in enumerate(e3)}
    Lz=len(e1)
    # entry anchors: e1 b-sites with s<=sig (index 2s+1 from Va), plus corner U_b = e1[Lz-2]
    ent=[e1[2*s+1] for s in range(0,sig+1)]+[e1[Lz-2]]
    # exit anchors: e2 a-sites with s in 1..sig (index 2s from W)
    ext=[e2[2*s] for s in range(1,sig+1)]
    dE=[G.out_dist(G.dang[q][0]) for q in ent]; dX=[G.out_dist(G.dang[q][0]) for q in ext]
    print("== %s: second frame towards %s ; entry anchors %d (incl. corner U_b), exit anchors %d ; placements %d"%(label,W,len(ent),len(ext),len(place)))
    allok=True
    for G1 in range(sig+1,m-2-sig):
        G2=m-2-G1; g=2*G1+1; gp=2*G2+2
        ok=[]
        for (w1,w2,w3,w4,dd1,dd4) in place:
            if not any(dd1 in d and d[dd1]<=g-1 and (g-1-d[dd1])%2==0 for d in dE): continue
            if not any(dd4 in d and d[dd4]<=gp-1 and (gp-1-d[dd4])%2==0 for d in dX): continue
            used={w1,w2,w3,w4}
            iso=[v for v in free if v not in used and all((w in used or w in frame) for w in bonded[v])]
            if iso: continue
            ok.append(tuple(sorted(idx3[w] if w in idx3 else -1 for w in (w1,w2,w3,w4))))
        exp={(2*G1,2*G1+1,2*G1+2,2*G1+3),(2*G1+1,2*G1+2,2*G1+3,2*G1+4)}
        good=(set(ok)==exp)
        allok&=good or (label!='intended' and not ok)
        print("   G1=%2d G2=%2d: clean feasible placements (indices on e3; -1 = elsewhere): %s %s"%(G1,G2,sorted(set(ok)),"" if label!='intended' else ("OK" if good else "UNEXPECTED")))
    return allok
others=[v for v in G.vertices if v not in (Va,Vb,Vc) and G.edge(Vb,v)]
r1=run(Vc,'intended')
for W in others:
    run(W,'alternative')
print("intended geometry: pinned exactly as predicted for every separator position:",r1)
