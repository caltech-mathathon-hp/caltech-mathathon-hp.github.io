import sys
from geom import *
m=int(sys.argv[1]) if len(sys.argv)>1 else 8
G=Geo(m,margin=8)
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
e1=G.edge(Va,Vb); e2=G.edge(Vc,Vb); e3=G.edge(Va,Vc)   # e1,e3 indexed from Va ; e2 indexed from Vc
L=len(e1)
print("m",m,"edge length (sites)",L,"Va,Vb,Vc",Va,Vb,Vc,"normal",tri[4])
assert e1[1]==e3[1]            # shared corner near Va
def dsite(z):
    ds=G.dang[z]; assert len(ds)==1; return ds[0]
# check faces of dangling sites
print("faces: e1 b:",set(G.face_of[dsite(e1[i])] for i in range(1,L-1,2))," e1 a:",set(G.face_of[dsite(e1[i])] for i in range(2,L-1,2)))
print("       e2 b:",set(G.face_of[dsite(e2[i])] for i in range(1,L-1,2))," e2 a:",set(G.face_of[dsite(e2[i])] for i in range(2,L-1,2)))
print("       e3 b:",set(G.face_of[dsite(e3[i])] for i in range(1,L-1,2))," e3 a:",set(G.face_of[dsite(e3[i])] for i in range(2,L-1,2)))
# D1: from b-sites on e1 (index i odd) to all sites of e3
print("\nD1[i on e1 (b-sites)][j on e3]: outside distance between dangling sites  (rows i=1,3,5..; cols j=1..L-2)")
for i in range(1,L-1,2):
    dist=G.out_dist(dsite(e1[i]))
    print("i=%2d:"%i," ".join("%2d"%dist.get(dsite(e3[j]),-1) for j in range(1,L-1)))
print("\nD2[i on e2 (a-sites), index from Vc][j on e3, index from Va]")
for i in range(2,L-1,2):
    dist=G.out_dist(dsite(e2[i]))
    print("i=%2d:"%i," ".join("%2d"%dist.get(dsite(e3[j]),-1) for j in range(1,L-1)))
print("\nD3[i on e2 (b-sites), index from Vc][j on e3, index from Va]")
for i in range(1,L-1,2):
    dist=G.out_dist(dsite(e2[i]))
    print("i=%2d:"%i," ".join("%2d"%dist.get(dsite(e3[j]),-1) for j in range(1,L-1)))
