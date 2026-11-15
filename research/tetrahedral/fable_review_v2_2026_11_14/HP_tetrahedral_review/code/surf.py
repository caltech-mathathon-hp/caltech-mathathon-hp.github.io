from oct import *
from collections import Counter, defaultdict
import sys
m=int(sys.argv[1]) if len(sys.argv)>1 else 5
S=octa(m)
# centre of octahedron
cx=sum(v[0] for v in S)/len(S); cy=sum(v[1] for v in S)/len(S); cz=sum(v[2] for v in S)/len(S)
print("centre",cx,cy,cz)
dang={v:[w for w in nbrs(v) if w not in S] for v in S}
surf=[v for v in S if dang[v]]
def face_of_site(v,w):
    # direction of dangling bond w-v is +-t_k : identifies the face normal
    d=(w[0]-v[0],w[1]-v[1],w[2]-v[2]); return d
faces=defaultdict(list)
for v in surf:
    for w in dang[v]: faces[face_of_site(v,w)].append(v)
print("faces (normal: #dangling):",{k:len(v) for k,v in faces.items()})
# adjacency between dangling sites
D={}   # dangling site -> atom
for v in surf:
    for w in dang[v]:
        assert w not in D; D[w]=v
adjpairs=[]
for w in D:
    for w2 in nbrs(w):
        if w2 in D and w<w2: adjpairs.append((w,w2))
print("#pairs of adjacent dangling sites (PP links):",len(adjpairs))
c=Counter()
for w,w2 in adjpairs:
    u,u2=D[w],D[w2]
    f1=face_of_site(u,w); f2=face_of_site(u2,w2)
    # lattice distance between u,u2 inside S? adjacency
    c[(f1,f2, 'bonded' if u2 in nbrs(u) else 'notbonded')]+=1
for k,v in sorted(c.items()): print("   ",k,v)
# bonded pairs of surface atoms
bp=[(u,w) for u in surf for w in nbrs(u) if w in S and dang[w] and u<w]
print("#bonded pairs of surface atoms (dimer spots):",len(bp))
c=Counter()
for u,w in bp:
    c[(len(dang[u]),len(dang[w]))]+=1
print("   by (#dangling,#dangling):",dict(c))
# distance-2 pairs of dangling sites (PPP link): common outside neighbour x not in S ; record whether x is itself a dangling site
c=Counter(); 
for w in D:
    for x in nbrs(w):
        if x in S: continue
        for w2 in nbrs(x):
            if w2!=w and w2 in D and w<w2:
                u,u2=D[w],D[w2]
                f1=face_of_site(u,w); f2=face_of_site(u2,w2)
                same = (f1==f2)
                c[('sameface' if same else 'difffaces', 'x is dangling site' if x in D else 'x free')]+=1
print("PPP links (dangling sites at distance 2):",dict(c))
