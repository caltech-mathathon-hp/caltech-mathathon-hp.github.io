import sys, itertools, time
from collections import deque
from geom import *
from bulk import bulk_cover
m=int(sys.argv[1]) if len(sys.argv)>1 else 12
G=Geo(m,margin=3); S=G.S
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MAJ='A' if sum(1 for v in S if sub(v)=='A')>len(S)/2 else 'B'
is_maj=lambda v: sub(v)==MAJ
E=set()
for V,W in itertools.combinations(G.vertices,2):
    e=G.edge(V,W)
    if e: E|=set(e)
X=S-E
elig=set(v for v in X if is_maj(v) and G.dang[v])
nP=sum(1 for v in X if is_maj(v))-sum(1 for v in X if not is_maj(v))
print("m",m,"|X|",len(X),"imbalance (number of odd Maj-Maj paths needed)",nP,"eligible ends",len(elig))
t=time.time()
paths=bulk_cover(X,is_maj,elig,nP,seed=1)
print("time %.1fs"%(time.time()-t), "paths:",None if paths is None else sorted(len(p) for p in paths))
