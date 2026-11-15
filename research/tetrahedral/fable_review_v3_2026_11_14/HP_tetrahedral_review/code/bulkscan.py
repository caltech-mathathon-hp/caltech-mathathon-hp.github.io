# Bulk Lemma, evidence: X_m = Oct(m) minus the 12 edge zigzags; path cover with surface ends (all paths odd, Maj ends), by max-flow + flips.
import sys, itertools, time
from geom import *
from bulk import bulk_cover
for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
    t0=time.time()
    G=Geo(m); S=G.S; N=len(S)
    sub=lambda v:'A' if sum(v)%4==0 else 'B'
    MAJ='A' if sum(1 for v in S if sub(v)=='A')>N/2 else 'B'
    is_maj=lambda v: sub(v)==MAJ
    alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
    E=set(v for e in alledges for v in e)
    X=S-E
    elig=set(v for v in X if is_maj(v) and G.dang[v])
    nP=sum(1 for v in X if is_maj(v))-sum(1 for v in X if not is_maj(v))
    try:
        paths=bulk_cover(X,is_maj,elig,nP,seed=1,verbose=False)
        ok=paths is not None and sum(len(p) for p in paths)==len(X) and all(len(p)>=3 and p[0] in elig and p[-1] in elig for p in paths) \
           and all(p[i+1] in nbrs(p[i]) for p in paths for i in range(len(p)-1)) and len(set(v for p in paths for v in p))==len(X)
        print("m=%2d |X|=%6d runs=%2d (m-6=%d) cover valid: %s  min/max length %d/%d  %.0fs"%(m,len(X),len(paths),m-6,ok,min(map(len,paths)),max(map(len,paths)),time.time()-t0),flush=True)
    except Exception as ex:
        print("m=%2d FAILED: %r"%(m,ex),flush=True)
