# all connected site-sets of the diamond lattice up to size 10 (up to translation): max number of bonds and #maximisers
from diamond import *
def canon(S):
    mn=min(S)
    # translate by an FCC vector so that the minimal site goes to (0,0,0) [A] or (1,1,1)... keep sublattice
    if sum(mn)%4==0: off=mn
    else: off=(mn[0]-1,mn[1]-1,mn[2]-1)
    return frozenset((v[0]-off[0],v[1]-off[1],v[2]-off[2]) for v in S)
level={canon([(0,0,0)]),canon([(1,1,1)])}
for n in range(1,11):
    best=max(edges(S) for S in level)
    mx=[S for S in level if edges(S)==best]
    print("n=%d  #animals=%d  max bonds=%d  min boundary=%d  #maximisers(up to translation)=%d"%(n,len(level),best,4*n-2*best,len(mx)))
    if n==10:
        for S in mx:
            deg=sorted(sum(1 for w in nbrs(v) if w in S) for v in S)
            print("   maximiser degree sequence:",deg)
        break
    nxt=set()
    for S in level:
        for v in S:
            for w in nbrs(v):
                if w not in S:
                    nxt.add(canon(list(S)+[w]))
    level=nxt
