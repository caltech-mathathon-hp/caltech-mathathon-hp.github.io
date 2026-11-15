# Is the repair pattern periodic along each edge (away from the vertices)?
import sys
from collections import defaultdict
import bent4
from geom import *
for m in [int(x) for x in sys.argv[1:]]:
    paths,msg,info=bent4.cover(m); G,E,D,alledges=bent4.cover.last
    res=[]
    for e in alledges:
        idx={v:i for i,v in enumerate(e)}
        u=tuple(e[4][i]-e[2][i] for i in range(3))
        # assign each modified bond to the nearest zigzag index of this edge (only if within 5 bonds)
        dist={v:(0,i) for v,i in idx.items()}; fr=list(e)
        for step in range(1,6):
            nf=[]
            for x in fr:
                for w in nbrs(x):
                    if w in G.S and w not in dist: dist[w]=(step,dist[x][1]); nf.append(w)
            fr=nf
        grp=defaultdict(set)
        for (sg,a,b) in D:
            if a in dist and b in dist: grp[min(dist[a][1],dist[b][1])].add((sg,a,b))
        sh=lambda bond,k: (bond[0],)+tuple(sorted((tuple(bond[1][i]+k*u[i] for i in range(3)),tuple(bond[2][i]+k*u[i] for i in range(3)))))
        def periodic(per,margin):
            allb=set().union(*[grp[i] for i in grp if margin<=i<=2*m-2-margin]) if grp else set()
            bad=0
            for b in allb:
                i=min(dist[b[1]][1],dist[b[2]][1])
                if i+2*per<=2*m-2-margin and sh(b,per) not in D: bad+=1
            return bad,len(allb)
        p1=periodic(1,12); p2=periodic(2,12)
        res.append((len([1 for i in grp]),p1,p2))
    print("m=%d (%s): per edge [#modified bonds in the middle part, violations of period 1 | period 2]:"%(m,msg))
    print("   "+"  ".join("%d:%d|%d"%(p1[1],p1[0],p2[0]) for _,p1,p2 in res))
