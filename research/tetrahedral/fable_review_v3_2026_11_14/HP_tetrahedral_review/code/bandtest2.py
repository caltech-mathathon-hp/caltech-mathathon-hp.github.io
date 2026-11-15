import sys, itertools
from collections import deque, Counter
from geom import *
m=int(sys.argv[1]); HMAX=int(sys.argv[2]); hs=[int(x) for x in sys.argv[3:]]
G=Geo(m,margin=400); S=G.S
ctr=[sum(v[t] for v in S)/len(S) for t in range(3)]
dS={}; dq=deque()
for v in S:
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=1; dq.append(w)
while dq:
    v=dq.popleft()
    if dS[v]>=HMAX: continue
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=dS[v]+1; dq.append(w)
signs=list(itertools.product((1,-1),repeat=3))
# face offsets
off={s:max(sum(s[i]*(v[i]-ctr[i]) for i in range(3)) for v in S) for s in signs}
def lab(v):
    val=[(sum(s[i]*(v[i]-ctr[i]) for i in range(3))-off[s],s) for s in signs]
    val.sort(reverse=True)
    return val[0][1], val[0][0]-val[1][0]
for h in hs:
    band=[v for v,d in dS.items() if d in (h,h+1)]; bs=set(band)
    L={v:lab(v)[0] for v in band}
    cross=Counter()
    for v in band:
        for w in nbrs(v):
            if w in bs and L[w]!=L[v] and v<w:
                cross[tuple(sorted((L[v],L[w])))]+=1
    print("h=%d: band %d sites; face-sheet sizes %s"%(h,len(band),sorted(Counter(L.values()).values())))
    print("   bonds between different face sheets: %d pairs of faces; counts %s"%(len(cross),sorted(cross.values())))
