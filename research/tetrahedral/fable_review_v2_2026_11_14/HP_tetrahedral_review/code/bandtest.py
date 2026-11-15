import sys
from collections import deque
from geom import *
m=int(sys.argv[1]); HMAX=int(sys.argv[2])
G=Geo(m,margin=400); S=G.S
dS={}; dq=deque()
for v in S:
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=1; dq.append(w)
while dq:
    v=dq.popleft()
    if dS[v]>=HMAX: continue
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=dS[v]+1; dq.append(w)
lev={}
for v,d in dS.items(): lev.setdefault(d,[]).append(v)
for h in range(1,HMAX-1):
    band=set(lev[h])|set(lev[h+1]); seen=set(); comps=[]
    for v in band:
        if v in seen: continue
        c=1; seen.add(v); dq=deque([v])
        while dq:
            x=dq.popleft()
            for w in nbrs(x):
                if w in band and w not in seen: seen.add(w); dq.append(w); c+=1
        comps.append(c)
    comps.sort(reverse=True)
    print("h=%2d band size %6d components %5d largest %s"%(h,len(band),len(comps),comps[:4]))
