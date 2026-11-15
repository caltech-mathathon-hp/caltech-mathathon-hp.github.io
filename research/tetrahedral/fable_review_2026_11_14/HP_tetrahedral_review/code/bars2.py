# How do the straight bars (t1/t2 zigzags) of Oct(m) meet the 12 edge zigzags?
import sys, itertools
from collections import Counter
from geom import *
m=int(sys.argv[1])
G=Geo(m); S=G.S
alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
E=set(v for e in alledges for v in e)
t1,t2=T[0],T[1]
def step(v,fwd):
    A=(sum(v)%4==0)
    if fwd: return tuple(v[i]+t1[i] for i in range(3)) if A else tuple(v[i]-t2[i] for i in range(3))
    else:   return tuple(v[i]+t2[i] for i in range(3)) if A else tuple(v[i]-t1[i] for i in range(3))
seen=set(); bars=[]
for v in sorted(S):
    if v in seen: continue
    b=[v]
    while step(b[-1],True) in S: b.append(step(b[-1],True))
    while step(b[0],False) in S: b.insert(0,step(b[0],False))
    bars.append(b); seen|=set(b)
print("m=%d bars: %d ; lengths %s"%(m,len(bars),dict(sorted(Counter(len(b) for b in bars).items()))))
pat=Counter()
bad=0
for b in bars:
    s=''.join('E' if v in E else ('s' if G.dang[v] else '.') for v in b)
    # compress interior
    key=(s[:3],s[-3:],'allE' if set(s)=={'E'} else ('E inside' if 'E' in s[3:-3] else ''))
    pat[key]+=1
for k,v in sorted(pat.items(),key=lambda x:-x[1]): print("  ends %s ... %s  %s : %d bars"%(k[0],k[1],k[2],v))
# after removing E: pieces and their end types
pieces=Counter()
for b in bars:
    cur=[]
    for v in b+[None]:
        if v is None or v in E:
            if cur:
                e0='s' if G.dang[cur[0]] else 'i'; e1='s' if G.dang[cur[-1]] else 'i'
                pieces[(e0+e1) if len(cur)>1 else ('single-'+e0)]+=1
            cur=[]
        else: cur.append(v)
print("pieces of bars after deleting edge sites, by end type (s = surface site with a free bond, i = interior):",dict(pieces))
