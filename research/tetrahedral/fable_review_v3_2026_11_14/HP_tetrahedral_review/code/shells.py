"""Structure of the far field of the bent foliation: level sets rho = h, rungs between levels, shell connectivity.
   Coordinates: Y = y - cy (cy even), Z = z - 1; rho = |Y|+|Z|, alpha = |Y|-|Z|.  (cy plays no role here.)"""
import sys
from diamond import *
from collections import Counter, deque
Yf=lambda v: v[1]; Zf=lambda v: v[2]-1
rho=lambda v: abs(Yf(v))+abs(Zf(v))
def level_components(h,xlo,xhi):
    sites=[]
    for x in range(xlo,xhi+1):
        for Y in range(-h,h+1):
            for sZ in (1,-1):
                Zv=sZ*(h-abs(Y))
                if Zv==0 and sZ==-1: continue
                v=(x,Y,Zv+1)
                if is_site(v): sites.append(v)
    S=set(sites); seen=set(); comps=[]
    for v in sites:
        if v in seen: continue
        comp=[v]; seen.add(v); dq=deque([v])
        while dq:
            u=dq.popleft()
            for w in nbrs(u):
                if w in S and w not in seen and rho(w)==h: seen.add(w); comp.append(w); dq.append(w)
        comps.append(comp)
    return S,comps
for h in (9,11,13,21):
    S,comps=level_components(h,-12,12)
    inner=[c for c in comps if min(v[0] for v in c)>-12 and max(v[0] for v in c)<12]
    deg=Counter(sum(1 for w in nbrs(v) if w in S) for c in inner for v in c)
    sizes=Counter(len(c) for c in inner); xspan=Counter(max(v[0] for v in c)-min(v[0] for v in c) for c in inner)
    xs=sorted(set(min(v[0] for v in c) for c in inner))
    print("rho=%d: %d closed components away from the cut; sizes %s ; in-level degrees %s ; X-span %s ; min-X values %s"%(h,len(inner),dict(sizes),dict(deg),dict(xspan),xs))
    # rungs: each site of level h has how many neighbours at level h+2 / h-2
    up=Counter(sum(1 for w in nbrs(v) if rho(w)==h+2) for c in inner for v in c)
    dn=Counter(sum(1 for w in nbrs(v) if rho(w)==h-2) for c in inner for v in c)
    print("        neighbours at rho+2: %s ; at rho-2: %s"%(dict(up),dict(dn)))
print("--- tracing one level curve")
sg=lambda t:(t>0)-(t<0)
for h in (9,21):
    # start at a site with rho=h, Y>0,Z>0
    v=None
    for x0 in (0,1,2,3):
        for Y in range(2,h-2):
            c=(x0,Y,h-Y+1)
            if v is None and is_site(c): v=c
    path=[v]; prev=None; cur=v
    for step in range(12*h):
        nx=[w for w in nbrs(cur) if rho(w)==h and w!=prev]
        if step==0: nx=nx[:1]
        assert len(nx)==1,(len(nx),cur)
        prev,cur=cur,nx[0]; path.append(cur)
        if (sg(Yf(cur)),sg(Zf(cur)))==(sg(Yf(v)),sg(Zf(v))) and Yf(cur)==Yf(v) and Zf(cur)==Zf(v): break
    print("rho=%d: back at the same (Y,Z) after %d steps ; X changed by %d ; X range on the way %d..%d"%(h,len(path)-1,cur[0]-v[0],min(p[0] for p in path),max(p[0] for p in path)))
    # how many distinct level curves per period of X?
    quad=[(sg(Yf(p)),sg(Zf(p)),p[0]) for p in path]
    xs_by_quad={}
    for a,b,x in quad: xs_by_quad.setdefault((a,b),set()).add(x)
    print("        X values per quadrant:",{k:sorted(v) for k,v in xs_by_quad.items()})
