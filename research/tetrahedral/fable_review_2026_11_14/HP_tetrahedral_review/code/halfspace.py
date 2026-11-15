# Explicit half-space description of Oct(m): is Oct(m) = { v in D : s.(v-c) <= R_s(m) for the 8 sign vectors s } ?
import itertools
from geom import *
from oct import octa
rows=[]
for m in range(4,15):
    S=octa(m); c=(0,2*(m-1),0)
    signs=list(itertools.product((1,-1),repeat=3))
    Rs={s:max(sum(s[i]*(v[i]-c[i]) for i in range(3)) for v in S) for s in signs}
    lo=min(min(v) for v in S)-3; hi=max(max(v) for v in S)+3
    def is_site(v): return (v[0]-v[1])%2==0 and (v[1]-v[2])%2==0 and sum(v)%4 in (0,3)
    T=set()
    for x in range(lo,hi+1):
        for y in range(lo,hi+1):
            for z in range(lo+(y-lo)%2 if False else lo,hi+1):
                v=(x,y,z)
                if is_site(v) and all(sum(s[i]*(v[i]-c[i]) for i in range(3))<=Rs[s] for s in signs): T.add(v)
    big=sorted(set(Rs[s] for s in signs if s[0]*s[1]*s[2]==1)); small=sorted(set(Rs[s] for s in signs if s[0]*s[1]*s[2]==-1))
    rows.append((m,T==S,big,small))
    print("m=%2d: Oct(m) equals the half-space set: %s ; R for sign product +1: %s ; for sign product -1: %s ; (2m-2, 2m-3) = (%d, %d)"%(m,T==S,big,small,2*m-2,2*m-3))
