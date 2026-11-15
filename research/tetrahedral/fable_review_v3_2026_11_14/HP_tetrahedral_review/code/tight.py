# Tight cases of (*): (a-t)+min(a,l*t) = W(a-t,a)+W(a,a+l), t>=s+1.  Print as (s,r,t,l) with a=s^2+r.
import math, sys
from collections import defaultdict
isq=math.isqrt
A=int(sys.argv[1])
pre=[0]*(2*A+10)
for y in range(2*A+8): pre[y+1]=pre[y]+isq(y)
W=lambda u,v: pre[v]-pre[u]
tight=defaultdict(list)
for a in range(1,A):
    s=isq(a); r=a-s*s
    for t in range(s+1,a+1):
        for l in range(1,a+2):
            if (a-t)+min(a,l*t)==W(a-t,a)+W(a,a+l): tight[(s,r)].append((t,l))
for (s,r),v in sorted(tight.items()):
    if s<=7: print("s=%d r=%2d (a=%3d): (t,l) = %s"%(s,r,s*s+r,v))
# conjecture test
bad=0
for (s,r),v in tight.items():
    for (t,l) in v:
        ok=False
        if r==s and t==s+1 and l==s: ok=True              # a=s^2+s, t=s+1, l=s
        if r>=s+1 and t==s+1 and l in (s,) : ok=True
        if not ok: bad+=1
print("tight triples not of the conjectured form:",bad)
