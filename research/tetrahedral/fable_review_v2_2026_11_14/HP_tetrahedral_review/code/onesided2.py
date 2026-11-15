# One-sided problem: partitions of [0,x]; value = sum over interior breakpoints a of min(a, l'*l).  A[x][l] = best value with last interval l.
# Which last intervals are optimal?  (input for the hand proof of Claim U: facts F2, F3)
import math, sys
N=int(sys.argv[1])
F=[0]*(N+2)
for y in range(N+1): F[y+1]=F[y]+math.isqrt(y)
A=[None]*(N+1)
for x in range(1,N+1):
    row={x:0}
    for l in range(1,x):
        a=x-l; best=-1
        for lp,val in A[a].items():
            v=val+min(a,lp*l)
            if v>best: best=v
        row[l]=best
    A[x]=row
ok=all(max(A[x].values())==F[x] for x in range(1,N+1))
print("A(x) = F(x) for all x <= %d: %s"%(N,ok))
# F3: at x = m^2 the optimal last intervals ; F2: at x = m^2+v (1<=v<=m-1) the optimal last intervals
f2=f3=True
for m in range(2,math.isqrt(N)+1):
    x=m*m
    opt=sorted(l for l,v in A[x].items() if v==F[x])
    f3&=(max(opt)==m)
    line="m=%2d: optimal last intervals at x=m^2: %s"%(m,opt)
    bad=[]
    for v in range(1,m):
        if x+v>N: break
        o=sorted(l for l,val in A[x+v].items() if val==F[x+v])
        if o!=[v]: bad.append((v,o))
    f2&=(not bad)
    if m<=9: print(line+" ; at x=m^2+v (1<=v<=m-1) the only optimal last interval is v: %s"%(not bad))
print("F3 (largest optimal last interval at m^2 is m): %s ; F2 (at m^2+v the last breakpoint is m^2): %s"%(f3,f2))
# general pattern: optimal last intervals for all x
import collections
pat=collections.Counter()
for x in range(2,N+1):
    s=math.isqrt(x); r=x-s*s
    opt=tuple(sorted(l for l,v in A[x].items() if v==F[x]))
    pat[(("r=0" if r==0 else "0<r<s" if r<s else "r=s" if r==s else "s<r<=2s"),)]+=0
print("examples: x, s=floor(sqrt x), r=x-s^2, optimal last intervals")
for x in list(range(30,52)):
    s=math.isqrt(x); print("   x=%d s=%d r=%d : %s"%(x,s,x-s*s,sorted(l for l,v in A[x].items() if v==F[x])))
