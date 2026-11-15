# last parts of optimal one-sided compositions; checks F2, F3, P(s), Q(s) and counts optimal compositions
import math, sys
X=int(sys.argv[1]); isq=math.isqrt
F=[0]*(X+2)
for y in range(X+1): F[y+1]=F[y]+isq(y)
NEG=-10**9
A=[[NEG]*(X+1) for _ in range(X+1)]   # A[x][l] best U for compositions of x with last part l
cnt=[[0]*(X+1) for _ in range(X+1)]   # number of optimal (=F(x)) compositions with last part l
for x in range(1,X+1):
    A[x][x]=0
    if F[x]==0: cnt[x][x]=1
    for l in range(1,x):
        a=x-l; best=NEG
        for lp in range(1,a+1):
            if A[a][lp]==NEG: continue
            v=A[a][lp]+min(a,lp*l)
            if v>best: best=v
        A[x][l]=best
# count optimal compositions: need full-count DP over (x,l) with value tracking
from collections import defaultdict
ways=[[defaultdict(int) for _ in range(X+1)] for _ in range(X+1)] if X<=120 else None
if ways:
    for x in range(1,X+1):
        ways[x][x][0]=1
        for l in range(1,x):
            a=x-l
            for lp in range(1,a+1):
                g=min(a,lp*l)
                for val,c in ways[a][lp].items():
                    # prune: keep only values that can still matter (within F slack) -- keep all for small X
                    ways[x][l][val+g]+=c
bad=0
for x in range(1,X+1):
    assert max(A[x][1:x+1])==F[x], x
    s=isq(x); r=x-s*s
    lam=[l for l in range(1,x+1) if A[x][l]==F[x]]
    if r==0:
        if max(lam)>s: bad+=1
    elif r<=s-1:
        if s in lam and r!=s: bad+=1
    if x<=40 or r in (0,s): print(x,(s,r),lam, [ways[x][l][F[x]] for l in lam] if ways else '')
print("violations of F2/F3:",bad)
