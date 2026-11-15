import math, random
from diamond import *
# (1) inequality (*) used in the induction for the one-sided bound
def W(u,v): return sum(math.isqrt(y) for y in range(u,v))
pre=[0]
for y in range(0,5000): pre.append(pre[-1]+math.isqrt(y))
def Wf(u,v): return pre[v]-pre[u]
bad=0; eq=0
for a in range(1,700):
    q=math.isqrt(a)
    for lp in range(q+1,a+1):
        for l in range(1,a+2):
            lhs=(a-lp)+min(a,l*lp); rhs=Wf(a-lp,a)+Wf(a,a+l)
            if lhs>rhs: bad+=1
            if lhs==rhs: eq+=1
print("(*) violations for a<700:",bad," equality cases:",eq)

# (3) random test of Theorem 3: |S| <= (4/3)(|dS|/4)^(3/2)
random.seed(1)
worst=0
for trial in range(3000):
    n=random.randint(1,400)
    S={(0,0,0)}; fr=[(0,0,0)]
    mode=random.random()
    while len(S)<n:
        v=random.choice(fr) if mode<0.5 else fr[random.randrange(max(1,len(fr)//3))]
        w=random.choice(nbrs(v))
        if w not in S: S.add(w); fr.append(w)
    b=boundary(S); bound=(4/3)*(b/4)**1.5
    assert len(S)<=bound+1e-9,(len(S),b)
    worst=max(worst,len(S)/bound)
print("Theorem 3 holds on 3000 random clusters; max |S|/bound =",round(worst,4))
