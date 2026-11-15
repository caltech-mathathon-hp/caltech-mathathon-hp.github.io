import random
from diamond import *
random.seed(1)
worst=0;cnt=0
for trial in range(1500):
    n=random.randint(1,300)
    S={(0,0,0)}; fr=[(0,0,0)]
    while len(S)<n:
        v=random.choice(fr)
        free=[w for w in nbrs(v) if w not in S]
        if not free: fr.remove(v); continue
        w=random.choice(free); S.add(w); fr.append(w)
    b=boundary(S); bound=(4/3)*(b/4)**1.5
    assert len(S)<=bound+1e-9,(len(S),b)
    worst=max(worst,len(S)/bound); cnt+=1
print("Theorem 3 holds on",cnt,"random connected clusters; max |S|/bound =",round(worst,4))
