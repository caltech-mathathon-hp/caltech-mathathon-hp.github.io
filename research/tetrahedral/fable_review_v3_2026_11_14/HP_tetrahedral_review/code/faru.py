"""Checks for the written proof of the Far-field Lemma (proof document, section 8.5):
   (1) an avenue A(q,l,a0) = {quadrant q, rho in {l,l+2}, alpha in {a0,a0+2}} is a path with exactly one site for each X;
   (2) the length-adjusting detour: from s_a backwards along A* to a site v0 (alpha=a0+2, eps=+1), hop to A** (strip a0+4),
       forwards along A** , hop back to A* at the first such site v1 beyond s_a, on to s_b:
       a simple path with  (X(s_b)-X(s_a)) + 2 + 2 (X(s_a)-X(v0))  bonds;  the extras 4,6,8,... all occur."""
from diamond import *
Yf=lambda v: v[1]; Zf=lambda v: v[2]-1
rho=lambda v: abs(Yf(v))+abs(Zf(v)); alpha=lambda v: abs(Yf(v))-abs(Zf(v))
sg=lambda t:(t>0)-(t<0)
def avenue(q,l,a0,xlo,xhi):
    out={}
    for x in range(xlo,xhi+1):
        c=[]
        for r in (l,l+2):
            for a in (a0,a0+2):
                v=(x,q[0]*(r+a)//2,q[1]*(r-a)//2+1)
                if is_site(v): c.append(v)
        assert len(c)==1,(x,c); out[x]=c[0]
    for x in range(xlo,xhi): assert out[x+1] in nbrs(out[x])
    return out
def eps(v,q): return (1 if sum(v)%4==0 else -1)*q[0]*q[1]
ok=0
for q in ((1,1),(1,-1),(-1,1),(-1,-1)):
    for l in (41,43):
        for a0 in (5,7,-9):
            A=avenue(q,l,a0,-60,60); B=avenue(q,l,a0+4,-60,60); ok+=1
            typ=[x for x in range(-50,50) if alpha(A[x])==a0+2 and eps(A[x],q)==1]
            assert all(b-a==4 for a,b in zip(typ,typ[1:]))
            extras=set()
            for xa in range(0,4):
                sa=A[xa]; xb=xa+23; sb=A[xb]
                for x0 in [t for t in typ if -40<=t<xa]:
                    v0=A[x0]; hop=[w for w in nbrs(v0) if rho(w)==rho(v0) and alpha(w)==a0+4]
                    assert len(hop)==1 and hop[0]==B[x0-1]
                    x1=min(t for t in typ if t>xa)
                    assert A[x1] in nbrs(B[x1-1])
                    path=[A[x] for x in range(xa,x0-1,-1)]+[B[x] for x in range(x0-1,x1)]+[A[x] for x in range(x1,xb+1)]
                    assert len(set(path))==len(path) and all(path[i+1] in nbrs(path[i]) for i in range(len(path)-1))
                    bonds=len(path)-1
                    assert bonds==(xb-xa)+2+2*(xa-x0)
                    extras.add(bonds-(xb-xa))
            assert set(range(4,60,2))<=extras,sorted(extras)[:8]
print("avenues are paths with one site per X (%d cases); detour paths are simple with the predicted lengths; all even extras >= 4 occur"%ok)
