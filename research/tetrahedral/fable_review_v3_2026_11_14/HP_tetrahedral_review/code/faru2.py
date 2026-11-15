"""Audit and repair of step D of Lemma F (far field), proof document section 8.5.
   Everything is checked for a FIXED start site s_a (the old script faru.py pooled over four positions of s_a,
   which is exactly what hid the defect).
   A*  = A((+,+),u,a*), A** = A((+,+),u,a*+4).  s_a, s_b: sites of A* with rho=u, alpha=a*.
   gate = site g of A* with alpha = a*+2 ; sign eps(g) ; outer neighbour g+ = the site of A** with X = X(g)-eps(g).
   detour(g0,g1): A* from s_a back to g0, g0+, A** forward to g1+, g1, A* forward to s_b.
   Claims: (1) g+ is a lattice neighbour of g ; (2) the detour is a simple lattice path inside A* u A** ;
           (3) it has  E = 2 + 2(X(s_a)-X(g0)) + eps(g0) - eps(g1)  more sites than the direct piece ;
           (4) for fixed s_a, with g1 the first gate of either sign beyond s_a, E runs through every even number
               >= 2*delta exactly once, delta = 1 if eps(s_a)=+1 and 2 if eps(s_a)=-1 ;
           (5) OLD construction (only gates of sign +1): a single residue class modulo 8."""
import sys
from diamond import *
def run(cy):
    Yf=lambda v: v[1]-cy; Zf=lambda v: v[2]-1
    rho=lambda v: abs(Yf(v))+abs(Zf(v)); alpha=lambda v: abs(Yf(v))-abs(Zf(v))
    eps=lambda v: (1 if sum(v)%4==0 else -1)                 # quadrant (+,+): sigma*tau = +1
    def avenue(l,a0,xlo,xhi):
        out={}
        for x in range(xlo,xhi+1):
            c=[]
            for r in (l,l+2):
                for a in (a0,a0+2):
                    v=(x,(r+a)//2+cy,(r-a)//2+1)
                    if is_site(v): c.append(v)
            assert len(c)==1,(x,c); out[x]=c[0]
        for x in range(xlo,xhi): assert out[x+1] in nbrs(out[x])
        return out
    res=[]
    for u in (41,43,45,47):
        for a0 in (5,7,9,11):
            LO,HI=-400,120
            A=avenue(u,a0,LO,HI); B=avenue(u,a0+4,LO-2,HI+2)
            P1=[x for x in range(-8,8) if rho(A[x])==u and alpha(A[x])==a0]
            xa=P1[0]; sa=A[xa]; xb=xa+48; sb=A[xb]; assert rho(sb)==u and alpha(sb)==a0
            e1=eps(sa); delta=1 if e1==1 else 2
            gates=[x for x in range(LO+4,HI-4) if alpha(A[x])==a0+2]
            for x in gates:                                  # (1)
                g=A[x]; gp=B[x-eps(g)]
                assert gp in nbrs(g) and rho(gp)==rho(g) and alpha(gp)==a0+4
            firstbeyond={s:min(x for x in gates if x>xa and eps(A[x])==s) for s in (1,-1)}
            assert all(xa<firstbeyond[s]<=xa+3 for s in (1,-1))
            E_all={}; E_old=set()
            for x0 in [x for x in gates if x<xa]:
                for s1 in (1,-1):
                    x1=firstbeyond[s1]; g0=A[x0]; g1=A[x1]
                    p0=x0-eps(g0); p1=x1-eps(g1); assert p0<=p1
                    path=[A[x] for x in range(xa,x0-1,-1)]+[B[x] for x in range(p0,p1+1)]+[A[x] for x in range(x1,xb+1)]
                    assert path[0]==sa and path[-1]==sb
                    assert len(set(path))==len(path)                                         # simple
                    assert all(path[i+1] in nbrs(path[i]) for i in range(len(path)-1))       # lattice path
                    E=(len(path)-1)-(xb-xa)
                    assert E==2+2*(xa-x0)+eps(g0)-eps(g1)                                    # (3)
                    assert E not in E_all; E_all[E]=(eps(g0),eps(g1),xa-x0)
                    if eps(g0)==1 and s1==1: E_old.add(E)
            top=max(E_all)-8
            assert sorted(e for e in E_all if e<=top)==list(range(2*delta,top+1,2)),(u,a0)   # (4)
            assert len(set(e%8 for e in E_old))==1                                           # (5)
            res.append((u,a0,e1,delta,sorted(set(e%8 for e in E_old))[0]))
    return res
tot=0
for cy in (0,2):
    r=run(cy); tot+=len(r)
    print("centre offset %d:"%cy)
    for u,a0,e1,delta,old in r[:4]+r[-2:]:
        print("   u=%d a*=%d eps(s_a)=%+d : new detours give every even E >= %d exactly once ; old construction only E = %d mod 8"%(u,a0,e1,2*delta,old))
print("%d cases (levels u = 41..47, strips a* = 5..11, both centre parities): claims (1)-(5) hold in all"%tot)
