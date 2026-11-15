"""Stand-alone check of the REPLACEMENT padding, Lemma F part D of the revised manuscript (crossing pairs + optional
   hexagon), written from the text only; raw diamond coordinates; one FIXED start site s_a per case.
   A_x, B_x: sites with X = x of A* = A((+,+),u,a*), A** = A((+,+),u,a*+4).  s_a = A_a, s_b = A_b, (rho,alpha) = (u,a*).
   Checks, for every even increase D in 6..DMAX:
     crossing pair p (last x < a with alpha = a*+2 and A_x ~ B_{x-1}); A_{p+1} ~ B_{p+2}; r = a-p in {2,3};
     t=(D-2r)/2 = 4d+j, delta = 1 (j even) / 0 (j odd), eta = j//2, v0 = p+delta-4d, v1 = p+delta+4, e = 1-2delta, q = p+8;
     path A_a..A_v0, B_{v0-e}..B_{v1-e}, A_v1..A_b with A_q~A_{q+1} replaced by A_q,B_{q-1},B_q,B_{q+1},B_{q+2},A_{q+1} if eta:
     lattice path, simple, inside A* u A**, exactly D sites more than the direct piece, v0 < a < v1 < q+1 < b,
     and the four (delta,eta) give the four classes of D mod 8.  Smallest gap b-a = 47 is used."""
from diamond import *
def run(cy,DMAX=400):
    Yf=lambda v: v[1]-cy; Zf=lambda v: v[2]-1
    rho=lambda v: abs(Yf(v))+abs(Zf(v)); alpha=lambda v: abs(Yf(v))-abs(Zf(v))
    def site(l,a0,x):
        c=[]
        for r in (l,l+2):
            for a in (a0,a0+2):
                v=(x,(r+a)//2+cy,(r-a)//2+1)
                if is_site(v): c.append(v)
        assert len(c)==1; return c[0]
    n=0; phases=set()
    for u in (41,43,45,47,61,63):
        for a0 in (5,7,9,11,23,25):
            A=lambda x: site(u,a0,x); B=lambda x: site(u,a0+4,x)
            for a in [x for x in range(0,8) if rho(A(x))==u and alpha(A(x))==a0]:
                b=min(x for x in range(a+47,a+52) if rho(A(x))==u and alpha(A(x))==a0)
                p=next(x for x in range(a-1,a-9,-1) if alpha(A(x))==a0+2 and B(x-1) in nbrs(A(x)))
                assert alpha(A(p+1))==a0+2 and A(p+1) in nbrs(A(p)) and B(p+2) in nbrs(A(p+1))
                r=a-p; assert r in (2,3); phases.add(r); cls={}
                for D in range(6,DMAX+1,2):
                    d,j=divmod((D-2*r)//2,4); dl=1 if j%2==0 else 0; eta=j//2
                    v0=p+dl-4*d; v1=p+dl+4; e=1-2*dl; q=p+8
                    assert v0<a<v1<=q and q+1<b
                    path=[A(x) for x in range(a,v0-1,-1)]+[B(x) for x in range(v0-e,v1-e+1)]
                    for x in range(v1,b+1):
                        path.append(A(x))
                        if eta and x==q: path+=[B(q-1),B(q),B(q+1),B(q+2)]
                    assert path[0]==A(a) and path[-1]==A(b)
                    assert len(set(path))==len(path)
                    assert all(path[i+1] in nbrs(path[i]) for i in range(len(path)-1))
                    assert len(path)==(b-a+1)+D
                    assert all(rho(v) in (u,u+2) and a0<=alpha(v)<=a0+6 and Yf(v)>0 and Zf(v)>0 for v in path)
                    cls.setdefault((dl,eta),set()).add(D%8); n+=1
                assert all(len(s)==1 for s in cls.values()) and len(set(min(s) for s in cls.values()))==4
    return n,phases
tot=0
for cy in (0,2):
    n,ph=run(cy); tot+=n; print("centre offset %d: %d padded paths, phases r occurring: %s"%(cy,n,sorted(ph)))
print("all checks passed: %d paths, every even increase 6..400, four (delta,eta) <-> four classes mod 8"%tot)
