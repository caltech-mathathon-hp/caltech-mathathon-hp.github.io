# Coordinate facts (C1),(C2) behind the general proof of the pinning lemma.
import sys, itertools
from geom import *
dot=lambda p,q: sum(p[i]*q[i] for i in range(3))
allok=True
for m in range(6,21):
    G=Geo(m); S=G.S
    small=[t for t in G.small_face_triples() if t[3]=='small']
    for (Va,Vb,Vc,_,_) in small[:1]+[(t[1],t[2],t[0],0,0) for t in small[:2]]+[(t[2],t[1],t[0],0,0) for t in small[:1]]:
        e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc); e2c=e2[::-1]
        u1=tuple((Vb[i]-Va[i])//(m-1) for i in range(3)); u3=tuple((Vc[i]-Va[i])//(m-1) for i in range(3))
        idx=lambda u:[(a,b) for a in range(4) for b in range(4) if a!=b and tuple(T[a][i]-T[b][i] for i in range(3))==u][0]
        a,b=idx(u1); a2,c=idx(u3)
        if a!=a2: # u1 = t_a - t_b and u3 = t_c' - t_b' with a common index elsewhere: rewrite via negatives
            # then u1 = -(t_b - t_a), u3 = -(t_c - t_a2): use common second index
            assert b==c or True
        if a==a2:
            d=[x for x in range(4) if x not in (a,b,c)][0]
            hv=tuple(T[a][i]+T[b][i] for i in range(3)); kv=tuple(T[a][i]+T[d][i] for i in range(3)); sg=1
        else:
            # u1 = t_a - t_b, u3 = t_a2 - t_c with b == c : common "minus" index
            assert b==c
            d=[x for x in range(4) if x not in (a,a2,b)][0]
            # h must be constant on u1 and +2 per u3 ; k constant on u2=u3-u1 and +2 per u3
            hv=tuple(-(T[a][i]+T[b][i]) for i in range(3)); kv=tuple(-(T[b][i]+T[d][i]) for i in range(3)); sg=1
        h=lambda v: dot(v,hv)//2; k=lambda v: dot(v,kv)//2
        c0=e3[1]; assert c0==e1[1]
        ok=all(abs(h(nb)-h(v))==1 and abs(k(nb)-k(v))==1 for v in e1+e2+e3 for nb in nbrs(v))          # +-1 per bond
        ok&=all(h(e3[i])==h(c0)+i-1 and k(e3[i])==k(c0)+i-1 for i in range(len(e3)))                       # track: +1 per zigzag step
        ok&=all(abs(h(v)-h(c0))<=1 for v in e1) and all(k(e1[i])==k(c0)+i-1 for i in range(len(e1)))        # e1: h constant, k increasing
        ok&=all(h(e2c[i])==h(Vc)-i for i in range(len(e2c))) and all(abs(k(v)-k(Vc))<=1 for v in e2)        # e2: k constant, h decreasing from V_c
        track=set(e3[1:2*m-2])|{e1[2]}
        alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
        Z=set(v for e in alledges for v in e)
        c1=all((h(z)<=h(c0)+1 or k(z)>=k(c0)+2*(m-2)-1) for z in Z if z not in track or z in (e1[2],c0))
        c1b=all((h(z)>h(c0)+1 and k(z)<k(c0)+2*(m-2)-1) for z in e3[4:2*m-5])
        allok&=ok and c1 and c1b
        if not (ok and c1 and c1b): print("m=%d FAIL"%m,ok,c1,c1b,(Va,Vb,Vc))
print("coordinate facts (C1),(C2) hold for m=6..20 and several choices of the small face / orientation:",allok)
