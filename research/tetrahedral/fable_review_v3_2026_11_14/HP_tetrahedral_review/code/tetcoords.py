# Checks of section 5.6: tetrahedral coordinates, Oct(m) description, (O1)-(O3) statements, Lemma T (clean form)
import sys, itertools
from geom import Geo
T=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
def isA(v): return v[0]%2==0
def nbrs(v):
    sg=1 if isA(v) else -1
    return [(v[0]+sg*t[0],v[1]+sg*t[1],v[2]+sg*t[2]) for t in T]
def fco(v,m):
    c=(0,2*m-2,0); return tuple(sum(t[i]*(v[i]-c[i]) for i in range(3)) for t in T)
def inoct(v,m):
    f=fco(v,m)
    if isA(v): return all(abs(x)<=2*m-2 for x in f)
    return all(-(2*m-1)<=x<=2*m-3 for x in f)
def insite(v):
    x,y,z=v
    return x%2==y%2==z%2 and (x+y+z)%4 in (0,3)
for m in range(3,13):
    G=Geo(m,3); S=set(G.S)
    box=range(-2*m-6,4*m+8)
    mine=set()
    for x in range(-2*m-4,2*m+5):
        for y in range(-6,4*m+4):
            for z in range(-2*m-4,2*m+5):
                v=(x,y,z)
                if insite(v) and inoct(v,m): mine.add(v)
    assert mine==S, m
    # congruences
    for v in S:
        f=fco(v,m); assert sum(f)==0
        assert all((x-(2*m-2))%4==0 for x in f) if isA(v) else all((x-(2*m+1))%4==0 for x in f)
    # O1
    dang={}
    for v in S:
        f=fco(v,m)
        out=[w for w in nbrs(v) if w not in S]
        exp=sum(1 for x in f if x==2*m-2) if isA(v) else sum(1 for x in f if x==-(2*m-1))
        assert len(out)==exp
        for w in out: dang.setdefault(w,[]).append(v)
    assert all(len(l)==1 for l in dang.values())
    assert not any(w2 in dang for w in dang for w2 in nbrs(w))
    assert sum(len(l) for l in dang.values())==4*m*m
    # O3: bonded surface pairs = consecutive edge zigzag sites
    surf={v for l in dang.values() for v in l}
    def edge_of(v):
        f=fco(v,m); r=[]
        for k in range(4):
            for j in range(4):
                if k==j: continue
                if isA(v) and f[k]==2*m-2 and f[j]==-(2*m-2): r.append((k,j))
                if (not isA(v)) and f[k]==2*m-3 and f[j]==-(2*m-1): r.append((k,j))
        return r
    for v in surf:
        for w in nbrs(v):
            if w in surf:
                assert set(edge_of(v))&set(edge_of(w)), (m,v,w)
    # O2: P^3 links join T-neighbours on a common face
    for v in surf:
        ends=set()
        for p1 in nbrs(v):
            if p1 in S: continue
            for p2 in nbrs(p1):
                if p2 in S: continue
                for p3 in nbrs(p2):
                    if p3 in S or p3==p1: continue
                    for w in nbrs(p3):
                        if w in S and w!=v and w!=p2: ends.add(w)
        f=fco(v,m)
        faces=[k for k in range(4) if (f[k]==2*m-2 if isA(v) else f[k]==-(2*m-1))]
        exp=set()
        for k in faces:
            for i in range(4):
                for l in range(4):
                    if i!=l and i!=k and l!=k:
                        sg=1 if isA(v) else -1
                        w=tuple(v[q]+sg*(T[l][q]-T[i][q]) for q in range(3))
                        if w in S: exp.add(w)
        assert ends==exp,(m,v)
print("5.6: Oct(m) description, congruences, (O1), (O2), (O3) verified for m=3..12")
# Lemma T clean form
def depths(v,m):
    f=fco(v,m); return tuple(2*m-2-x for x in f)+tuple(2*m-1+x for x in f)
bad=0; tot=0
for (R,Rp) in [(8,4),(14,6),(24,10)]:
    m0=(3*R+2*Rp+24+3)//4
    for m in range(m0,m0+4):
        c=(0,2*m-2,0)
        rng=range(-2*m-R,2*m+R+1)
        for X in range(-2*m-R//2,2*m+R//2+1):
            for Y in range(-2*m-R//2,2*m+R//2+1):
                for z in range(-2*m-R//2,2*m+R//2+1):
                    v=(X,Y+2*m-2,z)
                    if not insite(v): continue
                    d=depths(v,m)
                    if min(d)<-R: continue
                    Z=z-1
                    cand=[(abs(X),0,X)]
                    if abs(Y)>=Rp+2: cand.append((abs(Y),1,Y))
                    if abs(Z)>=Rp+2: cand.append((abs(z),2,z))
                    _,ax,val=max(cand)
                    e=[0,0,0]; e[ax]=1 if val>=0 else -1
                    w=(v[0]-2*e[0],v[1]-2*e[1]-2,v[2]-2*e[2])
                    assert insite(w)
                    d2=depths(w,m-1)
                    tot+=1
                    for p,q in zip(d,d2):
                        if not (p==q or (p>R+4 and q==p-4)): bad+=1
                    Y2=w[1]-(2*(m-1)-2); Z2=w[2]-1
                    for p,q in ((Y,Y2),(Z,Z2)):
                        if not (p==q or (abs(p)>=Rp and abs(q)>=Rp and (p>0)==(q>0))): bad+=1
print("Lemma T (clean form): sites tested",tot,"violations",bad)
