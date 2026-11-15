"""Bent foliation of Oct(m): in the quadrant (sign Y, sign Z) of the yz-plane use the zigzag direction (0,sY,sZ);
paths turn on the planes Y=0, Z=0 (chosen so that no lattice site lies on both).  Every face is then an exit face."""
import sys, itertools
from collections import Counter, defaultdict
from geom import *
def foliation(S):
    ys=[v[1] for v in S]; zs=[v[2] for v in S]
    cy=(min(ys)+max(ys))//2; cz=(min(zs)+max(zs))//2
    if (cy-cz)%2==0: cz+=1
    def tn(v,typ,coord,sign):
        """the neighbour of v along a bond of type typ (1: t1,t2 ; 2: t3,t4) whose coordinate coord changes by sign"""
        A=(sum(v)%4==0)
        for t in ((T[0],T[1]) if typ==1 else (T[2],T[3])):
            w=tuple(v[i]+t[i] for i in range(3)) if A else tuple(v[i]-t[i] for i in range(3))
            if w[coord]-v[coord]==sign: return w
    qt=lambda sy,sz: 1 if sy*sz>0 else 2
    nb={}
    for v in S:
        Y=v[1]-cy; Z=v[2]-cz
        if Y!=0 and Z!=0:
            t=qt(Y,Z); c=[tn(v,t,1,1),tn(v,t,1,-1)]
        elif Z==0:
            c=[tn(v,qt(Y,-1),2,-1),tn(v,qt(Y,1),2,1)]
        else:
            c=[tn(v,qt(-1,Z),1,-1),tn(v,qt(1,Z),1,1)]
        nb[v]=[w for w in c if w in S]
    return nb
if __name__=="__main__":
    for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
        G=Geo(m); S=G.S
        nb=foliation(S)
        sym=all(v in nb[w] for v in S for w in nb[v])
        deg=Counter(len(nb[v]) for v in S)
        ends=[v for v in S if len(nb[v])<2]
        legit=sum(1 for v in ends if G.dang[v])
        # components
        seen=set(); ncomp=0; ncyc=0; lens=[]
        for v in S:
            if v in seen: continue
            comp=[v]; seen.add(v); st=[v]
            while st:
                x=st.pop()
                for w in nb[x]:
                    if w not in seen: seen.add(w); st.append(w); comp.append(w)
            ncomp+=1; lens.append(len(comp))
            if all(len(nb[x])==2 for x in comp): ncyc+=1
        alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
        E=set(v for e in alledges for v in e)
        # after deleting E
        nb2={v:[w for w in nb[v] if w not in E] for v in S if v not in E}
        bad=[v for v in nb2 if len(nb2[v])<2 and not G.dang[v]]
        single=[v for v in nb2 if len(nb2[v])==0]
        print("m=%2d symmetric:%s degrees:%s paths:%d cycles:%d ends legit: %d/%d min len %d | after deleting edges: bad ends %d, isolated sites %d"%(m,sym,dict(deg),ncomp,ncyc,legit,len(ends),min(lens),len(bad),len(single)))
