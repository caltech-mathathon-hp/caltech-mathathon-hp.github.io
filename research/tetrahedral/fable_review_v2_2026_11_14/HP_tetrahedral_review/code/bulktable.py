"""Bulk table: for a segment P (constant alpha) joined at both ends, with both joints farther than 12 from every vertex,
   the way it is joined depends only on  key = (kind, signs, Xhat = min X + max X, alpha mod 4):
   value = set of (change of alpha, change of Xhat, kind of the neighbour).
   Checked: value is a function of key for all m in the range, and the table has the three properties A', B', C'."""
import sys
from canon import *
from canon_patches import PATCH
table={}; clash=0; firstseen={}
for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
    G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
    xs=[v[0] for v in S]; cx=(min(xs)+max(xs))//2
    seg={}; segs=[]
    for v in sorted(X):
        if v in seg: continue
        comp=[v]; seg[v]=len(segs); st=[v]
        while st:
            x=st.pop()
            for w in adj[x]:
                if w not in seg and alpha(w)==alpha(x): seg[w]=len(segs); comp.append(w); st.append(w)
        segs.append(comp)
    al=[alpha(c[0]) for c in segs]; xh=[min(v[0]-cx for v in c)+max(v[0]-cx for v in c) for c in segs]
    kind=[]
    for i,c in enumerate(segs):
        if any(Z(v)==0 and any(w in E for w in nb[v]) for v in c): kind.append('row')
        else: kind.append('Z' if al[i]>0 else 'Y')
    far=lambda v: all(max(abs(v[t]-V[t]) for t in range(3))>12 for V in G.vertices)
    joints=defaultdict(list)
    for v in X:
        for w in adj[v]:
            if seg[w]!=seg[v]: joints[seg[v]].append((v,w))
    new=0
    for i,js in joints.items():
        if len(js)!=2 or not all(far(v) for v,w in js): continue
        c=segs[i]
        if kind[i]=='Z': sgn=(sg(max(Y(v) for v in c)),)
        elif kind[i]=='Y': sgn=(sg(max(Z(v) for v in c)),)
        else: sgn=(sg(Y(c[0])),sg(xh[i]))
        key=(kind[i],sgn,xh[i] if kind[i]!="row" else None,(al[i] if abs(al[i])<=5 else "%d mod 4"%(al[i]%4)))
        val=frozenset((al[seg[w]]-al[i],xh[seg[w]]-xh[i],kind[seg[w]]) for v,w in js)
        if key not in table: table[key]=val; firstseen[key]=m; new+=1
        elif table[key]!=val: clash+=1
    print("m=%2d: table entries %d (new %d), clashes so far %d"%(m,len(table),new,clash),flush=True)
print()
okA=okB=okC=True
for key,val in sorted(table.items(),key=str):
    k=key[0]; v=sorted(val)
    if k=='Z':
        good=len(v)==2 and ((v[0][0]==-2 and v[1][0]==2) or any(x[2]=='row' for x in v)) ; okA&=good
    elif k=='Y':
        good=len(v)==2 and (v[0][1]<0<v[1][1] or v[1][1]<0<v[0][1] or any(x[2]!='Y' for x in v)); okB&=good
    else:
        s=key[1][1]; good=len(v)==2 and any(x[2]=='row' and x[1]*s>0 for x in v); okC&=good
    print("  %-28s -> %s   %s (first seen m=%d)"%(str(key),v,"ok" if good else "VIOLATION",firstseen[key]))
print("A' (kind Z: one neighbour with alpha+2 or a row): %s ; B' (kind Y: neighbours on opposite sides in X, or a neighbour of kind Z/row): %s ; C' (row: a row neighbour farther out): %s ; clashes: %d"%(okA,okB,okC,clash))
