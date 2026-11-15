"""Region transfers (notes 5.6): Oct(m+2) concentric with Oct(m) looks near v+T like Oct(m) near v, for
   T = 4*sigma*e_x, 4*sigma*e_y, 4*sigma*e_z or the arm vector (0,2sY,2sZ), under the stated conditions; and every
   site of Oct(m) satisfies at least one condition once m is large compared with the radius D."""
import sys, itertools
from diamond import *
TT=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
def fco(v,m): return tuple(sum(t[i]*(v[i]-(0,2*m-2,0)[i]) for i in range(3)) for t in TT)
def inoct(f,isA,M):          # octahedron of size M centred at c_m, f relative to c_m
    return all(abs(x)<=2*M-2 for x in f) if isA else all(-(2*M-1)<=x<=2*M-3 for x in f)
def depths(f,m):             # big faces j (s=t_j), small faces j (s=-t_j)
    return [2*m-2-x for x in f],[2*m-1+x for x in f]
sgn=lambda t:(t>0)-(t<0)
D=int(sys.argv[1]) if len(sys.argv)>1 else 4
for m in [int(a) for a in sys.argv[2:]] or [3*D+8,3*D+9]:
    tested=Counter() if False else {}
    bad=0; uncovered=0; tot=0
    R=range(-D,D+1)
    ball=[(a,b,c) for a in R for b in R for c in R]
    for x in range(-2*m,2*m+1):
        for Yc in range(-2*m,2*m+1):
            for z in range(-2*m,2*m+1):
                v=(x,Yc+2*m-2,z)
                if not is_site(v): continue
                f=fco(v,m); isA=sum(v)%4==0
                if not inoct(f,isA,m): continue
                tot+=1
                db,ds=depths(f,m); Y=Yc; Z=z-1
                conds=[]
                for ax,coord in ((0,x),(1,Y),(2,Z)):
                    for sig in (1,-1):
                        far=all((db[j] if TT[j][ax]==-sig else 10**9)>3*D for j in range(4)) and all((ds[j] if -TT[j][ax]==-sig else 10**9)>3*D for j in range(4))
                        if far and (ax==0 or sig*coord>D+1):
                            T=[0,0,0]; T[ax]=4*sig; conds.append(tuple(T))
                if abs(Y)>D+1 and abs(Z)>D+1:
                    sy,sz=sgn(Y),sgn(Z)
                    k=[j for j in range(4) if (TT[j][1],TT[j][2])==(sy,sz)][0]; i=[j for j in range(4) if (-TT[j][1],-TT[j][2])==(sy,sz)][0]
                    far=all(db[j]>3*D for j in range(4) if j!=k) and all(ds[j]>3*D for j in range(4) if j!=i)
                    if far: conds.append((0,2*sy,2*sz))
                if not conds: uncovered+=1; continue
                for T in conds:
                    tested[T]=tested.get(T,0)+1
                    for d in ball:
                        w=(v[0]+d[0],v[1]+d[1],v[2]+d[2])
                        if not is_site(w): continue
                        w2=(w[0]+T[0],w[1]+T[1],w[2]+T[2])
                        a=inoct(fco(w,m),sum(w)%4==0,m); b=inoct(fco(w2,m),sum(w2)%4==0,m+2)
                        Yw,Zw=w[1]-(2*m-2),w[2]-1; Y2,Z2=w2[1]-(2*m-2),w2[2]-1
                        if a!=b or sgn(Yw)!=sgn(Y2) or sgn(Zw)!=sgn(Z2) or (T[1]==0 and Yw!=Y2) or (T[2]==0 and Zw!=Z2): bad+=1
    print("D=%d m=%d: %d sites of Oct(m); without any applicable transfer: %d ; ball comparisons failing: %d ; transfers used: %d kinds"%(D,m,tot,uncovered,bad,len(tested)))
