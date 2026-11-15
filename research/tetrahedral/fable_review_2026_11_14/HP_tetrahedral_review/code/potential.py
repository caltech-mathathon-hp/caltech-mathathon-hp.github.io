"""Acyclicity certificate for the canonical cover.
   Segments = maximal subpaths with constant alpha (joined by foliation bonds); every other bond changes alpha by +-2.
   Omega(segment) = Xbar + K*max(alpha,0).  A cycle would contain a segment that is a strict local maximum of Omega
   among its (two) neighbouring segments.  We list all segments joined at both ends and test this."""
import sys
from canon import *
from canon_patches import PATCH
def segments(m):
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
    al=[alpha(c[0]) for c in segs]
    xb=[2*sum(v[0]-cx for v in c)/len(c) for c in segs]
    links=defaultdict(list)
    for v in X:
        for w in adj[v]:
            if seg[w]!=seg[v]: links[seg[v]].append((seg[w],v,w))
    return G,X,adj,Y,Z,alpha,segs,al,xb,links,cx
def check(m,K=1000,verbose=False):
    G,X,adj,Y,Z,alpha,segs,al,xb,links,cx=segments(m)
    om=[xb[i]+K*max(al[i],0) for i in range(len(segs))]
    nlink=Counter(len(links[i]) for i in range(len(segs)))
    viol=[]; ties=0
    for i,l in links.items():
        if len(l)>2: viol.append((i,'more than two links')); continue
        if any(om[j]==om[i] for j,_,_ in l): ties+=1
        if len(l)==2 and all(om[j]<om[i] for j,_,_ in l): viol.append((i,'local max'))
    return len(segs),dict(nlink),viol,ties,(G,X,adj,Y,Z,alpha,segs,al,xb,links,cx,om)
if __name__=="__main__":
    for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
        n,nl,viol,ties,data=check(m)
        G,X,adj,Y,Z,alpha,segs,al,xb,links,cx,om=data
        print("m=%2d: %d segments, by number of links %s ; strict local maxima of Omega among doubly linked segments: %d ; ties: %d"%(m,n,nl,len(viol),ties))
        for i,why in viol[:12]:
            v=segs[i][0]; V=nearest_vertex(G,v)
            print("    segment alpha %+d, 2*meanX %+.1f, %d sites, e.g. site rel. to vertex %s: %s ; neighbours (alpha, 2*meanX): %s"%(al[i],xb[i],len(segs[i]),V,tuple(v[t]-V[t] for t in range(3)),[(al[j],round(xb[j],1)) for j,_,_ in links[i]]))
