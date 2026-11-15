"""Acyclicity certificate for the canonical cover, for a range of m.
   Segment = maximal subpath of constant alpha.  Every other bond of the cover changes alpha by +-2.
   Omega(P) = C + |Xbar|          if P is a 'row' segment (contains a damaged end with Z = 0),
              K*alpha + Xbar       if alpha > 0 otherwise,
              Xbar                 if alpha < 0.          (Xbar = min X + max X over P, an integer)
   A cycle would contain a segment that is the maximum of Omega on the cycle: a strict local maximum (no ties occur).
   We list all strict local maxima T and check for each one that, following the path from T, within STEPS segments
   we meet an end of the path or a segment with larger Omega.  Then no cycle exists."""
import sys, time
from canon import *
from canon_patches import PATCH
K=10**4; C=10**9; STEPS=14
def certify(m):
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
    al=[alpha(c[0]) for c in segs]; xb=[min(v[0]-cx for v in c)+max(v[0]-cx for v in c) for c in segs]
    isrow=[any(Z(v)==0 and any(w in E for w in nb[v]) for v in c) for c in segs]
    om=[(C+abs(xb[i])) if isrow[i] else (K*al[i]+xb[i] if al[i]>0 else xb[i]) for i in range(len(segs))]
    links=defaultdict(set)
    for v in X:
        for w in adj[v]:
            if seg[w]!=seg[v]:
                assert abs(alpha(w)-alpha(v))==2
                links[seg[v]].add(seg[w])
    assert all(len(l)<=2 for l in links.values())
    ties=sum(1 for i,l in links.items() for j in l if om[i]==om[j])
    tops=[i for i,l in links.items() if len(l)==2 and all(om[j]<om[i] for j in l)]
    desc=[]; ok=True
    for i in tops:
        res=None
        for j in links[i]:
            prev,cur=i,j
            for step in range(STEPS):
                if om[cur]>om[i]: res="dominated after %d"%(step+1); break
                nx=[k for k in links[cur] if k!=prev]
                if not nx: res="path ends after %d"%(step+1); break
                prev,cur=cur,nx[0]
            if res: break
        if res is None: ok=False; res="NOT CERTIFIED"
        v=min(segs[i]); V=nearest_vertex(G,v); dist=max(abs(v[t]-V[t]) for t in range(3))
        desc.append((G.vertices.index(V),tuple(v[t]-V[t] for t in range(3)),len(segs[i]),res,dist))
    return len(segs),ties,tops,sorted(desc),ok
if __name__=="__main__":
    ref=None
    for m in range(int(sys.argv[1]),int(sys.argv[2])+1,int(sys.argv[3]) if len(sys.argv)>3 else 1):
        t0=time.time(); n,ties,tops,desc,ok=certify(m)
        key=[d[:3] for d in desc]
        same="" if ref is None else (" ; same list as m=%d: %s"%(ref[0],key==ref[1]))
        if ref is None: ref=(m,key)
        print("m=%2d: %d segments ; ties %d ; strict local maxima %d (max distance from a vertex %d) ; all certified: %s%s ; %.0fs"%(m,n,ties,len(tops),max(d[4] for d in desc),ok,same,time.time()-t0),flush=True)
    print("the local maxima (vertex index, position of the first site relative to the vertex, #sites, certificate):")
    for d in desc: print("   ",d[:4])
