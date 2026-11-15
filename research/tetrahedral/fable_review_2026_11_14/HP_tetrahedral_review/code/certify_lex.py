"""Bulk Lemma, Claim 2, with the LEXICOGRAPHIC potential (replaces the fixed constants K=10^4, C=10^9 of certify.py):
     Omega(P) = (2, |Xhat|, 0)   if P is a row segment,
                (1, alpha, Xhat) if alpha > 0 otherwise,
                (0, Xhat, 0)     if alpha < 0 otherwise           (compared lexicographically).
   mode 'cert m1 m2 [step]': list the strict local maxima and certify each (end of path or larger Omega within STEPS).
   mode 'witness m...'    : the configuration P,Q,R at the -y vertex reported by the audit; shows that with the OLD
                            numeric potential P becomes a local maximum for m >= 50004, and what the walk from P sees."""
import sys, time
from canon import *
from canon_patches import PATCH
STEPS=6
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
    al=[alpha(c[0]) for c in segs]; xb=[min(v[0]-cx for v in c)+max(v[0]-cx for v in c) for c in segs]
    isrow=[any(Z(v)==0 and any(w in E for w in nb[v]) for v in c) for c in segs]
    links=defaultdict(set)
    for v in X:
        for w in adj[v]:
            if seg[w]!=seg[v]:
                assert abs(alpha(w)-alpha(v))==2; links[seg[v]].add(seg[w])
    assert all(len(l)<=2 for l in links.values())
    return G,segs,seg,al,xb,isrow,links
lex=lambda r,a,x: (2,abs(x),0) if r else ((1,a,x) if a>0 else (0,x,0))
def certify(m):
    G,segs,seg,al,xb,isrow,links=segments(m)
    om=[lex(isrow[i],al[i],xb[i]) for i in range(len(segs))]
    ties=sum(1 for i,l in links.items() for j in l if om[i]==om[j])
    tops=[i for i,l in links.items() if len(l)==2 and all(om[j]<om[i] for j in l)]
    desc=[]; ok=True; mx=0
    for i in tops:
        res=None
        for j in links[i]:
            prev,cur=i,j
            for step in range(STEPS):
                if om[cur]>om[i]: res="dominated after %d"%(step+1); mx=max(mx,step+1); break
                nx=[k for k in links[cur] if k!=prev]
                if not nx: res="path ends after %d"%(step+1); mx=max(mx,step+1); break
                prev,cur=cur,nx[0]
            if res: break
        if res is None: ok=False; res="NOT CERTIFIED"
        v=min(segs[i]); V=nearest_vertex(G,v)
        desc.append((G.vertices.index(V),tuple(v[t]-V[t] for t in range(3)),len(segs[i]),res))
    return len(segs),ties,sorted(desc),ok,mx
if sys.argv[1]=='cert':
    ref=None; allok=True
    for m in range(int(sys.argv[2]),int(sys.argv[3])+1,int(sys.argv[4]) if len(sys.argv)>4 else 1):
        n,ties,desc,ok,mx=certify(m); key=[d[:3] for d in desc]
        if ref is None and m>=14: ref=(m,key)
        same=(ref is not None and key==ref[1]); allok&=ok and ties==0
        print("m=%3d: %7d segments ; ties %d ; strict local maxima %d ; all certified within %d steps: %s ; same list as m=%s: %s"%(m,n,ties,len(desc),mx,ok,ref[0] if ref else '-',same),flush=True)
    print("ALL OK:",allok); print("local maxima (vertex, first site rel. vertex, #sites, certificate):")
    for d in desc: print("   ",d)
else:
    K,C=10**4,10**9; MB=50034
    for m in map(int,sys.argv[2:]):
        G,segs,seg,al,xb,isrow,links=segments(m)
        P=seg[(0,4,0)]; assert sorted(segs[P])==[(0,4,0),(1,3,-1)]
        Q=seg[(-1,3,1)]; R=seg[(2,4,-2)]; assert links[P]=={Q,R} and segs[Q]==[(-1,3,1)] and segs[R]==[(2,4,-2)]
        assert isrow[Q] and not isrow[P] and not isrow[R]
        assert (al[P],xb[P])==(2*m-7,1) and abs(xb[Q])==2 and (al[R],xb[R])==(2*m-9,4)
        old=lambda i,M: (C+abs(xb[i])) if isrow[i] else K*(al[i]-2*m+2*M)+xb[i]      # old numeric Omega, transported to size M
        assert old(P,MB)==K*(2*MB-7)+1 and old(P,MB)>old(Q,MB) and old(P,MB)>old(R,MB) and old(P,50003)<old(Q,50003)
        walks=[]
        for j in (Q,R):
            prev,cur=P,j; w=[]
            for step in range(6):
                w.append(("row" if isrow[cur] else "a=2m%+d"%(al[cur]-2*m),xb[cur],old(cur,MB)>old(P,MB)))
                nx=[k for k in links[cur] if k!=prev]
                if not nx: w.append("END"); break
                prev,cur=cur,nx[0]
            walks.append(w)
        esc=any(x=="END" or x[2] for w in walks for x in w)
        print("m=%d: P,Q,R as reported; Omega_old(P)=1e4(2m-7)+1, Omega_old(Q)=1e9+2, Omega_old(R)=1e4(2m-9)+4."%m)
        print("   transported to m=%d (old potential): P local max: True ; escape within 6 segments: %s"%(MB,esc))
        for w in walks: print("   walk:",w)
        print("   lexicographic: Omega(Q)=%s > Omega(P)=%s  -> P is not a local maximum"%(lex(isrow[Q],al[Q],xb[Q]),lex(isrow[P],al[P],xb[P])))
