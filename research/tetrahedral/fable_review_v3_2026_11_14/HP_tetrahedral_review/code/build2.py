"""Explicit fold for one instance of the DIMER-ANCHOR design (notes section 14).
Frames on e1,e2 with slots; anchors = dimers in slots; separators tethered between anchors; bulk arbitrary."""
import sys, itertools, time, re
from collections import deque, Counter
from geom import *
from bulk import bulk_cover
m=int(sys.argv[1]) if len(sys.argv)>1 else 38
CAP=int(sys.argv[2]) if len(sys.argv)>2 else 4            # bin capacity in dimers (= lambda*B)
PACK=eval(sys.argv[3]) if len(sys.argv)>3 else [[4],[4]]  # items (in dimers) per bin
K=len(PACK); assert all(sum(b)==CAP for b in PACK)
J1=int(sys.argv[5]) if len(sys.argv)>5 else max(CAP+6,5*K+9)        # dimer index of first separator (final constants)
JS=[J1+k*(CAP+2) for k in range(K+1)]
R=(m-2)-(JS[-1]+1)                                        # dimers right of last separator
assert R>=max(CAP+3,5*K+3),("track too short",R)
SL1=[3*(k+1) for k in range(K+1)]                         # 2-slots on e1: (a_s,b_s), index from V_a
SL2=[5*k+3 for k in range(K+1)]                           # 6-slots on e2: a'_s..b'_{s+2}, index from V_c
t0=time.time()
G=Geo(m,margin=400); S=G.S; N=len(S)
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MAJ='A' if sum(1 for v in S if sub(v)=='A')>N/2 else 'B'
is_maj=lambda v: sub(v)==MAJ
small=[t for t in G.small_face_triples() if t[3]=='small']
Va,Vb,Vc=small[0][0],small[0][1],small[0][2]
e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc); e2c=e2[::-1]
alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
E=set(v for e in alledges for v in e)
def cap(u,avoid=()):
    c=[d for d in G.dang[u] if d not in avoid]; assert c,("no free dangling site",u); return c[0]
reserved=set()
def res(ps):
    for p in ps:
        assert p not in S and p not in reserved,("P clash",p); reserved.add(p)
def ppp(u,w):
    for du in G.dang[u]:
        for x in nbrs(du):
            if x in S or x in reserved: continue
            for dw in G.dang[w]:
                if dw!=du and dw in nbrs(x) and du not in reserved and dw not in reserved: return (du,x,dw)
    raise Exception("no PPP link %s %s"%(u,w))
def link(u,w,k,keep):
    """outside path with exactly k sites from a dangling site of u to one of w, avoiding reserved; caps in keep stay usable"""
    best=None
    for dw in G.dang[w]:
        dist={dw:0}; dq=deque([dw])
        while dq:
            x=dq.popleft()
            if dist[x]>=k: continue
            for y in nbrs(x):
                if y in S or y in dist or y in reserved or y in keep: continue
                dist[y]=dist[x]+1; dq.append(y)
        for du in G.dang[u]:
            if du not in dist: continue
            stack=[[du]]
            while stack:
                p=stack.pop()
                if len(p)==k:
                    if p[-1]==dw:
                        score=sum(1 for c in keep for y in nbrs(c) if y not in S and y not in p and y not in reserved)
                        ok=all(any(y not in S and y not in p and y not in reserved for y in nbrs(c)) for c in keep)
                        if ok and (best is None or score>best[0]): best=(score,p)
                    continue
                for y in nbrs(p[-1]):
                    if y in dist and y not in p and dist[y]<=k-1-len(p): stack.append(p+[y])
    assert best is not None,("no link",u,w,k); return best[1]
units=[]
# ---------- terminal on the stuck corner
Ub=e1[-2]; assert Ub==e2[1]
units.append(("terminal",[(Ub,'H'),(cap(Ub),'P')])); res([cap(Ub)])
# ---------- three isolated PHP's
for W in G.vertices:
    if W in (Va,Vb,Vc): continue
    d=G.dang[W]; units.append(("PHP",[(d[0],'P'),(W,'H'),(d[1],'P')])); res(d)
# ---------- skips on the two framed edges (zigzag indices from the first vertex of e1 / of e2)
L=2*m-2
skip1={1,2}|{2*m-3}                      # corner+a_1 (track extension), stuck corner
for s in SL1: skip1|={2*s,2*s+1}
skip2c={1}|{2*m-3}                       # in e2c indices (from V_c): corner at V_c ; stuck corner
for s in SL2: skip2c|=set(range(2*s,2*s+6))
skip2={L-i for i in skip2c}
slot_sites=[e1[i] for i in skip1 if i not in (1,2,2*m-3)]+[e2c[i] for i in skip2c if i not in (1,2*m-3)]
keepcaps=set(cap(z) for z in slot_sites)|{cap(e1[1]),cap(e1[2])}
def runs_of(e,skip):
    out=[]; cur=[]
    for i in range(1,L):
        if i in skip:
            if cur: out.append(cur); cur=[]
        else: cur.append(e[i])
    if cur: out.append(cur)
    return out
fr=[]; idx1={v:i for i,v in enumerate(e1)}; idx2={v:i for i,v in enumerate(e2)}
def flink(u,w,idx):
    c=abs(idx[w]-idx[u])-1; k=c+2 if c%2==1 else c+4
    p=link(u,w,k,keepcaps); res(p); return p
firstcap=None
prev=Va; seqframe=[(Va,'H')]
for e,skip,Vend,idx in ((e1,skip1,Vb,idx1),(e2,skip2,Vc,idx2)):
    for r in runs_of(e,skip):
        assert len(r)>=3,("short frame run",len(r))
        seqframe+=[(p,'P') for p in flink(prev,r[0],idx)]+[(v,'H') for v in r]; prev=r[-1]
    seqframe+=[(p,'P') for p in flink(prev,Vend,idx)]+[(Vend,'H')]; prev=Vend
usedP=set(p for p,l in seqframe if l=='P')
ca=cap(Va,avoid=usedP); cc=cap(Vc,avoid=usedP); res([ca,cc])
units.append(("frame",[(ca,'P')]+seqframe+[(cc,'P')]))
frame_sites=set(p for p,l in seqframe if l=='H')
print("frame built: links",Counter(len(x) for x in re.findall('P+',''.join(l for p,l in seqframe))),"%.0fs"%(time.time()-t0))
# ---------- dimer chains
def dimer_chain(pairs,endcaps=True):
    out=[]
    for i,(x,y) in enumerate(pairs):
        assert y in nbrs(x); out+=[(x,'H'),(y,'H')]
        if i+1<len(pairs):
            l=ppp(y,pairs[i+1][0]); res(l); out+=[(p,'P') for p in l]
    return out
def alt_pairs(sites):
    return [((sites[i],sites[i+1]) if (i//2)%2==0 else (sites[i+1],sites[i])) for i in range(0,len(sites),2)]
def with_caps(body):
    a=cap(body[0][0],avoid=reserved); res([a]); b=cap(body[-1][0],avoid=reserved); res([b])
    return [(a,'P')]+body+[(b,'P')]
z=e3
D=[(e1[2],e1[1])]+[(z[2*j],z[2*j+1]) for j in range(1,m-1)]      # track dimers D_0..D_{m-2} as (a,b)
def flat(a,b): return [s for j in range(a,b) for s in D[j]]
track_units=[]
track_units.append(("filler-left(%d)"%J1,with_caps(dimer_chain(alt_pairs(flat(0,J1))))))
for k in range(K):
    pos=JS[k]+2
    for sz in PACK[k]:
        track_units.append(("item(%d) in bin %d"%(sz,k+1),with_caps(dimer_chain(alt_pairs(flat(pos,pos+sz)))))); pos+=sz
    assert pos==JS[k+1]
track_units.append(("filler-right(%d)"%R,with_caps(dimer_chain(alt_pairs(flat(JS[-1]+2,m-1))))))
ring_units=[]
for (A_,B_,C_,kind,n_) in small[1:]:
    ring=[]
    for V,W in ((A_,B_),(B_,C_),(C_,A_)): ring+=G.edge(V,W)[1:2*m-3]
    assert len(ring)==6*(m-2)
    ring_units.append(("filler-ring(%d)"%(len(ring)//2),with_caps(dimer_chain(alt_pairs(ring)))))
# ---------- separator groups: entry anchor (single dimer), separator (2 dimers), exit anchor (3 dimers)
seps=[]
for k in range(K+1):
    j=JS[k]; s=SL1[k]; s2=SL2[K-k]
    A=(e1[2*s],e1[2*s+1])                                             # (a_s,b_s): linker at a_s, tether at b_s
    sep=dimer_chain([(z[2*j+1],z[2*j]),(z[2*j+2],z[2*j+3])])            # b_j a_j PPP a_{j+1} b_{j+1}
    w=[e2c[i] for i in range(2*s2,2*s2+6)]                              # a b a b a b
    X3=dimer_chain([(w[1],w[0]),(w[2],w[3]),(w[5],w[4])])               # tether at b'_s, linker at a'_{s+2}
    cA0=cap(A[0],avoid=reserved); cA1=cap(A[1],avoid=reserved); cS0=cap(z[2*j+1],avoid=reserved); cS1=cap(z[2*j+3],avoid=reserved)
    cX0=cap(w[1],avoid=reserved); cX1=cap(w[4],avoid=reserved); res([cA0,cA1,cS0,cS1,cX0,cX1])
    seps.append(dict(A=A,sep=sep,X3=X3,cA0=cA0,cA1=cA1,cS0=cS0,cS1=cS1,cX0=cX0,cX1=cX1,g=2*j+3,gp=2*(m-2-j)+1,j=j))
assigned=frame_sites|set(G.vertices)|{Ub}|set(p for nm,u in track_units+ring_units for p,l in u if l=='H')
for d in seps: assigned|=set(d['A'])|set(p for p,l in d['sep']+d['X3'] if l=='H')
assert E-assigned==set(),("edge sites not all assigned",len(E-assigned))
# ---------- bulk
X=S-E
cand=[v for v in X if is_maj(v) and G.dang[v] and all(max(abs(v[i]-e_[i]) for i in range(3))>8 for e_ in G.vertices)]
random_order=sorted(cand)
import random as _r; _r.seed(5); _r.shuffle(random_order)
elig=set(); cells={}
for v in random_order:                       # sparse set of admissible run ends: pairwise far apart, away from edges
    key=(v[0]//10,v[1]//10,v[2]//10)
    near=[w_ for dx in (-1,0,1) for dy in (-1,0,1) for dz in (-1,0,1) for w_ in cells.get((key[0]+dx,key[1]+dy,key[2]+dz),[])]
    if all(max(abs(v[i]-w_[i]) for i in range(3))>=10 for w_ in near) and all(w_ not in E for w_ in nbrs(v)) and all(x_ not in E for w_ in nbrs(v) for x_ in nbrs(w_)):
        elig.add(v); cells.setdefault(key,[]).append(v)
print("admissible bulk-run ends: %d (sparse, away from edges)"%len(elig))
nP=sum(1 for v in X if is_maj(v))-sum(1 for v in X if not is_maj(v))
print("m=%d N=%d K=%d CAP=%d ; bulk sites %d ; bulk runs %d (= m-6: %s)"%(m,N,K,CAP,len(X),nP,nP==m-6))
import pickle, os
cf='/home/claude/work/code/bulk_m%d.pkl'%m
if os.path.exists(cf): paths=pickle.load(open(cf,'rb'))
else:
    paths=bulk_cover(X,is_maj,elig,nP,seed=3,verbose=False); assert paths is not None
    pickle.dump(paths,open(cf,'wb'))
bulk_units=[]
for p in paths:
    a=cap(p[0],avoid=reserved); res([a]); b=cap(p[-1],avoid=reserved); res([b])
    bulk_units.append(("bulk(%d)"%len(p),[(a,'P')]+[(v,'H') for v in p]+[(b,'P')]))
print("bulk cover done, %.0fs"%(time.time()-t0))
# ---------- routing of tethers
blocked=set(reserved)
def bfs(src,dst):
    prev={src:None}; dq=deque([src])
    while dq:
        v=dq.popleft()
        if v==dst: break
        for w_ in nbrs(v):
            if w_ in prev or w_ in S: continue
            if w_ in blocked and w_!=dst: continue
            prev[w_]=v; dq.append(w_)
    if dst not in prev: return None
    p=[dst]
    while prev[p[-1]] is not None: p.append(prev[p[-1]])
    return p[::-1]
def pad(path,n):
    path=list(path)
    while len(path)<n:
        done=False
        for i in range(len(path)-2):
            u,v,w_=path[i],path[i+1],path[i+2]; onp=set(path)
            for a in nbrs(u):
                if a==v or a in S or a in blocked or a in onp: continue
                for b in nbrs(a):
                    if b==u or b in S or b in blocked or b in onp: continue
                    for c in nbrs(b):
                        if c==a or c in S or c in blocked or c in onp: continue
                        if w_ in nbrs(c): path[i+1:i+2]=[a,b,c]; done=True; break
                    if done: break
                if done: break
            if done: break
        assert done,"cannot pad tether"
    return path
def route_exact(src,dst,n):
    p=bfs(src,dst); assert p is not None and len(p)<=n and (n-len(p))%2==0,("tether",len(p) if p else None,n)
    p=pad(p,n)
    for q in p: blocked.add(q)
    return p
for d in seps: d['tout']=route_exact(d['cS1'],d['cX0'],d['gp'])
for d in seps: d['tin']=route_exact(d['cA1'],d['cS0'],d['g'])
sep_units=[]
for k,d in enumerate(seps):
    u=[(d['cA0'],'P'),(d['A'][0],'H'),(d['A'][1],'H')]+[(p,'P') for p in d['tin']]+d['sep']+[(p,'P') for p in d['tout']]+d['X3']+[(d['cX1'],'P')]
    sep_units.append(("anchor(1) P^%d separator(2) P^%d anchor(3)   [track dimers %d,%d]"%(d['g'],d['gp'],d['j'],d['j']+1),u))
print("tethers routed, %.0fs"%(time.time()-t0))
import random
HMAX=int(sys.argv[4]) if len(sys.argv)>4 else 60
dS={}; dq=deque()
for v in S:
    for w_ in nbrs(v):
        if w_ not in S and w_ not in dS: dS[w_]=1; dq.append(w_)
while dq:
    v=dq.popleft()
    if dS[v]>=HMAX: continue
    for w_ in nbrs(v):
        if w_ not in S and w_ not in dS: dS[w_]=dS[v]+1; dq.append(w_)
print("distance field: %d sites, %.0fs"%(len(dS),time.time()-t0))
FAR=5
ctr=[sum(v[t] for v in S)/N for t in range(3)]
def line_from(v,hmax):
    """straight zigzag column in direction (0,+-2,+-2) pointing away from the yz-centre (quadrant of v)"""
    sy=1 if v[1]>=ctr[1] else -1; sz=1 if v[2]>=ctr[2] else -1
    ab=[(a_,b_) for a_ in range(4) for b_ in range(4) if a_!=b_ and tuple(T[a_][i]-T[b_][i] for i in range(3))==(0,2*sy,2*sz)][0]
    path=[v]
    while dS[path[-1]]<hmax:
        x=path[-1]
        nx=tuple(x[i]+T[ab[0]][i] for i in range(3)) if sum(x)%4==0 else tuple(x[i]-T[ab[1]][i] for i in range(3))
        if nx not in dS: return None
        path.append(nx)
    return path
def route_all(order,blocked):
    pairs=[(order[i-1][1][-1][0],order[i][1][0][0]) for i in range(1,len(order))]
    alt={}
    for i,(a,b) in enumerate(pairs): alt[a]=alt[b]=FAR+2+2*i
    assert FAR+2*len(pairs)+6<=HMAX,("increase HMAX to",FAR+2*len(pairs)+6)
    allcaps=[c for pr_ in pairs for c in pr_]
    freecnt=lambda c: sum(1 for w_ in nbrs(c) if w_ not in S and w_ not in blocked)
    prio=[]; base_blocked=set(blocked)
    for restart in range(200):
        blocked.clear(); blocked.update(base_blocked)
        halo=set(); stub={}; line={}; fail=None
        rest=[c for c in sorted(allcaps,key=freecnt) if c not in prio]
        for c in prio+rest:
            prev={c:None}; dq=deque([c]); found=None
            while dq:
                v=dq.popleft()
                if dS[v]==FAR and v not in halo:
                    Lp=line_from(v,HMAX-1)
                    if Lp is not None and all((q not in blocked and q not in halo) for q in Lp[1:]):
                        found=v; break
                if dS[v]>FAR+2: continue
                for w_ in nbrs(v):
                    if w_ in prev or w_ not in dS or w_ in blocked: continue
                    prev[w_]=v; dq.append(w_)
            if found is None: fail=c; break
            p=[found]
            while prev[p[-1]] is not None: p.append(prev[p[-1]])
            stub[c]=p[::-1]; line[c]=Lp
            for q in stub[c]+Lp: blocked.add(q)
            for q in Lp:
                halo.add(q)
                for w_ in nbrs(q): halo.add(w_)
        if fail is None: break
        assert fail not in prio,("cap fails even with top priority",fail)
        prio.insert(0,fail)
    else: raise SystemExit("stub placement failed")
    print("  (%d priority restarts)"%len(prio))
    print("stubs and straight columns placed, %.0fs"%(time.time()-t0))
    linkpaths=[]
    for i,(a,b) in enumerate(pairs):
        h=alt[a]
        ia=next(k for k,q in enumerate(line[a]) if dS[q]==h); ib=next(k for k,q in enumerate(line[b]) if dS[q]==h)
        src=line[a][ia]; dst=line[b][ib]
        prev={src:None}; dq=deque([src])
        while dq:
            v=dq.popleft()
            if v==dst: break
            for w_ in nbrs(v):
                if w_ in prev or w_ not in dS: continue
                if w_!=dst and (w_ in blocked or not (h<=dS[w_]<=h+1)): continue
                prev[w_]=v; dq.append(w_)
        assert dst in prev,("arc failed",order[i][0],order[i+1][0],h)
        mid=[dst]
        while prev[mid[-1]] is not None: mid.append(prev[mid[-1]])
        mid=mid[::-1]
        for q in mid: blocked.add(q)
        p=stub[a]+line[a][1:ia+1]+mid[1:-1]+line[b][1:ib+1][::-1]+stub[b][::-1]
        assert len(set(p))==len(p),"self-crossing linker"
        linkpaths.append(p)
    return linkpaths
order=units+sep_units+track_units+ring_units+bulk_units
linkpaths=route_all(order,set(blocked))
chain=[]
for i,(nm,u) in enumerate(order):
    if i>0: chain+=[(q,'P') for q in linkpaths[i-1][1:-1]]
    chain+=u
print("routing done, %.0fs ; %d linkers, one shell each"%(time.time()-t0,len(linkpaths)))
# ---------- verification
sites=[p for p,l in chain]; seq=''.join(l for p,l in chain)
assert len(set(sites))==len(sites),"chain revisits a site"
assert all(sites[i+1] in nbrs(sites[i]) for i in range(len(sites)-1)),"chain is not a lattice walk"
H=set(p for p,l in chain if l=='H'); assert H==S,"H sites are not exactly the octahedron"
bonds=edges(H); bound=2*N-2*m*m
print("chain length %d (H: %d, P: %d)"%(len(seq),seq.count('H'),seq.count('P')))
print("H-H bonds in this fold: %d ; proved upper bound 2N-2m^2: %d ; OPTIMAL: %s"%(bonds,bound,bonds==bound))
runs=Counter(len(r) for r in re.findall('H+',seq)); pr=Counter(len(r) for r in re.findall('P+',seq))
print("H-run lengths:",dict(sorted(runs.items())))
print("P-run lengths <= 10:",{k:v for k,v in sorted(pr.items()) if k<=10})
print("PHP count:",len(re.findall('(?=PHP)',seq)),"; HPH:",'HPH' in seq,"; HPPH:",'HPPH' in seq)
for nm,u in sep_units+track_units: print("  unit:",nm)
open('/home/claude/work/demo2_fold_string.txt','w').write(seq+"\n")
open('/home/claude/work/demo2_fold_coords.txt','w').write(''.join('%d %d %d %s\n'%(p[0],p[1],p[2],l) for p,l in chain))
