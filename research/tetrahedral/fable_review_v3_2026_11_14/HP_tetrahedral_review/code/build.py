"""Explicit fold for one instance of the reduction (design of notes section 10A).
Instance: K=1 bin of capacity 6 dimers, items of sizes 3 and 3 (sizes already scaled by lambda=3)."""
import sys, itertools, time
from collections import deque, Counter
from geom import *
from bulk import bulk_cover

m=26; CAP=6; ITEMS=[3,3]; TSTAR=[8,16]            # separators at b-index t*; TSTAR[1]=TSTAR[0]+CAP+2
P1=[(5,7),(11,13)]                                 # e1 port pairs (b-index from V_a)
P2=[(12,15),(5,8)]                                 # e2 port pairs (b-index from V_c), one per separator
t0=time.time()
G=Geo(m,margin=72); S=G.S; N=len(S)
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MAJ='A' if sum(1 for v in S if sub(v)=='A')>N/2 else 'B'
is_maj=lambda v: sub(v)==MAJ
tris=G.small_face_triples()
small=[t for t in tris if t[3]=='small']
Va,Vb,Vc=small[0][0],small[0][1],small[0][2]
e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc)
alledges=[G.edge(V,W) for V,W in itertools.combinations(G.vertices,2) if G.edge(V,W)]
E=set(v for e in alledges for v in e)
L=len(e1)
def bidx(e,s): return e[2*s+1]
def aidx(e,j): return e[2*j]
def cap(u,avoid=()):
    c=[d for d in G.dang[u] if d not in avoid]; assert c,("no free dangling site",u); return c[0]
def ppp(u,w):
    for du in G.dang[u]:
        for x in nbrs(du):
            if x in S: continue
            for dw in G.dang[w]:
                if dw!=du and dw in nbrs(x): return (du,x,dw)
    raise Exception("no PPP link %s %s"%(u,w))
units=[]          # each: list of (site,letter)
# ---------- terminal 1 on the stuck corner
Ub=e1[-2]; assert Ub==e2[1]
units.append(("terminal1",[(Ub,'H'),(cap(Ub),'P')]))
# ---------- three isolated PHP's
for W in G.vertices:
    if W in (Va,Vb,Vc): continue
    d=G.dang[W]; units.append(("PHP",[(d[0],'P'),(W,'H'),(d[1],'P')]))
# ---------- frame chain
def frame_runs(e,ports):
    """runs of the frame along zigzag e (from its first vertex), skipping b-ports (indices from first vertex)"""
    runs=[]; j=1
    while j<=m-2:
        r=[aidx(e,j)]
        while j<m-2 and j not in ports:
            r.append(bidx(e,j)); j+=1; r.append(aidx(e,j))
        runs.append(r); j+=1
    return runs
ports1=set(s for p in P1 for s in p)
ports2=set((m-2)-s for p in P2 for s in p)        # as indices from V_b along e2
fr=[]
l1=ppp(Va,aidx(e1,1)); fr.append((cap(Va,avoid=(l1[0],)),'P')); fr.append((Va,'H'))
prev=Va
for e,ports,Vend in ((e1,ports1,Vb),(e2,ports2,Vc)):
    for r in frame_runs(e,ports):
        fr+= [(p,'P') for p in ppp(prev,r[0])]; fr+=[(v,'H') for v in r]; prev=r[-1]
    fr+=[(p,'P') for p in ppp(prev,Vend)]; fr.append((Vend,'H')); prev=Vend
used_c=[p for p,l in fr if l=='P']
fr.append((cap(Vc,avoid=used_c),'P'))
units.append(("frame",fr))
frame_sites=set(p for p,l in fr if l=='H')
port_sites=[bidx(e1,s) for s in ports1]+[bidx(e2,j) for j in ports2]
assert all(p not in frame_sites for p in port_sites)
# ---------- staples
def sp(a,b,forbid):
    prev={a:None}; dq=deque([a])
    while dq:
        v=dq.popleft()
        if v==b: break
        for w in nbrs(v):
            if w in S and w not in prev and (w==b or w not in forbid): prev[w]=v; dq.append(w)
    p=[b]
    while prev[p[-1]] is not None: p.append(prev[p[-1]])
    return p[::-1]
staple_sites=set()
st1=[]; st2=[]
e2c=e2[::-1]
for (s,s_) in P1:
    p=sp(bidx(e1,s_),bidx(e1,s),E|staple_sites); assert len(p)==7; st1.append(p); staple_sites|=set(p)   # ends at the flank port s
for (s,s_) in P2:
    p=sp(bidx(e2c,s),bidx(e2c,s_),E|staple_sites); assert len(p)==9; st2.append(p); staple_sites|=set(p)  # starts at the flank port s
# ---------- track layout
z=e3
def dimer_chain(seq_pairs):
    """seq_pairs: list of (enter,exit) bonded pairs; consecutive linked by PPP exit_i -> enter_{i+1}"""
    out=[(cap(seq_pairs[0][0]),'P')]
    for i,(x,y) in enumerate(seq_pairs):
        assert y in nbrs(x)
        out+=[(x,'H'),(y,'H')]
        if i+1<len(seq_pairs): out+=[(p,'P') for p in ppp(y,seq_pairs[i+1][0])]
    out.append((cap(seq_pairs[-1][1]),'P'))
    return out
def chain_from(sites,first_is_b):
    """consecutive zigzag sites (even count) -> dimer chain with alternating traversal"""
    pairs=[]
    for i in range(0,len(sites),2):
        x,y=sites[i],sites[i+1]
        pairs.append((x,y) if (i//2)%2==0 else (y,x))
    return dimer_chain(pairs)
c1=2*TSTAR[0]; c2=2*TSTAR[1]
left=[z[i] for i in range(1,c1-1)]; bstar=z[c1-1]
binsites=[z[i] for i in range(c1+4,c2)]
right=[z[i] for i in range(c2+4,2*m-2)]
assert len(binsites)==2*CAP and len(left)%2==0 and len(right)%2==0
track_units=[]
pos=0
for sz in ITEMS:
    track_units.append(("item(%d)"%sz,chain_from(binsites[pos:pos+2*sz],False))); pos+=2*sz
track_units.append(("filler-left(%d)"%(len(left)//2),chain_from(left,True)))
track_units.append(("filler-right(%d)"%(len(right)//2),chain_from(right,False)))
# ---------- rings
ring_units=[]
for (A_,B_,C_,kind,n_) in small[1:]:
    ring=[]
    for V,W in ((A_,B_),(B_,C_),(C_,A_)):
        ring+=G.edge(V,W)[1:2*m-3]
    assert len(ring)==6*(m-2)
    ring_units.append(("filler-ring(%d)"%(len(ring)//2),chain_from(ring,True)))
dimer_sites=set(p for nm,u in track_units+ring_units for p,l in u if l=='H')
# ---------- separator groups (tethers routed later)
sepdefs=[]
for k,t in enumerate(TSTAR):
    c=2*t
    sepdefs.append(dict(st1=st1[k],st2=st2[k],entry=z[c+1],a=z[c],a2=z[c+2],exit=z[c+3],g=2*t+3,gp=2*(m-2-t)+1))
    dimer_sites|={z[c],z[c+1],z[c+2],z[c+3]}
# ---------- bookkeeping of H coverage so far
assert E-set(G.vertices)-frame_sites-set(port_sites)-dimer_sites-{Ub,bstar}==set(), "edge sites not all assigned"
X=S-E-staple_sites
elig=set(v for v in X if is_maj(v) and G.dang[v])
nP=sum(1 for v in X if is_maj(v))-sum(1 for v in X if not is_maj(v))
print("m=%d N=%d ; bulk sites %d ; odd Maj-Maj bulk runs needed (imbalance) %d ; predicted by identity %d"%(m,N,len(X),nP,m-6-5-5+4+2))
paths=bulk_cover(X,is_maj,elig,nP,seed=3)
assert paths is not None
bulk_units=[("bulk(%d)"%len(p),[(cap(p[0]),'P')]+[(v,'H') for v in p]+[(cap(p[-1]),'P')]) for p in paths]
print("bulk cover done, %.0fs"%(time.time()-t0))
# ---------- reserved P sites
reserved=set()
def reserve(u):
    for p,l in u:
        if l=='P':
            assert p not in reserved and p not in S,("P clash",p); reserved.add(p)
for nm,u in units+track_units+ring_units+bulk_units: reserve(u)
sep_fixed=[]
for d in sepdefs:
    link=ppp(d['a'],d['a2'])
    fixedP=[cap(d['st1'][0]),cap(d['st1'][-1]),cap(d['entry'])]+list(link)+[cap(d['exit']),cap(d['st2'][0]),cap(d['st2'][-1])]
    for p in fixedP:
        assert p not in reserved and p not in S,("P clash sep",p); reserved.add(p)
    d['link']=link
capT2=cap(bstar); assert capT2 not in reserved; reserved.add(capT2)
# ---------- routing
blocked=set(reserved)
def bfs(src,dst):
    prev={src:None}; dq=deque([src])
    while dq:
        v=dq.popleft()
        if v==dst: break
        for w in nbrs(v):
            if w in prev or w in S or not G.inbox(w): continue
            if w in blocked and w!=dst: continue
            prev[w]=v; dq.append(w)
    if dst not in prev: return None
    p=[dst]
    while prev[p[-1]] is not None: p.append(prev[p[-1]])
    return p[::-1]
def pad(path,n):
    path=list(path)
    while len(path)<n:
        done=False
        for i in range(len(path)-2):
            u,v,w=path[i],path[i+1],path[i+2]
            onp=set(path)
            for a in nbrs(u):
                if a==v or a in S or a in blocked or a in onp: continue
                for b in nbrs(a):
                    if b==u or b in S or b in blocked or b in onp: continue
                    for c in nbrs(b):
                        if c==a or c in S or c in blocked or c in onp: continue
                        if w in nbrs(c):
                            path[i+1:i+2]=[a,b,c]; done=True; break
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
def route_free(src,dst):
    p=bfs(src,dst); assert p is not None,"linker routing failed"
    for q in p: blocked.add(q)
    return p
sep_units=[]
for k,d in enumerate(sepdefs):       # exit tethers first
    d['tout']=route_exact(cap(d['exit']),cap(d['st2'][0]),d['gp'])
for k,d in enumerate(sepdefs):
    d['tin']=route_exact(cap(d['st1'][-1]),cap(d['entry']),d['g'])
for k,d in enumerate(sepdefs):
    u=[(cap(d['st1'][0]),'P')]+[(v,'H') for v in d['st1']]+[(p,'P') for p in d['tin']]
    u+=[(d['entry'],'H'),(d['a'],'H')]+[(p,'P') for p in d['link']]+[(d['a2'],'H'),(d['exit'],'H')]
    u+=[(p,'P') for p in d['tout']]+[(v,'H') for v in d['st2']]+[(cap(d['st2'][-1]),'P')]
    sep_units.append(("separator%d (tethers P^%d, P^%d)"%(k+1,d['g'],d['gp']),u))
order=units+sep_units+track_units+ring_units+bulk_units+[("terminal2",[(capT2,'P'),(bstar,'H')])]
# distance of outside sites from S
dS={}; dq=deque()
for v in S:
    for w in nbrs(v):
        if w not in S and w not in dS: dS[w]=1; dq.append(w)
while dq:
    v=dq.popleft()
    for w in nbrs(v):
        if w not in S and w not in dS and G.inbox(w): dS[w]=dS[v]+1; dq.append(w)
FAR=5
def escape(c,h):
    prev={c:None}; dq=deque([c])
    while dq:
        v=dq.popleft()
        if dS.get(v,0)>=h:
            p=[v]
            while prev[p[-1]] is not None: p.append(prev[p[-1]])
            return p[::-1]
        for w in nbrs(v):
            if w in prev or w in S or w in blocked or not G.inbox(w): continue
            prev[w]=v; dq.append(w)
    return None
def outer(src,dst,h):
    prev={src:None}; dq=deque([src])
    while dq:
        v=dq.popleft()
        if v==dst: break
        for w in nbrs(v):
            if w in prev or w in S or not G.inbox(w): continue
            if w!=dst and (w in blocked or not (h<=dS.get(w,0)<=h+1)): continue
            prev[w]=v; dq.append(w)
    if dst not in prev: return None
    p=[dst]
    while prev[p[-1]] is not None: p.append(prev[p[-1]])
    return p[::-1]
pairs=[(order[i-1][1][-1][0],order[i][1][0][0]) for i in range(1,len(order))]
alt={}
for i,(a,b) in enumerate(pairs): alt[a]=alt[b]=FAR+2*i
allcaps=[c for pr_ in pairs for c in pr_]
freecnt=lambda c: sum(1 for w in nbrs(c) if w not in S and w not in blocked)
esc={}
for c in sorted(allcaps,key=lambda c:(freecnt(c),alt[c])):
    p=escape(c,alt[c])
    if p is None:
        print("FAILED escape for cap",c,[("S" if w in S else "blocked" if w in blocked else "free") for w in nbrs(c)]); raise SystemExit
    esc[c]=p
    for q in p: blocked.add(q)
chain=[]; linkers=[]
for i,(nm,u) in enumerate(order):
    if i>0:
        a,b=pairs[i-1]
        mid=outer(esc[a][-1],esc[b][-1],alt[a])
        if mid is None: print("FAILED outer route between",order[i-1][0],"and",nm); raise SystemExit
        for q in mid: blocked.add(q)
        p=esc[a]+mid[1:-1]+esc[b][::-1]
        linkers.append(len(p))
        chain+=[(q,'P') for q in p[1:-1]]
    chain+=u
print("routing done, %.0fs"%(time.time()-t0))
# ---------- verification
sites=[p for p,l in chain]; seq=''.join(l for p,l in chain)
assert len(set(sites))==len(sites),"chain revisits a site"
assert all(sites[i+1] in nbrs(sites[i]) for i in range(len(sites)-1)),"chain is not a lattice walk"
H=set(p for p,l in chain if l=='H')
assert H==S,"H sites are not exactly the octahedron"
bonds=edges(H); bound=2*N-2*m*m
print("chain length %d (H: %d, P: %d)"%(len(seq),seq.count('H'),seq.count('P')))
print("H-H bonds in this fold: %d ; proved upper bound 2N-2m^2: %d ; OPTIMAL: %s"%(bonds,bound,bonds==bound))
import re
runs=Counter(len(r) for r in re.findall('H+',seq)); pr=Counter(len(r) for r in re.findall('P+',seq))
print("H-run lengths:",dict(sorted(runs.items())))
print("short P-run lengths (<=3):",{k:v for k,v in sorted(pr.items()) if k<=3},"; linker lengths range %d..%d"%(min(linkers),max(linkers)))
print("PHP count:",len(re.findall('(?=PHP)',seq)),"; HPH:",'HPH' in seq,"; HPPH:",'HPPH' in seq)
for nm,u in order[:1]+sep_units+track_units: print("  unit:",nm)
open('/home/claude/work/demo_fold_string.txt','w').write(seq+"\n")
open('/home/claude/work/demo_fold_coords.txt','w').write(''.join('%d %d %d %s\n'%(p[0],p[1],p[2],l) for p,l in chain))
