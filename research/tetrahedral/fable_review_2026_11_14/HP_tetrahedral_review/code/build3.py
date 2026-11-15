"""Fold builder for the design of notes 10.7 (checkpoint 16):
   canonical bulk cover (10.4.1), columns = outward foliation arms, margin tethers in private skins,
   one private cylinder shell per long linker.  Usage: build3.py m CAP "PACK" [J1] [nochain]
   Fixed labelling (coordinates of 5.1/5.6): F' = small face 4, e1 = E(3,4), e2 = E(1,4), track e3 = E(2,4)."""
import sys, itertools, time, re
import os as _os
WORK=_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__)))     # output goes next to the code directory
from collections import deque, Counter
import diamond as dm
from canon import *
from canon_patches import PATCH
m=int(sys.argv[1]) if len(sys.argv)>1 else 40
CAP=int(sys.argv[2]) if len(sys.argv)>2 else 4
arg3=sys.argv[3] if len(sys.argv)>3 else "[[2,2]]"
if ';' in arg3:                                      # "ITEMS;ASSIGN": item sizes in string order ; bins as lists of item indices
    ITEMS=eval(arg3.split(';')[0]); ASSIGN=eval(arg3.split(';')[1])
else:                                                # bins as lists of sizes; string order = order along the track
    PACK=eval(arg3); ITEMS=[x for b in PACK for x in b]; ASSIGN=[]; i_=0
    for b in PACK: ASSIGN.append(list(range(i_,i_+len(b)))); i_+=len(b)
K=len(ASSIGN); assert sorted(i for b in ASSIGN for i in b)==list(range(len(ITEMS)))
assert all(sum(ITEMS[i] for i in b)==CAP for b in ASSIGN) and CAP%2==0 and all(x%2==0 for x in ITEMS)
J1=int(sys.argv[4]) if len(sys.argv)>4 else 2*((5*K+11)//2)
CHAIN=not (len(sys.argv)>5 and sys.argv[5]=="nochain")
RFLIP=int(sys.argv[6]) if len(sys.argv)>6 else 0
LMODE=sys.argv[7] if len(sys.argv)>7 else "natural"
TAG=sys.argv[8] if len(sys.argv)>8 else 'demo4_m%d'%m
assert J1%2==0
JS=[J1+k*(CAP+2) for k in range(K+1)]
R=(m-2)-(JS[-1]+1); assert R>=4,("track too short",R)
SL1=[3*(k+1) for k in range(K+1)]; SL2=[5*k+3 for k in range(K+1)]
t0=time.time()
G,S,E,X,nb,Y,Z,rho,alpha,adj,legit,merges=cover(m,PATCH)
msg,paths=validate(X,adj,legit); assert msg=="valid",msg
N=len(S); cc=(0,2*m-2,0)
fco=lambda v: tuple(sum(T[j][i]*(v[i]-cc[i]) for i in range(3)) for j in range(4))
isA=lambda v: sum(v)%4==0
def skin(v):
    f=fco(v)
    if isA(v): return max(0,-(-(max(abs(x) for x in f)-(2*m-2))//4))
    return max(0,-(-(max(f)-(2*m-3))//4),-(-(-min(f)-(2*m-1))//4))
Va,Vb,Vc=(0,2*m-2,-(2*m-2)),(0,4*m-4,0),(2*m-2,2*m-2,0)      # e1=E(3,4) (X-plane edge), e2=E(1,4), track e3=E(2,4)
e1=G.edge(Va,Vb); e2=G.edge(Vb,Vc); e3=G.edge(Va,Vc); e2c=e2[::-1]
assert e1 and e2 and e3 and e1[1]==e3[1] and e1[-2]==e2[1] and e2c[1]==e3[-2]
assert fco(e1[1])[3]==-(2*m-1)                       # the corner lies on small face 4
sgn=lambda t:(t>0)-(t<0)
NARM=4*K+40
def arm(p,n=NARM):
    out=[p]; sy,sz=sgn(Y(p)),sgn(Z(p))
    if sy==0 or sz==0:
        f=G.face_of[p]; sy=sy or sgn(f[1]); sz=sz or sgn(f[2])
    for _ in range(n):
        cur=out[-1]; nx=[w for w in nbrs(cur) if (Y(w)-Y(cur),Z(w)-Z(cur))==(sy,sz)]
        assert len(nx)==1; out.append(nx[0])
    return out
ARM={p:arm(p) for p in G.owner}                      # arms of all dangling sites
armowner={}
for p,a in ARM.items():
    for q in a:
        assert q not in S and q not in armowner; armowner[q]=p
print("m=%d: %d dangling sites, arms pairwise disjoint up to %d steps ; bulk paths %d ; %.0fs"%(m,len(ARM),NARM,len(paths),time.time()-t0))
reserved={}                                          # P site -> label
def res(ps,label):
    for p in ps:
        assert p not in S and p not in reserved,("P clash",p,label,reserved.get(p)); reserved[p]=label
def res_item(ps,label):                              # items may use the sites set aside for them ("zone")
    for p in ps:
        assert p not in S and reserved.get(p,"zone")=="zone",("P clash",p,label,reserved.get(p)); reserved[p]=label
def zres(ps):
    for p in ps:
        assert p not in S and reserved.get(p,"zone")=="zone",("zone clash",p,reserved.get(p)); reserved[p]="zone"
potcaps=set()                                        # caps of track a-sites inside the bins: possible item ends
def cap(u,avoid=()):
    c=[d for d in G.dang[u] if d not in avoid]; assert c,("no free dangling site",u); return c[0]
linkercaps=set()                                     # caps whose column is needed
INF=10**9
armuse={}                                            # arm (named by its dangling site) -> skin up to which it is used
COL={}
def getcol(c,upto=INF):
    """column of cap c: its own arm, or (if the second site is taken by a frame link) the arm of an unused neighbour"""
    if c in COL: return COL[c]
    if ARM[c][1] not in reserved and c not in armuse:
        armuse[c]=upto; COL[c]=ARM[c]; return COL[c]
    for q in nbrs(c):
        o=armowner.get(q)
        if q in S or q in reserved or o is None or ARM[o][1]!=q or o==c: continue
        if o in reserved or o in armuse or o in linkercaps or o in bulkcapset or o in potcaps: continue
        if any(x in reserved for x in ARM[o][1:]): continue
        armuse[o]=upto; COL[c]=[c]+ARM[o][1:]; return COL[c]
    raise Exception("no column for cap %s (owner %s)"%(c,G.owner[c]))
def ppp(u,w):
    r=[(du,x,dw) for du in G.dang[u] for x in nbrs(du) if x not in S for dw in G.dang[w] if dw!=du and dw in nbrs(x)]
    assert len(r)==1,("no unique PPP link",u,w); return r[0]
units=[]
# ---------- bulk run ends and their caps
bulkends=set(v for p in paths for v in (p[0],p[-1]))
bulkcaps={v:cap(v) for v in bulkends}
# ---------- frame
L=2*m-2
skip1={1,2}|{2*m-3}
for s in SL1: skip1|={2*s,2*s+1}
skip2c={1}|{2*m-3}
for s in SL2: skip2c|=set(range(2*s,2*s+6))
skip2={L-i for i in skip2c}
Ub=e1[-2]
slot_sites=[e1[i] for i in skip1 if i not in (1,2,2*m-3)]+[e2c[i] for i in skip2c if i not in (1,2*m-3)]
keepown=set(cap(z) for z in slot_sites)|{cap(e1[1]),cap(e1[2]),cap(e2c[1]),cap(Ub)}
bulkcapset=set(bulkcaps.values())
forbid_weak=keepown|bulkcapset|set(ARM[c][1] for c in bulkcapset)
forbid_strict=forbid_weak|set(ARM[c][1] for c in keepown)
def link(u,w,k):
    for forbid in (forbid_strict,forbid_weak):
        for du in G.dang[u]:
            if du in reserved or du in forbid: continue
            stack=[[du]]
            while stack:
                p=stack.pop()
                if len(p)==k:
                    if p[-1] in G.dang[w]: return p
                    continue
                for y in nbrs(p[-1]):
                    if y in S or y in reserved or y in forbid or y in p: continue
                    stack.append(p+[y])
    raise Exception("no frame link %s %s %d"%(u,w,k))
def runs_of(e,skip):
    out=[]; cur=[]
    for i in range(1,L):
        if i in skip:
            if cur: out.append(cur); cur=[]
        else: cur.append(e[i])
    if cur: out.append(cur)
    return out
idx1={v:i for i,v in enumerate(e1)}; idx2={v:i for i,v in enumerate(e2)}
def flink(u,w,idx):
    c=abs(idx[w]-idx[u])-1; k=c+2 if c%2==1 else c+4
    p=link(u,w,k); res(p,"frame link"); FL.append((u,w,p)); return p
FL=[]
prev=Va; seqframe=[(Va,'H')]
for e,skip,Vend,idx in ((e1,skip1,Vb,idx1),(e2,skip2,Vc,idx2)):
    for r in runs_of(e,skip):
        assert len(r)>=3
        seqframe+=[(p,'P') for p in flink(prev,r[0],idx)]+[(v,'H') for v in r]; prev=r[-1]
    seqframe+=[(p,'P') for p in flink(prev,Vend,idx)]+[(Vend,'H')]; prev=Vend
usedP=set(p for p,l in seqframe if l=='P')
ca=cap(Va,avoid=usedP); cb=cap(Vc,avoid=usedP); res([ca,cb],"frame end cap"); linkercaps|={ca,cb}
frame_unit=("frame",[(ca,'P')]+seqframe+[(cb,'P')])
frame_sites=set(p for p,l in seqframe if l=='H')
print("frame built: links",dict(Counter(len(x) for x in re.findall('P+',''.join(l for p,l in seqframe)))),"; max skin of a frame link site:",max(skin(p) for p in usedP),"%.0fs"%(time.time()-t0))
# ---------- terminal and the three isolated PHP's
c0=cap(Ub); res([c0],"terminal cap"); linkercaps.add(c0)
units.append(("terminal",[(Ub,'H'),(c0,'P')]))
for W in G.vertices:
    if W in (Va,Vb,Vc): continue
    d=G.dang[W]; res(d,"PHP cap"); linkercaps|=set(d)
    units.append(("PHP",[(d[0],'P'),(W,'H'),(d[1],'P')]))
units.append(frame_unit)
# ---------- dimer chains
def dimer_chain(pairs,rs=res):
    out=[]
    for i,(x,y) in enumerate(pairs):
        assert y in nbrs(x); out+=[(x,'H'),(y,'H')]
        if i+1<len(pairs):
            l=ppp(y,pairs[i+1][0]); rs(l,"P3 link"); out+=[(p,'P') for p in l]
    return out
def alt_pairs(sites,flip=0):
    return [((sites[i],sites[i+1]) if ((i//2)+flip)%2==0 else (sites[i+1],sites[i])) for i in range(0,len(sites),2)]
def with_caps(body):
    a=cap(body[0][0],avoid=reserved); res([a],"chain cap"); b=cap(body[-1][0],avoid=reserved); res([b],"chain cap")
    linkercaps.add(a); linkercaps.add(b)
    return [(a,'P')]+body+[(b,'P')]
z=e3
D=[(e1[2],e1[1])]+[(z[2*j],z[2*j+1]) for j in range(1,m-1)]
def flat(a,b): return [s for j in range(a,b) for s in D[j]]
left_unit=("filler-left(%d)"%J1,with_caps(dimer_chain(alt_pairs(flat(0,J1)))))
right_unit=("filler-right(%d)"%R,with_caps(dimer_chain(alt_pairs(flat(JS[-1]+2,m-1)))))
# everything an item could occupy is set aside now, so that the rest of the construction does not depend on the packing
for k in range(K):
    for o in range(CAP): potcaps.add(G.dang[D[JS[k]+2+o][0]][0])
for c in sorted(potcaps): getcol(c)
for k in range(K):
    lo=JS[k]+2
    for o in range(CAP):
        a_,b_=D[lo+o]; zres([G.dang[a_][0]])
        if o%2==0: zres(ppp(b_,D[lo+o+1][1]))
        elif o+1<CAP: zres(ppp(a_,D[lo+o+1][0]))
ring_units=[]
others=[V for V in G.vertices if V not in (Va,Vb,Vc)]
for tri in G.small_face_triples():
    A_,B_,C_,kind,n_=tri
    if kind!='small' or set((A_,B_,C_))=={Va,Vb,Vc}: continue
    sides=[G.edge(V,W)[1:2*m-3] for V,W in ((A_,B_),(B_,C_),(C_,A_))]
    if m%2==0:
        ring=sides[0]+sides[1]+sides[2]
        ring_units.append(("filler-ring(%d)"%(len(ring)//2),with_caps(dimer_chain(alt_pairs(ring)))))
    else:                                            # odd m: the alternation does not close at the corners; one chain per side
        for sd in sides:
            ring_units.append(("filler-ringside(%d)"%(len(sd)//2),with_caps(dimer_chain(alt_pairs(sd,RFLIP)))))
# ---------- separator groups
seps=[]
for k in range(K+1):
    j=JS[k]; s=SL1[k]; s2=SL2[K-k]
    A=(e1[2*s],e1[2*s+1])
    sep=dimer_chain([(z[2*j+1],z[2*j]),(z[2*j+2],z[2*j+3])])
    w=[e2c[i] for i in range(2*s2,2*s2+6)]
    X3=dimer_chain([(w[1],w[0]),(w[2],w[3]),(w[5],w[4])])
    cA0=cap(A[0]); cX1=cap(w[4]); res([cA0,cX1],"anchor linker cap"); linkercaps|={cA0,cX1}
    seps.append(dict(A=A,sep=sep,X3=X3,cA0=cA0,cX1=cX1,tA=cap(A[1]),tS0=cap(z[2*j+1]),tS1=cap(z[2*j+3]),tX=cap(w[1]),j=j,s=s,s2=s2))
assigned=frame_sites|set(G.vertices)|{Ub}|set(p for nm,u in [left_unit,right_unit]+ring_units for p,l in u if l=='H')|set(x for k in range(K) for x in flat(JS[k]+2,JS[k+1]))
for d in seps: assigned|=set(d['A'])|set(p for p,l in d['sep']+d['X3'] if l=='H')
assert E-assigned==set() and len(assigned)==len(E)
# ---------- margin tethers: riser on the own column, corridor in a private skin over F', descent on the own column
edgeb=set(v for e in (e1,e2,e3) for v in e if not isA(v))
def onF(v,j):
    M=m+2*j; f=fco(v)
    return skin(v)==j and (f[3]==-(2*M-2) if isA(v) else f[3]==-(2*M-1))
row2=set(v for v in S if not isA(v) and fco(v)[3]==-(2*m-1) and fco(v)[2]==2*m-7)     # second row of F' along e1=E(3,4)
assert not (row2&bulkends),"second-row sites along the X-plane edge should never be run ends"
for c in sorted(linkercaps): getcol(c)                                              # linker columns fixed before the tethers
def corridor_ok(v,j,own):
    if not onF(v,j) or v in reserved: return False
    o=armowner.get(v)
    if o is None or o in own: return True
    if o in linkercaps or o in bulkcapset or o in potcaps or armuse.get(o,0)>=j: return False
    return G.owner[o] in edgeb or G.owner[o] in row2
def tether(c1,c2,j,label):
    a1=getcol(c1,j); a2=getcol(c2,j); own={armowner.get(a1[1]),armowner.get(a2[1])}
    src=a1[2*j-2]; dst=a2[2*j-2]
    prev={src:None}; dq=deque([src])
    while dq:
        v=dq.popleft()
        if v==dst: break
        for w_ in nbrs(v):
            if w_ in prev or not corridor_ok(w_,j,own): continue
            prev[w_]=v; dq.append(w_)
    assert dst in prev,("no corridor path",label,j)
    midp=[dst]
    while prev[midp[-1]] is not None: midp.append(prev[midp[-1]])
    p=a1[:2*j-2]+midp[::-1]+a2[:2*j-2][::-1]
    assert len(set(p))==len(p)
    res(p,label); return p
ESK=[2+k for k in range(K+1)]; XSK=[K+3+k for k in range(K+1)]
for k,d in enumerate(seps):                           # declare all tether columns first (they block lower skins of other tethers)
    getcol(d['tA'],ESK[k]); getcol(d['tS0'],ESK[k]); getcol(d['tS1'],XSK[k]); getcol(d['tX'],XSK[k])
for k,d in enumerate(seps): d['tin']=tether(d['tA'],d['tS0'],ESK[k],"entry tether %d"%k)
for k,d in enumerate(seps): d['tout']=tether(d['tS1'],d['tX'],XSK[k],"exit tether %d"%k)
sep_units=[]
for k,d in enumerate(seps):
    u=[(d['cA0'],'P'),(d['A'][0],'H'),(d['A'][1],'H')]+[(p,'P') for p in d['tin']]+d['sep']+[(p,'P') for p in d['tout']]+d['X3']+[(d['cX1'],'P')]
    taut_in=2*d['j']+3; taut_out=2*(m-2-d['j'])+3
    print("  separator %d on track dimers %d,%d: entry tether P^%d (taut %d, slack %d, skin %d) ; exit tether P^%d (taut %d, slack %d, skin %d)"%(k+1,d['j'],d['j']+1,len(d['tin']),taut_in,len(d['tin'])-taut_in,ESK[k],len(d['tout']),taut_out,len(d['tout'])-taut_out,XSK[k]))
    sep_units.append(("anchor(1) P^%d separator(2) P^%d anchor(3)"%(len(d['tin']),len(d['tout'])),u))
print("tethers routed in margins, %.0fs"%(time.time()-t0))
# ---------- bulk units: optional chaining of run ends by P^3 links
endof={}
for i,p in enumerate(paths): endof[p[0]]=(i,0); endof[p[-1]]=(i,1)
par=list(range(len(paths)))
def find(x):
    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
    return x
joined={}                                            # end site -> (other end site, link)
if CHAIN:
    for v in sorted(bulkends):
        if v in joined: continue
        for dv in G.dang[v]:
            for x in nbrs(dv):
                if x in S or x in reserved or v in joined: continue
                for dw in nbrs(x):
                    w=G.owner.get(dw)
                    if w is None or w==v or w not in bulkends or w in joined or v in joined: continue
                    if find(endof[v][0])==find(endof[w][0]): continue
                    o=armowner.get(x)
                    if o not in (dv,dw) and (o in bulkcapset or o in linkercaps or o in potcaps or o in reserved): continue
                    if dv in reserved or dw in reserved: continue
                    res([dv,x,dw],"bulk P3 link"); joined[v]=(w,(dv,x,dw)); joined[w]=(v,(dw,x,dv)); par[find(endof[v][0])]=find(endof[w][0])
bulk_units=[]; seenp=set()
for i in range(len(paths)):
    if i in seenp: continue
    cur=i; sd_=0
    while paths[cur][0 if sd_==0 else -1] in joined:
        w,_=joined[paths[cur][0 if sd_==0 else -1]]; cur,sd=endof[w]; sd_=1-sd
    ent=sd_; body=[]; c_first=bulkcaps[paths[cur][0 if ent==0 else -1]]
    while True:
        seenp.add(cur); pth=paths[cur] if ent==0 else paths[cur][::-1]
        body+=[(v,'H') for v in pth]; last=pth[-1]
        if last in joined:
            w,l=joined[last]; body+=[(q,'P') for q in l]; cur,ent=endof[w]
        else: break
    c_last=bulkcaps[last]
    res([c_first,c_last],"bulk cap"); linkercaps|={c_first,c_last}
    bulk_units.append(("bulk(%d H)"%sum(1 for q,l in body if l=='H'),[(c_first,'P')]+body+[(c_last,'P')]))
assert sum(1 for nm,u in bulk_units for q,l in u if l=='H')==len(X)
print("bulk: %d runs in %d units (chaining %s), %.0fs"%(len(paths),len(bulk_units),CHAIN,time.time()-t0))
# ---------- items (the only part that depends on the packing)
item_units={}
for k in range(K):
    pos=JS[k]+2
    for idx in ASSIGN[k]:
        sz=ITEMS[idx]; body=dimer_chain(alt_pairs(flat(pos,pos+sz)),rs=res_item)
        a=G.dang[body[0][0]][0]; b=G.dang[body[-1][0]][0]; res_item([a,b],"item cap"); linkercaps|={a,b}; assert a in potcaps and b in potcaps
        item_units[idx]=("item %d (size %d) in bin %d, track dimers %d..%d"%(idx+1,sz,k+1,pos,pos+sz-1),[(a,'P')]+body+[(b,'P')]); pos+=sz
    assert pos==JS[k+1]
track_units=[left_unit]+[item_units[i] for i in range(len(ITEMS))]+[right_unit]
# ---------- near-field check: every linker cap has a free column, columns pairwise disjoint
for c in sorted(linkercaps): getcol(c)
colsite={}
bad=[]
for c in linkercaps:
    for q in COL[c][1:]:
        if reserved.get(q,"zone")!="zone": bad.append((c,q,reserved[q]))
        assert q not in colsite and q not in S; colsite[q]=c
borrowed=sum(1 for c in linkercaps if COL[c][1]!=ARM[c][1])
print("linker caps: %d (borrowed columns: %d) ; columns blocked by near-field P's: %d"%(len(linkercaps),borrowed,len(bad)))
for b in bad[:10]: print("   blocked:",b, "owner",G.owner[b[0]])
if bad: raise SystemExit("near field not consistent")
order=units+sep_units+track_units+ring_units+bulk_units
print("near field done: %d units, %d P sites reserved, %.0fs"%(len(order),len(reserved),time.time()-t0))
import os
if os.environ.get('NCHECK'):
    # ---- Lemma N, new checks: the objects attached to the slots are translates of each other
    rel=lambda q,o: tuple(q[i]-o[i] for i in range(3))
    def classes(items):
        cl={}
        for key,sh in items: cl.setdefault(sh,[]).append(key)
        return sorted(cl.values())
    l1=[(idx1[u]//6+1,tuple(rel(q,u) for q in p)) for u,w,p in FL if u in idx1 and w in idx1 and idx1[w]-idx1[u]==3]
    l2=[((L-idx2[w])//10,tuple(rel(q,w) for q in p)) for u,w,p in FL if u in idx2 and w in idx2 and abs(idx2[w]-idx2[u])==7]
    oth=[(("Va" if u==Va else "Vb" if u==Vb else "e"),("Vb" if w==Vb else "Vc" if w==Vc else "e"),tuple(rel(q,u) for q in p)) for u,w,p in FL if not ((u in idx1 and w in idx1 and idx1[w]-idx1[u]==3) or (u in idx2 and w in idx2 and abs(idx2[w]-idx2[u])==7))]
    print("NCHECK 2-slot links (P^%d), slots with equal shape:"%len(l1[0][1]),classes(l1))
    print("NCHECK 6-slot links (P^%d), slots (kappa from V_c) with equal shape:"%len(l2[0][1]),classes(l2))
    print("NCHECK other frame links:",[(a,b,len(sh)) for a,b,sh in oth])
    c1=[(d['s']//3,tuple((rel(COL[c][1],d['A'][0]) if c in COL else None) for c in (d['cA0'],d['tA']))+(rel(d['cA0'],d['A'][0]),rel(d['tA'],d['A'][0]))) for d in seps]
    c2=[((d['s2']-3)//5,tuple((rel(COL[c][1],d['X3'][0][0]) if c in COL else None) for c in (d['cX1'],d['tX']))+(rel(d['cX1'],d['X3'][0][0]),rel(d['tX'],d['X3'][0][0]))+tuple(rel(q,d['X3'][0][0]) for q,l in d['X3'])) for d in seps]
    print("NCHECK 2-slot anchors (caps, second column sites), slots with equal shape:",classes(c1))
    print("NCHECK 6-slot anchors (H's, PPP's, caps, second column sites), slots with equal shape:",classes(c2))
    if os.environ.get('NSHAPES'):
        print("SHAPE Lambda_2 (2-slot link, relative to its first H e1[6k-1]):",[sh for k,sh in l1 if k>=2 or len(l1)==1][-1] if len(l1)>1 else l1)
        print("SHAPE Lambda_a (V_a -> e1[3], relative to V_a):",[sh for u,w,p in FL if u==Va for sh in [tuple(rel(q,u) for q in p)]])
        print("SHAPE Lambda_6 (6-slot link, relative to its last H, the one nearer V_c):",l2[0][1])
        print("SHAPE vertex links (from, to, relative to the vertex):",[(a,b,tuple(rel(q,Vb if 'Vb' in (a,b) else Vc) for q in p)) for (a,b,sh),(u,w,p) in zip(oth,[f for f in FL if not ((f[0] in idx1 and f[1] in idx1 and idx1[f[1]]-idx1[f[0]]==3) or (f[0] in idx2 and f[1] in idx2 and abs(idx2[f[1]]-idx2[f[0]])==7))])])
        print("SHAPE 2-slot anchor: (second column site of linker cap, of tether cap, linker cap, tether cap) relative to the a-site e1[6k]:",c1[0][1])
        print("SHAPE e1[6k-1], e1[6k], e1[6k+1], e1[6k+2] relative to e1[6k]:",[rel(e1[5+t],e1[6]) for t in range(4)])
    # the shapes of Appendix C (absolute coordinates), asserted in every run
    L2_=((1,1,-1),(0,2,-2),(-1,3,-1),(0,4,0),(-1,5,1),(-2,4,2))
    LA_=((-1,1,-1),(0,2,-2),(1,3,-1),(0,4,0),(1,5,1),(2,4,2))
    L6_=((-6,8,2),(-5,9,1),(-4,8,0),(-3,7,1),(-2,6,0),(-1,5,1),(0,4,0),(1,3,1),(2,2,0),(1,1,-1))
    assert all(sh==(LA_ if u_==Va else L2_) for (u_,w_,p_),(k_,sh) in zip([f for f in FL if f[0] in idx1 and f[1] in idx1 and idx1[f[1]]-idx1[f[0]]==3],l1))
    assert all(sh==L6_ for k_,sh in l2) and len(l1)==K+2 and len(l2)==K+1
    vl=[tuple(rel(q,Vb if Vb in (u,w) else Vc) for q in p) for u,w,p in FL if Vb in (u,w) or w==Vc]
    assert vl==[((-1,-1,-3),(-2,0,-2),(-1,1,-1)),((1,1,1),(2,0,2),(3,-1,1)),((-1,3,1),(0,2,2),(1,1,1))]
    assert all(sh==((-2,0,-2),(3,3,1),(-1,1,-1),(2,2,0)) for k_,sh in c1) and len(classes(c2))==1
    print("NCHECK Appendix C shapes: OK ; all sites of frame links in skin 1:",all(skin(q)==1 for u,w,p in FL for q in p))
    slotcaps=set(d['cA0'] for d in seps)|set(d['tA'] for d in seps)
    ob=[]
    for c_ in sorted(COL):
        if COL[c_][1]!=ARM[c_][1] and c_ not in slotcaps:
            o_=G.owner[c_]; V_=min(G.vertices,key=lambda V:max(abs(o_[t]-V[t]) for t in range(3)))
            ob.append((G.vertices.index(V_),V_==Va,V_==Vb,V_==Vc,rel(o_,V_),rel(c_,V_),rel(COL[c_][1],V_)))
    print("NCHECK borrowed columns other than those of the 2-slot anchors (vertex#, isVa,isVb,isVc, owner, cap, second column site rel. vertex):",ob)
    assert ob==[(2,True,False,False,(0,2,2),(-1,3,1),(-2,4,2))]            # the only other borrowed column: cap of e1[2] (Appendix C)
    assert all(COL[d['tA']][1]!=ARM[d['tA']][1] and COL[d['cA0']][1]!=ARM[d['cA0']][1] for d in seps) and not any(c_ in COL and COL[c_][1]!=ARM[c_][1] for d in seps for c_ in (d['cX1'],d['tX']))
    print("NCHECK tether caps of the 2-slots with borrowed column:",sum(1 for d in seps if d['tA'] in COL and COL[d['tA']][1]!=ARM[d['tA']][1]),"of",len(seps),"; linker caps:",sum(1 for d in seps if COL[d['cA0']][1]!=ARM[d['cA0']][1]),"; 6-slot anchor caps borrowed:",sum(1 for d in seps for c_ in (d['cX1'],d['tX']) if c_ in COL and COL[c_][1]!=ARM[c_][1]))
    import pickle
    pickle.dump(dict(m=m,K=K,S=None,reserved=reserved,Va=Va,Vb=Vb,Vc=Vc,linkercaps=linkercaps,col2={c:COL[c][1] for c in COL},bulkends=bulkends),open(WORK+'/code/nf_%s.pkl'%TAG,'wb'))
if os.environ.get('NEARONLY'):
    print('NEAR FIELD OK: m=%d K=%d'%(m,K)); raise SystemExit(0)
# ---------- far field: one private cylinder shell {rho in {h,h+2}} per linker; columns of later linkers are punctures
pairs=[(order[i][1][-1][0],order[i+1][1][0][0]) for i in range(len(order)-1)]
assert all(a in linkercaps and b in linkercaps for a,b in pairs)
h0=max(rho(q) for q in reserved)+4; h0+=1-h0%2
def extend(col,h):
    """prolong a column until rho = h+2"""
    col=list(col); d=(Y(col[-1])-Y(col[-2]),Z(col[-1])-Z(col[-2]))
    while rho(col[-1])<h+2:
        cur=col[-1]; nx=[w for w in nbrs(cur) if (Y(w)-Y(cur),Z(w)-Z(cur))==d]
        assert len(nx)==1; col.append(nx[0])
    return col

FARMODE=sys.argv[9] if len(sys.argv)>9 else "shell"
PRESC=None
if LMODE.startswith('pad:'):
    ls=[list(map(int,open(f).read().split())) for f in LMODE[4:].split(',')]
    PRESC=[max(x) for x in zip(*ls)]
def pad_in_shell(mid,need,h,punct,i):
    """lengthen the path 'mid' by 'need' sites inside the shell {rho in {h,h+2}} by hexagon moves (one site -> three)"""
    onp=set(mid); t=1
    while need>0:
        done=False
        for tt in list(range(t,len(mid)-1))+list(range(1,t)):
            u,v,w=mid[tt-1],mid[tt],mid[tt+1]
            for a_ in nbrs(u):
                if a_==v or a_ in onp or a_ in punct or rho(a_) not in (h,h+2): continue
                for b_ in nbrs(a_):
                    if b_==u or b_ in onp or b_ in punct or rho(b_) not in (h,h+2): continue
                    for c_ in nbrs(b_):
                        if c_==a_ or c_ in onp or c_ in punct or rho(c_) not in (h,h+2) or w not in nbrs(c_): continue
                        mid[tt:tt+1]=[a_,b_,c_]; onp.discard(v); onp.update((a_,b_,c_)); done=True; break
                    if done: break
                if done: break
            if done: t=tt; break
        assert done,("cannot pad linker",i); need-=2
    return mid
linkpaths=[]; tot=0; natural=[]
if FARMODE=="shell":
    hh={}
    for i,(a,b) in enumerate(pairs): hh[a]=hh[b]=h0+4*i
    FULL={c:extend(COL[c],hh[c]) for c in hh}
    at={c:{rho(q):q for q in FULL[c]} for c in hh}        # rho -> site on the column
    for i,(a,b) in enumerate(pairs):
        h=h0+4*i
        punct=set()
        for (a2,b2) in pairs[i+1:]:
            for c in (a2,b2):
                for r in (h,h+2): punct.add(at[c][r])
        src=at[a][h]; dst=at[b][h]
        xlo=min(src[0],dst[0])-6; xhi=max(src[0],dst[0])+6
        for widen in (0,40,10**6):
            prev={src:None}; dq=deque([src])
            while dq:
                v=dq.popleft()
                if v==dst: break
                for w_ in nbrs(v):
                    if w_ in prev or w_ in punct or not (xlo-widen<=w_[0]<=xhi+widen): continue
                    r=rho(w_)
                    if r!=h and r!=h+2: continue
                    prev[w_]=v; dq.append(w_)
            if dst in prev: break
        assert dst in prev,("shell path failed",i)
        mid=[dst]
        while prev[mid[-1]] is not None: mid.append(prev[mid[-1]])
        mid=mid[::-1]
        ia=FULL[a].index(src); ib=FULL[b].index(dst)
        nat=ia+ib+len(mid); natural.append(nat)
        if PRESC is not None:                            # pad inside the private shell to the prescribed length
            need=PRESC[i]-nat; assert need>=0 and need%2==0,("prescribed length too short or wrong parity",i,PRESC[i],nat)
            onp=set(mid); t=1
            while need>0:
                done=False
                for tt in list(range(t,len(mid)-1))+list(range(1,t)):
                    u,v,w=mid[tt-1],mid[tt],mid[tt+1]
                    for a_ in nbrs(u):
                        if a_==v or a_ in onp or a_ in punct or rho(a_) not in (h,h+2): continue
                        for b_ in nbrs(a_):
                            if b_==u or b_ in onp or b_ in punct or rho(b_) not in (h,h+2): continue
                            for c_ in nbrs(b_):
                                if c_==a_ or c_ in onp or c_ in punct or rho(c_) not in (h,h+2) or w not in nbrs(c_): continue
                                mid[tt:tt+1]=[a_,b_,c_]; onp.discard(v); onp.update((a_,b_,c_)); done=True; break
                            if done: break
                        if done: break
                    if done: t=tt; break
                assert done,("cannot pad linker",i); need-=2
        p=FULL[a][:ia+1]+mid[1:-1]+FULL[b][:ib+1][::-1]
        assert len(set(p))==len(p),"self-crossing linker"
        if PRESC is not None: assert len(p)==PRESC[i]
        linkpaths.append(p); tot+=len(p)
elif FARMODE=="ordered":
    # ---- ordered scheme (notes 10.7): levels decreasing in X, avenues in the +X direction, private slabs, private outer shells
    quad=lambda v:(sgn(Y(v)),sgn(Z(v)))
    caps_=[c for pr in pairs for c in pr]
    xkey={c:min(COL[c][-1][0],COL[c][-2][0]) for c in caps_}
    xs=sorted(set(xkey.values()),reverse=True)
    lev={c:h0+4*xs.index(xkey[c]) for c in caps_}
    XF=max(max(q[0] for q in reserved),max(xkey.values()))+8
    topl=h0+4*len(xs)+8
    order_peel=sorted(caps_,key=lambda c:(-lev[c],xkey[c],c))
    slab={c:XF+10*r for r,c in enumerate(order_peel)}
    U={}
    for i,(a,b) in enumerate(pairs): U[a]=U[b]=topl+1-(topl%2)+4*i
    WIRE={}; ARMAT={}
    for c in caps_:
        col=extend(COL[c],lev[c]); col=col[:next(k for k,q in enumerate(col) if rho(q)==lev[c])+1]
        top=col[-1]; qd=quad(top); al=alpha(top); l=lev[c]
        ave=[]; cur=top
        while not (cur[0]>=slab[c] and rho(cur)==l+2 and ave and rho(ave[-2] if len(ave)>1 else top)==l):
            nx=[w for w in nbrs(cur) if w[0]==cur[0]+1 and rho(w) in (l,l+2) and quad(w)==qd and alpha(w) in (al,al+2)]
            assert len(nx)==1,("avenue step",c,len(nx)); cur=nx[0]; ave.append(cur)
        rad=[]
        while rho(cur)<U[c]:
            nx=[w for w in nbrs(cur) if rho(w)==rho(cur)+2 and quad(w)==qd]
            assert len(nx)==1,("radial step",c,len(nx)); cur=nx[0]; rad.append(cur)
        WIRE[c]=col+ave+rad; ARMAT[c]={rho(q):q for q in rad}
    occ={}
    for c in caps_:
        for q in WIRE[c]:
            assert q not in occ and q not in S and (q==c or reserved.get(q,"zone")=="zone"),("wire clash",c,q,occ.get(q),reserved.get(q)); occ[q]=c
    print("ordered scheme, stages A and B: %d wires, %d levels (rho %d..%d), slabs X = %d..%d, %d sites, pairwise disjoint ; %.0fs"%(len(caps_),len(xs),h0,topl,XF,XF+10*len(caps_),len(occ),time.time()-t0))
    QS=(1,1); AS=2*m+41+((2*m+41)%2==0)                # free strip: quadrant (+,+), alpha in {AS, AS+2}
    def helix_to_strip(t,u):
        """walk along the level set rho=u from t until the free strip is reached; both directions tried, shorter one kept"""
        best=None
        for first in [w for w in nbrs(t) if rho(w)==u]:
            p=[t,first]
            while not (quad(p[-1])==QS and alpha(p[-1]) in (AS,AS+2)):
                nx=[w for w in nbrs(p[-1]) if rho(w)==u and w!=p[-2]]
                assert len(nx)==1; p.append(nx[0])
            if best is None or len(p)<len(best): best=p
        return best
    for i,(a,b) in enumerate(pairs):
        u=U[a]; ta=WIRE[a][-1]; tb=WIRE[b][-1]
        ha=helix_to_strip(ta,u); hb=helix_to_strip(tb,u)
        sa,sb=ha[-1],hb[-1]; sdir=1 if sb[0]>sa[0] else -1
        ave=[sa]; guard=0
        while ave[-1]!=sb:
            cur=ave[-1]
            nx=[w for w in nbrs(cur) if w[0]==cur[0]+sdir and rho(w) in (u,u+2) and quad(w)==QS and alpha(w) in (AS,AS+2)]
            assert len(nx)==1,("strip step",i,len(nx)); ave.append(nx[0]); guard+=1; assert guard<10**7
        mid=ha+ave[1:]+hb[::-1][1:]
        nat=len(WIRE[a])+len(WIRE[b])+len(mid)-2; natural.append(nat)
        if PRESC is not None:
            need=PRESC[i]-nat; assert need>=0 and need%2==0,("prescribed length",i,PRESC[i],nat)
            punct=set()
            for c in caps_:
                if U[c]>u:
                    for r_ in (u,u+2): punct.add(ARMAT[c][r_])
            mid=pad_in_shell(mid,need,u,punct,i)
        p=WIRE[a]+mid[1:-1]+WIRE[b][::-1]
        assert len(set(p))==len(p),"self-crossing linker"
        linkpaths.append(p); tot+=len(p)
else:
    # ---- FARMODE "text[:Lstar|:resid]": the far field built LITERALLY as in the revised manuscript, section 8.5,
    #      Lemma F parts A-E (constants H = 20m+21, U_0 = H+4w+8, L* = 1000(m+w+1)+6; padding by crossing pairs + hexagon).
    #      Every inequality the text asserts on the way is checked by an assert.
    LSEL=FARMODE.split(':')[1] if ':' in FARMODE else 'Lstar'
    quad=lambda v:(sgn(Y(v)),sgn(Z(v))); QS=(1,1)
    Wc=[c for pr in pairs for c in pr]; w=len(Wc); assert len(set(Wc))==w and w==2*len(pairs)
    Hc=20*m+21; h0=Hc; Umax=Hc+6*w+8; U0=Hc+4*w+8; LSTAR=1000*(m+w+1)+6
    assert K<=m                                                                    # part E, first sentence
    tau_=set(tuple(D[j+1][0][i]-D[j][0][i] for i in range(3)) for j in range(JS[0]+2,JS[-1]))
    print('   track a-sites: consecutive differences',tau_,'; item-end caps on one sublattice:',len(set(isA(c) for c in potcaps))==1)
    assert len(tau_)==1 and all(t%2==0 for t in list(tau_)[0]) and sum(list(tau_)[0])%4==0
    assert len(set(isA(c) for c in potcaps))==1                                    # all possible item-end caps on ONE sublattice => linker parities do not depend on the packing
    nfr=max(rho(q) for q in reserved); assert nfr<=2*m+8*K+12<Hc,("near-field rho",nfr)   # part E: near field inside O_{2K+3}
    assert max(rho(q) for q in S)<Hc
    FULL={}; xkey={}; al={}; qd={}
    for c in Wc:
        col=extend(COL[c],Umax+4); FULL[c]=col
        xkey[c]=min(col[-1][0],col[-2][0]); al[c]=alpha(col[-1]); qd[c]=quad(col[-1])
        assert 0 not in qd[c]
        arm_=[q for q in col if rho(q)>2*m+4]                                       # beyond skin 1: an arm
        assert all(alpha(q)==al[c] and quad(q)==qd[c] and q[0] in (xkey[c],xkey[c]+1) for q in arm_),("not an arm",c)
        assert abs(al[c])<=2*m+4 and all(abs(q[0])<=2*m+4 for q in col),("part E, column bounds",c)
    AST=max(abs(al[c]) for c in Wc)+6
    assert AST%2==1 and Hc%2==1 and Hc>AST+2 and AST<=2*m+10                         # h_0 > max|alpha_c|+8 ; alpha* <= 2m+10
    # A. levels
    xs=sorted(set(xkey.values()),reverse=True)
    lev={c:h0+4*xs.index(xkey[c]) for c in Wc}; assert max(lev.values())<=Hc+4*(w-1)
    # B. slabs
    XF=Hc; assert all(q[0]<XF for c in Wc for q in FULL[c])
    orderW=sorted(Wc,key=lambda c:(-lev[c],c))                                       # decreasing level, ties arbitrarily
    slab={c:XF+60*(n+1) for n,c in enumerate(orderW)}
    U={}
    for i,(a,b) in enumerate(pairs): U[a]=U[b]=U0+4*(i+1)
    assert U0%2==1 and U0>max(lev.values())+4 and U0>AST+8 and max(U.values())<=Umax
    def avstep(cur,l,q,a0):
        nx=[v for v in nbrs(cur) if v[0]==cur[0]+1 and rho(v) in (l,l+2) and quad(v)==q and alpha(v) in (a0,a0+2)]
        assert len(nx)==1,("avenue step",cur,len(nx)); return nx[0]
    WIRE={}
    for c in Wc:
        l=lev[c]; col=FULL[c]; col=col[:next(k for k,q in enumerate(col) if rho(q)==l)+1]
        cur=col[-1]; assert cur[0]>=xkey[c]
        ave=[]
        while True:                                   # follow A_c to the first site E_c with X >= xi_c, rho = l+2, reached by a rung
            nxt=avstep(cur,l,qd[c],al[c]); pr_=rho(cur); ave.append(nxt); cur=nxt
            if cur[0]>=slab[c] and rho(cur)==l+2 and pr_==l: break
        assert cur[0]<=slab[c]+3
        rad=[]
        while rho(cur)<U[c]:
            nx=[v for v in nbrs(cur) if rho(v)==rho(cur)+2 and alpha(v)==alpha(cur) and quad(v)==qd[c]]
            assert len(nx)==1,("radial step",c,len(nx)); cur=nx[0]; rad.append(cur)
        assert all(slab[c]-1<=q[0]<=slab[c]+4 and alpha(q) in (al[c],al[c]+2) for q in rad)
        assert (len(col)-1)+len(rad)<=Umax+2 and len(ave)<=2*Hc+60*w+3               # part E
        WIRE[c]=col+ave+rad
    occ={}
    for c in Wc:
        for q in WIRE[c]:
            assert q not in occ and q not in S and (q==c or reserved.get(q,"zone")=="zone"),("wire clash",c,q,occ.get(q),reserved.get(q)); occ[q]=c
    print("text scheme A,B: w = %d wires, H = %d, alpha* = %d, levels %d..%d, slabs X = %d..%d, U_0 = %d, U_max = %d ; %d sites pairwise disjoint ; %.0fs"%(w,Hc,AST,h0,max(lev.values()),XF+60,XF+60*w,U0,Umax,len(occ),time.time()-t0))
    cy_=2*m-2
    def Asite(u,a0,x):
        """the unique site with X = x of the avenue A((+,+),u,a0)  (Lemma A)"""
        c_=[]
        for r_ in (u,u+2):
            for a_ in (a0,a0+2):
                v=(x,(r_+a_)//2+cy_,(r_-a_)//2+1)
                if dm.is_site(v): c_.append(v)
        assert len(c_)==1; v=c_[0]; assert quad(v)==QS and rho(v) in (u,u+2) and alpha(v) in (a0,a0+2); return v
    def helix(t,u,xi):
        """C: from t along Lambda_u, in the direction in which alpha increases inside (+,+), to the first site of A*"""
        good=[]
        for first in [v for v in nbrs(t) if rho(v)==u]:
            p=[t,first]
            while not (quad(p[-2])==QS and quad(p[-1])==QS):
                nx=[v for v in nbrs(p[-1]) if rho(v)==u and v!=p[-2]]; assert len(nx)==1; p.append(nx[0])
            if alpha(p[-1])>alpha(p[-2]): good.append(first)
        assert len(good)==1 and len([v for v in nbrs(t) if rho(v)==u])==2
        p=[t,good[0]]
        while not (quad(p[-1])==QS and alpha(p[-1]) in (AST,AST+2)):
            nx=[v for v in nbrs(p[-1]) if rho(v)==u and v!=p[-2]]; assert len(nx)==1; p.append(nx[0])
        s=p[-1]; assert alpha(s)==AST and s==Asite(u,AST,s[0])
        assert sum(1 for v in p if 0 in quad(v))<=3 and all(xi-5<=v[0]<=xi+8 for v in p)
        assert all(not (quad(v)==QS and alpha(v)>AST) for v in p) and len(p)-1<=4*Umax+4
        return p
    def padded(u,a,b,D):
        """D: the piece A_a..A_b of A* lengthened by exactly D sites (D even, D >= 6)"""
        A_=lambda x: Asite(u,AST,x); B_=lambda x: Asite(u,AST+4,x)
        assert (rho(A_(a)),alpha(A_(a)))==(u,AST) and (rho(A_(b)),alpha(A_(b)))==(u,AST) and b-a>=47
        p=next(x for x in range(a-1,a-9,-1) if alpha(A_(x))==AST+2 and B_(x-1) in nbrs(A_(x)))    # last crossing pair below a
        assert alpha(A_(p+1))==AST+2 and A_(p+1) in nbrs(A_(p)) and B_(p+2) in nbrs(A_(p+1))
        r=a-p; assert r in (2,3) and D%2==0 and D>=6
        d,j=divmod((D-2*r)//2,4); dl=1 if j%2==0 else 0; eta=j//2
        v0=p+dl-4*d; v1=p+dl+4; e=1-2*dl; q=p+8
        path=[A_(x) for x in range(a,v0-1,-1)]+[B_(x) for x in range(v0-e,v1-e+1)]
        for x in range(v1,b+1):
            path.append(A_(x))
            if eta and x==q: path+=[B_(q-1),B_(q),B_(q+1),B_(q+2)]
        assert len(path)==(b-a+1)+D
        return path,(r,dl,eta,D%8)
    stat=Counter(); betamax=0; LL=[]
    for i,(a,b) in enumerate(pairs):
        u=U[a]; ha=helix(WIRE[a][-1],u,slab[a]); hb=helix(WIRE[b][-1],u,slab[b])
        sa,sb=ha[-1],hb[-1]; assert abs(sa[0]-sb[0])<=60*w+13
        beta=len(WIRE[a])+len(WIRE[b])+(len(ha)-1)+(len(hb)-1)+abs(sa[0]-sb[0])-1   # P-sites incl. both caps
        assert beta<=280*m+240*w+406,("part E bound",beta); betamax=max(betamax,beta)
        if LSEL=='Lstar': L=LSTAR+((LSTAR-beta)%2)
        elif LSEL=='bound': Lb=280*m+240*w+412; L=Lb+((Lb-beta)%2)       # the smallest threshold part E proves
        else: L=beta+6+2*(i%16)
        lo,hi=min(sa[0],sb[0]),max(sa[0],sb[0])
        mid,info=padded(u,lo,hi,L-beta); stat[info]+=1
        if sa[0]>sb[0]: mid=mid[::-1]
        assert mid[0]==sa and mid[-1]==sb
        p=WIRE[a]+ha[1:]+mid[1:]+hb[::-1][1:]+WIRE[b][::-1][1:]
        assert len(p)==L and len(set(p))==len(p),"length or self-crossing"
        assert p[0]==a and p[-1]==b and all(p[k+1] in nbrs(p[k]) for k in range(len(p)-1))
        natural.append(beta); LL.append(L); linkpaths.append(p); tot+=len(p)
    allP={}
    for i,p in enumerate(linkpaths):
        for q in p:
            assert q not in allP and q not in S and (q in (p[0],p[-1]) or reserved.get(q,"zone")=="zone"),("linkers meet",i,allP.get(q)); allP[q]=i
    print("text scheme C-E: %d linkers pairwise disjoint and disjoint from Oct(m) and the near field ; max beta = %d <= bound %d ; L* = %d ; lengths %s"%(len(pairs),betamax,280*m+240*w+406,LSTAR,sorted(set(LL))[:3]+['...'] if LSEL!='Lstar' else sorted(set(LL))))
    print("   padding cases (r, delta, eta, increase mod 8) -> number of linkers:",dict(sorted(stat.items())))
    open(WORK+'/code/linklenL_%s.txt'%TAG,'w').write(' '.join(map(str,LL))+"\n")
open(WORK+'/code/linklen_%s.txt'%TAG,'w').write(' '.join(map(str,natural))+"\n")
print("far field: %d linkers routed, shells rho = %d ... %d, %d P's in linkers, %.0fs"%(len(pairs),h0,h0+4*len(pairs),tot,time.time()-t0))
chain=[]
for i,(nm,u) in enumerate(order):
    if i>0: chain+=[(q,'P') for q in linkpaths[i-1][1:-1]]
    chain+=u
sites=[p for p,l in chain]; seq=''.join(l for p,l in chain)
assert len(set(sites))==len(sites),"chain revisits a site"
assert all(sites[i+1] in nbrs(sites[i]) for i in range(len(sites)-1)),"chain is not a lattice walk"
H=set(p for p,l in chain if l=='H'); assert H==S,"H sites are not exactly the octahedron"
bonds=dm.edges(H); bound=2*N-2*m*m
print("chain length %d (H: %d, P: %d)"%(len(seq),seq.count('H'),seq.count('P')))
print("H-H bonds in this fold: %d ; proved upper bound 2N-2m^2: %d ; OPTIMAL: %s"%(bonds,bound,bonds==bound))
runs=Counter(len(r) for r in re.findall('H+',seq)); pr=Counter(len(r) for r in re.findall('P+',seq))
print("H-run lengths: 1:%d 2:%d (dimers) ; shortest other run %d"%(runs[1],runs[2],min(k for k in runs if k>2)))
print("P-run lengths <= 10:",{k:v for k,v in sorted(pr.items()) if k<=10})
print("PHP count:",len(re.findall('(?=PHP)',seq)),"; HPH:",'HPH' in seq,"; HPPH:",'HPPH' in seq)
for nm,u in sep_units+track_units: print("  unit:",nm)
tag=TAG
open(WORK+'/%s_fold_string.txt'%tag,'w').write(seq+"\n")
open(WORK+'/%s_fold_coords.txt'%tag,'w').write(''.join('%d %d %d %s\n'%(p[0],p[1],p[2],l) for p,l in chain))
print("written %s/%s_fold_*.txt ; total %.0fs"%(WORK,tag,time.time()-t0))
