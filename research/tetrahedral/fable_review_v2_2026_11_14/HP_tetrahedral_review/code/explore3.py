import sys
from fol import *
m=int(sys.argv[1])
G,S,E,X,nb,Y,Z,rho,alpha,edges,c=setup(m)
adj={v:set(w for w in nb[v] if w in X) for v in X}
legit=lambda v: bool(G.dang[v]); sg=lambda t:(t>0)-(t<0)
# pieces of the foliation in X
piece={}; pieces=[]
for v in sorted(X):
    if v in piece: continue
    # walk to an end
    comp=[v]; piece[v]=len(pieces); st=[v]
    while st:
        x=st.pop()
        for w in adj[x]:
            if w not in piece: piece[w]=len(pieces); comp.append(w); st.append(w)
    pieces.append(comp)
assert all(len(set(alpha(v) for v in p))==1 for p in pieces)
damaged=[v for v in X if any(w in E for w in nb[v])]
merges=[]; used={}; left=[]
for d in sorted(damaged):
    sy,sz=sg(Y(d)),sg(Z(d))
    cands=[w for w in nbrs(d) if w in X and w not in adj[d] and len(adj[w])<=1 and legit(w)]
    if sy!=0 and sz!=0: pick=[w for w in cands if (Y(w)-Y(d),Z(w)-Z(d))==(sz,-sy)]
    else: pick=cands if len(cands)==1 else []
    if pick and pick[0] not in used: used[pick[0]]=d; merges.append((d,pick[0]))
    else: left.append(d)
# piece graph
pg=defaultdict(list)
for d,w in merges: pg[piece[d]].append((piece[w],alpha(w)-alpha(d),'d')); pg[piece[w]].append((piece[d],alpha(d)-alpha(w),'s'))
ext=Counter(); kinds=Counter()
for p,l in pg.items():
    if len(l)==2:
        k=''.join(sorted(x[2] for x in l)); kinds[k]+=1
        if l[0][1]<0 and l[1][1]<0: ext[('max',k)]+=1
        if l[0][1]>0 and l[1][1]>0: ext[('min',k)]+=1
print("m=%d: pieces %d, merges %d, leftover %d ; pieces merged at both ends by kind %s ; local extrema of alpha among them: %s"%(m,len(pieces),len(merges),len(left),dict(kinds),dict(ext)))
# chains
seen=set(); chains=[]
for p in range(len(pieces)):
    if p in seen or len(pg[p])==2: continue
    if len(pg[p])==0: continue
    ch=[p]; seen.add(p)
    while True:
        nx=[q for q,_,_ in pg[ch[-1]] if q not in seen]
        if not nx: break
        ch.append(nx[0]); seen.add(nx[0])
    chains.append(ch)
cyc=[p for p in pg if p not in seen and len(pg[p])==2]
print("chains: %d ; pieces on closed chains: %d"%(len(chains),len(cyc)))
dv=lambda v: min((max(abs(v[i]-V[i]) for i in range(3)),V) for V in G.vertices)
def endinfo(p,exclude):
    # the free end(s) of piece p not used by merges
    ends=[v for v in pieces[p] if len(adj[v])<=1]
    mset=set(x for d,w in merges for x in (d,w))
    fr=[v for v in ends if v not in mset]
    out=[]
    for v in fr:
        dist,V=dv(v)
        out.append(("legit" if legit(v) else ("LEFTOVER" if v in left else "bad"),"alpha %d"%alpha(v),"near vertex %s at %s"%(V,tuple(v[i]-V[i] for i in range(3))) if dist<=8 else "far from vertices (dist %d)"%dist))
    return out
for ch in sorted(chains,key=len,reverse=True)[:40]:
    al=[alpha(pieces[p][0]) for p in ch]
    mono=all(b>a for a,b in zip(al,al[1:])) or all(b<a for a,b in zip(al,al[1:]))
    print("  chain of %3d pieces, alpha %4d -> %4d, monotone %s ; ends: %s | %s"%(len(ch),al[0],al[-1],mono,endinfo(ch[0],None),endinfo(ch[-1],None)))
print()
xs=[v[0] for v in S]; cx=(min(xs)+max(xs))//2
mof={}
for d,w in merges: mof[d]=('d',w); mof[w]=('s',d)
def desc(p):
    comp=pieces[p]; a=alpha(comp[0]); xi=sorted(set(v[0]-cx for v in comp)); fam=('Z' if a>0 else 'Y')
    ends=[v for v in comp if len(adj[v])<=1]
    es=[]
    for v in ends:
        q=('+' if Y(v)>0 else '-' if Y(v)<0 else '0')+('+' if Z(v)>0 else '-' if Z(v)<0 else '0')
        es.append(q+(mof[v][0] if v in mof else ('L' if v in left else 'f')))
    return "a%+d x%s n%d [%s]"%(a,"".join("%+d"%t for t in xi[:3]),len(comp)," ".join(es))
for ch in sorted(chains,key=len,reverse=True):
    if len(ch) in (5,2) and alpha(pieces[ch[0]][0]) not in (-7,-17,-19): continue
    print("chain (%d pieces):"%len(ch))
    print("   "+"  ->  ".join(desc(p) for p in ch[:24]))
