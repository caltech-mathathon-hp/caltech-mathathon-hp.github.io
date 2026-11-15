import sys
from fol import *
def analyse(m):
    G,S,E,X,nb,Y,Z,rho,alpha,edges,c=setup(m)
    xs=[v[0] for v in S]; cx=(min(xs)+max(xs))//2
    adj={v:set(w for w in nb[v] if w in X) for v in X}
    legit=lambda v: bool(G.dang[v]); sg=lambda t:(t>0)-(t<0)
    piece={}; pieces=[]
    for v in sorted(X):
        if v in piece: continue
        comp=[v]; piece[v]=len(pieces); st=[v]
        while st:
            x=st.pop()
            for w in adj[x]:
                if w not in piece: piece[w]=len(pieces); comp.append(w); st.append(w)
        pieces.append(comp)
    damaged=[v for v in X if any(w in E for w in nb[v])]
    merges=[]; used={}; left=[]
    for d in sorted(damaged):
        sy,sz=sg(Y(d)),sg(Z(d))
        cands=[w for w in nbrs(d) if w in X and w not in adj[d] and len(adj[w])<=1 and legit(w)]
        if sy!=0 and sz!=0: pick=[w for w in cands if (Y(w)-Y(d),Z(w)-Z(d))==(sz,-sy)]
        else: pick=cands if len(cands)==1 else []
        if pick and pick[0] not in used: used[pick[0]]=d; merges.append((d,pick[0]))
        else: left.append(d)
    # slab index of a piece: mean of X over its sites, doubled and rounded
    xi={p:round(2*sum(v[0]-cx for v in comp)/len(comp)) for p,comp in enumerate(pieces)}
    al={p:alpha(comp[0]) for p,comp in enumerate(pieces)}
    q=lambda v:('+' if Y(v)>0 else '-' if Y(v)<0 else '0')+('+' if Z(v)>0 else '-' if Z(v)<0 else '0')
    pg=defaultdict(list)
    for d,w in merges:
        pg[piece[d]].append(('d',q(d),al[piece[w]]-al[piece[d]],xi[piece[w]]-xi[piece[d]]))
        pg[piece[w]].append(('s',q(w),al[piece[d]]-al[piece[w]],xi[piece[d]]-xi[piece[w]]))
    return pieces,pg,al,xi,left,merges
if __name__=="__main__":
    m=int(sys.argv[1])
    pieces,pg,al,xi,left,merges=analyse(m)
    pat=Counter()
    for p,l in pg.items():
        if len(l)==2:
            l=sorted(l)
            pat[tuple(l)]+=1
    print("m=%d: patterns of pieces merged at both ends: (role, quadrant, d alpha, d(2*mean X)) x2 : count"%m)
    for k,v in sorted(pat.items(),key=lambda t:-t[1]): print("   ",k,":",v)
