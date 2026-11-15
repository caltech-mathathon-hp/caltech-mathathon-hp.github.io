# Free bonded-capable surface sites F after framing e1,e2 and pinning PHP's; maximum dimer matching.
import sys
from geom import *
sys.setrecursionlimit(100000)
m=int(sys.argv[1]) if len(sys.argv)>1 else 10
G=Geo(m,margin=2); S=G.S
tri=[t for t in G.small_face_triples() if t[3]=='small'][0]
Va,Vb,Vc=tri[0],tri[1],tri[2]
e1=G.edge(Va,Vb); e2=G.edge(Vc,Vb); e3=G.edge(Va,Vc)
surf=set(G.surf); bonded={v:[w for w in nbrs(v) if w in surf] for v in surf}
sub=lambda v:'A' if sum(v)%4==0 else 'B'
MAJ='A' if sum(1 for v in S if sub(v)=='A')>len(S)/2 else 'B'
others=[v for v in G.vertices if v not in (Va,Vb,Vc)]
def analyse(nphp):
    php=[Va,Vb,Vc]+others[:nphp-3]
    removed=set(e1[2:-1])|set(e2[2:-1])|set(php)       # frames occupy z_2..z_{L-2} (incl. corner U_b = e1[-2] = e2[-2]); corners U_a,U_c stay free
    removed.add(e1[-2])
    F=[v for v in surf if bonded[v] and v not in removed]
    Fs=set(F)
    adj={v:[w for w in bonded[v] if w in Fs] for v in F}
    maj=[v for v in F if sub(v)==MAJ]; mn=[v for v in F if sub(v)!=MAJ]
    match={}
    def aug(u,seen):
        for w in adj[u]:
            if w in seen: continue
            seen.add(w)
            if w not in match or aug(match[w],seen):
                match[w]=u; return True
        return False
    size=0
    for u in mn:
        if aug(u,set()): size+=1
    # components
    comp={}; comps=[]
    for v in F:
        if v in comp: continue
        st=[v]; comp[v]=len(comps); c=[v]
        while st:
            x=st.pop()
            for w in adj[x]:
                if w not in comp: comp[w]=len(comps); c.append(w); st.append(w)
        comps.append(c)
    print("PHP's=%d: |F|=%d (Maj %d, Min %d), max matching=%d, unmatched=%d, components (size: Maj-Min): %s"%(
        nphp,len(F),len(maj),len(mn),size,len(F)-2*size,
        sorted((len(c),sum(1 if sub(v)==MAJ else -1 for v in c)) for c in comps)))
    tc=comp[e3[5]]
    print("     track component: size %d, contains all free e3 sites: %s"%(len(comps[tc]),all(comp.get(z)==tc for z in e3[1:-1])))
for n in (3,4,5,6): analyse(n)
