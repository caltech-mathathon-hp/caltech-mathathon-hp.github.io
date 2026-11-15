"""Lemma T' (coverage of the region transfers), numerical check of statement and proof.
   Oct(M) with centre c: site p (relative to c) has depth  b_s - s.p  below face s, b_s = 2M-2 (s_x s_y s_z = +1) or 2M-1.
   Oct(m), m = M-2, same centre: b_s - 4.  Y = p_y, Z = p_z - 1.  F := 4D+12 ("far").
   For every lattice site p with all depths >= -R (rel. Oct(M)) the proof selects a translation tau:
     x : tau = 4 sg(p_x) e_x                       if the four faces with s_x = -sg(p_x) have depth >= F
     y : tau = 4 sg(Y) e_y                         if the faces with s_y = -sg(Y) have depth >= F and |Y| >= D+5
     z : tau = 4 sg(Z) e_z                         if the faces with s_z = -sg(Z) have depth >= F and |Z| >= D+5
     r : tau = (0, 2 sg(Y), 2 sg(Z))               if |Y|,|Z| >= D+3 and all faces except s_y=sg(Y), s_z=sg(Z) have depth >= F
   Claims: (a) for 4M >= 12D+46+R at least one applies; (b) whenever one applies, for every site w within D bonds of p:
     depths of w-tau rel. Oct(m) = depths of w rel. Oct(M) for the faces not required far, and both are >= 2D+3 for
     the far ones; sign(Y), sign(Z) (including zero) are the same for w and w-tau.
   Also: the counterexample to the old 'clean form' (m=11, R=0, R'=10, v=(0,30,10))."""
import sys, itertools
from diamond import *
SG=[s for s in itertools.product((1,-1),repeat=3)]
def depths(p,M): return {s:(2*M-2 if s[0]*s[1]*s[2]==1 else 2*M-1)-(s[0]*p[0]+s[1]*p[1]+s[2]*p[2]) for s in SG}
sg=lambda t:(t>0)-(t<0)
def options(p,M,D):
    F=4*D+12; d=depths(p,M); Y,Z=p[1],p[2]-1; out=[]
    for sx in ((sg(p[0]),) if p[0] else (1,-1)):
        if all(d[s]>=F for s in SG if s[0]==-sx): out.append(('x',(4*sx,0,0),[s for s in SG if s[0]==-sx]))
    if abs(Y)>=D+5 and all(d[s]>=F for s in SG if s[1]==-sg(Y)): out.append(('y',(0,4*sg(Y),0),[s for s in SG if s[1]==-sg(Y)]))
    if abs(Z)>=D+5 and all(d[s]>=F for s in SG if s[2]==-sg(Z)): out.append(('z',(0,0,4*sg(Z)),[s for s in SG if s[2]==-sg(Z)]))
    if abs(Y)>=D+3 and abs(Z)>=D+3:
        far=[s for s in SG if (s[1],s[2])!=(sg(Y),sg(Z))]
        if all(d[s]>=F for s in far): out.append(('r',(0,2*sg(Y),2*sg(Z)),far))
    return out
def ball(D):
    seen={(0,0,0)}; fr=[(0,0,0)]; 
    for _ in range(D):
        nf=[]
        for v in fr:
            for w in nbrs(v):
                if w not in seen: seen.add(w); nf.append(w)
        fr=nf
    return seen
def run(D,R,M,cy):
    c=(0,cy,0); m=M-2; rng=range(-(2*M+R),2*M+R+1); BA=ball(D)
    BB={(0,0,0)}|set(tuple(-x for x in v) for v in BA)       # balls around B-sites are the mirror images
    n=0; cnt={}
    for p in itertools.product(rng,repeat=3):
        if abs(p[0])+abs(p[1])+abs(p[2])>2*M+R: continue
        v=(p[0],p[1]+cy,p[2])
        if not is_site(v) or min(depths(p,M).values())<-R: continue
        op=options(p,M,D); assert op,("no transfer applies",D,R,M,p); n+=1
        for name,tau,far in op:
            cnt[name]=cnt.get(name,0)+1
            for dv in (BA if sum(v)%4==0 else BB):
                w=tuple(p[i]+dv[i] for i in range(3)); w0=tuple(w[i]-tau[i] for i in range(3))
                dM=depths(w,M); dm=depths(w0,m)
                for s in SG:
                    if s in far: assert dM[s]>=2*D+3 and dm[s]>=2*D+3
                    else: assert dM[s]==dm[s],(name,p,w,s)
                assert sg(w[1])==sg(w0[1]) and sg(w[2]-1)==sg(w0[2]-1)
    return n,cnt
# the audit's counterexample to the old clean form
m=11; c=(0,20,0); v=(0,30,10); p=tuple(v[i]-c[i] for i in range(3)); assert is_site(v) and min(depths(p,m).values())>=0
tv=(-2,28,10); c1=(0,18,0); p1=tuple(tv[i]-c1[i] for i in range(3))
s=(-1,1,1); print("old Lemma T, m=11,R=0,R'=10, v=(0,30,10): depth below small face (-,+,+): %d in Oct(11) -> %d in Oct(10) after tau ; hypothesis 4m>=3R+2R'+24: %s ; corrected hypothesis m>=R+R'+5: %s"%(depths(p,11)[s],depths(p1,10)[s],4*11>=24+20,11>=15))
for D,R,M in ((2,0,18),(2,5,20),(3,0,21),(3,7,23),(4,0,24)):
    assert 4*M>=12*D+46+R
    for cy in (0,2):
        n,cnt=run(D,R,M,cy); print("D=%d R=%d M=%d (m=%d) centre offset %d: %d sites, every one has a valid transfer; valid options checked: %s"%(D,R,M,M-2,cy,n,cnt),flush=True)
# corrected clean form of Lemma T: hypothesis m >= R+R'+5, R' >= 1: the four depths that drop are >= R+5
def cleanform(m,R,Rp):
    n=0
    for p in itertools.product(range(-(2*m+R),2*m+R+1),repeat=3):
        if abs(p[0])+abs(p[1])+abs(p[2])>2*m+R: continue
        v=(p[0],p[1]+2*m-2,p[2])
        if not is_site(v): continue
        d=depths(p,m)
        if min(d.values())<-R: continue
        el=[0]+([1] if abs(p[1])>=Rp+2 else [])+([2] if abs(p[2]-1)>=Rp+2 else [])
        ax=max(el,key=lambda i:abs(p[i]))
        for sgn_ in ((sg(p[ax]),) if p[ax] else (1,-1)):
            q=list(p); q[ax]-=2*sgn_; d1=depths(tuple(q),m-1); n+=1
            for s in SG:
                if s[ax]==-sgn_: assert d[s]>=R+5 and d1[s]==d[s]-4,(m,R,Rp,p,s)
                else: assert d1[s]==d[s]
    return n
for R,Rp in ((0,1),(0,3),(2,2),(3,1),(1,4),(0,10)):
    m=R+Rp+5; print("corrected Lemma T: R=%d R'=%d m=%d (minimal): %d cases, the four dropping depths are >= R+5 and drop by 4, the others unchanged"%(R,Rp,m,cleanform(m,R,Rp)))
