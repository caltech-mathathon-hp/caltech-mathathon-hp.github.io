"""Tethers of Lemma N (N4): coordinate check that uses NOTHING from the builder (no canon.py, no build3.py) and never
   constructs the octahedron, so it runs for the sizes of the actual reduction (m >= 336).
   Coordinates: centre c = (0,2m-2,0); f_i = t_i.(v-c); skin j = O_j minus O_(j-1), O_j = octahedron of size M = m+2j.
   F'-bilayer of skin j: surface (a,b,c): B-site, f_4 = -(2M-1), f_i = 2M-3-4(a,b,c)_i ; sub-surface g: A-site,
   f_4 = -(2M-2), f_i = 2M-2-4g_i.
   Entry tether k (k = 1..K+1), skin j = k+1: cap of the slot's b-site = e1[6k]+(2,2,0); borrowed column: +(1,1,1), then
     -t4, +t3 alternately; sub (m-3-3k+j,3k+j,2); surface (m-3-3k+j,3k+j,1); row c=1 down to b=j-1; row b=j-1 up to
     c = j_k+1; sub (m-2-j_k+j, j, j_k+1); down the column of the separator's first b-site (m-2-j_k,0,j_k) of F'.
   Exit tether k, skin j = K+2+k, kappa = K+1-k: up the column of the separator's second b-site (m-3-j_k,0,j_k+1);
     sub (m-3-j_k+j, j, j_k+2); surface (m-3-j_k+j, j-1, j_k+2); row b=j-1 until a=j-1; row a=j-1 until
     (j-1, 5kappa+3+j, m-4-5kappa); sub (j, 5kappa+3+j, m-4-5kappa); down the column of w_1 = (0,5kappa+3,m-5-5kappa).
   Checked: lattice path, self-avoiding, caps bonded to the right H's of Oct(m), every site in the stated skin,
   lengths 2j_k+10k+5 and 2(m-2-j_k)+14K+25-6k, all 2(K+1) tethers pairwise disjoint, and no site of a row lies on a
   column of F' other than those of e1-sites and second-row sites (c = 0, 1) that carry no tether in that skin."""
import sys
T=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
add=lambda v,t,s=1: (v[0]+s*t[0],v[1]+s*t[1],v[2]+s*t[2])
def is_site(v): return (v[0]-v[1])%2==0 and (v[1]-v[2])%2==0 and sum(v)%4 in (0,3)
def isA(v): return sum(v)%4==0
def bonded(u,v):
    d=(v[0]-u[0],v[1]-u[1],v[2]-u[2]) if isA(u) else (u[0]-v[0],u[1]-v[1],u[2]-v[2])
    return d in T
def check(m,K,J,C,verbose=False):
    cc=(0,2*m-2,0)
    fco=lambda v: tuple(sum(T[i][t]*(v[t]-cc[t]) for t in range(3)) for i in range(4))
    def inO(v,j):
        M=m+2*j; f=fco(v)
        return max(abs(x) for x in f)<=2*M-2 if isA(v) else (min(f)>=-(2*M-1) and max(f)<=2*M-3)
    def skin(v):
        j=0
        while not inO(v,j): j+=1
        return j
    def fsite(f):
        assert sum(f)==0; v=((f[0]+f[1])//2+cc[0],(f[0]+f[2])//2+cc[1],(f[0]+f[3])//2+cc[2]); assert is_site(v) and fco(v)==tuple(f); return v
    def surf(a,b,c,j):
        M=m+2*j; assert min(a,b,c)>=0 and a+b+c==M-2; return fsite((2*M-3-4*a,2*M-3-4*b,2*M-3-4*c,-(2*M-1)))
    def subs(g,j):
        M=m+2*j; assert min(g)>=1 and sum(g)==M-1; return fsite((2*M-2-4*g[0],2*M-2-4*g[1],2*M-2-4*g[2],-(2*M-2)))
    def owncol(v,n):                     # column of the dangling site of the F'-site v: v-t4, then +t3, -t4, ...
        col=[add(v,T[3],-1)]
        while len(col)<n: col.append(add(col[-1],T[2]) if len(col)%2==1 else add(col[-1],T[3],-1))
        return col
    Va=(0,2*m-2,-(2*m-2)); jk=lambda k: J+(k-1)*(C+2)
    assert m==J+K*(C+2)+(m-3-J-K*(C+2))+3
    allsites={}; out=[]; rowsites=[]
    for k in range(1,K+2):
        # ---- entry
        j=k+1; a0=add(Va,(0,6*k,6*k)); bsite=add(a0,(1,1,1)); cap=add(a0,(2,2,0))
        assert inO(a0,0) and inO(bsite,0) and bonded(bsite,cap) and skin(cap)==1
        col1=[cap,add(cap,(1,1,1))]
        while len(col1)<2*j-1: col1.append(add(col1[-1],T[3],-1) if len(col1)%2==0 else add(col1[-1],T[2]))
        a,b,c=m-3-3*k+j,3*k+j,1
        mid=[subs((a,b,2),j),surf(a,b,1,j)]; corners=[(a,b,c)]
        for _ in range(3*k+1): mid+=[subs((a+1,b,c),j),surf(a+1,b-1,c,j)]; a+=1; b-=1
        corners.append((a,b,c))
        for _ in range(jk(k)): mid+=[subs((a,b,c+1),j),surf(a-1,b,c+1,j)]; a-=1; c+=1
        corners.append((a,b,c)); mid.append(subs((a,j,c),j))
        v2=surf(m-2-jk(k),0,jk(k),0); col2=owncol(v2,2*j-1); assert inO(v2,0) and bonded(v2,col2[0])
        assert col1[2*j-2]==mid[0] and col2[2*j-2]==mid[-1]
        p=col1[:2*j-2]+mid+col2[:2*j-2][::-1]
        assert len(p)==2*jk(k)+10*k+5,("entry length",k,len(p))
        out.append(("entry",k,j,p,mid,cap,col1,col2,corners))
        # ---- exit
        j=K+2+k; kap=K+1-k
        v1=surf(m-3-jk(k),0,jk(k)+1,0); c1=owncol(v1,2*j-1); assert inO(v1,0) and bonded(v1,c1[0])
        a,b,c=m-3-jk(k)+j,j-1,jk(k)+2
        mid=[subs((a,j,c),j),surf(a,b,c,j)]
        for _ in range(m-2-jk(k)): mid+=[subs((a,b,c+1),j),surf(a-1,b,c+1,j)]; a-=1; c+=1
        assert (a,b,c)==(j-1,j-1,m)
        for _ in range(5*kap+4): mid+=[subs((a,b+1,c),j),surf(a,b+1,c-1,j)]; b+=1; c-=1
        assert (a,b,c)==(j-1,5*kap+3+j,m-4-5*kap); mid.append(subs((j,b,c),j))
        w1=surf(0,5*kap+3,m-5-5*kap,0); c2=owncol(w1,2*j-1); assert inO(w1,0) and bonded(w1,c2[0])
        assert c1[2*j-2]==mid[0] and c2[2*j-2]==mid[-1]
        p=c1[:2*j-2]+mid+c2[:2*j-2][::-1]
        assert len(p)==2*(m-2-jk(k))+14*K+25-6*k,("exit length",k,len(p))
        out.append(("exit",k,j,p,mid,c1[0],c1,c2,None))
    used={}                                                   # borrowed columns of the slots: F'-site (m-3-3k,3k,1), used up to skin k+1
    for kind,k,j,p,mid,cap,ca,cb,corners in out:
        assert all(is_site(v) for v in p) and all(bonded(p[i],p[i+1]) for i in range(len(p)-1)) and len(set(p))==len(p)
        assert all(skin(v)==j for v in mid) and all(skin(ca[i])==(i+2)//2 for i in range(2*j-2)) and all(skin(cb[i])==(i+2)//2 for i in range(2*j-2))
        for v in p:
            assert v not in allsites,("tethers meet",kind,k,allsites.get(v)); allsites[v]=(kind,k)
        M=m+2*j
        for v in mid[1:-1]:                                    # which column of F' passes through this site of skin j ?
            f=fco(v)
            if isA(v): g=[(2*M-2-f[i])//4 for i in range(3)]; own=(g[0]-j,g[1]-j,g[2]-1)
            else: g=[(2*M-3-f[i])//4 for i in range(3)]; own=(g[0]-j,g[1]-j,g[2])
            if min(own[0],own[1])<0: continue                  # rows b <= j-1 and a <= j-1: no column (Lemma R(d))
            assert kind=="entry" and own[2] in (0,1),("row site on a column of the interior of F'",kind,k,own)
            if own[2]==1 and own[1]%3==0 and own[0]==m-3-own[1]:     # borrowed column of the slot k' = own[1]/3
                kp=own[1]//3; assert kp==k or kp+1<j,("row c=1 meets a tether column in use",k,kp)
    if verbose:
        kind,k,j,p,mid,cap,ca,cb,corners=out[0]
        print("   m=%d K=%d, entry tether 1 (skin 2): start cap %s ; borrowed second site %s ; skin-2 column endpoint %s ; target cap %s ; target column endpoint %s"%(m,K,cap,ca[1],ca[2],cb[0],cb[2]))
        print("   surface route in F'-bilayer coordinates: %s -> %s -> %s ; P-sites: %d = 2*j_1+10+5 (taut %d, slack %d)"%(corners[0],corners[1],corners[2],len(p),2*jk(1)+3,len(p)-2*jk(1)-3))
    return len(out),sum(len(o[3]) for o in out)
print("actual reduction parameters (section 6): C = (18K+48)B, J = C+18K+48, R = J+1, m = J+K(C+2)+R+3")
for K,B in ((1,1),(1,2),(1,252),(2,1),(3,2),(9,1),(10,3),(12,1)):
    C=(18*K+48)*B; J=C+18*K+48; R=J+1; m=J+K*(C+2)+R+3; assert m==(K+2)*(18*K+48)*B+38*K+100 and m%2==0
    n,tot=check(m,K,J,C,verbose=(K,B)==(1,1))
    print("K=%2d B=%3d m=%6d: %d tethers, %d sites: explicit routes are disjoint lattice paths in their skins, lengths = formulas, rows free of used columns"%(K,B,m,n,tot),flush=True)
print("test layouts of Lemma N")
for m,K,J,C in ((80,8,14,4),(80,2,14,8),(82,8,14,4),(92,10,14,4)):
    n,tot=check(m,K,J,C); print("m=%d K=%d J=%d C=%d: %d tethers, %d sites: OK"%(m,K,J,C,n,tot))
