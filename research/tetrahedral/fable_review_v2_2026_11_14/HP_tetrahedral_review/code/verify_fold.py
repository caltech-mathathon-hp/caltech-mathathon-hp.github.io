"""Independent check of a fold file (lines: x y z letter). Uses nothing from the construction code."""
import sys
T=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
def is_site(v):
    x,y,z=v
    return (x-y)%2==0 and (y-z)%2==0 and (x+y+z)%4 in (0,3)
def nbrs(v):
    x,y,z=v; s=1 if (x+y+z)%4==0 else -1
    return [(x+s*a,y+s*b,z+s*c) for a,b,c in T]
rows=[l.split() for l in open(sys.argv[1])]
sites=[(int(r[0]),int(r[1]),int(r[2])) for r in rows]; seq=''.join(r[3] for r in rows)
assert all(is_site(v) for v in sites), "not all lattice sites"
assert len(set(sites))==len(sites), "a site is used twice"
assert all(sites[i+1] in nbrs(sites[i]) for i in range(len(sites)-1)), "consecutive monomers not adjacent"
H=set(v for v,l in zip(sites,seq) if l=='H'); N=len(H)
bonds=sum(1 for v in H for w in nbrs(v) if w in H)//2
m=round((3*N/4)**(1/3)+0.5)
while m*(4*m*m-1)//3>N: m-=1
ok=(m*(4*m*m-1)//3==N)
print("valid self-avoiding walk on the tetrahedral lattice: yes")
print("length %d, H %d, P %d"%(len(seq),N,len(seq)-N))
print("H-H bonds (chain bonds included): %d"%bonds)
if ok: print("N = N_m with m = %d ; proved upper bound 2N - 2m^2 = %d ; bound attained: %s"%(m,2*N-2*m*m,bonds==2*N-2*m*m))
print("isoperimetric check |S| <= (4/3)(|dS|/4)^1.5 :",N,"<=",round((4/3)*((4*N-2*bonds)/4)**1.5,1))
