"""Closed-form cap replacement: U_0^L has score 25L-14 for every L >= 2."""
from verify import *

# Auxiliary coordinates (r,s,k). The chain order is exactly U_0.
CAP=[(0,3,2),(0,2,1),(-1,2,2),(0,2,2),(0,1,1),(0,1,2),
     (-1,0,2),(0,0,1),(0,-1,1),(-1,-1,1),(0,-1,0),(-1,-1,0),
     (0,-1,-1),(0,0,0),(0,0,-1),(0,1,-1),(0,1,0),(0,2,0)]
TAIL=[(0,3,0),(0,2,0),(0,1,-1),(1,1,-1),(0,1,0),(0,0,-1),
      (1,0,-1),(1,1,0),(1,2,0),(1,3,1),(0,2,1),(0,2,2),
      (0,1,2),(0,1,1),(0,0,1),(1,0,0),(0,0,0),(0,-1,-1)]

def capped(L):
    assert L>=2
    return list(map(physical,CAP))+ribbon([0]*L)[18:]

def both_caps(bits):
    L=len(bits)
    assert L>=3 and bits[0]==bits[1]==bits[-2]==bits[-1]==0
    tail=[physical(add(p,(L-1,sum(bits[:-1]),0))) for p in TAIL]
    return list(map(physical,CAP))+ribbon(bits)[18:-18]+tail

def verify_cap():
    # Proof reduces to these local facts plus the layer bounds on all sites.
    cap=list(map(physical,CAP)); original=ribbon([0,0])
    assert len(check(U[0],cap))==10
    assert len(check(U[0]*2,cap+original[18:]))==36
    assert all(r<=0 for r,s,k in CAP)
    assert all(r==0 for (r,s,k),c in zip(CAP,U[0]) if c=='H')
    assert adjacent(cap[-1],original[18])
    edges=sum(adjacent(a,b) for a,c in zip(cap,U[0]) if c=='H'
              for b,d in zip(original[18:],U[0]) if d=='H')
    assert edges==16
    for L in [2,3,4,5,10,20,50,100]:
        assert len(check(U[0]*L,capped(L)))==25*L-14
    for L in range(3,11):
        for middle in it.product((0,1),repeat=max(0,L-4)):
            bits=[0]*L
            bits[2:L-2]=middle
            assert len(bits)==L
            assert len(check(U[0]*L,both_caps(bits)))==25*L-13-sum(bits)
    return {'within_raw':11,'interface_raw':16,'one_cap_formula':'25*L-14, L>=2',
            'two_caps_formula':'25*L-13-sum(bits), first/last two bits zero, L>=3'}

if __name__=='__main__':
    print(verify_cap())
    positions=capped(3)
    (ROOT/'cap_certificate.json').write_text(json.dumps(dict(word=U[0]*3,positions=positions,score=61),indent=2)+'\n')
    bits=[0,0,1,0,1,0,0]
    (ROOT/'wrong_bends_certificate.json').write_text(json.dumps(dict(word=U[0]*7,bits=bits,
        positions=both_caps(bits),score=160,original_threshold=160),indent=2)+'\n')
