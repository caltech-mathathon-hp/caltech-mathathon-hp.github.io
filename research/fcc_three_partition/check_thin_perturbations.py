"""Supplementary checks of the thin-template perturbation estimate (T2)."""
from verify import *
from robust_checks import edges,components
from random import Random

def main():
    C={physical((r,s,k)) for r in range(8) for s in range(9) for k in [-1,0]}
    U={physical((r,s,0)) for r in range(2,6) for s in [2,6]};S0=C-U
    shell={add(p,v) for p in C for v in DIR}-C
    assert max(sum(add(p,v) in C for v in DIR) for p in shell)==3
    assert all(sum(add(p,v) in C for v in DIR)==9 for p in U)
    for mask in range(1<<len(U)):
        D={p for i,p in enumerate(sorted(U)) if mask>>i&1};remaining=C-D
        assert min(sum(add(p,v) in remaining for v in DIR) for p in remaining)>=3
    rng=Random(304);eC=edges(C);cases=0
    for _ in range(1000):
        S=set(S0);A=set(U)
        for j in range(rng.randrange(1,12)):
            target=S if rng.randrange(2) else A
            target.remove(rng.choice(sorted(target)))
            target.add(rng.choice(sorted((C|shell)-(S|A))))
        H=S|A
        if any(sum(add(p,v) in H for v in DIR)>10 for p in A-C):continue
        loss=eC-edges(H);s=len(S0-S);t=len(A-U);c=components(U-H)
        assert 3*t+2*c<=2*loss+13*s
        assert t<=(2*max(loss,0)+13*s)//3
        cases+=1
    result=dict(C_sites=len(C),hole_sites=len(U),all_hole_deletion_subsets=1<<len(U),
                perturbation_cases=cases,inequality='3*t+2*c <= 2*loss+13*s')
    (ROOT/'thin_perturbation_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result)
if __name__=='__main__':main()
