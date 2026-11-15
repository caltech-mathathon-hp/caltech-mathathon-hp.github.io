"""Finite adversarial checks for the new perturbed-scaffold counting lemma.

The proof is in REPORT.md. These random tests supplement, not replace, it.
"""
from verify import *
from random import Random

def edges(A):
    A=set(A)
    return sum(add(p,d) in A for p in A for d in DIR)//2
def components(A):
    todo=set(A); count=0
    while todo:
        count+=1; stack=[todo.pop()]
        while stack:
            p=stack.pop()
            for d in DIR:
                q=add(p,d)
                if q in todo:
                    todo.remove(q); stack.append(q)
    return count

def main():
    R=8
    C={p for p in it.product(range(-R,R+1),repeat=3) if sum(p)%2==0 and sum(map(abs,p))<=R}
    U={(2+t,4-t,2) for t in range(3)}
    S0=C-U
    assert all(sum(add(p,d) in C for d in DIR)==9 for p in U)
    shell={add(p,d) for p in C for d in DIR}-C
    assert max(sum(add(p,d) in C for d in DIR) for p in shell)==3
    assert edges(U)==len(U)-1
    for mask in range(1<<len(U)):
        removed={p for i,p in enumerate(sorted(U)) if mask>>i&1}
        remaining=C-removed
        assert min(sum(add(p,d) in remaining for d in DIR) for p in remaining)>=4
    rng=Random(20261113); eC=edges(C); checks=0; sequence_cases=0
    # Repartition the occupied H set into scaffold and item labels after arbitrary swaps.
    for _ in range(1000):
        S=set(S0); A=set(U)
        for step in range(rng.randrange(1,9)):
            target=S if rng.randrange(2) else A
            old=rng.choice(sorted(target)); target.remove(old)
            free=sorted((C|shell)-(S|A)); target.add(rng.choice(free))
        union=S|A; d=len(U-union); s0=len(S0-union); s=len(S0-S)
        loss=eC-edges(union); c=components(U-union)
        assert 2*loss>=d+2*c-15*s0
        assert 2*loss>=d+2*c-11*s0
        eps=max(0,loss)
        assert len(A-U)<=2*eps+16*s
        assert len(A-U)<=2*eps+12*s
        outside_items=A-C
        if all(sum(add(p,v) in union for v in DIR)<=10 for p in outside_items):
            sequence_cases+=1
            assert loss>=len(A-U)+c-8*s
            assert 2*loss>=3*len(A-U)+2*c-12*s
            assert len(A-U)<=(2*eps+12*s)//3
        checks+=1
    result=dict(cases=checks,C_sites=len(C),C_edges=eC,hole_sites=len(U),
                inequality='2*(e(C)-e(S union A)) >= d+2*c(D)-15*s0',
                refined_oct_bin_inequality='2*(e(C)-e(S union A)) >= d+2*c(D)-11*s0')
    result['sequence_aware_bound']='3*|A outside U|+2*c(D) <= 2*loss+12*s, if outside item H degree <=10'
    result['sequence_aware_cases']=sequence_cases
    (ROOT/'robust_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result)
if __name__=='__main__': main()
