"""Thin all-(111)-face container and a fully threaded all-H-prefix failure.

No pins are present in the saved word/witness. The rectangle is an analysis
template, not part of the target input. All new claims are in CONTINUATION.md.
"""
from verify import *
from routing import terminal_path,axis_path

def make_counterexample(a,B):
    q=len(a)//3;scale=2;K=scale*sum(a);n=K+4;m=10*q+4;t=len(a)
    assert len(a)==3*q and sum(a)==q*B and all(B<4*x and 2*x<B for x in a)
    C={(r,s,k) for r in range(n) for s in range(m) for k in [-1,0]}
    holes={(r,0,0) for r in range(K)}
    prefix=[]
    # Bottom rectangle, ending at (0,m-1,-1), then top rows m-1 down to 1.
    for s in range(m):
        prefix.extend((r,s,-1) for r in (range(n) if s%2==0 else range(n-1,-1,-1)))
    for step,s in enumerate(range(m-1,0,-1)):
        prefix.extend((r,s,0) for r in (range(n) if step%2==0 else range(n-1,-1,-1)))
    prefix.extend((r,0,0) for r in range(n-1,K-1,-1))
    assert set(prefix)==C-holes and len(prefix)==2*n*m-K
    check('H'*len(prefix),list(map(physical,prefix)))
    blocks=[];offset=0
    for ai in a:
        block=[]
        for r in range(offset,offset+scale*ai):
            block.append((r,0,0))
            if r<offset+scale*ai-1:block.append((r,0,1))
        blocks.append(block);offset+=scale*ai
    M=40*(n+11)+4*(t+1)
    path=prefix.copy();word='H'*len(prefix);z0=n+1
    for i,block in enumerate(blocks):
        left=terminal_path(path[-1][0],0,n,10,1)
        right=terminal_path(block[0][0],0,n,10,1)
        z=z0+i+1
        def middle(Y):
            points=[left[-1]]
            for axis,target in [(2,z),(1,Y),(0,right[-1][0]),(1,right[-1][1]),(2,z0)]:
                points.extend(axis_path(points[-1],target,axis))
            return points
        mid=middle(4)
        length=len(left)+len(mid)+len(right)-3
        target=M+2 if i==0 else M+1
        assert target>=length and (target-length)%2==0
        mid=middle(4+(target-length)//2)
        connector=left+mid[1:]+list(reversed(right))[1:]
        assert len(connector)==target+1
        path+=connector[1:-1]+block
        word+='P'*(target-1)+'H'+'PH'*(scale*a[i]-1)
    path.append((K-1,0,1));word+='P'
    actual=list(map(physical,path));score=len(check(word,actual))
    expected_raw=9*n*m-5*n-5*m+2
    HH=len(prefix)-1
    assert score==expected_raw-HH
    assert {p for p,c in zip(path,word) if c=='H'}==C
    assert all(p[2]>0 for p,c in zip(path,word) if c=='P')
    intended={(r,2+10*j,0) for j in range(q) for r in range(2,2+scale*B)}
    assert len(intended)==K and intended.isdisjoint(holes)
    physical_C=set(map(physical,C));outside={add(p,d) for p in physical_C for d in DIR}-physical_C
    assert max(sum(add(p,d) in physical_C for d in DIR) for p in outside)==3
    assert min(sum(add(p,d) in physical_C for d in DIR) for p in physical_C)==3
    assert all(sum(add(physical(p),d) in physical_C for d in DIR)==9 for p in intended)
    return dict(a=a,B=B,q=q,scale=scale,n=n,m=m,M=M,prefix_H=len(prefix),word=word,
        positions=actual,ordinary_score=score,raw_H_contacts=expected_raw,
        source_has_partition=has_partition(a,B),H_count=len(C),
        actual_item_H_aux=sorted(holes),intended_bins_aux=sorted(intended))

def has_partition(a,B):
    if not a:return True
    for i,j in it.combinations(range(1,len(a)),2):
        if a[0]+a[i]+a[j]==B:
            rest=[x for k,x in enumerate(a) if k not in (0,i,j)]
            if has_partition(rest,B):return True
    return False

if __name__=='__main__':
    result=make_counterexample([4,4,4,6,6,6],15)
    assert not result['source_has_partition']
    (ROOT/'thin_false_positive.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k not in ['word','positions','actual_item_H_aux','intended_bins_aux']})
