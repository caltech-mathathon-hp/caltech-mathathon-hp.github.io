"""General-spacing version of notebook Section 6, with complete chain checks.

This constructs mobile item paths only; a supplied region is used for verification.
It does NOT construct or energetically force a freely folding scaffold prefix.
"""
from verify import *

def axis_path(start,target,axis):
    p=list(start); result=[]
    while p[axis]!=target:
        p[axis]+=1 if target>p[axis] else -1
        result.append(tuple(p))
    return result

def terminal_path(r,j,C,G,q):
    y=G*j
    route=[(r,y,0),(r,y+1,1),(r,y+2,1),(r,y+2,2)]
    def move(axis,target):route.extend(axis_path(route[-1],target,axis))
    move(2,C+1-r);move(0,2*r);move(2,C+1)
    Dj=2*C*j; Dmax=2*C*(q-1)
    for _ in range(Dj):
        move(0,route[-1][0]+1);move(2,route[-1][2]+1)
    move(2,C+1+Dmax)
    return route

def build(a,groups,B,scale=2,G=10):
    q=len(groups); t=len(a); C=scale*B
    assert scale>0 and scale%2==0 and G>=4
    assert sorted(sum(groups,[]))==list(range(t))
    assert all(sum(a[i] for i in group)==B for group in groups)
    M=20*(q+1)*(C+G+1)+4*t
    positions={}; assignments={}
    for j,group in enumerate(groups):
        offset=0
        for i in group:
            n=scale*a[i]
            path=[]
            for r in range(offset,offset+n):
                path.append((r,G*j,0))
                if r<offset+n-1:path.append((r,G*j,1))
            positions[i]=path;assignments[i]=(j,offset,offset+n-1)
            offset+=n
        assert offset==C
    chain=positions[0].copy();word='H'+'PH'*(scale*a[0]-1)
    z0=C+1+2*C*(q-1);Y0=G*(q-1)+4
    routes=[]
    for i in range(t-1):
        ja,_,ra=assignments[i];jb,rb,_=assignments[i+1]
        pa=terminal_path(ra,ja,C,G,q);pb=terminal_path(rb,jb,C,G,q)
        z=z0+i+1
        def middle(Y):
            p=[pa[-1]]
            for axis,target in [(2,z),(1,Y),(0,pb[-1][0]),(1,pb[-1][1]),(2,z0)]:
                p.extend(axis_path(p[-1],target,axis))
            return p
        mid=middle(Y0)
        length=(len(pa)-1)+(len(mid)-1)+(len(pb)-1)
        assert length<=M+1 and (M+1-length)%2==0
        mid=middle(Y0+(M+1-length)//2)
        connector=pa+mid[1:]+list(reversed(pb))[1:]
        assert len(connector)==M+2
        assert all(k>0 for r,s,k in connector[1:-1])
        chain+=connector[1:-1]+positions[i+1]
        word+='P'*M+'H'+'PH'*(scale*a[i+1]-1)
        routes.append(connector)
    # Optional whole-chain padding: a prefix can arrive along the first launch,
    # and the final H gets an unused outward P. Every item H then has two P ports.
    first=chain[0];last=chain[-1]
    padded_aux=[(first[0],first[1]+1,1)]+chain+[(last[0],last[1],1)]
    check('P'+word+'P',list(map(physical,padded_aux)))
    physical_chain=list(map(physical,chain));check(word,physical_chain)
    assert sum(c=='H' for c in word)==q*C
    # A particular octahedron makes the conditional confinement comparison concrete.
    R=2*(C+G*q+10)
    def in_oct(p):return sum(abs(x+R) for x in p)<=3*R
    assert all(in_oct(p) for p,c in zip(physical_chain,word) if c=='H')
    assert all(not in_oct(p) for p,c in zip(physical_chain,word) if c=='P')
    return dict(word=word,positions=physical_chain,M=M,R=R,C=C,G=G,q=q,
                residue_count=len(word),H_count=q*C)

if __name__=='__main__':
    examples=[([4,5,6,4,5,6],[[0,4,2],[3,1,5]],15,2,10),
              ([4,4,4,4,4,4],[[0,2,4],[1,3,5]],12,4,22),
              ([5]*9,[[0,3,6],[1,4,7],[2,5,8]],15,2,40)]
    results=[]
    for args in examples:
        d=build(*args)
        results.append({k:d[k] for k in ['M','R','C','G','q','residue_count','H_count']})
    (ROOT/'routing_verification.json').write_text(json.dumps(results,indent=2)+'\n')
    print(results)
