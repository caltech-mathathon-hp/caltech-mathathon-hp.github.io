"""Exact finite exploration of dense seven-site layer shapes and two-layer periods.

This only filters H sets by necessary P-neighbour counts, not by chain threading.
"""
import itertools as it, json
from pathlib import Path
from verify import ROOT
T=((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1))
CROSS=((0,0),(1,0),(0,-1))
def norm(A):
    origin=min(A)
    return tuple(sorted((x-origin[0],y-origin[1]) for x,y in A))
def e(A):
    S=set(A)
    return sum((x+dx,y+dy) in S for x,y in A for dx,dy in T)//2
def cross(A,B):
    return sum((x+dx,y+dy) in B for x,y in A for dx,dy in CROSS)
def shift(A,t):return {(x+t[0],y+t[1]) for x,y in A}
def degrees(A,B):
    # The cell alternates A,B,A,B with no transverse shear.
    return [sum((x+dx,y+dy) in A for dx,dy in T)
            +sum((x+dx,y+dy) in B for dx,dy in CROSS)
            +sum((x-dx,y-dy) in B for dx,dy in CROSS) for x,y in A]
def degrees_between(A,prev,next_):
    return [sum((x+dx,y+dy) in A for dx,dy in T)
            +sum((x+dx,y+dy) in next_ for dx,dy in CROSS)
            +sum((x-dx,y-dy) in prev for dx,dy in CROSS) for x,y in A]
def main():
    shapes={((0,0),)}; counts=[1]
    for size in range(2,8):
        new=set()
        for A in shapes:
            occupied=set(A)
            for x,y in A:
                for dx,dy in T:
                    p=(x+dx,y+dy)
                    if p not in occupied:new.add(norm(occupied|{p}))
        shapes=new;counts.append(len(shapes))
    dense=[set(A) for A in sorted(shapes) if e(A)>=11]
    hist={k:sum(e(A)==k for A in shapes) for k in range(13)}
    pairs=0; candidates=[]; high=[]; best=0
    transitions={}
    for ia,A in enumerate(dense):
        for ib,B in enumerate(dense):
            offsets={(ax+dx-bx,ay+dy-by) for ax,ay in A for bx,by in B for dx,dy in CROSS}
            transitions[ia,ib]=[(off,cross(A,shift(B,off))) for off in sorted(offsets)
                                if cross(A,shift(B,off))>=13]
    for ia,A in enumerate(dense):
        for ib,B0 in enumerate(dense):
            offsets={ (ax+dx-bx,ay+dy-by) for ax,ay in A for bx,by in B0 for dx,dy in CROSS}
            for off in sorted(offsets):
                B=shift(B0,off);ab=cross(A,B);ba=cross(B,A)
                raw=e(A)+e(B)+ab+ba
                if raw<53:continue
                pairs+=1
                da=degrees(A,B);db=degrees(B,A)
                # U0^2 per period: every H needs >=1 P; all but four need >=2.
                if max(da+db)>11 or sum(d==11 for d in da+db)>4:continue
                best=max(best,raw)
                high.append(dict(A=sorted(A),B=sorted(B),raw=raw,degrees=da+db))
    sheared_high=[]; sheared_cases=0
    for ia,A in enumerate(dense):
        for ib,B in enumerate(dense):
            for off,ab in transitions[ia,ib]:
                for back,ba in transitions[ib,ia]:
                    raw=e(A)+e(B)+ab+ba
                    if raw<53:continue
                    sheared_cases+=1
                    da=degrees_between(A,shift(B,(-back[0],-back[1])),shift(B,off))
                    db=degrees_between(B,shift(A,(-off[0],-off[1])),shift(A,back))
                    if max(da+db)>11 or sum(d==11 for d in da+db)>4:continue
                    sheared_high.append(dict(A=sorted(A),B=sorted(shift(B,off)),
                        shear=[off[i]+back[i] for i in range(2)],raw=raw,degrees=da+db))
    result=dict(connected_translation_classes=counts,seven_edge_histogram=hist,
                dense_shapes=len(dense),raw_at_least_53_cases=pairs,
                survivors_necessary_P_degree_test=high,best_surviving_raw=best,
                sheared_raw_at_least_53_cases=sheared_cases,sheared_survivors=sheared_high,
                scope='Seven H per layer, two-layer periods, arbitrary integral transverse shear. Necessary P-degree test, not threading.')
    (ROOT/'layer_enumeration.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k not in ('survivors_necessary_P_degree_test','sheared_survivors')})
    print('survivors',len(high),'sheared survivors',len(sheared_high))
if __name__=='__main__': main()
