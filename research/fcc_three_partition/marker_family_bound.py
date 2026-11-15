"""Exact finite transition accounting for every one-P-to-H recolouring per module.

This bounds only the notebook's ribbon geometry, including arbitrary choices
of which P is marked. It is not an unrestricted-fold bound.
"""
from fractions import Fraction
from verify import *

MARKERS=[i for i,c in enumerate('PHP'*6) if c=='P']
def marked(i): return ''.join('H' if j==i else c for j,c in enumerate('PHP'*6))
def main():
    states=list(it.product(MARKERS,(0,1)));n=len(states)
    intra=[len(check(marked(i),ribbon([b]))) for i,b in states]
    w=[]
    for ia,(i,b) in enumerate(states):
        row=[]
        for ja,(j,c) in enumerate(states):
            joint=len(check(marked(i)+marked(j),ribbon([b,c])))
            row.append(joint-intra[ia])
        w.append(row)
    assert max(intra)==10
    exceptional=[(states[i],states[j],w[i][j]) for i in range(n) for j in range(n) if w[i][j]>25]
    assert exceptional==[((9,1),(8,0),26)]
    # This directed transition cannot immediately follow itself; at most floor(L/2)
    # of the L-1 interfaces are exceptional. The following words attain the bound.
    for L in range(1,21):
        markers=([9,8]*((L+1)//2))[:L];bits=([1,0]*((L+1)//2))[:L]
        assert len(check(''.join(marked(i) for i in markers),ribbon(bits)))==25*L+L//2-15
    f=[[0]*n]
    for k in range(n): f.append([max(f[-1][i]+w[i][j] for i in range(n)) for j in range(n)])
    mean=max(min(Fraction(f[n][j]-f[k][j],n-k) for k in range(n)) for j in range(n))
    rate=mean;potential=[Fraction(0)]*n
    for k in range(n):potential=[max([0]+[w[i][j]-rate+potential[j] for j in range(n)]) for i in range(n)]
    assert all(w[i][j]<=rate+potential[i]-potential[j] for i in range(n) for j in range(n))
    boundary=max(intra[i]-rate+potential[i] for i in range(n))-min(potential)
    result=dict(states=states,intra=intra,transition_weights=w,potential=list(map(str,potential)),
                maximum_cycle_mean=str(mean),boundary_constant=str(boundary),
                exceptional_transition=exceptional,
                upper_bound='E <= 25*L+floor(L/2)-15 for any one-marker-per-module word on F_b',
                attaining_markers_zero_indexed=[9,8],attaining_geometry_bits=[1,0])
    (ROOT/'marker_family_bound.json').write_text(json.dumps(result,indent=2)+'\n')
    print(dict(maximum_cycle_mean=str(mean),potential=potential,boundary_constant=boundary,upper_bound=result['upper_bound']))
if __name__=='__main__':main()
