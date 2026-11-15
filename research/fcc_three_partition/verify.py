"""Independent standard-library coordinate and combinatorial certificate checks.

Run with Python 3. No optimization package, search result, or claimed score is trusted.
"""
import itertools as it
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIR = {p for p in it.product((-1, 0, 1), repeat=3) if sum(x*x for x in p) == 2}
U = ['PHP'*2 + 'PHH' + 'PHP'*3, 'HHP' + 'PHP'*5]
def add(a, b): return tuple(x+y for x,y in zip(a,b))
def sub(a, b): return tuple(x-y for x,y in zip(a,b))
def adjacent(a,b): return sub(a,b) in DIR
def physical(p):
    r,s,k = p
    return r+k, -r+s, -s+k
def auxiliary(p):
    x,y,z = p
    r=(x-y-z)//2
    return r,y+r,x-r
def ribbon(bits):
    result=[]; offset=0
    for r,b in enumerate(bits):
        rows=[(3,0),(2,0),(2,-1),(1,-1),(1,0),(0,-1),(-1,-1),(0,0),(-1,0),
              (b-1,1),(b,1),(b,2),(b+1,2),(b+1,1),(b+2,2),(b+3,2),(b+2,1),(b+3,1)]
        result += [physical((r,s+offset,k)) for s,k in rows]
        offset += b
    return result
def check(word, sites):
    sites=list(map(tuple,sites))
    assert len(word)==len(sites)
    assert all(len(p)==3 and all(type(v) is int for v in p) and sum(p)%2==0 for p in sites)
    assert len(set(sites))==len(sites), 'collision'
    assert all(adjacent(a,b) for a,b in zip(sites,sites[1:])), 'backbone failure'
    contacts=[(i,j) for i in range(len(word)) if word[i]=='H'
              for j in range(i+2,len(word)) if word[j]=='H' and adjacent(sites[i],sites[j])]
    return contacts
def defects(word, sites):
    sites=list(map(tuple,sites)); H={p for p,c in zip(sites,word) if c=='H'}; P=set(sites)-H
    alpha={p:12-sum(add(p,d) in H for d in DIR) for p in H}
    beta={p:sum(add(p,d) in H for d in DIR) for p in P}
    incidence=dict.fromkeys(sites,0); D=0; m=0
    for i in range(len(word)-1):
        if word[i]!=word[i+1]:
            a,b=sites[i:i+2]
            h,p=(a,b) if word[i]=='H' else (b,a)
            delta=alpha[h]+beta[p]-6
            assert delta>=0
            D+=delta; m+=1; incidence[a]+=1; incidence[b]+=1
    V=sum(add(p,d) not in H|P for p in H for d in DIR)
    RH=sum((2-incidence[p])*alpha[p] for p in H)
    RP=sum((2-incidence[p])*beta[p] for p in P)
    hh=sum(a==b=='H' for a,b in zip(word,word[1:]))
    E=len(check(word,sites))
    assert 8*(E+hh)==48*len(H)-6*m-D-2*V-RH-RP
    return dict(H=len(H),HP_edges=m,HH_edges=hh,D=D,V=V,RH=RH,RP=RP,budget=D+2*V+RH+RP)
def check_witnesses():
    result=[]
    for file in sorted(ROOT.glob('witness_*.json')):
        data=json.loads(file.read_text()); word=data['word']; sites=list(map(tuple,data['positions']))
        contacts=check(word,sites); assert len(contacts)==data['score']
        bits=[i%2 if data['mode']=='alternating' else 0 for i in range(data['L'])]
        base=ribbon(bits); assert len(check(word,base))==data['baseline']
        if data['locked']:
            lo,hi=data['locked']
            assert all(p==q for i,(p,q) in enumerate(zip(sites,base)) if not lo<=i<=hi)
        layers={}
        for p,c in zip(sites,word):
            if c=='H':
                r=auxiliary(p)[0]; layers[r]=layers.get(r,0)+1
        changed=[i for i,(p,q) in enumerate(zip(sites,base)) if p!=q]
        result.append(dict(file=file.name,score=len(contacts),baseline=data['baseline'],
                           changed_indices=changed,H_layer_sizes=layers,defects=defects(word,sites)))
    return result
def check_formula():
    count=0
    for L in range(1,6):
        for program in it.product((0,1),repeat=L):
            word=''.join(U[b] for b in program)
            for bits in it.product((0,1),repeat=L):
                expected=25*L-15-sum((1+2*(r<L-1 and program[r]!=program[r+1]))
                                     *(bits[r]!=program[r]) for r in range(L))
                assert len(check(word,ribbon(bits)))==expected
                count+=1
    return count
if __name__=='__main__':
    result=dict(witnesses=check_witnesses(),family_formula_cases=check_formula())
    (ROOT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    for r in result['witnesses']:
        print(r['file'],r['score'],'vs',r['baseline'],'layers',r['H_layer_sizes'])
    print('Program/fold formula cases:', result['family_formula_cases'])
