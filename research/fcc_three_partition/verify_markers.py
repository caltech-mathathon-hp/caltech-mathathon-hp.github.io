"""Independent common-core/common-port checks on all successful marker tiles."""
from universal_competitor import A,B,Q,V,H0,T
from verify import *
from random import Random

def main():
    files=sorted(ROOT.glob('marker_[0-9]*.json'))
    tiles=[]; VH=(1,1,1)
    for file in files:
        d=json.loads(file.read_text());word=d['word'];aux=list(map(tuple,d['positions_aux']))
        assert len(word)==36 and word.count('H')==14
        assert {p for p,c in zip(aux,word) if c=='H'}==A|B
        assert tuple(d['translation_aux'])==T
        assert aux[0]==(sub(Q,T) if word[0]=='P' else H0)
        assert aux[-1]==(V if word[-1]=='P' else VH)
        assert all(p[0] in (0,1) for p in aux[int(word[0]=='P'):])
        assert Q not in aux
        hh=sum(a==b=='H' for a,b in zip(word,word[1:]))
        assert len(check(word,list(map(physical,aux))))==38-hh
        tiles.append((word,aux))
    for end in [V,VH]:
        assert adjacent(physical(end),physical(Q))
        assert adjacent(physical(end),physical(add(H0,T)))
    d=json.loads((ROOT/'marker_9_8.json').read_text())
    hp=[physical(tuple(p)) for p,c in zip(d['positions_aux'][:18],d['word'][:18]) if c=='H']
    a,b,c=[sub(hp[i],hp[0]) for i in [1,2,4]]
    determinant=a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
    assert determinant==2
    rng=Random(13112026)
    for _ in range(100):
        m=rng.randrange(1,16);chosen=[rng.choice(tiles) for _ in range(m)]
        word=''.join(w for w,p in chosen)
        points=[physical(add(p,tuple(j*x for x in T))) for j,(w,ps) in enumerate(chosen) for p in ps]
        hh=sum(a==b=='H' for a,b in zip(word,word[1:]))
        assert len(check(word,points))==53*m-15-hh
    result=dict(certified_pairs=len(files),possible_pairs=144,random_mixtures=100,
        improved_candidate_first_module_determinant=determinant,
        raw_formula='53*m-15 for any concatenation of certified pairs',
        ordinary_formula='53*m-15 minus the actual word-dependent consecutive-HH count',
        uncertified_pairs=[(a,b) for a,c in enumerate('PHP'*6) if c=='P'
                           for b,d in enumerate('PHP'*6) if d=='P' and not (ROOT/f'marker_{a}_{b}.json').exists()])
    (ROOT/'marker_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result)
if __name__=='__main__':main()
