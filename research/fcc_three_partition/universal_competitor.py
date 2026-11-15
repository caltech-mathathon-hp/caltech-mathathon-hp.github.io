"""Certificate-based constructive theorem for EVERY even-length programmed word.

For sigma of length 2m, the four compatible tiles give an ordinary fold of
W_sigma with 51m-15 nonconsecutive contacts, versus the notebook's 50m-15.
The finite tile conditions below prove the construction for arbitrary m.
"""
from verify import *

T=(2,1,0)
A={(0,s,k) for s,k in [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1)]}
B={(1,s,k) for s,k in [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]}
Q=(1,1,2); V=(1,0,1); H0=(0,0,1)

def load_tiles():
    tiles={}
    for program in ['00','01','10','11']:
        suffix='' if program=='00' else '_'+program
        file=ROOT/('periodic_threaded_2'+suffix+'_cell_universal.json')
        d=json.loads(file.read_text())
        assert d['word']==''.join(U[int(b)] for b in program)
        assert tuple(d['translation_aux'])==T
        tiles[program]=list(map(tuple,d['positions_aux']))
    return tiles

def make_fold(program,tiles):
    assert len(program)%2==0 and len(program)>=2
    result=[]
    for j in range(len(program)//2):
        offset=tuple(j*x for x in T)
        result += [physical(add(p,offset)) for p in tiles[program[2*j:2*j+2]]]
    return result

def make_odd_fold(program,tiles):
    assert len(program)>=3 and len(program)%2==1
    return make_fold(program+'0',tiles)[:-18]

def prove_tile_conditions(tiles):
    H=A|B
    for program,aux in tiles.items():
        word=''.join(U[int(b)] for b in program)
        assert {p for p,c in zip(aux,word) if c=='H'}==H
        assert aux[-1]==V
        assert aux[0]==(sub(Q,T) if program[0]=='0' else H0)
        assert all(p[0] in (0,1) for p in aux[int(program[0]=='0'):])
        assert Q not in aux
        assert len(check(word,list(map(physical,aux))))==36
    assert adjacent(physical(V),physical(Q))
    assert adjacent(physical(V),physical(add(H0,T)))
    # The preceding interval separation plus reserved Q proves arbitrary mixing.
    within=sum(adjacent(physical(p),physical(q)) for p,q in it.combinations(H,2))
    between=sum(adjacent(physical(p),physical(add(q,T))) for p in H for q in H)
    assert within==38 and between==15
    assert min(p[0]+2*T[0] for p in H)-max(p[0] for p in H)>1
    cases=0
    for m in range(1,5):
        for bits in it.product('01',repeat=2*m):
            program=''.join(bits);word=''.join(U[int(b)] for b in program)
            fold=make_fold(program,tiles)
            assert len(check(word,fold))==51*m-15
            dd=defects(word,fold)
            assert dd['HP_edges']==24*m-int(program[0])
            assert dd['budget']==104*m+120+6*int(program[0])
            cases+=1
    odd_cases=0
    for m in range(1,5):
        for bits in it.product('01',repeat=2*m+1):
            program=''.join(bits);word=''.join(U[int(b)] for b in program)
            assert len(check(word,make_odd_fold(program,tiles)))==51*m-3+5*int(program[-1])
            odd_cases+=1
    return dict(tiles=4,within_raw=within,between_raw=between,HH_per_tile=2,
                exhaustive_mixed_examples=cases,exhaustive_odd_examples=odd_cases,
                formula='E(W_sigma) = 51*m-15 for |sigma|=2*m',
                odd_formula='E(W_sigma) = 51*m-3+5*last_bit for |sigma|=2*m+1>=3')

if __name__=='__main__':
    tiles=load_tiles(); result=prove_tile_conditions(tiles)
    (ROOT/'universal_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    program='00110110'
    (ROOT/'universal_example.json').write_text(json.dumps(dict(program=program,
        word=''.join(U[int(b)] for b in program),positions=make_fold(program,tiles),
        score=189,ribbon_threshold=185),indent=2)+'\n')
    rows=['| index | 00 | 01 | 10 | 11 |','|---:|---|---|---|---|']
    for i in range(36):
        rows.append('| '+str(i+1)+' | '+' | '.join(str(tiles[p][i]) for p in ['00','01','10','11'])+' |')
    (ROOT/'universal_tiles.md').write_text('# Four compatible auxiliary-coordinate tiles\n\n'
        'Each column folds the literal word U_a U_b. Translation between cells is (2,1,0).\n\n'
        +'\n'.join(rows)+'\n')
    print(result)
