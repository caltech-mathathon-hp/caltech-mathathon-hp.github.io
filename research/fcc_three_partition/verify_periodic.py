"""Independent verification and exact boundary accounting for periodic cells."""
from verify import *

def translated_cell(cell,T,i): return [add(p,tuple(i*x for x in T)) for p in cell]

def verify_periodic(data):
    word=data['word']; aux=list(map(tuple,data['positions_aux'])); T=tuple(data['translation_aux'])
    cell=list(map(physical,aux)); step=physical(T)
    assert T[0]>0
    def quotient(p):
        c=p[0]//T[0]
        return tuple(p[i]-c*T[i] for i in range(3))
    assert len(set(map(quotient,aux)))==len(aux), 'collision between periodic copies'
    check(word,cell)
    assert adjacent(cell[-1],add(cell[0],step)), 'cell join'
    # Enumerate every forward cross-cell contact. r changes by <=1 on an FCC edge.
    maxgap=(max(p[0] for p in aux)-min(p[0] for p in aux)+1)//T[0]+1
    counts={}
    for gap in range(1,maxgap+1):
        counts[gap]=sum(adjacent(p,add(q,tuple(gap*x for x in step)))
            for p,c in zip(cell,word) if c=='H' for q,d in zip(cell,word) if d=='H')
    # Remove the one possible consecutive HH across a cell boundary.
    counts[1]-=int(word[-1]==word[0]=='H')
    internal=len(check(word,cell)); rate=internal+sum(counts.values())
    assert rate==data['score_per_period'], (rate,data['score_per_period'])
    boundary=sum(gap*count for gap,count in counts.items())
    for m in [1,2,3,4,5,10,20]:
        whole=sum((translated_cell(cell,step,i) for i in range(m)),[])
        actual=len(check(word*m,whole))
        assert actual==m*internal+sum(max(0,m-gap)*c for gap,c in counts.items())
        if m>=maxgap: assert actual==m*rate-boundary
    return dict(internal_nonconsecutive=internal,forward_contact_counts=counts,
                ordinary_rate=rate,boundary_loss=boundary,formula_valid_for_m_at_least=maxgap,
                physical_translation=step)

if __name__=='__main__':
    result={}
    for file in sorted(ROOT.glob('periodic_*.json')):
        if file.name=='periodic_verification.json':continue
        result[file.name]=verify_periodic(json.loads(file.read_text()))
        print(file.name,result[file.name])
    (ROOT/'periodic_verification.json').write_text(json.dumps(result,indent=2)+'\n')
