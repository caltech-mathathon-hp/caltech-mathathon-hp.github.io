from diamond import *

def down(v):  # neighbours in layer x-1
    return [w for w in nbrs(v) if w[0]==v[0]-1]
def up(v):
    return [w for w in nbrs(v) if w[0]==v[0]+1]

def octa(m):
    """double pyramid (erosion) over the central m x m square in layer x=0"""
    S0=set()
    for i in range(m):
        for j in range(m):
            u,w=2*i,2*j
            S0.add((0,u+w,u-w))
    assert all(is_site(v) for v in S0)
    S=set(S0)
    cur=S0;k=0
    while cur:
        cand=set(w for v in cur for w in up(v))
        cur=set(c for c in cand if all(d in cur for d in down(c)))
        S|=cur
    cur=S0
    while cur:
        cand=set(w for v in cur for w in down(v))
        cur=set(c for c in cand if all(d in cur for d in up(c)))
        S|=cur
    return S

def layer_sizes(S,ax=0):
    d={}
    for v in S: d[v[ax]]=d.get(v[ax],0)+1
    return [d[k] for k in sorted(d)]

if __name__=="__main__":
    for m in range(1,8):
        S=octa(m)
        N=m*(4*m*m-1)//3
        dang={v:sum(1 for w in nbrs(v) if w not in S) for v in S}
        out={}
        for v in S:
            for w in nbrs(v):
                if w not in S: out[w]=out.get(w,0)+1
        from collections import Counter
        print("m",m,"N",len(S),N,"bd",boundary(S),4*m*m,
              "dangling-hist",sorted(Counter(dang.values()).items()),
              "outside-site S-nbr hist",sorted(Counter(out.values()).items()),
              "A,B",sum(1 for v in S if sub(v)=='A'),sum(1 for v in S if sub(v)=='B'))
        if m<=4:
            print("   layers x:",layer_sizes(S,0)); print("   layers y:",layer_sizes(S,1)); print("   layers z:",layer_sizes(S,2))
