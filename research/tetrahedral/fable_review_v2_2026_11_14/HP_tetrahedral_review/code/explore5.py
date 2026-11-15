import sys
from potential import *
m=int(sys.argv[1])
n,nl,viol,ties,data=check(m)
G,X,adj,Y,Z,alpha,segs,al,xb,links,cx,om=data
ex=set(i for i,_ in viol)
# for each exceptional segment follow the chain of segments both ways until an end or another exceptional segment or 40 steps
def walk(i,j):
    out=[]; prev=i; cur=j
    for step in range(400):
        tag="a%+d/x%+.0f/n%d"%(al[cur],xb[cur],len(segs[cur]))
        if cur in ex: out.append(tag+" [TOP]"); return out,cur
        out.append(tag)
        nx=[k for k,_,_ in links[cur] if k!=prev]
        if not nx: out.append("END"); return out,None
        prev,cur=cur,nx[0]
    return out,'?'
H=defaultdict(list)
for i,_ in viol:
    v=segs[i][0]; V=nearest_vertex(G,v)
    print("TOP a%+d/x%+.0f/n%d near vertex %s:"%(al[i],xb[i],len(segs[i]),V))
    for j,_,_ in links[i]:
        out,end=walk(i,j)
        H[i].append(end)
        s=out if len(out)<=9 else out[:4]+["... (%d segments) ..."%(len(out)-8)]+out[-4:]
        print("     -> "+"  ".join(s))
print("skeleton: tops %d ; connections between tops:"%len(ex),[(sorted(ex).index(i),[("end" if e is None else sorted(ex).index(e)) for e in H[i]]) for i in sorted(ex)])
