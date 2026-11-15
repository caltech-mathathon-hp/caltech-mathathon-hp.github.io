import sys
exec(open('build3.py').read().split("def link(u,w,k):")[0])
def allpaths(u,w,k):
    out=[]
    for du in G.dang[u]:
        stack=[[du]]
        while stack:
            p=stack.pop()
            if len(p)==k:
                if p[-1] in G.dang[w]: out.append(p)
                continue
            for y in nbrs(p[-1]):
                if y in S or y in p: continue
                stack.append(p+[y])
    return out
capname={}
for z_ in slot_sites: capname[cap(z_)]="slotcap"
capname[cap(e1[1])]="cap e1[1]"; capname[cap(e1[2])]="cap e1[2]"; capname[cap(e2c[1])]="cap corner Vc"; capname[cap(Ub)]="cap Ub"
for v,c in bulkcaps.items(): capname[c]="bulkcap"
def lab(q):
    r=[]
    if q in capname: r.append(capname[q])
    for c in keep:
        if ARM[c][1]==q: r.append("arm1 of "+capname.get(c,"?"))
    return r
def show(u,w,k):
    ps=allpaths(u,w,k)
    print("link",u,w,k,": %d candidate paths"%len(ps))
    for p in ps:
        print("   skins",[skin(q) for q in p]," hits:",[(i,lab(q)) for i,q in enumerate(p) if lab(q)])
show(Va,e1[3],6)
s=SL1[0]; show(e1[2*s-1],e1[2*s+2],6)
s2=SL2[0]; show(e2c[2*s2+6],e2c[2*s2-1],10)
show(e2c[2],e2c[0],3); show(e1[2*m-4],e1[2*m-2],3)
