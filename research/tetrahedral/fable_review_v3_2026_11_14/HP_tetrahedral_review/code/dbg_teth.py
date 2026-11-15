exec(open('build3.py').read().split("for k,d in enumerate(seps): d['tin']=tether")[0])
d=seps[0]; j=2
a1=ARM[d['tA']]; a2=ARM[d['tS0']]
print("slot arm skins",[skin(q) for q in a1[:8]],"onF",[onF(q,skin(q)) for q in a1[:8]])
print("sep arm skins ",[skin(q) for q in a2[:8]],"onF",[onF(q,skin(q)) for q in a2[:8]])
print("slot arm reserved:",[reserved.get(q) for q in a1[:6]])
print("sep arm reserved:",[reserved.get(q) for q in a2[:6]])
src=a1[2*j-2]; dst=a2[2*j-2]
def gco(v,j):
    M=m+2*j; f=fco(v)
    if isA(v): return tuple((2*M-2-f[i])//4 for i in range(3))
    return tuple((2*M-3-f[i])//4 for i in range(3))
print("src",src,"g",gco(src,j),"dst",dst,"g",gco(dst,j))
# flood the corridor from src
seen={src}; dq=deque([src])
while dq:
    v=dq.popleft()
    for w_ in nbrs(v):
        if w_ in seen or not corridor_ok(w_,j): continue
        seen.add(w_); dq.append(w_)
print("reachable corridor sites:",len(seen))
gs=sorted(set(gco(v,j) for v in seen))
print("g-range reachable: g1 %d..%d g2 %d..%d g3 %d..%d"%(min(g[0] for g in gs),max(g[0] for g in gs),min(g[1] for g in gs),max(g[1] for g in gs),min(g[2] for g in gs),max(g[2] for g in gs)))
# why blocked near the e3 row: list neighbours of reachable sites with g3<=1 that are not ok
cnt=Counter()
for v in seen:
    for w_ in nbrs(v):
        if w_ in seen or w_ in S: continue
        if onF(w_,j):
            o=armowner.get(w_)
            why="reserved:"+reserved[w_] if w_ in reserved else ("arm of edge-b linkercap" if (o in linkercaps and G.owner[o] in edgeb) else ("arm of non-edge site" if o is not None and G.owner[o] not in edgeb else "arm of "+str(o)))
            cnt[(why,gco(w_,j)[2]<=1)]+=1
print(cnt.most_common(12))
