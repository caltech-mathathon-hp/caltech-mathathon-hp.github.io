// Reimplement the stated local bulk-cover rules and inspect the Omega certificate.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {octSites,inOct,edgeSite,neighbours,coords,key,add,same,fs as tetraCoordinates,mod} from './audit_geometry.mjs';
const manuscript=fs.readFileSync(new URL('../../background/HP_tetrahedral_proof_Astra.md',import.meta.url),'utf8');
const patchLines=manuscript.split(/\r?\n/).filter(l=>l.startsWith('* Vertex '));
const parseBonds=s=>[...s.matchAll(/\((-?\d+),(-?\d+),(-?\d+)\)–\((-?\d+),(-?\d+),(-?\d+)\)/g)]
  .map(a=>[a.slice(1,4).map(Number),a.slice(4,7).map(Number)]);
function patches(m) {
  const out=[];
  for(const line of patchLines) {
    const label=line.match(/^\* Vertex ([−+][xyz])/)[1],axis='xyz'.indexOf(label[1]);
    const vertex=[0,2*m-2,0];vertex[axis]+=(label[0]==='+'?1:-1)*(2*m-2);
    const [a,r]=line.split('Add: ')[1].split('Remove: ');
    for(const [action,text] of [['add',a],['remove',r]])for(const [v,w] of parseBonds(text)) {
      out.push({action,v:add(v,vertex),w:add(w,vertex)});
    }
  }
  assert.equal(out.filter(p=>p.action==='add').length,32);
  assert.equal(out.filter(p=>p.action==='remove').length,19);return out;
}
export function build(m) {
  const sites=octSites(m).filter(v=>!edgeSite(m,v)),vertices=new Map(sites.map(v=>[key(v),v]));
  const graph=new Map(),damaged=new Set(),free=new Set();
  for(const v of sites) {
    const k=key(v),ns=neighbours(v),rho=coords(m,v).rho;
    graph.set(k,new Set(ns.filter(w=>vertices.has(key(w))&&coords(m,w).rho!==rho).map(key)));
    if(ns.some(w=>inOct(m,w)&&edgeSite(m,w)&&coords(m,w).rho!==rho))damaged.add(k);
    if(ns.some(w=>!inOct(m,w)))free.add(k);
  }
  const claims=new Map();
  for(const k of damaged) {
    const v=vertices.get(k),{Y,Z}=coords(m,v);
    const dY=Z===0?-Math.sign(Y):Math.sign(Z),dZ=Z===0?1:-Math.sign(Y);
    if(Y===0&&Z!==0)continue;
    const w=neighbours(v).find(w=>w[1]-v[1]===dY&&w[2]-v[2]===dZ);
    if(!w)continue;
    const wk=key(w);
    if(vertices.has(wk)&&graph.get(wk).size===1&&free.has(wk)) {
      if(!claims.has(wk))claims.set(wk,[]);claims.get(wk).push(k);
    }
  }
  let merges=0;
  for(const [w,ds] of claims)if(ds.length===1) {
    graph.get(w).add(ds[0]);graph.get(ds[0]).add(w);merges++;
  }
  for(const p of patches(m)) {
    const a=key(p.v),b=key(p.w);assert(vertices.has(a)&&vertices.has(b));
    assert(neighbours(p.v).some(w=>same(w,p.w)));
    if(p.action==='remove') {assert(graph.get(a).has(b));graph.get(a).delete(b);graph.get(b).delete(a);}
    else {assert(!graph.get(a).has(b));graph.get(a).add(b);graph.get(b).add(a);}
  }
  const visited=new Set();let components=0,cycles=0,badEnds=0,badDegrees=0,minSize=Infinity;
  for(const [k,ns]of graph) {
    if(ns.size<1||ns.size>2)badDegrees++;
    if(ns.size===1&&!free.has(k))badEnds++;
    if(visited.has(k))continue;
    const todo=[k],comp=[];visited.add(k);
    while(todo.length){const a=todo.pop();comp.push(a);for(const b of graph.get(a))if(!visited.has(b)){visited.add(b);todo.push(b);}}
    components++;minSize=Math.min(minSize,comp.length);
    if(comp.every(a=>graph.get(a).size===2))cycles++;
  }
  const segOf=new Map(),segments=[];
  for(const k of graph.keys())if(!segOf.has(k)) {
    const id=segments.length,seg={id,sites:[],neighbours:[],row:false},todo=[k];segOf.set(k,id);
    while(todo.length) {
      const a=todo.pop(),v=vertices.get(a),c=coords(m,v);seg.sites.push(v);
      if(damaged.has(a)&&c.Z===0)seg.row=true;
      for(const b of graph.get(a))if(coords(m,vertices.get(b)).rho!==c.rho&&!segOf.has(b)){segOf.set(b,id);todo.push(b);}
    }
    seg.alpha=coords(m,seg.sites[0]).alpha;
    assert(seg.sites.every(v=>coords(m,v).alpha===seg.alpha));
    seg.xhat=Math.min(...seg.sites.map(v=>v[0]))+Math.max(...seg.sites.map(v=>v[0]));
    segments.push(seg);
  }
  for(const [k,ns]of graph)for(const b of ns)if(segOf.get(k)!==segOf.get(b))segments[segOf.get(k)].neighbours.push(segOf.get(b));
  function omega(s){return s.row?1e9+Math.abs(s.xhat):s.alpha>0?1e4*s.alpha+s.xhat:s.xhat;}
  const maxima=segments.filter(s=>s.neighbours.length===2&&s.neighbours.every(id=>omega(segments[id])<omega(s)));
  const secondRowEnds=[];
  for(const [k,ns]of graph)if(ns.size===1) {
    const v=vertices.get(k),f=tetraCoordinates(m,v),A=mod(v[0],2)===0;
    for(const [big,small]of [[0,1],[1,0],[2,3],[3,2]]) {
      if(A?f[big]===2*m-2&&f[small]===-(2*m-2)+4:f[small]===-(2*m-1)&&f[big]===2*m-7)secondRowEnds.push(v);
    }
  }
  const summary={m,sites:sites.length,damaged:damaged.size,merges,components,cycles,badDegrees,badEnds,minSize,
    omegaLocalMaxima:maxima.length,secondRowEnds};
  return {summary,segments,maxima,omega,graph,vertices,damaged};
}

