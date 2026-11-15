// Independent coordinate tests of the translations specified in Proposition A.
import fs from 'node:fs';
import assert from 'node:assert/strict';
import {ts,mod,key,add,coords,inOct,edgeSite,neighbours,same} from './audit_geometry.mjs';
let moduleText=fs.readFileSync(new URL('./astra_local_cover.mjs',import.meta.url),'utf8');
moduleText=moduleText.replace('../../background/HP_tetrahedral_proof_Astra.md','./fable_review_v2_2026_11_14/HP_tetrahedral_review/HP_tetrahedral_proof.md').replace("sites.size<100,'this witness should have a short segment'","sites.size<4*m+20,'finite line intersection size bound'");
const modulePath=new URL('./fable_v2_local_cover.mjs',import.meta.url);fs.writeFileSync(modulePath,moduleText);
const {localCover}=await import(modulePath.href);
const models=new Map();
function model(m) {
 if(models.has(m))return models.get(m);
 const cover=localCover(m),bySite=new Map(),R=2*m-2,vertices=[];
 for(let axis=0;axis<3;axis++)for(const sign of [-1,1]){const v=[0,R,0];v[axis]+=sign*R;vertices.push(v);}
 const edges=[];
 for(let a=0;a<6;a++)for(let b=a+1;b<6;b++) {
  const V=vertices[a],W=vertices[b];
  if(V.filter((x,i)=>x!==W[i]).length!==2)continue;
  const u=W.map((x,i)=>(x-V[i])/(m-1));let pair=null;
  for(const ta of ts)for(const tb of ts)if(ta.every((x,i)=>x-tb[i]===u[i]))pair=[ta,tb];
  assert(pair);const [ta,tb]=pair;
  const axis=V.findIndex((x,i)=>x===W[i]);
  edges.push({a,b,axis,at:i=>V.map((x,j)=>x+Math.ceil(i/2)*ta[j]-Math.floor(i/2)*tb[j])});
 }
 function segment(v) {
  const k=key(v);if(bySite.has(k))return bySite.get(k);
  const s=cover.segment(v);s.id=s.sites.map(key).sort()[0];
  s.jointPairs=s.sites.flatMap(u=>cover.adjacent(u).filter(w=>coords(m,u).rho===coords(m,w).rho).map(w=>({from:u,to:w})));
  for(const v of s.sites)bySite.set(key(v),s);return s;
 }
 const distance=(v,w)=>Math.max(...v.map((x,i)=>Math.abs(x-w[i])));
 const far=v=>vertices.every(V=>distance(v,V)>12);
 const kind=s=>s.row?'row':s.alpha>0?'Z':'Y';
 function descriptor(s) {
  const k=kind(s);
  const sign=k==='row'?[Math.sign(coords(m,s.sites[0]).Y),Math.sign(s.xhat)]:[Math.sign(Math.max(...s.sites.map(v=>coords(m,v)[k==='Z'?'Y':'Z'])))];
  const key=[k,sign,k==='row'?null:s.xhat,Math.abs(s.alpha)<=5?s.alpha:`${mod(s.alpha,4)} mod 4`];
  const value=s.jointPairs.map(({to})=>{const q=segment(to);return[q.alpha-s.alpha,q.xhat-s.xhat,kind(q)];});
  return {key,value:[...new Set(value.map(v=>JSON.stringify(v)))].sort()};
 }
 const result={m,R,vertices,edges,cover,segment,descriptor,far};models.set(m,result);return result;
}
const results=[];
for(const m of [81,82,336,1000]) {
 const c=model(m),m0=m%2?59:60,m1=m%2?79:80,base0=model(m0),base1=model(m1),seen=new Set(),failures=[],counts={A3:0,A4:0,A5:0};
 const indices=new Set([14,15,16,17,20,21,30,31,42,43,Math.floor(c.R/2)-1,Math.floor(c.R/2),Math.floor(c.R/2)+1,c.R-42,c.R-43,c.R-30,c.R-31,c.R-14,c.R-15]);
 for(const edge of c.edges.filter(e=>e.axis!==1))for(const i of indices) {
  const e=edge.at(i),near=new Map();
  for(const v of neighbours(e))for(const w of [v,...neighbours(v)])if(inOct(m,w)&&!edgeSite(m,w))near.set(key(w),w);
  for(const v of near.values()) {
   if(!c.cover.adjacent(v).some(w=>coords(m,w).rho===coords(m,v).rho))continue;
   const s=c.segment(v);if(seen.has(s.id))continue;seen.add(s.id);
   if(s.jointPairs.length!==2||!s.jointPairs.every(p=>c.far(p.from)))continue;
   const isX=Math.max(...s.sites.map(v=>Math.abs(v[0])))<=5;
   let which,base,mapped;
   const end=s.jointPairs[0].from;
   if(isX&&Math.abs(s.alpha)<=2*m-38) {
    which='A3';base=base0;
    let ap=s.alpha;
    if(Math.abs(ap)>2*m0-38){let x=2*m0-38;while(mod(x,4)!==mod(Math.abs(ap),4))x--;ap=Math.sign(ap)*x;}
    const dm=m-m0,dy=dm+(s.alpha-ap)/2,dz=dm-(s.alpha-ap)/2,q=coords(m,end).q;
    mapped=[end[0],end[1]-2*dm-q[0]*dy,end[2]-q[1]*dz];
   } else if(isX) {
    which='A4';base=base0;
    const axis=s.alpha>0?1:2,sign=Math.sign(coords(m,end)[axis===1?'Y':'Z']);
    const V=[0,c.R,0],V0=[0,base.R,0];V[axis]+=sign*c.R;V0[axis]+=sign*base.R;
    mapped=end.map((x,t)=>x+V0[t]-V[t]);
   } else {
    which='A5';base=base1;assert.equal(edge.axis,2);
    const ee=base.edges.find(e=>e.a===edge.a&&e.b===edge.b);assert(ee);
    let delta;
    if(i>=42&&i<=2*m-44) {
     for(let ip=42;ip<=47;ip++)if(ip%2===i%2) {
      const ep=ee.at(ip),d=ep.map((x,t)=>x-e[t]),p=add(end,d);
      if(mod(coords(base.m,p).alpha-s.alpha,4)===0){delta=d;break;}
     }
     assert(delta);
    } else {
     const vertex=i<42?edge.a:edge.b;
     delta=base.vertices[vertex].map((x,t)=>x-c.vertices[vertex][t]);
    }
    mapped=add(end,delta);
   }
   counts[which]++;
   try {
    assert(inOct(base.m,mapped)&&!edgeSite(base.m,mapped));
    const r=base.segment(mapped);
    assert(r.jointPairs.length===2&&r.jointPairs.every(p=>base.far(p.from)));
    assert.deepEqual(base.descriptor(r),c.descriptor(s));
   } catch(error) { failures.push({which,edge:[edge.a,edge.b],i,start:end,mapped,alpha:s.alpha,kind:s.row?'row':'nonrow',error:error.message}); }
  }
 }
 const result={m,counts,failures};results.push(result);console.log(JSON.stringify(result));
 // Free the large-size caches after each size; keep only the small references.
 models.delete(m);
}
fs.writeFileSync(new URL('./fable_v2_proposition_results.json',import.meta.url),JSON.stringify(results,null,2)+'\n');
