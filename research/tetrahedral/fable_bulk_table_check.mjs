import assert from 'node:assert/strict';
import fs from 'node:fs';
import {build} from './astra_bulk_model.mjs';
import {coords,key} from './audit_geometry.mjs';
const results=[],all=new Map();
for(const m of [14,15,24,25,30,44,45,50,60]) {
 const b=build(m),segOf=new Map();
 for(const s of b.segments)for(const v of s.sites)segOf.set(key(v),s.id);
 const vertices=[];for(let a=0;a<3;a++)for(const sign of [-1,1]){const v=[0,2*m-2,0];v[a]+=sign*(2*m-2);vertices.push(v);}
 const distance=(v,w)=>Math.max(...v.map((x,i)=>Math.abs(x-w[i])));
 const far=v=>vertices.every(w=>distance(v,w)>12);
 const table=new Map(),clashes=[];
 for(const s of b.segments) {
  const js=s.sites.flatMap(v=>[...b.graph.get(key(v))].filter(w=>segOf.get(w)!==s.id).map(w=>[v,b.vertices.get(w)]));
  if(js.length!==2||!js.every(([v,w])=>far(v)))continue;
  const kind=s.row?'row':s.alpha>0?'Z':'Y';
  const sign=kind==='row'?[Math.sign(coords(m,s.sites[0]).Y),Math.sign(s.xhat)]:[Math.sign(Math.max(...s.sites.map(v=>coords(m,v)[kind==='Z'?'Y':'Z'])))];
  const k=JSON.stringify([kind,sign,kind==='row'?null:s.xhat,Math.abs(s.alpha)<=5?s.alpha:`${((s.alpha%4)+4)%4} mod 4`]);
  const val=JSON.stringify(js.map(([v,w])=>{const t=b.segments[segOf.get(key(w))];return[t.alpha-s.alpha,t.xhat-s.xhat,t.row?'row':t.alpha>0?'Z':'Y'];}).sort());
  if(all.has(k)&&all.get(k)!==val)clashes.push({k,old:all.get(k),val});
  table.set(k,val);all.set(k,val);
 }
 const nearExtents=[];
 for(const V of vertices) {
  const zone=new Set();
  for(const s of b.segments)if(s.sites.some(v=>distance(v,V)<=16&&[...b.graph.get(key(v))].some(w=>segOf.get(w)!==s.id)))zone.add(s.id);
  let grow=new Set(zone);
  for(let i=0;i<6;i++)grow=new Set([...grow,...[...grow].flatMap(id=>b.segments[id].neighbours)]);
  nearExtents.push({V,seeds:zone.size,segments:grow.size,extent:Math.max(...[...grow].flatMap(id=>b.segments[id].sites.map(v=>distance(v,V))))});
 }
 const result={m,tableEntries:table.size,cumulativeEntries:all.size,clashes,nearExtents};results.push(result);console.log(JSON.stringify(result));
}
fs.writeFileSync(new URL('./fable_bulk_table_results.json',import.meta.url),JSON.stringify(results,null,2)+'\n');
