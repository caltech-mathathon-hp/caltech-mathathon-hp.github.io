// Check the replacement lexicographic certificate on independently built covers.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {build} from './astra_bulk_model.mjs';
import {localCover} from './astra_local_cover.mjs';
import {key,coords} from './audit_geometry.mjs';
export const rank=s=>s.row?[2,Math.abs(s.xhat),0]:s.alpha>0?[1,s.alpha,s.xhat]:[0,s.xhat,0];
export const compare=(a,b)=>{const x=rank(a),y=rank(b);for(let i=0;i<3;i++)if(x[i]!==y[i])return Math.sign(x[i]-y[i]);return 0;};
const results=[];let certificate=null;
for(const m of [...Array.from({length:32},(_,i)=>i+9),60]) {
 const b=build(m),maxima=[];
 for(const s of b.segments) {
   for(const id of s.neighbours){assert.notEqual(compare(s,b.segments[id]),0);assert(Math.abs(s.xhat-b.segments[id].xhat)<=6);}
   if(s.neighbours.length===2&&s.neighbours.every(id=>compare(s,b.segments[id])>0))maxima.push(s);
 }
 assert.equal(maxima.length,10);assert.equal(b.summary.cycles,0);assert.equal(b.summary.badDegrees,0);assert.equal(b.summary.badEnds,0);assert.equal(b.summary.secondRowEnds.length,0);
 const witnesses=[];
 for(const s of maxima) {
   const todo=[{id:s.id,path:[s.id]}],seen=new Set();let witness=null;
   while(todo.length&&!witness) {
     const {id,path}=todo.shift();if(seen.has(id))continue;seen.add(id);
     const t=b.segments[id],end=t.sites.some(v=>b.graph.get(key(v)).size===1);
     if(end||compare(t,s)>0){witness={path,end,larger:compare(t,s)>0};break;}
     if(path.length<=6)for(const n of t.neighbours)todo.push({id:n,path:[...path,n]});
   }
   assert(witness,`No escape for m=${m}, segment ${s.id}`);
   witnesses.push({start:s.sites,rank:rank(s),...witness,segments:witness.path.map(id=>b.segments[id].sites)});
 }
 if(m===30)certificate=witnesses;
 results.push({m,maxima:maxima.length,maximumTransitions:Math.max(...witnesses.map(w=>w.path.length-1)),sites:b.summary.sites});
 console.log(JSON.stringify(results.at(-1)));
}
const large=[];
for(const m of [50034,1000000]) {
 const c=localCover(m),P=c.segment([0,4,0]),Q=c.segment([-1,3,1]);
 assert(compare(Q,P)>0);large.push({m,rankP:rank(P),rankQ:rank(Q)});
}
fs.writeFileSync(new URL('./astra_rank_results.json',import.meta.url),JSON.stringify({results,large,certificate},null,2)+'\n');
