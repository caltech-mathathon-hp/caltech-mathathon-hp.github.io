// Independent shortest-path audit of exactly the two rows and two columns
// specified for an entry tether in section 8.4, with Appendix C's borrowed arm.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {ts,mod,key,neighbours,inOct,up,fs as tetra} from './audit_geometry.mjs';
const results=[];
for(const [m,K,J,C]of [[80,8,14,4],[336,1,132,66],[732,1,264,198]]) {
 const R=2*m-2;
 const fromF=f=>[0,1,2].map(i=>ts.reduce((s,t,j)=>s+f[j]*t[i]/4,0)+(i===1?R:0));
 const surf=(j,a,b,c)=>fromF([2*(m+2*j)-3-4*a,2*(m+2*j)-3-4*b,2*(m+2*j)-3-4*c,-(2*(m+2*j)-1)]);
 const gamma=(j,a,b,c)=>fromF([2*(m+2*j)-2-4*a,2*(m+2*j)-2-4*b,2*(m+2*j)-2-4*c,-(2*(m+2*j)-2)]);
 for(let k=1;k<=K+1;k++) {
  const j=k+1,jk=J+(k-1)*(C+2),a=[0,R+6*k,-R+6*k];
  const start=a.map((x,i)=>x+[2,2,0][i]),second=a.map((x,i)=>x+[3,3,1][i]);
  const targetH=[2*jk+1,R+1,-R+2*jk+1];
  const target=neighbours(targetH).find(v=>!inOct(m,v));
  const col1=[start,second],col2=[target];
  for(const col of [col1,col2])while(tetra(m,col.at(-1))[3]!==-R-4*j)col.push(up(m,col.at(-1),[1,-1]));
  const allowed=new Map();const put=v=>allowed.set(key(v),v);
  for(const col of [col1,col2])col.forEach(put);
  const S=m+2*j-2;
  // All surface/sub-surface sites on either full row, a superset of the
  // finite row portions described in the manuscript. A lower bound here
  // is therefore also a lower bound for those portions.
  for(let aa=0;aa<=S;aa++)for(let bb=0;bb<=S-aa;bb++) {
   const cc=S-aa-bb;
   if(cc===1||bb===j-1)put(surf(j,aa,bb,cc));
  }
  for(let aa=1;aa<=S;aa++)for(let bb=1;bb<=S+1-aa;bb++) {
   const cc=S+1-aa-bb;
   if(cc>=1&&(cc===1||bb===j-1))put(gamma(j,aa,bb,cc));
  }
  const src=key(start),dst=key(target),previous=new Map([[src,null]]),queue=[src];
  for(let n=0;n<queue.length&&!previous.has(dst);n++)for(const v of neighbours(allowed.get(queue[n]))) {
   const q=key(v);if(allowed.has(q)&&!previous.has(q)){previous.set(q,queue[n]);queue.push(q);}
  }
  assert(previous.has(dst));const path=[];
  for(let q=dst;q!==null;q=previous.get(q))path.push(allowed.get(q));path.reverse();
  assert(path.every(v=>!inOct(m,v)));
  const slack=path.length-(2*jk+3),claimed=K<=6?(k===1?6:10*k-2):null;
  assert.equal(slack,10*k+2);
  const r={m,K,J,C,k,skin:j,jk,startCap:start,borrowedSecond:second,targetCap:target,
   shortestPsitesInStatedRowsAndColumns:path.length,slack,printedSlack:claimed,
   printedPsites:claimed===null?null:2*jk+3+claimed,allowedSites:allowed.size};
  if(m===336&&k===1)r.shortestPath=path;
  results.push(r);console.log(JSON.stringify({...r,shortestPath:undefined}));
 }
}
fs.writeFileSync(new URL('./fable_tether_witness_results.json',import.meta.url),JSON.stringify(results,null,2)+'\n');
