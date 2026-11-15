import assert from 'node:assert/strict';
import fs from 'node:fs';
import {coords,inD,inOct,edgeSite,neighbours,up,key} from './audit_geometry.mjs';
import {localCover} from './fable_v2_local_cover.mjs';
const distance=(u,v)=>Math.max(...u.map((x,i)=>Math.abs(x-v[i])));
const edge=(m,i)=>[i,2*m-2+i%2,-(2*m-2)+i];
// Ordinary PPP owners in an actual reduction: boundary 22 is b, boundary 23 is a.
const owner1=edge(336,45),owner2=edge(336,46);
assert.equal(distance(owner1,owner2),1);
const ordinary={m:336,K:1,B:1,J:132,boundaries:[22,23],owners:[owner1,owner2],
 ownerIndices:[45,46],actualOwnerDistance:distance(owner1,owner2),claimedDistance:2};
// A valid layout of family F with two consecutive item cuts four boundaries apart.
const layout={m:80,K:1,J:14,C:12,R:49,items:[[4,4,4]]};
assert.equal(layout.m,layout.J+layout.K*(layout.C+2)+layout.R+3);
assert(layout.m>=80&&layout.m>=5*layout.K+40&&layout.J>=14&&layout.R>=15);
const cuts=[19,23],capOwners=[edge(80,40),edge(80,46)];
assert.equal(distance(...capOwners),6);
const caps=capOwners.map(h=>neighbours(h).find(p=>!inOct(80,p)));
const objects=caps.map(p=>[p,up(80,p,[-1,-1])]);
assert.equal(new Set(objects.flat().map(key)).size,4);
const T8={cuts:[],Rboundary:15,Lboundary:19,matchingOwners:[edge(80,32),edge(80,38)]};
const Tcut={cuts:[19,29]};
// This is an omitted boundary-labelled case, not an unrepresented geometric
// pair: T8's R/L caps give identical translated objects. Record that distinction.
const translatedObjects=T8.matchingOwners.map(h=>{const p=neighbours(h).find(p=>!inOct(80,p));return[p,up(80,p,[-1,-1])];});
const delta=T8.matchingOwners[0].map((x,i)=>x-capOwners[0][i]);
assert.deepEqual(objects.map(o=>o.map(v=>v.map((x,i)=>x+delta[i]))),translatedObjects);
const cutPair={layout,cuts,ownerIndices:[40,46],owners:capOwners,ownerDistance:6,
 boundaryDistance:4,objects,selfAvoiding:true,referenceCuts:{T8:T8.cuts,Tcut:Tcut.cuts},
 geometricRepresentative:{layout:'T8',boundaryTypes:['R','L'],ownerIndices:[32,38],delta}};
// A counterexample to the numeric |Y|>=12 assertion in Proposition A(A5).
const m=336,R=2*m-2,cover=localCover(m),s=cover.segment([-657,659,1]);
assert(s.row&&s.sites.length===2&&s.joints.length===2);
const vertices=[];for(let axis=0;axis<3;axis++)for(const sign of [-1,1]){const v=[0,R,0];v[axis]+=sign*R;vertices.push(v);}
const joints=s.sites.flatMap(v=>cover.adjacent(v).filter(w=>coords(m,v).rho===coords(m,w).rho).map(w=>({from:v,to:w,distanceToNearestVertex:Math.min(...vertices.map(V=>distance(v,V)))})));
assert(joints.every(j=>j.distanceToNearestVertex>12));
const minAbsY=Math.min(...s.sites.map(v=>Math.abs(coords(m,v).Y)));assert.equal(minAbsY,11);
const A5={m,segment:s.sites,alpha:s.alpha,row:s.row,joints,minAbsY,claimedLowerBound:12};
// Literal domain issue: canonical bulk ends are in X_m, hence are not edge sites.
let bulkEnd=null;
for(let x=-12;x<=12&&!bulkEnd;x++)for(let y=0;y<=16&&!bulkEnd;y++)for(let z=-12;z<=12&&!bulkEnd;z++) {
 const v=[x,y,z];if(inD(v)&&inOct(m,v)&&!edgeSite(m,v)&&cover.adjacent(v).length===1)bulkEnd=v;
}
assert(bulkEnd);const cap=neighbours(bulkEnd).find(p=>!inOct(m,p));assert(cap);
const ownerDomain={m,bulkEnd,cap,isEdgeSite:edgeSite(m,bulkEnd),coverDegree:cover.adjacent(bulkEnd).length};
const result={ordinary,cutPair,A5,ownerDomain};console.log(JSON.stringify(result,null,2));
fs.writeFileSync(new URL('./fable_v2_coverage_results.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
