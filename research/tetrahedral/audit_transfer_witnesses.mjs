// Exact counterexamples to the stated transfer/certificate claims.
// The large-m witness is checked locally, without enumerating Oct(m).
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {coords,inD,inOct,edgeSite,depths,neighbours,key,add,same} from './audit_geometry.mjs';
const text=fs.readFileSync(new URL('../../background/HP_tetrahedral_proof.md',import.meta.url),'utf8');
function localCover(m) {
  const preCache=new Map(),candCache=new Map(),modifications=new Map();
  const inX=v=>inOct(m,v)&&!edgeSite(m,v);
  const pre=v=>{
    const k=key(v);if(preCache.has(k))return preCache.get(k);
    const out=neighbours(v).filter(w=>inX(w)&&coords(m,w).rho!==coords(m,v).rho);
    preCache.set(k,out);return out;
  };
  const damaged=v=>inX(v)&&neighbours(v).some(w=>inOct(m,w)&&edgeSite(m,w)&&coords(m,w).rho!==coords(m,v).rho);
  function candidate(v) {
    const k=key(v);if(candCache.has(k))return candCache.get(k);
    let out=null;
    if(damaged(v)) {
      const {Y,Z}=coords(m,v),dY=Z===0?-Math.sign(Y):Math.sign(Z),dZ=Z===0?1:-Math.sign(Y);
      if(Y!==0||Z===0) {
        const w=neighbours(v).find(w=>w[1]-v[1]===dY&&w[2]-v[2]===dZ);
        if(w&&inX(w)&&pre(w).length===1&&neighbours(w).some(z=>!inOct(m,z)))out=w;
      }
    }
    candCache.set(k,out);return out;
  }
  function claimants(w) {return neighbours(w).filter(v=>{const c=candidate(v);return c&&same(c,w);});}
  for(const line of text.split(/\r?\n/).filter(l=>l.startsWith('* Vertex '))) {
    const label=line.match(/^\* Vertex ([−+][xyz])/)[1],axis='xyz'.indexOf(label[1]);
    const vertex=[0,2*m-2,0];vertex[axis]+=(label[0]==='+'?1:-1)*(2*m-2);
    const [adds,removes]=line.split('Add: ')[1].split('Remove: ');
    for(const [operation,s] of [['add',adds],['remove',removes]]) {
      for(const a of s.matchAll(/\((-?\d+),(-?\d+),(-?\d+)\)–\((-?\d+),(-?\d+),(-?\d+)\)/g)) {
        const v=add(a.slice(1,4).map(Number),vertex),w=add(a.slice(4,7).map(Number),vertex);
        for(const [v0,w0] of [[v,w],[w,v]]) {
          if(!modifications.has(key(v0)))modifications.set(key(v0),[]);
          modifications.get(key(v0)).push({operation,w:w0});
        }
      }
    }
  }
  function adjacent(v) {
    assert(inX(v));const ns=new Map(pre(v).map(w=>[key(w),w]));
    const c=candidate(v);if(c&&claimants(c).length===1)ns.set(key(c),c);
    const claims=claimants(v);if(claims.length===1)ns.set(key(claims[0]),claims[0]);
    for(const p of modifications.get(key(v))||[]) {
      if(p.operation==='remove'){assert(ns.has(key(p.w)));ns.delete(key(p.w));}
      else {assert(!ns.has(key(p.w)));ns.set(key(p.w),p.w);}
    }
    assert(ns.size>=1&&ns.size<=2);return [...ns.values()];
  }
  function segment(start) {
    const todo=[start],sites=new Map([[key(start),start]]),joints=[];
    while(todo.length) {
      const v=todo.pop();
      for(const w of adjacent(v)) {
        if(coords(m,w).rho===coords(m,v).rho)joints.push(w);
        else if(!sites.has(key(w))){sites.set(key(w),w);todo.push(w);}
      }
      assert(sites.size<100,'this witness should have a short segment');
    }
    const vs=[...sites.values()],alpha=coords(m,start).alpha;
    assert(vs.every(v=>coords(m,v).alpha===alpha));
    const xhat=Math.min(...vs.map(v=>v[0]))+Math.max(...vs.map(v=>v[0]));
    const row=vs.some(v=>damaged(v)&&coords(m,v).Z===0);
    return {sites:vs,joints,alpha,xhat,row,omega:row?1e9+Math.abs(xhat):alpha>0?1e4*alpha+xhat:xhat};
  }
  return {segment,adjacent};
}
const output=[];
for(const m of [30,50034]) {
  const cover=localCover(m);
  const P=cover.segment([0,4,0]),Q=cover.segment([-1,3,1]),R=cover.segment([2,4,-2]);
  assert.deepEqual(new Set(P.sites.map(key)),new Set(['0,4,0','1,3,-1']));
  assert.deepEqual(new Set(Q.sites.map(key)),new Set(['-1,3,1']));
  assert.deepEqual(new Set(R.sites.map(key)),new Set(['2,4,-2']));
  assert.deepEqual(new Set(P.joints.map(key)),new Set(['-1,3,1','2,4,-2']));
  assert(!P.row&&Q.row&&!R.row);
  assert.equal(P.alpha,2*m-7);assert.equal(R.alpha,2*m-9);
  const localMaximum=P.omega>Q.omega&&P.omega>R.omega;
  assert.equal(localMaximum,m===50034);
  const seen=new Set(),queue=[{start:P.sites[0],distance:0}],escapes=[];
  while(queue.length) {
    const {start,distance}=queue.shift(),s=cover.segment(start),id=s.sites.map(key).sort().join(';');
    if(seen.has(id))continue;seen.add(id);
    const end=s.sites.some(v=>cover.adjacent(v).length===1);
    if(end||s.omega>P.omega)escapes.push({distance,end,largerOmega:s.omega>P.omega,sites:s.sites});
    if(distance<6)for(const j of s.joints)queue.push({start:j,distance:distance+1});
  }
  if(m===50034) {
    assert.equal(escapes.length,0,'the new maximum has no six-transition escape');
    const positiveP=cover.segment([0,4*m-8,0]);
    assert.equal(positiveP.joints.length,2);
    assert(positiveP.joints.every(v=>cover.segment(v).omega<positiveP.omega));
  }
  output.push({m,P,Q,R,PisLocalMaximum:localMaximum,escapeWithinSixSegments:escapes});
}
// This large m is an actual Section 6 size, not an unrestricted auxiliary parameter.
const K=1,B=252,Sigma=18*K+40,C=(Sigma+8)*B;
assert.equal((K+2)*C+38*K+100,50034);
const m=11,R=0,Rprime=10,v=[0,30,10],after=[-2,28,10];
assert(4*m>=3*R+2*Rprime+24);
assert(coords(m,v).Y<Rprime+2&&Math.abs(coords(m,v).Z)<Rprime+2);
assert(inOct(m,v)&&inD(after)&&!inOct(m-1,after));
assert(!inOct(m-1,[2,28,10]),'the other permitted x-sign fails as well');
console.log(JSON.stringify({bulkOmegaCounterexample:output,validReductionParameters:{K,B,m:50034},
  lemmaTCounterexample:{m,R,Rprime,v,before:depths(m,v),after,afterDepths:depths(m-1,after)}},null,2));
