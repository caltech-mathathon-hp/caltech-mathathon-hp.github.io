// Search explicit frame links using the displayed local cover and N1 exclusions.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {localCover} from './astra_local_cover.mjs';
import {coords,inOct,edgeSite,neighbours,key,same,fs as tetra,mod,up} from './audit_geometry.mjs';

export function frame(m,K) {
  const cover=localCover(m),R=2*m-2;
  const e1=i=>[mod(i,2),R+i,-R+i];
  const e2=i=>[R-i,R+i,mod(i,2)?-1:0];
  const slots=new Set();
  for(let k=1;k<=K+1;k++)for(const i of [6*k,6*k+1])slots.add(key(e1(i)));
  for(let k=0;k<=K;k++)for(let i=10*k+6;i<=10*k+11;i++)slots.add(key(e2(i)));
  const bulkEndCache=new Map(),forbiddenCache=new Map();
  const bulkEnd=v=>{
    const k=key(v);if(bulkEndCache.has(k))return bulkEndCache.get(k);
    const answer=inOct(m,v)&&!edgeSite(m,v)&&cover.adjacent(v).length===1;
    bulkEndCache.set(k,answer);return answer;
  };
  const surfaceSource=p=>neighbours(p).find(v=>inOct(m,v));
  const special=v=>slots.has(key(v))||same(v,e1(2))||
    (mod(v[0],2)===1&&tetra(m,v).filter(f=>f===2*m-3).length===2);
  function forbidden(p) {
    const k=key(p);if(forbiddenCache.has(k))return forbiddenCache.get(k);
    let bad=false;
    const v=surfaceSource(p);if(v&&(special(v)||bulkEnd(v)))bad=true;
    if(!bad)for(const q of neighbours(p))if(coords(m,q).rho===coords(m,p).rho-2) {
      const v=surfaceSource(q);
      if(v&&bulkEnd(v))bad=true;
    }
    forbiddenCache.set(k,bad);return bad;
  }
  const inSkin=v=>!inOct(m,v)&&inOct(m+2,[v[0],v[1]+4,v[2]]);
  function link(a,b,n) {
    const path=[a],visited=new Set([key(a)]);let answer=null;
    function dfs(v,left) {
      if(left===0){if(neighbours(v).some(w=>same(w,b)))answer=path.slice(1);return !!answer;}
      const candidates=neighbours(v).sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2]);
      for(const w of candidates) {
        if(visited.has(key(w))||!inSkin(w)||forbidden(w))continue;
        if(Math.max(...w.map((x,i)=>Math.abs(x-b[i])))>left)continue;
        path.push(w);visited.add(key(w));if(dfs(w,left-1))return true;visited.delete(key(w));path.pop();
      }
      return false;
    }
    dfs(a,n);assert(answer,`No frame link: m=${m} K=${K} ${key(a)} -> ${key(b)} P=${n}`);return answer;
  }
  const definitions=[{name:'e1-start',a:e1(0),b:e1(3),n:6}];
  for(let k=1;k<=K+1;k++)definitions.push({name:`e1-slot-${k}`,a:e1(6*k-1),b:e1(6*k+2),n:6});
  definitions.push({name:'e1-end',a:e1(R-2),b:e1(R),n:3});
  definitions.push({name:'e2-start',a:e2(0),b:e2(2),n:3});
  for(let k=0;k<=K;k++)definitions.push({name:`e2-slot-${k}`,a:e2(10*k+5),b:e2(10*k+12),n:10});
  definitions.push({name:'e2-end',a:e2(R-2),b:e2(R),n:3});
  const used=new Set(),rows=[];
  const templates={
    'e1-start':[[-1,1,-1],[0,2,-2],[1,3,-1],[0,4,0],[1,5,1],[2,4,2]],
    'e1-slot':[[1,1,-1],[0,2,-2],[-1,3,-1],[0,4,0],[-1,5,1],[-2,4,2]],
    'e1-end':[[-1,1,-1],[-2,2,0],[-1,3,1]],
    'e2-start':[[1,1,1],[0,2,2],[-1,3,1]],
    'e2-slot':[[1,1,-1],[2,2,0],[1,3,1],[0,4,0],[-1,5,1],[-2,6,0],[-3,7,1],[-4,8,0],[-5,9,1],[-6,8,2]],
    'e2-end':[[1,1,1],[0,2,2],[-1,3,1]]
  };
  for(const d of definitions) {
    const path=link(d.a,d.b,d.n);
    const offsets=path.map(p=>p.map((x,i)=>x-d.a[i]));
    assert.deepEqual(offsets,templates[d.name.replace(/-slot-\d+$/,'-slot')],'path agrees with the displayed fixed template');
    for(const p of path){assert(!used.has(key(p)),`frame collision at ${key(p)}`);used.add(key(p));}
    rows.push({name:d.name,from:d.a,to:d.b,offsets});
  }
  const caps=[];
  for(let k=1;k<=K+1;k++)for(const i of [6*k,6*k+1])caps.push({name:`entry-${k}-${i%2?'b':'a'}`,v:e1(i)});
  for(let k=0;k<=K;k++)for(const i of [10*k+7,10*k+10])caps.push({name:`exit-${k}-${i%2?'b':'a'}`,v:e2(i)});
  caps.push({name:'left-filler',v:e1(2)},{name:'right-filler',v:e2(1)},{name:'first-H',v:e1(R-1)});
  const borrowing=[];
  for(const c of caps) {
    const p=neighbours(c.v).find(v=>!inOct(m,v));
    const j=neighbours(c.v).findIndex(v=>same(v,p)),sign=mod(c.v[0],2)?-1:1;
    const t=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]][j],q=[sign*t[1],sign*t[2]];
    const own=up(m,p,q);
    if(used.has(key(own))) {
      const choices=[];
      for(const w of neighbours(p))if(inSkin(w)&&!used.has(key(w))) {
        for(const pp of neighbours(w))if(coords(m,pp).rho===coords(m,w).rho-2) {
          const v=surfaceSource(pp);
          if(v&&!bulkEnd(v)&&!same(v,c.v))choices.push({second:w,source:v});
        }
      }
      borrowing.push({name:c.name,p,choices});
    }
  }
  return {m,K,rows,borrowing};
}
const results=[];
if(process.argv[1]?.endsWith('astra_near_field.mjs'))for(const [m,K]of [[80,1],[80,6],[336,1],[1576,6],[10000,20]]) {
  const r=frame(m,K);results.push(r);
  console.log(JSON.stringify({m,K,links:r.rows.length,borrowedCaps:r.borrowing.length,emptyBorrowChoices:r.borrowing.filter(b=>!b.choices.length).map(b=>b.name)}));
}
if(results.length)fs.writeFileSync(new URL('./astra_frame_templates.json',import.meta.url),JSON.stringify(results,null,2)+'\n');
