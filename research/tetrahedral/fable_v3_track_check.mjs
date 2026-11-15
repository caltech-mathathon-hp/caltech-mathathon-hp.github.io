// Independent check of the revised track-object table, using only the lattice inequalities.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {key, neighbours, inOct, coords, up} from './audit_geometry.mjs';

const expected = [
  ['Acap','PPPa',0], ['PPPa','Acap',2], ['PPPa','PPPa',2],
  ['PPPb','PPPb',2], ['PPPb','Tcap',0], ['PPPb','Tcap',2]
].map(JSON.stringify).sort();
const results=[];
for (const m of [80,81,82,336,1000,1000000]) {
  const R=2*m-2;
  const edge=p=>[p,R+p%2,-R+p];
  const cap=p=>{
    const out=neighbours(edge(p)).filter(v=>!inOct(m,v));
    assert.equal(out.length,1); return out[0];
  };
  const object=(kind,p)=>{
    const a=cap(p);
    if(kind.endsWith('cap')) return {sites:new Set([key(a),key(up(m,a,coords(m,a).q))]),attached:[p]};
    const b=cap(p+2), mid=neighbours(a).filter(v=>!inOct(m,v) && neighbours(b).some(w=>key(v)===key(w)));
    assert.equal(mid.length,1);
    return {sites:new Set([key(a),key(mid[0]),key(b)]),attached:[p,p+2]};
  };
  const positions=m<2000 ? Array.from({length:(R-18)/2},(_,i)=>6+2*i) : [6,40,42,60,999998,R-12];
  let combinations=0;
  for(const p0 of positions) {
    const meetings=[]; let n=0;
    for(const p of [p0,p0+1]) for(let d=0;d<=6;d++) {
      const kinds=q=>q%2===0?['Acap','PPPa']:['Tcap','PPPb'];
      for(const k1 of kinds(p)) for(const k2 of kinds(p+d)) {
        if(d===0 && k1>=k2)continue;
        const a=object(k1,p), b=object(k2,p+d);
        const meet=[...a.sites].some(v=>b.sites.has(v));
        if(meet) {
          assert(a.attached.some(v=>b.attached.includes(v)),`Disjoint attachments collide: ${m},${p},${d},${k1},${k2}`);
          meetings.push(JSON.stringify([k1,k2,d]));
        }
        n++;
      }
    }
    assert.equal(n,50);
    assert.deepEqual(meetings.sort(),expected,`Different table at m=${m}, p=${p0}`);
    combinations+=n;
  }
  results.push({m,basePositions:positions.length,combinations,meetingTypes:expected.map(JSON.parse)});
}
const result={method:'Independent lattice-neighbour and octahedron-inequality calculation; no author code imported',results,totalCombinations:results.reduce((n,r)=>n+r.combinations,0),failures:0};
fs.writeFileSync(new URL('./fable_v3_track_results.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
