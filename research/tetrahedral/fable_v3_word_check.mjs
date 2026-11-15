// Check the supplied sample against an independent implementation of section 6 and the bulk rules.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import crypto from 'node:crypto';
import {build} from './astra_bulk_model.mjs';
const root=new URL('./fable_review_v3_2026_11_14/HP_tetrahedral_review/',import.meta.url);
const current=fs.readFileSync(new URL('HP_tetrahedral_proof.md',root),'utf8');
const astra=fs.readFileSync(new URL('../../background/HP_tetrahedral_proof_Astra.md',import.meta.url),'utf8');
const patches=s=>s.split(/\r?\n/).filter(l=>l.startsWith('* Vertex '));
assert.deepEqual(patches(current),patches(astra),'Independent bulk implementation uses different patch lists');
// Parameters of runbg5.sh's sample: build3.py 80 12 "[4,8,8,4];none" 14 nochain ... word.
const m=80,K=2,C=12,J=14,R=35,items=[4,8,8,4], edgeLength=2*m-2;
assert.equal(m,J+K*(C+2)+R+3);
const raw=fs.readFileSync(new URL('sample_fold/word_rle_m80_items_4_8_8_4.txt',root),'utf8').trim();
const actual=raw.split(/\s+/).map(s=>{assert(/^[HP][1-9][0-9]*$/.test(s));return [s[0],Number(s.slice(1))];});
for(let i=1;i<actual.length;i++)assert.notEqual(actual[i-1][0],actual[i][0]);
const unit=(runs,start,end)=>({runs,start,end});
const dimer=q=>Array.from({length:2*q-1},(_,i)=>i%2?['P',3]:['H',2]);
const units=[unit([['H',1]],'B','B'),...Array.from({length:3},()=>unit([['H',1]],'A','A'))];
const frame=[['H',1]];
const skips1=new Set([1,2,edgeLength-1]),skips2=new Set([1,edgeLength-1]);
for(let k=1;k<=K+1;k++)for(const i of [6*k,6*k+1])skips1.add(i);
for(let k=0;k<=K;k++)for(let i=10*k+6;i<=10*k+11;i++)skips2.add(edgeLength-i);
for(const skips of [skips1,skips2]) {
  let previous=0;
  for(let i=1;i<=edgeLength;) {
    if(skips.has(i)){i++;continue;}
    const start=i;while(i<edgeLength&&!skips.has(i+1))i++;
    const end=i, omitted=start-previous-1;
    assert(omitted>0);
    frame.push(['P',omitted+(omitted%2?2:4)],['H',end-start+1]);
    previous=end;i++;
  }
}
units.push(unit(frame,'A','A'));
for(let k=1;k<=K+1;k++) {
  const j=J+(k-1)*(C+2);
  units.push(unit([['H',2],['P',2*j+3+10*k+2],...dimer(2),['P',2*(m-2-j)+3+14*K+22-6*k],...dimer(3)],'A','A'));
}
units.push(unit(dimer(J),'A','A'));
for(const q of items)units.push(unit(dimer(q),'A','A'));
units.push(unit(dimer(R),'A','B'));
for(let i=0;i<3;i++)units.push(unit(dimer(3*(m-2)),'B','B'));
console.log('Building the independent bulk cover for m=80...');
const model=build(m), {graph,vertices}=model;
assert.equal(model.summary.badDegrees+model.summary.badEnds+model.summary.cycles,0);
const seen=new Set(),expectedBulk=new Map();let bulkCount=0;
const add=(map,k)=>map.set(k,(map.get(k)||0)+1);
for(const [start,adj] of graph) {
  if(adj.size!==1||seen.has(start))continue;
  let p=start,previous=null,length=0,last=null;
  while(p!==null) {
    assert(!seen.has(p));seen.add(p);length++;last=p;
    const next=[...graph.get(p)].find(q=>q!==previous)??null;
    previous=p;p=next;
  }
  const aEnds=[start,last].filter(v=>vertices.get(v)[0]%2===0).length;
  add(expectedBulk,JSON.stringify([length,aEnds]));bulkCount++;
}
assert.equal(seen.size,graph.size);
const totalUnits=units.length+bulkCount,w=2*(totalUnits-1),Lstar=1000*(m+w+1)+6;
const expectedPrefix=[];
for(let i=0;i<units.length;i++) {
  if(i)expectedPrefix.push(['P',Lstar+(units[i-1].end===units[i].start?1:0)]);
  expectedPrefix.push(...units[i].runs);
}
assert.deepEqual(actual.slice(0,expectedPrefix.length),expectedPrefix,'Non-bulk word differs from section 6');
const observedBulk=new Map();let previousEnd=units.at(-1).end;
for(let i=expectedPrefix.length;i<actual.length-1;i+=2) {
  const [pc,L]=actual[i],[hc,length]=actual[i+1];
  assert.equal(pc,'P');assert.equal(hc,'H');assert(L===Lstar||L===Lstar+1);
  const start=L%2?previousEnd:(previousEnd==='A'?'B':'A');
  const end=length%2?start:(start==='A'?'B':'A');
  add(observedBulk,JSON.stringify([length,[start,end].filter(s=>s==='A').length]));previousEnd=end;
}
assert.deepEqual(actual.at(-1),['P',1]);
assert.deepEqual([...observedBulk].sort(),[...expectedBulk].sort(),'Bulk run lengths or endpoint parity disagree');
const H=actual.filter(([c])=>c==='H').reduce((n,[,s])=>n+s,0),totalLength=actual.reduce((n,[,s])=>n+s,0);
assert.equal(H,m*(4*m*m-1)/3);
const result={method:'Independent section 6 construction for the complete non-bulk prefix; independent full bulk cover for bulk run-length/endpoint-colour multiset (not Python set iteration order)',m,K,C,J,R,items,nonBulkUnits:units.length,bulkUnits:bulkCount,totalUnits,w,Lstar,runs:actual.length,H,totalLength,md5:crypto.createHash('md5').update(raw).digest('hex'),checks:{nonBulkWordExact:true,bulkLengthAndEndpointColourMultiset:true,allBulkVerticesCovered:true,finalP:true},failures:0};
fs.writeFileSync(new URL('./fable_v3_word_results.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
