import assert from 'node:assert/strict';
import fs from 'node:fs';
import {inD,inOct,neighbours,same} from './audit_geometry.mjs';
// Section 6's smallest actual instance: K=B=1, m=336, J=132.
// Boundary 22 of the left filler joins the B-sites of D_22 and D_23.
const m=336,R=2*m-2;
const e3=i=>[i,R+i%2,-R+i];
const start=e3(45),end=e3(47);
const path=[[46,672,-626],[47,673,-625],[48,672,-624]];
const full=[start,...path,end];
assert(full.every(inD));assert(path.every(p=>!inOct(m,p)));
assert(inOct(m,start)&&inOct(m,end));
assert(full.slice(1).every((v,i)=>neighbours(full[i]).some(w=>same(w,v))));
assert.equal(new Set(full.map(v=>v.join(','))).size,5);
const radius=owner=>Math.max(...path.flatMap(p=>p.map((x,i)=>Math.abs(x-owner[i]))));
const owners=Array.from({length:R+1},(_,i)=>({index:i,site:e3(i),radius:radius(e3(i))}));
const minimum=Math.min(...owners.map(o=>o.radius));assert.equal(minimum,3);
const ppp={m,K:1,B:1,J:132,boundary:22,start,end,Psites:path,
 claimedOwnerRadius:2,minimumRadiusForAnyOwnerOnE3:minimum,
 bestOwners:owners.filter(o=>o.radius===minimum)};
// Corollary 4's false upper estimate: both sides are positive, and after
// multiplying the difference of their squares by 576*m^2, it is 16*m^2-9.
// Use m=2 for a short exact integer witness.
const leftSquaredNumerator=112n*112n*14n,rightSquaredNumerator=419n*419n;
assert(leftSquaredNumerator>rightSquaredNumerator);
const corollary={m:2,left:'7*sqrt(14)/3',claimedUpperBound:'419/48',
 comparisonAfterMultiplyingBy48:'112*sqrt(14) > 419',
 leftSquared:leftSquaredNumerator.toString(),rightSquared:rightSquaredNumerator.toString(),
 symbolicDifferenceOfSquares:'16*m^2 - 9, after multiplication by 576*m^2'};
const result={ppp,corollary};
console.log(JSON.stringify(result,null,2));
fs.writeFileSync(new URL('./fable_additional_witness_results.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
