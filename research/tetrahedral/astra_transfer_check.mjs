// Exhaustive finite checks of the strengthened transfer statement.
import assert from 'node:assert/strict';
import {inD,depths,coords} from './audit_geometry.mjs';
let checked=0;const cases=[];
for(const R of [0,2,6])for(const Rp of [0,3,10]) {
 const lower=Math.ceil(Math.max(4*R+20,2*R+4*Rp+22)/4);
 for(const m of [lower,lower+1]) {
   const bound=2*m-1+R;let count=0;
   for(let x=-bound;x<=bound;x++)for(let Y=-bound+Math.abs(x);Y<=bound-Math.abs(x);Y++) {
     if((x-Y)%2!==0)continue;
     const zmax=bound-Math.abs(x)-Math.abs(Y);
     for(let z=-zmax;z<=zmax;z++) {
       const v=[x,Y+2*m-2,z];if(!inD(v))continue;
       const before=depths(m,v);if(before.some(d=>d<-R))continue;
       const Z=z-1,rel=[x,Y,z],eligible=[0];if(Math.abs(Y)>=Rp+2)eligible.push(1);if(Math.abs(Z)>=Rp+2)eligible.push(2);
       const max=Math.max(...eligible.map(i=>Math.abs(rel[i])));
       for(const axis of eligible.filter(i=>Math.abs(rel[i])===max))for(const sign of rel[axis]===0?[-1,1]:[Math.sign(rel[axis])]) {
         const w=[...v];w[axis]-=2*sign;w[1]-=2;assert(inD(w));
         const after=depths(m-1,w);
         after.forEach((d,i)=>{assert(d===before[i]||d===before[i]-4);if(d!==before[i])assert(before[i]>R+4);});
         const c=coords(m-1,w);
         for(const [a,b]of [[Y,c.Y],[Z,c.Z]])if(a!==b){assert(a*b>=0);assert(Math.abs(b)>=Rp);}
         count++;checked++;
       }
     }
   }
   cases.push({m,R,Rprime:Rp,checked:count});
 }
}
assert(4*11<Math.max(4*0+20,2*0+4*10+22),'old counterexample is excluded');
console.log(JSON.stringify({status:'passed',checked,cases},null,2));
