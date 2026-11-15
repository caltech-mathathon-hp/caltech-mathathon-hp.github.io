// Reconstruct Lemma F(A-C) for ordinary columns and test the entire routing.
import assert from 'node:assert/strict';
import {coords,dangling,up,avenue,approach,inD,inOct,key,same,neighbours,depths} from './audit_geometry.mjs';

const results=[];
for(const m of [3,4,6])for(const pairing of ['adjacent','reverse','interleave']) {
  const caps=dangling(m),w=caps.length,H=20*m+21;
  let pairs;
  if(pairing==='adjacent')pairs=Array.from({length:w/2},(_,i)=>[2*i,2*i+1]);
  if(pairing==='reverse')pairs=Array.from({length:w/2},(_,i)=>[i,w-1-i]);
  if(pairing==='interleave')pairs=Array.from({length:w/2},(_,i)=>[i,i+w/2]);
  const wires=caps.map((c,id)=>{
    const next=up(m,c.p,c.q),co=coords(m,next);
    return {...c,id,alpha:co.alpha,x:Math.min(c.p[0],next[0])};
  });
  const xValues=[...new Set(wires.map(c=>c.x))].sort((a,b)=>b-a);
  for(const c of wires)c.ell=H+4*xValues.indexOf(c.x);
  const ordered=[...wires].sort((a,b)=>b.ell-a.ell||a.id-b.id);
  ordered.forEach((c,n)=>{c.xi=H+60*(n+1);});
  pairs.forEach((p,i)=>p.forEach(id=>{wires[id].u=H+4*w+8+4*(i+1);}));
  const alphaStar=Math.max(...wires.map(c=>Math.abs(c.alpha)))+6;
  for(const c of wires) {
    const path=[c.p];
    while(coords(m,path.at(-1)).rho<c.ell)path.push(up(m,path.at(-1),c.q));
    const T=path.at(-1);
    assert(same(T,avenue(m,c.q,c.ell,c.alpha,T[0])));
    let E;
    for(let x=c.xi;x<=c.xi+3;x++) {
      const v=avenue(m,c.q,c.ell,c.alpha,x);
      if(coords(m,v).rho===c.ell+2 && coords(m,avenue(m,c.q,c.ell,c.alpha,x-1)).rho===c.ell){E=v;break;}
    }
    assert(E);
    for(let x=T[0]+1;x<=E[0];x++)path.push(avenue(m,c.q,c.ell,c.alpha,x));
    while(coords(m,path.at(-1)).rho<c.u)path.push(up(m,path.at(-1),c.q));
    const tail=approach(m,path.at(-1),c.u,alphaStar);
    assert(tail.every(v=>v[0]>=c.xi-5&&v[0]<=c.xi+8));
    path.push(...tail.slice(1));c.path=path;
  }
  const occupied=new Map();let sites=0,maxLength=0;
  for(let i=0;i<pairs.length;i++) {
    const [a,b]=pairs[i].map(id=>wires[id]),sa=a.path.at(-1),sb=b.path.at(-1),path=[...a.path];
    const dx=Math.sign(sb[0]-sa[0]);assert.notEqual(dx,0);
    for(let x=sa[0]+dx;;x+=dx){path.push(avenue(m,[1,1],a.u,alphaStar,x));if(x===sb[0])break;}
    path.push(...b.path.slice(0,-1).reverse());
    for(let j=0;j<path.length;j++) {
      const v=path[j],k=key(v);
      assert(inD(v)&&!inOct(m,v));
      if(j)assert(neighbours(path[j-1]).some(z=>same(z,v)));
      assert(!occupied.has(k),JSON.stringify({m,pairing,linker:i,site:v,previous:occupied.get(k)}));
      occupied.set(k,{linker:i,index:j});
    }
    assert(path.length<1000*(m+w+1));
    sites+=path.length;maxLength=Math.max(maxLength,path.length);
  }
  results.push({m,pairing,w,linkers:pairs.length,sites,maxLength});
}
const v=[0,30,10],transferred=[-2,28,10];
assert(inOct(11,v));assert(inD(transferred));assert(!inOct(10,transferred));
console.log(JSON.stringify({farField:'passed for all ordinary dangling columns in the listed configurations',results,
  transferCounterexample:{m:11,R:0,Rprime:10,v,depthsBefore:depths(11,v),transferred,depthsAfter:depths(10,transferred)},
  smallestSection6Size:3*66+38+100},null,2));
