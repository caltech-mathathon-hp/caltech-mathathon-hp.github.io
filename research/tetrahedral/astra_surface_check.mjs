// Build frame links and every surface PPP for concrete admissible parameters.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {frame} from './astra_near_field.mjs';
import {localCover} from './astra_local_cover.mjs';
import {ts,mod,key,neighbours,inOct,same,coords,edgeSite,up,fs as tetra} from './audit_geometry.mjs';
function surface(m,K,B,unitItems=false) {
 const Sigma=18*K+40,C=(Sigma+8)*B,J=C+Sigma+8,Rfill=C+Sigma+9;
 assert.equal(m,J+K*(C+2)+Rfill+3);
 const R=2*m-2,cover=localCover(m),f=frame(m,K),occupied=new Map(),caps=[],ppps=[];
 const e1=i=>[mod(i,2),R+i,-R+i], e2=i=>[R-i,R+i,mod(i,2)?-1:0],e3=i=>[i,R+mod(i,2),-R+i];
 for(const row of f.rows)for(const p of row.offsets.map(d=>d.map((x,i)=>x+row.from[i])))occupied.set(key(p),row.name);
 const dangling=v=>{const a=neighbours(v).filter(w=>!inOct(m,w));assert.equal(a.length,1);return a[0];};
 const putPPP=(a,b,label)=>{
   const p=dangling(a),r=dangling(b),mid=neighbours(p).filter(q=>neighbours(r).some(w=>same(q,w))&&!inOct(m,q));
   assert.equal(mid.length,1,label);const path=[p,mid[0],r];
   for(const v of path){assert(!occupied.has(key(v)),`${label} collides with ${occupied.get(key(v))} at ${key(v)}`);occupied.set(key(v),label);}
   for(const q of neighbours(mid[0]))if(coords(m,q).rho===coords(m,mid[0]).rho-2) {
     for(const h of neighbours(q).filter(v=>inOct(m,v))) {
       assert(edgeSite(m,h)||cover.adjacent(h).length!==1,`${label} blocks a bulk column ${key(h)}`);
     }
   }
   ppps.push({a,b,path,label});
 };
 function chain(dim,label) {caps.push({v:dim[0][0],label:`${label}-start`},{v:dim.at(-1)[1],label:`${label}-end`});for(let j=0;j+1<dim.length;j++)putPPP(dim[j][1],dim[j+1][0],`${label}-${j}`);}
 const D=i=>i===0?[e1(2),e1(1)]:[e3(2*i),e3(2*i+1)];
 function track(start,length,firstAB,label){chain(Array.from({length},(_,j)=>((j%2===0)===firstAB?D(start+j):D(start+j).reverse())),label);}
 track(0,J,true,'left');
 for(let k=1;k<=K+1;k++) {
   const j=J+(k-1)*(C+2);track(j,2,false,`separator-${k}`);
   if(k<=K) {
     const size=unitItems?Sigma+8:C;
     for(let offset=0;offset<C;offset+=size)track(j+2+offset,size,true,`bin-${k}-${offset}`);
   }
   caps.push({v:e1(6*k),label:`entry-${k}-a`},{v:e1(6*k+1),label:`entry-${k}-b`});
   const kk=K+1-k,w=Array.from({length:6},(_,n)=>e2(10*kk+6+n));
   chain([[w[1],w[0]],[w[2],w[3]],[w[5],w[4]]],`exit-${k}`);
 }
 track(J+K*(C+2)+2,Rfill,true,'right');
 const fromF=f=>[0,1,2].map(i=>ts.reduce((s,t,j)=>s+f[j]*t[i]/4,0)+(i===1?R:0));
 for(let small=0;small<3;small++) {
   const vertices=new Map();
   for(let big=0;big<4;big++)if(big!==small) {
     const others=[0,1,2,3].filter(j=>j!==big&&j!==small),[a,b]=others;
     for(let n=1;n<=m-2;n++){const f=[];f[big]=R;f[small]=-R;f[a]=-R+4*n;f[b]=R-4*n;const v=fromF(f);vertices.set(key(v),v);}
     for(let n=0;n<=m-2;n++){const f=[];f[big]=R-1;f[small]=-R-1;f[a]=-R+3+4*n;f[b]=R-1-4*n;const v=fromF(f);vertices.set(key(v),v);}
   }
   const start=[...vertices.values()].filter(v=>mod(v[0],2)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2])[0];
   const cycle=[start];let prev=null;
   for(;;){const v=cycle.at(-1),ns=neighbours(v).filter(w=>vertices.has(key(w))&&(!prev||!same(w,prev))).sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2]);assert(ns.length);const next=ns[0];if(same(next,start))break;cycle.push(next);prev=v;assert(cycle.length<=vertices.size);}
   assert.equal(cycle.length,6*(m-2));
   const dim=[];for(let j=0;j<cycle.length/2;j++)dim.push(j%2?[cycle[2*j+1],cycle[2*j]]:[cycle[2*j],cycle[2*j+1]]);
   chain(dim,`ring-${small+1}`);
 }
 const byLabel=new Map(caps.map(c=>[c.label,c])),borrows=new Map(f.borrowing.map(c=>[key(c.p),[...c.choices].sort((a,b)=>(c.name==='left-filler'?-1:1)*(a.second[1]-b.second[1]))[0]]));
 const tetherLabels=new Set();for(let k=1;k<=K+1;k++)for(const label of [`entry-${k}-b`,`separator-${k}-start`,`separator-${k}-end`,`exit-${k}-start`])tetherLabels.add(label);
 const column=(h,j)=>{
   const p=dangling(h),path=[p],borrow=borrows.get(key(p));if(borrow)path.push(borrow.second);
   while(tetra(m,path.at(-1))[3]!==-R-4*j){path.push(up(m,path.at(-1),[1,-1]));assert(path.length<4*j+10);}
   return path;
 };
 const surf=(j,a,b,c)=>fromF([2*(m+2*j)-3-4*a,2*(m+2*j)-3-4*b,2*(m+2*j)-3-4*c,-(2*(m+2*j)-1)]);
 const gamma=(j,a,b,c)=>fromF([2*(m+2*j)-2-4*a,2*(m+2*j)-2-4*b,2*(m+2*j)-2-4*c,-(2*(m+2*j)-2)]);
 function row(path,j,start,end,axis) {
   let [a,b,c]=start;
   while(a!==end[0]||b!==end[1]||c!==end[2]) {
     if(axis==='c'){path.push(gamma(j,a+1,b,c));a++;b--;}
     if(axis==='b'){path.push(gamma(j,a,b,c+1));a--;c++;}
     if(axis==='a'){path.push(gamma(j,a,b+1,c));b++;c--;}
     path.push(surf(j,a,b,c));
   }
 }
 const tetherLengths=[];
 for(let k=1;k<=K+1;k++) {
   const jk=J+(k-1)*(C+2),kap=K+1-k;
   for(const entry of [true,false]) {
     const j=entry?k+1:K+2+k;
     const h1=byLabel.get(entry?`entry-${k}-b`:`separator-${k}-end`).v;
     const h2=byLabel.get(entry?`separator-${k}-start`:`exit-${k}-start`).v;
     const path=column(h1,j),other=column(h2,j);
     if(entry) {
       const start=[m-2-3*k+j,3*k+j-1,1],turn=[m-2+j,j-1,1],end=[m-2-jk+j,j-1,jk+1];
       path.push(surf(j,...start));row(path,j,start,turn,'c');row(path,j,turn,end,'b');
     } else {
       const start=[m-3-jk+j,j-1,jk+2],turn=[j-1,j-1,m],end=[j-1,5*kap+3+j,m-4-5*kap];
       path.push(surf(j,...start));row(path,j,start,turn,'b');row(path,j,turn,end,'a');
     }
     path.push(...other.reverse());
     const label=`tether-${entry?'entry':'exit'}-${k}`;
     for(let q=0;q<path.length;q++) {
       const v=path[q];assert(!inOct(m,v));if(q)assert(neighbours(path[q-1]).some(w=>same(w,v)),`${label} adjacency`);
       assert(!occupied.has(key(v)),`${label} hits ${occupied.get(key(v))} at ${key(v)}`);occupied.set(key(v),label);
     }
     const expected=entry?2*jk+3+10*k:2*(m-2-jk)+3+14*K+22-6*k;
     assert.equal(path.length,expected);tetherLengths.push(path.length);
   }
 }
 const longCaps=caps.filter(c=>!tetherLabels.has(c.label));
 // Include the singleton and all unused vertex caps.
 longCaps.push({v:e1(R-1),label:'first-H'});
 for(const axis of [0,1,2])for(const sign of [-1,1]) {
   const v=[0,R,0];v[axis]+=sign*R;
   for(const p of neighbours(v).filter(p=>!inOct(m,p)&&!occupied.has(key(p))))longCaps.push({v,p,label:`vertex-${axis}-${sign}`});
 }
 const longSources=new Map();
 for(const c of longCaps) {
   const p=c.p||dangling(c.v),borrow=borrows.get(key(p));
   assert(!occupied.has(key(p)),`long cap ${c.label} collides`);occupied.set(key(p),c.label);
   const sourceCap=borrow?dangling(borrow.source):p;longSources.set(key(sourceCap),{label:c.label,allowed:new Set([key(p)])});
   if(borrow){assert(!occupied.has(key(borrow.second)));occupied.set(key(borrow.second),c.label);longSources.get(key(sourceCap)).allowed.add(key(borrow.second));}
 }
 let columnChecks=0;
 for(const [site,label]of occupied) {
   let v=site.split(',').map(Number),source=null;
   for(let step=0;step<=4*K+10;step++) {
     source=neighbours(v).find(h=>inOct(m,h));if(source)break;
     const down=neighbours(v).filter(w=>coords(m,w).rho===coords(m,v).rho-2);if(down.length!==1)break;v=down[0];
   }
   if(!source)continue;
   const original=site.split(',').map(Number),quadrant=[Math.sign(v[1]-source[1]),Math.sign(v[2]-source[2])],observed=coords(m,original).q;
   if(site!==key(v)&&(observed[0]!==quadrant[0]||observed[1]!==quadrant[1]))continue;
   assert(edgeSite(m,source)||cover.adjacent(source).length!==1,`${label} hits bulk column at ${site}, source ${key(source)}`);
   const long=longSources.get(key(v));if(long)assert(long.allowed.has(site),`${label} hits ${long.label} column at ${site}`);
   columnChecks++;
 }
 return {m,K,B,unitItems,frameLinks:f.rows.length,ppps:ppps.length,nearPsites:occupied.size,longCaps:longCaps.length,tetherLengths,columnChecks};
}
const results=[];
for(const [K,B,unitItems]of [[1,1,false],[1,3,false],[1,3,true],[2,2,true],[6,1,false],[6,3,true]]) {
 const m=(K+2)*(18*K+48)*B+38*K+100;
 const result=surface(m,K,B,unitItems);results.push(result);console.log(JSON.stringify(result));
}
fs.writeFileSync(new URL('./astra_surface_results.json',import.meta.url),JSON.stringify(results,null,2)+'\n');
