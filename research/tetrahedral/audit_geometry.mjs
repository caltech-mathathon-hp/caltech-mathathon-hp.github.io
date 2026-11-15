// Coordinate primitives for the routing/transfer audit. No manuscript code imported.
import assert from 'node:assert/strict';
export const ts = [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]];
export const mod = (x,n) => ((x%n)+n)%n;
export const key = v => v.join(',');
export const add = (a,b) => a.map((x,i)=>x+b[i]);
export const same = (a,b) => key(a)===key(b);
export function inD(v) {
  return mod(v[0]-v[1],2)===0 && mod(v[0]-v[2],2)===0
    && mod(v.reduce((a,b)=>a+b,0),4)===(mod(v[0],2)===0?0:3);
}
export function neighbours(v) {
  const sign=mod(v[0],2)===0?1:-1;
  return ts.map(t=>v.map((x,i)=>x+sign*t[i]));
}
export function coords(m,v) {
  const Y=v[1]-(2*m-2), Z=v[2]-1;
  return {X:v[0],Y,Z,rho:Math.abs(Y)+Math.abs(Z),alpha:Math.abs(Y)-Math.abs(Z),
    q:[Math.sign(Y),Math.sign(Z)]};
}
export function fs(m,v) {
  const a=[v[0],v[1]-(2*m-2),v[2]];
  return ts.map(t=>t.reduce((s,x,i)=>s+x*a[i],0));
}
export function depths(m,v) { const f=fs(m,v); return [...f.map(x=>2*m-2-x),...f.map(x=>2*m-1+x)]; }
export function inOct(m,v) {
  return inD(v) && depths(m,v).every(x=>x>=0);
}
export function edgeSite(m,v) {
  if(!inOct(m,v))return false;
  const f=fs(m,v), A=mod(v[0],2)===0;
  return f.some(x=>x===(A?2*m-2:2*m-3)) && f.some(x=>x===(A?-(2*m-2):-(2*m-1)));
}
export function octSites(m) {
  const out=[], R=2*m-1;
  for(let x=-R;x<=R;x++)for(let Y=-R+Math.abs(x);Y<=R-Math.abs(x);Y++) {
    if(mod(x-Y,2)!==0)continue;
    const zmax=R-Math.abs(x)-Math.abs(Y);
    for(let z=-zmax;z<=zmax;z++) {
      const v=[x,Y+2*m-2,z];if(inOct(m,v))out.push(v);
    }
  }
  return out;
}
export function dangling(m) {
  const out=[];
  for(const v of octSites(m))neighbours(v).forEach((p,j)=>{
    if(inOct(m,p))return;
    const sign=mod(v[0],2)===0?1:-1;
    out.push({p,q:[sign*ts[j][1],sign*ts[j][2]],source:v,face:j});
  });
  assert.equal(out.length,4*m*m);
  assert.equal(new Set(out.map(c=>key(c.p))).size,out.length);
  return out;
}
export function up(m,v,q) {
  const rho=coords(m,v).rho;
  const choices=neighbours(v).filter(z=>{
    const c=coords(m,z);return c.rho===rho+2 && c.q[0]===q[0] && c.q[1]===q[1];
  });
  assert.equal(choices.length,1);return choices[0];
}
export function avenue(m,q,ell,alpha,x) {
  const out=[];
  for(const rho of [ell,ell+2])for(const a of [alpha,alpha+2]) {
    const Y=q[0]*(rho+a)/2,Z=q[1]*(rho-a)/2;
    const v=[x,Y+2*m-2,Z+1];
    if(Y*q[0]>0 && Z*q[1]>0 && inD(v))out.push(v);
  }
  assert.equal(out.length,1);return out[0];
}
export function approach(m,t,u,alpha) {
  const choices=neighbours(t).filter(v=>coords(m,v).rho===u);
  assert.equal(choices.length,2);
  for(const first of choices) {
    const path=[t,first];
    for(let steps=0;steps<4*u+4;steps++) {
      const v=path.at(-1),c=coords(m,v);
      if(c.q[0]===1 && c.q[1]===1 && [alpha,alpha+2].includes(c.alpha)) {
        if(c.alpha===alpha)return path;
        break;
      }
      const next=neighbours(v).filter(z=>coords(m,z).rho===u&&!same(z,path.at(-2)));
      assert.equal(next.length,1);path.push(next[0]);
      if(same(next[0],t))break;
    }
  }
  throw Error('No correctly oriented level-curve approach');
}
