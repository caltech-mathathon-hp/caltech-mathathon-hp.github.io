// Heuristic search only. Every saved incumbent is independently verified in Python.
const fs = require('fs');
const path = require('path');
const outdir = __dirname;
const dirs=[];
for(let a=-1;a<=1;a++)for(let b=-1;b<=1;b++)for(let c=-1;c<=1;c++)
 if(a*a+b*b+c*c===2)dirs.push([a,b,c]);
const add=(a,b)=>a.map((v,i)=>v+b[i]);
const sub=(a,b)=>a.map((v,i)=>v-b[i]);
const key=p=>p.join(',');
const adj=(a,b)=>{const d=sub(a,b);return Math.max(...d.map(Math.abs))===1&&d.reduce((s,x)=>s+x*x,0)===2};
const physical=([r,s,k])=>[r+k,-r+s,-s+k];
function ribbon(bits){let t=0,p=[];bits.forEach((b,r)=>{let rows=[[3,0],[2,0],[2,-1],[1,-1],[1,0],[0,-1],[-1,-1],[0,0],[-1,0],[b-1,1],[b,1],[b,2],[b+1,2],[b+1,1],[b+2,2],[b+3,2],[b+2,1],[b+3,1]];p.push(...rows.map(([s,k])=>physical([r,s+t,k])));t+=b});return p}
const U=['PHP'.repeat(2)+'PHH'+'PHP'.repeat(3),'HHP'+'PHP'.repeat(5)];
function score(p,w){let s=0;for(let i=0;i<p.length;i++)if(w[i]==='H')for(let j=i+2;j<p.length;j++)if(w[j]==='H'&&adj(p[i],p[j]))s++;return s}
let state=Number(process.env.SEED||7291)>>>0;
function rand(){state^=state<<13;state^=state>>>17;state^=state<<5;return (state>>>0)/4294967296}
const ri=n=>Math.floor(rand()*n);
function shuffle(a){for(let i=a.length-1;i>0;i--){let j=ri(i+1);[a[i],a[j]]=[a[j],a[i]]}return a}
const perms=[[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];
function mutation(p,locked){let n=p.length,q=p.slice();
 if(rand()<0.25){let lo=locked?locked[0]:0,hi=locked?locked[1]:n-1,a=lo+ri(hi-lo+1),b=lo+ri(hi-lo+1);if(a>b)[a,b]=[b,a];
  if(a===b||(a>0&&!adj(p[a-1],p[b]))||(b<n-1&&!adj(p[a],p[b+1])))return null;
  for(let i=a;i<=b;i++)q[i]=p[b+a-i];return q;
 }
 if(rand()<0.15&&!locked){let cut=ri(n-1),perm=perms[ri(6)],sg=[ri(2)*2-1,ri(2)*2-1,ri(2)*2-1];
  for(let i=cut+1;i<n;i++){let d=sub(p[i],p[cut]);q[i]=add(p[cut],perm.map((j,k)=>d[j]*sg[k]))}
  if(new Set(q.map(key)).size!==n)return null;return q;
 }
 let len=1+ri(5),lo=locked?locked[0]:0,hi=locked?locked[1]:n-1,a=lo+ri(hi-lo-len+2),b=a+len-1;
 if(locked&&(a<locked[0]||b>locked[1]))return null;
 let occ=new Set(p.filter((_,i)=>i<a||i>b).map(key));
 if(a===0){q.reverse();const z=mutation(q,locked? [n-1-locked[1],n-1-locked[0]]:null);return z?z.reverse():null}
 let visited=0;
 function dfs(i){if(i>b)return b===n-1||adj(q[b],q[b+1]);if(++visited>120)return false;
  for(let d of shuffle(dirs.slice())){let v=add(q[i-1],d),k=key(v);if(occ.has(k))continue;
   if(b<n-1){let dd=sub(v,q[b+1]).map(Math.abs),steps=b+1-i;if(Math.max(...dd)>steps||dd.reduce((s,x)=>s+x,0)>2*steps)continue}
   q[i]=v;occ.add(k);if(dfs(i+1))return true;occ.delete(k);
  }return false;
 }return dfs(a)?q:null;
}
function verify(p,w){if(p.length!==w.length||new Set(p.map(key)).size!==p.length||p.some(v=>v.reduce((a,b)=>a+b,0)%2!==0)||p.slice(1).some((v,i)=>!adj(v,p[i])))throw Error('invalid fold')}
let mode=process.argv[2]||'program',L=Number(process.argv[3]||4),seconds=Number(process.argv[4]||60);
let bits=Array.from({length:L},(_,i)=>mode==='alternating'?i%2:0),w=mode==='plain'?'PHP'.repeat(6*L):bits.map(b=>U[b]).join('');
let p=ribbon(bits),best=p,bestScore=score(p,w),cur=bestScore,steps=0,accepted=0;
const base=bestScore,start=Date.now(),lockMode=process.argv[5],locked=lockMode==='interior'?[18,18*(L-1)-1]:lockMode==='cap'?[0,17]:lockMode==='tail'?[18*(L-1),18*L-1]:null;
const filename=path.join(outdir,`witness_${mode}_${L}${locked?'_'+lockMode:''}${process.env.TAG||''}.json`);
function save(){verify(best,w);fs.writeFileSync(filename,JSON.stringify({kind:'heuristic coordinate witness',mode,L,seed:Number(process.env.SEED||7291),locked,word:w,baseline:base,score:bestScore,steps,positions:best},null,2));console.log(JSON.stringify({mode,L,locked,steps,bestScore,base,elapsed:(Date.now()-start)/1000}))}
save();
while(Date.now()-start<seconds*1000){steps++;let q=mutation(p,locked);if(!q)continue;let s=score(q,w),temp=0.05+Number(process.env.TEMP||0.8)*(1-(steps%5000)/5000);
 if(s>=cur||rand()<Math.exp((s-cur)/temp)){p=q;cur=s;accepted++}
 if(s>bestScore){best=q;bestScore=s;save()}
 if(steps%25000===0){p=best;cur=bestScore}
}save();
