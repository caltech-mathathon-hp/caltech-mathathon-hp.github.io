// Heuristic search of infinite periodic ordinary chains, represented by one cell.
// A saved cell plus translation is a finite certificate, checked separately.
const fs=require('fs'),path=require('path');
const L=Number(process.argv[2]||2),seconds=Number(process.argv[3]||300),mode=process.argv[4]||'program';
let seed=Number(process.env.SEED||37),state=seed;
function rand(){state^=state<<13;state^=state>>>17;state^=state<<5;return (state>>>0)/4294967296}
const ri=n=>Math.floor(rand()*n),add=(a,b)=>a.map((v,i)=>v+b[i]),sub=(a,b)=>a.map((v,i)=>v-b[i]);
const aux=([x,y,z])=>{let r=(x-y-z)/2;return [r,y+r,x-r]};
const physical=([r,s,k])=>[r+k,-r+s,-s+k];
const dirs=[];for(let x=-1;x<=1;x++)for(let y=-1;y<=1;y++)for(let z=-1;z<=1;z++)if(x*x+y*y+z*z===2)dirs.push(aux([x,y,z]));
const ds=new Set(dirs.map(p=>p.join(','))),adj=(a,b)=>ds.has(sub(a,b).join(','));
const bits=Array.from({length:L},(_,r)=>mode==='alternating'?r%2:0),shear=bits.reduce((a,b)=>a+b,0),T=[L,shear,0];
function key(p){let t=Math.floor(p[0]/L);return [p[0]-t*L,p[1]-t*shear,p[2]].join(',')}
function shuffle(a){for(let i=a.length-1;i>0;i--){let j=ri(i+1);[a[i],a[j]]=[a[j],a[i]]}return a}
const U=['PHP'.repeat(2)+'PHH'+'PHP'.repeat(3),'HHP'+'PHP'.repeat(5)];
let word=mode==='plain'?'PHP'.repeat(6*L):bits.map(b=>U[b]).join(''),N=word.length,p=[],t=0;
bits.forEach((b,r)=>{let rows=[[3,0],[2,0],[2,-1],[1,-1],[1,0],[0,-1],[-1,-1],[0,0],[-1,0],[b-1,1],[b,1],[b,2],[b+1,2],[b+1,1],[b+2,2],[b+3,2],[b+2,1],[b+3,1]];p.push(...rows.map(([s,k])=>[r,s+t,k]));t+=b});
const HH=Array.from({length:N},(_,i)=>word[i]==='H'&&word[(i+1)%N]==='H'?1:0).reduce((a,b)=>a+b,0);
function score(q){let H=new Set(q.filter((_,i)=>word[i]==='H').map(key)),total=0;for(let i=0;i<N;i++)if(word[i]==='H')for(let d of dirs)if(H.has(key(add(q[i],d))))total++;return total/2-HH}
function mutate(p){let q=p.slice(),a=1+ri(N-1),len=1+ri(Math.min(6,N-a)),b=a+len-1;
 if(rand()<0.3){b=a+ri(N-a);let end=b===N-1?add(p[0],T):p[b+1];if(!adj(p[a-1],p[b])||!adj(p[a],end))return null;for(let i=a;i<=b;i++)q[i]=p[a+b-i];return q}
 let end=b===N-1?add(p[0],T):p[b+1],occ=new Set(p.filter((_,i)=>i<a||i>b).map(key)),visits=0;
 function dfs(i){if(i>b)return adj(q[b],end);if(++visits>180)return false;
  for(let d of shuffle(dirs.slice())){let v=add(q[i-1],d),k=key(v);if(occ.has(k))continue;let dd=physical(sub(v,end)).map(Math.abs),remaining=b+1-i;if(Math.max(...dd)>remaining||dd.reduce((s,x)=>s+x,0)>2*remaining)continue;q[i]=v;occ.add(k);if(dfs(i+1))return true;occ.delete(k)}return false;
 }return dfs(a)?q:null;
}
let best=p,bs=score(p),cur=bs,baseline=bs,steps=0,start=Date.now();
const file=path.join(__dirname,`periodic_${mode}_${L}_${seed}.json`);
function save(){fs.writeFileSync(file,JSON.stringify({kind:'periodic heuristic witness',word,L,mode,seed,steps,score_per_period:bs,baseline,translation_aux:T,positions_aux:best},null,2));console.log(JSON.stringify({L,mode,steps,bs,baseline,seconds:(Date.now()-start)/1000}))}
save();
while(Date.now()-start<1000*seconds){steps++;let q=mutate(p);if(!q)continue;let s=score(q),temp=0.03+Number(process.env.TEMP||0.65)*(1-(steps%10000)/10000);if(s>=cur||rand()<Math.exp((s-cur)/temp)){p=q;cur=s}if(s>bs){bs=s;best=q;save()}if(steps%50000===0){p=best;cur=bs}}
save();
