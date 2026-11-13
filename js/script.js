'use strict';
const $=s=>document.querySelector(s),$$=s=>[...document.querySelectorAll(s)];
const CAP={32:7.22,64:15.95},F64=x=>x,fn=p=>+p===32?Math.fround:F64;
const KL={bien:1e2,mod:1e6,mal:1e10,ext:1e15},DEG={bien:3,mod:6,mal:9,ext:12};
const ROUTES={tidy:{l:'Tidy (tabla larga JS)',s:'Tidy',tidy:1,sum:'seq',v:'two'},native:{l:'Matricial (por pares)',s:'Matricial',sum:'pair',v:'twoP'},
 comp:{l:'Matricial compensada',s:'Compensada',sum:'kahan',v:'welf'},ctrl:{l:'Control secuencial',s:'Control',sum:'seq',v:'classic'}};
const COL={tidy:'#4cc9f0',native:'#90be6d',comp:'#f9c74f',ctrl:'#f94144'};
const rng=seed=>{let a=seed>>>0;return()=>{a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}};
const pick=(a,idx)=>{const o=new Float64Array(idx.length);for(let i=0;i<idx.length;i++)o[i]=a[idx[i]];return o};
const fm=x=>x==null||Number.isNaN(x)?'n/d':!isFinite(x)?'∞':(x!==0&&(Math.abs(x)<1e-3||Math.abs(x)>1e6))?x.toExponential(3):String(+x.toFixed(4));
function orderIdx(a,mode,seed){const n=a.length,id=Array.from({length:n},(_,i)=>i);
 if(mode==='asc')id.sort((i,j)=>a[i]-a[j]);else if(mode==='desc')id.sort((i,j)=>a[j]-a[i]);
 else if(mode==='perm'){const r=rng(seed);for(let i=n-1;i>0;i--){const j=Math.floor(r()*(i+1));[id[i],id[j]]=[id[j],id[i]]}}
 return id}

/* ReferenceEngine: aritmética entera exacta (BigInt) sobre dobles almacenados */
const dv=new DataView(new ArrayBuffer(8));
const dec=x=>{if(x===0)return[0n,0];dv.setFloat64(0,x);const hi=dv.getUint32(0),lo=dv.getUint32(4),ex=(hi>>>20)&2047;
 let m=(BigInt(hi&0xfffff)<<32n)|BigInt(lo),e=-1074;if(ex){m|=1n<<52n;e=ex-1075}return[hi>>>31?-m:m,e]};
const emin=t=>{let e=Infinity;for(const[m,x]of t)if(m!==0n&&x<e)e=x;return e};
const RE={exact(t){const e0=emin(t);if(e0===Infinity)return 0;let b=0n;for(const[m,e]of t)b+=m<<BigInt(e-e0);return Number(b)*Math.pow(2,e0)},
 sum:x=>RE.exact(Array.from(x,dec)),
 dot:(x,y)=>RE.exact(Array.from(x,(v,i)=>{const[a,e]=dec(v),[b,f]=dec(y[i]);return[a*b,e+f]})),
 var(x){const d=Array.from(x,dec),e0=emin(d),n=x.length;let A=0n,B=0n;for(const[m,e]of d){const s=BigInt(e-e0);A+=(m*m)<<(2n*s);B+=m<<s}
  return Number(BigInt(n)*A-B*B)/(n*(n-1))*Math.pow(2,2*e0)}};

/* AuditEngine: LRE, ULP, dispersión */
const f64=new Float64Array(1),i64=new BigInt64Array(f64.buffer),f32=new Float32Array(1),i32=new Int32Array(f32.buffer);
const o64=x=>{f64[0]=x;const b=i64[0];return b<0n?-(b&0x7fffffffffffffffn):b};
const o32=x=>{f32[0]=x;const b=i32[0];return b<0?-(b&0x7fffffff):b};
const AE={lre(q,r,p){if(!isFinite(q))return 0;if(q===r)return CAP[p];if(r===0)return NaN;return Math.min(CAP[p],Math.max(0,-Math.log10(Math.abs(q-r)/Math.abs(r))))},
 ulp(q,r,p){if(!isFinite(q))return Infinity;if(p==32)return Math.abs(o32(q)-o32(Math.fround(r)));const d=o64(q)-o64(r);return Number(d<0n?-d:d)},
 score(q,r,p){if(Array.isArray(r)||q instanceof Float64Array){const s=Array.from(q,(v,i)=>[AE.lre(v,r[i],p),AE.ulp(v,r[i],p)]);return{lre:Math.min(...s.map(a=>a[0])),ulp:Math.max(...s.map(a=>a[1]))}}
  return{lre:AE.lre(q,r,p),ulp:AE.ulp(q,r,p)}},
 spread(qs,r){if(Array.isArray(r)){let m=0;r.forEach((rv,j)=>{const v=qs.map(q=>q[j]);m=Math.max(m,(Math.max(...v)-Math.min(...v))/Math.abs(rv))});return m}
  return r===0?NaN:(Math.max(...qs)-Math.min(...qs))/Math.abs(r)}};

/* NumericalEngine: suma secuencial, por pares, Kahan; varianza clásica, dos pasadas, Welford; producto interno; regresión */
const NE={seq(a,f){let s=0;for(let i=0;i<a.length;i++)s=f(s+a[i]);return s},
 pair(a,f,lo=0,hi=a.length){if(hi-lo<=8){let s=0;for(let i=lo;i<hi;i++)s=f(s+a[i]);return s}const m=(lo+hi)>>1;return f(NE.pair(a,f,lo,m)+NE.pair(a,f,m,hi))},
 kahan(a,f){let s=0,c=0;for(let i=0;i<a.length;i++){const y=f(a[i]-c),t=f(s+y);c=f(f(t-s)-y);s=t}return s},
 grp(a,g,f,alg){if(!g)return alg(a,f);const p=[];let o=0;for(const n of g){p.push(alg(a.subarray(o,o+n),f));o+=n}return alg(Float64Array.from(p),f)},
 prod(a,b,f){const p=new Float64Array(a.length);for(let i=0;i<p.length;i++)p[i]=f(a[i]*b[i]);return p},
 vr(kind,a,f,g){const n=a.length;
  if(kind==='welf'){let m=0,s=0;for(let i=0;i<n;i++){const d=f(a[i]-m);m=f(m+f(d/(i+1)));s=f(s+f(d*f(a[i]-m)))}return f(s/(n-1))}
  if(kind==='classic'){let s=0,q=0;for(let i=0;i<n;i++){s=f(s+a[i]);q=f(q+f(a[i]*a[i]))}return f(f(q-f(f(s*s)/n))/(n-1))}
  const al=kind==='twoP'?NE.pair:NE.seq,m=f(NE.grp(a,g,f,al)/n),d=new Float64Array(n);for(let i=0;i<n;i++){const t=f(a[i]-m);d[i]=f(t*t)}
  return f(NE.grp(d,g,f,al)/(n-1))},
 solve(A,b){const k=b.length;for(let c=0;c<k;c++){let p=c;for(let r=c+1;r<k;r++)if(Math.abs(A[r][c])>Math.abs(A[p][c]))p=r;[A[c],A[p]]=[A[p],A[c]];[b[c],b[p]]=[b[p],b[c]];
  for(let r=c+1;r<k;r++){const m=A[r][c]/A[c][c];for(let j=c;j<k;j++)A[r][j]-=m*A[c][j];b[r]-=m*b[c]}}
  const x=new Float64Array(k);for(let r=k-1;r>=0;r--){let s=b[r];for(let j=r+1;j<k;j++)s-=A[r][j]*x[j];x[r]=s/A[r][r]}return x},
 normal(X,y,alg){const n=y.length,k=X[0].length,A=[],b=new Float64Array(k),col=new Float64Array(n);
  for(let r=0;r<k;r++){A.push(new Float64Array(k));for(let i=0;i<n;i++)col[i]=X[i][r]*y[i];b[r]=NE[alg](col,F64);
   for(let c=0;c<k;c++){for(let i=0;i<n;i++)col[i]=X[i][r]*X[i][c];A[r][c]=NE[alg](col,F64)}}return NE.solve(A,b)},
 qr(X,y){const m=y.length,k=X[0].length,A=X.map(r=>Float64Array.from(r)),b=Float64Array.from(y);
  for(let j=0;j<k;j++){let nr=0;for(let i=j;i<m;i++)nr+=A[i][j]**2;nr=Math.sqrt(nr);if(A[j][j]>0)nr=-nr;
   const v=new Float64Array(m);for(let i=j;i<m;i++)v[i]=A[i][j];v[j]-=nr;let vv=0;for(let i=j;i<m;i++)vv+=v[i]*v[i];if(!vv)continue;
   for(let c=j;c<k;c++){let d=0;for(let i=j;i<m;i++)d+=v[i]*A[i][c];d=2*d/vv;for(let i=j;i<m;i++)A[i][c]-=d*v[i]}
   let d=0;for(let i=j;i<m;i++)d+=v[i]*b[i];d=2*d/vv;for(let i=j;i<m;i++)b[i]-=d*v[i]}
  const x=new Float64Array(k);for(let j=k-1;j>=0;j--){let s=b[j];for(let c=j+1;c<k;c++)s-=A[j][c]*x[c];x[j]=s/A[j][j]}return x}};

/* TidyEngine: melt/pivot/sort/groupby/partición sobre tabla larga (fila, columna, valor) */
const TE={melt(xs,ys,R,C){const n=R*C,i=new Int32Array(n),j=new Int32Array(n),v=new Float64Array(n),w=ys?new Float64Array(n):null;let k=0;
  for(let c=0;c<C;c++)for(let r=0;r<R;r++){i[k]=r;j[k]=c;v[k]=xs[r*C+c];if(w)w[k]=ys[r*C+c];k++}return{i,j,v,w}},
 pivot(t,R,C,key='v'){const m=new Float64Array(R*C);for(let k=0;k<t.v.length;k++)m[t.i[k]*C+t.j[k]]=t[key][k];return m},
 view(t,st,R,C){const n=t.v.length;
  if(st==='pivot')return{a:TE.pivot(t,R,C),b:t.w?TE.pivot(t,R,C,'w'):null,g:null};
  if(st==='sort'){const id=Array.from({length:n},(_,i)=>i).sort((p,q)=>t.v[p]-t.v[q]);return{a:pick(t.v,id),b:t.w?pick(t.w,id):null,g:null}}
  let g=null;if(st==='groupby')g=Array(C).fill(R);if(st==='partition'){const bs=Math.ceil(n/8);g=[];for(let o=0;o<n;o+=bs)g.push(Math.min(bs,n-o))}
  return{a:t.v,b:t.w,g}}};

/* DataGenerator */
const DG={cancel(n,k,r){const pairs=Math.floor(n/4),ns=n-2*pairs,B=k/(2*pairs),x=new Float64Array(n);let o=0;
  for(let i=0;i<pairs;i++){const b=B*(0.5+r());x[o++]=b;x[o++]=-b}for(let i=0;i<ns;i++)x[o++]=1/ns;
  for(let i=n-1;i>0;i--){const j=Math.floor(r()*(i+1)),t=x[i];x[i]=x[j];x[j]=t}return x},
 numacc(i){const mu=[1e7+.2,1.2,1e6+.2,1e7+.2][i-1];if(i===1)return Float64Array.of(mu-.1,mu,mu+.1);
  const a=[mu];for(let k=0;k<500;k++)a.push(mu-.1,mu+.1);return Float64Array.from(a)},
 dims(n){let d=Math.floor(Math.sqrt(n));while(n%d)d--;return[d,n/d]},
 vander(cfg){const n=40,deg=cfg.kv,k=deg+1,X=[],y=new Float64Array(n);
  for(let i=0;i<n;i++){const x=i/(n-1),row=new Float64Array(k);let p=1;for(let j=0;j<k;j++){row[j]=p;p*=x}X.push(row);let s=0;for(let j=0;j<k;j++)s+=row[j];y[i]=s}
  return{X,y,ref:Array(k).fill(1),kappa:null}},
 make(cfg){if(cfg.op==='reg')return DG.vander(cfg);let x,y=null,R=cfg.R,C=cfg.C;const r=rng(cfg.seed);
  if(cfg.ds==='csv')x=Float64Array.from(CSV.data);else if(cfg.ds!=='synth')x=DG.numacc(+cfg.ds[2]);
  else if(cfg.op==='var'){x=new Float64Array(R*C);const g=()=>Math.sqrt(-2*Math.log(r()||1e-12))*Math.cos(2*Math.PI*r());for(let i=0;i<x.length;i++)x[i]=cfg.kv+g()}
  else{x=DG.cancel(R*C,cfg.kv,r);if(cfg.op==='dot'){y=new Float64Array(x.length);for(let i=0;i<y.length;i++)y[i]=1+r()}}
  if(cfg.ds!=='synth')[R,C]=DG.dims(x.length);
  if(+cfg.prec===32){x=Float64Array.from(x,Math.fround);if(y)y=Float64Array.from(y,Math.fround)}
  let ref,kappa;if(cfg.op==='var'){ref=RE.var(x);kappa=cfg.ds==='synth'?cfg.kv:null}
  else if(cfg.op==='dot'){ref=RE.dot(x,y);kappa=x.reduce((s,v,i)=>s+Math.abs(v*y[i]),0)/Math.abs(ref)}
  else{ref=RE.sum(x);kappa=x.reduce((s,v)=>s+Math.abs(v),0)/Math.abs(ref);if(cfg.op==='mean')ref/=x.length}
  return{x,y,R,C,ref,kappa}}};
const CSV={data:null};

/* MatrixEngine / orquestación de rutas */
const base=(D,o,cfg)=>{if(cfg.op==='reg'){const id=orderIdx(D.y,o.mode,o.seed);return{X:id.map(i=>D.X[i]),y:pick(D.y,id)}}
 const id=orderIdx(D.x,o.mode,o.seed);return{xs:pick(D.x,id),ys:D.y?pick(D.y,id):null}};
const convert=(r,B,cfg,D)=>cfg.op==='reg'?B:r.tidy?TE.view(TE.melt(B.xs,B.ys,D.R,D.C),cfg.st,D.R,D.C):{a:B.xs,b:B.ys,g:null};
function exec(rk,r,cfg,P){const f=fn(cfg.prec),al=NE[r.sum];
 if(cfg.op==='reg')return rk==='comp'?NE.qr(P.X,P.y):NE.normal(P.X,P.y,rk==='native'?'pair':'seq');
 if(cfg.op==='sum')return NE.grp(P.a,P.g,f,al);
 if(cfg.op==='mean')return f(NE.grp(P.a,P.g,f,al)/P.a.length);
 if(cfg.op==='var')return NE.vr(r.v,P.a,f,P.g);
 return NE.grp(NE.prod(P.a,P.b,f),P.g,f,al)}
function evalCase(cfg,D,routes,orders){return routes.map(rk=>{const r=ROUTES[rk];
 const per=orders.map(o=>{const q=exec(rk,r,cfg,convert(r,base(D,o,cfg),cfg,D));return{q,...AE.score(q,D.ref,cfg.prec)}});
 return{rk,per,lreSel:per[0].lre,lreMin:Math.min(...per.map(p=>p.lre)),ulpMax:Math.max(...per.map(p=>p.ulp)),spread:AE.spread(per.map(p=>p.q),D.ref),q:per[0].q}})}

/* BenchmarkEngine: performance.now(), calentamiento descartado, estadísticas */
const BE={stats(a){const s=[...a].sort((x,y)=>x-y),m=a.reduce((x,y)=>x+y,0)/a.length;return{med:s[s.length>>1],mean:m,sd:Math.sqrt(a.reduce((x,y)=>x+(y-m)**2,0)/a.length)}},
 time(fnc,reps){for(let w=0;w<2;w++)fnc();const t=[];for(let k=0;k<7;k++){const a=performance.now();for(let i=0;i<reps;i++)fnc();t.push((performance.now()-a)/reps)}return BE.stats(t)},
 route(rk,D,cfg){const r=ROUTES[rk],o={mode:'orig'},B=base(D,o,cfg),n=cfg.op==='reg'?D.y.length:D.x.length,reps=Math.max(1,Math.ceil(3e5/(n+1)));
  const conv=r.tidy&&cfg.op!=='reg'?BE.time(()=>convert(r,B,cfg,D),reps):{med:0,sd:0},P=convert(r,B,cfg,D),calc=BE.time(()=>exec(rk,r,cfg,P),reps);
  const vb=+cfg.prec===32?4:8,bpc=r.tidy&&cfg.op!=='reg'?vb+8:vb;return{conv:conv.med,calc:calc.med,sd:calc.sd,bpc,factor:bpc/vb}}};

/* Service: interfaz sustituible por FastAPI (POST /api/v1/experiments con cfg → record) */
const Service={async run(cfg,progress){return Local.run(cfg,progress)}};
const tick=()=>new Promise(r=>setTimeout(r,15));
const Local={async run(cfg,progress){const t0=performance.now(),reg=cfg.op==='reg';
 const routes=cfg.routes.filter(k=>!(reg&&k==='ctrl')),D=DG.make(cfg);
 const orders=[{mode:cfg.ord,seed:cfg.seed},{mode:'orig'},{mode:'asc'},{mode:'desc'},...[1,2,3,4,5].map(k=>({mode:'perm',seed:cfg.seed+k}))],o5=orders.slice(1,6);
 progress('Evaluando rutas y órdenes…');await tick();const rows=evalCase(cfg,D,routes,orders);
 progress('Midiendo rendimiento…');await tick();rows.forEach(w=>Object.assign(w,BE.route(w.rk,D,cfg)));
 let sweep=null,pm=null;
 if(cfg.ds==='synth'){progress('Barrido de condicionamiento…');await tick();
  const ks=reg?[2,3,4,5,6,7,8,9,10,11,12]:[1e2,1e4,1e6,1e8,1e10,1e12,1e14,1e16];sweep={ks,reg,d:{}};routes.forEach(k=>sweep.d[k]=[]);
  for(const k of ks){const c2={...cfg,kv:k},res=evalCase(c2,DG.make(c2),routes,o5);res.forEach(w=>sweep.d[w.rk].push(w.lreMin))}}
 if(!reg){progress('Comparando float32 y float64…');await tick();pm={};
  for(const p of [32,64]){const c2={...cfg,prec:p};pm[p]={};evalCase(c2,DG.make(c2),routes,o5).forEach(w=>pm[p][w.rk]=w.lreMin)}}
 return{id:Date.now(),ts:new Date().toISOString(),cfg,kappa:D.kappa,ref:D.ref,n:reg?D.y.length:D.x.length,R:D.R,C:D.C,
  labels:['seleccionado','original','ascendente','descendente','perm 1','perm 2','perm 3','perm 4','perm 5'],
  rows:rows.map(w=>({rk:w.rk,q:w.q instanceof Float64Array?Array.from(w.q):w.q,lreSel:w.lreSel,lreMin:w.lreMin,ulpMax:w.ulpMax,spread:w.spread,conv:w.conv,calc:w.calc,sd:w.sd,bpc:w.bpc,factor:w.factor,lreOrd:w.per.map(p=>p.lre)})),
  sweep,pm,secs:(performance.now()-t0)/1000}}};

/* StorageEngine */
const SE={k:'numtidy_hist',load(){try{return JSON.parse(localStorage.getItem(SE.k))||[]}catch{return[]}},
 save(h){try{localStorage.setItem(SE.k,JSON.stringify(h.slice(-40)))}catch{}},clear(){try{localStorage.removeItem(SE.k)}catch{}}};
let HIST=SE.load();

/* VisualizationEngine */
const VE={ch:{},draw(id,type,labels,sets,o={}){if(VE.ch[id])VE.ch[id].destroy();const log=o.log?{type:'logarithmic'}:{};
 VE.ch[id]=new Chart($('#'+id),{type,data:{labels,datasets:sets},options:{responsive:true,maintainAspectRatio:false,animation:{duration:400},
  plugins:{legend:{display:sets.length>1,labels:{boxWidth:10}}},scales:{x:{stacked:!!o.st,title:{display:!!o.xt,text:o.xt}},y:{...log,stacked:!!o.st,min:o.min,max:o.max,title:{display:!!o.yt,text:o.yt}}}}})},
 update(rec){const rs=rec.rows,lb=rs.map(w=>ROUTES[w.rk].s),cl=rs.map(w=>COL[w.rk]),cap=CAP[rec.cfg.prec];
  if(rec.sweep)VE.draw('c1','line',rec.sweep.ks.map(k=>rec.sweep.reg?'grado '+k:k.toExponential(0)),rs.map(w=>({label:ROUTES[w.rk].s,data:rec.sweep.d[w.rk],borderColor:COL[w.rk],backgroundColor:COL[w.rk],tension:.15})),{min:0,max:cap,yt:'LRE (dígitos)',xt:rec.sweep.reg?'grado (κ(X) crece)':'κ'});
  else VE.draw('c1','bar',lb,[{label:'LRE mínimo entre órdenes',data:rs.map(w=>w.lreMin),backgroundColor:cl}],{min:0,max:cap,yt:'LRE (dígitos); barrido solo con datos sintéticos'});
  VE.draw('c2','bar',lb,[{label:'ULP máx (0 se dibuja como 0,1)',data:rs.map(w=>Math.max(w.ulpMax,.1)),backgroundColor:cl}],{log:1,yt:'ULP'});
  VE.draw('c3','bar',lb,[{label:'Conversión (melt/vista)',data:rs.map(w=>w.conv),backgroundColor:'#7b61ff'},{label:'Cálculo',data:rs.map(w=>w.calc),backgroundColor:'#4cc9f0'}],{st:1,yt:'ms (mediana)'});
  VE.draw('c4','bar',lb,[{label:'bytes/celda (estimado)',data:rs.map(w=>w.bpc),backgroundColor:cl}],{yt:'bytes por celda'});
  VE.draw('c5','bar',lb,[{label:'(máx−mín)/|ref| (0 se dibuja como 1e-18)',data:rs.map(w=>Math.max(w.spread||0,1e-18)),backgroundColor:cl}],{log:1,yt:'dispersión relativa'});
  if(rec.pm)VE.draw('c6','bar',lb,[32,64].map(p=>({label:'float'+p,data:rs.map(w=>rec.pm[p][w.rk]),backgroundColor:p===32?'#f9c74f':'#4cc9f0'})),{min:0,max:15.95,yt:'LRE (dígitos)'});
  else VE.draw('c6','bar',[],[{label:'No disponible en regresión (solo float64)',data:[]}])}};

/* UI */
function readCfg(){const g=i=>$('#'+i).value,t=g('kv').trim(),op=g('op');
 return{routes:$$('#rt input:checked').map(e=>e.value),prec:+g('prec'),st:g('st'),op,ds:g('ds'),ord:g('ord'),seed:+g('seed')|0,R:+g('R'),C:+g('C'),kv:t?+t:(op==='reg'?DEG[g('kl')]:KL[g('kl')])}}
function validate(c){const e=[];if(!c.routes.length)e.push('Selecciona al menos una ruta.');
 if(c.op==='reg'){if(c.prec===32)e.push('La regresión solo está disponible en float64 en el navegador.');if(c.ds!=='synth')e.push('La regresión usa la matriz de Vandermonde; elige el conjunto sintético.');if(!(c.kv>=2&&c.kv<=13&&Number.isInteger(c.kv)))e.push('Grado de regresión: entero entre 2 y 13.')}
 else{if(c.ds.startsWith('na')&&c.op==='dot')e.push('NumAcc solo admite suma, media y varianza.');
  if(c.ds==='csv'&&!CSV.data)e.push('Carga primero un archivo CSV.');if(c.ds==='csv'&&c.op==='dot')e.push('El producto interno requiere dos vectores; usa el conjunto sintético.');
  if(c.ds==='synth'){if(!(c.kv>=1&&c.kv<=1e16))e.push('κ debe estar entre 1 y 10¹⁶.');if(!(c.R>=1&&c.C>=1&&c.R*c.C>=8&&c.R*c.C<=1e6))e.push('Tamaño: entre 8 y 1 000 000 de elementos.')}}
 return e}
const msg=(t,err)=>{const m=$('#msg');m.textContent=t;m.className='msg'+(err?' err':'')};
async function execute(cfg,tag=''){const er=validate(cfg);if(er.length)return msg(er.join(' '),1);
 $('#run').disabled=$('#demo').disabled=true;try{const rec=await Service.run(cfg,msg);rec.tag=tag;HIST.push(rec);SE.save(HIST);msg(`Listo en ${rec.secs.toFixed(1)} s.`);renderAll();showTab('lab')}
 catch(e){msg('Error: '+e.message,1)}finally{$('#run').disabled=$('#demo').disabled=false}}
function renderAll(){const last=HIST[HIST.length-1];$('#empty').hidden=!!last;$('#charts').hidden=!last;renderKpis();renderHist();
 if(!last)return;VE.update(last);const c=last.cfg;
 $('#res').innerHTML=`<h3>${last.tag||'Experimento'} · ${c.op} · float${c.prec} · κ medido: ${fm(last.kappa)} · n=${last.n} · semilla ${c.seed}</h3><p class="note">Referencia ${Array.isArray(last.ref)?'(regresión: β=1 por construcción de y; no es solución exacta de los datos almacenados)':'exacta (BigInt): '+fm(last.ref)}. Tiempos: mediana de 7 ejecuciones tras 2 de calentamiento. Memoria: estimación analítica, no RAM real.</p><table><thead><tr><th>Ruta</th><th>Resultado</th><th>LRE sel.</th><th>LRE mín</th><th>ULP máx</th><th>Dispersión</th><th>Conv. ms</th><th>Cálculo ms</th><th>B/celda</th><th>Factor</th></tr></thead><tbody>${last.rows.map(w=>`<tr><td>${ROUTES[w.rk].l}</td><td>${Array.isArray(w.q)?'β₀='+fm(w.q[0]):fm(w.q)}</td><td>${fm(w.lreSel)}</td><td>${fm(w.lreMin)}</td><td>${fm(w.ulpMax)}</td><td>${fm(w.spread)}</td><td>${fm(w.conv)}</td><td>${fm(w.calc)}</td><td>${w.bpc}</td><td>${w.factor.toFixed(1)}</td></tr>`).join('')}</tbody></table>`;
 $('#audt').innerHTML=`<h3>LRE por orden de evaluación (último experimento)</h3><table><thead><tr><th>Ruta</th>${last.labels.map(l=>`<th>${l}</th>`).join('')}</tr></thead><tbody>${last.rows.map(w=>`<tr><td>${ROUTES[w.rk].l}</td>${w.lreOrd.map(v=>`<td>${fm(v)}</td>`).join('')}</tr>`).join('')}</tbody></table>`}
function renderKpis(){const l=HIST[HIST.length-1];let best=null,loss=null,fac='—',ratio='—';
 HIST.forEach(r=>r.rows.forEach(w=>{if(!isNaN(w.lreSel)&&(best==null||w.lreSel>best))best=w.lreSel;const d=CAP[r.cfg.prec]-w.lreMin;if(!isNaN(d)&&(loss==null||d>loss))loss=d}));
 if(l){const t=l.rows.find(w=>w.rk==='tidy'),n=l.rows.find(w=>w.rk==='native');if(t)fac=t.factor.toFixed(1)+'×';if(t&&n&&n.calc>0)ratio=((t.conv+t.calc)/n.calc).toFixed(1)+'×'}
 const k=(v,t)=>`<div class="kpi"><b>${v}</b><span>${t}</span></div>`;
 $('#kpis').innerHTML=k(HIST.length,'Experimentos ejecutados')+k(best==null?'—':fm(best)+' díg.','Mejor precisión (LRE)')+k(loss==null?'—':fm(loss)+' díg.','Mayor pérdida de dígitos')+k(fac,'Inflación de memoria (estimada)')+k(ratio,'Tiempo Tidy/matricial')+k(l?`${l.cfg.op}/f${l.cfg.prec}`:'—','Último experimento')}
const csvOf=r=>'ruta,resultado,lre_sel,lre_min,ulp_max,dispersion,conv_ms,calc_ms,bytes_celda,factor\n'+r.rows.map(w=>[w.rk,Array.isArray(w.q)?w.q[0]:w.q,w.lreSel,w.lreMin,w.ulpMax,w.spread,w.conv,w.calc,w.bpc,w.factor].join(',')).join('\n');
const dl=(name,txt,type)=>{const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([txt],{type}));a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),500)};
function renderHist(){$('#ht').innerHTML=HIST.length?`<table><thead><tr><th>Fecha</th><th>Operación</th><th>Prec.</th><th>Semilla</th><th>n</th><th></th></tr></thead><tbody>${HIST.map(r=>`<tr><td>${r.ts.slice(0,19).replace('T',' ')}${r.tag?' ('+r.tag+')':''}</td><td>${r.cfg.op}</td><td>f${r.cfg.prec}</td><td>${r.cfg.seed}</td><td>${r.n}</td><td><button data-a="csv" data-i="${r.id}">CSV</button> <button data-a="cfg" data-i="${r.id}">Config</button></td></tr>`).join('')}</tbody></table>`:'<p class="note">Historial vacío.</p>'}
function showTab(t){$$('section').forEach(s=>s.classList.toggle('on',s.id===t));$$('#nav button').forEach(b=>b.classList.toggle('on',b.dataset.t===t))}
function compare(){const R=Math.min(12,+$('#cR').value||3),C=Math.min(12,+$('#cC').value||4),r=rng(+$('#cS').value|0),m=new Float64Array(R*C).map(()=>Math.round((r()*20-10)*100)/100);
 const t=TE.melt(m,null,R,C),b=TE.pivot(t,R,C),u=new BigUint64Array(m.buffer),w=new BigUint64Array(b.buffer);let same=0;for(let i=0;i<u.length;i++)if(u[i]===w[i])same++;
 const mt=(a)=>`<table>${Array.from({length:R},(_,i)=>`<tr>${Array.from({length:C},(_,j)=>`<td>${a[i*C+j]}</td>`).join('')}</tr>`).join('')}</table>`;
 $('#cout').innerHTML=`<div class="card"><h3>1. Matriz original</h3>${mt(m)}</div><div class="card"><h3>2. Tabla Tidy (melt, columna a columna; primeras 40 filas)</h3><table><thead><tr><th>Fila</th><th>Columna</th><th>Valor</th></tr></thead><tbody>${Array.from({length:Math.min(40,t.v.length)},(_,k)=>`<tr><td>${t.i[k]+1}</td><td>${t.j[k]+1}</td><td>${t.v[k]}</td></tr>`).join('')}</tbody></table></div><div class="card"><h3>3. Matriz reconstruida (pivot)</h3>${mt(b)}<p class="${same===u.length?'eq':'bad'}">Idéntica bit a bit: ${same===u.length?'sí':'no'} (${same}/${u.length} celdas)</p></div>`}
function resetForm(){['prec','st','op','ds','kl','ord'].forEach(i=>$('#'+i).selectedIndex=0);$('#kv').value='';$('#seed').value=42;$('#R').value=50;$('#C').value=40;$$('#rt input:not(:disabled)').forEach(e=>e.checked=true);msg('')}
$$('#nav button').forEach(b=>b.onclick=()=>showTab(b.dataset.t));
$('#run').onclick=()=>execute(readCfg());
$('#demo').onclick=()=>{resetForm();$('#kl').value='mal';$('#op').value='sum';execute(readCfg(),'demo')};
$('#reset').onclick=resetForm;$('#cgo').onclick=compare;
$('#csv').onchange=e=>{const f=e.target.files[0];if(!f)return;f.text().then(t=>{const v=t.split(/[\s,;]+/).map(Number).filter(Number.isFinite);CSV.data=v.length>=3?v:null;msg(CSV.data?`CSV: ${v.length} valores cargados.`:'El CSV necesita al menos 3 valores numéricos.',!CSV.data);if(CSV.data)$('#ds').value='csv'})};
$('#xall').onclick=()=>dl('informe_numtidy.json',JSON.stringify({generado:new Date().toISOString(),nota:'Resultados medidos en el navegador; referencia BigInt exacta, no mpmath.',experimentos:HIST},null,1),'application/json');
$('#xcsv').onclick=()=>dl('historial_numtidy.csv',HIST.map(r=>`# ${r.ts} ${JSON.stringify(r.cfg)}\n`+csvOf(r)).join('\n\n'),'text/csv');
$('#xclr').onclick=()=>{HIST=[];SE.clear();renderAll()};
$('#ht').onclick=e=>{const b=e.target.closest('button');if(!b)return;const r=HIST.find(x=>x.id==b.dataset.i);if(b.dataset.a==='csv')dl('experimento_'+r.id+'.csv',csvOf(r),'text/csv');else{const p=$('#cfgv');p.hidden=false;p.textContent=JSON.stringify(r.cfg,null,1)}};
renderAll();