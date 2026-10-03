/* CyberShield – DSA + cybersecurity simulator (vanilla JS, hash router) */
const $=(s,r=document)=>r.querySelector(s),$$=(s,r=document)=>[...r.querySelectorAll(s)];
const IC={Internet:'🌐',Firewall:'🔥',Router:'📡',Server:'🖥',Computer:'💻',Database:'🗄'};
const SEV={Critical:4,High:3,Medium:2,Low:1};
const ls={get(k){try{return JSON.parse(localStorage.getItem('cs_'+k))}catch(e){return null}},set(k,v){try{localStorage.setItem('cs_'+k,JSON.stringify(v))}catch(e){}}};
const now=()=>new Date().toTimeString().slice(0,8);
const badge=s=>`<span class="badge ${s}">${s}</span>`;
const N=(id,name,type,ip,x,y,risk='Low')=>({id,name,type,ip,x,y,risk,status:'Online'});
const mk=cnt=>{cnt=Math.max(8,Math.min(30,+cnt||+S.settings.nodes||10));const p=cnt-6,pad=x=>String(x).padStart(2,'0');
 const nodes=[N(0,'Internet','Internet','0.0.0.0',350,35),N(1,'Firewall-01','Firewall','10.0.0.1',350,110),N(2,'Router-01','Router','10.0.1.1',350,190),
 N(3,'Server-01','Server','10.0.2.10',255,280,'Medium'),N(4,'Server-02','Server','10.0.2.11',445,280),N(7,'Database-01','Database','10.0.4.2',350,365)];
 const edges=[[0,1,1],[1,2,1],[2,3,2],[2,4,3],[3,7,1],[4,7,2]];
 for(let k=0;k<p;k++){const side=k%2,j=Math.floor(k/2),sc=side?Math.floor(p/2):Math.ceil(p/2),col=Math.floor(j/6),rows=Math.min(6,sc-col*6),id=k<2?5+k:8+(k-2);
  nodes.push(N(id,'PC-'+pad(k+1),'Computer','10.0.3.'+(k+4),side?630-col*95:70+col*95,55+(j%6+.5)*(300/rows),k==0?'High':['Low','Medium','Low'][k%3]));edges.push([2,id,[4,3,2,3][k%4]])}
 return{nodes:nodes.sort((a,b)=>a.id-b.id),edges}};
const S={settings:Object.assign({theme:'dark',anim:true,sound:true,auto:true,speed:600,nodes:10},ls.get('set')||{}),
 alerts:ls.get('alerts')||[{id:1,time:'10:21',name:'Unauthorized Access',dev:'Server-01',sev:'Critical',status:'Open'},{id:2,time:'10:25',name:'Malware',dev:'PC-04',sev:'High',status:'Blocked'},
 {id:3,time:'10:29',name:'Network Anomaly',dev:'Router-02',sev:'Medium',status:'Investigating'},{id:4,time:'10:32',name:'Port Scan',dev:'Server-02',sev:'Low',status:'Resolved'}],
 hist:ls.get('hist')||[{id:1,sc:'Malware Spread',algo:'BFS',res:'Blocked'},{id:2,sc:'Network Anomaly',algo:'DFS',res:'Blocked'},{id:3,sc:'Unauthorized Access',algo:'Dijkstra',res:'Isolated'},{id:4,sc:'Port Scan',algo:'A*',res:'Resolved'}],
 act:{BFS:82,DFS:65,Dijkstra:74,'A*':58,'Priority Queue':91},scores:[],ch:null,sel:null,atk:null,dlog:[]};
let net=ls.get('net')||mk();
const persist=()=>{ls.set('alerts',S.alerts);ls.set('hist',S.hist);ls.set('set',S.settings)};
const nd=id=>net.nodes.find(n=>n.id==id),idOf=nm=>(net.nodes.find(x=>x.name==nm)||net.nodes[0]).id,ek=(a,b)=>'e'+Math.min(a,b)+'-'+Math.max(a,b);
let T=null;const stop=()=>{clearInterval(T);T=null};
const delay=()=>S.settings.anim?+S.settings.speed:30;
function toast(m){const t=$('#toast');t.textContent=m;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),2200)}
let AC;
function tone(f,d=.08,ty='sine',v=.05,at=0){if(!S.settings.sound)return;try{AC=AC||new(window.AudioContext||window.webkitAudioContext)();if(AC.state=='suspended')AC.resume();
 const o=AC.createOscillator(),g=AC.createGain(),t=AC.currentTime+at;o.type=ty;o.frequency.value=f;g.gain.setValueAtTime(v,t);g.gain.exponentialRampToValueAtTime(.0001,t+d);o.connect(g);g.connect(AC.destination);o.start(t);o.stop(t+d)}catch(e){}}
function snd(k){const m={alert:()=>{tone(880,.12,'square',.04);tone(660,.15,'square',.04,.15)},crit:()=>{[880,660,880,660].forEach((f,i)=>tone(f,.1,'square',.05,i*.13))},ok:()=>{tone(520,.08);tone(780,.14,'sine',.05,.09)},
 done:()=>[523,659,784,1047].forEach((f,i)=>tone(f,.16,'triangle',.06,i*.11)),warn:()=>tone(300,.12,'sawtooth',.035),err:()=>tone(150,.3,'sawtooth',.05)};(m[k]||(()=>{}))()}
function addAlert(name,dev,sev,status='Open'){S.alerts.unshift({id:Date.now(),time:now(),name,dev,sev,status});persist();toast('🚨 '+name+' – '+dev);snd(sev=='Critical'?'crit':'alert')}

/* ---------- Data structures & algorithms ---------- */
class PQ{constructor(){this.a=[]}push(x,p){this.a.push([p,x]);this.a.sort((m,n)=>m[0]-n[0])}pop(){return this.a.shift()}get size(){return this.a.length}}
function qsort(a,c){if(a.length<2)return a;const[p,...r]=a;return[...qsort(r.filter(x=>c(x,p)<0),c),p,...qsort(r.filter(x=>c(x,p)>=0),c)]}
const bySev=(a,b)=>SEV[b.sev]-SEV[a.sev];
function adj(){const m={};net.nodes.forEach(n=>m[n.id]=[]);const ok=i=>!['Isolated','Blocked'].includes(nd(i).status);
 net.edges.forEach(([a,b,w])=>{if(ok(a)&&ok(b)){m[a].push([b,w]);m[b].push([a,w])}});return m}
const CX={BFS:['O(V + E)','O(V)'],DFS:['O(V + E)','O(V)'],Dijkstra:['O((V + E) log V)','O(V)'],'A*':['Depends on heuristic','O(V)']};
function run(algo,s,t){const A=adj(),vis=[],steps=[],prev={},dist={[s]:0};let chk=0;
 const snap=u=>steps.push({cur:u,vis:[...vis],chk,path:null});
 if(algo=='BFS'){const q=[s],seen=new Set([s]);while(q.length){const u=q.shift();vis.push(u);snap(u);if(u==t)break;for(const[v]of A[u]){chk++;if(!seen.has(v)){seen.add(v);prev[v]=u;q.push(v)}}}}
 else if(algo=='DFS'){const st=[[s,null]];while(st.length){const[u,p]=st.pop();if(vis.includes(u))continue;if(p!==null)prev[u]=p;vis.push(u);snap(u);if(u==t)break;for(const[v]of A[u]){chk++;if(!vis.includes(v))st.push([v,u])}}}
 else{const pq=new PQ(),h=u=>algo=='A*'?Math.hypot(nd(u).x-nd(t).x,nd(u).y-nd(t).y)/200:0;pq.push(s,h(s));
  while(pq.size){const[,u]=pq.pop();if(vis.includes(u))continue;vis.push(u);snap(u);if(u==t)break;
   for(const[v,w]of A[u]){chk++;const d=dist[u]+w;if(dist[v]===undefined||d<dist[v]){dist[v]=d;prev[v]=u;pq.push(v,d+h(v))}}}}
 const last=steps[steps.length-1];let path=[];
 if(last&&vis.includes(t)){for(let x=t;x!==undefined;x=prev[x])path.unshift(x);if(path[0]!=s)path=[]}
 if(last)last.path=path;return steps}

/* ---------- Graph renderer ---------- */
function graph(el,o={}){const cls=o.cls||{};let s='<svg viewBox="0 0 700 410" class="g">';
 net.edges.forEach(([a,b,w])=>{const A=nd(a),B=nd(b);s+=`<line x1="${A.x}" y1="${A.y}" x2="${B.x}" y2="${B.y}" class="${cls[ek(a,b)]||''}"/><text class="w" x="${(A.x+B.x)/2+6}" y="${(A.y+B.y)/2}">${w}</text>`});
 const rd=net.nodes.length>16?16:23;net.nodes.forEach(n=>s+=`<g class="n ${n.status} ${cls[n.id]||''} ${S.sel==n.id&&o.sel?'sel':''}" data-id="${n.id}" transform="translate(${n.x},${n.y})"><circle r="${rd}"/><text class="ic" y="${rd>20?6:5}" style="font-size:${rd>20?18:13}px">${IC[n.type]}</text><text class="lb" y="${rd+14}" style="font-size:${rd>20?12:10}px">${n.name}</text></g>`);
 el.innerHTML=s+'</svg>';$$('.n',el).forEach(g=>g.onclick=()=>o.click&&o.click(+g.dataset.id))}
const opts=sel=>net.nodes.map(n=>`<option value="${n.id}" ${n.id==sel?'selected':''}>${n.name}</option>`).join('');
const bar=(l,p)=>`<div class="brow"><span>${l}</span><div class="meter"><i style="width:${p}%"></i></div><span>${p}%</span></div>`;
const table=(h,rows,cls='')=>`<div class="wrap"><table><tr>${h.map(x=>`<th>${x}</th>`).join('')}</tr>${rows}</table></div>`;

/* ---------- Pages ---------- */
function dash(v){const th=S.alerts.filter(a=>['Open','Investigating'].includes(a.status));
 const card=(l,n)=>`<div class="card"><small>${l}</small><b>${String(n).padStart(2,'0')}</b></div>`;
 v.innerHTML=`<h1>Dashboard</h1><p class="mut">Build → Visualize → Attack → Detect → Defend → Analyze → Learn</p>
 <div class="cards">${card('Network nodes',net.nodes.length)}${card('Active threats',th.length)}${card('Blocked',S.alerts.filter(a=>a.status=='Blocked').length)}${card('Isolated',net.nodes.filter(n=>n.status=='Isolated').length)}</div>
 <div class="two"><div class="panel"><h3>Network topology</h3><div id="g"></div><p id="info" class="mut">Click a node for details.</p></div>
 <div class="panel"><h3>Active threats</h3>${qsort(th,bySev).slice(0,6).map(a=>`<div class="row"><span>${a.name} · ${a.dev}</span>${badge(a.sev)}</div>`).join('')||'<p class="mut">No active threats.</p>'}</div></div>
 <div class="panel"><h3>Network devices</h3>${table(['Device','Type','Status','Risk'],net.nodes.map(n=>`<tr><td>${n.name}</td><td>${n.type}</td><td>${n.status}</td><td>${badge(n.risk)}</td></tr>`).join(''))}</div>
 <div class="panel"><h3>Algorithm activity</h3>${Object.entries(S.act).map(([k,p])=>bar(k,Math.min(p,100))).join('')}</div>`;
 graph($('#g'),{click:id=>{const n=nd(id);$('#info').textContent=`${n.name} · ${n.type} · ${n.ip} · ${n.status} · risk ${n.risk}`}})}

function netPage(v){let mode='select',type='Computer',pend=null;
 v.innerHTML=`<h1>Network Simulator</h1><p class="mut">Create and manage your virtual network.</p>
 <div class="two"><div class="panel"><div class="bar" id="pal">${Object.keys(IC).filter(t=>t!='Internet').map(t=>`<button data-t="${t}">${IC[t]} ${t}</button>`).join('')}</div><div id="g"></div>
 <div class="bar"><button id="add" class="pri">Add node</button><button data-m="connect">Connect / Disconnect</button><button data-m="delete">Delete</button><button data-m="select">Select</button><button id="rst">Reset</button><button id="sv">Save network</button></div>
 <div class="bar"><b>Nodes</b><button id="nminus">−</button><button id="nplus">+</button><b>Shields</b><button id="sminus">−</button><button id="splus">+</button><span id="cn" class="mut"></span></div></div>
 <div class="panel" id="side"></div></div>`;
 const side=()=>{const n=nd(S.sel);
  if(!n){$('#side').innerHTML=`<h3>Properties</h3><p class="mut">Select a node on the canvas to edit its name, IP address, type, status and risk level, or to disconnect it.</p><p class="mut">Devices: ${net.nodes.length} · Links: ${net.edges.length}</p>`;return}
  const nb=net.edges.filter(e=>e[0]==n.id||e[1]==n.id),sel=(id,arr,cur)=>`<select id="${id}">${arr.map(t=>`<option ${t==cur?'selected':''}>${t}</option>`).join('')}</select>`;
  $('#side').innerHTML=`<h3>${IC[n.type]} ${n.name}</h3><div class="bar" style="flex-direction:column;align-items:stretch">
  <label>Name <input id="f-name" value="${n.name}"></label><label>IP address <input id="f-ip" value="${n.ip}"></label>
  <label>Type ${sel('f-type',Object.keys(IC),n.type)}</label><label>Status ${sel('f-status',['Online','Compromised','Isolated','Blocked'],n.status)}</label>
  <label>Risk level ${sel('f-risk',Object.keys(SEV),n.risk)}</label></div>
  <h3 style="margin-top:14px">Connections</h3>${nb.map(e=>{const o=nd(e[0]==n.id?e[1]:e[0]);return`<div class="row"><span>${o.name} (cost ${e[2]})</span><button data-x="${o.id}">Disconnect</button></div>`}).join('')||'<p class="mut">No links.</p>'}
  <div class="bar" style="margin-top:10px"><button id="dn">Delete node</button></div>`;
  [['name','name'],['ip','ip'],['type','type'],['status','status'],['risk','risk']].forEach(([i,k])=>$('#f-'+i).onchange=e=>{n[k]=e.target.value;draw()});
  $$('[data-x]',$('#side')).forEach(b=>b.onclick=()=>{net.edges=net.edges.filter(e=>ek(e[0],e[1])!=ek(n.id,+b.dataset.x));draw()});
  $('#dn').onclick=()=>{net.nodes=net.nodes.filter(x=>x.id!=n.id);net.edges=net.edges.filter(e=>e[0]!=n.id&&e[1]!=n.id);S.sel=null;draw()}};
 const draw=()=>{graph($('#g'),{sel:1,click});side();$('#cn').textContent=`Nodes: ${net.nodes.length} · Shields: ${net.nodes.filter(n=>n.type=='Firewall').length}`;$$('[data-m]').forEach(b=>b.classList.toggle('on',b.dataset.m==mode));$$('[data-t]').forEach(b=>b.classList.toggle('on',b.dataset.t==type))};
 function click(id){if(mode=='select'){S.sel=id}
  else if(mode=='delete'){net.nodes=net.nodes.filter(n=>n.id!=id);net.edges=net.edges.filter(e=>e[0]!=id&&e[1]!=id);S.sel=null}
  else{if(pend===null){pend=id;toast('Pick the second node')}else if(pend!=id){const i=net.edges.findIndex(e=>ek(e[0],e[1])==ek(pend,id));
   if(i>=0){net.edges.splice(i,1);toast('Disconnected')}else{net.edges.push([pend,id,+prompt('Link cost (1–9)',1)||1]);toast('Connected')}pend=null}}draw()}
 $$('[data-t]').forEach(b=>b.onclick=()=>{type=b.dataset.t;draw()});$$('[data-m]').forEach(b=>b.onclick=()=>{mode=b.dataset.m;pend=null;draw()});
 $('#add').onclick=()=>{const id=Math.max(...net.nodes.map(n=>n.id))+1,c=net.nodes.filter(n=>n.type==type).length+1;net.nodes.push(N(id,`${type}-${String(c).padStart(2,'0')}`,type,`10.0.9.${id}`,60+Math.random()*580,60+Math.random()*290));S.sel=id;draw()};
 $('#rst').onclick=()=>{net=mk();S.sel=null;draw()};$('#sv').onclick=()=>{ls.set('net',net);toast('Network saved')};
 const place=t=>{const id=Math.max(...net.nodes.map(n=>n.id))+1,c=net.nodes.filter(n=>n.type==t).length+1;net.nodes.push(N(id,`${t}-${String(c).padStart(2,'0')}`,t,`10.0.9.${id}`,60+Math.random()*580,60+Math.random()*290));return id};
 const hook=(id,types)=>{const h=net.nodes.filter(n=>n.id!=id&&types.includes(n.type));net.edges.push([id,(h[Math.floor(Math.random()*h.length)]||net.nodes[0]).id,1+Math.floor(Math.random()*4)])};
 const rm=id=>{net.nodes=net.nodes.filter(n=>n.id!=id);net.edges=net.edges.filter(e=>e[0]!=id&&e[1]!=id);if(S.sel==id)S.sel=null};
 const last=ts=>net.nodes.filter(n=>ts.includes(n.type)).sort((a,b)=>b.id-a.id)[0];
 $('#nplus').onclick=()=>{if(net.nodes.length>=30)return toast('Maximum 30 nodes');const id=place(Math.random()<.3?'Server':'Computer');hook(id,['Router','Server','Firewall']);draw()};
 $('#nminus').onclick=()=>{const n=last(['Computer','Server','Database']);if(!n)return toast('No more devices to remove');rm(n.id);draw()};
 $('#splus').onclick=()=>{if(net.nodes.filter(n=>n.type=='Firewall').length>=6)return toast('Maximum 6 shields');const id=place('Firewall');hook(id,['Router']);draw()};
 $('#sminus').onclick=()=>{if(net.nodes.filter(n=>n.type=='Firewall').length<=1)return toast('Keep at least one shield');rm(last(['Firewall']).id);draw()};
 draw()}

function algoPage(v){const ch=S.ch;let steps=[],i=0,paused=false,algo='BFS';
 v.innerHTML=`<h1>Algorithm Visualizer</h1>${ch?`<div class="panel note">🎯 Challenge: ${ch.title} (use ${ch.algo})</div>`:''}
 <div class="panel bar">Algorithm <select id="al">${Object.keys(CX).map(a=>`<option ${ch&&ch.algo==a?'selected':''}>${a}</option>`).join('')}</select>
 Start <select id="s">${opts(idOf('PC-01'))}</select> Target <select id="t">${opts(idOf('Server-02'))}</select>
 <button id="go" class="pri">▶ Start</button><button id="pa">⏸ Pause</button><button id="rs">↻ Reset</button></div>
 ${net.nodes.some(n=>['Isolated','Blocked'].includes(n.status))?`<div class="panel note">Some devices are isolated or blocked, so algorithms skip them and routes may be cut. <button id="rv">Restore all devices</button></div>`:''}
 <div class="two"><div class="panel" id="g"></div><div class="panel" id="st"></div></div><p class="legend">○ Unvisited &nbsp; ◉ Current (bright) &nbsp; ✓ Visited (teal) &nbsp; ★ Target (gold ring)</p>`;
 const draw=()=>{const st=steps[i-1],cls={};const t=+$('#t').value;if(st){st.vis.forEach(x=>cls[x]='vis');cls[st.cur]='cur';if(st.path)st.path.forEach((x,k)=>{cls[x]='path';if(k)cls[ek(x,st.path[k-1])]='path'})}cls[t]=(cls[t]||'')+' tgt';
  graph($('#g'),{cls});const [tc,sc]=CX[algo];
  $('#st').innerHTML=`<h3>Algorithm status</h3><div class="row"><span>Algorithm</span><b>${algo}</b></div><div class="row"><span>Nodes visited</span><b>${st?st.vis.length:0}</b></div><div class="row"><span>Edges checked</span><b>${st?st.chk:0}</b></div>
  <div class="row"><span>Current node</span><b>${st?nd(st.cur).name:'–'}</b></div><div class="row"><span>Path found</span><b>${st&&st.path?(st.path.length?'YES':'NO'):'…'}</b></div>
  <div class="row"><span>Path</span><b>${st&&st.path?st.path.map(x=>nd(x).name).join(' → '):'–'}</b></div><div class="row"><span>Time</span><b>${tc}</b></div><div class="row"><span>Space</span><b>${sc}</b></div><div id="sc"></div>`};
 const finish=()=>{stop();const st=steps[steps.length-1];snd(st.path&&st.path.length?'done':'err');S.act[algo]=Math.min(100,(S.act[algo]||50)+3);
  if(ch){const sc=Math.max(0,100-st.vis.length*6)+(algo==ch.algo?20:0)+(st.path&&st.path.length?20:0);S.scores.push({t:ch.title,algo,sc:Math.min(sc,140)});$('#sc').innerHTML=`<p class="badge Low">Challenge score: ${Math.min(sc,140)}</p>`}};
 $('#go').onclick=()=>{stop();algo=$('#al').value;steps=run(algo,+$('#s').value,+$('#t').value);i=0;paused=false;if(!S.settings.anim){i=steps.length;draw();finish();return}
 T=setInterval(()=>{if(paused)return;i++;draw();tone(300+i*35,.06,'sine',.04);if(i>=steps.length)finish()},delay())};
 $('#pa').onclick=()=>{paused=!paused;$('#pa').textContent=paused?'▶ Resume':'⏸ Pause'};$('#rs').onclick=()=>{stop();steps=[];i=0;draw()};
 $('#al').onchange=e=>{algo=e.target.value;draw()};$('#t').onchange=draw;if($('#rv'))$('#rv').onclick=()=>{net.nodes.forEach(n=>n.status='Online');algoPage(v)};draw()}

const SCEN={'Malware Spread':{i:'🦠',d:'Simulate propagation',a:'BFS',sev:'High'},'Unauthorized Access':{i:'🔓',d:'Path to the database',a:'Dijkstra',sev:'Critical'},
 'Network Anomaly':{i:'🌐',d:'Unusual traffic spreading',a:'DFS',sev:'Medium'},'Port Scan':{i:'🔍',d:'Probe nearby servers',a:'A*',sev:'Low'}};
function attackPage(v){let sc=S.pend||'Malware Spread';S.pend=null;
 v.innerHTML=`<h1>Attack Simulator</h1><p class="mut">Educational and fully simulated – nothing real is attacked.</p>
 <div class="cards">${Object.entries(SCEN).map(([k,s])=>`<div class="card pick" data-k="${k}"><b style="font-size:26px">${s.i}</b>${k}<br><small>${s.d} · ${s.a}</small></div>`).join('')}</div>
 <div class="panel bar">Source <select id="s">${opts(idOf('PC-01'))}</select><button id="go" class="pri">▶ Start simulation</button><button id="rs">Reset network</button><a href="#/defense"><button>Go to defense →</button></a></div>
 <div class="two"><div class="panel" id="g"></div><div class="panel"><h3>Threat status: <span id="ts">IDLE</span></h3><div class="meter"><i id="pr" style="width:0"></i></div><h3 style="margin-top:14px">Attack log</h3><div class="log" id="lg"></div></div></div>`;
 const mark=()=>$$('.card.pick').forEach(c=>c.classList.toggle('sel',c.dataset.k==sc));mark();graph($('#g'));
 $$('.card.pick').forEach(c=>c.onclick=()=>{sc=c.dataset.k;mark()});
 $('#rs').onclick=()=>{net.nodes.forEach(n=>n.status='Online');S.atk=null;attackPage(v)};
 const log=m=>{$('#lg').innerHTML+=`[${now()}] ${m}<br>`;$('#lg').scrollTop=1e5};
 $('#go').onclick=()=>{stop();const s=+$('#s').value,def=SCEN[sc],tgt=sc=='Unauthorized Access'?idOf('Database-01'):sc=='Port Scan'?idOf('Server-02'):-1;
  const st=run(def.a,s,tgt),order=(st[st.length-1]?st[st.length-1].vis:[s]).filter(x=>nd(x).type!='Internet');let k=0;
  const auto=(...a)=>S.settings.auto?addAlert(...a):log('Auto alerts are off – raise one yourself in the Defense Simulator');
  S.atk={sc,algo:def.a,sev:def.sev};S.cont=false;$('#lg').innerHTML='';log('Simulation started ('+sc+' via '+def.a+')');log('Source node identified: '+nd(s).name);
  const step=()=>{if(k>=order.length){stop();$('#ts').textContent='DETECTED';log('Defense response required');snd('alert');return false}
   const n=nd(order[k]);n.status='Compromised';k++;log('Threat propagated to '+n.name);snd('warn');
   if(n.type=='Firewall'){log('Firewall detected anomaly');auto(sc,n.name,def.sev)}
   $('#pr').style.width=Math.round(k/order.length*100)+'%';$('#ts').textContent='SPREADING';graph($('#g'));
   if(k==order.length){auto(sc,n.name,def.sev);$('#ts').textContent='DETECTED'}return true};
  if(!S.settings.anim){while(step());return}T=setInterval(step,delay())}}

function defPage(v){const sel=()=>nd(S.sel);
 v.innerHTML=`<h1>Defense Simulator</h1><p class="mut">Select a compromised device, then choose a response.</p>
 <div class="two"><div class="panel" id="g"></div><div class="panel"><h3>Threat detected</h3><div id="d"></div>
 <div class="bar" style="flex-direction:column;align-items:stretch"><button data-a="block">🛡 Block connection</button><button data-a="iso">🔒 Isolate device</button><button data-a="fw">🔥 Activate firewall</button><button data-a="alert">🚨 Generate alert</button><button data-a="rst">🔄 Reset network</button></div>
 <h3 style="margin-top:14px">Defense status</h3><div id="ds" class="log"></div></div></div>`;
 const draw=()=>{graph($('#g'),{sel:1,click:id=>{S.sel=id;draw()}});const n=S.sel!=null&&nd(S.sel),bad=net.nodes.filter(x=>x.status=='Compromised');
  $('#d').innerHTML=n?`<p><b>${n.name}</b> · ${n.status}<br>Risk: ${badge(n.risk)}</p>`:'<p class="mut">Click a node in the topology.</p>';
  $('#ds').innerHTML=S.dlog.map(x=>'✓ '+x).join('<br>')+`<br><b>Threat status: ${S.atk?(bad.length?'ACTIVE ('+bad.length+' compromised)':'CONTAINED'):(S.cont?'CONTAINED':'No simulation')}</b>`};
 const done=()=>{if(S.atk&&!net.nodes.some(x=>x.status=='Compromised')){S.hist.unshift({id:S.hist.length+1,sc:S.atk.sc,algo:S.atk.algo,res:S.dlog.some(x=>x.includes('Isolated'))?'Isolated':'Blocked'});persist();S.atk=null;S.cont=true;toast('Threat contained');snd('done')}};
 $$('[data-a]').forEach(b=>b.onclick=()=>{const a=b.dataset.a,n=S.sel!=null&&nd(S.sel);
  if(['block','iso','alert'].includes(a)&&!n){snd('err');return toast('Select a node first')}
  if(a=='block'){n.status='Blocked';S.dlog.push('Connection blocked: '+n.name)}
  if(a=='iso'){n.status='Isolated';S.dlog.push('Isolated '+n.name)}
  if(a=='fw'){net.nodes.filter(x=>x.status=='Compromised').forEach(x=>x.status='Blocked');net.nodes.filter(x=>x.type=='Firewall').forEach(x=>x.status='Online');S.dlog.push('Firewall rules applied')}
  if(a=='alert'){addAlert('Manual alert',n.name,n.risk);S.dlog.push('Alert generated for '+n.name)}
  if(a=='rst'){net.nodes.forEach(x=>x.status='Online');S.dlog.push('Network reset');S.atk=null}
  snd('ok');done();draw()});draw()}

function alertsPage(v){let f={sev:'All',st:'All',q:''},cur=null;const uniq=k=>['All',...new Set(S.alerts.map(a=>a[k]))];
 v.innerHTML=`<h1>Security Alerts</h1><div class="panel bar">Severity <select id="fs">${['All',...Object.keys(SEV)].map(x=>`<option>${x}</option>`).join('')}</select>
 Status <select id="ft">${uniq('status').map(x=>`<option>${x}</option>`).join('')}</select><input id="fq" placeholder="Search alerts"></div><div class="panel" id="tb"></div><div class="panel" id="dt"></div>`;
 const draw=()=>{const L=qsort(S.alerts.filter(a=>(f.sev=='All'||a.sev==f.sev)&&(f.st=='All'||a.status==f.st)&&(a.name+a.dev).toLowerCase().includes(f.q)),bySev);
  $('#tb').innerHTML=table(['Time','Alert','Device','Severity','Status'],L.map(a=>`<tr class="click" data-id="${a.id}"><td>${a.time}</td><td>${a.name}</td><td>${a.dev}</td><td>${badge(a.sev)}</td><td>${a.status}</td></tr>`).join('')||'<tr><td colspan=5>No alerts match.</td></tr>');
  $$('tr.click').forEach(r=>r.onclick=()=>{cur=S.alerts.find(a=>a.id==r.dataset.id);det()});det()};
 const det=()=>{$('#dt').innerHTML=cur?`<h3>Alert details</h3><p>Threat: <b>${cur.name}</b><br>Device: ${cur.dev}<br>Severity: ${badge(cur.sev)}<br>Detected: ${cur.time}<br>Status: ${cur.status}</p>
  <div class="bar"><button data-s="Investigating">Investigate</button><button data-s="Isolated">Isolate</button><button data-s="Resolved">Resolve</button></div>`:'<p class="mut">Select an alert to see details.</p>';
  $$('[data-s]').forEach(b=>b.onclick=()=>{cur.status=b.dataset.s;if(cur.status=='Isolated'){const n=net.nodes.find(x=>x.name==cur.dev);if(n)n.status='Isolated'}persist();draw()})};
 $('#fs').onchange=e=>{f.sev=e.target.value;draw()};$('#ft').onchange=e=>{f.st=e.target.value;draw()};$('#fq').oninput=e=>{f.q=e.target.value.toLowerCase();draw()};draw()}

function anaPage(v){const cnt=(arr,k)=>arr.reduce((m,x)=>(m[x[k]]=(m[x[k]]||0)+1,m),{}),sec=(t,o)=>`<div class="panel"><h3>${t}</h3>${Object.entries(o).map(([k,n])=>bar(k,Math.round(n/Math.max(...Object.values(o))*100))).join('')}</div>`;
 const A=S.alerts,H=S.hist;
 v.innerHTML=`<h1>Analytics & Reports</h1><div class="cards">${[['Total simulations',H.length],['Threats detected',A.length],['Threats blocked',A.filter(a=>a.status=='Blocked').length],['Resolved',A.filter(a=>a.status=='Resolved').length],['Defense actions',S.dlog.length+H.length]].map(([l,n])=>`<div class="card"><small>${l}</small><b>${n}</b></div>`).join('')}</div>
 ${sec('Threats by type',cnt(A,'name'))}${sec('Threat severity',cnt(A,'sev'))}${sec('Algorithm usage',cnt(H,'algo'))}
 <div class="bar"><button class="pri" id="gr">Generate report</button><button id="csv">Export CSV</button><button id="pr">Print report</button></div>`;
 $('#gr').onclick=()=>toast('Report generated from '+A.length+' alerts');$('#pr').onclick=()=>print();
 $('#csv').onclick=()=>{const r=['Time,Alert,Device,Severity,Status',...A.map(a=>[a.time,a.name,a.dev,a.sev,a.status].join(','))].join('\n'),l=document.createElement('a');l.href=URL.createObjectURL(new Blob([r],{type:'text/csv'}));l.download='cybershield-report.csv';l.click()}}

function histPage(v){const draw=()=>{v.innerHTML=`<h1>Simulation History</h1><div class="panel">${table(['ID','Scenario','Algorithm','Result',''],S.hist.map((h,i)=>`<tr><td>#${String(h.id).padStart(3,'0')}</td><td>${h.sc}</td><td>${h.algo}</td><td>${h.res}</td>
 <td><button data-v="${i}">View</button> <button data-r="${i}">Replay</button> <button data-d="${i}">Delete</button></td></tr>`).join('')||'<tr><td colspan=5>No simulations yet.</td></tr>')}</div><p id="vw" class="mut"></p>`;
  $$('[data-v]').forEach(b=>b.onclick=()=>{const h=S.hist[b.dataset.v];$('#vw').textContent=`#${h.id}: ${h.sc} was analysed with ${h.algo} and ended as ${h.res}.`});
  $$('[data-r]').forEach(b=>b.onclick=()=>{S.pend=S.hist[b.dataset.r].sc;location.hash='#/attack'});
  $$('[data-d]').forEach(b=>b.onclick=()=>{S.hist.splice(b.dataset.d,1);persist();draw()})};draw()}

function scenPage(v){const C=[['🟢 Beginner','Detect a compromised PC','BFS'],['🟡 Intermediate','Find the shortest safe route','Dijkstra'],['🔴 Advanced','Contain network propagation','BFS + DFS']];
 v.innerHTML=`<h1>Security Challenges</h1><div class="cards">${C.map((c,i)=>`<div class="card"><b style="font-size:20px">${c[0]}</b>${c[1]}<br><small>Algorithm: ${c[2]}</small><br><br><button class="pri" data-i="${i}">Start</button></div>`).join('')}</div>
 <div class="panel"><h3>Scores</h3><p class="mut">Score rewards few nodes explored, the correct algorithm and a path found.</p>${S.scores.map(s=>`<div class="row"><span>${s.t} (${s.algo})</span><b>${s.sc}</b></div>`).join('')||'<p class="mut">Finish a challenge to see your score.</p>'}</div>`;
 $$('[data-i]').forEach(b=>b.onclick=()=>{const c=C[b.dataset.i];S.ch={title:c[1],algo:c[2].split(' ')[0]};location.hash='#/algorithm'})}

function setPage(v){const s=S.settings,spd=()=>Math.round((1600-s.speed)/150);
 const G=[['Quick start','Follow the flow: build a network, visualize algorithms, simulate an attack, detect it, defend, analyze the results, then read Learn.'],
 ['Dashboard','Shows node, threat, blocked and isolated counts. Click a node in the topology for its details. Threats are sorted by severity.'],
 ['Network Simulator','Pick a device type and press Add node. Choose Connect / Disconnect, then click two nodes (it asks for the link cost; clicking two linked nodes removes the link). Select a node to edit its name, IP, type, status and risk on the right. Use Nodes − / + and Shields − / + to resize the network. Save network keeps it, Reset restores the default network.'],
 ['Algorithm Visualizer','Choose BFS, DFS, Dijkstra or A*, then a start and target node, and press Start. Teal nodes are visited, the bright node is current, green marks the final path. Pause and Reset work any time.'],
 ['Sorting & Searching','Choose a sorting algorithm and the number of elements with − / +, or type your own values and press Use values. Press Start; with Sound on, the pitch follows the bar value. After sorting, search with Linear or Binary search.'],
 ['Path Finding','Choose an algorithm, then draw: Shield blocks cells, Risk zone costs 5, Source and Target move the endpoints. Grid − / + and Shields − / + change the size. Press Start to watch the search and the final route.'],
 ['Attack Simulator','Pick a scenario and a source PC, then Start. Red nodes are compromised and the log shows each step. With Auto alerts on, alerts are raised for you.'],
 ['Defense Simulator','Click a red node, then Block connection or Isolate device. Activate firewall blocks every compromised node. When none are left the threat is contained and saved to History.'],
 ['Security Alerts','Filter by severity or status, or search. Click a row, then Investigate, Isolate or Resolve.'],
 ['Analytics & Reports','Charts are built from your alerts and history. Export CSV downloads the alert table, Print opens the print dialog.'],
 ['Simulation History','View shows a summary, Replay reruns that scenario in the Attack Simulator, Delete removes it.'],
 ['Scenarios','Start a challenge to open the visualizer with the suggested algorithm. Your score appears when the run finishes.'],
 ['Learn','Documentation: algorithms, data structures, security concepts, architecture and workflow.']];
 v.innerHTML=`<h1>Settings</h1>
 <div class="panel"><h3>Appearance</h3><label><input type="radio" name="th" value="dark" ${s.theme=='dark'?'checked':''}> Dark</label> &nbsp; <label><input type="radio" name="th" value="light" ${s.theme=='light'?'checked':''}> Light</label></div>
 <div class="panel"><h3>Simulation</h3>
 <label><input type="checkbox" id="an" ${s.anim?'checked':''}> Animation</label><p class="mut">Off: every simulation jumps straight to its result.</p>
 <label><input type="checkbox" id="so" ${s.sound?'checked':''}> Sound</label> <button id="ts">Test sound</button><p class="mut">Beeps for alerts, attack spread, defense actions and results. Algorithm steps, sorting and path finding play tones too.</p>
 <label><input type="checkbox" id="au" ${s.auto?'checked':''}> Auto alerts</label><p class="mut">On: the attack simulator raises alerts by itself. Off: raise them in the Defense Simulator.</p></div>
 <div class="panel"><h3>Visualization</h3><label>Animation speed &nbsp; <span class="mut">slow</span> <input type="range" id="sp" min="1" max="10" value="${spd()}"> <span class="mut">fast</span></label><p class="mut">Used by the algorithm visualizer, attack simulator, sorting and path finding.</p></div>
 <div class="panel"><h3>Network</h3><label>Default nodes <input type="number" id="dn" min="8" max="30" value="${s.nodes}"></label><p class="mut">Devices in the default network (8 to 30). Saving a new value rebuilds the network. Reset in the Network Simulator uses it too.</p>
 <button class="pri" id="sv">Save settings</button> <button id="rs">Reset settings</button></div>
 <div class="panel"><h3>How to use CyberShield</h3>${G.map(([t,x],k)=>`<details ${k==0?'open':''}><summary>${t}</summary><p class="mut">${x}</p></details>`).join('')}</div>`;
 $$('[name=th]').forEach(r=>r.onchange=()=>{s.theme=r.value;persist();theme()});
 [['an','anim'],['so','sound'],['au','auto']].forEach(([i,k])=>$('#'+i).onchange=e=>{s[k]=e.target.checked;persist();if(k=='sound'&&s.sound)snd('ok')});
 $('#sp').oninput=e=>{s.speed=1600-e.target.value*150;persist()};
 $('#ts').onclick=()=>s.sound?snd('done'):toast('Turn Sound on first');
 $('#sv').onclick=()=>{const old=s.nodes;s.nodes=Math.max(8,Math.min(30,+$('#dn').value||10));$('#dn').value=s.nodes;persist();
  if(old!=s.nodes||net.nodes.length!=s.nodes){net=mk(s.nodes);ls.set('net',null);S.sel=null;toast(`Saved – network rebuilt with ${s.nodes} nodes`)}else toast('Settings saved')};
 $('#rs').onclick=()=>{Object.assign(s,{theme:'dark',anim:true,sound:true,auto:true,speed:600,nodes:10});net=mk(10);ls.set('net',null);persist();theme();setPage(v);toast('Settings reset')}}

function learnPage(v){const P=(t,b)=>`<div class="card"><b style="font-size:16px">${t}</b>${b}</div>`;
 v.innerHTML=`<div class="learn"><h1>Learn & Documentation</h1>
 <h2>About CyberShield</h2><p>CyberShield is an educational cybersecurity network simulator. It shows how a computer network can be represented as a graph, analysed with algorithms, attacked inside a safe simulation and protected with defensive actions.</p>
 <h2>Algorithms used</h2><div class="grid">${P('BFS','Explores level by level. Finds devices reachable from a compromised node. Time O(V + E), space O(V).')}${P('DFS','Goes deep before backtracking. Explores connected devices during threat propagation. Time O(V + E), space O(V).')}
 ${P('Dijkstra','Shortest weighted path. Finds the lowest-cost route between devices. Time O((V + E) log V).')}${P('A*','Heuristic pathfinding. Finds an efficient route between two nodes. Complexity depends on the heuristic.')}
 ${P('Quick sort','Orders security alerts by severity.')}${P('Binary search','Searches sorted security data quickly, O(log n).')}${P('Bubble, selection, insertion, merge, quick sort','The Sorting & Searching page shows how each one orders risk scores.')}${P('Grid path finding','Shields block routes and risk zones cost more. BFS, DFS, Dijkstra and A* find routes.')}</div>
 <h2>Data structures used</h2>${table(['Structure','Use'],[['Graph','Network topology'],['Queue','BFS traversal, event processing'],['Stack','DFS traversal'],['Priority queue','Dijkstra, A*, alert prioritisation'],['Array','Nodes and simulation data'],['Hash map','Device and alert lookup']].map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td></tr>`).join(''))}
 <h2>Cybersecurity concepts</h2><div class="grid">${P('Firewall','Filters traffic. Shown as a node between the Internet and the network.')}${P('Threat detection','The simulator flags a threat when a propagating attack reaches the firewall or a server.')}
 ${P('Network isolation','An affected node is cut from the graph, so no algorithm can reach it.')}${P('Security alerts','Each alert has a severity: Low, Medium, High or Critical.')}</div>
 <h2>Project architecture</h2><pre class="dia">            CYBERSHIELD
   ┌──────────────┼──────────────┐
 NETWORK       SECURITY       ANALYTICS
 (graph)    (attack/defense)  (reports)
   │              │
 Algorithms     Defense
   └──────┬───────┘
    Simulation engine
          │
     Dashboard / UI</pre>
 <h2>Technologies</h2><p>HTML5, CSS3, JavaScript (hash router), SVG visualization, CSS animations, graph algorithms, queue, stack, priority queue, arrays and hash maps.</p>
 <h2>Project objectives</h2><p>✓ Understand network topology &nbsp; ✓ Visualize graph algorithms &nbsp; ✓ Simulate threats safely &nbsp; ✓ Demonstrate defenses &nbsp; ✓ Understand complexity &nbsp; ✓ Analyze security events</p>
 <h2>Complete workflow</h2><pre class="dia">Create network → Select algorithm → Analyze network → Start attack simulation → Detect threat
→ Generate alert → Select defense → Contain threat → Update network → Store results → Generate analytics</pre>
 <h2>Algorithm → feature mapping</h2>${table(['Algorithm','Feature'],[['BFS','Reachability and threat propagation'],['DFS','Deep network exploration'],['Dijkstra','Lowest-cost path'],['A*','Efficient pathfinding'],['Quick sort','Sorting alerts'],['Binary search','Searching sorted data'],['Priority queue','Processing alerts and path search']].map(r=>`<tr><td>${r[0]}</td><td>${r[1]}</td></tr>`).join(''))}</div>`}


//#pure-start
function sortFrames(algo,arr){const a=[...arr],F=[],sorted=new Set();let cmp=0,mv=0;
 const f=c=>F.push({a:[...a],c,s:[...sorted],cmp,mv}),sw=(i,j)=>{[a[i],a[j]]=[a[j],a[i]];mv++};
 if(algo=='Bubble'){for(let i=0;i<a.length-1;i++){for(let j=0;j<a.length-1-i;j++){cmp++;f([j,j+1]);if(a[j]>a[j+1]){sw(j,j+1);f([j,j+1])}}sorted.add(a.length-1-i)}}
 else if(algo=='Selection'){for(let i=0;i<a.length;i++){let m=i;for(let j=i+1;j<a.length;j++){cmp++;f([m,j]);if(a[j]<a[m])m=j}if(m!=i){sw(i,m);f([i,m])}sorted.add(i)}}
 else if(algo=='Insertion'){for(let i=1;i<a.length;i++){for(let j=i;j>0;j--){cmp++;f([j-1,j]);if(a[j-1]>a[j]){sw(j-1,j);f([j-1,j])}else break}}}
 else if(algo=='Merge'){const ms=(l,r)=>{if(r<=l)return;const m=(l+r)>>1;ms(l,m);ms(m+1,r);const L=a.slice(l,m+1),R=a.slice(m+1,r+1);let i=0,j=0,k=l;
  while(i<L.length||j<R.length){cmp++;if(j>=R.length||(i<L.length&&L[i]<=R[j]))a[k]=L[i++];else a[k]=R[j++];mv++;f([k]);k++}};ms(0,a.length-1)}
 else{const qs=(l,r)=>{if(l>=r){if(l==r)sorted.add(l);return}const p=a[r];let i=l;for(let j=l;j<r;j++){cmp++;f([j,r]);if(a[j]<p){if(i!=j){sw(i,j);f([i,j])}i++}}
  if(i!=r){sw(i,r);f([i,r])}sorted.add(i);qs(l,i-1);qs(i+1,r)};qs(0,a.length-1)}
 a.forEach((_,i)=>sorted.add(i));f([]);return F}
function searchFrames(kind,a,t){const F=[];let cmp=0;
 if(kind=='Linear'){for(let i=0;i<a.length;i++){cmp++;const hit=a[i]==t;F.push({a,c:hit?[]:[i],s:[],h:hit?i:-1,cmp,mv:0});if(hit)break}}
 else{let lo=0,hi=a.length-1;while(lo<=hi){const m=(lo+hi)>>1;cmp++;const d=[];a.forEach((_,k)=>{if(k<lo||k>hi)d.push(k)});const hit=a[m]==t;F.push({a,c:hit?[]:[m],s:[],d,h:hit?m:-1,cmp,mv:0});if(hit)break;if(a[m]<t)lo=m+1;else hi=m-1}}
 return F}
function gridRun(algo,g,s,t){const R=g.length,C=g[0].length,key=(r,c)=>r*C+c,prev={},dist={},order=[],seen=new Set();
 const nb=(r,c)=>[[1,0],[0,1],[-1,0],[0,-1]].map(([a,b])=>[r+a,c+b]).filter(([a,b])=>a>=0&&b>=0&&a<R&&b<C&&g[a][b]!=1);
 const cost=(r,c)=>g[r][c]==2?5:1,sk=key(...s),tk=key(...t),h=(r,c)=>algo=='A*'?Math.abs(r-t[0])+Math.abs(c-t[1]):0;let found=false;dist[sk]=0;
 if(algo=='BFS'){const q=[s];seen.add(sk);while(q.length){const[r,c]=q.shift();order.push([r,c]);if(key(r,c)==tk){found=true;break}for(const[a,b]of nb(r,c)){const k=key(a,b);if(!seen.has(k)){seen.add(k);prev[k]=key(r,c);q.push([a,b])}}}}
 else if(algo=='DFS'){const st=[[s,null]];while(st.length){const[[r,c],p]=st.pop(),k=key(r,c);if(seen.has(k))continue;seen.add(k);if(p!==null)prev[k]=p;order.push([r,c]);if(k==tk){found=true;break}for(const[a,b]of nb(r,c))if(!seen.has(key(a,b)))st.push([[a,b],k])}}
 else{const pq=new PQ();pq.push(s,h(...s));while(pq.size){const[,[r,c]]=pq.pop(),k=key(r,c);if(seen.has(k))continue;seen.add(k);order.push([r,c]);if(k==tk){found=true;break}
  for(const[a,b]of nb(r,c)){const kk=key(a,b),d=dist[k]+cost(a,b);if(dist[kk]===undefined||d<dist[kk]){dist[kk]=d;prev[kk]=k;pq.push([a,b],d+h(a,b))}}}}
 const path=[];if(found)for(let k=tk;k!==undefined;k=prev[k])path.unshift([Math.floor(k/C),k%C]);
 return{order,path,found,cost:path.slice(1).reduce((s,[r,c])=>s+cost(r,c),0)}}
//#pure-end

function sortPage(v){let n=30,base=[],cur=[],F=[],i=0,paused=false,name='Bubble';
 const CXS={Bubble:['O(n²)','O(1)'],Selection:['O(n²)','O(1)'],Insertion:['O(n²)','O(1)'],Merge:['O(n log n)','O(n)'],Quick:['O(n log n) avg, O(n²) worst','O(log n)'],Linear:['O(n)','O(1)'],Binary:['O(log n)','O(1)']};
 const gen=()=>{base=Array.from({length:n},()=>5+Math.floor(Math.random()*95));cur=[...base]};gen();
 const sv=Math.max(1,Math.min(20,Math.round(20-(S.settings.speed-100)/1400*19)));
 v.innerHTML=`<h1>Sorting & Searching</h1><p class="mut">Every bar is a risk score from 5 to 99 and shows its value. Sort the scores, then search them – binary search needs sorted data.</p>
 <div class="panel bar">Sort <select id="al">${['Bubble','Selection','Insertion','Merge','Quick'].map(a=>`<option>${a}</option>`).join('')}</select>
 Elements <button id="m">−</button><b id="n"></b><button id="p">+</button> Speed <input type="range" id="sp" min="1" max="20" value="${sv}">
 <button id="nw">New random values</button><button id="go" class="pri">▶ Start</button><button id="pa">⏸ Pause</button><button id="rs">↻ Reset</button></div>
 <div class="panel bar">Your own values <input id="cv" placeholder="e.g. 40, 12, 88, 5, 63, 27" style="flex:1;min-width:220px"><button id="uv">Use values</button></div>
 <div class="panel"><div class="bars" id="bars"></div><p class="mut" id="arr" style="margin:10px 0 0;word-break:break-word"></p></div>
 <div class="key"><span><b style="background:var(--ac)"></b>Unsorted</span><span><b style="background:var(--warn)"></b>Comparing</span><span><b style="background:var(--ok)"></b>Sorted</span><span><b style="background:#a78bfa"></b>Found</span></div>
 <div class="two"><div class="panel" id="st"></div><div class="panel"><h3>Search</h3><div class="bar">Value <input id="tv" type="number" min="1" max="99" style="width:90px"><button id="ls">Linear search</button><button id="bs">Binary search</button></div><p id="sm" class="mut">Choose a value and search for it. Binary search works after sorting.</p></div></div>`;
 const draw=fr=>{const a=fr?fr.a:cur,c=new Set(fr?fr.c:[]),s=new Set(fr?fr.s:[]),d=new Set(fr&&fr.d||[]);
  $('#bars').className='bars'+(a.length>25?' many':'');
  $('#bars').innerHTML=a.map((x,k)=>`<i class="${c.has(k)?'cmp':''} ${s.has(k)?'ok':''} ${d.has(k)?'dim':''} ${fr&&fr.h===k?'hit':''}" style="height:${x}%">${x}</i>`).join('');
  $('#arr').textContent='Values: ['+a.join(', ')+']';$('#n').textContent=n;const x=CXS[name];
  $('#st').innerHTML=`<h3>Status</h3><div class="row"><span>Algorithm</span><b>${name}</b></div><div class="row"><span>Elements</span><b>${n}</b></div><div class="row"><span>Comparisons</span><b>${fr?fr.cmp:0}</b></div><div class="row"><span>Moves</span><b>${fr?fr.mv:0}</b></div><div class="row"><span>Time</span><b>${x[0]}</b></div><div class="row"><span>Space</span><b>${x[1]}</b></div>`};
 const play=(fr,fin)=>{stop();F=fr;i=0;paused=false;const k=S.settings.anim?+$('#sp').value:F.length;
  T=setInterval(()=>{if(paused)return;i=Math.min(F.length,i+k);const f=F[i-1];draw(f);if(f.c.length)tone(180+f.a[f.c[0]]*7,.05,'sine',.03);if(i>=F.length){stop();fin&&fin(F[F.length-1])}},30)};
 const fresh=()=>{stop();gen();name=$('#al').value;$('#tv').value=cur[Math.floor(n/2)];draw()};
 $('#m').onclick=()=>{n=Math.max(5,n-5);fresh()};$('#p').onclick=()=>{n=Math.min(80,n+5);fresh()};$('#nw').onclick=fresh;
 $('#uv').onclick=()=>{const a=$('#cv').value.split(/[\s,;]+/).filter(Boolean).map(Number);if(a.length<2||a.length>80||a.some(x=>!Number.isInteger(x)||x<1||x>99))return toast('Enter 2–80 whole numbers between 1 and 99');
  stop();base=a;cur=[...a];n=a.length;name=$('#al').value;$('#tv').value=a[0];draw()};
 $('#al').onchange=()=>{name=$('#al').value;draw()};
 $('#go').onclick=()=>{name=$('#al').value;play(sortFrames(name,base),l=>{cur=l.a;S.act[name+' Sort']=Math.min(100,(S.act[name+' Sort']||40)+3);$('#sm').textContent='Sorted. Binary search is now available.';snd('done')})};
 $('#pa').onclick=()=>{paused=!paused;$('#pa').textContent=paused?'▶ Resume':'⏸ Pause'};$('#rs').onclick=()=>{stop();cur=[...base];draw()};
 const srch=k=>{const t=+$('#tv').value;if(!t)return toast('Enter a value to search');name=k;
  if(k=='Binary'&&cur.some((x,j)=>j&&cur[j-1]>x)){$('#sm').textContent='Binary search needs sorted data. Run a sort first.';snd('err');return}
  play(searchFrames(k,cur,t),l=>{$('#sm').textContent=l.h>=0?`${k} search found ${t} at index ${l.h} after ${l.cmp} comparisons.`:`${k} search: ${t} is not in the array (${l.cmp} comparisons).`;snd(l.h>=0?'done':'err')})};
 $('#ls').onclick=()=>srch('Linear');$('#bs').onclick=()=>srch('Binary');$('#tv').value=cur[Math.floor(n/2)];draw()}

function pathPage(v){let C=24,R=13,g=[],st=[6,2],en=[6,21],tool='sh',down=false,pv=0,ec=[];
 const mkg=()=>{const o=g,ng=Array.from({length:R},(_,r)=>Array.from({length:C},(_,c)=>(o[r]&&o[r][c])||0));g=ng;st=[Math.min(st[0],R-1),Math.min(st[1],C-1)];en=[Math.min(en[0],R-1),Math.min(en[1],C-1)];if(st+''==en+'')st=[0,0]};
 v.innerHTML=`<h1>Path Finding</h1><p class="mut">Route traffic from the source to the target. Shields block a path, risk zones cost 5 instead of 1.</p>
 <div class="panel bar">Algorithm <select id="al">${['BFS','DFS','Dijkstra','A*'].map(a=>`<option>${a}</option>`).join('')}</select>
 Grid <button id="gm">−</button><button id="gp">+</button> Shields <button id="sm">−</button><button id="sp">+</button> Speed <input type="range" id="sd" min="1" max="12" value="${Math.max(1,Math.min(12,Math.round(12-(S.settings.speed-100)/1400*11)))}">
 <button id="go" class="pri">▶ Start</button><button id="rs">↻ Clear path</button><button id="cl">Clear all</button></div>
 <div class="panel bar">Draw: ${[['sh','🛡 Shield'],['rk','⚠ Risk zone'],['st','Source'],['en','Target'],['er','Erase']].map(([k,l])=>`<button data-t="${k}">${l}</button>`).join('')}<button id="rn">Random shields</button></div>
 <div class="two"><div class="panel"><div class="pg" id="pg"></div></div><div class="panel" id="info"></div></div>
 <div class="key"><span><b style="background:#3b82f6"></b>Source</span><span><b style="background:#fbbf24"></b>Target</span><span><b style="background:#64748b"></b>Shield</span><span><b style="background:#9a3412"></b>Risk zone</span><span><b style="background:#0e7490"></b>Explored</span><span><b style="background:var(--ok)"></b>Path</span></div>`;
 const shields=()=>g.flat().filter(x=>x==1).length;
 const cls=(r,c)=>r==st[0]&&c==st[1]?'st':r==en[0]&&c==en[1]?'en':['','sh','rk'][g[r][c]];
 const info=(o={})=>{$('#info').innerHTML=`<h3>Status</h3><div class="row"><span>Algorithm</span><b>${$('#al').value}</b></div><div class="row"><span>Grid nodes</span><b>${R*C}</b></div><div class="row"><span>Shields</span><b>${shields()}</b></div><div class="row"><span>Explored</span><b>${o.ex??0}</b></div><div class="row"><span>Path found</span><b>${o.f===undefined?'…':o.f?'YES':'NO'}</b></div><div class="row"><span>Path length</span><b>${o.pl??'–'}</b></div><div class="row"><span>Path cost</span><b>${o.pc??'–'}</b></div><p class="mut">DFS ignores cost, BFS minimizes steps, Dijkstra and A* minimize cost.</p>`};
 const build=()=>{mkg();const el=$('#pg');el.style.gridTemplateColumns=`repeat(${C},1fr)`;el.innerHTML='';ec=[];
  for(let r=0;r<R;r++){ec[r]=[];for(let c=0;c<C;c++){const d=document.createElement('div');d.className=cls(r,c);d.dataset.r=r;d.dataset.c=c;el.appendChild(d);ec[r][c]=d}}
  $$('[data-t]').forEach(b=>b.classList.toggle('on',b.dataset.t==tool));info()};
 const clearViz=()=>{stop();for(let r=0;r<R;r++)for(let c=0;c<C;c++)ec[r][c].className=cls(r,c);info()};
 const paint=(r,c,first)=>{if(tool=='st'){if(g[r][c]!=1&&[r,c]+''!=en+''){st=[r,c]}}else if(tool=='en'){if(g[r][c]!=1&&[r,c]+''!=st+''){en=[r,c]}}
  else if(r==st[0]&&c==st[1]||r==en[0]&&c==en[1])return;else{const w={sh:1,rk:2,er:0}[tool];if(first)pv=g[r][c]==w?0:w;g[r][c]=pv}
  clearViz();$$('#pg div').forEach(()=>{});for(let a=0;a<R;a++)for(let b=0;b<C;b++)ec[a][b].className=cls(a,b);info()};
 const at=e=>{const t=document.elementFromPoint(e.clientX,e.clientY);return t&&t.dataset&&t.dataset.r!==undefined?[+t.dataset.r,+t.dataset.c]:null};
 $('#pg').onpointerdown=e=>{const p=at(e);if(!p)return;down=true;paint(p[0],p[1],true)};
 $('#pg').onpointermove=e=>{if(!down)return;const p=at(e);if(p&&tool!='st'&&tool!='en')paint(p[0],p[1],false)};
 window.onpointerup=()=>down=false;
 $$('[data-t]').forEach(b=>b.onclick=()=>{tool=b.dataset.t;$$('[data-t]').forEach(x=>x.classList.toggle('on',x==b))});
 const rnd=k=>{let t=0;while(k>0&&t++<500){const r=Math.floor(Math.random()*R),c=Math.floor(Math.random()*C);if(!g[r][c]&&cls(r,c)==''){g[r][c]=1;k--}}};
 $('#rn').onclick=()=>{rnd(Math.round(R*C*.2));clearViz();build()};
 $('#sp').onclick=()=>{rnd(5);build()};
 $('#sm').onclick=()=>{const L=[];g.forEach((row,r)=>row.forEach((x,c)=>x==1&&L.push([r,c])));L.sort(()=>Math.random()-.5).slice(0,5).forEach(([r,c])=>g[r][c]=0);build()};
 $('#gp').onclick=()=>{C=Math.min(48,C+4);R=Math.round(C*.55);build()};$('#gm').onclick=()=>{C=Math.max(12,C-4);R=Math.round(C*.55);build()};
 $('#cl').onclick=()=>{g=g.map(r=>r.map(()=>0));build()};$('#rs').onclick=clearViz;
 $('#go').onclick=()=>{clearViz();const algo=$('#al').value,res=gridRun(algo,g,st,en),sp=S.settings.anim?+$('#sd').value:1e6;let k=0,p=0;
  T=setInterval(()=>{if(k<res.order.length){for(let j=0;j<sp&&k<res.order.length;j++,k++){const[r,c]=res.order[k];if(cls(r,c)=='')ec[r][c].className='vs';else if(cls(r,c)=='sh'||cls(r,c)=='rk')ec[r][c].className='vs'}info({ex:k});tone(250+Math.min(k,300)*3,.03,'sine',.025)}
   else if(p<res.path.length){const[r,c]=res.path[p++];if(cls(r,c)=='')ec[r][c].className='pt';info({ex:res.order.length,f:true,pl:p-1,pc:res.cost});tone(500+p*25,.05,'triangle',.04)}
   else{stop();S.act[algo]=Math.min(100,(S.act[algo]||50)+3);info({ex:res.order.length,f:res.found,pl:res.found?res.path.length-1:undefined,pc:res.found?res.cost:undefined});if(!res.found){toast('No route – the shields block every path');snd('err')}else snd('done')}},25)};
 build();rnd(Math.round(R*C*.15));build()}

/* ---------- Router ---------- */
const routes={dashboard:dash,network:netPage,algorithm:algoPage,sorting:sortPage,pathfinding:pathPage,attack:attackPage,defense:defPage,alerts:alertsPage,analytics:anaPage,history:histPage,scenarios:scenPage,learn:learnPage,settings:setPage};
const theme=()=>document.body.dataset.theme=S.settings.theme;
function route(){stop();const r=location.hash.replace('#/','')||'dashboard';if(r!='algorithm'&&r!='scenarios')S.ch=null;
 $$('#nav a').forEach(a=>a.classList.toggle('on',a.getAttribute('href')=='#/'+r));(routes[r]||dash)($('#view'));window.scrollTo(0,0)}
window.addEventListener('hashchange',route);theme();route();
