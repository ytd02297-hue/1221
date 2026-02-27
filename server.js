const WebSocket = require('ws');
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

// ══════════════════════════════════════════════════════════
//  ⚙️  CONFIG
// ══════════════════════════════════════════════════════════
const OWNER_NAME = 'Admin';       // ← ПОСТАВЬ СВОЙ НИК
const ADMIN_PASS = 'secret123';   // ← ПОСТАВЬ СВОЙ ПАРОЛЬ

const server = http.createServer((req, res) => {
  if (req.url === '/' || req.url === '/index.html') {
    res.writeHead(200, { 'Content-Type': 'text/html' });
    res.end(fs.readFileSync(path.join(__dirname, 'index.html')));
  } else {
    res.writeHead(404); res.end('Not found');
  }
});

// ── WebSocket on SAME server (Railway fix) ──────────────
const wss = new WebSocket.Server({ server });

const WORLD_W = 5000, WORLD_H = 5000, TICK_RATE = 60;
const MAX_FOOD = 300, MAX_SHAPES = 180, MAX_PENTAGONS = 30,
      MAX_HEXAGONS = 20, MAX_POWERUPS = 22, MAX_BOSSES = 3;

let players = {}, bullets = {}, food = [], shapes = [], powerups = [], bosses = [];
let nextId = 1;
let serverLog = [], chatHistory = [];
const takenNames = new Set();
const ownerToken = crypto.randomBytes(20).toString('hex');
let ownerConnected = false;

// ── Active server event ─────────────────────────────────
let activeEvent = null; // { type, endFrame, data }
let eventTimer = 0;
const EVENT_INTERVAL = 60 * 300; // every 5 min

function rand(a,b){return Math.random()*(b-a)+a;}
function randInt(a,b){return Math.floor(rand(a,b+1));}
function dist(ax,ay,bx,by){return Math.sqrt((ax-bx)**2+(ay-by)**2);}
function ang(ax,ay,bx,by){return Math.atan2(by-ay,bx-ax);}
function clamp(v,a,b){return Math.max(a,Math.min(b,v));}

// ══════════════════════════════════════════════════════════
//  TANK CONFIGS
// ══════════════════════════════════════════════════════════
const TANKS = [
  {name:'Basic',      B:[{a:0,w:12,l:30}],                                                                                      fr:22,bs:8, bd:20,bl:90},
  {name:'Twin',       B:[{a:-.18,w:10,l:30},{a:.18,w:10,l:30}],                                                                 fr:13,bs:8, bd:14,bl:85},
  {name:'Sniper',     B:[{a:0,w:8,l:55}],                                                                                        fr:38,bs:16,bd:55,bl:135},
  {name:'MachineGun', B:[{a:0,w:18,l:28}],                                                                                       fr:6, bs:7, bd:10,bl:60,sp:.07},
  {name:'Flank',      B:[{a:0,w:12,l:30},{a:Math.PI,w:10,l:25}],                                                                fr:20,bs:8, bd:17,bl:85},
  {name:'Triplet',    B:[{a:-.28,w:10,l:30},{a:0,w:12,l:34},{a:.28,w:10,l:30}],                                                 fr:15,bs:8, bd:13,bl:80},
  {name:'Destroyer',  B:[{a:0,w:24,l:40}],                                                                                       fr:58,bs:11,bd:95,bl:98},
  {name:'Octo',       B:[0,1,2,3,4,5,6,7].map(i=>({a:i*Math.PI/4,w:10,l:28})),                                                  fr:10,bs:7, bd:11,bl:78},
  {name:'Tri-angle',  B:[{a:0,w:14,l:32},{a:2.35,w:10,l:26},{a:-2.35,w:10,l:26}],                                              fr:16,bs:9, bd:17,bl:84},
  {name:'Sprayer',    B:[{a:0,w:15,l:30}],                                                                                        fr:4, bs:9, bd:9, bl:72,sp:.15},
  {name:'Booster',    B:[{a:0,w:12,l:32},{a:2.5,w:8,l:22},{a:-2.5,w:8,l:22},{a:Math.PI,w:8,l:20}],                            fr:15,bs:10,bd:15,bl:85},
  {name:'PentaShot',  B:[{a:-.5,w:9,l:28},{a:-.25,w:10,l:31},{a:0,w:12,l:34},{a:.25,w:10,l:31},{a:.5,w:9,l:28}],              fr:20,bs:8, bd:12,bl:80},
  {name:'Annihilator',B:[{a:0,w:32,l:46}],                                                                                       fr:75,bs:12,bd:140,bl:102},
  {name:'Auto3',      B:[{a:0,w:12,l:30},{a:2.09,w:10,l:28},{a:-2.09,w:10,l:28}],                                              fr:18,bs:8, bd:15,bl:84},
  {name:'Streamliner',B:[{a:0,w:9,l:52},{a:0,w:7,l:45},{a:0,w:5,l:38}],                                                        fr:8, bs:13,bd:12,bl:112},
  {name:'Stalker',    B:[{a:0,w:6,l:60}],                                                                                        fr:45,bs:18,bd:60,bl:150},
  {name:'Spread3',    B:[{a:-.4,w:11,l:30},{a:0,w:13,l:33},{a:.4,w:11,l:30}],                                                   fr:18,bs:8, bd:15,bl:82,sp:.04},
];

const LT=[0,500,1000,2000,4000,7500,11250,15000,22500,30000,40000,55000,75000,100000,130000];
function getLevel(s){for(let i=LT.length-1;i>=0;i--)if(s>=LT[i])return i;return 0;}

// ══════════════════════════════════════════════════════════
//  WORLD SPAWN
// ══════════════════════════════════════════════════════════
function spawnFood(){
  while(food.length<MAX_FOOD)
    food.push({id:nextId++,x:rand(60,WORLD_W-60),y:rand(60,WORLD_H-60),r:10,score:10});
}
function makeShape(type){
  const cfg={
    triangle:{hp:30,sc:25}, square:{hp:100,sc:100},
    pentagon:{hp:250,sc:300}, hexagon:{hp:180,sc:200},
    alpha:{hp:4000,sc:4000}, crasher:{hp:20,sc:15}
  }[type]||{hp:100,sc:100};
  return{id:nextId++,x:rand(150,WORLD_W-150),y:rand(150,WORLD_H-150),type,...cfg,maxHp:cfg.hp,angle:rand(0,Math.PI*2),rotSpeed:rand(-.016,.016),vx:0,vy:0};
}
function spawnShapes(){
  while(shapes.filter(s=>['triangle','square'].includes(s.type)).length<MAX_SHAPES){
    const t=Math.random()<.44?'triangle':'square';shapes.push(makeShape(t));
  }
  while(shapes.filter(s=>s.type==='pentagon').length<MAX_PENTAGONS) shapes.push(makeShape('pentagon'));
  while(shapes.filter(s=>s.type==='hexagon').length<MAX_HEXAGONS) shapes.push(makeShape('hexagon'));
  while(shapes.filter(s=>s.type==='crasher').length<15) shapes.push({...makeShape('crasher'),vx:rand(-1.5,1.5),vy:rand(-1.5,1.5)});
  if(!shapes.find(s=>s.type==='alpha')) shapes.push({...makeShape('alpha'),x:rand(600,WORLD_W-600),y:rand(600,WORLD_H-600),rotSpeed:.0025});
}
function spawnPU(){
  const types=['health','speed','damage','shield','freeze','magnet','ghost','nuke','doubleScore','invincible'];
  powerups.push({id:nextId++,x:rand(120,WORLD_W-120),y:rand(120,WORLD_H-120),type:types[randInt(0,types.length-1)],life:1100});
}
spawnFood(); spawnShapes();
for(let i=0;i<MAX_POWERUPS;i++) spawnPU();

// ══════════════════════════════════════════════════════════
//  HELPERS
// ══════════════════════════════════════════════════════════
function broadcast(d){const m=JSON.stringify(d);for(const ws of wss.clients)if(ws.readyState===WebSocket.OPEN)ws.send(m);}
function send(ws,d){if(ws&&ws.readyState===WebSocket.OPEN)ws.send(JSON.stringify(d));}
function cc(ax,ay,ar,bx,by,br){const dx=ax-bx,dy=ay-by;return dx*dx+dy*dy<(ar+br)*(ar+br);}
function logEv(m){const e=`[${new Date().toLocaleTimeString()}] ${m}`;serverLog.unshift(e);if(serverLog.length>120)serverLog.pop();console.log(e);}

function ser(p){
  return{id:p.id,x:p.x,y:p.y,angle:p.angle,hp:p.hp,maxHp:p.maxHp,score:p.score,level:p.level,
    tankType:p.tankType,name:p.name,alive:p.alive,kills:p.kills,shieldActive:p.shieldActive,
    isOwner:p.isOwner,frozen:p.frozen,rainbow:p.rainbow,size:p.size||1,isBot:p.isBot||false,
    ghost:p.ghost||false,invincible:p.invincible>0};
}
function calcHp(p){return Math.floor((100+p.stats.maxHealth*25)*(p.size||1));}
function applyStats(p){
  p.maxHp=calcHp(p);if(p.hp>p.maxHp)p.hp=p.maxHp;
  const c=TANKS[p.tankType]||TANKS[0];
  p.fireRate=Math.max(3,c.fr-p.stats.reload*2);
  p.bulletSpeed=c.bs+p.stats.bulletSpeed*.9;
  p.bulletDamage=c.bd+p.stats.bulletDamage*6;
  p.bulletLife=c.bl;
  p.speed=(3+p.stats.movementSpeed*.45)/(p.size||1);
}
function upgradeTank(p){
  const lvl=getLevel(p.score);
  if(lvl!==p.level){
    const g=lvl-p.level;p.level=lvl;p.statPoints=Math.min(56,p.statPoints+g);
    applyStats(p);
    broadcast({type:'levelUp',id:p.id,level:lvl});
    if(p.ws&&p.ws.readyState===1) send(p.ws,{type:'statsUpdated',stats:p.stats,statPoints:p.statPoints,maxHp:p.maxHp});
  }
}
function makeUnique(n){
  const base=(n||'Player').substring(0,18).trim();
  if(!takenNames.has(base)){takenNames.add(base);return base;}
  for(let i=2;i<9999;i++){const t=base+i;if(!takenNames.has(t)){takenNames.add(t);return t;}}
  return base+'_'+randInt(100,999);
}
function releaseName(n){takenNames.delete(n);}

// ══════════════════════════════════════════════════════════
//  SERVER EVENTS
// ══════════════════════════════════════════════════════════
const EVENTS=[
  {type:'doubleXP',    name:'⭐ DOUBLE XP',    color:'#ffdd44', duration:60*120},
  {type:'chaos',       name:'💥 CHAOS MODE',   color:'#ff4444', duration:60*90},
  {type:'feast',       name:'🍕 FOOD FEAST',   color:'#44ff88', duration:60*60},
  {type:'bossRaid',    name:'👹 BOSS RAID',    color:'#ff6600', duration:60*180},
  {type:'shapeStorm',  name:'🔷 SHAPE STORM',  color:'#8844ff', duration:60*90},
  {type:'speedrun',    name:'⚡ SPEED RUN',    color:'#44aaff', duration:60*60},
];

function startEvent(typeOverride){
  const ev=typeOverride
    ? EVENTS.find(e=>e.type===typeOverride)||EVENTS[randInt(0,EVENTS.length-1)]
    : EVENTS[randInt(0,EVENTS.length-1)];
  activeEvent={...ev,endFrame:frameCount+ev.duration};
  if(ev.type==='feast'){for(let i=0;i<80;i++){const f={id:nextId++,x:rand(60,WORLD_W-60),y:rand(60,WORLD_H-60),r:14,score:30};food.push(f);}broadcast({type:'foodSpawn',food:food.slice(-80)});}
  if(ev.type==='bossRaid'){spawnBoss();if(bosses.length<MAX_BOSSES)spawnBoss();}
  if(ev.type==='shapeStorm'){for(let i=0;i<40;i++)shapes.push(makeShape(Math.random()<.5?'pentagon':'hexagon'));broadcast({type:'shapeSpawn',shapes});}
  broadcast({type:'eventStart',event:{type:ev.type,name:ev.name,color:ev.color,duration:ev.duration}});
  broadcast({type:'announce',msg:`🎉 EVENT: ${ev.name}!`,color:ev.color});
  logEv(`Event started: ${ev.name}`);
}
function endEvent(){
  if(!activeEvent)return;
  broadcast({type:'eventEnd',eventType:activeEvent.type});
  broadcast({type:'announce',msg:`Event "${activeEvent.name}" ended!`,color:'#aaaaaa'});
  logEv(`Event ended: ${activeEvent.name}`);
  activeEvent=null;
}

// ══════════════════════════════════════════════════════════
//  BOT AI
// ══════════════════════════════════════════════════════════
const DIFF={easy:{spd:1.4,react:.02},medium:{spd:2.2,react:.07},hard:{spd:3.1,react:.18}};
function mkBot(name,diff='medium'){
  const id='bot'+nextId++;
  const d=DIFF[diff]||DIFF.medium;
  const uname=makeUnique(name||'Bot');
  const bot={
    id,isBot:true,diff,diffName:diff,ws:null,
    x:rand(300,WORLD_W-300),y:rand(300,WORLD_H-300),vx:0,vy:0,angle:0,
    hp:100,maxHp:100,score:0,level:0,tankType:0,
    name:uname,speed:d.spd,
    fireRate:25,bulletDamage:18,bulletSpeed:8,bulletLife:88,
    statPoints:0,
    stats:{healthRegen:0,maxHealth:0,bodyDamage:0,bulletSpeed:0,bulletPen:0,bulletDamage:0,reload:0,movementSpeed:0},
    fireCooldown:0,kills:0,deaths:0,
    shieldActive:false,shieldTimer:0,
    inputs:{up:false,down:false,left:false,right:false,fire:false},
    alive:true,invincible:120,regenTimer:0,
    isOwner:false,frozen:false,rainbow:false,ghost:false,size:1,
    aiState:0,aiWP:{x:rand(200,WORLD_W-200),y:rand(200,WORLD_H-200)},aiTimer:0,aiUpTimer:0,
    respawnTimer:0,
  };
  players[id]=bot;
  broadcast({type:'playerJoin',player:ser(bot)});
  logEv(`🤖 Bot "${uname}" (${diff})`);
  return bot;
}

function tickBot(bot){
  // Respawn
  if(!bot.alive){
    if(++bot.respawnTimer>=300){
      bot.alive=true;bot.hp=calcHp(bot);bot.invincible=120;
      bot.respawnTimer=0;
      bot.x=rand(300,WORLD_W-300);bot.y=rand(300,WORLD_H-300);
      broadcast({type:'playerRespawn',id:bot.id,x:bot.x,y:bot.y,hp:bot.hp,maxHp:bot.maxHp,score:bot.score,level:bot.level});
    }
    return;
  }
  if(bot.invincible>0)bot.invincible--;
  if(bot.frozen)return;

  // Regen
  if(++bot.regenTimer>=90&&bot.hp<bot.maxHp){bot.hp=Math.min(bot.maxHp,bot.hp+2);bot.regenTimer=0;}

  // Auto-upgrade stats
  if(++bot.aiUpTimer>90&&bot.statPoints>0){
    const sl=['bulletDamage','reload','movementSpeed','bulletSpeed','maxHealth','healthRegen','bulletPen'];
    const s=sl[randInt(0,sl.length-1)];
    if(bot.stats[s]<7){bot.stats[s]++;bot.statPoints--;applyStats(bot);}
    bot.aiUpTimer=0;
  }
  // Auto pick tank
  if(bot.level>=16&&bot.tankType<15)bot.tankType=randInt(10,16);
  else if(bot.level>=8&&bot.tankType<7)bot.tankType=randInt(4,9);
  else if(bot.level>=4&&bot.tankType<3)bot.tankType=randInt(1,4);

  bot.aiTimer++;
  const d=DIFF[bot.diffName]||DIFF.medium;

  // Find targets
  let nf=null,nfd=Infinity,ne=null,ned=Infinity;
  for(const f of food){const dd=dist(bot.x,bot.y,f.x,f.y);if(dd<nfd){nfd=dd;nf=f;}}
  for(const pid in players){
    const p=players[pid];if(pid===bot.id||!p.alive)continue;
    const dd=dist(bot.x,bot.y,p.x,p.y);if(dd<ned){ned=dd;ne=p;}
  }

  const lowHp=bot.hp/bot.maxHp<0.28;
  let tx=bot.aiWP.x,ty=bot.aiWP.y;
  bot.inputs.fire=false;

  if(bot.aiTimer>80+randInt(0,60)){bot.aiTimer=0;bot.aiWP={x:rand(200,WORLD_W-200),y:rand(200,WORLD_H-200)};}

  if(ne&&ned<320&&!lowHp&&Math.random()<d.react){
    tx=ne.x;ty=ne.y;
    bot.angle=ang(bot.x,bot.y,ne.x,ne.y)+(Math.random()-.5)*.2;
    bot.inputs.fire=ned<300;
  } else if(lowHp&&ne&&ned<250){
    tx=bot.x*2-ne.x;ty=bot.y*2-ne.y;
  } else if(nf&&nfd<220){
    tx=nf.x;ty=nf.y;bot.angle=ang(bot.x,bot.y,nf.x,nf.y);
  } else {
    bot.angle=ang(bot.x,bot.y,tx,ty);
  }

  const dx=tx-bot.x,dy=ty-bot.y,dl=Math.sqrt(dx*dx+dy*dy)||1;
  if(dl>10){bot.x=clamp(bot.x+dx/dl*bot.speed,22,WORLD_W-22);bot.y=clamp(bot.y+dy/dl*bot.speed,22,WORLD_H-22);}

  // Shoot
  if(--bot.fireCooldown<=0&&bot.inputs.fire){
    const cfg=TANKS[bot.tankType]||TANKS[0];bot.fireCooldown=bot.fireRate;
    for(const barrel of cfg.B){
      const sp=cfg.sp?(Math.random()-.5)*cfg.sp*2:0;
      const ba=bot.angle+(barrel.a||0)+sp;
      const bid='bb'+nextId++;
      bullets[bid]={id:bid,owner:bot.id,x:bot.x+Math.cos(ba)*(barrel.l||30),y:bot.y+Math.sin(ba)*(barrel.l||30),vx:Math.cos(ba)*bot.bulletSpeed,vy:Math.sin(ba)*bot.bulletSpeed,r:(barrel.w||12)/2+2,damage:bot.bulletDamage,pen:1+Math.floor(bot.stats.bulletPen/2),life:bot.bulletLife};
    }
  }
  // Eat food
  for(let i=food.length-1;i>=0;i--){
    if(cc(bot.x,bot.y,22,food[i].x,food[i].y,food[i].r)){
      const sc=activeEvent?.type==='doubleXP'?food[i].score*2:food[i].score;
      bot.score+=sc;upgradeTank(bot);broadcast({type:'foodEat',id:food[i].id});food.splice(i,1);
    }
  }
}

// ══════════════════════════════════════════════════════════
//  PLAYER CONNECTION
// ══════════════════════════════════════════════════════════
wss.on('connection',(ws)=>{
  const id='p'+nextId++;
  const p={
    id,ws,x:rand(400,WORLD_W-400),y:rand(400,WORLD_H-400),vx:0,vy:0,angle:0,
    hp:100,maxHp:100,score:0,level:0,tankType:0,name:'Player',speed:3,
    fireRate:22,bulletDamage:20,bulletSpeed:8,bulletLife:90,statPoints:0,
    stats:{healthRegen:0,maxHealth:0,bodyDamage:0,bulletSpeed:0,bulletPen:0,bulletDamage:0,reload:0,movementSpeed:0},
    fireCooldown:0,kills:0,deaths:0,shieldActive:false,shieldTimer:0,
    inputs:{up:false,down:false,left:false,right:false,fire:false},
    alive:true,invincible:180,regenTimer:0,selectedTank:0,
    isOwner:false,frozen:false,rainbow:false,ghost:false,size:1,freezeTimer:0,magnetActive:false,
    isBot:false,sessionToken:'',doubleScore:false,
  };
  players[id]=p;

  send(ws,{type:'init',id,worldW:WORLD_W,worldH:WORLD_H,
    food,shapes,
    powerups:powerups.map(pu=>({id:pu.id,x:pu.x,y:pu.y,type:pu.type})),
    bosses:bosses.map(b=>({id:b.id,x:b.x,y:b.y,hp:b.hp,maxHp:b.maxHp,angle:b.angle})),
    players:Object.values(players).filter(q=>q.id!==id).map(ser),
    chatHistory:chatHistory.slice(0,30),
    activeEvent,
  });
  broadcast({type:'playerJoin',player:ser(p)});
  logEv(`+ ${id} connected`);

  ws.on('message',(raw)=>{
    try{
      const msg=JSON.parse(raw);
      if(!players[id])return;
      const p=players[id];

      if(msg.type==='input'){
        if(!p.frozen){p.inputs=msg.inputs;p.angle=msg.angle;}
        if(msg.name&&msg.name!==p.name){
          const req=msg.name.trim().substring(0,20);
          if(req===OWNER_NAME){
            if(msg.adminPass===ADMIN_PASS&&!ownerConnected){
              releaseName(p.name);p.name=OWNER_NAME;takenNames.add(OWNER_NAME);
              p.isOwner=true;p.sessionToken=ownerToken;ownerConnected=true;
              send(ws,{type:'modAccess',granted:true,token:ownerToken});
              broadcast({type:'nameChange',id,name:p.name,isOwner:true});
              logEv(`👑 OWNER logged in`);
            } else if(ownerConnected){
              const u=makeUnique(req+'_');releaseName(p.name);p.name=u;send(ws,{type:'nameTaken',suggested:u});
            } else {
              const u=makeUnique(req);releaseName(p.name);p.name=u;send(ws,{type:'nameTaken',suggested:u});
            }
          } else {
            const u=makeUnique(req);if(p.name&&p.name!==u)releaseName(p.name);p.name=u;
            if(u!==req)send(ws,{type:'nameTaken',suggested:u});
          }
          broadcast({type:'nameChange',id,name:p.name,isOwner:p.isOwner});
        }
      }
      else if(msg.type==='adminLogin'){
        if(msg.name===OWNER_NAME&&msg.pass===ADMIN_PASS&&!ownerConnected){
          p.isOwner=true;p.sessionToken=ownerToken;ownerConnected=true;
          send(ws,{type:'modAccess',granted:true,token:ownerToken});
          logEv(`👑 OWNER auth OK`);
        } else { send(ws,{type:'modError',msg:'Wrong password or already online'}); }
      }
      else if(msg.type==='respawn'){
        if(p.alive)return;
        const ns=Math.floor(p.score*.5);
        Object.assign(p,{hp:calcHp(p),maxHp:calcHp(p),score:ns,x:rand(400,WORLD_W-400),y:rand(400,WORLD_H-400),alive:true,invincible:180,level:getLevel(ns),fireCooldown:0,shieldActive:false,shieldTimer:0,frozen:false,ghost:false});
        applyStats(p);
        broadcast({type:'playerRespawn',id,x:p.x,y:p.y,hp:p.hp,maxHp:p.maxHp,score:p.score,level:p.level});
      }
      else if(msg.type==='upgrade'){
        if(p.statPoints<=0)return;
        const v=['healthRegen','maxHealth','bodyDamage','bulletSpeed','bulletPen','bulletDamage','reload','movementSpeed'];
        if(v.includes(msg.stat)&&p.stats[msg.stat]<7){p.stats[msg.stat]++;p.statPoints--;applyStats(p);send(ws,{type:'statsUpdated',stats:p.stats,statPoints:p.statPoints,maxHp:p.maxHp});}
      }
      else if(msg.type==='selectTank'){
        if(typeof msg.tankType==='number'&&msg.tankType>=0&&msg.tankType<TANKS.length&&(p.level>=msg.tankType||p.isOwner)){
          p.tankType=msg.tankType;applyStats(p);broadcast({type:'tankChanged',id,tankType:p.tankType});
        }
      }
      else if(msg.type==='chat'){
        const text=(msg.text||'').substring(0,120).trim();if(!text)return;
        const entry={name:p.name,text,isOwner:p.isOwner,ts:Date.now()};
        chatHistory.unshift(entry);if(chatHistory.length>60)chatHistory.pop();
        broadcast({type:'chat',entry});
      }
      else if(msg.type==='mod'){
        if(!p.isOwner||p.sessionToken!==ownerToken){send(ws,{type:'modError',msg:'Access denied'});return;}
        handleMod(p,ws,msg);
      }
    }catch(e){console.error('MSG err:',e.message);}
  });

  ws.on('close',()=>{
    const q=players[id];
    if(q){if(q.isOwner)ownerConnected=false;releaseName(q.name);logEv(`- ${id} (${q.name}) left`);}
    delete players[id];broadcast({type:'playerLeave',id});
  });
});

// ══════════════════════════════════════════════════════════
//  MOD HANDLER
// ══════════════════════════════════════════════════════════
function handleMod(p,ws,msg){
  const act=msg.action,tid=msg.targetId,tgt=players[tid];
  switch(act){
    case 'getPlayerList': send(ws,{type:'modPlayerList',players:Object.values(players).map(pl=>({id:pl.id,name:pl.name,score:pl.score,kills:pl.kills,deaths:pl.deaths||0,alive:pl.alive,level:pl.level,isBot:pl.isBot||false,tankType:pl.tankType,isOwner:pl.isOwner}))}); break;
    case 'getLog': send(ws,{type:'modLog',log:serverLog}); break;
    case 'getStats': send(ws,{type:'modStats',stats:{players:Object.keys(players).length,bots:Object.values(players).filter(q=>q.isBot).length,humans:Object.values(players).filter(q=>!q.isBot).length,bosses:bosses.length,shapes:shapes.length,food:food.length,bullets:Object.keys(bullets).length,uptime:Math.floor(process.uptime()),event:activeEvent?activeEvent.name:'None'}}); break;
    case 'spawnBoss': if(bosses.length<MAX_BOSSES){spawnBoss();send(ws,{type:'modOk',msg:'Boss spawned!'});}else send(ws,{type:'modError',msg:'Max bosses reached'}); break;
    case 'killBosses': bosses.forEach(b=>broadcast({type:'bossDestroy',id:b.id,x:b.x,y:b.y}));bosses=[];broadcast({type:'announce',msg:'👑 All bosses cleared',color:'#ffdd44'});logEv('Admin cleared bosses'); break;
    case 'clearShapes': shapes.forEach(s=>broadcast({type:'shapeDestroy',id:s.id,scorer:null,x:s.x,y:s.y}));shapes=[];logEv('Admin cleared shapes'); break;
    case 'refillShapes': spawnShapes();broadcast({type:'shapeSpawn',shapes});logEv('Admin filled shapes'); break;
    case 'clearBullets': for(const b in bullets){broadcast({type:'bulletRemove',id:b});}bullets={}; break;
    case 'clearAllFood': food.forEach(f=>broadcast({type:'foodEat',id:f.id}));food=[];logEv('Admin cleared food'); break;
    case 'announce': broadcast({type:'announce',msg:msg.text||'',color:msg.color||'#ffdd44'});logEv(`Announce: ${msg.text}`); break;
    case 'chatMsg': const ce={name:'[ADMIN]',text:msg.text||'',isOwner:true,ts:Date.now()};chatHistory.unshift(ce);broadcast({type:'chat',entry:ce}); break;
    // Events
    case 'startEvent': startEvent(msg.eventType); break;
    case 'endEvent': endEvent(); break;
    // Bots
    case 'spawnBot': mkBot(msg.botName,msg.difficulty);send(ws,{type:'modOk',msg:`Bot "${msg.botName||'Bot'}" spawned!`}); break;
    case 'spawnBots': for(let i=0;i<Math.min(msg.count||3,15);i++)mkBot((msg.botName||'Bot')+(msg.count>1?'_'+(i+1):''),msg.difficulty);send(ws,{type:'modOk',msg:`${Math.min(msg.count||3,15)} bots spawned!`}); break;
    case 'removeAllBots': for(const pid in players){if(players[pid].isBot){releaseName(players[pid].name);broadcast({type:'playerLeave',id:pid});delete players[pid];}}send(ws,{type:'modOk',msg:'All bots removed!'}); break;
    case 'setBotDiff': for(const pid in players){if(players[pid].isBot){players[pid].diffName=msg.difficulty||'medium';players[pid].speed=(DIFF[msg.difficulty]||DIFF.medium).spd;}}send(ws,{type:'modOk',msg:`All bots set to ${msg.difficulty}`}); break;
    // Owner self
    case 'godMode': p.invincible=999999;p.hp=p.maxHp=999999;p.score=Math.max(p.score,100000);p.level=getLevel(p.score);p.statPoints=56;applyStats(p);send(ws,{type:'statsUpdated',stats:p.stats,statPoints:p.statPoints,maxHp:p.maxHp});send(ws,{type:'modOk',msg:'God Mode ON!'});logEv('Admin: God Mode'); break;
    case 'maxStats': Object.keys(p.stats).forEach(s=>p.stats[s]=7);p.statPoints=0;applyStats(p);send(ws,{type:'statsUpdated',stats:p.stats,statPoints:0,maxHp:p.maxHp});send(ws,{type:'modOk',msg:'All stats maxed!'}); break;
    case 'allTanks': p.level=16;send(ws,{type:'modOk',msg:'All tanks unlocked!'}); break;
    case 'ownerRainbow': p.rainbow=!p.rainbow;broadcast({type:'playerRainbow',id:p.id,rainbow:p.rainbow}); break;
    case 'tpCenter': p.x=WORLD_W/2;p.y=WORLD_H/2; break;
    case 'addScore': p.score+=msg.amount||10000;upgradeTank(p); break;
    case 'setScore': p.score=Math.max(0,msg.amount||0);p.level=getLevel(p.score);applyStats(p); break;
    // Target
    default:
      if(!tgt){send(ws,{type:'modError',msg:'Player not found'});return;}
      switch(act){
        case 'kick': tgt.ws&&tgt.ws.close();logEv(`Kicked ${tgt.name}`); break;
        case 'kill': tgt.hp=0;tgt.alive=false;tgt.deaths=(tgt.deaths||0)+1;broadcast({type:'playerDie',id:tid,killer:p.id,killerName:'[Admin]'});logEv(`Admin killed ${tgt.name}`); break;
        case 'freeze': tgt.frozen=!tgt.frozen;tgt.freezeTimer=tgt.frozen?600:0;broadcast({type:'playerFrozen',id:tid,frozen:tgt.frozen}); break;
        case 'tp': tgt.x=p.x+rand(-80,80);tgt.y=p.y+rand(-80,80); break;
        case 'tpMeTo': p.x=tgt.x+rand(-80,80);p.y=tgt.y+rand(-80,80); break;
        case 'giveScore': tgt.score+=msg.amount||5000;upgradeTank(tgt);tgt.ws&&send(tgt.ws,{type:'announce',msg:`+${msg.amount||5000} score from Admin!`,color:'#ffdd44'}); break;
        case 'setScore': tgt.score=Math.max(0,msg.amount||0);tgt.level=getLevel(tgt.score);applyStats(tgt); break;
        case 'heal': tgt.hp=tgt.maxHp;tgt.alive=true;broadcast({type:'playerHit',id:tid,hp:tgt.hp}); break;
        case 'rainbow': tgt.rainbow=!tgt.rainbow;broadcast({type:'playerRainbow',id:tid,rainbow:tgt.rainbow}); break;
        case 'setSize': tgt.size=clamp(msg.size||1,.3,5);tgt.maxHp=calcHp(tgt);tgt.hp=tgt.maxHp;applyStats(tgt);broadcast({type:'playerSize',id:tid,size:tgt.size}); break;
        case 'setTank': if(msg.tankType>=0&&msg.tankType<TANKS.length){tgt.tankType=msg.tankType;applyStats(tgt);broadcast({type:'tankChanged',id:tid,tankType:tgt.tankType});} break;
        case 'giveGod': tgt.invincible=99999;tgt.ws&&send(tgt.ws,{type:'announce',msg:'👑 You got God Mode!',color:'#ffdd44'}); break;
        case 'sendMsg': tgt.ws&&send(tgt.ws,{type:'announce',msg:msg.text||'',color:msg.color||'#ffdd44'}); break;
        case 'revealPos': send(ws,{type:'modOk',msg:`${tgt.name}: (${Math.round(tgt.x)},${Math.round(tgt.y)}) score:${tgt.score}`}); break;
        case 'maxTarget': Object.keys(tgt.stats).forEach(s=>tgt.stats[s]=7);tgt.statPoints=0;applyStats(tgt);tgt.ws&&send(tgt.ws,{type:'statsUpdated',stats:tgt.stats,statPoints:0,maxHp:tgt.maxHp});break;
        case 'swapPos': if(tgt){const ox=p.x,oy=p.y;p.x=tgt.x;p.y=tgt.y;tgt.x=ox;tgt.y=oy;} break;
      }
  }
}

// ══════════════════════════════════════════════════════════
//  BOSS
// ══════════════════════════════════════════════════════════
function spawnBoss(){
  if(bosses.length>=MAX_BOSSES)return;
  const side=randInt(0,3);
  let x=rand(300,WORLD_W-300),y=rand(300,WORLD_H-300);
  if(side===0)x=130;else if(side===1)x=WORLD_W-130;else if(side===2)y=130;else y=WORLD_H-130;
  bosses.push({id:nextId++,x,y,hp:3500,maxHp:3500,score:7000,angle:0,rotSpeed:.01,targetId:null,fireCooldown:0,speed:.95,phase:0,pat:0});
  broadcast({type:'bossSpawn',bosses:bosses.map(b=>({id:b.id,x:b.x,y:b.y,hp:b.hp,maxHp:b.maxHp,angle:b.angle}))});
  broadcast({type:'announce',msg:'⚠️ A BOSS HAS APPEARED!',color:'#ff4444'});
  logEv('Boss spawned');
}
function tickBoss(boss){
  boss.angle+=boss.rotSpeed;
  boss.phase=boss.hp<boss.maxHp*.25?2:boss.hp<boss.maxHp*.6?1:0;
  const spd=boss.speed*[1,1.5,2.4][boss.phase];
  const chaos=activeEvent?.type==='chaos';

  let nd=Infinity,ni=null;
  for(const id in players){const q=players[id];if(!q.alive||q.isBot)continue;const d=dist(boss.x,boss.y,q.x,q.y);if(d<nd){nd=d;ni=id;}}
  boss.targetId=ni;
  if(ni&&nd<900){const t=players[ni],a=ang(boss.x,boss.y,t.x,t.y);boss.x=clamp(boss.x+Math.cos(a)*spd,90,WORLD_W-90);boss.y=clamp(boss.y+Math.sin(a)*spd,90,WORLD_H-90);}

  if(--boss.fireCooldown<=0&&ni){
    const fi=chaos?[15,8,4][boss.phase]:[32,20,9][boss.phase];
    boss.fireCooldown=fi;
    const t=players[ni],shots=chaos?[8,12,16][boss.phase]:[5,7,10][boss.phase];
    const pat=boss.pat%5;boss.pat++;
    for(let i=0;i<shots;i++){
      let a;
      if(pat===0)a=ang(boss.x,boss.y,t.x,t.y)+(i-shots/2+.5)*.28;
      else if(pat===1)a=(Math.PI*2/shots)*i+boss.angle;
      else if(pat===2)a=ang(boss.x,boss.y,t.x,t.y)+(Math.random()-.5)*.7;
      else if(pat===3)a=(Math.PI*2/shots)*i+boss.angle*1.8;
      else a=ang(boss.x,boss.y,t.x,t.y)+(i%2===0?1:-1)*(i*.15);
      const bid='bx'+nextId++;
      bullets[bid]={id:bid,owner:'boss_'+boss.id,x:boss.x+Math.cos(a)*66,y:boss.y+Math.sin(a)*66,vx:Math.cos(a)*(chaos?10:8),vy:Math.sin(a)*(chaos?10:8),r:11,damage:chaos?45:30+boss.phase*14,pen:1,life:135,isBoss:true};
    }
  }
  for(const pid in players){
    const q=players[pid];if(!q.alive||q.invincible>0||q.shieldActive||q.ghost)continue;
    if(cc(boss.x,boss.y,62,q.x,q.y,20*(q.size||1))){
      q.hp-=7;if(q.hp<=0){q.hp=0;q.alive=false;q.deaths=(q.deaths||0)+1;broadcast({type:'playerDie',id:pid,killer:'boss',killerName:'👹 Boss'});}
      broadcast({type:'playerHit',id:pid,hp:q.hp});
    }
  }
}

// ══════════════════════════════════════════════════════════
//  GAME LOOP
// ══════════════════════════════════════════════════════════
let frameCount=0,bossTimer=0;

setInterval(()=>{
  frameCount++;bossTimer++;eventTimer++;

  // Event check
  if(activeEvent&&frameCount>=activeEvent.endFrame) endEvent();
  if(!activeEvent&&eventTimer>=EVENT_INTERVAL&&Object.keys(players).filter(id=>!players[id].isBot).length>0){eventTimer=0;startEvent();}

  // Boss
  if(bossTimer>=60*180&&bosses.length===0&&Object.keys(players).length>0){bossTimer=0;spawnBoss();}
  for(const b of bosses)tickBoss(b);

  // Bots
  for(const id in players){if(players[id].isBot)tickBot(players[id]);}

  // Crashers move on their own
  for(const s of shapes){
    s.angle+=s.rotSpeed;
    s.x=clamp(s.x+s.vx,60,WORLD_W-60);s.y=clamp(s.y+s.vy,60,WORLD_H-60);
    s.vx*=0.98;s.vy*=0.98;
    if(s.type==='crasher'){
      // Crashers home in on nearest player
      let nd=Infinity,np=null;
      for(const id in players){const q=players[id];if(!q.alive)continue;const d=dist(s.x,s.y,q.x,q.y);if(d<nd){nd=d;np=q;}}
      if(np&&nd<400){const a=ang(s.x,s.y,np.x,np.y);s.vx+=Math.cos(a)*.12;s.vy+=Math.sin(a)*.12;const spd=Math.sqrt(s.vx**2+s.vy**2);if(spd>2){s.vx=s.vx/spd*2;s.vy=s.vy/spd*2;}}
    }
  }

  // Powerup timer
  for(let i=powerups.length-1;i>=0;i--){if(--powerups[i].life<=0){broadcast({type:'powerupRemove',id:powerups[i].id});powerups.splice(i,1);}}

  // Players
  for(const id in players){
    const p=players[id];if(!p.alive||p.isBot)continue;
    if(p.invincible>0)p.invincible--;
    if(p.shieldActive&&--p.shieldTimer<=0){p.shieldActive=false;broadcast({type:'shieldOff',id});}
    p.regenTimer++;
    const rr=Math.max(40,200-p.stats.healthRegen*22);
    if(p.regenTimer>=rr&&p.hp<p.maxHp){p.hp=Math.min(p.maxHp,p.hp+1+Math.floor(p.stats.healthRegen/2));p.regenTimer=0;}
    if(p.frozen&&--p.freezeTimer<=0){p.frozen=false;broadcast({type:'playerFrozen',id,frozen:false});}

    const inp=p.inputs;
    let dx=(inp.right?1:0)-(inp.left?1:0),dy=(inp.down?1:0)-(inp.up?1:0);
    if(dx&&dy){dx*=.707;dy*=.707;}
    const spd=activeEvent?.type==='speedrun'?p.speed*1.8:p.speed;
    if(!p.frozen){p.x=clamp(p.x+dx*spd,22,WORLD_W-22);p.y=clamp(p.y+dy*spd,22,WORLD_H-22);}

    if(p.magnetActive){for(const f of food){const d=dist(p.x,p.y,f.x,f.y);if(d<240&&d>5){const a=ang(f.x,f.y,p.x,p.y);f.x+=Math.cos(a)*3.5;f.y+=Math.sin(a)*3.5;}}}

    if(--p.fireCooldown<=0&&inp.fire&&!p.frozen){
      const cfg=TANKS[p.tankType]||TANKS[0];p.fireCooldown=p.fireRate;
      for(const barrel of cfg.B){
        const sp=cfg.sp?(Math.random()-.5)*cfg.sp*2:0,ba=p.angle+(barrel.a||0)+sp;
        const bid='b'+nextId++;
        bullets[bid]={id:bid,owner:id,x:p.x+Math.cos(ba)*(barrel.l||30),y:p.y+Math.sin(ba)*(barrel.l||30),vx:Math.cos(ba)*p.bulletSpeed,vy:Math.sin(ba)*p.bulletSpeed,r:(barrel.w||12)/2+2,damage:p.bulletDamage,pen:1+Math.floor(p.stats.bulletPen/2),life:p.bulletLife};
      }
    }

    for(let i=food.length-1;i>=0;i--){
      if(cc(p.x,p.y,22,food[i].x,food[i].y,food[i].r)){
        let sc=food[i].score;
        if(activeEvent?.type==='doubleXP')sc*=2;
        if(p.doubleScore)sc*=2;
        p.score+=sc;upgradeTank(p);broadcast({type:'foodEat',id:food[i].id});food.splice(i,1);
      }
    }

    for(let i=powerups.length-1;i>=0;i--){
      const pu=powerups[i];
      if(!cc(p.x,p.y,24,pu.x,pu.y,18))continue;
      if(pu.type==='health')p.hp=Math.min(p.maxHp,p.hp+p.maxHp*.55);
      else if(pu.type==='speed'){const b=p.speed;p.speed*=1.8;setTimeout(()=>{if(players[id])p.speed=3+p.stats.movementSpeed*.45;},5000);}
      else if(pu.type==='damage'){p.bulletDamage*=2.5;setTimeout(()=>{if(players[id])applyStats(p);},5000);}
      else if(pu.type==='shield'){p.shieldActive=true;p.shieldTimer=480;broadcast({type:'shieldOn',id});}
      else if(pu.type==='freeze'){for(const pid in players){if(pid===id)continue;const q=players[pid];if(q.alive&&dist(p.x,p.y,q.x,q.y)<340&&!q.isOwner){q.frozen=true;q.freezeTimer=220;broadcast({type:'playerFrozen',id:pid,frozen:true});}}}
      else if(pu.type==='magnet'){p.magnetActive=true;setTimeout(()=>{if(players[id])p.magnetActive=false;},8000);}
      else if(pu.type==='ghost'){p.ghost=true;p.invincible=360;broadcast({type:'playerGhost',id,ghost:true});setTimeout(()=>{if(players[id]){p.ghost=false;p.invincible=0;broadcast({type:'playerGhost',id,ghost:false});}},6000);}
      else if(pu.type==='nuke'){
        const radius=380;
        for(const pid in players){if(pid===id)continue;const q=players[pid];if(q.alive&&dist(p.x,p.y,q.x,q.y)<radius&&!q.isOwner&&!q.shieldActive){q.hp=Math.max(1,q.hp-q.maxHp*.75);broadcast({type:'playerHit',id:pid,hp:q.hp});}}
        broadcast({type:'nuke',x:p.x,y:p.y,r:radius});
      }
      else if(pu.type==='doubleScore'){p.doubleScore=true;setTimeout(()=>{if(players[id])p.doubleScore=false;},10000);send(ws,{type:'announce',msg:'⭐ Double Score for 10s!',color:'#ffdd44'});}
      else if(pu.type==='invincible'){p.invincible=600;broadcast({type:'announce',msg:`${p.name} is invincible!`,color:'#88ffcc'});}
      broadcast({type:'powerupCollect',id:pu.id,player:id,puType:pu.type});
      powerups.splice(i,1);
    }
  }

  // Bullets
  for(const bid in bullets){
    const b=bullets[bid];b.x+=b.vx;b.y+=b.vy;
    if(--b.life<=0||b.x<0||b.x>WORLD_W||b.y<0||b.y>WORLD_H){delete bullets[bid];broadcast({type:'bulletRemove',id:bid});continue;}
    let hit=false;
    // vs shapes
    for(let i=shapes.length-1;i>=0;i--){
      const s=shapes[i];
      const sr={triangle:22,square:27,pentagon:37,hexagon:32,alpha:72,crasher:16}[s.type]||27;
      if(cc(b.x,b.y,b.r,s.x,s.y,sr)){
        const a=ang(b.x,b.y,s.x,s.y);s.vx+=Math.cos(a)*1.5;s.vy+=Math.sin(a)*1.5;
        s.hp-=b.damage;
        if(s.hp<=0){
          const own=players[b.owner];
          if(own&&own.alive){let sc=s.score;if(activeEvent?.type==='doubleXP')sc*=2;if(own.doubleScore)sc*=2;own.score+=sc;upgradeTank(own);}
          broadcast({type:'shapeDestroy',id:s.id,scorer:b.owner,x:s.x,y:s.y});shapes.splice(i,1);
        } else broadcast({type:'shapeHit',id:s.id,hp:s.hp});
        if(--b.pen<=0){hit=true;break;}
      }
    }
    if(hit){delete bullets[bid];broadcast({type:'bulletRemove',id:bid});continue;}
    // vs bosses
    if(!b.isBoss){
      for(let i=bosses.length-1;i>=0;i--){
        if(cc(b.x,b.y,b.r,bosses[i].x,bosses[i].y,63)){
          bosses[i].hp-=b.damage;broadcast({type:'bossHit',id:bosses[i].id,hp:bosses[i].hp,maxHp:bosses[i].maxHp});
          if(bosses[i].hp<=0){
            for(const pid in players){const q=players[pid];if(q.alive&&dist(q.x,q.y,bosses[i].x,bosses[i].y)<900){q.score+=bosses[i].score;upgradeTank(q);}}
            broadcast({type:'bossDestroy',id:bosses[i].id,x:bosses[i].x,y:bosses[i].y});
            broadcast({type:'announce',msg:'🏆 BOSS DEFEATED! +7000 XP!',color:'#44ff88'});
            logEv(`Boss killed by ${players[b.owner]?.name||'?'}`);
            bosses.splice(i,1);
          }
          hit=true;break;
        }
      }
    }
    if(hit){delete bullets[bid];broadcast({type:'bulletRemove',id:bid});continue;}
    // vs players
    for(const pid in players){
      if(pid===b.owner)continue;
      const q=players[pid];if(!q.alive||q.invincible>0||q.ghost)continue;
      if(cc(b.x,b.y,b.r,q.x,q.y,20*(q.size||1))){
        if(q.shieldActive){hit=true;broadcast({type:'shieldBlock',id:pid});break;}
        q.hp-=b.damage;
        if(q.hp<=0){
          q.hp=0;q.alive=false;q.deaths=(q.deaths||0)+1;
          const killer=players[b.owner];
          if(killer&&killer.alive){let sc=Math.floor(q.score*.15)+600;if(activeEvent?.type==='doubleXP')sc*=2;killer.score+=sc;killer.kills++;upgradeTank(killer);}
          broadcast({type:'playerDie',id:pid,killer:b.owner,killerName:killer?.name||'?'});
          logEv(`${killer?.name||'?'} killed ${q.name}`);
        }
        hit=true;broadcast({type:'playerHit',id:pid,hp:q.hp});break;
      }
    }
    if(hit){delete bullets[bid];broadcast({type:'bulletRemove',id:bid});}
  }

  // World regen
  if(frameCount%60===0){
    const nf=[];
    const cap=activeEvent?.type==='feast'?MAX_FOOD+100:MAX_FOOD;
    while(food.length+nf.length<cap){const f={id:nextId++,x:rand(60,WORLD_W-60),y:rand(60,WORLD_H-60),r:10,score:10};nf.push(f);food.push(f);}
    if(nf.length)broadcast({type:'foodSpawn',food:nf});
    spawnShapes();
    const ns=shapes.slice(-5);if(ns.length)broadcast({type:'shapeSpawn',shapes:ns});
    const np=[];
    while(powerups.length+np.length<MAX_POWERUPS&&Math.random()<.5){const types=['health','speed','damage','shield','freeze','magnet','ghost','nuke','doubleScore','invincible'];const pu={id:nextId++,x:rand(120,WORLD_W-120),y:rand(120,WORLD_H-120),type:types[randInt(0,types.length-1)],life:1100};np.push(pu);powerups.push(pu);}
    if(np.length)broadcast({type:'powerupSpawn',powerups:np.map(p=>({id:p.id,x:p.x,y:p.y,type:p.type}))});
  }

  broadcast({
    type:'state',
    players:Object.values(players).map(ser),
    bullets:Object.values(bullets).map(b=>({id:b.id,x:b.x,y:b.y,r:b.r,isBoss:!!b.isBoss})),
    shapes:shapes.map(s=>({id:s.id,x:s.x,y:s.y,type:s.type,hp:s.hp,maxHp:s.maxHp,angle:s.angle})),
    bosses:bosses.map(b=>({id:b.id,x:b.x,y:b.y,hp:b.hp,maxHp:b.maxHp,angle:b.angle,phase:b.phase})),
    activeEvent:activeEvent?{type:activeEvent.type,name:activeEvent.name,color:activeEvent.color,remaining:activeEvent.endFrame-frameCount}:null,
  });
},1000/TICK_RATE);

// ── IMPORTANT: Listen on 0.0.0.0 for Railway ───────────
const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => {
  console.log(`\n🎮 ═══════════════════════════════════════`);
  console.log(`🎮  DIEP.IO Clone v5.0`);
  console.log(`🎮  Port: ${PORT}  (0.0.0.0)`);
  console.log(`🎮  Owner: "${OWNER_NAME}"  Pass: "${ADMIN_PASS}"`);
  console.log(`🎮 ═══════════════════════════════════════\n`);
});
