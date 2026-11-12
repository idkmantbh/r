require('dotenv').config();

const { Client, GatewayIntentBits, EmbedBuilder, WebhookClient, AttachmentBuilder } = require('discord.js');
const WebSocket = require('ws');
const http = require('http');
const fs   = require('fs');
const path = require('path');
const crypto = require('crypto');

const DISCORD_TOKEN = process.env.DISCORD_TOKEN;
const CHANNEL_ID    = process.env.CHANNEL_ID;
const WEBHOOK_URL   = process.env.WEBHOOK_URL;

if (!DISCORD_TOKEN || DISCORD_TOKEN === 'YOUR_BOT_TOKEN_HERE') {
    console.error('[RemoteBridge] ERROR: Set DISCORD_TOKEN in your .env file!');
    process.exit(1);
}
if (!CHANNEL_ID || CHANNEL_ID === 'YOUR_CHANNEL_ID_HERE') {
    console.error('[RemoteBridge] ERROR: Set CHANNEL_ID in your .env file!');
    process.exit(1);
}

const discord = new Client({
    intents: [
        GatewayIntentBits.Guilds,
        GatewayIntentBits.GuildMessages,
        GatewayIntentBits.MessageContent
    ]
});

const webhook = WEBHOOK_URL && WEBHOOK_URL !== 'YOUR_WEBHOOK_URL_HERE'
    ? new WebhookClient({ url: WEBHOOK_URL })
    : null;

// ── Instance tracking ─────────────────────────────────────────────────────────
const instances = new Map();
const pendingKicks = new Map(); // channelId -> instanceId
const pendingJoins = new Map();  // channelId -> instanceId
const serverHistory = new Map(); // username -> Set of IPs
const socketToId = new Map(); // ws -> that connection's CURRENT instance id (can change on renumber, below)
const lastIdForUsername = new Map(); // username -> the instance # it last used, so a reconnect slides back into it
let mcChannel = null;

function getNextId() {
    let id = 1;
    while (instances.has(id)) id++;
    return id;
}

function getLabel(id) {
    const inst = instances.get(id);
    const name = inst && inst.username ? inst.username : '...';
    return `[#${id} | ${name}]`;
}

// ── Mod auto-update ────────────────────────────────────────────────────────────
// To push a new build: drop the jar in mods/ as mods/remotebridge-latest.jar
// (always that exact name — just overwrite it each time) and push. No version
// number or config to edit: the bridge hashes the file itself, and every
// connected bot compares that hash to its own jar on connect, every 10
// minutes after that, and whenever you run !update. On a mismatch it
// downloads the new jar into its own mods folder, ready for the next launch.

const MODS_DIR = path.join(__dirname, 'mods');
const JAR_PATH = path.join(MODS_DIR, 'remotebridge-latest.jar');

// process.env.BASE_URL is an optional manual override; Render sets
// RENDER_EXTERNAL_URL automatically, so most setups need neither.
const BASE_URL = (process.env.BASE_URL || process.env.RENDER_EXTERNAL_URL || '').replace(/\/$/, '');

function getLatestMod() {
    try {
        const stat = fs.statSync(JAR_PATH);
        const hash = crypto.createHash('sha256').update(fs.readFileSync(JAR_PATH)).digest('hex');
        return { hash, shortHash: hash.slice(0, 8), size: stat.size };
    } catch (e) {
        return null; // no mods/remotebridge-latest.jar yet — auto-update is just off
    }
}

function maybeSendUpdate(id, reportedHash) {
    const latest = getLatestMod();
    if (!latest) return false;
    if (!BASE_URL) {
        console.warn('[RemoteBridge] mods/remotebridge-latest.jar present but no public URL could be determined (set BASE_URL).');
        return false;
    }
    if (reportedHash === latest.hash) return false;
    sendToMinecraft({
        type: 'update',
        version: latest.shortHash,
        url: `${BASE_URL}/mods/remotebridge-latest.jar?v=${latest.shortHash}`
    }, id);
    return true;
}

// ── Live watch ─────────────────────────────────────────────────────────────────
// instanceId -> Set of browser WebSocket connections watching that instance.
// The Minecraft client only captures frames while this set is non-empty —
// opening the page starts it, closing the last tab stops it, automatically.
const watchers = new Map();

// Per-link secret. !watch makes a fresh random key for the instance; the page
// and the viewer WebSocket both must present it. Expires after an hour, is
// replaced by the next !watch, and dies when the bot disconnects.
const watchKeys = new Map(); // instanceId -> { key, expires }
const WATCH_KEY_TTL_MS = 60 * 60 * 1000;

function newWatchKey(id) {
    const key = crypto.randomBytes(12).toString('hex');
    watchKeys.set(id, { key, expires: Date.now() + WATCH_KEY_TTL_MS });
    return key;
}

function checkWatchKey(id, key) {
    if (checkDashboardKey(key)) return true; // the dashboard key opens any instance's page too
    const e = watchKeys.get(id);
    if (!e || !key || Date.now() > e.expires) return false;
    const a = Buffer.from(String(key)), b = Buffer.from(e.key);
    return a.length === b.length && crypto.timingSafeEqual(a, b);
}

// ── Dashboard: one page, every connected bot ──────────────────────────────────
// Single shared key (not per-instance) made by !dashboard. Also valid on any
// /watch/<id> link, so "open full view" from a tile can reuse it.
let dashboardKeyStore = null; // { key, expires }
const dashboardViewers = new Set(); // ws connections on /dashboard-ws

function newDashboardKey() {
    const key = crypto.randomBytes(12).toString('hex');
    dashboardKeyStore = { key, expires: Date.now() + WATCH_KEY_TTL_MS };
    return key;
}

function checkDashboardKey(key) {
    if (!dashboardKeyStore || !key || Date.now() > dashboardKeyStore.expires) return false;
    const a = Buffer.from(String(key)), b = Buffer.from(dashboardKeyStore.key);
    return a.length === b.length && crypto.timingSafeEqual(a, b);
}

function broadcastDashboard(obj) {
    if (dashboardViewers.size === 0) return;
    const msg = JSON.stringify(obj);
    for (const v of dashboardViewers) {
        if (v.readyState === WebSocket.OPEN) v.send(msg);
    }
}

// Starts/stops a bot's capture based on everyone who currently wants its frames
// (its own /watch page viewers, plus the dashboard if it's open) — only sends
// watch_start/watch_stop to the mod when that combined answer actually changes.
function syncWatch(id) {
    const inst = instances.get(id);
    if (!inst) return;
    const want = (watchers.get(id)?.size || 0) > 0 || dashboardViewers.size > 0;
    if (want === inst.watching) return;
    inst.watching = want;
    sendToMinecraft({ type: want ? 'watch_start' : 'watch_stop' }, id);
}

// Pushes a log entry (command result, status text, a screenshot, etc.) to every
// browser currently watching this instance's page, so the command panel on
// /watch/<id> can show results without needing Discord open.
function notifyWatchers(id, entry) {
    const set = watchers.get(id);
    if (!set || set.size === 0) return;
    const msg = JSON.stringify({ type: 'log', ts: Date.now(), ...entry });
    for (const v of set) {
        if (v.readyState === WebSocket.OPEN) v.send(msg);
    }
}

// Moves a connection from one instance id to another, carrying over everything
// keyed by that id (watchers, the watch-page key, the socket->id lookup). Used
// when a bot reconnects and its old number is free, so it slides back into the
// same slot instead of becoming a brand-new instance — otherwise every link,
// !control, and open dashboard tile was pointing at a bot that just vanished.
function renumber(fromId, toId) {
    const inst = instances.get(fromId);
    if (!inst || fromId === toId) return fromId;
    instances.delete(fromId);
    instances.set(toId, inst);
    socketToId.set(inst.socket, toId);
    const w = watchers.get(fromId);
    if (w) { watchers.delete(fromId); watchers.set(toId, w); }
    const k = watchKeys.get(fromId);
    if (k) { watchKeys.delete(fromId); watchKeys.set(toId, k); }
    console.log(`[RemoteBridge] Instance #${fromId} reconnected — sliding back into #${toId}.`);
    broadcastDashboard({ type: 'instance_disconnected', id: fromId });
    broadcastDashboard({ type: 'instance_connected', id: toId, username: inst.username, status: inst.lastStatus });
    syncWatch(toId);
    return toId;
}

function clamp01(v) {
    v = Number(v);
    return Number.isFinite(v) ? Math.min(1, Math.max(0, v)) : 0;
}

function watchPage(id) {
    return `<!doctype html>
<html><head><meta charset="utf-8"><title>RemoteBridge — Watching #${id}</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
  :root {
    --bg:#0b0b0d; --panel:#141416; --panel2:#1b1b1e; --border:#2a2a2e;
    --text:#e8e8ea; --muted:#8a8a90; --accent:#5b8cff; --accent-dim:#2a3a66;
    --green:#2ecc71; --red:#e2493d; --amber:#e2a53d;
  }
  * { box-sizing:border-box; }
  body {
    background:var(--bg); margin:0; min-height:100vh; color:var(--text);
    font:13px/1.45 ui-monospace, 'SF Mono', Menlo, Consolas, monospace;
  }
  #app { display:flex; flex-direction:column; height:100vh; }

  header {
    display:flex; align-items:center; justify-content:space-between; gap:12px;
    padding:10px 16px; background:var(--panel); border-bottom:1px solid var(--border);
    flex-wrap:wrap;
  }
  .title { display:flex; align-items:center; gap:8px; font-weight:600; letter-spacing:.2px; }
  .dot { width:9px; height:9px; border-radius:50%; background:var(--muted); flex:none; }
  .dot.live { background:var(--green); box-shadow:0 0 6px var(--green); }
  .dot.err { background:var(--red); box-shadow:0 0 6px var(--red); }
  #statusText { color:var(--muted); font-weight:400; }

  .streamctl { display:flex; align-items:center; gap:8px; flex-wrap:wrap; }
  button, select, input {
    font:inherit; color:var(--text); background:var(--panel2);
    border:1px solid var(--border); border-radius:7px; padding:6px 10px; cursor:pointer;
  }
  button:hover { background:#242428; }
  button:active { transform:translateY(1px); }
  select { cursor:pointer; }
  input { cursor:text; }
  input::placeholder { color:var(--muted); }
  #ctl.on, #look.on { background:var(--red); border-color:var(--red); color:#fff; }
  button.danger { border-color:#5a2420; color:#ff9b91; }
  button.danger:hover { background:#3a1a17; }
  button.primary { background:var(--accent-dim); border-color:var(--accent); color:#dce6ff; }
  button.primary:hover { background:#34437c; }

  main { flex:1; display:grid; grid-template-columns:1fr 360px; min-height:0; }
  .video {
    background:#000; display:flex; align-items:center; justify-content:center;
    overflow:hidden; position:relative;
  }
  .video img { max-width:100%; max-height:100%; image-rendering:pixelated; display:block; }
  .video .hint {
    position:absolute; bottom:10px; left:10px; color:#999; background:#000a;
    padding:4px 10px; border-radius:6px; font-size:11px; pointer-events:none;
  }

  aside.panel { background:var(--panel); border-left:1px solid var(--border); overflow-y:auto; padding:10px; }
  .section { background:var(--panel2); border:1px solid var(--border); border-radius:10px; padding:10px 12px; margin-bottom:10px; }
  .section h2 { margin:0 0 8px; font-size:11px; text-transform:uppercase; letter-spacing:.08em; color:var(--muted); font-weight:600; }
  .btnrow { display:flex; flex-wrap:wrap; gap:6px; }
  .btnrow button { flex:1 1 auto; white-space:nowrap; }
  .inline { display:flex; gap:6px; margin-top:6px; }
  .inline:first-of-type { margin-top:0; }
  .inline input { flex:1; min-width:0; }

  .log-section { display:flex; flex-direction:column; max-height:320px; }
  #log { overflow-y:auto; display:flex; flex-direction:column; gap:6px; }
  .logentry { border-left:2px solid var(--border); padding:4px 0 4px 8px; }
  .logentry .t { color:var(--muted); font-size:10px; }
  .logentry .m { white-space:pre-wrap; word-break:break-word; }
  .logentry img { max-width:100%; border-radius:6px; margin-top:4px; display:block; }
  #log:empty::after { content:"No activity yet — try a command above."; color:var(--muted); }

  @media (max-width: 860px) {
    main { grid-template-columns:1fr; grid-template-rows:45vh 1fr; }
    aside.panel { border-left:none; border-top:1px solid var(--border); }
  }
</style></head>
<body>
<div id="app">
  <header>
    <div class="title"><span id="dot" class="dot"></span><span>RemoteBridge <span id="statusText">connecting…</span></span></div>
    <div class="streamctl">
      <select id="fps" title="Stream speed (higher = smoother but uses more bandwidth)">
        <option value="5">5 fps</option><option value="10" selected>10 fps</option>
        <option value="15">15 fps</option><option value="20">20 fps</option>
      </select>
      <button id="look" title="In-game camera. Click the picture to capture the mouse; Esc releases it.">Mouse look: OFF</button>
      <button id="ctl">Control: OFF</button>
    </div>
  </header>
  <main>
    <div class="video">
      <img id="frame" alt="waiting for a frame…">
      <div class="hint">Turn Control ON to click &amp; type here</div>
    </div>
    <aside class="panel">
      <div class="section">
        <h2>Info</h2>
        <div class="btnrow">
          <button data-action="status">📊 Status</button>
          <button data-action="coords">📍 Coords</button>
          <button data-action="gamemode">🎮 Gamemode</button>
          <button data-action="players">👥 Players</button>
          <button data-action="mods">📦 Mods</button>
        </div>
      </div>

      <div class="section">
        <h2>Say &amp; run commands</h2>
        <div class="inline"><input id="sayInput" placeholder="chat message…"><button id="sayBtn" class="primary">💬 Say</button></div>
        <div class="inline"><input id="cmdInput" placeholder="command, e.g. /tp 0 100 0"><button id="cmdBtn" class="primary">⚙️ Run</button></div>
      </div>

      <div class="section">
        <h2>Screenshots &amp; GIF</h2>
        <div class="btnrow">
          <button data-action="screenshot">📸 Screenshot</button>
          <button data-action="inventory">🎒 Inventory</button>
        </div>
        <div class="inline">
          <input id="gifSecs" type="number" min="1" max="15" value="5" style="max-width:70px">
          <button id="gifBtn">🎬 Record GIF</button>
        </div>
      </div>

      <div class="section">
        <h2>Chat relay</h2>
        <div class="btnrow">
          <button data-action="chat_start">▶️ All</button>
          <button data-action="chat_stop">⏹️ All</button>
          <button data-action="chat_in_start">▶️ In</button>
          <button data-action="chat_in_stop">⏹️ In</button>
          <button data-action="chat_out_start">▶️ Out</button>
          <button data-action="chat_out_stop">⏹️ Out</button>
        </div>
      </div>

      <div class="section">
        <h2>Connection &amp; power</h2>
        <div class="inline"><input id="joinInput" placeholder="server IP…"><button id="joinBtn">🌐 Join</button></div>
        <div class="inline"><input id="kickInput" placeholder="disconnect message (optional)…"><button id="kickBtn">👢 Kick</button></div>
        <div class="btnrow" style="margin-top:6px">
          <button id="updateBtn">⬆️ Update mod</button>
          <button id="killBtn" class="danger">☠️ Kill game</button>
        </div>
      </div>

      <div class="section log-section">
        <h2>Log</h2>
        <div id="log"></div>
      </div>
    </aside>
  </main>
</div>
<script>
  const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
  const ws = new WebSocket(proto + '//' + location.host + '/watch-ws/${id}' + location.search);
  const img = document.getElementById('frame');
  const dot = document.getElementById('dot');
  const statusText = document.getElementById('statusText');
  const logEl = document.getElementById('log');

  const esc = (s) => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  function addLog(text, image) {
    const e = document.createElement('div');
    e.className = 'logentry';
    const time = new Date().toLocaleTimeString();
    e.innerHTML = '<div class="t">' + time + '</div><div class="m">' + esc(text) + '</div>' +
      (image ? '<img src="data:image/jpeg;base64,' + image + '">' : '');
    logEl.insertBefore(e, logEl.firstChild);
    while (logEl.children.length > 60) logEl.removeChild(logEl.lastChild);
  }

  ws.onopen = () => { dot.className = 'dot live'; statusText.textContent = 'live — instance #${id}'; };
  ws.onclose = () => { dot.className = 'dot'; statusText.textContent = 'disconnected'; };
  ws.onerror = () => { dot.className = 'dot err'; statusText.textContent = 'connection error'; };
  ws.onmessage = (ev) => {
    const msg = JSON.parse(ev.data);
    if (msg.type === 'watch_frame') img.src = 'data:image/jpeg;base64,' + msg.data;
    else if (msg.type === 'log') addLog(msg.text || '', msg.image);
  };

  const send = (o) => { if (ws.readyState === 1) ws.send(JSON.stringify(o)); };
  const sendAction = (action, extra) => send({ kind: 'action', action, ...(extra || {}) });

  // ── Command panel ──
  document.querySelectorAll('[data-action]').forEach(b => {
    b.onclick = () => { sendAction(b.dataset.action); b.blur(); };
  });
  const take = (inp) => { const v = inp.value; inp.value = ''; return v; };
  document.getElementById('sayBtn').onclick = () => { const v = take(document.getElementById('sayInput')); if (v) sendAction('say', { message: v }); };
  document.getElementById('cmdBtn').onclick = () => { const v = take(document.getElementById('cmdInput')); if (v) sendAction('cmd', { command: v }); };
  document.getElementById('joinBtn').onclick = () => { const v = take(document.getElementById('joinInput')); if (v) sendAction('join', { ip: v }); };
  document.getElementById('kickBtn').onclick = () => { const v = take(document.getElementById('kickInput')); sendAction('kick', { message: v }); };
  document.getElementById('gifBtn').onclick = () => sendAction('gif', { seconds: Number(document.getElementById('gifSecs').value) || 5 });
  document.getElementById('updateBtn').onclick = () => sendAction('update');
  document.getElementById('killBtn').onclick = () => { if (confirm('Close the game on this instance?')) sendAction('kill'); };
  ['sayInput', 'cmdInput', 'joinInput', 'kickInput'].forEach(id2 => {
    document.getElementById(id2).addEventListener('keydown', (e) => {
      if (e.key === 'Enter') document.getElementById(id2.replace('Input', 'Btn')).click();
    });
  });

  // ── Remote control (inputs are ignored by the game until !control on) ──
  let ctl = false;
  const btn = document.getElementById('ctl');
  const pos = (e) => {
    const r = img.getBoundingClientRect();
    return { x: (e.clientX - r.left) / r.width, y: (e.clientY - r.top) / r.height };
  };
  btn.onclick = () => {
    ctl = !ctl;
    btn.textContent = 'Control: ' + (ctl ? 'ON' : 'OFF');
    btn.classList.toggle('on', ctl);
    if (!ctl) send({ kind: 'releaseAll' });
    btn.blur();
  };
  img.draggable = false;

  // Mouse look: for in-game camera control. Uses the browser's pointer lock so the
  // mouse can turn the camera endlessly (relative movement, not screen position).
  let look = false, ax = 0, ay = 0;
  const lbtn = document.getElementById('look');
  lbtn.onclick = () => {
    look = !look;
    lbtn.textContent = 'Mouse look: ' + (look ? 'ON' : 'OFF');
    lbtn.classList.toggle('on', look);
    if (!look && document.pointerLockElement) document.exitPointerLock();
    lbtn.blur();
  };
  img.addEventListener('click', () => { if (ctl && look && !document.pointerLockElement) img.requestPointerLock(); });

  // Flush accumulated camera movement once per display frame (~60/s) for smooth turning.
  (function flushLook() {
    if (ctl && (ax || ay)) { send({ kind: 'look', dx: ax, dy: ay }); ax = 0; ay = 0; }
    requestAnimationFrame(flushLook);
  })();

  // Stream speed
  const fpsSel = document.getElementById('fps');
  const sendFps = () => send({ kind: 'fps', value: Number(fpsSel.value) });
  fpsSel.onchange = () => { sendFps(); fpsSel.blur(); };
  if (ws.readyState === 1) sendFps(); else ws.addEventListener('open', sendFps);

  let lastMove = 0;
  img.addEventListener('mousemove', (e) => {
    if (!ctl) return;
    if (document.pointerLockElement === img) { ax += e.movementX; ay += e.movementY; return; }
    const n = Date.now(); if (n - lastMove < 33) return; lastMove = n;
    send({ kind: 'move', ...pos(e) });
  });
  img.addEventListener('mousedown', (e) => { if (!ctl) return; e.preventDefault(); send({ kind: 'down', button: e.button, ...pos(e) }); });
  window.addEventListener('mouseup', (e) => { if (!ctl) return; send({ kind: 'up', button: e.button, ...pos(e) }); });
  img.addEventListener('contextmenu', (e) => { if (ctl) e.preventDefault(); });
  img.addEventListener('wheel', (e) => { if (!ctl) return; e.preventDefault(); send({ kind: 'wheel', amount: Math.sign(e.deltaY) }); }, { passive: false });
  window.addEventListener('keydown', (e) => {
    if (!ctl || e.repeat) return;
    if (['INPUT', 'SELECT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;
    e.preventDefault(); send({ kind: 'keydown', code: e.code });
  });
  window.addEventListener('keyup', (e) => {
    if (!ctl) return;
    if (['INPUT', 'SELECT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;
    e.preventDefault(); send({ kind: 'keyup', code: e.code });
  });
  window.addEventListener('blur', () => send({ kind: 'releaseAll' }));
</script>
</body></html>`;
}

function dashboardPage() {
    return `<!doctype html>
<html><head><meta charset="utf-8"><title>RemoteBridge — Dashboard</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
  body { background:#0b0b0d; margin:0; min-height:100vh; color:#eee; font:14px/1.4 monospace; padding:16px; box-sizing:border-box; }
  h1 { font-size:16px; margin:0 0 14px; color:#aaa; font-weight:normal; }
  #grid { display:grid; grid-template-columns:repeat(auto-fill, minmax(280px, 1fr)); gap:14px; }
  .tile { background:#161618; border:1px solid #2a2a2e; border-radius:8px; overflow:hidden; }
  .tile .thumb { position:relative; width:100%; aspect-ratio:16/9; background:#000; }
  .tile img { width:100%; height:100%; object-fit:contain; display:block; }
  .tile .dot { position:absolute; top:6px; left:6px; width:8px; height:8px; border-radius:50%; background:#2ecc71; box-shadow:0 0 4px #2ecc71; }
  .tile .dot.off { background:#555; box-shadow:none; }
  .tile .body { padding:8px 10px; }
  .tile .name { font-weight:bold; margin-bottom:4px; }
  .tile .stats { color:#999; font-size:12px; min-height:16px; }
  .tile .row { display:flex; gap:8px; margin-top:8px; }
  .tile button, .tile a.btn { flex:1; text-align:center; background:#2a2a2e; color:#eee; border:0; border-radius:5px; padding:5px 0; font:12px monospace; text-decoration:none; cursor:pointer; }
  .tile button:hover, .tile a.btn:hover { background:#38383d; }
  #empty { color:#777; }
</style></head>
<body>
<h1>RemoteBridge — live view of every connected bot (updates automatically)</h1>
<div id="grid"></div>
<div id="empty" style="display:none">No Minecraft instances connected right now. This page updates itself as they connect.</div>
<script>
  const KEY = new URLSearchParams(location.search).get('key') || '';
  const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
  const grid = document.getElementById('grid');
  const empty = document.getElementById('empty');
  const tiles = new Map(); // id -> { el, img, dot, name, stats }

  function updateEmpty() { empty.style.display = tiles.size === 0 ? 'block' : 'none'; }

  function makeTile(id) {
    const el = document.createElement('div');
    el.className = 'tile';
    el.innerHTML =
      '<div class="thumb"><div class="dot"></div><img alt="waiting for a frame…"></div>' +
      '<div class="body">' +
        '<div class="name">#' + id + '</div>' +
        '<div class="stats">—</div>' +
        '<div class="row">' +
          '<a class="btn" target="_blank">Open full view →</a>' +
          '<button>🔄 Refresh</button>' +
        '</div>' +
      '</div>';
    const img = el.querySelector('img');
    const dot = el.querySelector('.dot');
    const name = el.querySelector('.name');
    const stats = el.querySelector('.stats');
    const link = el.querySelector('a.btn');
    link.href = '/watch/' + id + '?key=' + encodeURIComponent(KEY);
    el.querySelector('button').onclick = () => { if (ws.readyState === 1) ws.send(JSON.stringify({ kind: 'refresh', id })); };
    grid.appendChild(el);
    const t = { el, img, dot, name, stats };
    tiles.set(id, t);
    updateEmpty();
    return t;
  }

  function removeTile(id) {
    const t = tiles.get(id);
    if (!t) return;
    t.el.remove();
    tiles.delete(id);
    updateEmpty();
  }

  function fmtStatus(s) {
    if (!s) return 'No status yet — press 🔄';
    if (!s.online) return (s.username || 'Offline') + ' · not in a world';
    return (s.username || '?') + ' · ' + (s.server || '?') + ' · ❤' + s.health + '/' + s.max_health +
      ' · ' + Math.round(s.x) + ' ' + Math.round(s.y) + ' ' + Math.round(s.z);
  }

  let ws;
  function connect() {
    ws = new WebSocket(proto + '//' + location.host + '/dashboard-ws?key=' + encodeURIComponent(KEY));
    ws.onmessage = (ev) => {
      const msg = JSON.parse(ev.data);
      if (msg.type === 'instance_connected') {
        const t = tiles.get(msg.id) || makeTile(msg.id);
        t.dot.classList.remove('off');
        if (msg.username) t.name.textContent = '#' + msg.id + ' — ' + msg.username;
        if (msg.status) t.stats.textContent = fmtStatus(msg.status);
      } else if (msg.type === 'instance_disconnected') {
        removeTile(msg.id);
      } else if (msg.type === 'watch_frame') {
        const t = tiles.get(msg.id);
        if (t) t.img.src = 'data:image/jpeg;base64,' + msg.data;
      } else if (msg.type === 'status') {
        const t = tiles.get(msg.id) || makeTile(msg.id);
        if (msg.status && msg.status.username) t.name.textContent = '#' + msg.id + ' — ' + msg.status.username;
        t.stats.textContent = fmtStatus(msg.status);
      }
    };
    ws.onclose = () => setTimeout(connect, 2000);
    ws.onerror = () => {};
  }
  connect();
</script>
</body></html>`;
}

// ── HTTP + WebSocket Server (shared port for Render) ─────────────────────────

const PORT = process.env.PORT || 8080;

const server = http.createServer((req, res) => {
    const url = req.url.split('?')[0];
    if (url === '/mods/remotebridge-latest.jar') {
        if (!fs.existsSync(JAR_PATH)) { res.writeHead(404); res.end('Not found'); return; }
        res.writeHead(200, { 'Content-Type': 'application/java-archive' });
        fs.createReadStream(JAR_PATH).pipe(res);
        return;
    }
    const watchMatch = url.match(/^\/watch\/(\d+)$/);
    if (watchMatch) {
        const wid = parseInt(watchMatch[1]);
        const key = new URL(req.url, 'http://x').searchParams.get('key');
        if (!checkWatchKey(wid, key)) {
            res.writeHead(403, { 'Content-Type': 'text/plain' });
            res.end('This link is invalid or has expired. Run !watch in Discord for a new one.');
            return;
        }
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end(watchPage(wid));
        return;
    }
    if (url === '/dashboard') {
        const key = new URL(req.url, 'http://x').searchParams.get('key');
        if (!checkDashboardKey(key)) {
            res.writeHead(403, { 'Content-Type': 'text/plain' });
            res.end('This link is invalid or has expired. Run !dashboard in Discord for a new one.');
            return;
        }
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end(dashboardPage());
        return;
    }
    res.writeHead(200);
    res.end('RemoteBridge OK');
});

// Two kinds of WebSocket client share this port: Minecraft bots (any other
// path) and browser viewers (/watch-ws/<id>) — routed manually since they
// need different handling.
const mcWss = new WebSocket.Server({ noServer: true });
const watchWss = new WebSocket.Server({ noServer: true });

const dashboardWss = new WebSocket.Server({ noServer: true });

server.on('upgrade', (req, socket, head) => {
    const url = req.url.split('?')[0];
    const watchMatch = url.match(/^\/watch-ws\/(\d+)$/);
    if (watchMatch) {
        const wid = parseInt(watchMatch[1]);
        const key = new URL(req.url, 'http://x').searchParams.get('key');
        if (!checkWatchKey(wid, key)) {
            socket.write('HTTP/1.1 403 Forbidden\r\n\r\n');
            socket.destroy();
            return;
        }
        watchWss.handleUpgrade(req, socket, head, (ws) => {
            watchWss.emit('connection', ws, parseInt(watchMatch[1]));
        });
    } else if (url === '/dashboard-ws') {
        const key = new URL(req.url, 'http://x').searchParams.get('key');
        if (!checkDashboardKey(key)) {
            socket.write('HTTP/1.1 403 Forbidden\r\n\r\n');
            socket.destroy();
            return;
        }
        dashboardWss.handleUpgrade(req, socket, head, (ws) => {
            dashboardWss.emit('connection', ws);
        });
    } else {
        mcWss.handleUpgrade(req, socket, head, (ws) => {
            mcWss.emit('connection', ws);
        });
    }
});

dashboardWss.on('connection', (ws) => {
    dashboardViewers.add(ws);

    // Snapshot of everything currently connected, then start their streams.
    for (const [id, inst] of instances.entries()) {
        ws.send(JSON.stringify({ type: 'instance_connected', id, username: inst.username, status: inst.lastStatus }));
        syncWatch(id);
    }

    ws.on('message', (data) => {
        let m;
        try { m = JSON.parse(data.toString()); } catch (e) { return; }
        if (m && m.kind === 'refresh' && Number.isInteger(m.id)) {
            sendToMinecraft({ type: 'status' }, m.id); // also posts the normal !status embed to Discord
        }
    });

    ws.on('close', () => {
        dashboardViewers.delete(ws);
        for (const id of instances.keys()) syncWatch(id);
    });
    ws.on('error', () => {});
});

mcWss.on('error', (err) => {
    console.error('[RemoteBridge] WebSocket server error:', err.message);
});

server.listen(PORT, () => {
    console.log('[RemoteBridge] WebSocket server running on port ' + PORT);
});

// Keeps idle connections alive. A bot that's just sitting there AFK with no
// commands going back and forth can look idle to a router, an ISP, or Render's
// own edge, which may silently drop it — neither side notices until the next
// write fails, and it shows up as a "random" disconnect. Regular traffic in
// either direction resets that idle timer, so this is cheap insurance.
const KEEPALIVE_MS = Number(process.env.RB_KEEPALIVE_MS) || 20_000;
setInterval(() => {
    for (const inst of instances.values()) {
        if (inst.socket.readyState === WebSocket.OPEN) {
            try { inst.socket.send(JSON.stringify({ type: 'ping' })); } catch (e) { /* ignore; close will fire on its own */ }
        }
    }
}, KEEPALIVE_MS);

mcWss.on('connection', (ws) => {
    const id = getNextId(); // provisional — status_response below may slide this back to an earlier number
    socketToId.set(ws, id);
    instances.set(id, { socket: ws, username: null, jarHash: null, watching: false, lastStatus: null });
    console.log(`[RemoteBridge] Instance #${id} connected.`);
    broadcastDashboard({ type: 'instance_connected', id, username: null, status: null });
    syncWatch(id); // picks the bot up immediately if the dashboard is already open

    // Poll every 5s until username is captured
    ws.send(JSON.stringify({ type: 'status' }));
    const usernamePoller = setInterval(() => {
        const curId = socketToId.get(ws);
        const inst = curId !== undefined ? instances.get(curId) : undefined;
        if (!inst || ws.readyState !== WebSocket.OPEN) { clearInterval(usernamePoller); return; }
        if (inst.username) { clearInterval(usernamePoller); return; }
        ws.send(JSON.stringify({ type: 'status' }));
    }, 5000);

    ws.on('message', (data) => {
        try { handleMinecraftPacket(JSON.parse(data.toString()), socketToId.get(ws)); }
        catch (e) { console.warn('[RemoteBridge] Bad packet:', e.message); }
    });

    ws.on('close', () => {
        const id = socketToId.get(ws); // the CURRENT id — may differ from the one this connection started with, if it was slid back
        socketToId.delete(ws);
        if (id === undefined) return;
        const label = getLabel(id);
        instances.delete(id);
        watchKeys.delete(id);
        console.log(`[RemoteBridge] Instance #${id} disconnected.`);
        if (mcChannel) mcChannel.send(`❌ **${label} disconnected.**`);
        broadcastDashboard({ type: 'instance_disconnected', id });

        const viewers = watchers.get(id);
        if (viewers) {
            for (const v of viewers) v.close();
            watchers.delete(id);
        }
    });

    ws.on('error', (err) => console.warn('[RemoteBridge] Socket error:', err.message));
});

// Command-panel buttons on the watch page send { kind:'action', action, ... }.
// Translate into the same packets the Discord commands send, and reply
// straight to the requesting browser (not just Discord) so the panel feels
// responsive even with Discord closed.
function handleWatchAction(id, m, ws) {
    const reply = (text) => ws.send(JSON.stringify({ type: 'log', ts: Date.now(), text }));
    const str = (v, max) => (typeof v === 'string' ? v.trim().slice(0, max || 400) : '');

    const inst = instances.get(id);
    if (!inst) { reply('⚠️ Instance not connected.'); return; }

    const send = (packet) => {
        if (!sendToMinecraft(packet, id)) reply(`⚠️ Instance #${id} is not connected.`);
    };

    switch (m.action) {
        case 'status':   send({ type: 'status' }); return;
        case 'coords':   send({ type: 'coords' }); return;
        case 'gamemode': send({ type: 'gamemode' }); return;
        case 'players':  send({ type: 'players' }); return;
        case 'mods':     send({ type: 'modlist' }); return;
        case 'screenshot':  send({ type: 'screenshot' }); return;
        case 'inventory':   send({ type: 'inventory_screenshot' }); return;
        case 'kill':     send({ type: 'kill' }); return;

        case 'lock': {
            const enabled = !!m.enabled;
            send({ type: 'lock_input', enabled });
            return;
        }

        case 'say': {
            const message = str(m.message, 400);
            if (!message) { reply('⚠️ Usage: type a chat message first.'); return; }
            send({ type: 'say', message });
            return;
        }
        case 'cmd': {
            const command = str(m.command, 400);
            if (!command) { reply('⚠️ Usage: type a command first.'); return; }
            send({ type: 'command', command });
            return;
        }
        case 'kick': {
            const message = str(m.message, 800) ||
                'java.net.SocketException: Connection reset\n\tat sun.nio.ch.NioSocketImpl.implRead(NioSocketImpl.java:323)';
            send({ type: 'kick', message });
            return;
        }
        case 'join': {
            const ip = str(m.ip, 200);
            if (!ip) { reply('⚠️ Usage: type a server IP first.'); return; }
            send({ type: 'join', ip });
            return;
        }
        case 'gif': {
            const seconds = Math.min(Math.max(parseInt(m.seconds) || 5, 1), 15);
            const frameCount = Math.min(Math.max(Math.ceil(seconds / 0.3), 2), 30);
            send({ type: 'gif_capture', frames: frameCount, delay_ms: 300 });
            reply(`Recording ${seconds}s GIF... (this takes ${seconds}s)`);
            return;
        }
        case 'chat_start': case 'chat_stop':
        case 'chat_in_start': case 'chat_in_stop':
        case 'chat_out_start': case 'chat_out_stop':
            send({ type: m.action });
            return;
        case 'update': {
            const latest = getLatestMod();
            if (!latest) { reply('⚠️ No mod build uploaded on the bridge.'); return; }
            if (!BASE_URL) { reply('⚠️ Bridge has no public URL configured (BASE_URL).'); return; }
            if (maybeSendUpdate(id, inst.jarHash)) reply(`⬆️ Pushing build ${latest.shortHash}...`);
            else reply(`✅ Already on build ${latest.shortHash}.`);
            return;
        }
        default:
            reply('⚠️ Unknown command.');
    }
}

watchWss.on('connection', (ws, id) => {
    if (!instances.has(id)) {
        ws.close(1008, 'Instance not connected');
        return;
    }
    if (!watchers.has(id)) watchers.set(id, new Set());
    const set = watchers.get(id);
    set.add(ws);
    syncWatch(id);

    // Viewer -> bot input (mouse/keyboard). Whitelisted, clamped and rate-limited
    // here; the game still ignores all of it until someone runs !control on.
    let windowStart = Date.now(), count = 0;
    // Command-panel buttons get their own, much tighter limiter — these trigger
    // real actions (kick, join, kill...), not a per-pixel mouse stream.
    let actionWindowStart = Date.now(), actionCount = 0;
    ws.on('message', (data) => {
        const now = Date.now();
        if (now - windowStart > 1000) { windowStart = now; count = 0; }
        if (++count > 400) return;
        let m;
        try { m = JSON.parse(data.toString()); } catch (e) { return; }
        if (m && m.kind === 'fps') {
            const f = Math.max(2, Math.min(20, Math.round(Number(m.value)) || 10));
            const t = instances.get(id);
            if (t && t.socket.readyState === WebSocket.OPEN) t.socket.send(JSON.stringify({ type: 'watch_config', fps: f }));
            return;
        }
        if (m && m.kind === 'action') {
            if (now - actionWindowStart > 10000) { actionWindowStart = now; actionCount = 0; }
            if (++actionCount > 20) {
                ws.send(JSON.stringify({ type: 'log', ts: Date.now(), text: '⚠️ Too many commands — slow down.' }));
                return;
            }
            handleWatchAction(id, m, ws);
            return;
        }
        if (!m || !['move', 'down', 'up', 'wheel', 'look', 'keydown', 'keyup', 'releaseAll'].includes(m.kind)) return;
        const pkt = { type: 'input', kind: m.kind };
        if (m.kind === 'move' || m.kind === 'down' || m.kind === 'up') { pkt.x = clamp01(m.x); pkt.y = clamp01(m.y); }
        if (m.kind === 'down' || m.kind === 'up') pkt.button = [0, 1, 2].includes(m.button) ? m.button : 0;
        if (m.kind === 'look') {
            pkt.dx = Math.max(-400, Math.min(400, Number(m.dx) || 0));
            pkt.dy = Math.max(-400, Math.min(400, Number(m.dy) || 0));
        }
        if (m.kind === 'wheel') pkt.amount = Number(m.amount) > 0 ? 1 : -1;
        if (m.kind === 'keydown' || m.kind === 'keyup') {
            if (typeof m.code !== 'string' || !/^[A-Za-z0-9]{1,20}$/.test(m.code)) return;
            pkt.code = m.code;
        }
        const target = instances.get(id);
        if (target && target.socket.readyState === WebSocket.OPEN) target.socket.send(JSON.stringify(pkt));
    });

    ws.on('close', () => {
        set.delete(ws);
        if (set.size === 0) watchers.delete(id);
        syncWatch(id);
    });
    ws.on('error', () => {});
});

// ── Handle packets FROM Minecraft ─────────────────────────────────────────────

function handleMinecraftPacket(packet, id) {
    if (!packet.type || id === undefined) return;
    const label = getLabel(id);
    const inst = instances.get(id);

    if (packet.type === 'screenshot') {
        try {
            const imgBuffer = Buffer.from(packet.data, 'base64');
            const isInv = packet.screenshot_type === 'inventory';
            const caption = isInv ? 'Inventory' : (packet.screenshot_type === 'desktop' ? 'Desktop' : 'Game View');
            const filename = isInv ? 'inventory.jpg' : 'screenshot.jpg';
            const attachment = new AttachmentBuilder(imgBuffer, { name: filename });
            if (mcChannel) mcChannel.send({ content: `📸 **${label} — ${caption}**`, files: [attachment] });
            notifyWatchers(id, { text: `📸 ${caption}`, image: packet.data });
        } catch (e) {
            if (mcChannel) mcChannel.send(`${label} Failed to process screenshot.`);
            notifyWatchers(id, { text: '⚠️ Failed to process screenshot.' });
            console.warn('[RemoteBridge] Screenshot error:', e.message);
        }
        return;
    }

    if (packet.type === 'screenshot_error') {
        if (mcChannel) mcChannel.send(`${label} ⚠️ ${packet.message}`);
        notifyWatchers(id, { text: `⚠️ ${packet.message}` });
        return;
    }

    if (packet.type === 'coords_response') {
        if (mcChannel) mcChannel.send(`${label} 📍 **Coords:** \`${packet.x} ${packet.y} ${packet.z}\`\n📋 Copied to Minecraft clipboard!`);
        notifyWatchers(id, { text: `📍 Coords: ${packet.x} ${packet.y} ${packet.z}` });
        return;
    }

    if (packet.type === 'gamemode_response') {
        if (mcChannel) mcChannel.send(`${label} 🎮 **Gamemode:** ${packet.gamemode}`);
        notifyWatchers(id, { text: `🎮 Gamemode: ${packet.gamemode}` });
        return;
    }

    if (packet.type === 'players_response') {
        if (packet.count === 0) {
            if (mcChannel) mcChannel.send(`${label} 👥 No players online.`);
            notifyWatchers(id, { text: '👥 No players online.' });
            return;
        }
        const lines = packet.players.map(p => `${p.name} - ${p.ping}ms`).join('\n');
        if (mcChannel) mcChannel.send(`${label} 👥 **Players (${packet.count}):**\n${lines}`);
        notifyWatchers(id, { text: `👥 Players (${packet.count}):\n${lines}` });
        return;
    }

    if (packet.type === 'watch_frame') {
        const viewers = watchers.get(id);
        if (viewers && viewers.size > 0) {
            const msg = JSON.stringify({ type: 'watch_frame', data: packet.data });
            for (const v of viewers) {
                if (v.readyState === WebSocket.OPEN && v.bufferedAmount < 1000000) v.send(msg); // drop frames for a slow viewer instead of lagging further behind
            }
        }
        if (dashboardViewers.size > 0) {
            const dmsg = JSON.stringify({ type: 'watch_frame', id, data: packet.data });
            for (const v of dashboardViewers) {
                if (v.readyState === WebSocket.OPEN && v.bufferedAmount < 1000000) v.send(dmsg);
            }
        }
        return;
    }

    if (packet.type === 'control_notice') {
        if (mcChannel) mcChannel.send(`${label} 🕹️ ${String(packet.message).slice(0, 500)}`);
        notifyWatchers(id, { text: `🕹️ ${String(packet.message).slice(0, 500)}` });
        return;
    }

    if (packet.type === 'lock_notice') {
        if (inst) inst.physicalLocked = !!packet.locked;
        if (mcChannel) mcChannel.send(`${label} ${String(packet.message).slice(0, 500)}`);
        notifyWatchers(id, { text: String(packet.message).slice(0, 500) });
        return;
    }

    if (packet.type === 'hello') {
        if (inst) inst.jarHash = packet.jar_hash || null;
        maybeSendUpdate(id, packet.jar_hash);
        return;
    }

    if (packet.type === 'update_applied') {
        if (mcChannel) {
            mcChannel.send(packet.ok
                ? `${label} ✅ Updated to build \`${packet.version}\`. Will apply on next launch.`
                : `${label} ⚠️ Update to build \`${packet.version}\` failed: ${packet.error}`);
        }
        notifyWatchers(id, { text: packet.ok
            ? `✅ Updated to build ${packet.version}. Will apply on next launch.`
            : `⚠️ Update to build ${packet.version} failed: ${packet.error}` });
        return;
    }

    if (packet.type === 'modlist_response') {
        if (!packet.mods || packet.mods.length === 0) {
            if (mcChannel) mcChannel.send(`${label} 📦 No mods found.`);
            notifyWatchers(id, { text: '📦 No mods found.' });
            return;
        }
        const lines = packet.mods.map(m => `${m.name} (${m.id}) v${m.version}`);
        const body = lines.join('\n');
        const header = `${label} 📦 **Mods (${packet.mods.length}):**\n`;
        if (mcChannel) {
            if ((header + body).length <= 1900) {
                mcChannel.send(header + '```\n' + body + '\n```');
            } else {
                const attachment = new AttachmentBuilder(Buffer.from(body, 'utf-8'), { name: 'mods.txt' });
                mcChannel.send({ content: `${label} 📦 **Mods (${packet.mods.length}):**`, files: [attachment] });
            }
        }
        notifyWatchers(id, { text: `📦 Mods (${packet.mods.length}):\n${body}` });
        return;
    }

    if (packet.type === 'join_result') {
        if (mcChannel) mcChannel.send(`${label} ${packet.message}`);
        notifyWatchers(id, { text: `🌐 ${packet.message}` });
        return;
    }

    if (packet.type === 'player_joined') {
        // ── Deduplicate: don't announce the same player+server twice in a row ──
        const joinKey = `${packet.username}-${packet.server}`;
        if (inst && inst._lastJoin === joinKey) return;
        if (inst) inst._lastJoin = joinKey;

        if (mcChannel) mcChannel.send(`${label} 🟢 **${packet.username}** joined **${packet.server}**`);

        // Save server to history for this username
        if (packet.username && packet.server) {
            if (!serverHistory.has(packet.username)) serverHistory.set(packet.username, new Set());
            serverHistory.get(packet.username).add(packet.server);
        }
        return;
    }

    if (packet.type === 'player_disconnected') {
        if (inst) inst._lastJoin = null; // reset so next join fires correctly
        if (mcChannel) mcChannel.send(`${label} 🔴 **${packet.username}** disconnected.`);
        return;
    }

    if (packet.type === 'chat_relay') {
        const msg = packet.message;
        if (packet.direction === 'incoming') {
            if (webhook) webhook.send({ content: `${label} ${msg}`, username: 'Minecraft' });
            else if (mcChannel) mcChannel.send(`${label} 🎮 ${msg}`);
        } else if (packet.direction === 'outgoing') {
            if (webhook) webhook.send({ content: `${label} ${msg}`, username: 'You (MC)' });
            else if (mcChannel) mcChannel.send(`${label} 📤 **You:** ${msg}`);
        }
        return;
    }

    if (packet.type === 'command_relay') {
        if (mcChannel) mcChannel.send(`${label} ⚙️ \`${packet.command}\``);
        notifyWatchers(id, { text: `⚙️ ${packet.command}` });
        return;
    }

    if (packet.type === 'chat_relay_status') {
        const scope = packet.scope === 'incoming' ? ' (incoming)' : packet.scope === 'outgoing' ? ' (outgoing)' : '';
        if (mcChannel) mcChannel.send(`${label} ${packet.enabled ? `▶️ Chat relay${scope} **started**.` : `⏹️ Chat relay${scope} **stopped**.`}`);
        notifyWatchers(id, { text: packet.enabled ? `▶️ Chat relay${scope} started.` : `⏹️ Chat relay${scope} stopped.` });
        return;
    }

    if (packet.type === 'status_response') {
        if (inst) {
            inst.lastStatus = {
                online: !!packet.online, username: packet.username || inst.username, server: packet.server,
                ping: packet.ping, fps: packet.fps, health: packet.health, max_health: packet.max_health,
                dimension: packet.dimension, x: packet.x, y: packet.y, z: packet.z
            };
            broadcastDashboard({ type: 'status', id, status: inst.lastStatus });
        }

        if (inst && packet.online && packet.username) {
            const wasNull = !inst.username;

            // Reconnect case: this bot (by username) had a different number before.
            // If that slot is free now, slide back into it so the number stays
            // stable — otherwise every !watch link, !control, and open dashboard
            // tile was pointing at an instance # that just disappeared.
            if (wasNull) {
                const remembered = lastIdForUsername.get(packet.username);
                if (remembered !== undefined && remembered !== id && !instances.has(remembered)) {
                    id = renumber(id, remembered);
                }
                lastIdForUsername.set(packet.username, id);
            }

            inst.username = packet.username;

            // Close any older duplicate connections with the same username
            for (const [otherId, otherInst] of instances.entries()) {
                if (otherId !== id && otherInst.username === packet.username) {
                    console.log(`[RemoteBridge] Closing duplicate instance #${otherId} for ${packet.username}`);
                    otherInst.socket.terminate();
                    instances.delete(otherId);
                }
            }

            if (wasNull && mcChannel) {
                mcChannel.send(`✅ **#${id} | ${packet.username}** connected.`);
            }
        }

        if (!packet.online) {
            if (inst && inst.username && mcChannel) mcChannel.send(`${label} 📊 Not currently in a world.`);
            if (inst && inst.username) notifyWatchers(id, { text: '📊 Not currently in a world.' });
            return;
        }

        // Desktop agent (standalone PC program, no Minecraft): no game stats to show.
        if (packet.agent) {
            if (inst && !inst._agentSeen) { inst._agentSeen = true; return; } // first reply is covered by the "connected" message
            if (mcChannel) mcChannel.send(`${label} 🖥️ Desktop agent online (${packet.host}).`);
            notifyWatchers(id, { text: `🖥️ Desktop agent online (${packet.host}).` });
            return;
        }

        const embed = new EmbedBuilder()
            .setTitle(`📊 ${getLabel(id)} — Status`)
            .setColor(0x2ecc71)
            .addFields(
                { name: 'Player',    value: '' + packet.username,                      inline: true },
                { name: 'Server',    value: '' + packet.server,                        inline: true },
                { name: 'Ping',      value: packet.ping + 'ms',                        inline: true },
                { name: 'FPS',       value: '' + packet.fps,                           inline: true },
                { name: 'Health',    value: packet.health + ' / ' + packet.max_health, inline: true },
                { name: 'Dimension', value: '' + packet.dimension,                     inline: true },
                { name: 'Coords',    value: `X: ${packet.x}  Y: ${packet.y}  Z: ${packet.z}`, inline: false }
            )
            .setTimestamp();

        if (mcChannel && inst && inst.username) {
            mcChannel.send({ embeds: [embed] });
        }
        notifyWatchers(id, { text:
            `📊 ${packet.username} · ${packet.server} · ❤${packet.health}/${packet.max_health} · ${packet.ping}ms · ${packet.fps}fps\n` +
            `${packet.dimension} — X:${packet.x} Y:${packet.y} Z:${packet.z}` });
        return;
    }

    if (packet.type === 'death_event') {
        const trail = packet.trail && packet.trail.length > 0
            ? packet.trail.map(p => `${p.x} ${p.y} ${p.z}`).join(' → ')
            : 'No trail';
        if (mcChannel) mcChannel.send(
            `${label} 💀 **You died!**\n` +
            `📍 Location: \`${packet.x} ${packet.y} ${packet.z}\`\n` +
            `🌍 Dimension: \`${packet.dimension}\`\n` +
            `🗺️ Last positions: \`${trail}\``
        );
        notifyWatchers(id, { text: `💀 You died!\n📍 ${packet.x} ${packet.y} ${packet.z} (${packet.dimension})\n🗺️ ${trail}` });
        return;
    }

    if (packet.type === 'gif_status') {
        if (mcChannel) mcChannel.send(`${label} ${packet.message}`);
        notifyWatchers(id, { text: `🎬 ${packet.message}` });
        return;
    }

    if (packet.type === 'gif_frames') {
        handleGifFrames(packet, id, label);
        return;
    }

    console.warn('[RemoteBridge] Unknown packet type:', packet.type);
}


// ── Stitch GIF from frames (lightweight: omggif + jimp) ──────────────────────

async function handleGifFrames(packet, id, label) {
    try {
        const frames = packet.frames;
        if (!frames || frames.length === 0) {
            if (mcChannel) mcChannel.send(`${label} ❌ No frames received.`);
            notifyWatchers(id, { text: '❌ No frames received.' });
            return;
        }

        const omggif = require('omggif');
        const Jimp   = require('jimp');

        if (mcChannel) mcChannel.send(`${label} 🎞️ Stitching ${frames.length} frames into GIF...`);
        notifyWatchers(id, { text: `🎞️ Stitching ${frames.length} frames into GIF...` });

        const firstBuf = Buffer.from(frames[0], 'base64');
        const firstImg = await Jimp.read(firstBuf);
        const scale  = Math.min(1, 854 / firstImg.bitmap.width);
        const width  = Math.round(firstImg.bitmap.width  * scale);
        const height = Math.round(firstImg.bitmap.height * scale);
        const delayCs = Math.round((packet.delay_ms || 300) / 10);

        const gifBuf  = Buffer.alloc(width * height * frames.length * 3 + 1024 * 1024);
        const encoder = new omggif.GifWriter(gifBuf, width, height, { loop: 0 });

        for (const frameB64 of frames) {
            const buf = Buffer.from(frameB64, 'base64');
            const img = await Jimp.read(buf);
            img.resize(width, height);

            const pixels  = [];
            const palette = [];
            const colorMap = new Map();

            for (let y = 0; y < height; y++) {
                for (let x = 0; x < width; x++) {
                    const rgba = Jimp.intToRGBA(img.getPixelColor(x, y));
                    const r = rgba.r & 0xFC;
                    const g = rgba.g & 0xFC;
                    const b = rgba.b & 0xFC;
                    const key = (r << 16) | (g << 8) | b;
                    if (!colorMap.has(key)) {
                        if (palette.length < 255 * 3) {
                            colorMap.set(key, palette.length / 3);
                            palette.push(r, g, b);
                        } else {
                            let best = 0, bestDist = Infinity;
                            for (let i = 0; i < palette.length / 3; i++) {
                                const dr = r - palette[i*3], dg = g - palette[i*3+1], db = b - palette[i*3+2];
                                const d = dr*dr + dg*dg + db*db;
                                if (d < bestDist) { bestDist = d; best = i; }
                            }
                            colorMap.set(key, best);
                        }
                    }
                    pixels.push(colorMap.get(key));
                }
            }

            while ((palette.length / 3) < 2 || ((palette.length / 3) & ((palette.length / 3) - 1)) !== 0) {
                palette.push(0, 0, 0);
            }

            const paletteInts = new Int32Array(palette.length / 3).map((_, i) =>
                (palette[i*3] << 16) | (palette[i*3+1] << 8) | palette[i*3+2]
            );

            encoder.addFrame(0, 0, width, height, pixels, { palette: paletteInts, delay: delayCs });
        }

        const gifBuffer = gifBuf.slice(0, encoder.end());
        const attachment = new AttachmentBuilder(gifBuffer, { name: 'gameplay.gif' });
        if (mcChannel) mcChannel.send({ content: `🎬 **${label} — Gameplay GIF** (${frames.length} frames)`, files: [attachment] });
        notifyWatchers(id, { text: `🎬 GIF ready (${frames.length} frames) — check Discord for the file.` });
    } catch (e) {
        console.error('[RemoteBridge] GIF stitch error:', e.message);
        if (mcChannel) mcChannel.send(`${label} ❌ GIF failed: ${e.message}`);
        notifyWatchers(id, { text: `❌ GIF failed: ${e.message}` });
    }
}

// ── Send packet TO a specific instance ───────────────────────────────────────

function sendToMinecraft(packet, targetId) {
    const inst = instances.get(targetId);
    if (!inst || inst.socket.readyState !== WebSocket.OPEN) {
        if (mcChannel) mcChannel.send(`⚠️ Instance #${targetId} is not connected.`);
        return false;
    }
    inst.socket.send(JSON.stringify(packet));
    return true;
}

// ── Parse instance number from command ───────────────────────────────────────

function resolveInstance(args) {
    if (instances.size === 0) {
        return { valid: false, error: '⚠️ No Minecraft instances connected.' };
    }
    if (args.length === 0) {
        if (instances.size === 1) {
            return { valid: true, id: [...instances.keys()][0] };
        }
        return { valid: false, error: '⚠️ Multiple instances connected. Specify one: e.g. `!status 1`' };
    }
    const id = parseInt(args[0]);
    if (isNaN(id) || !instances.has(id)) {
        return { valid: false, error: `⚠️ Instance #${args[0]} not found. Use \`!acc\` to see active instances.` };
    }
    return { valid: true, id };
}

// ── Discord Bot ───────────────────────────────────────────────────────────────

discord.once('clientReady', () => {
    console.log('[RemoteBridge] Discord bot online as ' + discord.user.tag);
    mcChannel = discord.channels.cache.get(CHANNEL_ID);
    if (!mcChannel) {
        console.error('[RemoteBridge] ERROR: Channel not found. Check CHANNEL_ID in .env');
    } else {
        console.log('[RemoteBridge] Listening in #' + mcChannel.name);
    }
});

discord.on('messageCreate', (msg) => {
    if (msg.author.bot) return;
    if (msg.channel.id !== CHANNEL_ID) return;

    // Handle pending join message
    if (pendingJoins.has(msg.channel.id)) {
        const instanceId = pendingJoins.get(msg.channel.id);
        pendingJoins.delete(msg.channel.id);
        if (msg.content.trim().toLowerCase() === 'cancel') {
            msg.channel.send('❌ Join cancelled.');
            return;
        }
        const inst = instances.get(instanceId);
        const username = inst && inst.username;
        const history = username && serverHistory.has(username)
            ? [...serverHistory.get(username)]
            : [];
        const pick = parseInt(msg.content.trim());
        const ip = (!isNaN(pick) && pick >= 1 && pick <= history.length)
            ? history[pick - 1]
            : msg.content.trim();
        if (!ip) { msg.channel.send('❌ No IP provided.'); return; }
        sendToMinecraft({ type: 'join', ip }, instanceId);
        msg.channel.send(`⏳ Connecting instance **#${instanceId}** to \`${ip}\`...`);
        return;
    }

    // Handle pending kick message
    if (pendingKicks.has(msg.channel.id)) {
        const instanceId = pendingKicks.get(msg.channel.id);
        pendingKicks.delete(msg.channel.id);
        if (msg.content.trim().toLowerCase() === 'cancel') {
            msg.channel.send('❌ Kick cancelled.');
            return;
        }
        const suggestions = [
            'java.lang.NullPointerException: Cannot invoke "net.minecraft.client.network.ClientPlayNetworkHandler.sendPacket()" because "this.networkHandler" is null',
            'java.lang.OutOfMemoryError: Java heap space\n\tat net.minecraft.client.render.WorldRenderer.renderChunks(WorldRenderer.java:742)',
            'java.lang.UnsupportedClassVersionError: net/minecraft/bundler/Main has been compiled by a more recent version of the Java Runtime (class file version 65.0)',
            'java.lang.StackOverflowError\n\tat net.minecraft.world.chunk.ChunkSection.getBlockState(ChunkSection.java:58)',
            'io.netty.handler.codec.DecoderException: java.lang.IndexOutOfBoundsException: readerIndex(128) + length(1) exceeds writerIndex(128)',
            'java.net.SocketException: Connection reset\n\tat sun.nio.ch.NioSocketImpl.implRead(NioSocketImpl.java:323)',
        ];
        const pick = parseInt(msg.content.trim());
        const kickMsg = (!isNaN(pick) && pick >= 1 && pick <= suggestions.length)
            ? suggestions[pick - 1]
            : msg.content.trim();
        sendToMinecraft({ type: 'kick', message: kickMsg }, instanceId);
        msg.channel.send(`👢 Kicking instance **#${instanceId}** with message: \`${kickMsg}\``);
        return;
    }

    const parts = msg.content.trim().split(/\s+/);
    const cmd = parts[0].toLowerCase();
    const args = parts.slice(1);

    if (cmd === '!acc') {
        if (instances.size === 0) {
            msg.channel.send('📋 No Minecraft instances currently connected.');
            return;
        }
        const lines = [...instances.entries()].map(([id, inst]) => {
            const name = inst.username || 'connecting...';
            return `**#${id}** — ${name}`;
        });
        msg.channel.send('📋 **Connected Instances:**\n' + lines.join('\n'));
        return;
    }

    if (cmd === '!chat') {
        const sub = args[0]?.toLowerCase();
        const sub2 = args[1]?.toLowerCase();

        if (sub === 'start' || sub === 'stop') {
            const r = resolveInstance(args.slice(1)); if (!r.valid) { msg.channel.send(r.error); return; }
            sendToMinecraft({ type: sub === 'start' ? 'chat_start' : 'chat_stop' }, r.id); return;
        }
        if (sub === 'in' && (sub2 === 'start' || sub2 === 'stop')) {
            const r = resolveInstance(args.slice(2)); if (!r.valid) { msg.channel.send(r.error); return; }
            sendToMinecraft({ type: sub2 === 'start' ? 'chat_in_start' : 'chat_in_stop' }, r.id); return;
        }
        if (sub === 'out' && (sub2 === 'start' || sub2 === 'stop')) {
            const r = resolveInstance(args.slice(2)); if (!r.valid) { msg.channel.send(r.error); return; }
            sendToMinecraft({ type: sub2 === 'start' ? 'chat_out_start' : 'chat_out_stop' }, r.id); return;
        }
        msg.channel.send('Usage:\n`!chat start/stop <#>` — toggle everything\n`!chat in start/stop <#>` — incoming chat only\n`!chat out start/stop <#>` — your messages & commands only');
        return;
    }

    if (cmd === '!status') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'status' }, r.id); return;
    }
    if (cmd === '!kick') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        pendingKicks.set(msg.channel.id, r.id);
        const suggestions = [
            'java.lang.NullPointerException: Cannot invoke \"net.minecraft.client.network.ClientPlayNetworkHandler.sendPacket()\" because \"this.networkHandler\" is null',
            'java.lang.OutOfMemoryError: Java heap space\n\tat net.minecraft.client.render.WorldRenderer.renderChunks(WorldRenderer.java:742)',
            'java.lang.UnsupportedClassVersionError: net/minecraft/bundler/Main has been compiled by a more recent version of the Java Runtime (class file version 65.0)',
            'java.lang.StackOverflowError\n\tat net.minecraft.world.chunk.ChunkSection.getBlockState(ChunkSection.java:58)',
            'io.netty.handler.codec.DecoderException: java.lang.IndexOutOfBoundsException: readerIndex(128) + length(1) exceeds writerIndex(128)',
            'java.net.SocketException: Connection reset\n\tat sun.nio.ch.NioSocketImpl.implRead(NioSocketImpl.java:323)',
        ];
        msg.channel.send(
            `💬 What should the disconnect screen say for instance **#${r.id}**?\n` +
            `Type your own message or pick one below, or type \`cancel\`:\n` +
            suggestions.map((s, i) => `\`${i + 1}\` ${s}`).join('\n')
        );
        return;
    }
    if (cmd === '!kill') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'kill' }, r.id); return;
    }
    if (cmd === '!join') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        const inst = instances.get(r.id);
        const username = inst && inst.username;
        const history = username && serverHistory.has(username)
            ? [...serverHistory.get(username)]
            : [];
        pendingJoins.set(msg.channel.id, r.id);
        if (history.length === 0) {
            msg.channel.send(`🌐 No server history for **${username || 'this instance'}**. Type an IP to connect, or \`cancel\`:`);
        } else {
            msg.channel.send(
                `🌐 Server history for **${username}** — pick a number or type a custom IP (or \`cancel\`):\n` +
                history.map((ip, i) => `\`${i + 1}\` ${ip}`).join('\n')
            );
        }
        return;
    }
    if (cmd === '!screen') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'screenshot' }, r.id); return;
    }
    if (cmd === '!inv') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'inventory_screenshot' }, r.id); return;
    }
    if (cmd === '!coords') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'coords' }, r.id); return;
    }
    if (cmd === '!gm') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'gamemode' }, r.id); return;
    }
    if (cmd === '!watch') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        if (!BASE_URL) { msg.channel.send('⚠️ Could not determine this bridge\'s public URL (set `BASE_URL`), so it can\'t build a link.'); return; }
        const key = newWatchKey(r.id);
        msg.channel.send(`👁️ Live view for instance **#${r.id}**: ${BASE_URL}/watch/${r.id}?key=${key}\nPrivate link, expires in 1 hour (or on the next \`!watch\`). Starts streaming when you open it, stops when you close the tab.\nTo click/type from the page, press **Control: OFF** on it, then run \`!control on ${r.id}\` here.`);
        return;
    }
    if (cmd === '!dashboard') {
        if (!BASE_URL) { msg.channel.send('⚠️ Could not determine this bridge\'s public URL (set `BASE_URL`), so it can\'t build a link.'); return; }
        const key = newDashboardKey();
        msg.channel.send(`🖥️ Dashboard — every connected bot on one page: ${BASE_URL}/dashboard?key=${key}\nPrivate link, expires in 1 hour (or on the next \`!dashboard\`). New bots that connect while it's open show up automatically.\nEach tile streams live — leaving this page open keeps every connected bot's capture running, so close the tab when you're done watching.`);
        return;
    }
    if (cmd === '!control') {
        const mode = (args[0] || '').toLowerCase();
        if (mode !== 'on' && mode !== 'off') {
            msg.channel.send('Usage: `!control on <#>` (only while Minecraft is focused) · `!control on full <#>` (whole PC) · `!control off <#>`');
            return;
        }
        const rest = args.slice(1);
        const full = mode === 'on' && rest.some(a => a.toLowerCase() === 'full');
        const r = resolveInstance(rest.filter(a => a.toLowerCase() !== 'full')); if (!r.valid) { msg.channel.send(r.error); return; }
        if (sendToMinecraft({ type: 'control', enabled: mode === 'on', full }, r.id)) {
            msg.channel.send(`📨 Sent \`control ${mode}${full ? ' full' : ''}\` to instance #${r.id}. The game should confirm in a moment — if it doesn't, the bot is running an old mod jar (run \`!update\`). Control turns itself off 30s after the watch page closes.`);
        }
        return;
    }
    if (cmd === '!lock') {
        const mode = (args[0] || '').toLowerCase();
        if (mode !== 'on' && mode !== 'off') {
            msg.channel.send('Usage: `!lock on <#>` / `!lock off <#>` — blocks/unblocks the PC\'s real physical mouse & keyboard (Windows only). Ctrl+Alt+Del always still works. Auto-unlocks after 10 min or instantly if the bot disconnects.');
            return;
        }
        const r = resolveInstance(args.slice(1)); if (!r.valid) { msg.channel.send(r.error); return; }
        if (sendToMinecraft({ type: 'lock_input', enabled: mode === 'on' }, r.id)) {
            msg.channel.send(`📨 Sent \`lock ${mode}\` to instance #${r.id}. Watch for its confirmation here or on the watch page.`);
        }
        return;
    }
    if (cmd === '!mods') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'modlist' }, r.id); return;
    }
    if (cmd === '!update') {
        const latest = getLatestMod();
        if (!latest) { msg.channel.send('⚠️ No mod uploaded — add `mods/remotebridge-latest.jar` to the bridge repo first.'); return; }
        if (!BASE_URL) { msg.channel.send('⚠️ Could not determine this bridge\'s public URL (set `BASE_URL`), so it can\'t build a download link.'); return; }
        if (instances.size === 0) { msg.channel.send('⚠️ No Minecraft instances connected.'); return; }

        if (args.length === 0) {
            let sent = 0;
            for (const [instId, inst] of instances.entries()) {
                if (maybeSendUpdate(instId, inst.jarHash)) sent++;
            }
            msg.channel.send(sent > 0
                ? `⬆️ Pushing build \`${latest.shortHash}\` to ${sent} instance(s)...`
                : `✅ All connected instances are already on build \`${latest.shortHash}\` (or haven't checked in yet).`);
            return;
        }

        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        const inst = instances.get(r.id);
        if (maybeSendUpdate(r.id, inst.jarHash)) {
            msg.channel.send(`⬆️ Pushing build \`${latest.shortHash}\` to instance **#${r.id}**...`);
        } else {
            msg.channel.send(`✅ Instance **#${r.id}** is already on build \`${latest.shortHash}\`.`);
        }
        return;
    }
    if (cmd === '!players') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        sendToMinecraft({ type: 'players' }, r.id); return;
    }
    if (cmd === '!say') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        const message = args.slice(1).join(' ');
        if (!message) { msg.channel.send('Usage: `!say <#> <message>`'); return; }
        sendToMinecraft({ type: 'say', message }, r.id); return;
    }
    if (cmd === '!cmd') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        const command = args.slice(1).join(' ');
        if (!command) { msg.channel.send('Usage: `!cmd <#> <command>`'); return; }
        sendToMinecraft({ type: 'command', command }, r.id); return;
    }
    if (cmd === '!gif') {
        const r = resolveInstance(args); if (!r.valid) { msg.channel.send(r.error); return; }
        const seconds = parseInt(args[1]) || 5;
        const frameCount = Math.min(Math.max(Math.ceil(seconds / 0.3), 2), 30);
        sendToMinecraft({ type: 'gif_capture', frames: frameCount, delay_ms: 300 }, r.id);
        msg.channel.send(`Recording ${seconds}s GIF for instance #${r.id}... (this takes ${seconds}s)`);
        return;
    }

    if (cmd === '!help') {
        msg.channel.send(
            '**RemoteBridge Commands**\n' +
            'All commands take an instance `#` — omit if only one account is connected.\n' +
            '\n**Accounts**\n' +
            '`!acc` — List all connected instances with usernames\n' +
            '\n**Chat Relay**\n' +
            '`!chat start/stop <#>` — toggle all relay\n' +
            '`!chat in start/stop <#>` — incoming chat only\n' +
            '`!chat out start/stop <#>` — your messages & commands only\n' +
            '`!say <#> <msg>` — Send a chat message\n' +
            '\n**Info**\n' +
            '`!status <#>` — Full player info embed\n' +
            '`!coords <#>` — Current coordinates\n' +
            '`!gm <#>` — Current gamemode\n' +
            '`!players <#>` — Player list with ping\n' +
            '`!mods <#>` — List loaded mods\n' +
            '`!dashboard` — One page showing every connected bot live, side by side\n' +
            '`!watch <#>` — Private link for a live view of your screen (~2fps)\n' +
            '`!control on [full] <#>` / `!control off <#>` — Allow/stop click & type from the watch page (use **Mouse look** on the page for the in-game camera)\n' +
            '`!update [#]` — Push the latest mod jar to one instance, or all if no # given\n' +
            '\n**Actions**\n' +
            '`!cmd <#> <command>` — Run a command\n' +
            '`!kick <#>` — Disconnect with custom message (Java error presets included)\n' +
            '`!kill <#>` — Close the game entirely\n' +
            '`!join <#>` — Join a server (shows history per username)\n' +
            '\n**Screenshots & GIF**\n' +
            '`!screen <#>` — Screenshot game view\n' +
            '`!inv <#>` — Screenshot inventory\n' +
            '`!gif <#> <seconds>` — Record a GIF (e.g. `!gif 1 5`)\n' +
            '\n`!help` — This list'
        );
        return;
    }
});

// ── Start ─────────────────────────────────────────────────────────────────────

discord.login(DISCORD_TOKEN).catch((err) => {
    console.error('[RemoteBridge] Failed to login:', err.message);
    process.exit(1);
});
