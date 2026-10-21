import 'dotenv/config';
import makeWASocket, {
  DisconnectReason,
  fetchLatestBaileysVersion,
  useMultiFileAuthState,
  Browsers
} from '@whiskeysockets/baileys';
import pino from 'pino';
import fs from 'node:fs';
import path from 'node:path';

const logger = pino({ level: process.env.LOG_LEVEL || 'warn' });
const DATA_DIR = path.resolve(process.env.DATA_DIR || './data');
const AUTH_DIR = path.resolve('./auth');
const GROUP_NAMES = (process.env.AUTHORIZED_GROUP_NAMES || '')
  .split('|||').map(s => s.trim()).filter(Boolean);
const ADMINS = new Set((process.env.ADMIN_NUMBERS || '')
  .split(',').map(s => normalizeNumber(s)).filter(Boolean));
const PAIRING = (process.env.USE_PAIRING_CODE || 'true').toLowerCase() === 'true';
const PHONE = normalizeNumber(process.env.WHATSAPP_PHONE_NUMBER || '');
const DB_FILE = path.join(DATA_DIR, 'bot-data.json');

fs.mkdirSync(DATA_DIR, { recursive: true });
fs.mkdirSync(AUTH_DIR, { recursive: true });

function normalizeNumber(value) {
  return String(value || '').replace(/[^0-9]/g, '');
}
function readDb() {
  try {
    const parsed = JSON.parse(fs.readFileSync(DB_FILE, 'utf8'));
    return {
      online: parsed.online || {},
      deliveries: parsed.deliveries || [],
      nextDeliveryId: Number(parsed.nextDeliveryId || 1),
      history: parsed.history || []
    };
  } catch {
    return { online: {}, deliveries: [], nextDeliveryId: 1, history: [] };
  }
}
let db = readDb();
function saveDb() {
  const tmp = `${DB_FILE}.tmp`;
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2), { mode: 0o600 });
  fs.renameSync(tmp, DB_FILE);
}
function senderNumber(jid = '') {
  const left = String(jid).split('@')[0].split(':')[0];
  return normalizeNumber(left);
}
function isAdmin(jid) {
  return ADMINS.has(senderNumber(jid));
}
function getText(message) {
  const m = message?.message;
  return m?.conversation
    || m?.extendedTextMessage?.text
    || m?.imageMessage?.caption
    || m?.videoMessage?.caption
    || '';
}
function formatDuration(ms) {
  const seconds = Math.max(0, Math.floor(ms / 1000));
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = seconds % 60;
  return `${h}h ${m}min ${s}s`;
}
function elapsedFor(worker, now = Date.now()) {
  return (worker.totalMs || 0) + (worker.startedAt ? now - worker.startedAt : 0);
}
function displayName(jid, pushName) {
  return pushName || senderNumber(jid) || jid;
}

async function startBot() {
  const { state, saveCreds } = await useMultiFileAuthState(AUTH_DIR);
  let version;
  try {
    ({ version } = await fetchLatestBaileysVersion());
  } catch {
    version = undefined;
  }
  const sock = makeWASocket({
    version,
    auth: state,
    logger,
    browser: Browsers.ubuntu('Chegô Delivery Server'),
    printQRInTerminal: false,
    markOnlineOnConnect: false,
    syncFullHistory: false,
    generateHighQualityLinkPreview: false
  });

  sock.ev.on('creds.update', saveCreds);

  let pairingRequested = false;
  sock.ev.on('connection.update', async ({ connection, lastDisconnect }) => {
    if (connection === 'connecting' && PAIRING && !state.creds.registered && !pairingRequested) {
      pairingRequested = true;
      if (!PHONE) {
        console.error('Configure WHATSAPP_PHONE_NUMBER no .env para gerar o código de pareamento.');
      } else {
        try {
          const code = await sock.requestPairingCode(PHONE);
          console.log(`Código de pareamento do WhatsApp: ${code}`);
          console.log('Digite-o no WhatsApp: Dispositivos conectados → Conectar dispositivo → conectar com número de telefone.');
        } catch (err) {
          pairingRequested = false;
          console.error('Não foi possível gerar o código de pareamento:', err?.message || err);
        }
      }
    }
    if (connection === 'open') {
      console.log('Chegô Delivery conectado ao WhatsApp.');
      const groups = await sock.groupFetchAllParticipating().catch(() => ({}));
      const found = [];
      for (const [jid, metadata] of Object.entries(groups)) {
        if (GROUP_NAMES.includes(metadata.subject)) found.push({ jid, name: metadata.subject });
      }
      console.log(`Grupos autorizados encontrados: ${found.length}/${GROUP_NAMES.length}`);
      for (const g of found) console.log(`- ${g.name}: ${g.jid}`);
      for (const name of GROUP_NAMES) {
        if (!found.some(g => g.name === name)) console.warn(`Grupo ainda não encontrado: ${name}`);
      }
    }
    if (connection === 'close') {
      const status = lastDisconnect?.error?.output?.statusCode;
      const loggedOut = status === DisconnectReason.loggedOut;
      console.error('Conexão encerrada.', loggedOut ? 'Sessão desconectada; verifique a autenticação.' : 'Tentando reconectar...');
      if (!loggedOut) setTimeout(() => startBot().catch(console.error), 3000);
    }
  });

  sock.ev.on('messages.upsert', async ({ messages, type }) => {
    if (type !== 'notify') return;
    for (const msg of messages) {
      try {
        if (!msg.message || msg.key.fromMe) continue;
        const chat = msg.key.remoteJid;
        if (!chat || chat === 'status@broadcast' || chat.endsWith('@newsletter')) continue;
        const text = getText(msg).trim();
        if (!text.startsWith('!')) continue;

        const isGroup = chat.endsWith('@g.us');
        const senderJid = isGroup ? (msg.key.participant || '') : chat;
        const sender = senderNumber(senderJid);
        const groupMeta = isGroup ? await sock.groupMetadata(chat).catch(() => null) : null;
        const allowedGroup = Boolean(groupMeta && GROUP_NAMES.includes(groupMeta.subject));
        const reply = async (body) => sock.sendMessage(chat, { text: body }, { quoted: msg });
        const commandLine = text.slice(1).trim();
        const [rawCommand, ...args] = commandLine.split(/\s+/);
        const command = (rawCommand || '').toLowerCase();
        const payload = args.join(' ').trim();
        const name = displayName(senderJid, msg.pushName);

        if (command === 'menu' || command === 'ajuda') {
          await reply(
            '🚀 *CHEGÔ DELIVERY — COMANDOS INICIAIS*\\n' +
            '1️⃣ `!online` — ficar online (somente nos grupos autorizados)\\n' +
            '2️⃣ `!offline` — encerrar tempo online\\n' +
            '3️⃣ `!lista online` — ver entregadores online\\n' +
            '4️⃣ `!tempo` — ver seu tempo online acumulado\\n' +
            '5️⃣ `!entrega descrição` — registrar entrega\\n' +
            '6️⃣ `!editar ID nova descrição` — editar entrega\\n' +
            '7️⃣ `!relatorio` — relatório administrativo'
          );
          continue;
        }

        if (command === 'tempo') {
          const worker = db.online[sender] || { totalMs: 0, startedAt: null };
          await reply(`⏱️ *Seu tempo online acumulado:* ${formatDuration(elapsedFor(worker))}`);
          continue;
        }

        if (!isGroup || !allowedGroup) {
          await reply('⚠️ Este comando só pode ser usado nos quatro grupos autorizados.');
          continue;
        }

        if (command === 'online') {
          const worker = db.online[sender] || { number: sender, name, totalMs: 0, startedAt: null };
          if (worker.startedAt) {
            await reply(`🟢 ${name}, você já está online há ${formatDuration(Date.now() - worker.startedAt)}.`);
          } else {
            worker.name = name;
            worker.number = sender;
            worker.startedAt = Date.now();
            worker.lastGroup = groupMeta.subject;
            db.online[sender] = worker;
            db.history.push({ type: 'online', number: sender, name, group: groupMeta.subject, at: Date.now() });
            saveDb();
            await reply(`🟢 *${name} agora está ONLINE!*\\nSeu tempo começou a contar.`);
          }
          continue;
        }

        if (command === 'offline') {
          const worker = db.online[sender];
          if (!worker?.startedAt) {
            await reply('🟡 Você não está marcado como online.');
          } else {
            const now = Date.now();
            const session = now - worker.startedAt;
            worker.totalMs = (worker.totalMs || 0) + session;
            worker.startedAt = null;
            db.history.push({ type: 'offline', number: sender, name: worker.name || name, group: groupMeta.subject, durationMs: session, at: now });
            saveDb();
            await reply(`🔴 *${worker.name || name} ficou OFFLINE.*\\nTempo desta sessão: ${formatDuration(session)}\\nTotal acumulado: ${formatDuration(worker.totalMs)}.`);
          }
          continue;
        }

        if (command === 'lista' && args[0]?.toLowerCase() === 'online') {
          const workers = Object.values(db.online).filter(w => w.startedAt);
          await reply(workers.length
            ? `🟢 *ENTREGADORES ONLINE (${workers.length})*\\n` + workers.map((w, i) => `${i + 1}. ${w.name || w.number} — ${formatDuration(Date.now() - w.startedAt)}`).join('\\n')
            : '🟡 Não há entregadores online no momento.');
          continue;
        }

        if (command === 'entrega') {
          if (!payload) { await reply('Use: `!entrega descrição da entrega`'); continue; }
          const item = {
            id: db.nextDeliveryId++, description: payload, group: groupMeta.subject,
            createdBy: sender, createdByName: name, createdAt: Date.now(), updatedAt: Date.now()
          };
          db.deliveries.push(item);
          db.history.push({ type: 'delivery_created', id: item.id, number: sender, group: groupMeta.subject, at: Date.now() });
          saveDb();
          await reply(`📦 *Entrega #${item.id} registrada*\\n${item.description}`);
          continue;
        }

        if (command === 'editar') {
          const id = Number(args[0]);
          const description = args.slice(1).join(' ').trim();
          const item = db.deliveries.find(d => d.id === id && d.group === groupMeta.subject);
          if (!Number.isInteger(id) || !item || !description) {
            await reply('Use: `!editar ID nova descrição`\\nA entrega precisa existir neste grupo.');
            continue;
          }
          if (item.createdBy !== sender && !isAdmin(senderJid)) {
            await reply('⛔ Só quem registrou a entrega ou um administrador pode editá-la.');
            continue;
          }
          item.description = description;
          item.updatedAt = Date.now();
          item.updatedBy = sender;
          db.history.push({ type: 'delivery_edited', id, number: sender, group: groupMeta.subject, at: Date.now() });
          saveDb();
          await reply(`✏️ *Entrega #${id} atualizada*\\n${description}`);
          continue;
        }

        if (command === 'relatorio') {
          if (!isAdmin(senderJid)) { await reply('⛔ Comando restrito aos administradores.'); continue; }
          const workers = Object.values(db.online);
          const deliveries = db.deliveries.filter(d => d.group === groupMeta.subject);
          const total = workers.reduce((sum, w) => sum + elapsedFor(w), 0);
          await reply(
            `📊 *RELATÓRIO — ${groupMeta.subject}*\\n` +
            `Entregadores registrados: ${workers.length}\\n` +
            `Entregadores online: ${workers.filter(w => w.startedAt).length}\\n` +
            `Entregas registradas neste grupo: ${deliveries.length}\\n` +
            `Tempo online acumulado (todos): ${formatDuration(total)}\\n` +
            `Gerado em: ${new Date().toLocaleString('pt-BR', { timeZone: process.env.TIMEZONE || 'America/Fortaleza' })}`
          );
          continue;
        }
      } catch (err) {
        logger.error({ err }, 'Falha ao processar mensagem');
      }
    }
  });
}

startBot().catch(err => {
  console.error('Falha ao iniciar Chegô Delivery:', err);
  process.exitCode = 1;
});
