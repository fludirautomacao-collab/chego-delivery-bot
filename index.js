const {
  default: makeWASocket,
  useMultiFileAuthState,
  DisconnectReason,
  jidNormalizedUser,
  downloadMediaMessage
} = require('@whiskeysockets/baileys')

const qrcode = require('qrcode-terminal')
const pino = require('pino')
const fs = require('fs')
const zlib = require('zlib')
const crypto = require('crypto')
const http = require('http')

const path = require('path')
const { atomicWriteFile, atomicWriteFileAsync } = require('./persistencia')

// Compatibilidade com hospedagens Node.js: permite apontar os dados para um disco persistente.
// Sem DATA_DIR/AUTH_DIR, mantém o comportamento original de salvar ao lado do index.js.
const DATA_DIR = path.resolve(process.env.DATA_DIR || __dirname)
const AUTH_DIR = path.resolve(process.env.AUTH_DIR || path.join(DATA_DIR, 'auth'))
try { fs.mkdirSync(DATA_DIR, { recursive: true }) } catch (e) { console.error('Não foi possível preparar DATA_DIR:', e.message) }
try { fs.mkdirSync(AUTH_DIR, { recursive: true }) } catch (e) { console.error('Não foi possível preparar AUTH_DIR:', e.message) }
const ARQUIVO = path.join(DATA_DIR, 'fila.json')
// Histórico dos relatórios fica fora da pasta do código/ZIP para sobreviver à troca dos arquivos do bot.
// Em hospedagens com volume persistente, configure REPORTS_FILE para um caminho nesse volume.
const REPORTS_FILE = path.resolve(process.env.REPORTS_FILE || path.join(DATA_DIR, 'chego-relatorios-persistentes.json'))
const CAMPOS_RELATORIOS_PERSISTENTES = ['historicoEntregas', 'sessoesOnline', 'solicitacoesRelatorio', 'importacoesRelatorio', 'corridas', 'entregasAceitas', 'bloqueiosTaxas']
const AUTH = AUTH_DIR

// Diagnóstico antecipado: não confundir gravação local com persistência após troca do ZIP.
function verificarDiretorioGravavel(diretorio, rotulo) {
  const teste = path.join(diretorio, `.chego-write-check-${process.pid}-${crypto.randomBytes(4).toString('hex')}.tmp`)
  try {
    fs.mkdirSync(diretorio, { recursive: true })
    fs.writeFileSync(teste, 'ok', { flag: 'wx', mode: 0o600 })
    fs.unlinkSync(teste)
    console.log(`💾 Armazenamento gravável (${rotulo}): ${diretorio}`)
    return true
  } catch (e) {
    try { if (fs.existsSync(teste)) fs.unlinkSync(teste) } catch (_) {}
    console.error(`🚨 ARMAZENAMENTO NÃO GRAVÁVEL (${rotulo}): ${diretorio} — ${e.message}`)
    return false
  }
}

function diagnosticarPersistencia() {
  const dataDirConfigurado = Boolean(process.env.DATA_DIR && process.env.DATA_DIR.trim())
  if (!dataDirConfigurado) {
    console.warn('⚠️ DATA_DIR não configurado: os dados estão sendo gravados junto ao código do bot. Se a hospedagem substituir/recriar essa pasta ao enviar ZIP ou reiniciar, os dados podem ser perdidos. Configure DATA_DIR para um volume persistente oferecido pelo provedor.')
  }
  verificarDiretorioGravavel(DATA_DIR, 'dados e backups')
  verificarDiretorioGravavel(AUTH_DIR, 'sessão WhatsApp')
  verificarDiretorioGravavel(path.dirname(REPORTS_FILE), 'histórico de relatórios')
  if (!process.env.REPORTS_FILE && process.env.DATA_DIR) {
    console.log('ℹ️ REPORTS_FILE não configurado; o histórico de relatórios usará DATA_DIR.')
  }
}

diagnosticarPersistencia()

const EMPRESA_CONFIG = {
  SEU_DELIVERY: { nome: 'SEU DELIVERY', g1Nome: 'EQUIPE MOTOBOY', g2Nome: 'SEU DELIVERY PATOS-PB' },
  CHEGO_DELIVERY: { nome: 'CHEGÔ DELIVERY', g1Nome: 'CHEGÔ ENTREGADORES🚀', g2Nome: 'CHEGÔ DELIVERY (EMPRESAS)' }
}

let empresaAtual = 'SEU_DELIVERY'
let empresas = {}
// Limites individuais globais: valem em todos os grupos/empresas do bot.
let limitesEntregasGlobais = {}
let aliasesComandos = { indo: [], offline: [], online: [], proximo: [], final: [], ocupado: [], livre: [], lista: [] }
// Quando ativado pelo ADM no privado, o bot não apaga mensagens em grupos das empresas.
let naoApagarMensagensEmpresas = false
let ultimaListaPublicada = ''
let ultimaListaEnviada = ''
// Referência persistente da única mensagem de lista exibida e horário da última edição.
let ultimaListaMensagemKey = null
let ultimaListaPublicadaEm = 0
// Conta edições/criações bem-sucedidas para diagnóstico e sincronização de comandos.
let contadorAtualizacaoLista = 0
// Evita repetir falhas de edição a cada ciclo do temporizador. O comando manual Lista
// continua podendo recuperar a publicação imediatamente.
const falhasEdicaoListaAte = new Map()
const INTERVALO_SUPRESSAO_FALHA_EDICAO_MS = 30_000
let listaSuspensaPico = false
let bloquearPicoAutomatico = false
let listaSuspensaADM = false
let statusPicoAnterior = {}
let socketWhatsAppCadastro = null
let servidorCadastro = null

// Serializa eventos para impedir que as duas empresas troquem o estado
// global no meio de um comando assíncrono.
let filaExecucao = Promise.resolve()

function executarSerializado(fn) {
  const proximo = filaExecucao.then(fn, fn)
  // A fila continua utilizável após uma falha, mas o erro deixa de ser
  // descartado silenciosamente. O chamador continua recebendo a rejeição.
  filaExecucao = proximo.catch((erro) => {
    const instante = new Date().toISOString()
    console.error(`[ERRO-EXECUCAO-SERIALIZADA] ${instante}:`, erro?.stack || erro?.message || erro)
  })
  return proximo
}

const COMANDOS_ON = [
  'online',
  'on',
  'on line',
  'onli',
  'onl',
  'onliine',
  'onlin',
  'onlane',
  'onlne',
  'onine',
  'onlie',
  'onlime',
  'onlina',
  'onlini',
  'onlinne',
  'onlinr',
  'onlinem',
  'orlaine',
  'orlaim',
  'orlaime',
  'orlaine',
  'orline',
  'orlin',
  'orlaim',
  'auline',
  'aulini',
  'auline',
  'auline',
  'oline',
  'olline',
  'onile',
  'onile',
  'onlin',
  'on-line',
  'onlinee',
  'onlinei',
  'onlineo',
  'onlline',
  'onnline',
  'onliine'
]

const COMANDOS_OFF = [
  'off',
  'offline',
  'off line',
  'of',
  'offi',
  'offli',
  'offl',
  'offlin',
  'ofline',
  'ofiline',
  'oflane',
  'oflne',
  'offine',
  'offlie',
  'offlime',
  'offlina',
  'offlini',
  'offlinne',
  'offliner',
  'onfile',
  'onfline',
  'onfli',
  'onfl',
  'ofline',
  'oflinee',
  'off-line',
  'offlinee',
  'offlne',
  'offine',
  'offliine',
  'offlline',
  'offfline',
  'ofline',
  'oflinee'
]

// Aceita erros comuns de digitação e frases curtas usadas para confirmar que saiu.
// A normalização abaixo também ignora acentos, maiúsculas e pontuação final.
const COMANDOS_INDO = [
  // Variações comuns de digitação de "indo" (sem frases que ninguém usa).
  'indi', 'indo', 'indio', 'indu', 'lndo', 'indoo', 'indooo', 'indoooo', 'indooooo',
  'ind', 'indd', 'indoo', 'indooo', 'ind0', 'indo0',
  'idno', 'inod', 'iondo', 'inndo', 'iindo', 'inndo',
  'indo.', 'indo!', 'indo?', 'lndo.', 'lndo!',
  'indoo.', 'indooo.', 'indooo!', 'indoo!',
  'indooo', 'indoooo', 'indoooo!',
  'indo..', 'indo!!', 'indo???', 'lndoo', 'lndoo!',
  // Outras variações solicitadas: substituições, omissões, duplicações,
  // inversões e separadores comuns no teclado do celular.
  'ando','endo','ondo','undo','ynda','ynde','yndi','yndu','yndy','yndo',
  '8ndo','9ndo','0ndo','pndo','lndo','kndo','jndo','hndo','gndo','fndo','tndo','r ndo','vndo','bndo','mndo','nndo','cndo','xndo','zndo','w ndo','qndo',
  'iado','iedo','iido','iudo','iydo','ikdo','ijdo','ildo','imdo','isdo','ifdo','igdo','ihdo','itdo','irdo','ipdo','ibdo','ivdo','icdo','ixdo','izdo','iwdo','iqdo','i0do','i9do','i8do',
  'inbo','inco','ineo','info','ingo','inho','injo','inko','inlo','inmo','inno','inro','inso','into','invo','inxo','inyo','inzo','in0o','in9o','in8o','inpo','inqo','inwo',
  'inda','inde','indi','indu','indy','indp','indl','indk','indj','indm','indn','indb','indv','indc','indx','inds','indf','indg','indh','indr','indt','indw','indq','indz','ind1','ind2','ind3','ind0','ind9',
  'ndo','ido','ino','ind','indd','io','in','id','inod','idno','iodn','odni','dino','nido','dnoi','dion','onid','nodi',
  'iindo','iiindo','inndo','innndo','inddo','indddo','indoo','indooo','indoooo','indooooo','iinndo','inndoo','iinndoo','inddoo','iindoo','innddo',
  'iondo','inido','inudo','indio','induo','indyo','indoe','indoi','indou','indos','indom','indon','indor','indot','aindo','eindo','oindo','uindo','yindo','iando','iendo','iundo','iyndo',
  'indoa','indo1','ind0','indo.', 'indo!', 'indo?', 'i ndo','in do','ind o','i n d o','i.ndo','in.do','ind.o','i-ndo','in-do','ind-o','in_do','ind_o','i/ndo','in/do','ind/o','i,ndo','in,do','ind,o','i!ndo','in!do','ind!o'
]

// Reconhece também combinações novas de até duas edições de "indo". Limita-se
// a tokens curtos e exclui palavras comuns para evitar que "no" ou conversa normal
// sejam interpretados como aceite de entrega.
function ehComandoIndo(valor, msg = null) {
  const token = normalizarTexto(valor).replace(/[^a-z0-9]/g, '')
  if (!token || token.length < 3 || token.length > 5) return false
  if (COMANDOS_INDO.some(alias => normalizarTexto(alias).replace(/[^a-z0-9]/g, '') === token)) return true
  // Variações aproximadas (1 edição) só valem quando a mensagem é resposta a outra
  // mensagem (a da entrega); conversa solta nunca é lida como aceite.
  if (!msg || !obterMensagemRespondida(msg)) return false
  if (PALAVRAS_COMUNS_NAO_INDO.includes(token)) return false
  const alvo = 'indo'
  let anterior = Array.from({length: alvo.length + 1}, (_, i) => i)
  for (let i = 1; i <= token.length; i++) {
    const atual = [i]
    for (let j = 1; j <= alvo.length; j++) {
      atual[j] = Math.min(atual[j - 1] + 1, anterior[j] + 1, anterior[j - 1] + (token[i - 1] === alvo[j - 1] ? 0 : 1))
    }
    anterior = atual
  }
  return anterior[alvo.length] <= 1
}
const PALAVRAS_COMUNS_NAO_INDO = ['nao','sim','oi','ola','opa','no','sai','fim','dia','bom','tudo','todo','lindo','mundo','sendo','fundo','vindo','rindo','findo','ando','ido','undo','endo','onde','inda','indio','ido']


// Comandos canônicos que também podem receber apelidos cadastrados por ADM no privado.
const COMANDOS_PROXIMO = ['proximo','próximo','prox','proxim','proximoo','prossimo','prossimu','prochimo','prochimu','prosim','prosimu','procsimo']
const COMANDOS_FINAL = ['final','ultimo','último']
const COMANDOS_OCUPADO = ['ocupado']
const COMANDOS_LIVRE = ['livre','🟢']
const COMANDOS_LISTA = ['lista']

let grupos = { g1: null, g2: null, g1Participantes: [] }

let estado = {
  online: [], espera: [], bloqueados: [], bloqueadosSemana: [],
  corridas: [], contadorCorrida: 0, rotaAtiva: null, entregasAceitas: [], indosSemEntrega: [], historicoEntregas: [], sessoesOnline: [], solicitacoesRelatorio: [], importacoesRelatorio: [], taxasSemanais: {}, bloqueiosTaxas: [],
  g1Admins: [], entregadores: [], bairrosAdicionados: [], mapeamentosBairrosAntigos: {}, ultimaLimpeza: null, undoADM: null, historicoUndoLista: [], ultimoSnapshotUndoLista: null, bloqueiosAutomaticosEscala: [], ultimaAvaliacaoEscala: null, variacoesEntrega: { entrega: false, indo: false, fracionado: false }, feriado: false, silencio: false
}

function estadoVazio() {
  return {
    online: [], espera: [], bloqueados: [], bloqueadosSemana: [],
    corridas: [], contadorCorrida: 0, rotaAtiva: null, entregasAceitas: [], indosSemEntrega: [], historicoEntregas: [], sessoesOnline: [], solicitacoesRelatorio: [], importacoesRelatorio: [], taxasSemanais: {}, bloqueiosTaxas: [],
    g1Admins: [], entregadores: [], bairrosAdicionados: [], mapeamentosBairrosAntigos: {}, ultimaLimpeza: null, undoADM: null, historicoUndoLista: [], ultimoSnapshotUndoLista: null, bloqueiosAutomaticosEscala: [], ultimaAvaliacaoEscala: null, variacoesEntrega: { entrega: false, indo: false, fracionado: false }, feriado: false
  }
}

function inicializarEmpresas() {
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    if (!empresas[chave]) empresas[chave] = {
      grupos: { g1: null, g2: null, g1Participantes: [] },
      estado: estadoVazio(), ultimaListaPublicada: '', ultimaListaEnviada: '', ultimaListaMensagemKey: null, ultimaListaPublicadaEm: 0, listaSuspensaPico: false, listaSuspensaADM: false, statusPicoAnterior: {}, bloquearPicoAutomatico: false
    }
    empresas[chave].estado = { ...estadoVazio(), ...(empresas[chave].estado || {}) }
    empresas[chave].estado.variacoesEntrega = { entrega: false, indo: false, fracionado: false, ...(empresas[chave].estado.variacoesEntrega || {}) }
    empresas[chave].grupos = { g1: null, g2: null, g1Participantes: [], ...(empresas[chave].grupos || {}) }
    // Mantém o estado por grupo inicializado no disco. Em arquivos antigos,
    // migra os metadados legados para g1 uma única vez; não aceita uma chave
    // sem ID, sem fromMe=true ou pertencente a outro grupo.
    if (!empresas[chave].estadosPorGrupo || typeof empresas[chave].estadosPorGrupo !== 'object' || Array.isArray(empresas[chave].estadosPorGrupo)) {
      empresas[chave].estadosPorGrupo = {}
    }
    if (!empresas[chave].estadosPorGrupo.g1 || typeof empresas[chave].estadosPorGrupo.g1 !== 'object' || Array.isArray(empresas[chave].estadosPorGrupo.g1)) {
      const chaveLegada = empresas[chave].ultimaListaMensagemKey
      const jidLegado = String(chaveLegada?.remoteJid || '').trim().toLowerCase()
      const jidG1 = String(empresas[chave].grupos.g1 || '').trim().toLowerCase()
      const chaveLegadaValida = Boolean(chaveLegada?.id && chaveLegada?.fromMe === true && jidLegado && jidG1 && jidLegado === jidG1)
      empresas[chave].estadosPorGrupo.g1 = {
        ultimaListaPublicada: String(empresas[chave].ultimaListaPublicada || ''),
        ultimaListaEnviada: String(empresas[chave].ultimaListaEnviada || ''),
        ultimaListaMensagemKey: chaveLegadaValida ? { ...chaveLegada } : null,
        ultimaListaPublicadaEm: Number(empresas[chave].ultimaListaPublicadaEm) || 0,
        listaSuspensaPico: !!empresas[chave].listaSuspensaPico,
        listaSuspensaADM: !!empresas[chave].listaSuspensaADM,
        bloquearPicoAutomatico: !!empresas[chave].bloquearPicoAutomatico,
        statusPicoAnterior: { ...(empresas[chave].statusPicoAnterior || {}) }
      }
    } else {
      const metaG1 = empresas[chave].estadosPorGrupo.g1
      const chaveG1 = metaG1.ultimaListaMensagemKey
      const jidG1 = String(empresas[chave].grupos.g1 || '').trim().toLowerCase()
      const jidChave = String(chaveG1?.remoteJid || '').trim().toLowerCase()
      if (!chaveG1?.id || chaveG1?.fromMe !== true || !jidG1 || !jidChave || jidChave !== jidG1) metaG1.ultimaListaMensagemKey = null
      if (!Number.isFinite(Number(metaG1.ultimaListaPublicadaEm))) metaG1.ultimaListaPublicadaEm = 0
      else metaG1.ultimaListaPublicadaEm = Number(metaG1.ultimaListaPublicadaEm)
      if (!metaG1.statusPicoAnterior || typeof metaG1.statusPicoAnterior !== 'object') metaG1.statusPicoAnterior = {}
    }
    if (!empresas[chave].ultimaListaMensagemKey || typeof empresas[chave].ultimaListaMensagemKey !== 'object' || !empresas[chave].ultimaListaMensagemKey.id) empresas[chave].ultimaListaMensagemKey = null
    if (!Number.isFinite(Number(empresas[chave].ultimaListaPublicadaEm))) empresas[chave].ultimaListaPublicadaEm = 0
    else empresas[chave].ultimaListaPublicadaEm = Number(empresas[chave].ultimaListaPublicadaEm)
    if (!empresas[chave].statusPicoAnterior || typeof empresas[chave].statusPicoAnterior !== 'object') empresas[chave].statusPicoAnterior = {}
    empresas[chave].bloquearPicoAutomatico = !!empresas[chave].bloquearPicoAutomatico
    if (!Array.isArray(empresas[chave].estado.online)) empresas[chave].estado.online = []
    if (!Array.isArray(empresas[chave].estado.espera)) empresas[chave].estado.espera = []
    if (!Array.isArray(empresas[chave].estado.bloqueados)) empresas[chave].estado.bloqueados = []
    if (!Array.isArray(empresas[chave].estado.bloqueadosSemana)) empresas[chave].estado.bloqueadosSemana = []
    if (!Array.isArray(empresas[chave].estado.corridas)) empresas[chave].estado.corridas = []
    if (!Array.isArray(empresas[chave].estado.entregasAceitas)) empresas[chave].estado.entregasAceitas = []
    if (!Array.isArray(empresas[chave].estado.indosSemEntrega)) empresas[chave].estado.indosSemEntrega = []
    if (!Array.isArray(empresas[chave].estado.historicoEntregas)) empresas[chave].estado.historicoEntregas = []
    if (!Array.isArray(empresas[chave].estado.sessoesOnline)) empresas[chave].estado.sessoesOnline = []
    if (!empresas[chave].estado.taxasSemanais || typeof empresas[chave].estado.taxasSemanais !== 'object') empresas[chave].estado.taxasSemanais = {}
    if (!Array.isArray(empresas[chave].estado.bloqueiosTaxas)) empresas[chave].estado.bloqueiosTaxas = []
    if (!Array.isArray(empresas[chave].estado.solicitacoesRelatorio)) empresas[chave].estado.solicitacoesRelatorio = []
    if (!Array.isArray(empresas[chave].estado.importacoesRelatorio)) empresas[chave].estado.importacoesRelatorio = []
    if (!Array.isArray(empresas[chave].estado.g1Admins)) empresas[chave].estado.g1Admins = []
    if (!Array.isArray(empresas[chave].estado.entregadores)) empresas[chave].estado.entregadores = []
    if (!Array.isArray(empresas[chave].estado.cadastrosMotoboyPendentes)) empresas[chave].estado.cadastrosMotoboyPendentes = []
    if (!Array.isArray(empresas[chave].estado.cadastrosMotoboy)) empresas[chave].estado.cadastrosMotoboy = []
    if (!Array.isArray(empresas[chave].estado.bairrosAdicionados)) empresas[chave].estado.bairrosAdicionados = []
    if (!empresas[chave].estado.mapeamentosBairrosAntigos || typeof empresas[chave].estado.mapeamentosBairrosAntigos !== 'object') empresas[chave].estado.mapeamentosBairrosAntigos = {}
    if (!empresas[chave].estado.tabelaPrecosBairros || typeof empresas[chave].estado.tabelaPrecosBairros !== 'object') empresas[chave].estado.tabelaPrecosBairros = {}
    if (!Array.isArray(empresas[chave].estado.folguistasEscala)) empresas[chave].estado.folguistasEscala = []
    if (!Array.isArray(empresas[chave].estado.semEscalaPermanente)) empresas[chave].estado.semEscalaPermanente = []
    if (!Array.isArray(empresas[chave].estado.justificativasEscala)) empresas[chave].estado.justificativasEscala = []
    if (!Array.isArray(empresas[chave].estado.bloqueiosAutomaticosEscala)) empresas[chave].estado.bloqueiosAutomaticosEscala = []
    if (empresas[chave].estado.ultimaAvaliacaoEscala === undefined) empresas[chave].estado.ultimaAvaliacaoEscala = null
    if (!Array.isArray(empresas[chave].estado.historicoUndoLista)) empresas[chave].estado.historicoUndoLista = []
    if (empresas[chave].estado.historicoUndoLista.length > 100) empresas[chave].estado.historicoUndoLista.splice(0, empresas[chave].estado.historicoUndoLista.length - 100)
    if (empresas[chave].estado.ultimoSnapshotUndoLista && typeof empresas[chave].estado.ultimoSnapshotUndoLista !== 'object') empresas[chave].estado.ultimoSnapshotUndoLista = null
    empresas[chave].estado.feriado = !!empresas[chave].estado.feriado
    empresas[chave].estado.silencio = !!empresas[chave].estado.silencio
  }
}

function selecionarEmpresa(chave) {
  if (!empresas[chave]) return false
  if (empresas[empresaAtual]) {
    const empresaAnterior = empresas[empresaAtual]
    empresaAnterior.estado = estado
    empresaAnterior.grupos = grupos
    // O escopo g1 é a fonte de verdade da mensagem de lista visível. Não permita
    // que uma troca temporária de contexto (por exemplo, ao processar g2) regrave
    // os campos legados com uma referência antiga.
    const metaListaVisivel = empresaAnterior.estadosPorGrupo?.g1 || {}
    empresaAnterior.ultimaListaPublicada = metaListaVisivel.ultimaListaPublicada !== undefined ? metaListaVisivel.ultimaListaPublicada : ultimaListaPublicada
    empresaAnterior.ultimaListaEnviada = metaListaVisivel.ultimaListaEnviada !== undefined ? metaListaVisivel.ultimaListaEnviada : ultimaListaEnviada
    empresaAnterior.ultimaListaMensagemKey = metaListaVisivel.ultimaListaMensagemKey !== undefined ? metaListaVisivel.ultimaListaMensagemKey : ultimaListaMensagemKey
    empresaAnterior.ultimaListaPublicadaEm = Number(metaListaVisivel.ultimaListaPublicadaEm !== undefined ? metaListaVisivel.ultimaListaPublicadaEm : ultimaListaPublicadaEm) || 0
    empresaAnterior.listaSuspensaPico = listaSuspensaPico
    empresaAnterior.bloquearPicoAutomatico = bloquearPicoAutomatico
    empresaAnterior.listaSuspensaADM = listaSuspensaADM
    empresaAnterior.statusPicoAnterior = statusPicoAnterior
  }
  empresaAtual = chave
  estado = empresas[chave].estado
  grupos = empresas[chave].grupos
  ultimaListaPublicada = empresas[chave].ultimaListaPublicada || ''
  ultimaListaEnviada = empresas[chave].ultimaListaEnviada || ''
  ultimaListaMensagemKey = empresas[chave].ultimaListaMensagemKey || null
  ultimaListaPublicadaEm = Number(empresas[chave].ultimaListaPublicadaEm) || 0
  listaSuspensaPico = !!empresas[chave].listaSuspensaPico
  listaSuspensaADM = !!empresas[chave].listaSuspensaADM
  statusPicoAnterior = { ...(empresas[chave].statusPicoAnterior || {}) }
  bloquearPicoAutomatico = !!empresas[chave].bloquearPicoAutomatico
  return true
}

function empresaDoGrupo(jid) {
  const id = jidNormalizedUser(jid || '')
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const g = empresas[chave]?.grupos || {}
    if (mesmoJid(g.g1, id) || mesmoJid(g.g2, id)) return chave
  }
  return null
}

// Compara JIDs de grupo de forma tolerante a maiúsculas e sufixos de dispositivo.
// A identificação da empresa e o roteamento dos comandos precisam usar a mesma regra.
function normalizarJidComparacao(valor) {
  const bruto = String(valor || '').trim().toLowerCase()
  if (!bruto) return ''
  let normalizado = bruto
  try { normalizado = String(jidNormalizedUser(bruto) || bruto).toLowerCase() } catch {}
  return normalizado.replace(/:\d+(?=@)/g, '')
}

function mesmoJid(a, b) {
  const idA = normalizarJidComparacao(a)
  const idB = normalizarJidComparacao(b)
  return Boolean(idA && idB && idA === idB)
}


/* =====================================
   CARREGAR DADOS
===================================== */

function carregar() {
  try {
    const dados = JSON.parse(fs.readFileSync(ARQUIVO, 'utf8'))
    if (dados && dados.empresas) {
      empresas = dados.empresas
      limitesEntregasGlobais = dados.limitesEntregasGlobais && typeof dados.limitesEntregasGlobais === 'object' ? dados.limitesEntregasGlobais : {}
      naoApagarMensagensEmpresas = dados.naoApagarMensagensEmpresas === true
      aliasesComandos = { indo: [], offline: [], online: [], proximo: [], final: [], ocupado: [], livre: [], lista: [], ...(dados.aliasesComandos || {}) }
      for (const tipo of Object.keys(aliasesComandos)) { if (!Array.isArray(aliasesComandos[tipo])) aliasesComandos[tipo] = []; aliasesComandos[tipo] = [...new Set(aliasesComandos[tipo].map(normalizarTexto).filter(Boolean))] }
      for (const [tipo, lista] of Object.entries(aliasesComandos)) { const alvo = ({indo:COMANDOS_INDO,offline:COMANDOS_OFF,online:COMANDOS_ON,proximo:COMANDOS_PROXIMO,final:COMANDOS_FINAL,ocupado:COMANDOS_OCUPADO,livre:COMANDOS_LIVRE,lista:COMANDOS_LISTA})[tipo]; if (alvo) for (const alias of lista) if (!alvo.includes(alias)) alvo.push(alias) }
    } else {
      inicializarEmpresas()
      empresas.SEU_DELIVERY.estado = { ...estadoVazio(), ...(dados || {}) }
    }
  } catch (erro) {
    empresas = {}
    limitesEntregasGlobais = {}
    naoApagarMensagensEmpresas = false
  }
  // Recupera o histórico persistente externo e une os registros sem apagar os atuais.
  try {
    if (fs.existsSync(REPORTS_FILE)) {
      const persistidos = JSON.parse(fs.readFileSync(REPORTS_FILE, 'utf8'))
      for (const chave of Object.keys(EMPRESA_CONFIG)) {
        const atual = empresas[chave] = empresas[chave] || { estado: estadoVazio() }
        atual.estado = atual.estado || estadoVazio()
        const salvo = persistidos?.empresas?.[chave] || {}
        for (const campo of CAMPOS_RELATORIOS_PERSISTENTES) {
          const a = Array.isArray(atual.estado[campo]) ? atual.estado[campo] : []
          const b = Array.isArray(salvo[campo]) ? salvo[campo] : []
          const vistos = new Set(a.map(item => JSON.stringify(item)))
          atual.estado[campo] = [...a, ...b.filter(item => { const k = JSON.stringify(item); if (vistos.has(k)) return false; vistos.add(k); return true })]
        }
        atual.estado.taxasSemanais = { ...(salvo.taxasSemanais || {}), ...(atual.estado.taxasSemanais || {}) }
      }
    }
  } catch (e) {
    console.error('Não foi possível ler o arquivo persistente de relatórios:', e.message)
  }
  inicializarEmpresas()
  empresaAtual = 'SEU_DELIVERY'
  estado = empresas.SEU_DELIVERY.estado
  grupos = empresas.SEU_DELIVERY.grupos
  ultimaListaPublicada = empresas.SEU_DELIVERY.ultimaListaPublicada || ''
  ultimaListaEnviada = empresas.SEU_DELIVERY.ultimaListaEnviada || ''
  ultimaListaMensagemKey = empresas.SEU_DELIVERY.ultimaListaMensagemKey || null
  ultimaListaPublicadaEm = Number(empresas.SEU_DELIVERY.ultimaListaPublicadaEm) || 0
  listaSuspensaPico = !!empresas.SEU_DELIVERY.listaSuspensaPico
  listaSuspensaADM = !!empresas.SEU_DELIVERY.listaSuspensaADM
  statusPicoAnterior = { ...(empresas.SEU_DELIVERY.statusPicoAnterior || {}) }
  bloquearPicoAutomatico = !!empresas.SEU_DELIVERY.bloquearPicoAutomatico
}

carregar()

let ultimoRelatorioPersistidoJson = null
let ultimaFilaPersistidaJson = null

function salvar() {
  try {
    if (!empresas[empresaAtual]) return
    empresas[empresaAtual].estado = estado
    empresas[empresaAtual].grupos = grupos
    const metaListaVisivel = empresas[empresaAtual].estadosPorGrupo?.g1 || {}
    empresas[empresaAtual].ultimaListaPublicada = metaListaVisivel.ultimaListaPublicada !== undefined ? metaListaVisivel.ultimaListaPublicada : ultimaListaPublicada
    empresas[empresaAtual].ultimaListaEnviada = metaListaVisivel.ultimaListaEnviada !== undefined ? metaListaVisivel.ultimaListaEnviada : ultimaListaEnviada
    empresas[empresaAtual].ultimaListaMensagemKey = metaListaVisivel.ultimaListaMensagemKey !== undefined ? metaListaVisivel.ultimaListaMensagemKey : ultimaListaMensagemKey
    empresas[empresaAtual].ultimaListaPublicadaEm = Number(metaListaVisivel.ultimaListaPublicadaEm !== undefined ? metaListaVisivel.ultimaListaPublicadaEm : ultimaListaPublicadaEm) || 0
    empresas[empresaAtual].listaSuspensaPico = listaSuspensaPico
    empresas[empresaAtual].bloquearPicoAutomatico = bloquearPicoAutomatico
    empresas[empresaAtual].listaSuspensaADM = listaSuspensaADM
    agendarGravacaoDisco()
  } catch (e) {
    console.error(`[ERRO-PERSISTENCIA] ${new Date().toISOString()} Falha ao preparar dados principais:`, e?.stack || e?.message || e)
  }
}

let temporizadorGravacaoDisco = null
let gravacaoDiscoEmAndamento = false
function agendarGravacaoDisco() {
  if (temporizadorGravacaoDisco) return
  temporizadorGravacaoDisco = setTimeout(() => { temporizadorGravacaoDisco = null; gravarDisco(false) }, 400)
}
// sincrono=true: usado no encerramento do processo e antes de backups.
function gravarDisco(sincrono) {
  if (sincrono && temporizadorGravacaoDisco) { clearTimeout(temporizadorGravacaoDisco); temporizadorGravacaoDisco = null }
  if (gravacaoDiscoEmAndamento && !sincrono) { agendarGravacaoDisco(); return }
  try {
    const filaJson = JSON.stringify({ versao: 3, empresas, limitesEntregasGlobais, aliasesComandos, naoApagarMensagensEmpresas })
    if (filaJson !== ultimaFilaPersistidaJson) {
      ultimaFilaPersistidaJson = filaJson
      if (sincrono) atomicWriteFile(ARQUIVO, filaJson)
      else {
        gravacaoDiscoEmAndamento = true
        atomicWriteFileAsync(ARQUIVO, filaJson).catch(e => { ultimaFilaPersistidaJson = null; console.error('[ERRO-PERSISTENCIA] fila.json:', e?.message || e) }).finally(() => { gravacaoDiscoEmAndamento = false })
      }
    }
    // Grava separadamente o histórico dos relatórios, sem depender do arquivo dentro do ZIP.
    try {
      fs.mkdirSync(path.dirname(REPORTS_FILE), { recursive: true })
      const historico = { versao: 1, empresas: {} }
      for (const chave of Object.keys(EMPRESA_CONFIG)) {
        const est = empresas[chave]?.estado || {}
        historico.empresas[chave] = {}
        for (const campo of CAMPOS_RELATORIOS_PERSISTENTES) historico.empresas[chave][campo] = Array.isArray(est[campo]) ? est[campo] : []
        historico.empresas[chave].taxasSemanais = est.taxasSemanais && typeof est.taxasSemanais === 'object' ? est.taxasSemanais : {}
      }
      const historicoConteudo = JSON.stringify(historico)
      if (historicoConteudo !== ultimoRelatorioPersistidoJson) {
        historico.atualizadoEm = new Date().toISOString()
        atomicWriteFile(REPORTS_FILE, JSON.stringify(historico))
        ultimoRelatorioPersistidoJson = historicoConteudo
      }
    } catch (erroRelatorios) {
      console.error('Erro ao salvar arquivo persistente dos relatórios:', erroRelatorios.message)
    }
  } catch (e) {
    console.error(`[ERRO-PERSISTENCIA] ${new Date().toISOString()} Falha ao salvar dados principais:`, e?.stack || e?.message || e)
  }
}
for (const sinal of ['SIGINT', 'SIGTERM']) process.on(sinal, () => { try { gravarDisco(true) } catch (_) {} process.exit(0) })
process.on('beforeExit', () => { try { gravarDisco(true) } catch (_) {} })
process.on('unhandledRejection', (motivo) => { console.error('[unhandledRejection]', motivo?.stack || motivo) })
process.on('uncaughtException', (erro) => { console.error('[uncaughtException]', erro?.stack || erro); try { gravarDisco(true) } catch (_) {} })


/* =====================================
   BACKUP PERSISTENTE DE DADOS E SESSÃO WHATSAPP
   Dados: a cada 3 horas; sessão: a cada 12 horas.
===================================== */
const PASTA_BACKUPS_DADOS = path.join(DATA_DIR, 'backups', 'dados')
const PASTA_BACKUPS_AUTH = path.join(DATA_DIR, 'backups', 'whatsapp-auth')
const MARCADOR_SESSAO_REJEITADA = path.join(DATA_DIR, '.whatsapp-auth-rejected')
const INTERVALO_BACKUP_DADOS = 3 * 60 * 60 * 1000
const INTERVALO_BACKUP_AUTH = 12 * 60 * 60 * 1000
let ultimoBackupDadosEm = 0
let ultimoBackupAuthEm = 0
let temporizadorRestauracaoAuth = null
let restauracaoAuthEmAndamento = false
let conectadoWhatsApp = false
let desconectadoDesde = 0
let restaurouAuthNestaQueda = false

const CHAVE_BACKUP = process.env.BACKUP_KEY ? crypto.scryptSync(String(process.env.BACKUP_KEY), 'chego-backup-v1', 32) : null
if (!CHAVE_BACKUP) console.warn('⚠️ BACKUP_KEY não definida: backups da sessão e dos dados ficam SEM criptografia. Defina BACKUP_KEY no painel do provedor.')
function cifrarBackup(buf) {
  const iv = crypto.randomBytes(12)
  const c = crypto.createCipheriv('aes-256-gcm', CHAVE_BACKUP, iv)
  const enc = Buffer.concat([c.update(buf), c.final()])
  return Buffer.concat([Buffer.from('CHB1'), iv, c.getAuthTag(), enc])
}
function decifrarBackup(buf) {
  if (!CHAVE_BACKUP) throw new Error('Backup criptografado e BACKUP_KEY ausente')
  if (buf.subarray(0, 4).toString() !== 'CHB1') throw new Error('Formato de backup inválido')
  const d = crypto.createDecipheriv('aes-256-gcm', CHAVE_BACKUP, buf.subarray(4, 16))
  d.setAuthTag(buf.subarray(16, 32))
  return Buffer.concat([d.update(buf.subarray(32)), d.final()])
}
// Lê um arquivo de backup, claro ou .enc.
function lerArquivoBackup(arquivo) {
  if (fs.existsSync(arquivo)) return fs.readFileSync(arquivo)
  if (fs.existsSync(arquivo + '.enc')) return decifrarBackup(fs.readFileSync(arquivo + '.enc'))
  const e = new Error('ENOENT: ' + arquivo); e.code = 'ENOENT'; throw e
}
function gravarArquivoBackup(destino, buf) {
  fs.mkdirSync(path.dirname(destino), { recursive: true, mode: 0o700 })
  if (CHAVE_BACKUP) fs.writeFileSync(destino + '.enc', cifrarBackup(buf), { mode: 0o600 })
  else fs.writeFileSync(destino, buf, { mode: 0o600 })
}
function copiarDiretorioParaBackup(origem, destino) {
  fs.mkdirSync(destino, { recursive: true, mode: 0o700 })
  for (const e of fs.readdirSync(origem, { withFileTypes: true })) {
    const o = path.join(origem, e.name), d = path.join(destino, e.name)
    if (e.isDirectory()) copiarDiretorioParaBackup(o, d)
    else if (e.isFile()) gravarArquivoBackup(d, fs.readFileSync(o))
  }
}
function restaurarDiretorioDeBackup(origem, destino) {
  fs.mkdirSync(destino, { recursive: true })
  for (const e of fs.readdirSync(origem, { withFileTypes: true })) {
    const o = path.join(origem, e.name)
    if (e.isDirectory()) { restaurarDiretorioDeBackup(o, path.join(destino, e.name)); continue }
    if (!e.isFile()) continue
    if (e.name.endsWith('.enc')) fs.writeFileSync(path.join(destino, e.name.slice(0, -4)), decifrarBackup(fs.readFileSync(o)), { mode: 0o600 })
    else fs.copyFileSync(o, path.join(destino, e.name))
  }
}

function nomeSnapshot(prefixo, timestamp = Date.now()) {
  return `${prefixo}-${new Date(timestamp).toISOString().replace(/[:.]/g, '-')}`
}
function copiarArquivoSeExiste(origem, destino) {
  if (!fs.existsSync(origem)) return false
  gravarArquivoBackup(destino, fs.readFileSync(origem))
  return true
}
function limparSnapshots(pasta, prefixo, maximo) {
  try {
    const nomes = fs.readdirSync(pasta).filter(n => n.startsWith(prefixo + '-') && fs.statSync(path.join(pasta, n)).isDirectory()).sort()
    for (const nome of nomes.slice(0, Math.max(0, nomes.length - maximo))) fs.rmSync(path.join(pasta, nome), { recursive: true, force: true })
  } catch (_) {}
}
function criarBackupDados(forcar = false) {
  const agora = Date.now()
  if (!forcar && agora - ultimoBackupDadosEm < INTERVALO_BACKUP_DADOS) return false
  try {
    try { gravarDisco(true) } catch (_) {}
    fs.mkdirSync(PASTA_BACKUPS_DADOS, { recursive: true, mode: 0o700 })
    const pasta = path.join(PASTA_BACKUPS_DADOS, nomeSnapshot('dados', agora))
    fs.mkdirSync(pasta, { recursive: true })
    let copiou = false
    for (const arquivo of [ARQUIVO, REPORTS_FILE]) copiou = copiarArquivoSeExiste(arquivo, path.join(pasta, path.basename(arquivo))) || copiou
    if (!copiou) { fs.rmSync(pasta, { recursive: true, force: true }); return false }
    fs.writeFileSync(path.join(pasta, 'backup-manifest.json'), JSON.stringify({ criadoEm: new Date(agora).toISOString(), arquivos: [ARQUIVO, REPORTS_FILE].filter(fs.existsSync) }, null, 2))
    ultimoBackupDadosEm = agora
    limparSnapshots(PASTA_BACKUPS_DADOS, 'dados', 96) // até 12 dias, em intervalos de 3 horas
    console.log(`💾 Backup dos dados concluído: ${pasta}`)
    return true
  } catch (e) { console.error('Falha no backup dos dados:', e.message); return false }
}
function snapshotAuthPodeSerRestaurado(pastaSnapshot) {
  // Somente snapshots regulares gerados pelo backup periódico. Nunca restaura
  // diretórios auth-rejected-* ou sessões preservadas durante pareamento manual.
  const nome = path.basename(pastaSnapshot)
  if (!/^auth-\d{4}-\d{2}-\d{2}T/.test(nome)) return false
  const creds = path.join(pastaSnapshot, 'creds.json')
  try {
    const dados = JSON.parse(lerArquivoBackup(creds).toString('utf8'))
    return !!dados && typeof dados === 'object' && !Array.isArray(dados) && Object.keys(dados).length > 0
  } catch (_) { return false }
}
function localizarUltimoSnapshotValido(pasta, prefixo, arquivoObrigatorio) {
  try {
    const nomes = fs.readdirSync(pasta).filter(n => n.startsWith(prefixo + '-')).sort().reverse()
    for (const nome of nomes) {
      const dir = path.join(pasta, nome)
      if (!fs.statSync(dir).isDirectory()) continue
      if (prefixo === 'auth' && !snapshotAuthPodeSerRestaurado(dir)) continue
      const arquivo = path.join(dir, arquivoObrigatorio)
      try { JSON.parse(lerArquivoBackup(arquivo).toString('utf8')); return dir } catch (_) {}
    }
  } catch (_) {}
  return null
}
function pontuarDadosFila(dados) {
  let total = 0
  const campos = ['entregadores','online','espera','bloqueados','bloqueadosSemana','historicoEntregas','sessoesOnline','corridas','entregasAceitas','solicitacoesRelatorio','escalasManuais','folguistasEscala','justificativasEscala','bairrosAdicionados','bloqueiosAutomaticosEscala']
  for (const empresa of Object.values(dados?.empresas || {})) {
    const est = empresa?.estado || {}
    for (const campo of campos) total += Array.isArray(est[campo]) ? est[campo].length : 0
    for (const campo of ['tabelaPrecosBairros','taxasSemanais','mapeamentosBairrosAntigos']) total += est[campo] && typeof est[campo] === 'object' ? Object.keys(est[campo]).length : 0
    total += Array.isArray(empresa?.escalasManuais) ? empresa.escalasManuais.length : 0
  }
  return total
}
function recuperarDadosSeNecessario() {
  const precisaFila = !fs.existsSync(ARQUIVO) || (() => { try { JSON.parse(fs.readFileSync(ARQUIVO, 'utf8')); return false } catch (_) { return true } })()
  const precisaRelatorios = !fs.existsSync(REPORTS_FILE) || (() => { try { JSON.parse(fs.readFileSync(REPORTS_FILE, 'utf8')); return false } catch (_) { return true } })()
  // Regra de segurança: backup nunca substitui arquivo atual que seja JSON válido.
  // Quantidade de registros não indica qual versão é mais recente; um backup antigo
  // pode ter mais itens e apagar alterações recentes (ex.: remoções e correções).
  // A recuperação automática abaixo só atua quando o arquivo está ausente ou inválido.
  if (!precisaFila && !precisaRelatorios) return false
  try {
    const dirs = fs.readdirSync(PASTA_BACKUPS_DADOS).filter(n => n.startsWith('dados-')).sort().reverse()
    for (const nome of dirs) {
      const dir = path.join(PASTA_BACKUPS_DADOS, nome)
      let restaurou = false
      if (precisaFila) {
        const f = path.join(dir, path.basename(ARQUIVO))
        try { const txt = lerArquivoBackup(f).toString('utf8'); const d = JSON.parse(txt); if (d && typeof d === 'object') { atomicWriteFile(ARQUIVO, txt); restaurou = true } } catch (_) {}
      }
      if (precisaRelatorios) {
        const f = path.join(dir, path.basename(REPORTS_FILE))
        try { const txt = lerArquivoBackup(f).toString('utf8'); const d = JSON.parse(txt); if (d && typeof d === 'object') { atomicWriteFile(REPORTS_FILE, txt); restaurou = true } } catch (_) {}
      }
      if (restaurou) console.log(`♻️ Dados recuperados automaticamente do backup ${nome}`)
      if ((!precisaFila || fs.existsSync(ARQUIVO)) && (!precisaRelatorios || fs.existsSync(REPORTS_FILE))) return restaurou
    }
  } catch (e) { console.error('Falha ao procurar backup para recuperação:', e.message) }
  return false
}
function criarBackupAuth(forcar = false) {
  const agora = Date.now()
  if (!forcar && agora - ultimoBackupAuthEm < INTERVALO_BACKUP_AUTH) return false
  try {
    if (!fs.existsSync(AUTH_DIR) || !fs.readdirSync(AUTH_DIR).length) return false
    fs.mkdirSync(PASTA_BACKUPS_AUTH, { recursive: true, mode: 0o700 })
    const pasta = path.join(PASTA_BACKUPS_AUTH, nomeSnapshot('auth', agora))
    if (fs.existsSync(pasta)) throw new Error('snapshot já existe')
    copiarDiretorioParaBackup(AUTH_DIR, pasta)
    if (!snapshotAuthPodeSerRestaurado(pasta)) {
      fs.rmSync(pasta, { recursive: true, force: true })
      console.error('Backup da sessão ignorado: creds.json ausente, inválido ou snapshot não restaurável.')
      return false
    }
    ultimoBackupAuthEm = agora
    limparSnapshots(PASTA_BACKUPS_AUTH, 'auth', 5)
    console.log(`🔐 Backup da sessão WhatsApp concluído: ${pasta}`)
    return true
  } catch (e) { console.error('Falha no backup da sessão WhatsApp:', e.message); return false }
}
function restaurarUltimoBackupAuth() {
  // Depois de loggedOut/401, nenhum snapshot antigo pode ser restaurado:
  // ele pode conter exatamente a sessão que o WhatsApp acabou de rejeitar.
  if (fs.existsSync(MARCADOR_SESSAO_REJEITADA)) {
    console.warn('Recuperação automática de AUTH bloqueada: sessão anterior foi rejeitada; é necessário novo pareamento.')
    return false
  }
  if (restauracaoAuthEmAndamento) return false
  restauracaoAuthEmAndamento = true
  try {
    const dirs = fs.readdirSync(PASTA_BACKUPS_AUTH).filter(n => n.startsWith('auth-')).sort().reverse()
    for (const nome of dirs) {
      const origem = path.join(PASTA_BACKUPS_AUTH, nome)
      try {
        if (!fs.statSync(origem).isDirectory() || !snapshotAuthPodeSerRestaurado(origem)) continue
        const quarentena = path.join(DATA_DIR, `auth-anterior-${Date.now()}`)
        if (fs.existsSync(AUTH_DIR)) fs.renameSync(AUTH_DIR, quarentena)
        restaurarDiretorioDeBackup(origem, AUTH_DIR)
        console.log(`♻️ Sessão WhatsApp restaurada do backup ${nome}`)
        try { fs.rmSync(quarentena, { recursive: true, force: true }) } catch (_) {}
        return true
      } catch (e) { console.error(`Backup de sessão inválido (${nome}):`, e.message) }
    }
    console.error('Não existe backup válido da sessão WhatsApp para restaurar.')
  } catch (e) { console.error('Falha ao restaurar sessão WhatsApp:', e.message) }
  finally { restauracaoAuthEmAndamento = false }
  return false
}

// Recupera arquivos ausentes/corrompidos antes de iniciar conexões; recarrega o estado restaurado.
recuperarDadosSeNecessario()
carregar()

/* =====================================
   BACKUP DIÁRIO ÀS 06:00 (horário de São Paulo)
   Preserva fila, relatórios, cadastros e o código atual.
===================================== */
function verificarBackupDiario() {
  try {
    const agora = new Date()
    const partes = new Intl.DateTimeFormat('en-CA', { timeZone: 'America/Sao_Paulo', year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).formatToParts(agora).reduce((o, p) => (o[p.type] = p.value, o), {})
    const hoje = `${partes.year}-${partes.month}-${partes.day}`
    if (Number(partes.hour) !== 6 || Number(partes.minute) !== 0 || global.__chegoBackupFeitoHoje === hoje) return
    const pasta = path.join(DATA_DIR, 'backups')
    fs.mkdirSync(pasta, { recursive: true })
    if (fs.existsSync(ARQUIVO)) fs.copyFileSync(ARQUIVO, path.join(pasta, `fila-${hoje}.json`))
    const fonte = path.join(__dirname, 'index.js')
    if (fs.existsSync(fonte)) fs.copyFileSync(fonte, path.join(pasta, `index-${hoje}.js`))
    // Retém os últimos 30 backups diários para evitar crescimento ilimitado.
    const arquivos = fs.readdirSync(pasta).filter(n => /^(fila|index)-\d{4}-\d{2}-\d{2}\./.test(n)).sort()
    for (const nome of arquivos.slice(0, Math.max(0, arquivos.length - 60))) { try { fs.unlinkSync(path.join(pasta, nome)) } catch {} }
    global.__chegoBackupFeitoHoje = hoje
    console.log(`💾 Backup diário concluído: ${pasta} (${hoje})`)
  } catch (e) { console.error('Falha no backup diário:', e.message) }
}

/* =====================================
   ZERAR LISTA ÀS 06:00
===================================== */

function verificarZerarLista() {

  const agora = new Date()
  const partesHora = new Intl.DateTimeFormat('en-CA', { timeZone: 'America/Sao_Paulo', year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).formatToParts(agora).reduce((o,p) => (o[p.type] = p.value, o), {})
  const hora = Number(partesHora.hour)
  const minuto = Number(partesHora.minute)

  if (
    hora !== 6 ||
    minuto !== 0
  ) {
    return
  }

  const hoje = `${partesHora.year}-${partesHora.month}-${partesHora.day}`

  if (
    estado.ultimaLimpeza === hoje
  ) {
    return
  }

  finalizarTodasSessoesOnline()
  estado.online = []
  estado.espera = []
  estado.feriado = false
  ajustarLimiteFila()
  // Mantém o estado compartilhado de g1 alinhado com a limpeza diária;
  // sem isso, a fila em memória podia estar vazia e a lista usar dados antigos.
  sincronizarFilaCompartilhadaComLista()

  estado.ultimaLimpeza = hoje

  salvar()

  console.log(
    '🧹 LISTA ONLINE E ESPERA ZERADAS ÀS 06:00'
  )
}


/* =====================================
   TEXTO DA MENSAGEM
===================================== */

function obterTexto(msg) {

  return (
    msg.message?.conversation ||
    msg.message?.extendedTextMessage?.text ||
    msg.message?.imageMessage?.caption ||
    msg.message?.videoMessage?.caption ||
    ''
  ).trim()
}


/* =====================================
   ID DO USUÁRIO
===================================== */

function obterId(msg) {

  return jidNormalizedUser(
    msg.key.participant ||
    msg.key.remoteJid
  )
}


/* =====================================
   NOME DO USUÁRIO
===================================== */

function obterNome(msg) {

  return (
    msg.pushName ||
    'Motoboy'
  )
}


/* =====================================
   ID DA MENSAGEM RESPONDIDA
===================================== */

function obterMensagemRespondida(msg) {
  const mensagem = msg?.message || {}
  return (
    mensagem.extendedTextMessage?.contextInfo?.stanzaId ||
    mensagem.imageMessage?.contextInfo?.stanzaId ||
    mensagem.videoMessage?.contextInfo?.stanzaId ||
    mensagem.stickerMessage?.contextInfo?.stanzaId ||
    mensagem.documentMessage?.contextInfo?.stanzaId ||
    mensagem.audioMessage?.contextInfo?.stanzaId ||
    mensagem.viewOnceMessage?.message?.extendedTextMessage?.contextInfo?.stanzaId ||
    mensagem.viewOnceMessageV2?.message?.extendedTextMessage?.contextInfo?.stanzaId ||
    null
  )
}


/* =====================================
   LIMITE DE ONLINE
===================================== */

function limiteAtual() {
  if (estado?.feriado) return Infinity
  // Aos sábados e domingos, não há limite de entregadores online.
  // Usa a data e o horário de Brasília, independentemente do fuso do servidor.
  const agora = new Date()
  const diaBrasilia = new Intl.DateTimeFormat('en-US', {
    timeZone: 'America/Sao_Paulo', weekday: 'short'
  }).format(agora)
  if (diaBrasilia === 'Sat' || diaBrasilia === 'Sun') return Infinity
  const horaBrasilia = Number(new Intl.DateTimeFormat('en-US', {
    timeZone: 'America/Sao_Paulo', hour: '2-digit', hourCycle: 'h23'
  }).format(agora))
  return horaBrasilia < 12 ? 5 : 8
}

/* =====================================
   VERIFICAR BLOQUEIO
===================================== */

function estaBloqueado(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return false
  const agora = Date.now()
  if (!Array.isArray(estado.bloqueiosAutomaticosEscala)) estado.bloqueiosAutomaticosEscala = []
  const expirados = estado.bloqueiosAutomaticosEscala.filter(x => Number(x.ate || 0) <= agora)
  if (expirados.length) {
    const idsExpirados = new Set(expirados.map(x => jidNormalizedUser(x.id)).filter(Boolean))
    estado.bloqueiosAutomaticosEscala = estado.bloqueiosAutomaticosEscala.filter(x => Number(x.ate || 0) > agora)
    for (const idExp of idsExpirados) {
      if (!estado.bloqueiosAutomaticosEscala.some(x => jidNormalizedUser(x.id) === idExp)) {
        estado.bloqueados = estado.bloqueados.filter(x => jidNormalizedUser(x) !== idExp)
        estado.bloqueadosSemana = estado.bloqueadosSemana.filter(x => jidNormalizedUser(x) !== idExp)
      }
    }
    salvar()
  }
  const bloqueioAutomaticoAtivo = estado.bloqueiosAutomaticosEscala.some(x => jidNormalizedUser(x.id) === usuario && Number(x.inicio || 0) <= agora && Number(x.ate || 0) > agora)
  const bloqueioManualAtivo =
    estado.bloqueados.some(x => jidNormalizedUser(x) === usuario) ||
    estado.bloqueadosSemana.some(x => jidNormalizedUser(x) === usuario)
  return bloqueioAutomaticoAtivo || bloqueioManualAtivo
}


/* =====================================
   VERIFICAR SE JÁ ESTÁ EM ALGUMA FILA
===================================== */

function estaNaFila(id) {
  const usuario = jidNormalizedUser(String(id || ''))
  if (!usuario) return false
  return (Array.isArray(estado.online) ? estado.online : []).some(p => jidNormalizedUser(String(p?.id || '')) === usuario) ||
    (Array.isArray(estado.espera) ? estado.espera : []).some(p => jidNormalizedUser(String(p?.id || '')) === usuario)
}

/* =====================================
   RECONCILIAR E PROMOVER A FILA
===================================== */

function ajustarLimiteFila() {
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []
  const limite = limiteAtual()

  // Se o limite diminuiu, os últimos ONLINE passam para o início da espera
  // na mesma ordem em que saíram da lista. Nenhum entregador é duplicado.
  while (Number.isFinite(limite) && estado.online.length > limite) {
    const excedente = estado.online.pop()
    const id = jidNormalizedUser(String(excedente?.id || ''))
    if (!id) continue
    excedente.id = id
    const existeOnline = estado.online.some(p => jidNormalizedUser(String(p?.id || '')) === id)
    const indiceEspera = estado.espera.findIndex(p => jidNormalizedUser(String(p?.id || '')) === id)
    if (!existeOnline && indiceEspera === -1) {
      // Ao sair de ONLINE para ESPERA, encerra o período online registrado.
      finalizarSessaoOnline(id)
      estado.espera.unshift(excedente)
    }
  }
}

function promoverEspera() {
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []

  // Primeiro saneia ONLINE mantendo a ordem existente e a primeira ocorrência.
  const idsOnline = new Set()
  const onlineNormalizados = []
  const sessoesParaFinalizar = new Set()
  for (const pessoa of estado.online) {
    const id = jidNormalizedUser(String(pessoa?.id || ''))
    if (!pessoa || !id || idsOnline.has(id)) continue
    if (estaBloqueado(id)) {
      sessoesParaFinalizar.add(id)
      continue
    }
    pessoa.id = id
    idsOnline.add(id)
    onlineNormalizados.push(pessoa)
  }
  estado.online = onlineNormalizados
  for (const id of sessoesParaFinalizar) finalizarSessaoOnline(id)

  // A espera também fica única, cronológica e sem quem já está ONLINE/bloqueado.
  const idsVistos = new Set(idsOnline)
  const esperaNormalizada = []
  for (const pessoa of estado.espera) {
    const id = jidNormalizedUser(String(pessoa?.id || ''))
    if (!pessoa || !id || idsVistos.has(id) || estaBloqueado(id)) continue
    pessoa.id = id
    idsVistos.add(id)
    esperaNormalizada.push(pessoa)
  }
  estado.espera = esperaNormalizada

  ajustarLimiteFila()
  const limite = limiteAtual()
  while (estado.online.length < limite && estado.espera.length) {
    const proximo = estado.espera.shift()
    const id = jidNormalizedUser(String(proximo?.id || ''))
    if (!id || estaBloqueado(id) || idsOnline.has(id)) continue
    proximo.id = id
    estado.online.push(proximo)
    // A sessão de tempo online começa quando a pessoa realmente ocupa uma vaga ONLINE,
    // não enquanto aguarda na fila ESPERA.
    iniciarSessaoOnline(id, proximo.nome || 'Entregador')
    idsOnline.add(id)
  }
  sincronizarFilaCompartilhadaComLista()
}

/* =====================================
   LIMPAR DUPLICADOS
===================================== */

function limparDuplicados() {
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []
  const vistos = new Set()
  const normalizarColecao = (colecao) => colecao.filter(pessoa => {
    const id = jidNormalizedUser(String(pessoa?.id || ''))
    if (!pessoa || !id || vistos.has(id)) return false
    pessoa.id = id
    vistos.add(id)
    pessoa.perdasConsecutivas = obterPerdasConsecutivas(id)
    return true
  })
  estado.online = normalizarColecao(estado.online)
  estado.espera = normalizarColecao(estado.espera)
  promoverEspera()
  sincronizarFilaCompartilhadaComLista()
  salvar()
}

function registrarEntregador(id, nome) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return null

  const existente = estado.entregadores.find(x => x.id === usuario)

  if (existente) {
    if (nome && nome !== 'Motoboy') existente.nome = nome
    existente.perdasConsecutivas = Math.max(
      0,
      Number(existente.perdasConsecutivas) || 0
    )
    // Limite individual de entregas simultâneas.
    // null = sem limite.
    if (
      existente.limiteEntregas !== null &&
      existente.limiteEntregas !== undefined &&
      (!Number.isInteger(Number(existente.limiteEntregas)) || Number(existente.limiteEntregas) < 1)
    ) {
      existente.limiteEntregas = null
    }
    if (existente.limiteEntregas === undefined) existente.limiteEntregas = null
    if (existente.statusManual !== '🔴' && existente.statusManual !== '🟢') existente.statusManual = null
    if (!['🟢','🚀','🟠','🔴'].includes(existente.statusOperacional)) existente.statusOperacional = existente.statusManual || '🟢'
    return existente
  }

  const novo = {
    id: usuario,
    nome: nome || 'Motoboy',
    perdasConsecutivas: 0,
    limiteEntregas: null,
    statusManual: null,
    statusOperacional: '🟢'
  }

  estado.entregadores.push(novo)
  return novo
}

function obterLimiteEntregas(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return null

  // A configuração global tem prioridade; migra também limites antigos já salvos por empresa.
  const global = Number(limitesEntregasGlobais[usuario])
  if (Number.isInteger(global) && global >= 1) return global

  for (const chave of Object.keys(empresas || {})) {
    const cadastro = (empresas[chave]?.estado?.entregadores || []).find(
      x => jidNormalizedUser(x.id) === usuario
    )
    const limite = Number(cadastro?.limiteEntregas)
    if (Number.isInteger(limite) && limite >= 1) return limite
  }
  return null
}

function definirLimiteEntregas(id, limite) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return false

  if (limite === null) {
    delete limitesEntregasGlobais[usuario]
    // Remove limites antigos em todos os cadastros para que não reapareçam.
    for (const chave of Object.keys(empresas || {})) {
      const cadastro = (empresas[chave]?.estado?.entregadores || []).find(
        x => jidNormalizedUser(x.id) === usuario
      )
      if (cadastro) cadastro.limiteEntregas = null
    }
    registrarEntregador(usuario)
    salvar()
    return true
  }

  const valor = Number(limite)
  if (!Number.isInteger(valor) || valor < 1) return false

  limitesEntregasGlobais[usuario] = valor
  // Mantém o cadastro local compatível com versões antigas do bot.
  const entregador = registrarEntregador(usuario)
  if (entregador) entregador.limiteEntregas = valor
  salvar()
  return true
}

function quantidadePendenteDaEntrega(entrega) {
  if (!entrega || entrega.concluida) return 0
  const fracaoTotal = Number(entrega?.fracionado?.total)
  if (Number.isSafeInteger(fracaoTotal) && fracaoTotal > 0) {
    const atual = Math.max(0, Math.min(fracaoTotal, Number(entrega?.fracionado?.ultimoAtual) || 0))
    return Math.max(0, fracaoTotal - atual)
  }
  return Math.max(1, Number(entrega?.quantidadeEntregas) || 1)
}

function quantidadeEntregasAtivas(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return 0

  // Limite GLOBAL por entregador: considera todos os grupos/empresas.
  if (empresas?.[empresaAtual]) empresas[empresaAtual].estado = estado

  let total = 0
  const mensagensContadas = new Set()
  for (const chave of Object.keys(empresas || {})) {
    const entregas = empresas[chave]?.estado?.entregasAceitas || []
    for (let i = 0; i < entregas.length; i++) {
      const entrega = entregas[i]
      if (jidNormalizedUser(entrega?.entregadorId || '') !== usuario || entrega?.concluida) continue

      const idMensagem = entrega?.mensagemId || entrega?.mensagem?.key?.id || entrega?.id
      const identidade = idMensagem
        ? `mensagem:${String(idMensagem)}`
        : `${chave}:indice:${i}:inicio:${Number(entrega?.aceitoEm || entrega?.enviadaEm || 0)}`
      if (mensagensContadas.has(identidade)) continue
      mensagensContadas.add(identidade)

      // Após 1/4, há três unidades ainda em andamento; o limite libera vagas
      // conforme os fracionados avançam, sem esperar o lote inteiro terminar.
      total += quantidadePendenteDaEntrega(entrega)
    }
  }
  return total
}

function excedeLimiteEntregas(id, quantidade = 1, entregaDeRota = false) {
  // O limite é global por entregador: considera todos os grupos e cada bairro/destino.
  const limite = obterLimiteEntregas(id)
  if (limite === null) return false
  return quantidadeEntregasAtivas(id) + Math.max(1, Number(quantidade) || 1) > limite
}

function podeAceitarEntrega(id, entregaDeRota = false, quantidade = 1) {
  return !excedeLimiteEntregas(id, quantidade, entregaDeRota)
}

function obterEntregadoresComLimite() {
  return (estado.entregadores || [])
    .filter(entregador => obterLimiteEntregas(entregador.id) !== null)
    .map(entregador => ({
      ...entregador,
      limiteEntregas: obterLimiteEntregas(entregador.id)
    }))
}

function obterPerdasConsecutivas(id) {
  const usuario = jidNormalizedUser(id)
  const entregador = (estado.entregadores || []).find(
    x => jidNormalizedUser(x.id) === usuario
  )

  return Math.max(
    0,
    Number(entregador?.perdasConsecutivas) || 0
  )
}

function definirPerdasConsecutivas(id, quantidade) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return

  const valor = Math.max(0, Number(quantidade) || 0)
  const entregador = registrarEntregador(usuario)

  if (entregador) {
    entregador.perdasConsecutivas = valor
  }

  const online = estado.online.find(
    x => jidNormalizedUser(x.id) === usuario
  )

  if (online) {
    online.perdasConsecutivas = valor
  }

  const espera = estado.espera.find(
    x => jidNormalizedUser(x.id) === usuario
  )

  if (espera) {
    espera.perdasConsecutivas = valor
  }
}

/* =====================================
   HISTÓRICO DE TEMPO ONLINE
===================================== */
function iniciarSessaoOnline(id, nome) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return
  if (!Array.isArray(estado.sessoesOnline)) estado.sessoesOnline = []
  const aberta = estado.sessoesOnline.find(s => jidNormalizedUser(s.entregadorId) === usuario && !s.finalizadaEm)
  if (aberta) {
    if (nome) aberta.entregadorNome = nome
    return
  }
  estado.sessoesOnline.push({ entregadorId: usuario, entregadorNome: nome || 'Entregador', iniciadaEm: Date.now(), finalizadaEm: null })
  // Persiste a sessão no momento em que o entregador entra na fila.
  salvar()
}

function finalizarSessaoOnline(id, quando = Date.now()) {
  const usuario = jidNormalizedUser(id)
  if (!usuario || !Array.isArray(estado.sessoesOnline)) return
  let alterou = false
  for (const sessao of estado.sessoesOnline) {
    if (jidNormalizedUser(sessao.entregadorId) === usuario && !sessao.finalizadaEm) {
      sessao.finalizadaEm = quando
      alterou = true
    }
  }
  if (alterou) salvar()
}

function finalizarTodasSessoesOnline(quando = Date.now()) {
  if (!Array.isArray(estado.sessoesOnline)) estado.sessoesOnline = []
  let alterou = false
  for (const sessao of estado.sessoesOnline) if (!sessao.finalizadaEm) { sessao.finalizadaEm = quando; alterou = true }
  if (alterou) salvar()
}

/* =====================================
   COLOCAR ONLINE
===================================== */

function colocarOnline(id, nome) {
  const usuario = jidNormalizedUser(String(id || ''))
  if (!usuario) return false

  registrarEntregador(usuario, nome)
  const perdasConsecutivas = obterPerdasConsecutivas(usuario)

  if (estaBloqueado(usuario)) {
    finalizarSessaoOnline(usuario)
    estado.online = (estado.online || []).filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
    estado.espera = (estado.espera || []).filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
    promoverEspera()
    sincronizarFilaCompartilhadaComLista()
    salvar()
    return false
  }

  const online = (estado.online || []).find(p => jidNormalizedUser(String(p?.id || '')) === usuario)
  const espera = (estado.espera || []).find(p => jidNormalizedUser(String(p?.id || '')) === usuario)
  if (online || espera) {
    const existente = online || espera
    existente.id = usuario
    if (nome && nome !== 'Motoboy') existente.nome = nome
    existente.perdasConsecutivas = perdasConsecutivas
    if (online) estado.espera = estado.espera.filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
    // Não ultrapassa quem já está na fila de espera; promove apenas os primeiros.
    promoverEspera()
    sincronizarFilaCompartilhadaComLista()
    salvar()
    return false
  }

  ajustarLimiteFila()
  const pessoa = {
    id: usuario,
    nome: nome || 'Motoboy',
    entrou: Date.now(),
    perdasConsecutivas
  }
  if (estado.online.length < limiteAtual()) {
    estado.online.push(pessoa)
    iniciarSessaoOnline(usuario, nome || 'Motoboy')
  } else {
    // Entrar na ESPERA não deve contar como tempo ONLINE.
    estado.espera.push(pessoa)
  }

  promoverEspera()
  sincronizarFilaCompartilhadaComLista()
  salvar()
  return true
}

/* =====================================
   COLOCAR OFFLINE
===================================== */

function colocarOffline(id) {
  const usuario = jidNormalizedUser(String(id || ''))
  const compararUsuario = (valor) => mesmoJid(valor, usuario)
  if (!usuario) return false
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []

  // A menção do WhatsApp pode chegar com uma forma de JID diferente da
  // guardada na fila (por exemplo, sufixo de dispositivo). Usar a mesma
  // comparação normalizada em detecção e remoção evita um OFF aparentemente aceito.
  const onlineAntes = estado.online.length
  const esperaAntes = estado.espera.length
  const tinhaLugar = estado.online.some(p => compararUsuario(p?.id)) ||
    estado.espera.some(p => compararUsuario(p?.id))
  finalizarSessaoOnline(usuario)
  estado.online = estado.online.filter(p => !compararUsuario(p?.id))
  estado.espera = estado.espera.filter(p => !compararUsuario(p?.id))
  if (tinhaLugar) promoverEspera()
  sincronizarFilaCompartilhadaComLista()
  salvar()
  console.log(`[LISTA-OFF] alvo=${usuario}; encontrado=${tinhaLugar}; online=${onlineAntes}->${estado.online.length}; espera=${esperaAntes}->${estado.espera.length}; empresa=${empresaAtual}`)
  return tinhaLugar
}

/* =====================================
   LIBERAR ENTREGAS DE QUEM PERDEU A VEZ
===================================== */

function colocarEntregasDoEntregadorEmDisputa(id, motivo = 'final') {
  const usuario = jidNormalizedUser(id)
  if (!usuario || !Array.isArray(estado.corridas)) return 0

  let alteradas = 0
  const agora = Date.now()

  for (const corrida of estado.corridas) {
    if (!corrida) continue
    const responsavel = jidNormalizedUser(corrida.entregadorResponsavelId || '')
    const atribuidaAoUsuario = responsavel === usuario

    // Libera somente as corridas deste entregador. A condição antiga
    // também limpava disputas pertencentes a OUTROS entregadores.
    // Corridas antigas em disputa com vínculo do mesmo usuário continuam
    // sendo corrigidas aqui, sem afetar ninguém mais.
    if (!atribuidaAoUsuario) continue

    // Guarda o responsável anterior apenas para auditoria. A corrida fica
    // sem dono e qualquer ONLINE pode aceitá-la quando estiver em disputa.
    if (responsavel) {
      corrida.responsavelAnteriorId = responsavel
      corrida.responsavelAnteriorNome = corrida.entregadorResponsavelNome || corrida.responsavelAnteriorNome || null
      corrida.entregadorResponsavelId = null
      corrida.entregadorResponsavelNome = null
    }
    corrida.motivoDisputa = motivo
    corrida.disputa = true
    corrida.alertaInicio = agora
    corrida.alertasEnviados = 0
    corrida.ultimoAlerta = 0
    alteradas++
    console.log(`ENTREGA LIBERADA PARA DISPUTA: corrida ${corrida.id} | responsável anterior ${corrida.responsavelAnteriorNome || responsavel || 'nenhum'} | motivo ${motivo}`)
  }

  if (alteradas) salvar()
  return alteradas
}

/* =====================================
   ENTREGADOR VAI PARA O FINAL
===================================== */

// A fila ONLINE/ESPERA é a mesma para os dois grupos da empresa:
// o grupo g1 exibe a lista e o grupo g2 recebe os pedidos e os INDO.
// Persistimos imediatamente a fila compartilhada para que uma publicação
// iniciada antes do finally de processarMensagemInterna já veja a nova ordem.
function sincronizarFilaCompartilhadaComLista() {
  const empresa = empresas?.[empresaAtual]
  if (!empresa) return false
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []

  // A fila operacional é a fonte de verdade. ONLINE tem prioridade caso
  // algum caminho antigo tenha deixado o mesmo entregador nas duas filas.
  const idsOnline = new Set()
  const onlineLimpo = []
  for (const pessoa of estado.online) {
    const id = jidNormalizedUser(String(pessoa?.id || ''))
    if (!pessoa || !id || idsOnline.has(id)) continue
    pessoa.id = id
    idsOnline.add(id)
    onlineLimpo.push(pessoa)
  }
  const idsTotais = new Set(idsOnline)
  const esperaLimpa = []
  for (const pessoa of estado.espera) {
    const id = jidNormalizedUser(String(pessoa?.id || ''))
    if (!pessoa || !id || idsTotais.has(id)) continue
    pessoa.id = id
    idsTotais.add(id)
    esperaLimpa.push(pessoa)
  }
  const mudou = onlineLimpo.length !== estado.online.length || esperaLimpa.length !== estado.espera.length
  estado.online = onlineLimpo
  estado.espera = esperaLimpa
  if (mudou) console.warn(`[FILA] Integridade reconciliada antes de sincronizar a lista | empresa=${empresaAtual} | online=${estado.online.length} | espera=${estado.espera.length}`)

  if (!empresa.estadosPorGrupo || typeof empresa.estadosPorGrupo !== 'object') empresa.estadosPorGrupo = {}
  if (!empresa.estadosPorGrupo.g1 || typeof empresa.estadosPorGrupo.g1 !== 'object') empresa.estadosPorGrupo.g1 = {}
  const escopoLista = empresa.estadosPorGrupo.g1
  const onlineCanonico = structuredClone(estado.online)
  const esperaCanonica = structuredClone(estado.espera)

  // empresa.estado é a única fonte canônica. Remova cópias antigas migradas
  // de versões anteriores para impedir que algum fluxo volte a lê-las.
  delete escopoLista.online
  delete escopoLista.espera
  if (!empresa.estado || typeof empresa.estado !== 'object') empresa.estado = estadoVazio()
  empresa.estado.online = structuredClone(onlineCanonico)
  empresa.estado.espera = structuredClone(esperaCanonica)

  // ONLINE/ESPERA existem em um único lugar: empresa.estado.
  // estadosPorGrupo guarda somente metadados de cada grupo, nunca outra fila.
  for (const escopoGrupo of Object.values(empresa.estadosPorGrupo)) {
    if (!escopoGrupo || typeof escopoGrupo !== 'object') continue
    delete escopoGrupo.online
    delete escopoGrupo.espera
  }
  return true
}

function mandarParaFinal(id, motivo = 'final') {
  const usuario = jidNormalizedUser(String(id || ''))
  if (!usuario || estaBloqueado(usuario)) return false
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []
  const indiceAnterior = estado.online.findIndex(p => jidNormalizedUser(String(p?.id || '')) === usuario)
  const eraOnline = indiceAnterior !== -1
  const pessoa = eraOnline ? estado.online[indiceAnterior] : estado.espera.find(p => jidNormalizedUser(String(p?.id || '')) === usuario)
  if (!pessoa) {
    console.warn(`[FILA] Não foi possível mover ao final: entregador não encontrado na fila da empresa ${empresaAtual}.`)
    return false
  }

  const entregasPendentes = (estado.corridas || []).filter(c =>
    c && jidNormalizedUser(String(c.entregadorResponsavelId || '')) === usuario
  )
  if (motivo === 'proximo' || motivo === 'perda-de-vez') colocarEntregasDoEntregadorEmDisputa(usuario, motivo)

  estado.online = estado.online.filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
  estado.espera = estado.espera.filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
  if (eraOnline && motivo === 'aceite') {
    // Um aceite de disputa põe quem aceitou no fim da fila ativa, mas mantém
    // depois dele quem já havia perdido a vez. Isso produz B,D,C,A no exemplo
    // em que A perdeu a vez e C aceitou a entrega em disputa.
    const perdeuVezDepois = estado.online.filter(p => p?.perdeuVezPendenteOrdem === true)
    const filaNormal = estado.online.filter(p => p?.perdeuVezPendenteOrdem !== true)
    delete pessoa.perdeuVezPendenteOrdem
    delete pessoa.perdeuVezEm
    estado.online = [...filaNormal, pessoa, ...perdeuVezDepois]
  } else if (eraOnline) {
    estado.online.push(pessoa)
  } else {
    estado.espera.push(pessoa)
  }

  if (motivo === 'final' && entregasPendentes.length) {
    const proximoDaVez = estado.online.find(p => jidNormalizedUser(String(p?.id || '')) !== usuario) || null
    for (const corrida of entregasPendentes) {
      corrida.entregadorResponsavelId = proximoDaVez ? jidNormalizedUser(proximoDaVez.id) : null
      corrida.entregadorResponsavelNome = proximoDaVez?.nome || null
      corrida.disputa = !proximoDaVez
      corrida.motivoReatribuicao = 'final'
      corrida.reatribuidaEm = Date.now()
      corrida.avisoPrivadoEnviado = false
    }
  }

  promoverEspera()
  sincronizarFilaCompartilhadaComLista()
  salvar()
  const indiceNovo = estado.online.findIndex(p => jidNormalizedUser(p.id) === usuario)
  console.log(`[FILA] Movimento para o final concluído | empresa=${empresaAtual} | motivo=${motivo} | posição=${eraOnline ? indiceAnterior + 1 : 'espera'} -> ${eraOnline ? indiceNovo + 1 : 'espera'} | fila sincronizada com g1`)
  return true
}

/* =====================================
   PRÓXIMO
===================================== */

function proximo() {
  if (!Array.isArray(estado.online) || estado.online.length === 0) return false

  const atual = estado.online[0]
  if (!atual || !atual.id) return false

  // O entregador que estava na vez vai para o final e suas entregas
  // pendentes entram em disputa; as entregas dos demais não são afetadas.
  return mandarParaFinal(atual.id, 'proximo')
}


/* =====================================
   PERDA DA VEZ — PROCESSAMENTO ÚNICO
===================================== */

async function processarPerdaDeVez(sock, corrida, opcoes = {}) {
  if (!corrida || corrida.perdaDeVezProcessada) return false

  // Marcar ANTES de qualquer await impede que o temporizador e a mensagem
  // INDO processem a mesma perda duas vezes.
  const agora = Date.now()
  const responsavelId = jidNormalizedUser(corrida.entregadorResponsavelId || '')
  const responsavelNaFila = responsavelId && (
    estado.online.some(p => jidNormalizedUser(p.id) === responsavelId) ||
    estado.espera.some(p => jidNormalizedUser(p.id) === responsavelId)
  )

  corrida.perdaDeVezProcessada = true
  corrida.perdaDeVezEm = agora
  corrida.disputa = true
  corrida.motivoDisputa = 'perda-de-vez'
  corrida.alertaInicio = agora
  corrida.alertasEnviados = 0
  corrida.ultimoAlerta = 0

  if (responsavelId && responsavelNaFila) {
    const perdas = obterPerdasConsecutivas(responsavelId) + 1
    definirPerdasConsecutivas(responsavelId, perdas)
    const pessoa = estado.online.find(p => jidNormalizedUser(p.id) === responsavelId) ||
      estado.espera.find(p => jidNormalizedUser(p.id) === responsavelId)
    if (pessoa) {
      pessoa.perdasConsecutivas = perdas
      // Mantém o entregador que perdeu a vez depois de quem aceitar a disputa.
      // Ex.: B,C,D,A -> C aceita -> B,D,C,A.
      pessoa.perdeuVezPendenteOrdem = true
      pessoa.perdeuVezEm = agora
    }

    const moveu = mandarParaFinal(responsavelId, 'perda-de-vez')
    // Mesmo que o entregador esteja bloqueado ou tenha saído da fila,
    // a solicitação não pode continuar presa ao responsável anterior.
    if (!moveu) colocarEntregasDoEntregadorEmDisputa(responsavelId, 'perda-de-vez')
    console.log(`PERDA DE VEZ: ${pessoa?.nome || responsavelId} | ${perdas} ocorrência(s) | fila atualizada e entregas liberadas para disputa`)
  } else if (responsavelId) {
    colocarEntregasDoEntregadorEmDisputa(responsavelId, 'perda-de-vez')
  }

  // A corrida atual pode ter sido liberada pela rotina acima; mantém o estado
  // idempotente mesmo em registros legados ou quando não havia responsável.
  corrida.disputa = true
  corrida.motivoDisputa = 'perda-de-vez'
  if (!Number(corrida.alertaInicio)) corrida.alertaInicio = agora
  if (!Number.isFinite(Number(corrida.alertasEnviados))) corrida.alertasEnviados = 0
  if (!Number.isFinite(Number(corrida.ultimoAlerta))) corrida.ultimoAlerta = 0
  salvar()

  // A perda da vez também altera a ordem da fila exibida no grupo g1.
  // Tenta editar a mensagem existente após a perda da vez; se a edição não for
  // possível, a rotina de publicação cria uma nova lista e guarda sua referência.
  if (opcoes.publicarLista !== false && responsavelId && responsavelNaFila && sock?.sendMessage) {
    try {
      await publicarListaEmpresaNoEstadoDoGrupo(sock, empresaAtual, 'g1', {
        apenasEditarExistente: true,
        forcarAtualizacao: true
      })
    } catch (erroListaPerdaVez) {
      console.error('[LISTA] Não foi possível editar a lista após perda da vez:', erroListaPerdaVez?.message || erroListaPerdaVez)
    }
  }

  // Seta o sinal antes de aguardar/rede para impedir avisos duplicados.
  if (responsavelId && !corrida.avisoPerdaEnviado) {
    corrida.avisoPerdaEnviado = true
    salvar()
    if (sock?.sendMessage) {
      try {
        await new Promise(resolve => setTimeout(resolve, 5000))
        const mensagemCitacao = corrida.mensagemOriginalKey && corrida.mensagemOriginalConteudo
          ? { key: corrida.mensagemOriginalKey, message: corrida.mensagemOriginalConteudo }
          : null
        await sock.sendMessage(responsavelId, {
          text: '❌ *VOCÊ PERDEU A VEZ DESTA ENTREGA*\n\nA entrega foi liberada para os outros entregadores. Toque na mensagem citada abaixo para abrir a mensagem original da empresa.',
          mentions: [responsavelId]
        }, mensagemCitacao ? { quoted: mensagemCitacao } : {})
      } catch (e) {
        console.log(`Erro ao avisar perda de vez no privado (${corrida.entregadorResponsavelNome || responsavelId}):`, e.message)
      }
    }
  }

  salvar()
  return true
}

/* =====================================
   CRIAR SOLICITAÇÃO DE ENTREGA
===================================== */

// A disputa libera sempre após 2 minutos pelo minuto do relógio,
// ignorando os segundos e quaisquer prazos antigos gravados em prazo/prazoRota.
// Ex.: solicitação às 08:42:56 libera às 08:44:00.
function prazoDeDisputaAtingido(corrida, agora = Date.now()) {
  if (!corrida) return false
  const enviadaEm = Number(corrida.enviadaEm || corrida.inicio || 0)
  // Registro legado sem horário de origem não pode continuar preso por um
  // prazo legado inconsistente: libera a disputa.
  if (!Number.isFinite(enviadaEm) || enviadaEm <= 0) return true
  const minutoSolicitacao = Math.floor(enviadaEm / 60000)
  const minutoAtual = Math.floor(agora / 60000)
  return minutoAtual >= minutoSolicitacao + 2
}

function criarCorrida(msg, analiseGemini = null) {

  const agora = Date.now()
  const empresaId = jidNormalizedUser(
    msg?.key?.participant ||
    msg?.key?.remoteJid ||
    ''
  )
  const empresaNome = msg?.pushName || 'Empresa'
  const mensagemId = msg?.key?.id || null

  // Se a rota anterior expirou, apenas encerra a prioridade temporária.
  // Expiração de rota não é motivo para alterar a posição na fila.
  if (estado.rotaAtiva && agora >= Number(estado.rotaAtiva.expiraEm || 0)) estado.rotaAtiva = null

  const inicio = new Date(agora)

  // Ignora os segundos: uma entrega às 12:36:56 libera disputa às 12:38:00.
  const inicioDoMinuto = Math.floor(agora / 60000) * 60000
  const prazo = inicioDoMinuto + (2 * 60 * 1000)

  // PRIORIDADE DE ROTA DA MESMA EMPRESA:
  // A prioridade dura 2 minutos a partir do minuto da primeira solicitação.
  // Entregas de outras empresas entre as duas não interrompem essa rota.
  // Se a primeira já foi aceita e existe uma rota ativa desta empresa,
  // preserva o entregador dono da rota.
  const janelaRota = agora - 2 * 60 * 1000
  const rotaDaMesmaEmpresa = estado.rotaAtiva &&
    agora < Number(estado.rotaAtiva.expiraEm || 0) &&
    estado.rotaAtiva.empresaId === empresaId
      ? estado.rotaAtiva
      : null

  const corridaAnteriorMesmaEmpresa = (estado.corridas || [])
    .filter(item =>
      item &&
      item.empresaId === empresaId &&
      Number(item.enviadaEm || item.inicio || 0) >= janelaRota &&
      Number(item.enviadaEm || item.inicio || 0) <= agora &&
      !prazoDeDisputaAtingido(item, agora) &&
      item.entregadorResponsavelId
    )
    .sort((a, b) => Number(a.enviadaEm || a.inicio || 0) - Number(b.enviadaEm || b.inicio || 0))[0]

  const entregaAceitaMesmaEmpresa = (estado.entregasAceitas || [])
    .filter(item =>
      item &&
      item.empresaId === empresaId &&
      Number(item.enviadaEm || item.aceitoEm || 0) >= janelaRota &&
      Number(item.enviadaEm || item.aceitoEm || 0) <= agora &&
      !item.entregaDeRota &&
      Math.floor(Number(item.enviadaEm || item.aceitoEm || 0) / 60000) + 2 > Math.floor(agora / 60000)
    )
    .sort((a, b) => Number(a.aceitoEm || 0) - Number(b.aceitoEm || 0))[0]

  let responsavel = null
  const responsavelRotaId = rotaDaMesmaEmpresa?.entregadorId ||
    corridaAnteriorMesmaEmpresa?.entregadorResponsavelId ||
    entregaAceitaMesmaEmpresa?.entregadorId ||
    null

  if (responsavelRotaId) {
    responsavel = estado.online.find(pessoa =>
      jidNormalizedUser(pessoa.id) === jidNormalizedUser(responsavelRotaId)
    ) || null
  }

  // Para entregas sem vínculo de rota, mantém a distribuição normal da fila.
  if (!responsavel) {
    const pendentesAntes = (estado.corridas || []).filter(item => !item.disputa).length
    const posicaoResponsavel = estado.online.length > 0
      ? pendentesAntes % estado.online.length
      : -1
    responsavel = posicaoResponsavel >= 0 ? estado.online[posicaoResponsavel] : null
  }

  estado.contadorCorrida++

  const corridaBaseRota = (estado.corridas || [])
    .filter(item => item && item.empresaId === empresaId &&
      Number(item.enviadaEm || item.inicio || 0) >= janelaRota &&
      Number(item.enviadaEm || item.inicio || 0) <= agora &&
      !prazoDeDisputaAtingido(item, agora))
    .sort((a, b) => Number(a.enviadaEm || a.inicio || 0) - Number(b.enviadaEm || b.inicio || 0))[0] || null
  const prazoRota = corridaBaseRota
    ? Number(corridaBaseRota.prazoRota || corridaBaseRota.prazo || prazo)
    : prazo

  const corrida = {
    id: estado.contadorCorrida,
    mensagemId,
    mensagemOriginalKey: msg?.key ? { ...msg.key } : null,
    mensagemOriginalConteudo: msg?.message || null,
    empresaId,
    empresaNome,
    inicio: inicio.getTime(),
    prazo,
    prazoRota,
    enviadaEm: agora,
    entregadorResponsavelId: responsavel ? jidNormalizedUser(responsavel.id) : null,
    entregadorResponsavelNome: responsavel?.nome || null,
    textoEntrega: obterTexto(msg) || '[entrega enviada como mídia]',
    bairrosIdentificados: extrairBairrosPatos(obterTexto(msg)).length
      ? extrairBairrosPatos(obterTexto(msg))
      : (Array.isArray(analiseGemini?.neighborhoods) ? analiseGemini.neighborhoods : []),
    quantidadeEntregas: Math.max(1, extrairBairrosPatos(obterTexto(msg)).length || (analiseGemini?.neighborhoods || []).length),
    avisoPrivadoEnviado: false,
    avisoPerdaEnviado: false,
    disputa: false,
    alertaInicio: null,
    alertasEnviados: 0,
    ultimoAlerta: 0
  }

  estado.corridas.push(corrida)

  // Histórico persistente de solicitações para ranking por empresa.
  // Uma mensagem só pode entrar uma vez; entregas múltiplas em bairros distintos
  // contam pela quantidade de destinos reconhecidos (mínimo de uma entrega).
  if (!Array.isArray(estado.solicitacoesRelatorio)) estado.solicitacoesRelatorio = []
  if (!estado.solicitacoesRelatorio.some(item => item && item.mensagemId && item.mensagemId === mensagemId && String(item.empresaId || '') === String(empresaId || ''))) {
    estado.solicitacoesRelatorio.push({
      mensagemId,
      empresaId,
      empresaNome: empresaNome || 'Empresa',
      quantidade: Math.max(1, Number(corrida.quantidadeEntregas) || 1),
      solicitadaEm: agora,
      data: inicio.toISOString().slice(0, 10)
    })
  }

  /*
    ROTA CONDICIONAL — JANELA DE 60 SEGUNDOS

    A rota NÃO é criada apenas porque uma entrega foi aceita.
    Ela só existe quando há pelo menos duas entregas da mesma empresa
    enviadas dentro de uma janela de 60 segundos.

    Se a primeira entrega já foi aceita e uma segunda entrega da mesma
    empresa chega dentro desses 60 segundos, a rota é criada usando o
    horário em que a primeira entrega foi aceita.
  */
  if (!estado.rotaAtiva) {
    const limite60 = agora - 60 * 1000
    const aceitasRecentes = Array.isArray(estado.entregasAceitas)
      ? estado.entregasAceitas.filter(e =>
          e.empresaId === empresaId &&
          Number(e.enviadaEm || e.aceitoEm || 0) >= limite60 &&
          Number(e.enviadaEm || e.aceitoEm || 0) <= agora &&
          Math.floor(Number(e.enviadaEm || e.aceitoEm || 0) / 60000) + 2 > Math.floor(agora / 60000) &&
          !e.entregaDeRota
        )
      : []

    if (aceitasRecentes.length > 0) {
      const primeira = aceitasRecentes.sort((a, b) => Number(a.aceitoEm) - Number(b.aceitoEm))[0]
      iniciarRotaCondicional(primeira, empresaId, empresaNome)
    }
  }

  salvar()
  return corrida

}

/* =====================================
   ROTA CONDICIONAL
===================================== */

function iniciarRotaCondicional(entregaBase, empresaId, empresaNome) {
  if (!entregaBase || estado.rotaAtiva) return false

  const iniciouEm = Number(entregaBase.enviadaEm || entregaBase.aceitoEm || 0)
  if (!iniciouEm) return false

  estado.rotaAtiva = {
    id: entregaBase.rotaId || `${empresaId || 'empresa'}-${iniciouEm}`,
    empresaId: empresaId || entregaBase.empresaId || null,
    empresaNome: empresaNome || entregaBase.empresaNome || 'Empresa',
    entregadorId: jidNormalizedUser(entregaBase.entregadorId),
    entregadorNome: entregaBase.entregadorNome || 'Entregador',
    iniciouEm,
    expiraEm: Math.floor(iniciouEm / 60000) * 60000 + 2 * 60 * 1000,
    entregas: 1
  }

  console.log(
    `ROTA 60S ATIVADA: ${estado.rotaAtiva.entregadorNome} | ${estado.rotaAtiva.empresaNome}`
  )

  salvar()
  return true
}

/* =====================================
   ACEITAR CORRIDA
===================================== */

function capturarReferenciaMensagem(msg) {
  if (!msg?.key?.id || !msg?.key?.remoteJid) return null
  return {
    id: String(msg.key.id),
    remoteJid: String(msg.key.remoteJid),
    participant: String(msg.key.participant || msg.key.remoteJid || ''),
    fromMe: !!msg.key.fromMe,
    timestamp: Number(msg.messageTimestamp || Math.floor(Date.now() / 1000)) * 1000,
    message: msg.message || null,
    texto: String(obterTexto(msg) || '').slice(0, 500)
  }
}

async function enviarReferenciaCitada(sock, jid, referencia, rotulo) {
  if (!referencia?.id || !referencia?.remoteJid || !referencia?.message) {
    const conteudo = referencia?.texto ? `
Mensagem registrada: “${referencia.texto}”` : ''
    await sock.sendMessage(jid, { text: `📌 ${rotulo}: não há uma referência completa para abrir a mensagem original.${conteudo}` })
    return false
  }

  // Recria a mesma estrutura de mensagem recebida que já funciona no aviso
  // privado de entrega atribuída: sendMessage(..., { quoted: mensagemOriginal }).
  // Não montar contextInfo manualmente: isso pode produzir uma citação visual
  // sem a referência clicável correta, sobretudo quando a origem é um grupo.
  const mensagemCitacao = {
    key: {
      remoteJid: referencia.remoteJid,
      id: referencia.id,
      participant: referencia.participant || undefined,
      fromMe: !!referencia.fromMe
    },
    message: referencia.message,
    messageTimestamp: Math.floor(Number(referencia.timestamp || Date.now()) / 1000)
  }

  try {
    await sock.sendMessage(jid, { text: `📌 ${rotulo}` }, { quoted: mensagemCitacao })
    return true
  } catch (erro) {
    console.log('Não foi possível citar mensagem do histórico:', erro?.message || erro)
    const conteudo = referencia.texto ? `
Mensagem registrada: “${referencia.texto}”` : ''
    await sock.sendMessage(jid, { text: `📌 ${rotulo}${conteudo}
Grupo de origem: ${referencia.remoteJid}` })
    return false
  }
}

function registrarEntregaAceita(corrida, id, mensagemAceiteId = null, posicaoOriginal = null, entregaDeRota = false, rotaId = null, mensagemAceite = null) {
  if (!Array.isArray(estado.entregasAceitas)) estado.entregasAceitas = []
  const usuario = jidNormalizedUser(id)
  const pessoa = estado.online.find(item => item.id === usuario) || estado.espera.find(item => item.id === usuario)
  const aceitoEm = Date.now()

  const registro = {
    mensagemId: corrida.mensagemId || null,
    corridaId: corrida.id ?? null,
    mensagemOriginalKey: corrida.mensagemOriginalKey ? { ...corrida.mensagemOriginalKey } : null,
    mensagemOriginalConteudo: corrida.mensagemOriginalConteudo || null,
    textoEntrega: corrida.textoEntrega || '',
    bairrosIdentificados: Array.isArray(corrida.bairrosIdentificados) ? [...corrida.bairrosIdentificados] : [],
    responsavelAntesAceiteId: corrida.entregadorResponsavelId || null,
    responsavelAntesAceiteNome: corrida.entregadorResponsavelNome || null,
    disputaAntesAceite: !!corrida.disputa,
    prazoAntesAceite: Number(corrida.prazo) || null,
    prazoRotaAntesAceite: Number(corrida.prazoRota) || null,
    inicioSolicitacao: Number(corrida.inicio || corrida.enviadaEm || aceitoEm),
    empresaId: corrida.empresaId || null,
    empresaNome: corrida.empresaNome || 'Empresa',
    entregadorId: usuario,
    entregadorNome: pessoa?.nome || 'Entregador',
    mensagemAceiteId: mensagemAceiteId || null,
    mensagemIndoRef: capturarReferenciaMensagem(mensagemAceite),
    mensagemFinalizacaoRef: null,
    posicaoOriginal: Number.isInteger(posicaoOriginal) ? posicaoOriginal : null,
    aceitoEm,
    enviadaEm: Number(corrida.enviadaEm || corrida.inicio || aceitoEm),
    fracionado: null,
    quantidadeEntregas: Math.max(1, Number(corrida.quantidadeEntregas) || 1),
    concluida: false,
    rotaId: rotaId || `${corrida.empresaId || 'empresa'}-${aceitoEm}`,
    entregaDeRota: !!entregaDeRota
  }

  estado.entregasAceitas.push(registro)

  // A entrega entra no histórico no momento em que é aceita (indo ou
  // atribuição do ADM). A finalização posterior não deve contá-la novamente.
  const idEventoContagem = mensagemAceiteId || `aceite-${registro.mensagemId || 'sem-id'}-${aceitoEm}`
  registrarEventoHistoricoEntrega(
    registro,
    registro.quantidadeEntregas,
    { key: { id: idEventoContagem } }
  )
  registro.eventoHistoricoMensagemId = idEventoContagem
  const eventoCriado = [...(estado.historicoEntregas || [])].reverse().find(item =>
    String(item.eventoMensagemId || '') === String(idEventoContagem) &&
    jidNormalizedUser(item.entregadorId || '') === usuario &&
    String(item.empresaId || '') === String(registro.empresaId || '')
  )
  if (eventoCriado && registro.mensagemIndoRef) eventoCriado.mensagemIndoRef = registro.mensagemIndoRef
  if (eventoCriado && Array.isArray(corrida.bairrosIdentificados)) eventoCriado.bairrosIdentificados = [...corrida.bairrosIdentificados]
  // Mesmo se o evento já existir (reentrega da mesma mensagem), não reconta
  // esta entrega quando chegar a figurinha ou o fracionamento.
  registro.contagemRegistrada = true

  definirPerdasConsecutivas(usuario, 0)
  salvar()
  return registro
}

function entregasDaMesmaEmpresaNaJanela(corrida) {
  if (!corrida) return []

  const empresaId = corrida.empresaId
  const enviadaEm = Number(corrida.enviadaEm || corrida.inicio || Date.now())

  return (estado.corridas || []).filter(item => {
    if (!item || item.empresaId !== empresaId) return false
    const outraEnviadaEm = Number(item.enviadaEm || item.inicio || 0)
    const prazoBase = Number(item.prazoRota || item.prazo || (Math.floor(outraEnviadaEm / 60000) * 60000 + 120000))
    return Math.abs(enviadaEm - outraEnviadaEm) <= 2 * 60 * 1000 && Date.now() < prazoBase
  })
}

function deveAtivarRota(corrida) {
  return entregasDaMesmaEmpresaNaJanela(corrida).length >= 2
}

function aceitarCorrida(id, mensagemRespondidaId = null, mensagemAceiteId = null, mensagemAceite = null) {

  if (!estado.corridas || estado.corridas.length === 0) return false

  const usuario = jidNormalizedUser(id)
  const estaOnline = estado.online.some(pessoa => pessoa.id === usuario)
  if (!estaOnline) return false

  if (mensagemRespondidaId) {
    const jaAceita = Array.isArray(estado.entregasAceitas) &&
      estado.entregasAceitas.some(entrega => entrega.mensagemId === mensagemRespondidaId)
    if (jaAceita) return false
  }

  let corrida

  if (mensagemRespondidaId) {
    corrida = estado.corridas.find(item => item.mensagemId === mensagemRespondidaId)
    if (!corrida) return false
  } else {
    corrida = estado.corridas[0]
  }

  // O limite individual vale para entregas normais.
  // Se a entrega fizer parte de uma rota, o limite não é aplicado.
  const rotaAtivaAntesDoAceite = estado.rotaAtiva &&
    Date.now() < Number(estado.rotaAtiva.expiraEm || 0)
      ? estado.rotaAtiva
      : null

  const mesmaRotaAntesDoAceite = rotaAtivaAntesDoAceite &&
    rotaAtivaAntesDoAceite.empresaId === corrida.empresaId &&
    jidNormalizedUser(rotaAtivaAntesDoAceite.entregadorId) === usuario

  const ativarRotaAgora = !rotaAtivaAntesDoAceite && deveAtivarRota(corrida)

  if (!podeAceitarEntrega(
    usuario,
    (!!mesmaRotaAntesDoAceite && !!rotaAtivaAntesDoAceite) || ativarRotaAgora,
    Math.max(1, Number(corrida.quantidadeEntregas) || 1)
  )) {
    return false
  }

  const rotaAtiva = estado.rotaAtiva &&
    Date.now() < Number(estado.rotaAtiva.expiraEm || 0)
      ? estado.rotaAtiva
      : null

  const mesmaRota = rotaAtiva &&
    rotaAtiva.empresaId === corrida.empresaId &&
    jidNormalizedUser(rotaAtiva.entregadorId) === usuario

  /*
    Antes do prazo, somente o entregador reservado para esta entrega aceita.
    Depois do prazo, a entrega fica em disputa e qualquer ONLINE pode aceitar.
    Corridas antigas sem responsável salvo mantêm a regra do primeiro da fila.
  */
  const responsavelId = corrida.entregadorResponsavelId
    ? jidNormalizedUser(corrida.entregadorResponsavelId)
    : ''
  const prazoExpirou = prazoDeDisputaAtingido(corrida)
  if (!corrida.disputa && !prazoExpirou && (!responsavelId || responsavelId !== usuario)) return false
  if (prazoExpirou) corrida.disputa = true

  /*
    ROTA 60S: o entregador mantém sua posição somente para escolher
    outra entrega da MESMA empresa. Uma entrega de outra empresa
    continua seguindo o funcionamento normal da fila.
  */
  const entraNaRota = !!mesmaRota
  const ativarAgora = !rotaAtiva && deveAtivarRota(corrida)

  const posicaoOriginal = estado.online.findIndex(pessoa => pessoa.id === usuario)

  const registro = registrarEntregaAceita(
    corrida,
    usuario,
    mensagemAceiteId,
    posicaoOriginal,
    entraNaRota,
    rotaAtiva?.id || null,
    mensagemAceite
  )
  alterarStatusOperacional(usuario, 'aceite')

  if (ativarAgora) {
    iniciarRotaCondicional(registro, corrida.empresaId, corrida.empresaNome)
  }

  // Aceitar uma entrega, por si só, não altera a posição na fila.
  // O entregador só vai ao final por próximo/final, comando ADM @entregador final,
  // perda da vez ou INDO respondido a uma mensagem que o Bot não reconheceu.

  const indiceCorrida = estado.corridas.indexOf(corrida)
  if (indiceCorrida !== -1) estado.corridas.splice(indiceCorrida, 1)

  salvar()
  return true
}

/* =====================================
   REVERSÃO / CANCELAMENTO DE ACEITAÇÃO
===================================== */

function removerHistoricoDaAceitacao(entrega) {
  if (!entrega || !Array.isArray(estado.historicoEntregas)) return 0
  const usuario = jidNormalizedUser(entrega.entregadorId || '')
  const empresaId = String(entrega.empresaId || '')
  const eventos = new Set([
    entrega.eventoHistoricoMensagemId,
    entrega.mensagemAceiteId
  ].filter(Boolean).map(String))
  const antes = estado.historicoEntregas.length
  estado.historicoEntregas = estado.historicoEntregas.filter(item => {
    if (jidNormalizedUser(item?.entregadorId || '') !== usuario) return true
    if (String(item?.empresaId || '') !== empresaId) return true
    if (eventos.size && eventos.has(String(item?.eventoMensagemId || ''))) return false
    // Compatibilidade com aceites antigos que não guardavam o ID do evento.
    return !(String(item?.mensagemId || '') === String(entrega.mensagemId || '') &&
      !item?.finalizadaEm && !item?.fracionamentoAtualizadoEm)
  })
  return antes - estado.historicoEntregas.length
}

function removerSolicitacaoRelatorio(mensagemId) {
  if (!mensagemId || !Array.isArray(estado.solicitacoesRelatorio)) return 0
  const antes = estado.solicitacoesRelatorio.length
  estado.solicitacoesRelatorio = estado.solicitacoesRelatorio.filter(item => String(item?.mensagemId || '') !== String(mensagemId))
  return antes - estado.solicitacoesRelatorio.length
}

function restaurarCorridaDeAceiteCancelado(entrega) {
  if (!entrega?.mensagemId || !entrega.mensagemOriginalKey || !entrega.mensagemOriginalConteudo) {
    console.log('Não foi possível restaurar a solicitação original após apagar INDO: registro legado sem mensagem original completa.')
    return false
  }
  if ((estado.corridas || []).some(item => String(item?.mensagemId || '') === String(entrega.mensagemId))) return false

  const enviadaEm = Number(entrega.enviadaEm || entrega.inicioSolicitacao || entrega.aceitoEm || Date.now())
  const prazoPadrao = Math.floor(enviadaEm / 60000) * 60000 + 120000
  const prazo = prazoPadrao
  // Ao restaurar um aceite apagado, a disputa também respeita o prazo fixo
  // de 2 minutos; prazoRotaAntesAceite é preservado apenas como dado de rota.
  const expirou = prazoDeDisputaAtingido({ enviadaEm }, Date.now())
  const disputa = !!entrega.disputaAntesAceite || expirou
  const idCorrida = Number(entrega.corridaId)
  if (!Number.isFinite(Number(estado.contadorCorrida))) estado.contadorCorrida = 0
  const novoId = Number.isSafeInteger(idCorrida) && idCorrida > 0 ? idCorrida : ++estado.contadorCorrida
  estado.contadorCorrida = Math.max(Number(estado.contadorCorrida) || 0, novoId)

  const corrida = {
    id: novoId,
    mensagemId: String(entrega.mensagemId),
    mensagemOriginalKey: { ...entrega.mensagemOriginalKey },
    mensagemOriginalConteudo: entrega.mensagemOriginalConteudo,
    empresaId: entrega.empresaId || null,
    empresaNome: entrega.empresaNome || 'Empresa',
    inicio: enviadaEm,
    enviadaEm,
    prazo,
    prazoRota: Number(entrega.prazoRotaAntesAceite) || prazo,
    entregadorResponsavelId: disputa ? null : (entrega.responsavelAntesAceiteId || entrega.entregadorId || null),
    entregadorResponsavelNome: disputa ? null : (entrega.responsavelAntesAceiteNome || entrega.entregadorNome || null),
    textoEntrega: entrega.textoEntrega || '[entrega restaurada após apagar INDO]',
    bairrosIdentificados: Array.isArray(entrega.bairrosIdentificados) ? [...entrega.bairrosIdentificados] : [],
    quantidadeEntregas: Math.max(1, Number(entrega.fracionado?.total) || Number(entrega.quantidadeEntregas) || 1),
    avisoPrivadoEnviado: false,
    avisoPerdaEnviado: false,
    disputa,
    motivoDisputa: disputa ? 'aceite-cancelado-apos-prazo' : null,
    alertaInicio: disputa ? Date.now() : null,
    alertasEnviados: 0,
    ultimoAlerta: 0
  }
  estado.corridas.push(corrida)
  salvar()
  console.log(`SOLICITAÇÃO RESTAURADA após apagar INDO | corrida ${corrida.id} | disputa=${corrida.disputa}`)
  return true
}

/* =====================================
   PROCESSAR ENTREGA APAGADA
===================================== */

async function processarEntregaApagada(sock, entrada) {

  const protocolo =
    entrada?.message?.protocolMessage ||
    entrada?.update?.message?.protocolMessage ||
    entrada?.update?.protocolMessage

  if (!protocolo) {
    return false
  }

  const mensagemApagadaId =
    protocolo?.key?.id

  if (!mensagemApagadaId) {
    return false
  }

  /*
    Primeiro verifica se a entrega ainda
    estava pendente.
    
    Se ninguém aceitou, apenas remove.
  */

  if (
    estado.corridas &&
    estado.corridas.length > 0
  ) {

    const indice =
      estado.corridas.findIndex(
        corrida =>
          corrida.mensagemId ===
          mensagemApagadaId
      )

    if (indice !== -1) {
      estado.corridas.splice(indice, 1)
      removerSolicitacaoRelatorio(mensagemApagadaId)
      salvar()
      console.log('Entrega pendente removida:', mensagemApagadaId)
      return true
    }
  }

  /*
    Se a mensagem apagada foi um INDO respondido a mensagem não reconhecida,
    restaura a posição original do entregador na fila.
  */
  if (!Array.isArray(estado.indosSemEntrega)) estado.indosSemEntrega = []
  const indiceIndoSemEntrega = estado.indosSemEntrega.findIndex(
    item => String(item?.mensagemAceiteId || '') === String(mensagemApagadaId)
  )
  if (indiceIndoSemEntrega !== -1) {
    const registroIndo = estado.indosSemEntrega.splice(indiceIndoSemEntrega, 1)[0]
    const usuarioIndo = jidNormalizedUser(registroIndo.entregadorId || '')
    const indiceAtualIndo = estado.online.findIndex(p => jidNormalizedUser(p?.id || '') === usuarioIndo)
    if (indiceAtualIndo !== -1) {
      const pessoaIndo = estado.online.splice(indiceAtualIndo, 1)[0]
      const destinoIndo = Math.max(0, Math.min(Number(registroIndo.posicaoOriginal) || 0, estado.online.length))
      estado.online.splice(destinoIndo, 0, pessoaIndo)
    }
    sincronizarFilaCompartilhadaComLista()
    salvar()
    try { await publicarLista(sock, { forcarAtualizacao: true }) }
    catch (erroListaIndoApagado) { console.log('Não foi possível atualizar a lista após apagar o INDO:', erroListaIndoApagado?.message || erroListaIndoApagado) }
    console.log(`[INDO APAGADO] Posição original restaurada para ${registroIndo.entregadorNome || usuarioIndo}.`)
    return true
  }

  /*
    Se a mensagem apagada foi o "indo" do entregador,
    ele volta para a posição que ocupava antes de aceitar.
  */
  const indiceIndoApagado =
    Array.isArray(estado.entregasAceitas)
      ? estado.entregasAceitas.findIndex(
          entrega => entrega.mensagemAceiteId === mensagemApagadaId
        )
      : -1

  if (indiceIndoApagado !== -1) {
    const entrega = estado.entregasAceitas[indiceIndoApagado]
    const usuario = jidNormalizedUser(entrega.entregadorId)
    const posicaoOriginal = Number(entrega.posicaoOriginal)

    if (Number.isInteger(posicaoOriginal) && posicaoOriginal >= 0) {
      const indiceAtual = estado.online.findIndex(pessoa => jidNormalizedUser(pessoa.id) === usuario)
      if (indiceAtual !== -1) {
        const pessoa = estado.online.splice(indiceAtual, 1)[0]
        const destino = Math.min(posicaoOriginal, estado.online.length)
        estado.online.splice(destino, 0, pessoa)
      }
    }

    // Apagar o INDO reverte também a contagem do entregador e devolve a
    // solicitação original à fila, caso a mensagem da empresa ainda exista.
    estado.entregasAceitas.splice(indiceIndoApagado, 1)
    removerHistoricoDaAceitacao(entrega)
    restaurarCorridaDeAceiteCancelado(entrega)
    alterarStatusOperacional(usuario, 'cancelamento')
    salvar()

    console.log(
      'INDO APAGADO: aceite revertido; histórico/status sincronizados; posição restaurada:',
      entrega.entregadorNome,
      '| posição:', posicaoOriginal + 1
    )
    return true
  }

  /*
    Agora verifica se algum entregador
    já tinha aceitado a entrega.
  */

  if (
    !estado.entregasAceitas ||
    estado.entregasAceitas.length === 0
  ) {
    return false
  }

  const indiceAceita =
    estado.entregasAceitas.findIndex(
      entrega =>
        entrega.mensagemId ===
        mensagemApagadaId
    )

  if (indiceAceita === -1) {
    return false
  }

  const entrega =
    estado.entregasAceitas[indiceAceita]

  /*
    Remove antes de enviar o aviso para
    impedir aviso duplicado caso o WhatsApp
    envie o evento de exclusão novamente.
  */

  estado.entregasAceitas.splice(indiceAceita, 1)
  removerHistoricoDaAceitacao(entrega)
  removerSolicitacaoRelatorio(mensagemApagadaId)
  alterarStatusOperacional(entrega.entregadorId, 'cancelamento')
  if (estado.rotaAtiva && jidNormalizedUser(estado.rotaAtiva.entregadorId) === jidNormalizedUser(entrega.entregadorId) && estado.rotaAtiva.empresaId === entrega.empresaId) {
    estado.rotaAtiva = null
  }
  salvar()

  console.log(
    'ENTREGA ACEITA CANCELADA; contagem/status sincronizados:',
    mensagemApagadaId,
    '| Empresa:',
    entrega.empresaNome,
    '| Entregador:',
    entrega.entregadorNome
  )
  return true
}


/* =====================================
   IDENTIFICAR EMPRESA
===================================== */

function ehEmpresa(msg) {

  const jid =
    msg.key?.participant ||
    msg.key?.remoteJid

  if (!jid) {
    return false
  }

  return !grupos.g1Participantes.includes(jidNormalizedUser(jid))
}


/* =====================================
   IDENTIFICAR ADM
===================================== */

async function ehADM(sock, msg) {
  const id = jidNormalizedUser(obterId(msg))
  if (!id) return false

  // Verifica os administradores atuais do G1 no momento do comando.
  // Se a consulta falhar, usa a lista atualizada de estado.g1Admins como fallback.
  try {
    const meta = await sock.groupMetadata(grupos.g1)
    const admins = (meta?.participants || [])
      .filter(p => p.admin === 'admin' || p.admin === 'superadmin')
      .map(p => jidNormalizedUser(p.id))
      .filter(Boolean)

    estado.g1Admins = admins
    salvar()
    return admins.includes(id)
  } catch (e) {
    return Array.isArray(estado.g1Admins) && estado.g1Admins.includes(id)
  }
}

function desbloquear(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return false

  const antes =
    estado.bloqueados.length +
    estado.bloqueadosSemana.length +
    (estado.bloqueiosAutomaticosEscala || []).filter(x => jidNormalizedUser(x.id) === usuario).length +
    (estado.bloqueiosTaxas || []).filter(x => jidNormalizedUser(typeof x === 'string' ? x : x.id) === usuario).length

  // Compara JIDs normalizados: o WhatsApp pode apresentar o mesmo
  // participante em formatos diferentes (ex.: número/LID).
  estado.bloqueados = estado.bloqueados.filter(x => jidNormalizedUser(x) !== usuario)
  estado.bloqueadosSemana = estado.bloqueadosSemana.filter(x => jidNormalizedUser(x) !== usuario)
  estado.bloqueiosAutomaticosEscala = (estado.bloqueiosAutomaticosEscala || []).filter(x => jidNormalizedUser(x.id) !== usuario)
  estado.bloqueiosTaxas = (estado.bloqueiosTaxas || []).filter(x => jidNormalizedUser(typeof x === 'string' ? x : x.id) !== usuario)

  salvar()

  const depois = estado.bloqueados.length + estado.bloqueadosSemana.length +
    (estado.bloqueiosAutomaticosEscala || []).filter(x => jidNormalizedUser(x.id) === usuario).length +
    (estado.bloqueiosTaxas || []).filter(x => jidNormalizedUser(typeof x === 'string' ? x : x.id) === usuario).length
  return antes !== depois
}


/* =====================================
   PEGAR MARCAÇÕES
===================================== */

function obterMarcados(msg) {

  return (
    msg.message
      ?.extendedTextMessage
      ?.contextInfo
      ?.mentionedJid ||
    []
  )
}


/* =====================================
   BLOQUEAR
===================================== */

function bloquear(id, semanal) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return
  estado.online = (estado.online || []).filter(p => jidNormalizedUser(p.id) !== usuario)
  estado.espera = (estado.espera || []).filter(p => jidNormalizedUser(p.id) !== usuario)
  finalizarSessaoOnline(usuario)
  estado.bloqueados = (estado.bloqueados || []).filter(x => jidNormalizedUser(x) !== usuario)
  estado.bloqueadosSemana = (estado.bloqueadosSemana || []).filter(x => jidNormalizedUser(x) !== usuario)
  if (semanal) estado.bloqueadosSemana.push(usuario)
  else estado.bloqueados.push(usuario)
  promoverEspera()
  salvar()
}

/* =====================================
   TEXTO DA LISTA
===================================== */

function normalizarIdParaLista(id) {
  const valor = String(id || '').trim()
  if (!valor) return ''
  try {
    if (valor.includes('@')) return jidNormalizedUser(valor)
  } catch {}
  const numero = valor.replace(/\D/g, '')
  return numero ? `${numero}@s.whatsapp.net` : ''
}

function montarConteudoListaAtual() {
  const mencoes = new Set()
  const mencionar = (id, nomeAlternativo = '') => {
    const jid = normalizarIdParaLista(id)
    if (!jid) return String(nomeAlternativo || id || 'Entregador').trim()
    mencoes.add(jid)
    return `@${jid.split('@')[0].split(':')[0]}`
  }

  const online = (Array.isArray(estado?.online) ? estado.online : []).map((pessoa, indice) => {
    const id = pessoa?.id || pessoa?.phoneNumber || ''
    return `${indice + 1} - ${mencionar(id, pessoa?.nome)} ${statusEntregador(id)}`.trim()
  })
  const espera = (Array.isArray(estado?.espera) ? estado.espera : []).map((pessoa, indice) => {
    const id = pessoa?.id || pessoa?.phoneNumber || ''
    return `${indice + 1} - ${mencionar(id, pessoa?.nome)}`
  })
  const bloqueados = (Array.isArray(estado?.bloqueados) ? estado.bloqueados : []).map(id => mencionar(id))
  const bloqueadosSemana = (Array.isArray(estado?.bloqueadosSemana) ? estado.bloqueadosSemana : []).map(id => mencionar(id))
  const limite = limiteAtual()

  const regraLimite = estado?.feriado
    ? '🎉 *FERIADO: LISTA ONLINE SEM LIMITE*'
    : limite === Infinity
      ? '🎉 *FIM DE SEMANA: LISTA ONLINE SEM LIMITE*'
      : limite === 5
        ? '• *SERÃO 5 ENTREGADORES ATÉ 12H; APÓS 12H, 8 ENTREGADORES*'
        : '• *SERÃO 8 ENTREGADORES ONLINE*'

  let texto =
`*TEMPO DE RESPOSTA A EMPRESA (2min), CASO NÃO RESPONDA PERDE A VEZ E VAI PRO FIM DA FILA. (2 MIN DISPUTA).*\n\n${regraLimite}\n\n🟢 *LISTA ONLINE*\n\n${online.join('\n') || '(vazia)'}`

  if (espera.length) texto += `\n\n⛔ *LISTA DE ESPERA*\n\n${espera.join('\n')}`
  if (bloqueados.length) texto += `\n\n🚫 *BLOQUEADOS SEG - TER - QUA*\n\n${bloqueados.join('\n')}`
  if (bloqueadosSemana.length) texto += `\n\n🚫 *BLOQUEADOS POR UMA SEMANA*\n\n${bloqueadosSemana.join('\n')}`
  texto += '\n\n🔋 *Mantenha a bateria acima de 15%*\n\n⏱️ *TEMPO PARA RETIRADA ATE 10 MIN*\n🛵 *TEMPO PARA ENTREGA ATE 15 MIN*'

  return { text: texto, mentions: [...mencoes] }
}

// Compatibilidade: rotinas antigas que só precisam do texto continuam usando o mesmo renderizador.
function gerarLista() {
  return montarConteudoListaAtual().text
}

/* =====================================
   ENVIAR MENSAGEM
===================================== */

async function enviar(
  sock,
  grupo,
  mensagem
) {

  /*
    Esta função só será chamada
    para o grupo CHAT BOT.
  */

  if (
    !grupo ||
    !mensagem
  ) {

    return
  }

  try {

    await sock.sendMessage(
      grupo,
      {
        text: mensagem
      }
    )

  } catch (e) {

    console.log(
      'Erro ao enviar:',
      e.message
    )
  }
}


/* =====================================
   PUBLICAR LISTA
===================================== */

/* =====================================
   PUBLICAR LISTA
===================================== */

function contarEntregasAtivasEntregador(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return 0
  // Sincroniza a referência da empresa atual antes de somar todas as empresas.
  if (empresas?.[empresaAtual]) empresas[empresaAtual].estado = estado
  let quantidade = 0
  const mensagensContadas = new Set()
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const empresa = empresas[chave]
    // As entregas são registradas enquanto o contexto está no grupo g2, mas o
    // renderizador da lista trabalha no g1. Ler apenas empresa.estado ignorava
    // o escopo g2 e deixava o status visual parado até outra operação manual.
    // Unimos o estado legado e os escopos por grupo; a identidade abaixo evita
    // contar duas vezes registros que ainda estejam espelhados em mais de um local.
    const listas = [
      // Durante o processamento de uma mensagem, `estado` é a cópia viva do
      // grupo que está sendo processado; ela pode conter o INDO recém-recebido
      // antes do finally persistir estadosPorGrupo.g2.
      empresaAtual === chave ? estado?.entregasAceitas : null,
      empresa?.estadosPorGrupo?.g2?.entregasAceitas,
      empresa?.estado?.entregasAceitas,
      empresa?.estadosPorGrupo?.g1?.entregasAceitas
    ]
    for (let origem = 0; origem < listas.length; origem++) {
      const lista = Array.isArray(listas[origem]) ? listas[origem] : []
      for (let i = 0; i < lista.length; i++) {
        const entrega = lista[i]
        if (jidNormalizedUser(entrega?.entregadorId || '') !== usuario || entrega?.concluida) continue
        const idMensagem = entrega?.mensagemId || entrega?.id
        // IDs de mensagem são únicos dentro do grupo de origem, não
        // necessariamente entre empresas. Isolar por empresa evita fusões.
        const empresaEntrega = String(entrega?.empresaId || chave)
        const identidade = idMensagem
          ? `empresa:${empresaEntrega}:mensagem:${String(idMensagem)}`
          : `${chave}:sem-id:${jidNormalizedUser(entrega?.entregadorId || '')}:${Number(entrega?.aceitoEm || entrega?.criadoEm || 0)}:${Number(entrega?.quantidadePendente || entrega?.quantidade || 1)}:${String(entrega?.bairro || entrega?.texto || '')}`
        if (mensagensContadas.has(identidade)) continue
        mensagensContadas.add(identidade)
        quantidade += quantidadePendenteDaEntrega(entrega)
      }
    }
  }
  return quantidade
}

function statusOperacionalSalvoEntregador(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return '🟢'
  const ordem = [empresaAtual, ...Object.keys(EMPRESA_CONFIG).filter(chave => chave !== empresaAtual)]
  for (const chave of ordem) {
    const cadastro = (empresas[chave]?.estado?.entregadores || []).find(x => jidNormalizedUser(x.id) === usuario)
    if (cadastro && ['🟢','🚀','🟠','🔴'].includes(cadastro.statusOperacional)) return cadastro.statusOperacional
  }
  return '🟢'
}

function statusManualSalvoEntregador(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return null
  const ordem = [empresaAtual, ...Object.keys(EMPRESA_CONFIG).filter(chave => chave !== empresaAtual)]
  for (const chave of ordem) {
    const cadastro = (empresas[chave]?.estado?.entregadores || []).find(x => jidNormalizedUser(x.id) === usuario)
    if (cadastro && ['🔴','🟢'].includes(cadastro.statusManual)) return cadastro.statusManual
  }
  return null
}

function statusEntregador(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return '🟢'
  const ativas = contarEntregasAtivasEntregador(usuario)
  const salvo = statusOperacionalSalvoEntregador(usuario)
  const manual = statusManualSalvoEntregador(usuario)

  // O comando administrativo 'Limpar status' libera visualmente todos os entregadores.
  // Esse verde manual prevalece até uma nova mudança operacional atualizar o status.
  if (manual === '🟢') return '🟢'

  // O status reflete entregas ainda não finalizadas: 2 ou mais = vermelho.
  if (ativas >= 2) return '🔴'
  if (ativas === 1) {
    // Laranja representa a queda de 2+ entregas pendentes para apenas 1.
    return ['🔴','🟠'].includes(salvo) ? '🟠' : '🚀'
  }

  // Sem entregas ativas, mantém os comandos manuais existentes (ocupado/livre).
  return statusManualSalvoEntregador(usuario) || '🟢'
}

function registrarHorarioLivreNaFila(usuario, quando = Date.now()) {
  const pessoa = (Array.isArray(estado.online) ? estado.online : []).find(p => jidNormalizedUser(p.id) === usuario)
  if (pessoa) pessoa.livreDesde = quando
}

function alterarStatusOperacional(id, evento) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return false
  registrarEntregador(usuario)

  // Usa o status persistido ANTES de recalcular. statusEntregador() deriva o
  // status a partir das entregas já alteradas; após concluir a última entrega,
  // ele já retornaria verde e apagaria a transição que registra livreDesde.
  const statusAnterior = statusOperacionalSalvoEntregador(usuario)
  const salvosAntes = statusAnterior
  const ativas = contarEntregasAtivasEntregador(usuario)
  let proximo = '🟢'
  if (ativas >= 2) {
    proximo = '🔴'
  } else if (ativas === 1) {
    if (['conclusao','fracionado'].includes(evento) && ['🔴','🟠'].includes(salvosAntes)) proximo = '🟠'
    else proximo = '🚀'
  }

  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const cadastros = empresas[chave]?.estado?.entregadores || []
    let cadastro = cadastros.find(x => jidNormalizedUser(x.id) === usuario)
    if (!cadastro && chave === empresaAtual) cadastro = registrarEntregador(usuario)
    if (cadastro) {
      cadastro.statusOperacional = proximo
      cadastro.statusManual = null
    }
  }
  if (proximo === '🟢' && statusAnterior !== '🟢') {
    registrarHorarioLivreNaFila(usuario)
  } else if (proximo !== '🟢') {
    // Ao voltar a ficar ocupado, descarta a disponibilidade anterior. Se não,
    // no fim do pico ele poderia ganhar prioridade com um horário antigo.
    const pessoaOnline = (Array.isArray(estado.online) ? estado.online : [])
      .find(p => jidNormalizedUser(p.id) === usuario)
    if (pessoaOnline) delete pessoaOnline.livreDesde
  }
  salvar()
  return true
}

function limparTodosStatusVerde() {
  for (const chave of Object.keys(empresas || {})) {
    for (const cadastro of (empresas[chave]?.estado?.entregadores || [])) {
      cadastro.statusOperacional = '🟢'
      cadastro.statusManual = '🟢'
    }
  }
  for (const cadastro of (estado.entregadores || [])) { cadastro.statusOperacional = '🟢'; cadastro.statusManual = '🟢' }
  salvar()
}

function definirStatusManual(id, status) {
  const usuario = jidNormalizedUser(id)
  if (!usuario || !['🔴', '🟢'].includes(status)) return false

  const entregador = registrarEntregador(usuario)
  if (!entregador) return false
  const statusAnterior = statusEntregador(usuario)
  let alterou = statusAnterior !== status
  if (status === '🟢' && statusAnterior !== '🟢') {
    registrarHorarioLivreNaFila(usuario)
  } else if (status !== '🟢') {
    const pessoaOnline = (Array.isArray(estado.online) ? estado.online : [])
      .find(p => jidNormalizedUser(p.id) === usuario)
    if (pessoaOnline) delete pessoaOnline.livreDesde
  }
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    let cadastro = (empresas[chave]?.estado?.entregadores || []).find(x => jidNormalizedUser(x.id) === usuario)
    if (!cadastro && chave === empresaAtual) cadastro = entregador
    if (cadastro) { cadastro.statusManual = status; cadastro.statusOperacional = status }
  }
  salvar()
  return alterou
}

function limparStatusManual(id) {
  const usuario = jidNormalizedUser(id)
  if (!usuario) return false
  let alterou = false
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const cadastro = (empresas[chave]?.estado?.entregadores || []).find(x => jidNormalizedUser(x.id) === usuario)
    if (cadastro && (cadastro.statusManual || cadastro.statusOperacional !== '🟢')) alterou = true
    if (cadastro) { cadastro.statusManual = null; cadastro.statusOperacional = '🟢' }
  }
  salvar()
  return alterou
}

function capturarStatusPicoAtual() {
  const mapa = {}
  for (const pessoa of (Array.isArray(estado.online) ? estado.online : [])) {
    mapa[jidNormalizedUser(pessoa.id)] = statusEntregador(pessoa.id)
  }
  return mapa
}

function ordenarFilaAposHorarioPico() {
  const filaAntes = Array.isArray(estado.online) ? [...estado.online] : []
  const dataLivre = (pessoa) => {
    const livreDesde = Number(pessoa?.livreDesde)
    if (Number.isFinite(livreDesde) && livreDesde > 0) return livreDesde
    const entrou = Number(pessoa?.entrou)
    return Number.isFinite(entrou) && entrou > 0 ? entrou : Number.MAX_SAFE_INTEGER
  }
  const livres = filaAntes
    .filter(p => statusEntregador(p.id) === '🟢')
    .sort((a, b) => dataLivre(a) - dataLivre(b))
  const livresIds = new Set(livres.map(p => jidNormalizedUser(String(p?.id || ''))).filter(Boolean))
  estado.online = [...livres, ...filaAntes.filter(p => !livresIds.has(jidNormalizedUser(String(p?.id || ''))))]
  sincronizarFilaCompartilhadaComLista()
  return livres
}

async function ativarHorarioPico(sock, motivo = 'manual') {
  if (listaSuspensaPico) return false

  // No modo automático, ativa quando há entregadores online e nenhum está livre (🟢).
  const onlineAtuais = Array.isArray(estado.online) ? estado.online : []
  const verdes = onlineAtuais.filter(p => statusEntregador(p.id) === '🟢').length
  if (motivo === 'automatico' && (onlineAtuais.length === 0 || verdes > 0)) {
    return false
  }

  listaSuspensaPico = true
  if (empresas.CHEGO_DELIVERY?.estado) { empresas.CHEGO_DELIVERY.estado.horarioPicoIniciadoEm = Date.now(); empresas.CHEGO_DELIVERY.estado.horarioPicoEncerradoEm = 0 }
  statusPicoAnterior = capturarStatusPicoAtual()
  // Quem já estava livre antes/durante o início do pico precede quem ficar livre depois.
  const inicioPico = Date.now()
  for (const pessoa of onlineAtuais) {
    if (statusEntregador(pessoa.id) === '🟢' && !Number.isFinite(Number(pessoa.livreDesde))) {
      pessoa.livreDesde = inicioPico - 1
    }
  }
  salvar()
  try {
    await sock.sendMessage(grupos.g1, { text: '🚀 *HORÁRIO DE PICO ATIVADO*\n\nQualquer entregador ONLINE pode aceitar uma entrega.' })
  } catch (e) {
    console.log('Erro ao avisar início do horário de pico:', e.message)
  }
  return true
}

async function desativarHorarioPico(sock, motivo = 'manual') {
  if (!listaSuspensaPico) return false

  // Ao encerrar o pico, todos os disponíveis são colocados no começo da fila,
  // ordenados pelo instante em que ficaram livres (primeiro livre, primeiro da fila).
  ordenarFilaAposHorarioPico()

  listaSuspensaPico = false
  if (empresas.CHEGO_DELIVERY?.estado) empresas.CHEGO_DELIVERY.estado.horarioPicoEncerradoEm = Date.now()
  statusPicoAnterior = capturarStatusPicoAtual()
  salvar()

  try {
    await sock.sendMessage(grupos.g1, { text: '🟢 *HORÁRIO DE PICO ENCERRADO*\n\nA ordem normal da fila foi restaurada.' })
  } catch (e) {
    console.log('Erro ao avisar fim do horário de pico:', e.message)
  }

  return true
}

async function alternarHorarioPico(sock) {
  if (listaSuspensaPico) {
    bloquearPicoAutomatico = true
    await desativarHorarioPico(sock, 'manual')
    salvar()
    await publicarLista(sock, { forcarAtualizacao: true })
    return true
  }

  bloquearPicoAutomatico = false
  await ativarHorarioPico(sock, 'manual')
  salvar()
  return true
}

async function verificarFimHorarioPicoPorEntregadorLivre(sock) {
  if (!listaSuspensaPico) return false

  const onlineAtuais = Array.isArray(estado.online) ? estado.online : []
  const entregadoresVerdes = onlineAtuais.filter(p => statusEntregador(p.id) === '🟢')
  statusPicoAnterior = capturarStatusPicoAtual()

  // O horário de pico só termina automaticamente com pelo menos dois 🟢.
  if (entregadoresVerdes.length < 2) {
    salvar()
    return false
  }

  ordenarFilaAposHorarioPico()
  listaSuspensaPico = false
  if (empresas.CHEGO_DELIVERY?.estado) empresas.CHEGO_DELIVERY.estado.horarioPicoEncerradoEm = Date.now()
  salvar()
  try {
    await sock.sendMessage(grupos.g1, {
      text: '🟢 *HORÁRIO DE PICO ENCERRADO*\n\nOs entregadores livres foram reorganizados no começo da fila pela ordem em que ficaram disponíveis.'
    })
  } catch (e) {
    console.log('Erro ao avisar fim do horário de pico:', e.message)
  }
  return true
}

async function sincronizarHorarioPicoAutomatico(sock) {
  const onlineAtuais = Array.isArray(estado.online) ? estado.online : []
  const entregadoresVerdes = onlineAtuais.filter(p => statusEntregador(p.id) === '🟢')

  if (listaSuspensaPico) {
    // Ao chegar a dois verdes, desativa o pico; a chamada de publicarLista
    // que iniciou esta verificação atualizará a mensagem existente.
    return verificarFimHorarioPicoPorEntregadorLivre(sock)
  }

  // Não ativa pico sem entregadores online; também preserva o comando manual
  // que desativa o automático até o ADM habilitá-lo novamente.
  if (!bloquearPicoAutomatico && onlineAtuais.length > 1 && entregadoresVerdes.length === 0) {
    return ativarHorarioPico(sock, 'automatico')
  }
  return false
}

async function publicarListaComAtraso(sock) {
  // Aceitar entrega altera status e posição do entregador. Tenta editar a lista
  // existente; se não for possível, publicarLista cria uma nova e guarda a referência.
  await new Promise(resolve => setTimeout(resolve, 400))
  let algumaAtualizada = false
  const anterior = empresaAtual
  try {
    for (const chave of Object.keys(EMPRESA_CONFIG)) {
      if (!empresas[chave]?.grupos?.g1) continue
      try {
        const atualizada = await publicarListaEmpresaNoEstadoDoGrupo(sock, chave, 'g1', {
          apenasEditarExistente: true,
          forcarAtualizacao: true
        })
        if (atualizada) algumaAtualizada = true
      } catch (erro) {
        console.error(`[LISTA] Falha ao editar lista após aceite de entrega (${chave}):`, erro?.message || erro)
      }
    }
  } finally {
    selecionarEmpresa(anterior)
  }
  return algumaAtualizada
}

function snapshotEstadoListaUndo() {
  // Estado necessário para reverter as alterações que afetam a lista e a fila.
  return JSON.parse(JSON.stringify({
    online: estado.online || [],
    espera: estado.espera || [],
    bloqueados: estado.bloqueados || [],
    bloqueadosSemana: estado.bloqueadosSemana || [],
    sessoesOnline: estado.sessoesOnline || [],
    corridas: estado.corridas || [],
    entregasAceitas: estado.entregasAceitas || [],
    contadorCorrida: estado.contadorCorrida || 0,
    rotaAtiva: estado.rotaAtiva || null,
    statusEntregadores: (estado.entregadores || []).map(p => ({ id: p.id, statusOperacional: p.statusOperacional || p.statusManual || '🟢', statusManual: p.statusManual || null }))
  }))
}

const LIMITE_UNDO_LISTA = Number(process.env.LIMITE_UNDO_LISTA) || 100
function registrarHistoricoUndoLista() {
  const atual = snapshotEstadoListaUndo()
  if (!estado.ultimoSnapshotUndoLista) {
    // Primeira execução após instalar a função: cria uma base, sem inventar undo antigo.
    estado.ultimoSnapshotUndoLista = atual
    return
  }
  const anterior = estado.ultimoSnapshotUndoLista
  // Guarda apenas as chaves que mudaram (valores anteriores), não o snapshot inteiro.
  const diferenca = {}
  let mudou = false
  for (const chave of new Set([...Object.keys(atual), ...Object.keys(anterior)])) {
    if (JSON.stringify(atual[chave]) !== JSON.stringify(anterior[chave])) { diferenca[chave] = anterior[chave]; mudou = true }
  }
  if (mudou) {
    if (!Array.isArray(estado.historicoUndoLista)) estado.historicoUndoLista = []
    estado.historicoUndoLista.push(diferenca)
    if (estado.historicoUndoLista.length > LIMITE_UNDO_LISTA) estado.historicoUndoLista.splice(0, estado.historicoUndoLista.length - LIMITE_UNDO_LISTA)
  }
}

function atualizarSnapshotUndoLista() {
  estado.ultimoSnapshotUndoLista = snapshotEstadoListaUndo()
  salvar()
}

function desfazerUltimaAtualizacaoLista() {
  if (!Array.isArray(estado.historicoUndoLista) || estado.historicoUndoLista.length === 0) return false
  const anterior = estado.historicoUndoLista.pop()
  for (const chave of ['online', 'espera', 'bloqueados', 'bloqueadosSemana', 'sessoesOnline', 'corridas', 'entregasAceitas', 'contadorCorrida', 'rotaAtiva']) {
    if (!(chave in anterior)) continue // entrada em formato de diferença: chave não alterada
    estado[chave] = anterior[chave] === undefined ? (chave === 'contadorCorrida' ? 0 : (chave === 'rotaAtiva' ? null : [])) : anterior[chave]
  }
  for (const registro of (anterior.statusEntregadores || [])) {
    const usuario = jidNormalizedUser(registro.id)
    for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
      const cadastro = (empresas[chaveEmpresa]?.estado?.entregadores || []).find(p => jidNormalizedUser(p.id) === usuario)
      if (cadastro) { cadastro.statusOperacional = registro.statusOperacional || '🟢'; cadastro.statusManual = registro.statusManual || null }
    }
    const local = (estado.entregadores || []).find(p => jidNormalizedUser(p.id) === usuario)
    if (local) { local.statusOperacional = registro.statusOperacional || '🟢'; local.statusManual = registro.statusManual || null }
  }
  estado.ultimoSnapshotUndoLista = snapshotEstadoListaUndo()
  sincronizarFilaCompartilhadaComLista()
  salvar()
  return true
}

function deveCriarNovaListaPorIdade(ultimaPublicacaoEm, agora = Date.now()) {
  const ultima = Number(ultimaPublicacaoEm) || 0
  return ultima > 0 && Number(agora) - ultima >= 10 * 60 * 1000
}

async function publicarLista(sock, opcoes = {}) {
  const opcoesLista = opcoes && typeof opcoes === 'object' ? opcoes : {}
  const forcarNovaListaManual = opcoesLista.forcarNova === true
  let forcarNovaLista = forcarNovaListaManual
  const comandoListaExplicito = opcoesLista.permitirCriarSeSemReferencia === true
  const naoPromoverEspera = opcoesLista.naoPromoverEspera === true
  const naoAjustarLimiteFila = opcoesLista.naoAjustarLimiteFila === true

  if (!conectadoWhatsApp) {
    console.log('[LISTA] WhatsApp desconectado; publicação/edição cancelada.')
    return false
  }
  if (!sock || typeof sock.sendMessage !== 'function' || !grupos?.g1) {
    console.error('[LISTA] Socket ou grupo g1 indisponível; nenhuma mensagem foi enviada.')
    return false
  }

  const empresa = empresas?.[empresaAtual]
  const escopo = empresa?.estadosPorGrupo?.g1 || null
  const ultimaPublicacaoConhecida = Number(escopo?.ultimaListaPublicadaEm ?? empresa?.ultimaListaPublicadaEm) || 0
  const novaListaPorIdade = !forcarNovaListaManual && deveCriarNovaListaPorIdade(ultimaPublicacaoConhecida)
  if (novaListaPorIdade) {
    forcarNovaLista = true
    console.log(`[LISTA] Última publicação tem pelo menos 10 minutos; a próxima atualização operacional criará uma nova mensagem. empresa=${empresaAtual}`)
  }
  // Uma atualização automática edita a mensagem existente até completar 10 minutos.
  // Depois disso, a próxima alteração real cria uma nova referência.
  const apenasEditarExistente = !forcarNovaLista
  const grupoDestino = String(grupos.g1)
  const normalizarJid = (jid) => {
    const valor = String(jid || '').trim()
    if (!valor) return ''
    try { return jidNormalizedUser(valor).toLowerCase() }
    catch { return valor.toLowerCase() }
  }
  const pertenceAoGrupo = (chave, aceitarSemDestino = false) => {
    if (!chave?.id || chave.fromMe !== true) return false
    if (!chave.remoteJid) return aceitarSemDestino
    return normalizarJid(chave.remoteJid) === normalizarJid(grupoDestino)
  }
  // Uma referência editável precisa identificar uma mensagem enviada pelo bot,
  // com ID e grupo de destino conhecidos. Não transforme uma chave incompleta
  // ou de outra origem em uma chave aparentemente válida.
  const prepararChave = (chave) => ({
    ...(chave || {}),
    remoteJid: String(chave?.remoteJid || ''),
    fromMe: chave?.fromMe === true,
    id: String(chave?.id || '')
  })

  let chaveLista = null
  if (pertenceAoGrupo(escopo?.ultimaListaMensagemKey, false)) {
    chaveLista = prepararChave(escopo.ultimaListaMensagemKey)
  }

  // Só o comando explícito Lista pode atravessar as pausas de pico/administrativa.
  // forcarAtualizacao significa "recalcular o conteúdo", não "ignorar uma pausa".
  try {
    await sincronizarHorarioPicoAutomatico(sock)
  } catch (erroPico) {
    console.error('[LISTA] Falha ao reconciliar horário de pico:', erroPico?.message || erroPico)
  }
  const podeIgnorarPausa = comandoListaExplicito || forcarNovaListaManual
  if (listaSuspensaPico && !podeIgnorarPausa) {
    console.log('[LISTA] Atualização suspensa durante horário de pico; estado preservado para a próxima atualização permitida.')
    return false
  }
  if (listaSuspensaADM && !podeIgnorarPausa) {
    console.log('[LISTA] Atualização suspensa pelo ADM; aguardando Lista ou lista on.')
    return false
  }

  // Toda publicação passa pelo mesmo reconciliador da fila, mas renderizar não
  // recria estruturas: somente os arrays operacionais já existentes são ajustados.
  if (!Array.isArray(estado.online)) estado.online = []
  if (!Array.isArray(estado.espera)) estado.espera = []
  if (!Array.isArray(estado.bloqueados)) estado.bloqueados = []
  if (!Array.isArray(estado.bloqueadosSemana)) estado.bloqueadosSemana = []
  registrarHistoricoUndoLista()
  // Limpezas administrativas precisam publicar exatamente a fila vazia solicitada.
  // Não ajustar limite nesse caminho: isso poderia mover pessoas de ONLINE para ESPERA
  // logo após o comando limpar lista, fazendo parecer que a limpeza falhou.
  if (!naoAjustarLimiteFila) ajustarLimiteFila()
  if (!naoPromoverEspera) promoverEspera()
  statusPicoAnterior = capturarStatusPicoAtual()
  salvar()

  const conteudo = montarConteudoListaAtual()
  // O pós-processamento das mensagens do grupo chama este caminho como rede
  // de segurança. Só envia a edição se o texto realmente divergir do último
  // conteúdo salvo para a mensagem visível; o comando manual Lista não usa
  // esta opção e mantém seu comportamento explícito.
  if (opcoesLista.somenteSeTextoMudou === true && String(escopo?.ultimaListaPublicada || '') === conteudo.text) {
    return true
  }
  const historicoAnterior = Boolean(
    escopo?.ultimaListaPublicada || escopo?.ultimaListaEnviada || Number(escopo?.ultimaListaPublicadaEm) > 0
  )

  const salvarReferencia = (chave, texto) => {
    const agora = Date.now()
    const chaveNormalizada = chave?.id ? prepararChave(chave) : null
    ultimaListaPublicada = texto
    ultimaListaEnviada = texto
    ultimaListaMensagemKey = chaveNormalizada
    ultimaListaPublicadaEm = agora

    if (empresa) {
      if (!empresa.estadosPorGrupo || typeof empresa.estadosPorGrupo !== 'object') empresa.estadosPorGrupo = {}
      if (!empresa.estadosPorGrupo.g1 || typeof empresa.estadosPorGrupo.g1 !== 'object') empresa.estadosPorGrupo.g1 = {}
      Object.assign(empresa.estadosPorGrupo.g1, {
        ultimaListaPublicada: texto,
        ultimaListaEnviada: texto,
        ultimaListaMensagemKey: chaveNormalizada ? { ...chaveNormalizada } : null,
        ultimaListaPublicadaEm: agora
      })
      // Campos legados são mantidos para migração; sua chave só volta a ser
      // considerada se tiver o remoteJid correto na próxima atualização.
      empresa.ultimaListaPublicada = texto
      empresa.ultimaListaEnviada = texto
      empresa.ultimaListaMensagemKey = chaveNormalizada ? { ...chaveNormalizada } : null
      empresa.ultimaListaPublicadaEm = agora
    }
    contadorAtualizacaoLista++
    atualizarSnapshotUndoLista()
    salvar()
  }

  // A criação automática só ocorre quando a última publicação já tem 10 minutos.
  // Falhas de edição antes desse prazo não geram mensagens duplicadas.
  const publicarNovaListaDeRecuperacao = async (motivo) => {
    // O comando Lista sempre pode criar uma nova mensagem; a atualização automática
    // também pode fazê-lo quando a referência atingiu 10 minutos de idade.
    if (!forcarNovaLista) {
      console.warn(`[LISTA] Nova publicação de recuperação bloqueada (${motivo}); use o comando Lista para criar uma nova mensagem.`)
      return false
    }
    try {
      const enviada = await sock.sendMessage(grupoDestino, {
        text: conteudo.text,
        mentions: conteudo.mentions
      })
      const chaveNova = enviada?.key?.id ? prepararChave({
        ...enviada.key,
        remoteJid: grupoDestino,
        fromMe: true
      }) : null
      salvarReferencia(chaveNova, conteudo.text)
      if (!chaveNova) {
        console.error(`[LISTA] Nova lista enviada após ${motivo}, mas sem ID retornado; será necessário recuperar a referência.`)
        return false
      }
      falhasEdicaoListaAte.clear()
      console.warn(`[LISTA] Nova lista publicada após ${motivo}; empresa=${empresaAtual}; grupo=${grupoDestino}; id=${chaveNova.id}`)
      return true
    } catch (erroNovaLista) {
      console.error(`[LISTA] Falharam a edição e a publicação de recuperação (${motivo}).`, {
        empresa: empresaAtual,
        grupo: grupoDestino,
        mensagem: erroNovaLista?.message || String(erroNovaLista)
      })
      return false
    }
  }

  // Se existe chave, tenta editar a mesma mensagem primeiro. Se o WhatsApp
  // rejeitar a edição, publica uma nova lista e substitui a referência salva.
  if (chaveLista && !forcarNovaLista) {
    const chaveFalhaEdicao = `${normalizarJid(grupoDestino)}:${chaveLista.id}`
    try {
      const retorno = await sock.sendMessage(grupoDestino, {
        text: conteudo.text,
        mentions: conteudo.mentions,
        edit: chaveLista
      })

      // Só considera a edição confirmada quando o retorno aponta para a mesma
      // mensagem e o mesmo grupo. Se a resposta não confirmar o alvo, troca a
      // referência publicando uma lista nova para não deixar a lista desatualizada.
      const idRetornado = String(retorno?.key?.id || '')
      const destinoRetornado = normalizarJid(retorno?.key?.remoteJid || grupoDestino)
      const edicaoConfirmada = Boolean(
        idRetornado &&
        idRetornado === String(chaveLista.id) &&
        destinoRetornado === normalizarJid(grupoDestino)
      )

      if (!edicaoConfirmada) {
        falhasEdicaoListaAte.set(chaveFalhaEdicao, Date.now() + INTERVALO_SUPRESSAO_FALHA_EDICAO_MS)
        console.error('[LISTA] A edição não confirmou a mensagem-alvo; não haverá nova publicação automática. Use Lista para criar uma nova mensagem.', {
          empresa: empresaAtual,
          grupo: grupoDestino,
          idMensagemOriginal: chaveLista.id,
          idRetornado: idRetornado || null,
          destinoRetornado: retorno?.key?.remoteJid || null
        })
        // Não substituir a mensagem por outra automaticamente: preservar a referência
    // e aguardar o comando Lista caso o WhatsApp não confirme a edição.
    return false
      }

      falhasEdicaoListaAte.delete(chaveFalhaEdicao)
      salvarReferencia(chaveLista, conteudo.text)
      console.log(`[LISTA] Edição confirmada para a mensagem atual. empresa=${empresaAtual}; grupo=${grupoDestino}; id=${chaveLista.id}`)
      return true
    } catch (erroEdicao) {
      falhasEdicaoListaAte.set(chaveFalhaEdicao, Date.now() + INTERVALO_SUPRESSAO_FALHA_EDICAO_MS)
      console.error('[LISTA] A edição falhou; nova publicação automática bloqueada. Use Lista para criar uma nova mensagem.', {
        empresa: empresaAtual,
        grupo: grupoDestino,
        idMensagem: chaveLista.id,
        codigo: erroEdicao?.code || erroEdicao?.output?.statusCode || null,
        mensagem: erroEdicao?.message || String(erroEdicao)
      })
      // Não publicar cópia quando a edição falhar; o grupo só recebe nova lista
      // quando alguém envia explicitamente o comando Lista.
      return false
    }
  }

  // Sem referência válida, só publica automaticamente se a janela de 10 minutos
  // já venceu; caso contrário, preserva o grupo sem duplicar a lista.
  if (apenasEditarExistente) {
    console.warn(`[LISTA] Não há chave válida para editar no grupo ${grupoDestino}; aguardando o comando Lista para criar uma nova mensagem.`)
    return await publicarNovaListaDeRecuperacao('referência ausente ou inválida')
  }
  // Não criar uma nova mensagem por atualização automática ou por outros comandos.
  // Somente a chamada do comando manual Lista define forcarNovaLista.
  const podeCriar = forcarNovaLista
  if (!podeCriar) {
    const causa = historicoAnterior ? 'há histórico sem referência' : 'a primeira publicação ainda não foi solicitada'
    console.warn(`[LISTA] Nenhuma lista nova criada: ${causa}; use o comando Lista para recuperar/publicar.`)
    return false
  }

  try {
    const enviada = await sock.sendMessage(grupoDestino, {
      text: conteudo.text,
      mentions: conteudo.mentions
    })
    // O destino desta chamada é a fonte autoritativa do grupo da mensagem.
    // Não persistir a chave devolvida sem remoteJid/fromMe: ela seria descartada
    // na próxima execução e as atualizações automáticas perderiam a referência.
    const chaveNova = enviada?.key?.id ? prepararChave({
      ...enviada.key,
      remoteJid: grupoDestino,
      fromMe: true
    }) : null
    salvarReferencia(chaveNova, conteudo.text)
    if (!chaveNova) {
      console.error('[LISTA] A mensagem foi enviada, mas o WhatsApp não devolveu a chave. O próximo comando Lista será necessário para recuperar a referência.')
    } else {
      console.log(`[LISTA] Referência da lista criada/recuperada. empresa=${empresaAtual}; grupo=${grupoDestino}; id=${chaveNova.id}`)
    }
    return true
  } catch (erroEnvio) {
    console.error('[LISTA] Falha ao criar a mensagem inicial/de recuperação:', erroEnvio?.message || erroEnvio)
    return false
  }
}

async function publicarUltimaLista(sock) {
  if (!conectadoWhatsApp || !grupos?.g1) return false
  return await publicarLista(sock, { apenasEditarExistente: true, forcarAtualizacao: true })
}

async function publicarListaEmpresa(sock, chave) {
  if (!empresas[chave]) return false

  // Guarda o mapeamento próprio da empresa antes de trocar o contexto global.
  // Isso evita que uma referência antiga de `grupos` apague o g1 já encontrado.
  const gruposDaEmpresa = empresas[chave].grupos
  const grupoLista = gruposDaEmpresa?.g1

  if (!grupoLista) {
    console.log(`${EMPRESA_CONFIG[chave].nome} | grupo da lista não encontrado`)
    return false
  }

  // Todas as atualizações automáticas/operacionais editam a referência da
  // mensagem que está sendo exibida. Nenhuma rotina de atualização cria cópias.
  return await publicarListaEmpresaNoEstadoDoGrupo(sock, chave, 'g1')
}

// Publica a lista automática usando explicitamente o estado isolado do grupo g1.
// O processamento de mensagens mantém online/espera e a referência da lista por grupo;
// o temporizador precisa carregar esse mesmo escopo, em vez de usar o estado-base da empresa.
// Serializa trocas temporárias de contexto global. Sem fila, duas atualizações
// simultâneas (por exemplo, comando de ADM e temporizador) poderiam alternar
// empresaAtual/estado/grupos enquanto uma publicação ainda está aguardando o WhatsApp.
let filaPublicacaoEstadoGrupo = Promise.resolve()

function publicarListaEmpresaNoEstadoDoGrupo(sock, chave, chaveGrupo = 'g1', opcoesPublicacao = {}) {
  const executar = () => publicarListaEmpresaNoEstadoDoGrupoSerializado(sock, chave, chaveGrupo, opcoesPublicacao)
  const resultado = filaPublicacaoEstadoGrupo.then(executar, executar)
  // Mantém a fila utilizável mesmo se uma execução falhar.
  filaPublicacaoEstadoGrupo = resultado.then(() => undefined, () => undefined)
  return resultado
}

async function publicarListaEmpresaNoEstadoDoGrupoSerializado(sock, chave, chaveGrupo = 'g1', opcoesPublicacao = {}) {
  const empresa = empresas[chave]
  if (!empresa) return false

  // Não use selecionarEmpresa() aqui: o processamento pode chamar esta função
  // quando o contexto global já está temporariamente isolado no grupo. A troca
  // antiga copiava esse contexto temporário para empresa.estado e contaminava a base.
  const contextoAnterior = {
    empresaAtual, estado, grupos, ultimaListaPublicada, ultimaListaEnviada,
    ultimaListaMensagemKey, ultimaListaPublicadaEm, listaSuspensaPico,
    listaSuspensaADM, bloquearPicoAutomatico, statusPicoAnterior
  }
  const estadoBaseEmpresa = empresa.estado || estadoVazio()
  const gruposBaseEmpresa = empresa.grupos || {}
  const metaBaseEmpresa = {
    ultimaListaPublicada: empresa.ultimaListaPublicada || '',
    ultimaListaEnviada: empresa.ultimaListaEnviada || '',
    ultimaListaMensagemKey: empresa.ultimaListaMensagemKey || null,
    ultimaListaPublicadaEm: Number(empresa.ultimaListaPublicadaEm) || 0,
    listaSuspensaPico: !!empresa.listaSuspensaPico,
    listaSuspensaADM: !!empresa.listaSuspensaADM,
    bloquearPicoAutomatico: !!empresa.bloquearPicoAutomatico,
    statusPicoAnterior: structuredClone(empresa.statusPicoAnterior || {})
  }
  if (!empresa.estadosPorGrupo || typeof empresa.estadosPorGrupo !== 'object') empresa.estadosPorGrupo = {}
  if (!empresa.estadosPorGrupo[chaveGrupo]) empresa.estadosPorGrupo[chaveGrupo] = {}
  const escopo = empresa.estadosPorGrupo[chaveGrupo]
  const camposEstado = CAMPOS_ESTADO_POR_GRUPO
  const metaCampos = ['ultimaListaPublicada', 'ultimaListaEnviada', 'ultimaListaMensagemKey', 'ultimaListaPublicadaEm', 'listaSuspensaPico', 'listaSuspensaADM', 'bloquearPicoAutomatico', 'statusPicoAnterior']

  try {
    // Carrega explicitamente a base da empresa e, em seguida, o estado operacional
    // do grupo. Tanto o comando Lista quanto o temporizador passam por este caminho.
    empresaAtual = chave
    // Trabalha em objeto separado para não sobrescrever o estado-base da empresa
    // ao carregar os campos operacionais exclusivos deste grupo.
    estado = { ...estadoBaseEmpresa }
    grupos = gruposBaseEmpresa
    ultimaListaPublicada = metaBaseEmpresa.ultimaListaPublicada
    ultimaListaEnviada = metaBaseEmpresa.ultimaListaEnviada
    ultimaListaMensagemKey = metaBaseEmpresa.ultimaListaMensagemKey
    ultimaListaPublicadaEm = metaBaseEmpresa.ultimaListaPublicadaEm
    listaSuspensaPico = metaBaseEmpresa.listaSuspensaPico
    listaSuspensaADM = metaBaseEmpresa.listaSuspensaADM
    bloquearPicoAutomatico = metaBaseEmpresa.bloquearPicoAutomatico
    statusPicoAnterior = structuredClone(metaBaseEmpresa.statusPicoAnterior)

    for (const campo of camposEstado) {
      if (campo === 'online' || campo === 'espera') {
        if (!Array.isArray(estadoBaseEmpresa[campo])) estadoBaseEmpresa[campo] = []
        delete escopo[campo]
        estado[campo] = structuredClone(estadoBaseEmpresa[campo])
      } else {
        if (escopo[campo] === undefined) escopo[campo] = structuredClone(estadoBaseEmpresa[campo])
        estado[campo] = structuredClone(escopo[campo])
      }
    }
    for (const campo of metaCampos) {
      const baseValor = metaBaseEmpresa[campo]
      if (escopo[campo] === undefined) escopo[campo] = structuredClone(baseValor)
    }
    // Não migrar chaves do estado-base: a referência válida pertence somente ao grupo.
    ultimaListaPublicada = escopo.ultimaListaPublicada || ''
    ultimaListaEnviada = escopo.ultimaListaEnviada || ''
    ultimaListaMensagemKey = escopo.ultimaListaMensagemKey || null
    ultimaListaPublicadaEm = Number(escopo.ultimaListaPublicadaEm) || 0
    listaSuspensaPico = !!escopo.listaSuspensaPico
    listaSuspensaADM = !!escopo.listaSuspensaADM
    bloquearPicoAutomatico = !!escopo.bloquearPicoAutomatico
    statusPicoAnterior = structuredClone(escopo.statusPicoAnterior || {})

    let resultadoPublicacao = false
    if (opcoesPublicacao?.reconciliarFilaAutomaticamente === true) {
      // A rotina periódica precisa operar sobre o mesmo estado g1 usado pela
      // mensagem visível. Antes, selecionarEmpresa() carregava o estado-base,
      // podendo comparar uma fila diferente e tentar editar uma referência fora
      // do contexto da lista publicada.
      const textoAntes = montarConteudoListaAtual().text
      ajustarLimiteFila()
      promoverEspera()
      limparDuplicados()
      const textoDepois = montarConteudoListaAtual().text
      if (textoDepois !== textoAntes) {
        resultadoPublicacao = await publicarLista(sock, {
          apenasEditarExistente: true,
          forcarAtualizacao: true
        })
      } else {
        console.log(`[LISTA-DIAG] Reconciliação periódica sem alteração visível; empresa=${chave}; grupo=${chaveGrupo}`)
      }
    } else {
      resultadoPublicacao = await publicarLista(sock, opcoesPublicacao)
    }
    return resultadoPublicacao
  } finally {
    // A fila é persistida somente em empresa.estado; o escopo g1 guarda os demais campos.
    for (const campo of camposEstado) {
      if (campo === 'online' || campo === 'espera') {
        estadoBaseEmpresa[campo] = structuredClone(estado[campo])
        delete escopo[campo]
      } else {
        escopo[campo] = structuredClone(estado[campo])
      }
    }
    Object.assign(escopo, {
      ultimaListaPublicada, ultimaListaEnviada, ultimaListaMensagemKey,
      ultimaListaPublicadaEm, listaSuspensaPico, listaSuspensaADM,
      bloquearPicoAutomatico, statusPicoAnterior: structuredClone(statusPicoAnterior || {})
    })

    empresa.estado = estadoBaseEmpresa
    empresa.grupos = gruposBaseEmpresa
    // Persiste com o contexto da empresa que acabou de ser atualizado.
    empresaAtual = chave
    estado = estadoBaseEmpresa
    grupos = gruposBaseEmpresa
    ultimaListaPublicada = metaBaseEmpresa.ultimaListaPublicada
    ultimaListaEnviada = metaBaseEmpresa.ultimaListaEnviada
    ultimaListaMensagemKey = metaBaseEmpresa.ultimaListaMensagemKey
    ultimaListaPublicadaEm = metaBaseEmpresa.ultimaListaPublicadaEm
    listaSuspensaPico = metaBaseEmpresa.listaSuspensaPico
    listaSuspensaADM = metaBaseEmpresa.listaSuspensaADM
    bloquearPicoAutomatico = metaBaseEmpresa.bloquearPicoAutomatico
    statusPicoAnterior = structuredClone(metaBaseEmpresa.statusPicoAnterior)
    salvar()

    // Restaura todos os globais do chamador, não apenas empresaAtual. A função
    // pode ter sido chamada enquanto outra mensagem usa um contexto isolado.
    empresaAtual = contextoAnterior.empresaAtual
    estado = contextoAnterior.estado
    grupos = contextoAnterior.grupos
    ultimaListaPublicada = contextoAnterior.ultimaListaPublicada
    ultimaListaEnviada = contextoAnterior.ultimaListaEnviada
    ultimaListaMensagemKey = contextoAnterior.ultimaListaMensagemKey
    ultimaListaPublicadaEm = contextoAnterior.ultimaListaPublicadaEm
    listaSuspensaPico = contextoAnterior.listaSuspensaPico
    listaSuspensaADM = contextoAnterior.listaSuspensaADM
    bloquearPicoAutomatico = contextoAnterior.bloquearPicoAutomatico
    statusPicoAnterior = contextoAnterior.statusPicoAnterior
    estado = contextoAnterior.estado
    grupos = contextoAnterior.grupos
    ultimaListaPublicada = contextoAnterior.ultimaListaPublicada
    ultimaListaEnviada = contextoAnterior.ultimaListaEnviada
    ultimaListaMensagemKey = contextoAnterior.ultimaListaMensagemKey
    ultimaListaPublicadaEm = contextoAnterior.ultimaListaPublicadaEm
    listaSuspensaPico = contextoAnterior.listaSuspensaPico
    listaSuspensaADM = contextoAnterior.listaSuspensaADM
    bloquearPicoAutomatico = contextoAnterior.bloquearPicoAutomatico
    statusPicoAnterior = contextoAnterior.statusPicoAnterior
  }
}

async function publicarListasTodasEmpresas(sock) {
  const anterior = empresaAtual
  let algumaAtualizada = false
  try {
    for (const chave of Object.keys(EMPRESA_CONFIG)) {
      if (!empresas[chave]?.grupos?.g1) continue
      try {
        const resultado = await publicarListaEmpresa(sock, chave)
        if (resultado) algumaAtualizada = true
      } catch (erro) {
        console.error(`[LISTA] Falha ao sincronizar ${EMPRESA_CONFIG[chave].nome}:`, erro?.message || erro)
      }
    }
  } finally {
    selecionarEmpresa(anterior)
  }
  return algumaAtualizada
}

function salvarUndoADM() {
  estado.undoADM = {
    online: JSON.parse(JSON.stringify(estado.online || [])),
    espera: JSON.parse(JSON.stringify(estado.espera || [])),
    bloqueados: [...(estado.bloqueados || [])],
    bloqueadosSemana: [...(estado.bloqueadosSemana || [])]
  }
}

function desfazerADM() {
  // Cada execução desfaz uma publicação/alteração da lista; chamadas repetidas
  // percorrem o histórico para trás, uma atualização por vez.
  if (desfazerUltimaAtualizacaoLista()) return true
  // Compatibilidade com o único undo antigo salvo em versões anteriores.
  if (!estado.undoADM) return false
  estado.online = estado.undoADM.online || []
  estado.espera = estado.undoADM.espera || []
  estado.bloqueados = estado.undoADM.bloqueados || []
  estado.bloqueadosSemana = estado.undoADM.bloqueadosSemana || []
  estado.undoADM = null
  estado.ultimoSnapshotUndoLista = snapshotEstadoListaUndo()
  salvar()
  return true
}

async function executarADMLista(sock, msg, comando) {
  if (!(await ehADM(sock, msg))) return false
  const marcados = obterMarcados(msg)
  if (comando === 'desfazer') {
    if (desfazerADM()) {
      await publicarLista(sock)
      try { await sock.sendMessage(grupos.g1, { text: `↩️ *DESFEITO:* última atualização da lista revertida. Restam ${estado.historicoUndoLista.length} atualização(ões) no histórico.` }) } catch {}
    } else {
      try { await sock.sendMessage(grupos.g1, { text: 'ℹ️ Não há mais atualizações da lista para desfazer.' }) } catch {}
    }
    return true
  }
  if (!marcados.length) return false
  if (comando === 'final') {
    salvarUndoADM()
    let alterou = false
    for (const id of marcados) {
      if (mandarParaFinal(id)) alterou = true
    }
    if (alterou) { salvar(); await publicarLista(sock) }
    else estado.undoADM = null
    return true
  }
  if (comando === 'off') {
    salvarUndoADM()
    let alterou = false
    for (const id of marcados) {
      const alvo = jidNormalizedUser(id)
      const antesOnline = estado.online.length
      const antesEspera = estado.espera.length

      // Use o resultado da remoção, não apenas a diferença no tamanho das filas.
      // Se um ONLINE sai e alguém da ESPERA é promovido, os tamanhos podem ficar
      // iguais mesmo que o conteúdo da lista tenha mudado.
      const removido = colocarOffline(alvo)
      if (removido || estado.online.length !== antesOnline || estado.espera.length !== antesEspera) {
        alterou = true
      }
    }
    if (alterou) {
      promoverEspera()
      sincronizarFilaCompartilhadaComLista()
      salvar()
      await publicarLista(sock, { forcarAtualizacao: true })
    } else estado.undoADM = null
    return true
  }
  return false
}

/* =====================================
   COLOCAR ENTREGADOR EM POSIÇÃO
===================================== */

function colocarNaPosicao(id, posicao, nomeInformado = 'Entregador') {
  const usuario = jidNormalizedUser(String(id || ''))
  const alvo = Number(posicao)
  if (!usuario || !Number.isInteger(alvo) || alvo < 1 || estaBloqueado(usuario)) return false

  const pessoaExistente = (estado.online || []).find(p => jidNormalizedUser(String(p?.id || '')) === usuario) ||
    (estado.espera || []).find(p => jidNormalizedUser(String(p?.id || '')) === usuario)
  estado.online = (estado.online || []).filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)
  estado.espera = (estado.espera || []).filter(p => jidNormalizedUser(String(p?.id || '')) !== usuario)

  const cadastro = registrarEntregador(usuario, nomeInformado)
  const pessoa = pessoaExistente || {
    id: usuario,
    nome: cadastro?.nome || nomeInformado || 'Entregador',
    entrou: Date.now(),
    perdasConsecutivas: obterPerdasConsecutivas(usuario)
  }
  pessoa.id = usuario
  if (nomeInformado && nomeInformado !== 'Entregador' && (!pessoa.nome || pessoa.nome === 'Motoboy')) pessoa.nome = nomeInformado

  ajustarLimiteFila()
  if (estado.online.length < limiteAtual()) {
    estado.online.splice(Math.min(alvo - 1, estado.online.length), 0, pessoa)
    iniciarSessaoOnline(usuario, pessoa.nome)
  } else {
    estado.espera.push(pessoa)
  }
  promoverEspera()
  sincronizarFilaCompartilhadaComLista()
  salvar()
  return true
}

// Centraliza exclusões enviadas pelo bot. Com a política ativada, só permite
// exclusões nos grupos de entregadores (g1); nos grupos das empresas (g2),
// nenhuma mensagem é apagada, inclusive INDO inválido/duplicado e áudios.
async function apagarMensagemControlada(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (naoApagarMensagensEmpresas && jid.endsWith('@g.us')) {
    const chave = empresaDoGrupo(jid)
    const grupoEntregadores = chave ? String(empresas[chave]?.grupos?.g1 || '') : ''
    if (!chave || jid !== grupoEntregadores) {
      console.log('EXCLUSÃO BLOQUEADA: mensagens de grupos das empresas são preservadas.')
      return false
    }
  }
  try {
    await sock.sendMessage(jid, { delete: msg.key })
    return true
  } catch (erro) {
    console.log('Não foi possível apagar mensagem:', erro?.message || erro)
    return false
  }
}

/* =====================================
   MODO SILÊNCIO
===================================== */

function comandoEhSilencio(comando) {
  return /^(silêncio|silencio)$/i.test(String(comando || '').trim())
}

const COMANDOS_PERMITIDOS_SILENCIO = new Set([
  'online', 'offline', 'proximo', 'final', 'livre', 'ocupado', 'lista'
])

function comandoPermitidoNoSilencio(comando) {
  // Somente os sete comandos expressamente liberados pela Administração.
  // A normalização aceita diferenças de acento e pontuação, mas não aliases extras.
  const cmd = normalizarTexto(String(comando || '').trim()).replace(/[.!?]+$/g, '').trim()
  return COMANDOS_PERMITIDOS_SILENCIO.has(cmd)
}

async function processarModoSilencio(sock, msg, comando) {
  if (!grupos.g1 || msg?.key?.remoteJid !== grupos.g1) return false

  const ehAdm = await ehADM(sock, msg)

  // O comando é exclusivo do ADM e funciona como liga/desliga.
  if (comandoEhSilencio(comando)) {
    if (!ehAdm) return true

    estado.silencio = !estado.silencio
    salvar()

    try {
      await sock.sendMessage(grupos.g1, {
        text: estado.silencio
          ? 'Vms parar de falar de besteira no grupo'
          : 'Conversadeiro de bosta liberado 👍🏻'
      })
    } catch (e) {
      console.log('Erro ao avisar modo silêncio:', e.message)
    }

    return true
  }

  if (!estado.silencio || ehAdm) return false

  // Em silêncio, entregador só pode usar os comandos operacionais.
  if (comandoPermitidoNoSilencio(comando)) return false

  try {
    await apagarMensagemControlada(sock, msg)
  } catch (e) {
    console.log('Erro ao apagar mensagem no modo silêncio:', e.message)
  }

  return true
}

/* =====================================
   PROCESSAR GRUPO MOTOBOY
===================================== */

async function processarGrupoMotoboy(
  sock,
  msg
) {

  const texto =
    obterTexto(msg)

  // Menções são o alvo dos comandos ADM.
  // Ex.: "@entregador on" deve colocar o MENCIONADO online,
  // e nunca o ADM que enviou a mensagem.
  const comando = normalizarTexto(texto)
      .replace(/@\S+/g, '')
      .replace(/[.!?]+$/g, '')
      .replace(/\s+/g, ' ')
      .trim()

  const id =
    obterId(msg)

  const nome =
    obterNome(msg)

  // Modo silêncio: o ADM alterna o estado e entregadores ficam
  // limitados aos comandos operacionais permitidos.
  if (await processarModoSilencio(sock, msg, comando)) return


  /*
    COMANDOS ADMINISTRATIVOS PARA OUTRO ENTREGADOR
  */

  if (await ehADM(sock, msg)) {
    const marcadosADM = obterMarcados(msg)

    /*
      STATUS MANUAL PARA OUTRO ENTREGADOR
      @entregador ocupado -> 🔴
      @entregador 🟢       -> 🟢
    */
    if (marcadosADM.length && (COMANDOS_OCUPADO.includes(comando) || COMANDOS_LIVRE.includes(comando))) {
      let alterou = false

      for (const marcado of marcadosADM) {
        // "ocupado" força 🔴. "livre"/"🟢" libera o status manual,
        // fazendo o status voltar a ser calculado automaticamente.
        if (COMANDOS_OCUPADO.includes(comando)) {
          if (definirStatusManual(marcado, '🔴')) alterou = true
        } else {
          if (definirStatusManual(marcado, '🟢')) alterou = true
          else alterou = true
        }
      }

      if (alterou) await publicarLista(sock)
      return
    }

    // ON para OUTRO entregador: usa obrigatoriamente a menção como alvo.
    if (marcadosADM.length && COMANDOS_ON.includes(comando)) {
      let alterou = false

      for (const marcado of marcadosADM) {
        const alvo = jidNormalizedUser(marcado)
        if (!alvo) continue

        let nomeAlvo = 'Entregador'
        const cadastrado = (estado.entregadores || []).find(p => jidNormalizedUser(p.id) === alvo)
        if (cadastrado?.nome) nomeAlvo = cadastrado.nome

        // Tenta obter o nome atual do participante para a lista.
        try {
          const meta = await sock.groupMetadata(grupos.g1)
          const participante = (meta?.participants || []).find(p => jidNormalizedUser(p.id) === alvo)
          if (participante?.notify || participante?.name) {
            nomeAlvo = participante.notify || participante.name
          }
        } catch {}

        // Mesmo por ordem do ADM, entregador bloqueado não pode entrar ONLINE nem na espera.
        if (estaBloqueado(alvo)) {
          // Reconciliar a fila mesmo quando o ADM tenta colocar ONLINE alguém bloqueado.
          // A versão anterior só removia o alvo e salvava: podia deixar a vaga vazia,
          // não finalizar a sessão online e não promover o próximo da espera.
          const filaAntes = JSON.stringify({ online: estado.online || [], espera: estado.espera || [] })
          estado.online = (estado.online || []).filter(p => jidNormalizedUser(p?.id) !== alvo)
          estado.espera = (estado.espera || []).filter(p => jidNormalizedUser(p?.id) !== alvo)
          finalizarSessaoOnline(alvo)
          promoverEspera()
          sincronizarFilaCompartilhadaComLista()
          const filaDepois = JSON.stringify({ online: estado.online || [], espera: estado.espera || [] })
          if (filaAntes !== filaDepois) alterou = true
          salvar()
          continue
        }
        if (colocarOnline(alvo, nomeAlvo)) alterou = true
        else if (estado.online.some(p => jidNormalizedUser(p.id) === alvo) || estado.espera.some(p => jidNormalizedUser(p.id) === alvo)) alterou = true
      }

      // Esta mensagem já está no contexto isolado do grupo; não recarregar o escopo antigo pelo helper.
      if (alterou) {
        console.log(`[LISTA] Comando @entregador on reconhecido; online=${estado.online.length}; espera=${estado.espera.length}. Atualizando no contexto já carregado do grupo ${grupos.g1}.`)
        // Estamos dentro de processarMensagemInterna, que já carregou o estado deste grupo.
        // Chamar publicarListaEmpresaNoEstadoDoGrupo aqui recarregaria o estado antigo de escopo
        // e a rotina externa sobrescreveria a nova chave da mensagem no finally.
        await publicarLista(sock, { forcarAtualizacao: true })
      }
      return
    }

    // OFF para o entregador mencionado.
    if (marcadosADM.length && COMANDOS_OFF.includes(comando)) {
      let alterou = false
      const alvos = [...new Set(marcadosADM.map(marcado => jidNormalizedUser(marcado)).filter(Boolean))]
      for (const alvo of alvos) {
        // Não comparar somente a quantidade total: promoção da fila de espera
        // pode manter o total constante, embora o entregador mencionado tenha saído.
        const removido = colocarOffline(alvo)
        if (removido) alterou = true
      }
      if (alterou) {
        sincronizarFilaCompartilhadaComLista()
        // A fila foi consolidada em empresa.estado por sincronizarFilaCompartilhadaComLista().
        salvar()
        console.log(`[LISTA-OFF] Comando ADM por menção processado; alvos=${alvos.length}; online=${estado.online.length}; espera=${estado.espera.length}; fonte=empresa.estado.`)
        await publicarLista(sock, { forcarAtualizacao: true })
      } else {
        console.warn(`[LISTA-OFF] Comando ADM por menção não encontrou alvos nas filas atuais; alvos=${alvos.join(',') || 'nenhum'}; empresa=${empresaAtual}`)
      }
      return
    }

    // @nome X = coloca o entregador MENCIONADO na posição X.
    if (marcadosADM.length && /^\d+$/.test(comando)) {
      salvarUndoADM()
      let alterou = false
      const posicao = Number(comando)

      for (const marcado of marcadosADM) {
        if (colocarNaPosicao(marcado, posicao, obterNome(msg))) alterou = true
      }

      if (alterou) {
        salvar()
        await publicarLista(sock)
      } else {
        estado.undoADM = null
      }
      return
    }

    /*
      LIMITE INDIVIDUAL DE ENTREGAS SIMULTÂNEAS

      @entregador limite X
      @entregador limpar limite
      lista limite
    */
    if (marcadosADM.length && /^limite\s+\d+$/i.test(comando)) {
      const limite = Number(comando.match(/^limite\s+(\d+)$/i)?.[1])
      let alterou = false

      if (Number.isInteger(limite) && limite >= 1) {
        for (const marcado of marcadosADM) {
          if (definirLimiteEntregas(marcado, limite)) alterou = true
        }
      }

      if (alterou) {
        const mencoes = marcadosADM.map(id => jidNormalizedUser(id)).filter(Boolean)
        const textoLimite = `*LIMITE ATUALIZADO ${marcadosADM.map(id => `@${jidNormalizedUser(id).split('@')[0]}`).join(', ')} ${limite} ENTREGAS*`
        await sock.sendMessage(grupos.g1, {
          text: textoLimite,
          mentions: mencoes
        })
      }
      return
    }

    if (marcadosADM.length && comando === 'limpar limite') {
      let alterou = false

      for (const marcado of marcadosADM) {
        if (definirLimiteEntregas(marcado, null)) alterou = true
      }

      if (alterou) {
        const mencoes = marcadosADM.map(id => jidNormalizedUser(id)).filter(Boolean)
        const textoLimite = `*LIMITE ATUALIZADO ${marcadosADM.map(id => `@${jidNormalizedUser(id).split('@')[0]}`).join(', ')} SEM LIMITE*`
        await sock.sendMessage(grupos.g1, {
          text: textoLimite,
          mentions: mencoes
        })
      }
      return
    }

    if (comando === 'lista limite') {
      const limitados = obterEntregadoresComLimite()

      if (!limitados.length) {
        await sock.sendMessage(grupos.g1, {
          text: '*LISTA DE LIMITES*\\nNenhum entregador com limite de entregas.'
        })
        return
      }

      const mencoes = limitados.map(x => jidNormalizedUser(x.id))
      const linhas = limitados.map(
        x => `• @${jidNormalizedUser(x.id).split('@')[0]} — ${x.limiteEntregas} entregas`
      )

      await sock.sendMessage(grupos.g1, {
        text: `*LISTA DE LIMITES*\\n${linhas.join('\n')}`,
        mentions: mencoes
      })
      return
    }

    if (comando === 'desfazer') {
      await executarADMLista(sock, msg, 'desfazer')
      return
    }
    if (COMANDOS_FINAL.includes(comando) && marcadosADM.length) {
      await executarADMLista(sock, msg, 'final')
      return
    }
    if (comando === 'off' && marcadosADM.length) {
      await executarADMLista(sock, msg, 'off')
      return
    }
  }

  /*
    LISTA OFF / LISTA ON — somente ADM
    LISTA OFF congela a mensagem atualmente exibida.
    LISTA ON reativa as atualizações e sincroniza essa mesma mensagem com
    o estado operacional mais recente da fila.
  */
  if (await ehADM(sock, msg) && comando.trim() === 'lista off') {
    listaSuspensaADM = true
    salvar()
    try {
      await sock.sendMessage(grupos.g1, {
        text: '⏸️ *LISTA PAUSADA*\n\nA lista não será atualizada até o comando *lista on*.'
      })
    } catch (e) {
      console.log('Erro ao avisar lista off:', e.message)
    }
    return
  }

  if (await ehADM(sock, msg) && comando.trim() === 'lista on') {
    listaSuspensaADM = false
    salvar()
    await publicarLista(sock, { forcarAtualizacao: true })
    return
  }

  /*
    HORÁRIO DE PICO — somente ADM
  */
  if (
    await ehADM(sock, msg) &&
    /^(horário|horario) de pico$/i.test(comando.trim())
  ) {
    await alternarHorarioPico(sock)
    return
  }

  /*
    STATUS MANUAL DO PRÓPRIO ENTREGADOR
    ocupado -> 🔴
    livre    -> 🟢
  */
  if (COMANDOS_OCUPADO.includes(comando) || COMANDOS_LIVRE.includes(comando)) {
    const status = COMANDOS_OCUPADO.includes(comando) ? '🔴' : '🟢'

    if (definirStatusManual(id, status)) {
      await publicarLista(sock, { forcarAtualizacao: true })
    }

    return
  }

  /*
    ONLINE
  */

  if (
    COMANDOS_ON.includes(
      comando
    )
  ) {

    // Sempre reconciliar a lista ao receber ON no grupo, mesmo se o
    // entregador já constar como online no estado interno. Isso corrige
    // listas que ficaram desatualizadas após uma tentativa anterior de edição.
    colocarOnline(
      id,
      nome
    )

    console.log(`[LISTA] Comando on reconhecido; online=${estado.online.length}; espera=${estado.espera.length}. Atualizando no contexto já carregado do grupo ${grupos.g1}.`)
    // Não chamar o wrapper que recarrega o escopo: o estado atual já contém a inclusão deste entregador.
    await publicarLista(sock, { forcarAtualizacao: true })

    return
  }


  /*
    OFFLINE
  */

  if (
    COMANDOS_OFF.includes(
      comando
    )
  ) {

    if (
      colocarOffline(id)
    ) {

      await publicarLista(sock, { forcarAtualizacao: true })
    }

    return
  }


  /*
    PRÓXIMO
  */

  if (COMANDOS_PROXIMO.includes(comando)) {
    if (mandarParaFinal(id, 'proximo')) {
      await publicarLista(sock)
    }

    return
  }


  /*
    FERIADO
    ADM ativa o modo sem limite de ONLINE.
    "fim feriado" retorna aos limites normais.
  */

  if (await ehADM(sock, msg) && comando.trim() === 'feriado') {
    estado.feriado = !estado.feriado
    if (estado.feriado) promoverEspera()
    else { ajustarLimiteFila(); promoverEspera() }
    salvar()
    await sock.sendMessage(grupos.g1, { text: estado.feriado ? '🎉 *FERIADO ATIVADO* — lista ONLINE sem limite.' : '📅 *FERIADO ENCERRADO* — limites normais restaurados.' }).catch(() => {})
    await publicarLista(sock)
    return
  }

  if (await ehADM(sock, msg) && comando.trim() === 'fim feriado') {
    estado.feriado = false
    ajustarLimiteFila()
    promoverEspera()
    salvar()
    await publicarLista(sock)
    return
  }

  /*
    LIMPAR LISTA / FILA DE ESPERA
  */

  if (await ehADM(sock, msg) && comando.trim() === 'limpar listas') {
    finalizarTodasSessoesOnline()
    estado.online = []
    estado.espera = []
    estado.bloqueados = []
    estado.bloqueadosSemana = []
    estado.bloqueiosAutomaticosEscala = []
    estado.bloqueiosTaxas = []
    sincronizarFilaCompartilhadaComLista()
    salvar()
    console.log(`[LISTA-LIMPEZA] limpar listas aplicado | empresa=${empresaAtual} | online=${estado.online.length} | espera=${estado.espera.length}`)
    await publicarLista(sock, { forcarAtualizacao: true, naoPromoverEspera: true, naoAjustarLimiteFila: true })
    return
  }

  if (await ehADM(sock, msg) && comando.trim() === 'limpar lista') {
    for (const pessoa of estado.online) finalizarSessaoOnline(pessoa.id)
    estado.online = []
    sincronizarFilaCompartilhadaComLista()
    salvar()
    console.log(`[LISTA-LIMPEZA] limpar lista aplicado | empresa=${empresaAtual} | online=${estado.online.length} | espera=${estado.espera.length}`)
    await publicarLista(sock, { forcarAtualizacao: true, naoPromoverEspera: true, naoAjustarLimiteFila: true })
    return
  }

  if (await ehADM(sock, msg) && (
    comando.trim() === 'limpar fila de espera' ||
    comando.trim() === 'limpar espera'
  )) {
    estado.espera = []
    sincronizarFilaCompartilhadaComLista()
    salvar()
    await publicarLista(sock, { forcarAtualizacao: true, naoPromoverEspera: true, naoAjustarLimiteFila: true })
    return
  }

  if (await ehADM(sock, msg) && comando.trim() === 'limpar status') {
    limparTodosStatusVerde()
    statusPicoAnterior = {}
    salvar()
    await publicarListasTodasEmpresas(sock)
    return
  }

  /*
    FINAL / ÚLTIMO
  */

  if (COMANDOS_FINAL.includes(comando)) {
    if (mandarParaFinal(id)) await publicarLista(sock)
    return
  }

  /*
    DESBLOQUEAR
  */

  const ehComandoDesbloqueio =
    /^(desbloquear|desbloqueado|desbloqueia|desqueado|desbloqueado)$/i.test(comando.trim()) ||
    /^(desbloquear|desbloqueado|desbloqueia|desqueado)\s+@/i.test(comando.trim())

  if (ehComandoDesbloqueio && await ehADM(sock, msg)) {
    const marcados = obterMarcados(msg)

    for (const marcado of marcados) {
      desbloquear(marcado)
    }

    if (marcados.length) {
      await publicarLista(sock)
    }

    return
  }

  /*
    LIMPAR LISTA DE BLOQUEADOS
    Remove todos os entregadores das duas listas de bloqueio.
  */
  if (
    await ehADM(sock, msg) &&
    /^(limpar lista de bloqueados|limpar bloqueados)$/i.test(comando.trim())
  ) {
    estado.bloqueados = []
    estado.bloqueadosSemana = []
    estado.bloqueiosAutomaticosEscala = []
    estado.bloqueiosTaxas = []
    salvar()
    await publicarLista(sock)
    return
  }

  /*
    BLOQUEIOS FEITOS POR ADM
  */

  if (
    await ehADM(sock, msg) &&
    /^(bloqueado|bloqueado por uma semana)$/.test(comando)
  ) {

    const marcados =
      obterMarcados(msg)


    /*
      "bloqueado por uma semana"
    */

    const semanal =
      /bloqueado\s+por\s+uma\s+semana/i.test(
        comando
      )


    for (
      const marcado of marcados
    ) {

      bloquear(
        marcado,
        semanal
      )
    }


    if (
      marcados.length > 0
    ) {

      await publicarLista(
        sock
      )
    }
  }
}


/* =====================================
   CONCLUSÃO DE ENTREGA
===================================== */

function tipoDeMensagem(msg) {
  const m = msg?.message || {}
  if (m.stickerMessage) return 'sticker'
  if (m.audioMessage) return 'audio'
  if (m.imageMessage) return 'image'
  if (m.videoMessage) return 'video'
  return 'text'
}

/* =====================================
   IDENTIFICAR CONVERSA SOCIAL/ADMINISTRATIVA
===================================== */

function normalizarTexto(texto) {
  return String(texto || '')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .replace(/\s+/g, ' ')
    .trim()
}

// Bairros e localidades usados para interpretar pedidos das empresas em Patos-PB.
// O nome comercial da empresa não é usado como destino; só são extraídos nomes desta lista.
const BAIRROS_PATOS = [
  'Alto da Tubiba', 'Ana Leite', 'Bela Vista', 'Belo Horizonte', 'Bivar Olinto',
  'Brasília', 'Centro', 'Distrito Industrial', 'Jardim Magnólia', 'Jatobá',
  'Liberdade', 'Maternidade', 'Monte Castelo', 'Morada do Sol', 'Morro',
  'Noé Trajano', 'Nova Conquista', 'Novo Horizonte', 'Salgadinho',
  'Santa Cecília (Jardim Santa Cecília)', 'Santo Antônio', 'São Sebastião',
  'Sete Casas', 'Bairro dos Estados', 'Jardim Europa', 'Jardim Assunção',
  'Jardim Guanabara', 'Jardim Lacerda', 'Jardim Colonial', 'Jardim Espanha',
  'Jardim Santa Tereza', 'Santa Clara', 'Vila Mariana', 'Geraldo Carvalho',
  'Vista da Serra', 'Placas', 'Jardim Soraia'
]

const ALIASES_BAIRROS_PATOS = {
  'Condomínio dos Portugueses': ['cond dos portugueses', 'cond. dos portugueses', 'condominio dos portugueses'],
  'Condomínio Vila dos Lagos': ['cond vila dos lagos', 'cond. vila dos lagos', 'condominio vila dos lagos'],
  'Conjunto Geralda Medeiros': ['conj geralda medeiros', 'conj. geralda medeiros'],
  'Conjunto Itatiunga': ['conj itatiunga', 'conj. itatiunga'],
  'Conjunto José Mariz': ['conj jose mariz', 'conj. jose mariz'],
  'Conjunto São Judas Tadeu': ['conj s judas tadeu', 'conj. s. judas tadeu', 'conjunto s judas tadeu'],
  'Conjunto Geraldo Carvalho': ['conj geraldo carvalho', 'conj. geraldo carvalho'],
  'Conjunto Vista da Serra': ['conj vista da serra', 'conj. vista da serra'],
  'Distrito Industrial': ['dist industrial', 'dist. industrial'],
  'Loteamento Campestre': ['lot campestre', 'lot. campestre'],
  'Loteamento Luar do Angelita': ['lot luar do angelita', 'lot. luar do angelita'],
  'Loteamento Luar de Carmen Leda': ['lot luar de carmen leda', 'lot. luar de carmen leda'],
  'Nova Conquista': ['nova coquista'],
  'Belo Horizonte / Jardim Queiroz': ['belo horizonte', 'jardim queiroz']
}

function escaparRegex(texto) {
  return String(texto).replace(/[.*+?^${}()|[\\]\\]/g, '\\$&')
}

function listarBairrosPatos() {
  const adicionais = Object.keys(EMPRESA_CONFIG).flatMap(chave =>
    Array.isArray(empresas[chave]?.estado?.bairrosAdicionados) ? empresas[chave].estado.bairrosAdicionados : []
  )
  return [...new Set([...BAIRROS_PATOS, ...adicionais].map(x => String(x || '').trim()).filter(Boolean))]
}

function adicionarBairroPatos(nomeBairro) {
  const nome = String(nomeBairro || '').replace(/[\r\n\t]/g, ' ').replace(/\s+/g, ' ').trim()
  if (!nome || nome.length > 80) return { ok: false, motivo: 'invalido' }
  const existente = listarBairrosPatos().find(x => normalizarTexto(x) === normalizarTexto(nome))
  if (existente) return { ok: false, motivo: 'existe', nome: existente }
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const st = empresas[chave].estado
    if (!Array.isArray(st.bairrosAdicionados)) st.bairrosAdicionados = []
    st.bairrosAdicionados.push(nome)
  }
  salvar()
  return { ok: true, nome }
}

function extrairBairrosPatos(texto) {
  const normalizado = normalizarTexto(texto)
    .replace(/\b(cond|conj|lot|dist)\s*\./g, '$1 ')
    .replace(/[^a-z0-9]+/g, ' ')
    .replace(/\s+/g, ' ')
    .trim()
  const encontrados = []
  for (const bairro of BAIRROS_PATOS) {
    const formas = [bairro, ...(ALIASES_BAIRROS_PATOS[bairro] || [])]
    const achou = formas.some(forma => {
      const alvo = normalizarTexto(forma).replace(/[^a-z0-9]+/g, ' ').replace(/\s+/g, ' ').trim()
      return alvo && (` ${normalizado} `).includes(` ${alvo} `)
    })
    if (achou && !encontrados.includes(bairro)) encontrados.push(bairro)
  }
  // Nomes antigos/adicionais são reconhecidos, mas retornam o bairro oficial escolhido pelo ADM.
  for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
    const mapa = empresas[chaveEmpresa]?.estado?.mapeamentosBairrosAntigos || {}
    for (const [nomeAntigo, bairroOficial] of Object.entries(mapa)) {
      const alvo = normalizarTexto(nomeAntigo).replace(/[^a-z0-9]+/g, ' ').replace(/\s+/g, ' ').trim()
      if (alvo && (` ${normalizado} `).includes(` ${alvo} `) && BAIRROS_PATOS.some(b => normalizarTexto(b) === normalizarTexto(bairroOficial)) && !encontrados.some(b => normalizarTexto(b) === normalizarTexto(bairroOficial))) encontrados.push(bairroOficial)
    }
  }
  return encontrados
}

// Resolve o bairro extraído pelo OCR contra a lista oficial/dinâmica do Bot.
// Retorna o nome padronizado, nunca o texto cru da comanda quando há correspondência.
function identificarBairroComanda(texto) {
  const normalizar = valor => normalizarChaveAprendizado(valor).replace(/\s+/g, ' ').trim()
  const entrada = normalizar(texto)
  if (!entrada) return ''
  const candidatos = []
  const adicionar = (nome, oficial = nome) => {
    const n = String(nome || '').trim()
    const o = String(oficial || '').trim()
    if (!n || !o) return
    if (!candidatos.some(x => normalizar(x.nome) === normalizar(n) && normalizar(x.oficial) === normalizar(o))) candidatos.push({ nome: n, oficial: o })
  }
  for (const bairro of listarBairrosPatos()) adicionar(bairro, bairro)
  for (const [oficial, aliases] of Object.entries(ALIASES_BAIRROS_PATOS || {})) {
    for (const alias of aliases || []) adicionar(alias, oficial)
  }
  for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
    const estado = empresas[chaveEmpresa]?.estado || {}
    for (const [antigo, oficial] of Object.entries(estado.mapeamentosBairrosAntigos || {})) adicionar(antigo, oficial)
  }
  // Correspondências exatas primeiro; depois procura nomes completos dentro do texto.
  candidatos.sort((a, b) => normalizar(b.nome).length - normalizar(a.nome).length)
  const exato = candidatos.find(x => normalizar(x.nome) === entrada)
  if (exato) return exato.oficial
  for (const item of candidatos) {
    const alvo = normalizar(item.nome)
    if (alvo.length >= 4 && (` ${entrada} `).includes(` ${alvo} `)) return item.oficial
  }
  // Tolerância limitada a OCR: permite uma letra de diferença em nomes com 7+ letras,
  // somente quando o texto recebido é curto e parece ser o valor isolado do campo Bairro.
  if (entrada.length >= 7 && entrada.length <= 42) {
    const distanciaUm = (a, b) => {
      if (Math.abs(a.length - b.length) > 1) return false
      let i = 0, j = 0, erros = 0
      while (i < a.length && j < b.length) {
        if (a[i] === b[j]) { i++; j++; continue }
        if (++erros > 1) return false
        if (a.length > b.length) i++
        else if (b.length > a.length) j++
        else { i++; j++ }
      }
      if (i < a.length || j < b.length) erros++
      return erros <= 1
    }
    const aproximado = candidatos.find(x => {
      const alvo = normalizar(x.nome)
      return alvo.length >= 7 && !alvo.includes(' ') && !entrada.includes(' ') && distanciaUm(entrada, alvo)
    })
    if (aproximado) return aproximado.oficial
  }
  return ''
}

function ehPedidoEntregaPeloConteudo(texto) {
  // Regra operacional solicitada: no grupo das empresas, o texto só é
  // cadastrado automaticamente como entrega quando contém um bairro reconhecido.
  // Palavras como 'entrega', 'pedido' ou 'motoboy' sem bairro podem fazer parte
  // de uma conversa e não devem abrir corrida nem iniciar o temporizador.
  return extrairBairrosPatos(texto).length > 0
}


// Chaves de IA são configuradas pelo administrador no privado e guardadas fora do código.
// Em hospedagem, configure DATA_DIR para um volume persistente e gravável.
const ARQUIVO_CHAVES_IA = path.join(DATA_DIR, 'chego-chaves-ia.json')
const configuracoesIAEmMemoria = { gemini: '', openai: '', ocrspace: '' }
const aguardandoChaveIA = new Map()
let avisoChaveGeminiAusenteExibido = false
let geminiClassificacaoSemCotaAte = 0
// Evita martelar provedores cuja cota/saldo já foi recusada nesta execução.
let geminiPrivadaSemCotaAte = 0
const usoIAPrivada = new Map()
function permitirUsoIAPrivada(jid) {
  const usuario = jidNormalizedUser(jid)
  let conhecido = false
  try {
    conhecido = ehAdminPrivadoChego(usuario) || Object.values(empresas || {}).some(e =>
      (e?.estado?.entregadores || []).some(p => jidNormalizedUser(p.id) === usuario) ||
      (e?.estado?.cadastrosMotoboy || []).some(c => jidNormalizedUser(c.id) === usuario))
  } catch (_) {}
  const limiteHora = conhecido ? Number(process.env.IA_LIMITE_HORA) || 10 : 3
  const limiteDia = conhecido ? Number(process.env.IA_LIMITE_DIA) || 30 : 6
  const agora = Date.now()
  const usos = (usoIAPrivada.get(usuario) || []).filter(t => agora - t < 24 * 3600 * 1000)
  const naHora = usos.filter(t => agora - t < 3600 * 1000).length
  if (naHora >= limiteHora || usos.length >= limiteDia) { usoIAPrivada.set(usuario, usos); return false }
  usos.push(agora); usoIAPrivada.set(usuario, usos)
  if (usoIAPrivada.size > 5000) for (const [k, v] of usoIAPrivada) { if (!v.length || agora - v[v.length - 1] > 24 * 3600 * 1000) usoIAPrivada.delete(k) }
  return true
}
const MODELO_GEMINI = process.env.GEMINI_MODEL || 'gemini-3.8-flash'
let openAISemCotaAte = 0

function lerChavesIA() {
  try {
    const dados = JSON.parse(fs.readFileSync(ARQUIVO_CHAVES_IA, 'utf8'))
    configuracoesIAEmMemoria.gemini = typeof dados.gemini === 'string' ? dados.gemini.trim() : ''
    configuracoesIAEmMemoria.openai = typeof dados.openai === 'string' ? dados.openai.trim() : ''
    configuracoesIAEmMemoria.ocrspace = typeof dados.ocrspace === 'string' ? dados.ocrspace.trim() : ''
  } catch (_) { /* arquivo ainda não configurado */ }
  return configuracoesIAEmMemoria
}

function obterChaveIA(tipo) {
  const chaves = lerChavesIA()
  if (tipo === 'gemini') return process.env.GEMINI_API_KEY || process.env.GOOGLE_API_KEY || chaves.gemini || ''
  return process.env.OPENAI_API_KEY || process.env.OPENAI_API_TOKEN || chaves.openai || ''
}

function salvarChavesIA() {
  fs.mkdirSync(DATA_DIR, { recursive: true })
  const temporario = `${ARQUIVO_CHAVES_IA}.tmp`
  fs.writeFileSync(temporario, JSON.stringify(configuracoesIAEmMemoria, null, 2), { mode: 0o600 })
  try { fs.chmodSync(temporario, 0o600) } catch (_) {}
  fs.renameSync(temporario, ARQUIVO_CHAVES_IA)
  try { fs.chmodSync(ARQUIVO_CHAVES_IA, 0o600) } catch (_) {}
}

const JID_ADM_IURY_BAIRRO = '5584921524273@s.whatsapp.net'

async function avisarAdmBairroNaoIdentificado(sock, mensagemOriginal, grupoOrigem, mensagemId) {
  const jidAdm = JID_ADM_IURY_BAIRRO
  // Encaminha a mensagem original ao privado do ADM para que ele possa
  // identificar o bairro sem depender do formato do número digitado.
  try {
    if (mensagemOriginal && typeof sock.copyNForward === 'function') {
      await sock.copyNForward(jidAdm, mensagemOriginal, true)
    } else if (mensagemOriginal) {
      // Não enviar o aviso genérico: reproduzir o texto original da empresa.
      const conteudo = mensagemOriginal.message || mensagemOriginal
      const textoOriginal = String(
        conteudo?.conversation ||
        conteudo?.extendedTextMessage?.text ||
        conteudo?.imageMessage?.caption ||
        conteudo?.videoMessage?.caption ||
        conteudo?.documentMessage?.caption ||
        conteudo?.audioMessage?.caption ||
        conteudo?.buttonsResponseMessage?.selectedDisplayText || ''
      ).trim()
      if (textoOriginal) {
        await sock.sendMessage(jidAdm, {
          text: textoOriginal,
          contextInfo: { forwardingScore: 1, isForwarded: true }
        })
      } else {
        console.log('Mensagem original sem texto/caption; encaminhamento nativo indisponível.')
      }
    }
  } catch (e) {
    console.log('Falha ao encaminhar mensagem original de bairro não identificado:', e?.message || e)
    // Fallback sem citação: se o encaminhamento nativo falhar, envia o conteúdo
    // textual original como uma nova mensagem ao ADM, sem responder/ citar a empresa.
    try {
      const conteudo = mensagemOriginal?.message || mensagemOriginal
      const textoOriginal = String(
        conteudo?.conversation ||
        conteudo?.extendedTextMessage?.text ||
        conteudo?.imageMessage?.caption ||
        conteudo?.videoMessage?.caption ||
        conteudo?.documentMessage?.caption ||
        conteudo?.buttonsResponseMessage?.selectedDisplayText || ''
      ).trim()
      if (textoOriginal) {
        await sock.sendMessage(jidAdm, {
          text: `↪️ *MENSAGEM DA EMPRESA (encaminhamento alternativo)*\n\n${textoOriginal}`,
          contextInfo: { forwardingScore: 1, isForwarded: true }
        })
      }
    } catch (fallbackErro) {
      console.log('Falha no encaminhamento alternativo da mensagem da empresa:', fallbackErro?.message || fallbackErro)
    }
  }
}

async function processarConfiguracaoChavesIA(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const usuario = jidNormalizedUser(jid)
  const texto = String(obterTexto(msg) || '').trim()
  if (!ehAdminPrivadoChego(usuario)) {
    if (/^(?:configurar|status ia|status ocr|status ocrspace|apagar chave|remover chave)\s+(?:gemini|openai|ocr|ocrspace)|^status ia$|^status ocr$|^status ocrspace$/.test(normalizarTexto(texto))) {
      await sock.sendMessage(jid, { text: '🔒 Este comando só pode ser usado por um administrador autorizado.' })
      return true
    }
    return false
  }
  const normalizado = normalizarTexto(texto).replace(/[.!?]+$/g, '').trim()
  const pendente = aguardandoChaveIA.get(usuario)
  if (pendente) {
    if (normalizado === 'cancelar') {
      aguardandoChaveIA.delete(usuario)
      await sock.sendMessage(jid, { text: 'Configuração cancelada. Nenhuma chave foi alterada.' })
      return true
    }
    const chave = texto.replace(/\s/g, '')
    const pareceValida = pendente === 'openai' ? /^sk-(?:proj-)?[A-Za-z0-9_-]{20,}$/.test(chave) : pendente === 'ocrspace' ? chave.length >= 8 && !/\s/.test(chave) : /^(?:AIza[\w-]{20,}|AQ\.[A-Za-z0-9_-]{20,})$/.test(chave)
    if (!pareceValida) {
      await sock.sendMessage(jid, { text: `Não reconheci o formato da chave ${pendente === 'openai' ? 'OpenAI' : pendente === 'ocrspace' ? 'OCR.space' : 'Gemini'}. Envie a chave completa ou digite CANCELAR. A chave não foi salva.` })
      return true
    }
    lerChavesIA()
    configuracoesIAEmMemoria[pendente] = chave
    try {
      salvarChavesIA()
      aguardandoChaveIA.delete(usuario)
      await sock.sendMessage(jid, { text: `✅ Chave ${pendente === 'openai' ? 'OpenAI' : pendente === 'ocrspace' ? 'OCR.space' : 'Gemini'} salva. Por segurança, não vou repetir nem exibir a chave. Use *Status IA* para conferir a configuração.` })
      console.log(`🔐 Chave ${pendente} atualizada pelo administrador autorizado (valor oculto).`)
    } catch (e) {
      aguardandoChaveIA.delete(usuario)
      console.log(`❌ Não foi possível salvar a chave ${pendente}: ${e?.message || e}`)
      await sock.sendMessage(jid, { text: '❌ Não consegui salvar a chave no disco. Verifique se DATA_DIR é gravável e persistente no servidor. A chave não foi confirmada como salva.' })
    }
    return true
  }
  if (normalizado === 'status ia' || normalizado === 'status das ia' || normalizado === 'status das ias') {
    const g = !!obterChaveIA('gemini')
    const o = !!obterChaveIA('openai')
    const c = !!obterChaveOCRSpace()
    await sock.sendMessage(jid, { text: `🤖 *STATUS DAS IAs*\n\nGemini: ${g ? '✅ chave configurada' : '❌ sem chave'}\nOpenAI: ${o ? '✅ chave configurada' : '❌ sem chave'}\nOCR.space: ${c ? '✅ chave configurada' : '❌ sem chave'}\n\nO bot tenta Gemini primeiro e OpenAI como reserva. Este status verifica a presença das chaves, não garante que a API esteja válida ou com créditos.` })
    return true
  }
  if (normalizado === 'status ocr' || normalizado === 'status ocrspace') {
    await sock.sendMessage(jid, { text: `OCR.space: ${obterChaveOCRSpace() ? '✅ chave configurada' : '❌ sem chave'}. Isso confirma apenas que a chave está presente, não que a API esteja válida.` })
    return true
  }
  if (normalizado === 'configurar ocr' || normalizado === 'configurar ocrspace' || normalizado === 'configurar chave ocr') {
    aguardandoChaveIA.set(usuario, 'ocrspace')
    await sock.sendMessage(jid, { text: '🔑 Envie agora a chave da API OCR.space em uma única mensagem privada. Não vou repeti-la. Digite CANCELAR para desistir.' })
    return true
  }
  if (normalizado === 'apagar chave ocr' || normalizado === 'apagar chave ocrspace') {
    lerChavesIA(); configuracoesIAEmMemoria.ocrspace = ''
    try { salvarChavesIA(); await sock.sendMessage(jid, { text: 'Chave OCR.space salva pelo bot apagada.' }) } catch (_) { await sock.sendMessage(jid, { text: 'Não consegui apagar a chave por falta de permissão de escrita.' }) }
    return true
  }
  if (normalizado === 'configurar gemini' || normalizado === 'configurar chave gemini') {
    aguardandoChaveIA.set(usuario, 'gemini')
    await sock.sendMessage(jid, { text: '🔑 Envie agora a chave da API do Gemini em uma única mensagem. Não vou repeti-la na resposta. Digite CANCELAR para desistir.' })
    return true
  }
  if (normalizado === 'configurar openai' || normalizado === 'configurar chave openai' || normalizado === 'configurar chatgpt') {
    aguardandoChaveIA.set(usuario, 'openai')
    await sock.sendMessage(jid, { text: '🔑 Envie agora a chave da API da OpenAI em uma única mensagem. Não vou repeti-la na resposta. Digite CANCELAR para desistir.' })
    return true
  }
  if (normalizado === 'apagar chave gemini' || normalizado === 'remover chave gemini' || normalizado === 'apagar gemini') {
    lerChavesIA(); configuracoesIAEmMemoria.gemini = ''
    try { salvarChavesIA(); await sock.sendMessage(jid, { text: 'Chave Gemini salva pelo bot foi apagada. Uma variável de ambiente GEMINI_API_KEY, se existir, continua tendo prioridade.' }) } catch (_) { await sock.sendMessage(jid, { text: 'Não consegui apagar a chave por falta de permissão de escrita.' }) }
    return true
  }
  if (normalizado === 'apagar chave openai' || normalizado === 'remover chave openai' || normalizado === 'apagar openai') {
    lerChavesIA(); configuracoesIAEmMemoria.openai = ''
    try { salvarChavesIA(); await sock.sendMessage(jid, { text: 'Chave OpenAI salva pelo bot foi apagada. Uma variável de ambiente OPENAI_API_KEY, se existir, continua tendo prioridade.' }) } catch (_) { await sock.sendMessage(jid, { text: 'Não consegui apagar a chave por falta de permissão de escrita.' }) }
    return true
  }
  return false
}

function extrairEnderecoParaMapa(texto) {
  let t = String(texto || '').trim().replace(/[\r\n]+/g, ' ').replace(/\s+/g, ' ')
  // Remove a pergunta sobre preço/entrega e mantém somente o endereço solicitado.
  t = t.replace(/^(?:por favor[, ]*)?(?:me diga|me diz|quero saber|sabe me dizer|quanto fica|qual (?:é )?o valor|qual o preço|quanto custa|quanto sai|tem como saber)\s+(?:a entrega|o valor da entrega|o preço da entrega|a taxa da entrega)?\s*(?:para|pro|pra|no|na|do|da)?\s*(?:o endereço|endereço|o endereco|endereco)?\s*/i, '')
  t = t.replace(/^(?:a entrega|o valor da entrega|o preço da entrega)\s+(?:para|pro|pra)\s+(?:o endereço|endereço|o endereco|endereco)\s+/i, '')
  t = t.replace(/[?!.]+$/g, '').trim()
  // Remove molduras comuns ainda presentes, sem apagar nome de rua ou bairro.
  t = t.replace(/^(?:endereço|endereco)\s*[:,-]?\s*/i, '').trim()
  return t
}

function pareceEnderecoParaMapa(texto) {
  const original = String(texto || '').trim()
  if (original.length < 8 || original.length > 240) return false
  const t = extrairEnderecoParaMapa(original)
  if (t.length < 8 || t.length > 180) return false
  const temNumero = /\b\d{1,5}\b/.test(t)
  const temRuaOuBairro = /\b(rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|bairro|pra[cç]a|lote|quadra|n[uú]mero|nº)\b/i.test(t)
  return temNumero && temRuaOuBairro
}

function criarContextoDadosEntregador(jid) {
  const usuario = jidNormalizedUser(jid)
  const regs = coletarRegistrosRelatorio('últimos 28 dias').filter(reg => mesmoEntregadorRelatorio(reg, { id: usuario, nome: '' }))
  const comTempo = regs.filter(reg => Number.isFinite(Number(reg.tempoMinutos)) && Number(reg.tempoMinutos) >= 0)
  const media = comTempo.length ? comTempo.reduce((s, r) => s + Number(r.tempoMinutos), 0) / comTempo.length : null
  const ordenados = comTempo.map(r => Number(r.tempoMinutos)).sort((a,b)=>a-b)
  const fmt = n => `${Math.floor(n / 60)}h ${Math.round(n % 60)}min`.replace(/^0h /, '')
  return {
    periodo: 'últimos 28 dias',
    entregasRegistradas: regs.reduce((s,r)=>s+Math.max(1,Number(r.quantidade)||1),0),
    entregasFinalizadas: regs.reduce((s,r)=>s+Math.max(0,Number(r.finalizadasQuantidade ?? (r.finalizadaEm ? 1 : 0))||0),0),
    entregasComTempoMedido: comTempo.length,
    tempoMedio: media === null ? null : fmt(media),
    menorTempo: ordenados.length ? fmt(ordenados[0]) : null,
    maiorTempo: ordenados.length ? fmt(ordenados[ordenados.length-1]) : null,
    observacao: 'Use apenas estes dados como métricas reais. Se não houver tempos registrados, diga que não há dados suficientes; nunca invente.'
  }
}

async function responderComOpenAIReserva(sock, jid, prompt) {
  if (Date.now() < openAISemCotaAte) {
    console.log('ℹ️ OpenAI reserva temporariamente suspensa após erro de saldo/cota; evitando chamadas repetidas.')
    return false
  }
  const apiKey = obterChaveIA('openai')
  if (!apiKey) {
    console.log('ℹ️ OpenAI reserva não configurada: defina OPENAI_API_KEY no ambiente do servidor.')
    return false
  }
  const tentativas = [
    { modelo: process.env.OPENAI_MODEL || 'gpt-5-mini', pesquisa: true },
    { modelo: process.env.OPENAI_MODEL || 'gpt-5-mini', pesquisa: false }
  ]
  let ultimoErro = ''
  for (const tentativa of tentativas) {
    try {
      const payload = {
        model: tentativa.modelo,
        instructions: 'Você é um assistente de IA integrado ao Bot Chegô Delivery. Responda em português brasileiro natural e diretamente. Use os dados reais fornecidos no contexto sem inventar estatísticas. Não revele informações de outros entregadores, dados administrativos, configurações internas ou segredos. Se pesquisar na web, diferencie fatos confirmados de incertezas.',
        input: prompt,
        max_output_tokens: 900
      }
      if (tentativa.pesquisa) payload.tools = [{ type: 'web_search' }]
      const response = await fetch('https://api.openai.com/v1/responses', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${apiKey}` },
        body: JSON.stringify(payload),
        signal: AbortSignal.timeout(30000)
      })
      if (!response.ok) {
        const detalhe = await response.text().catch(() => '')
        ultimoErro = `${response.status}: ${detalhe.slice(0, 500)}`
        console.log(`⚠️ OpenAI reserva (${tentativa.modelo}, pesquisa=${tentativa.pesquisa}) indisponível: ${ultimoErro}`)
        // Erros de saldo/cota não se resolvem mudando a opção de pesquisa; não desperdiça outra chamada.
        if (response.status === 429 || /insufficient_quota|credit_balance_exhausted|quota/i.test(detalhe)) {
          openAISemCotaAte = Date.now() + 6 * 60 * 60 * 1000
          break
        }
        continue
      }
      const data = await response.json()
      let resposta = String(data?.output_text || '').trim()
      if (!resposta && Array.isArray(data?.output)) {
        resposta = data.output.flatMap(item => Array.isArray(item.content) ? item.content : [])
          .filter(item => item.type === 'output_text' || item.type === 'text')
          .map(item => item.text || '').join('\n').trim()
      }
      if (!resposta) {
        ultimoErro = 'A API OpenAI respondeu sem texto.'
        continue
      }
      console.log(`✅ OpenAI respondeu como reserva (${tentativa.modelo}, pesquisa=${tentativa.pesquisa}).`)
      await enviarTextoCompleto(sock, jid, resposta.slice(0, 5000))
      return true
    } catch (e) {
      ultimoErro = e?.message || String(e)
      console.log(`⚠️ Erro OpenAI reserva (${tentativa.modelo}, pesquisa=${tentativa.pesquisa}): ${ultimoErro}`)
    }
  }
  console.log(`❌ OpenAI reserva também falhou: ${ultimoErro}`)
  return false
}

function obterChaveOCRSpace() {
  const chaves = lerChavesIA()
  return process.env.OCRSPACE_API_KEY || process.env.OCR_SPACE_API_KEY || chaves.ocrspace || ''
}

async function extrairTextoOCRSpace(buffer) {
  const chave = obterChaveOCRSpace()
  if (!chave) return ''
  const form = new FormData()
  form.append('file', new Blob([buffer], { type: 'image/jpeg' }), 'imagem.jpg')
  form.append('language', 'por')
  form.append('isOverlayRequired', 'false')
  const resposta = await fetch('https://api.ocr.space/parse/image', { method: 'POST', headers: { apikey: chave }, body: form, signal: AbortSignal.timeout(25000) })
  if (!resposta.ok) throw new Error(`OCR.space HTTP ${resposta.status}`)
  const dados = await resposta.json()
  if (dados?.IsErroredOnProcessing) throw new Error('OCR.space não conseguiu processar a imagem')
  return String((dados?.ParsedResults || []).map(x => x?.ParsedText || '').join('\n')).trim()
}

// A leitura de comandas usa exclusivamente OCR tradicional e regras locais.
const ARQUIVO_APRENDIZADO_COMANDAS = path.join(DATA_DIR, 'chego-aprendizado-comandas.json')
const ultimasComandasOCRPorUsuario = new Map()
// Correções exatas por hash ficam apenas em memória. Modelos persistidos guardam
// somente nome do estabelecimento, assinatura estrutural e aliases de rótulos.
const correcoesPorHashImagem = new Map()
const estabelecimentoPendentePorUsuario = new Map()
let aliasesBairroAprendidos = {}
let modelosLayoutComandas = {}
let termosRemoverComanda = []
const selecaoRemovidosPendentePorUsuario = new Map()
let aliasesDicionarioComanda = {}
function normalizarChaveAprendizado(valor) {
  return String(valor || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/[^a-z0-9 ]/g, ' ').replace(/\s+/g, ' ').trim()
}
function assinaturaLayoutComanda(texto) {
  const linhas = String(texto || '').split(/\n+/).map(x => x.trim()).filter(Boolean)
  const estrutura = linhas.map(l => {
    const m = l.match(/^\s*([^:：]{2,35})\s*[:：]/)
    if (m) return normalizarChaveAprendizado(m[1]).slice(0, 30)
    if (/\b(?:cliente|telefone|endereco|endereço|bairro|apartamento|pedido|entrega|referencia|referência|localizador)\b/i.test(l)) return normalizarChaveAprendizado(l).split(' ').slice(0, 4).join(' ')
    return ''
  }).filter(Boolean).slice(0, 24)
  const cabecalho = linhas.slice(0, 5).filter(l => !/\d/.test(l) && !/^\s*(?:cliente|telefone|endereco|endereço|bairro|apartamento|pedido|entrega|referencia|referência|localizador)\s*[:：]/i.test(l)).slice(0, 2).map(normalizarChaveAprendizado).map(x => x.split(' ').slice(0, 4).join(' ')).join('|')
  return crypto.createHash('sha256').update(`${cabecalho}::${estrutura.join('|')}`).digest('hex').slice(0, 24)
}
function carregarAprendizadoComandas() {
  try {
    const dados = JSON.parse(fs.readFileSync(ARQUIVO_APRENDIZADO_COMANDAS, 'utf8'))
    aliasesBairroAprendidos = dados && dados.aliasesBairro && typeof dados.aliasesBairro === 'object' ? dados.aliasesBairro : {}
    modelosLayoutComandas = dados && dados.modelosLayout && typeof dados.modelosLayout === 'object' ? dados.modelosLayout : {}
    termosRemoverComanda = Array.isArray(dados.termosRemoverComanda) ? dados.termosRemoverComanda.filter(x => typeof x === 'string' && x.trim()).slice(0, 100) : []
    aliasesDicionarioComanda = dados && dados.aliasesDicionarioComanda && typeof dados.aliasesDicionarioComanda === 'object' ? dados.aliasesDicionarioComanda : {}
  } catch (_) { aliasesBairroAprendidos = {}; modelosLayoutComandas = {}; termosRemoverComanda = []; aliasesDicionarioComanda = {} }
}
function salvarAprendizadoComandas() {
  try {
    fs.mkdirSync(path.dirname(ARQUIVO_APRENDIZADO_COMANDAS), { recursive: true })
    atomicWriteFile(ARQUIVO_APRENDIZADO_COMANDAS, JSON.stringify({ versao: 4, atualizadoEm: new Date().toISOString(), aliasesBairro: aliasesBairroAprendidos, modelosLayout: modelosLayoutComandas, termosRemoverComanda, aliasesDicionarioComanda }, null, 2))
    return true
  } catch (e) {
    console.error('[APRENDIZADO-COMANDAS] Não foi possível salvar os modelos; aprendizado pode ficar só nesta sessão:', e?.message || e)
    return false
  }
}
function aplicarRemocoesComanda(texto) {
  let linhas = String(texto || '').split(/\r?\n/)
  for (const termo of termosRemoverComanda) {
    const literal = String(termo || '').trim()
    if (!literal) continue
    const chaveTermo = normalizarChaveAprendizado(literal)
    const escaped = literal.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
    // Remove o termo como palavra/expressão completa, sem apagar partes de outras palavras.
    const regex = new RegExp(`(?<![\\p{L}\\p{N}])${escaped}(?![\\p{L}\\p{N}])`, 'giu')
    linhas = linhas.filter(linha => {
      const l = String(linha || '').trim()
      if (!l) return false
      if (normalizarChaveAprendizado(l) === chaveTermo) return false
      const campo = l.match(/^[^:：]{1,40}\s*[:：]\s*(.*)$/)
      if (campo && normalizarChaveAprendizado(campo[1]) === chaveTermo) return false
      return true
    }).map(linha => String(linha).replace(regex, '').replace(/[ \t]{2,}/g, ' ').replace(/\s*[:：]\s*$/g, '').trim()).filter(Boolean)
  }
  return linhas.join('\n')
}
async function processarComandoRemoverComanda(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const original = String(obterTexto(msg) || '').trim()
  // Aceita tanto "Remover prédio" quanto o formato antigo "Remover: prédio".
  const comando = original.match(/^remover(?:\s*[:：]\s*|\s+)([\s\S]+)$/i)
  if (!comando) return false
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Somente ADM pode cadastrar termos para remoção das comandas.' })
    return true
  }
  const conteudo = comando[1].trim()
  const termos = conteudo.split(/\r?\n/).map(linha => linha.trim()).filter(Boolean)
  if (!termos.length || termos.some(t => t.length > 80 || /^remover$/i.test(t))) {
    await sock.sendMessage(jid, { text: 'Informe o termo que deve ser ignorado nas futuras leituras. Exemplo: *Remover prédio*' })
    return true
  }
  let adicionados = 0
  for (const termo of termos) {
    const chave = normalizarChaveAprendizado(termo)
    if (!chave) continue
    if (!termosRemoverComanda.some(x => normalizarChaveAprendizado(x) === chave)) {
      if (termosRemoverComanda.length >= 100) termosRemoverComanda.shift()
      termosRemoverComanda.push(termo)
      adicionados++
    }
  }
  const salvou = salvarAprendizadoComandas()
  await sock.sendMessage(jid, { text: `${adicionados ? '✅' : 'ℹ️'} ${adicionados ? 'Regra adicionada' : 'Esse texto já estava cadastrado'}: ${termos.join(', ')}.\n\nVou ignorar esse texto nas próximas leituras de comandas${salvou ? ', e a regra foi salva no armazenamento disponível do servidor.' : ', mas ⚠️ o servidor não permitiu gravar em disco; ela pode ser perdida se o bot reiniciar.'}` })
  return true
}

// Comando ADM: lista as regras cadastradas via Remover: e permite excluir uma pelo número.
async function processarComandoRemovidos(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if ((!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) || msg?.key?.fromMe) return false
  const original = String(obterTexto(msg) || '').trim()
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  const texto = normalizarTexto(original).replace(/[.!?]+$/g, '').trim()
  const pendente = selecaoRemovidosPendentePorUsuario.get(usuario)

  if (pendente) {
    if (/^(?:cancelar|cancela|voltar)$/i.test(texto)) {
      selecaoRemovidosPendentePorUsuario.delete(usuario)
      await sock.sendMessage(jid, { text: 'Seleção cancelada. Nenhuma regra foi removida.' })
      return true
    }
    if (!/^\d+$/.test(texto)) return false
    const numero = Number(texto)
    if (!Number.isSafeInteger(numero) || numero < 1 || numero > pendente.itens.length) {
      await sock.sendMessage(jid, { text: `Número inválido. Responda com um número de 1 a ${pendente.itens.length}, ou envie *Cancelar*.` })
      return true
    }
    const alvo = pendente.itens[numero - 1]
    const indiceAtual = termosRemoverComanda.findIndex(x => normalizarChaveAprendizado(x) === normalizarChaveAprendizado(alvo))
    selecaoRemovidosPendentePorUsuario.delete(usuario)
    if (indiceAtual < 0) {
      await sock.sendMessage(jid, { text: 'Essa regra já não está cadastrada. Envie *Removidos* para atualizar a lista.' })
      return true
    }
    const [removido] = termosRemoverComanda.splice(indiceAtual, 1)
    const salvou = salvarAprendizadoComandas()
    await sock.sendMessage(jid, { text: `✅ Regra removida: *${removido}*.\n${salvou ? 'A alteração foi salva no armazenamento disponível do servidor.' : '⚠️ O servidor não permitiu gravar a alteração em disco; ela pode ser perdida se o Bot reiniciar.'}` })
    return true
  }

  if (texto !== 'removidos') return false
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Somente ADM pode consultar e remover itens dessa lista.' })
    return true
  }
  if (!termosRemoverComanda.length) {
    await sock.sendMessage(jid, { text: 'A lista de itens cadastrados pelo comando *Remover:* está vazia.' })
    return true
  }
  const itens = [...termosRemoverComanda]
  selecaoRemovidosPendentePorUsuario.set(usuario, { itens })
  const lista = itens.map((item, i) => `${i + 1}. ${item}`).join('\n')
  await sock.sendMessage(jid, { text: `🗑️ *Itens cadastrados pelo comando Remover:*\n\n${lista}\n\nEnvie somente o número do item que deseja retirar da lista.\nEnvie *Cancelar* para desistir.` })
  return true
}
// Comando ADM no privado para ampliar o dicionário local de rótulos de comandas.
// Formato: Adicionar\nEndereço: End, rua, R. (uma linha por campo).
async function processarAdicionarVariacoesDicionarioComanda(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const original = String(obterTexto(msg) || '').trim()
  if (!/^adicionar(?:\s*\r?\n|\s+)[\s\S]+/i.test(original)) return false
  const linhas = original.split(/\r?\n/).map(x => x.trim()).filter(Boolean)
  if (linhas.length < 2 || normalizarTexto(linhas[0]) !== 'adicionar') return false
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Somente ADM pode cadastrar variações no dicionário de comandas.' })
    return true
  }
  const camposValidos = new Map(DICIONARIO_ROTULOS_COMANDA.map(item => [normalizarChaveAprendizado(item.canonico), item.canonico]))
  const alteracoes = []
  const erros = []
  for (const linha of linhas.slice(1)) {
    const m = linha.match(/^\s*([^:：]{1,48})\s*[:：]\s*(.+?)\s*$/)
    if (!m) { erros.push(`“${linha}”: use Campo: variação 1, variação 2`); continue }
    const chaveCampo = normalizarChaveAprendizado(m[1])
    const canonico = camposValidos.get(chaveCampo)
    if (!canonico) { erros.push(`“${m[1]}”: campo desconhecido`); continue }
    const variacoes = m[2].split(/[,;|]/).map(x => x.trim()).filter(Boolean)
    if (!variacoes.length || variacoes.some(x => x.length > 48 || x.length < 1)) { erros.push(`“${m[1]}”: variação vazia ou muito longa`); continue }
    if (!aliasesDicionarioComanda[canonico]) aliasesDicionarioComanda[canonico] = []
    for (const variacao of variacoes) {
      const chave = normalizarChaveAprendizado(variacao)
      if (!chave) continue
      const existente = aliasesDicionarioComanda[canonico].some(x => normalizarChaveAprendizado(x) === chave) || DICIONARIO_ROTULOS_COMANDA.find(item => item.canonico === canonico).aliases.some(x => normalizarChaveAprendizado(x) === chave)
      if (existente) continue
      const conflito = DICIONARIO_ROTULOS_COMANDA.some(item => item.canonico !== canonico && item.aliases.some(x => normalizarChaveAprendizado(x) === chave)) || Object.entries(aliasesDicionarioComanda).some(([campo, lista]) => campo !== canonico && Array.isArray(lista) && lista.some(x => normalizarChaveAprendizado(x) === chave))
      if (conflito) { erros.push(`“${variacao}”: já está associado a outro campo`); continue }
      if (aliasesDicionarioComanda[canonico].length >= 100) { erros.push(`Limite de 100 variações atingido para ${canonico}`); break }
      aliasesDicionarioComanda[canonico].push(variacao)
      alteracoes.push(`${canonico}: ${variacao}`)
    }
  }
  if (!alteracoes.length && !erros.length) erros.push('Nenhuma variação nova foi encontrada.')
  const salvou = alteracoes.length ? salvarAprendizadoComandas() : true
  let resposta = alteracoes.length ? `✅ *Dicionário de comandas atualizado*\n\n${alteracoes.map(x => `• ${x}`).join('\n')}\n\n` : ''
  if (alteracoes.length) resposta += salvou ? 'As variações foram salvas e serão usadas nas próximas leituras.' : '⚠️ As variações estão ativas nesta sessão, mas o servidor não permitiu salvá-las em disco; podem ser perdidas ao reiniciar.'
  if (erros.length) resposta += `${resposta ? '\n\n' : ''}⚠️ *Não cadastradas:*\n${erros.map(x => `• ${x}`).join('\n')}`
  await sock.sendMessage(jid, { text: resposta })
  return true
}

// Dicionário local de sinônimos de comandas. Não usa serviços de IA: apenas
// normaliza rótulos conhecidos e converte variantes para os campos do parser.
const DICIONARIO_ROTULOS_COMANDA = [
  { canonico: 'Cliente', aliases: ['cliente', 'nome', 'nome cliente', 'nome do cliente', 'destinatario', 'recebedor', 'entregar para', 'entregue para', 'consumidor', 'nome destinatario', 'dados do cliente', 'cliente entrega'] },
  { canonico: 'Telefone', aliases: ['telefone', 'telefone cliente', 'telefone do cliente', 'tel', 'tel cliente', 'celular', 'whatsapp', 'fone', 'contato', 'numero de contato', 'telefone destinatario', 'telefone para contato', 'cel', 'fone cliente'] },
  { canonico: 'Contato/central iFood', aliases: ['central ifood', 'telefone ifood', 'contato ifood', 'suporte ifood', 'telefone da central', 'central de atendimento ifood'] },
  { canonico: 'Localizador iFood', aliases: ['localizador', 'localizador ifood', 'codigo localizador', 'codigo do localizador', 'codigo de entrega', 'codigo do pedido', 'id pedido', 'id do pedido', 'pedido ifood', 'identificador do pedido'] },
  { canonico: 'Endereço', aliases: ['endereco', 'endereco de entrega', 'endereco entrega', 'local de entrega', 'entrega em', 'entregar em', 'logradouro', 'rua', 'avenida', 'av', 'travessa', 'tv', 'alameda', 'rodovia', 'estrada', 'praca', 'endereco residencial', 'endereco do cliente', 'localizacao de entrega'] },
  { canonico: 'Número', aliases: ['numero', 'numero da casa', 'numero do imovel', 'numero endereco', 'n casa', 'nº', 'num', 'porta'] },
  { canonico: 'Bairro', aliases: ['bairro', 'bairro de entrega', 'regiao', 'loteamento', 'conjunto habitacional', 'residencial'] },
  { canonico: 'Apartamento', aliases: ['apartamento', 'apto', 'apt', 'apart', 'unidade', 'numero do apartamento', 'n apartamento', 'bloco e apartamento', 'bloco/apartamento'] },
  { canonico: 'Complemento', aliases: ['complemento', 'complemento endereco', 'complemento do endereco', 'bloco', 'casa dos fundos', 'informacoes adicionais', 'dados adicionais'] },
  { canonico: 'Referência', aliases: ['referencia', 'ponto de referencia', 'referencia de entrega', 'referencia endereco', 'proximo a', 'em frente a', 'ao lado de', 'perto de', 'observacao para entrega', 'observacoes de entrega'] },
  { canonico: 'Quadra', aliases: ['quadra', 'qd', 'qd.', 'q.'] },
  { canonico: 'Lote', aliases: ['lote', 'lt', 'lt.'] },
  { canonico: 'CEP', aliases: ['cep', 'codigo postal'] }
]
function aplicarDicionarioRotulosComanda(texto) {
  const porAlias = new Map()
  for (const item of DICIONARIO_ROTULOS_COMANDA) {
    for (const alias of item.aliases) porAlias.set(normalizarChaveAprendizado(alias), item.canonico)
  }
  // Variações cadastradas pelos ADMs são salvas no arquivo local de aprendizado.
  for (const [canonico, lista] of Object.entries(aliasesDicionarioComanda || {})) {
    if (!DICIONARIO_ROTULOS_COMANDA.some(item => item.canonico === canonico) || !Array.isArray(lista)) continue
    for (const alias of lista) {
      const chaveAlias = normalizarChaveAprendizado(alias)
      if (chaveAlias) porAlias.set(chaveAlias, canonico)
    }
  }
  return String(texto || '').split(/\r?\n/).map(linha => {
    const original = String(linha || '').trim()
    if (!original) return ''
    // Só interpreta um rótulo no começo da linha seguido de separador ou sozinho;
    // assim, uma rua chamada "Rua das Flores" não é confundida com um campo.
    const m = original.match(/^\s*([^:：]{1,48}?)\s*(?:[:：]|\s+-\s+|\s*#\s*)(.*)$/)
    const rotulo = m ? m[1] : original
    const valor = m ? String(m[2] || '').trim() : ''
    const chave = normalizarChaveAprendizado(rotulo)
    let canonico = porAlias.get(chave)
    if (!canonico) {
      // Corrige variações frequentes do OCR, mas só quando a semelhança é inequívoca.
      const compacto = chave.replace(/\s+/g, '')
      const candidatos = [...porAlias.entries()].filter(([a]) => {
        const ac = a.replace(/\s+/g, '')
        const prefixoIgual = compacto.slice(0, Math.min(5, compacto.length)) === ac.slice(0, Math.min(5, ac.length))
        return compacto.length >= 5 && (compacto === ac.replace(/0/g, 'o') || (Math.abs(compacto.length - ac.length) <= 1 && prefixoIgual))
      })
      const unicos = [...new Set(candidatos.map(([, c]) => c))]
      if (unicos.length === 1) canonico = unicos[0]
    }
    if (!canonico) return original
    if (canonico === 'CEP') return '' // CEP é explicitamente descartado neste fluxo.
    return valor ? `${canonico}: ${valor}` : `${canonico}:`
  }).filter(Boolean).join('\n')
}
function aplicarAliasesModeloComanda(texto, modelo) {
  let saida = String(texto || '')
  const aliases = modelo && modelo.aliases && typeof modelo.aliases === 'object' ? modelo.aliases : {}
  const rotulos = { nome: 'Cliente', telefone: 'Telefone', endereco: 'Endereço', bairro: 'Bairro', apartamento: 'Apartamento', complemento: 'Complemento', referencia: 'Referência', localizadorIfood: 'Localizador iFood' }
  for (const [campo, lista] of Object.entries(aliases)) {
    const canonico = rotulos[campo]
    if (!canonico || !Array.isArray(lista)) continue
    for (const alias of lista.slice(0, 20)) {
      const a = String(alias || '').trim().replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
      if (a.length >= 2) saida = saida.replace(new RegExp(`(^|\\n)\\s*${a}\\s*[:：-]`, 'ig'), `$1${canonico}:`)
    }
  }
  return saida
}
async function processarNomeEstabelecimentoPendente(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  const pendente = estabelecimentoPendentePorUsuario.get(usuario) || estabelecimentoPendentePorUsuario.get(jid)
  if (!pendente) return false
  const nome = String(obterTexto(msg) || '').trim()
  if (!nome || nome.length > 100 || /^(?:cancelar|cancela)$/i.test(nome)) {
    estabelecimentoPendentePorUsuario.delete(usuario); estabelecimentoPendentePorUsuario.delete(jid)
    await sock.sendMessage(jid, { text: 'Cadastro do modelo cancelado. Você pode enviar a foto novamente quando quiser.' })
    return true
  }
  const chave = pendente.assinatura
  const anterior = modelosLayoutComandas[chave] || { aliases: {} }
  modelosLayoutComandas[chave] = { nomeEstabelecimento: nome, assinatura: chave, aliases: anterior.aliases || {}, criadoEm: anterior.criadoEm || new Date().toISOString(), atualizadoEm: new Date().toISOString(), exemplosCorrigidos: Number(anterior.exemplosCorrigidos || 0) }
  const salvou = salvarAprendizadoComandas()
  estabelecimentoPendentePorUsuario.delete(usuario); estabelecimentoPendentePorUsuario.delete(jid)
  await sock.sendMessage(jid, { text: `✅ Modelo de comanda cadastrado para *${nome}*.\n\nVou manter esse modelo separado dos demais e aprender os rótulos quando você corrigir os campos. ${salvou ? 'O cadastro foi salvo no armazenamento disponível do servidor.' : '⚠️ O servidor não permitiu gravar em disco; o aprendizado será perdido se o bot reiniciar.'}\n\nEnvie a próxima comanda desse estabelecimento normalmente.` })
  return true
}
carregarAprendizadoComandas()

// Link direto do WhatsApp: não consulta encurtadores externos e não atrasa
// o processamento da comanda. O próprio Android/WhatsApp abre a conversa.
function gerarLinkWhatsAppLocalizacao(telefone) {
  let digitos = String(telefone || '').replace(/\D/g, '')
  if (digitos.length === 10 || digitos.length === 11) digitos = `55${digitos}`
  if (!/^55\d{10,11}$/.test(digitos)) return ''
  // Abre a conversa sem texto pré-preenchido: somente o número do cliente.
  return `https://wa.me/${digitos}`
}

async function formatarComandaCorrigida(c) {
  const saida = []
  if (c.nome) saida.push(`👤 *Cliente:* ${c.nome}`)
  if (c.telefone) {
    const digitos = String(c.telefone).replace(/\D/g, '')
    let wa = digitos
    if (wa.length === 11 || wa.length === 10) wa = `55${wa}`
    const linkWhatsApp = gerarLinkWhatsAppLocalizacao(c.telefone)
    saida.push(`📞 *Telefone${c.nome ? ` de ${c.nome}` : ' do cliente'}:* ${linkWhatsApp || c.telefone}`)
  }
  if (c.contatoIfood) saida.push(`☎️ *Contato/central iFood:* ${c.contatoIfood}`)
  if (c.localizadorIfood) saida.push(`🔎 *Código localizador iFood:* ${c.localizadorIfood}`)
  if (c.quantidadePedidos) saida.push(`📦 *Quantidade de pedidos:* ${c.quantidadePedidos}`)
  if (c.estabelecimentoComanda) saida.push(`🏪 *Estabelecimento:* ${c.estabelecimentoComanda}`)
  if (c.cepComanda) saida.push(`📮 *CEP:* ${c.cepComanda}`)
  if (c.endereco) {
    const consultaMaps = String(c.endereco).normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/[^a-zA-Z0-9 ,]/g, ' ').replace(/\s+/g, ' ').replace(/\s*,\s*/g, ', ').trim()
    const url = `https://maps.google.com/?q=${encodeURIComponent(consultaMaps).replace(/%20/g, '+')}`
    saida.push(`📍 *Endereço:* ${c.endereco}${c.apartamento ? `\n🏠 *Apartamento:* ${c.apartamento}` : ''}${c.bairro ? `\n🏘️ *Bairro:* ${c.bairro}` : ''}${c.cidadeEntrega ? `\n🏙️ *Cidade:* ${c.cidadeEntrega}` : ''}${c.quadra ? `\n🔢 *Quadra:* ${c.quadra}` : ''}${c.lote ? `\n🔢 *Lote:* ${c.lote}` : ''}${c.complemento ? `\n🏠 *Complemento:* ${c.complemento}` : ''}${c.referencia ? `\n📌 *Ponto de referência:* ${c.referencia}` : ''}\n🗺️ *Abrir no Google Maps:* ${url}`)
  }
  return saida.join('\n\n')
}
async function processarCorrecaoComandaAprendizado(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const original = String(obterTexto(msg) || '').trim()
  if (!/^corrigir\s+(?:comanda|bairro|apartamento|apto|refer[eê]ncia|ref|telefone(?:\s+do\s+cliente)?|rua|endere[cç]o|complemento|localizador(?:\s+ifood)?|cliente)\s*[:\n]/i.test(original)) return false
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  const atual = ultimasComandasOCRPorUsuario.get(usuario) || ultimasComandasOCRPorUsuario.get(jid)
  if (!atual) {
    await sock.sendMessage(jid, { text: 'Ainda não tenho uma comanda recente nesta conversa para corrigir. Envie primeiro a foto da comanda e depois mande, por exemplo, *Corrigir bairro: Jardim Guanabara*.' })
    return true
  }
  const campos = {
    cliente: 'nome', nome: 'nome', telefone: 'telefone', 'telefone do cliente': 'telefone', rua: 'endereco', endereco: 'endereco', 'endereco de entrega': 'endereco', bairro: 'bairro', apartamento: 'apartamento', apto: 'apartamento', referencia: 'referencia', ref: 'referencia', 'ponto de referencia': 'referencia', complemento: 'complemento', localizador: 'localizadorIfood', 'localizador ifood': 'localizadorIfood', 'codigo localizador ifood': 'localizadorIfood'
  }
  const linhas = original.split(/\r?\n/).map(x => x.trim()).filter(Boolean)
  let aplicadas = 0
  const camposCorrigidos = new Set()
  let bairroAnterior = String(atual.bairroLido || atual.bairro || '').trim()
  const valoresAntes = { nome: atual.nome, telefone: atual.telefone, endereco: atual.endereco, bairro: atual.bairro, apartamento: atual.apartamento, complemento: atual.complemento, referencia: atual.referencia, localizadorIfood: atual.localizadorIfood }
  for (const linha of linhas) {
    const m = linha.match(/^\s*(?:corrigir\s+)?([^:：]+)\s*[:：]\s*(.*?)\s*$/i)
    if (!m) continue
    const chave = normalizarChaveAprendizado(m[1]).replace(/^corrigir\s+/, '').trim()
    const campo = campos[chave]
    const valor = String(m[2] || '').trim()
    if (!campo || !valor || /^\[.*\]$/.test(valor)) continue
    atual[campo] = valor
    camposCorrigidos.add(campo)
    aplicadas++
  }
  if (!aplicadas) {
    await sock.sendMessage(jid, { text: 'Não identifiquei os campos da correção. Use uma linha por campo, por exemplo:\n*Corrigir bairro: Jardim Guanabara*\n*Corrigir apartamento: 202*\n*Corrigir referência: Edifício Ecoville*' })
    return true
  }
  // Aprende rótulos específicos do layout usando somente o prefixo da linha OCR;
  // os valores pessoais reconhecidos nunca entram no arquivo persistente.
  if (atual.assinaturaLayout && atual.textoOCRBruto) {
    const modelo = modelosLayoutComandas[atual.assinaturaLayout]
    if (modelo) {
      modelo.aliases = modelo.aliases || {}
      for (const [campo, antigo] of Object.entries(valoresAntes)) {
        if (!camposCorrigidos.has(campo)) continue
        if (!antigo || String(antigo).trim().length < 2) continue
        const valorNormalizado = normalizarChaveAprendizado(antigo)
        const linhaOCR = String(atual.textoOCRBruto).split(/\n+/).find(l => normalizarChaveAprendizado(l).includes(valorNormalizado))
        if (!linhaOCR) continue
        const prefixo = linhaOCR.match(/^\s*([^:：]{2,35})\s*[:：]/)
        if (!prefixo) continue
        const rotulo = prefixo[1].trim()
        const lista = modelo.aliases[campo] || (modelo.aliases[campo] = [])
        if (!lista.some(x => normalizarChaveAprendizado(x) === normalizarChaveAprendizado(rotulo)) && lista.length < 20) lista.push(rotulo)
      }
      modelo.exemplosCorrigidos = Number(modelo.exemplosCorrigidos || 0) + 1
      modelo.atualizadoEm = new Date().toISOString()
      salvarAprendizadoComandas()
    }
  }
  // Aprende apenas alias de bairro, um dado público e não identificável. Não grava
  // nomes, telefones, localizadores, ruas, apartamentos ou referências de clientes.
  if (atual.bairro && bairroAnterior && normalizarChaveAprendizado(bairroAnterior) !== normalizarChaveAprendizado(atual.bairro)) {
    const chaveAnterior = normalizarChaveAprendizado(bairroAnterior)
    if (chaveAnterior && chaveAnterior.length >= 3) {
      aliasesBairroAprendidos[chaveAnterior] = String(atual.bairro).trim()
      salvarAprendizadoComandas()
      atual.bairroLido = bairroAnterior
    }
  }
  if (atual.imagemHash) {
    const camposAprendidos = ['nome', 'telefone', 'localizadorIfood', 'endereco', 'apartamento', 'bairro', 'complemento', 'referencia', 'quadra', 'lote', 'numeroImovel']
    const correcoes = {}
    for (const campo of camposAprendidos) if (atual[campo]) correcoes[campo] = atual[campo]
    correcoesPorHashImagem.set(atual.imagemHash, correcoes)
    while (correcoesPorHashImagem.size > 100) correcoesPorHashImagem.delete(correcoesPorHashImagem.keys().next().value)
  }
  ultimasComandasOCRPorUsuario.set(usuario, atual)
  ultimasComandasOCRPorUsuario.set(jid, atual)
  const texto = await formatarComandaCorrigida(atual)
  await sock.sendMessage(jid, { text: `✅ *Comanda corrigida.*${texto ? `\n\n${texto}` : '\n\nOs campos foram atualizados, mas ainda não consegui montar um endereço completo.'}\n\n📚 A correção foi aplicada à comanda atual. O reconhecimento usa OCR tradicional e regras de dicionário local, sem IA. Valores pessoais de clientes não são gravados como exemplos permanentes.` })
  return true
}

async function responderImagemPrivadaComIA(sock, msg) {
  const jid = msg?.key?.remoteJid || ''
  if ((!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) || !ehImagemMensagem(msg)) return false
  if (!permitirUsoIAPrivada(jid)) {
    await sock.sendMessage(jid, { text: 'Você atingiu o limite de análises de imagem por enquanto. Tente novamente mais tarde.' })
    return true
  }
  let buffer
  try {
    buffer = await downloadMediaMessage(msg, 'buffer', {}, { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage })
  } catch (e) {
    console.log('⚠️ Não foi possível baixar a imagem enviada no privado:', e?.message || e)
    await sock.sendMessage(jid, { text: 'Não consegui abrir essa imagem agora. Tente enviá-la novamente, de preferência como foto (não como visualização única).' })
    return true
  }
  if (!Buffer.isBuffer(buffer) || !buffer.length) {
    await sock.sendMessage(jid, { text: 'A imagem chegou vazia ou não pôde ser lida. Tente enviá-la novamente.' })
    return true
  }
  const imagemHash = crypto.createHash('sha256').update(buffer).digest('hex')
  // Comandas são processadas sem IA generativa: OCR.space + regras locais.
  // Não há fallback Tesseract porque o RTCloud não garante o binário/dados de idioma.
  const chaveOCRConfigurada = !!obterChaveOCRSpace()
  if (!chaveOCRConfigurada) {
    await sock.sendMessage(jid, { text: '⚠️ O leitor de comandas ainda não está configurado. Envie *configurar ocr* em uma conversa privada com o bot e informe sua chave OCR.space. Depois confira com *status ocr*.' })
    return true
  }
  let textoOCR = ''
  try {
    textoOCR = await extrairTextoOCRSpace(buffer)
    if (textoOCR) console.log('Imagem lida pela API OCR.space.')
  } catch (e) {
    console.log('⚠️ OCR.space falhou:', e?.message || e)
    await sock.sendMessage(jid, { text: 'Erro na leitura\n\nTentei novamente ou mande outra comanda' })
    return true
  }
  if (!textoOCR) {
    await sock.sendMessage(jid, { text: 'Não consegui identificar texto legível nesta imagem. Tente enviar uma captura mais nítida ou digite o endereço na mensagem.' })
    return true
  }
  textoOCR = aplicarRemocoesComanda(textoOCR)
  textoOCR = aplicarDicionarioRotulosComanda(textoOCR)
  if (!textoOCR.trim()) {
    await sock.sendMessage(jid, { text: 'Depois de aplicar as regras de remoção, não sobrou texto legível na comanda. Revise os termos cadastrados com o comando *Remover*.' })
    return true
  }
  const assinaturaLayoutAtual = assinaturaLayoutComanda(textoOCR)
  const modeloLayoutAtual = modelosLayoutComandas[assinaturaLayoutAtual]
  if (modeloLayoutAtual) textoOCR = aplicarAliasesModeloComanda(textoOCR, modeloLayoutAtual)
  // Extrai nome, telefone e endereço do pedido. O OCR costuma colocar os valores
  // nas linhas seguintes aos rótulos (Cliente, telefone, Endereço).
  // CEP não deve ser usado como endereço nem como pista para montar o endereço.
  // Remove linhas que sejam apenas um CEP (com ou sem rótulo) e elimina CEPs
  // isolados de linhas mistas antes de executar os fallbacks do OCR.
  const removerCEP = valor => String(valor || '')
    // Só remove 8 dígitos sem hífen quando vierem identificados como CEP.
    // Um localizador do iFood também costuma ter 8 dígitos e precisa ser preservado.
    .replace(/\bCEP\s*[:：-]?\s*\d{5}[-\s]?\d{3}\b/gi, '')
    .replace(/\bCEP\s*[:：-]?\s*\d{8}\b/gi, '')
    .replace(/\b\d{5}-\d{3}\b/g, '')
    .trim()
  // Privacidade: nunca extrair nem devolver CPF de cliente em transcrições de comandas.
  // Remove rótulo e número mesmo quando aparecem no meio da mesma linha do telefone.
  const removerCPF = valor => String(valor || '')
    .replace(/\bCPF\s*[:：-]?\s*\d{3}\.?\d{3}\.?\d{3}[-.]?\d{2}\b/gi, '')
    .replace(/\bCPF\s*[:：-]?\s*[\d.\-/ ]{11,18}/gi, '')
    .replace(/\s{2,}/g, ' ')
    .trim()
  const linhasOCRBrutas = textoOCR.split(/\n+/).map(x => x.replace(/[\t ]+/g, ' ').trim()).filter(Boolean)
  const linhas = linhasOCRBrutas
    // Remove CEPs isolados, mas preserva um código numérico logo após Localizador/ID.
    .filter((x, i, arr) => {
      if (/^\s*(?:CEP\s*[:：-]?\s*)?\d{5}[-\s]?\d{3}\s*$/i.test(x)) return false
      if (/^\s*(?:CEP\s*[:：-]?\s*)?\d{8}\s*$/i.test(x)) {
        const anterior = arr[i - 1] || ''
        if (/(?:localizador|c[oó]digo\s+(?:do\s+pedido|localizador)|\bID\s*[:：#-]?\s*$)/i.test(anterior)) return true
        return false
      }
      return true
    })
    .map(x => removerCPF(removerCEP(x)).replace(/[ \t]{2,}/g, ' ').trim())
    .filter(Boolean)
  const limpar = valor => String(valor || '').replace(/^[\s:：\-•]+|[\s|•]+$/g, '').trim()
  const indiceRotulo = (regex, inicio = 0) => linhas.findIndex((l, i) => i >= inicio && regex.test(l))
  // Primeiro identifica o localizador: ele pode ter oito dígitos e não deve
  // ser confundido com telefone, CEP ou número do imóvel.
  let localizadorIfood = ''
  for (let i = 0; i < linhas.length; i++) {
    const l = linhas[i]
    let m = l.match(/(?:c[oó]digo\s+)?localizador(?:\s+do\s+pedido)?\s*[:：#-]?\s*(\d{6,10})/i)
    if (!m) m = l.match(/c[oó]digo\s+(?:do\s+pedido\s+)?localizador\s*[:：#-]?\s*(\d{6,10})/i)
    // Em comandas do iFood, às vezes aparece apenas "0800 ... ID: 12345678".
    if (!m && /\b0800\b|ifood/i.test(l)) m = l.match(/\bID\s*[:：#-]?\s*(\d{6,10})\b/i)
    if (m) { localizadorIfood = m[1]; break }
    if (/^(?:localizador|código\s+localizador|localizador\s+do\s+pedido)\s*[:：-]?$/i.test(l) && /^\d{6,10}$/.test(linhas[i + 1] || '')) {
      localizadorIfood = linhas[i + 1]
      break
    }
    if (/^ID\s*[:：#-]?\s*$/i.test(l) && /^\d{6,10}$/.test(linhas[i + 1] || '')) {
      const contexto = linhas.slice(Math.max(0, i - 2), i + 1).join(' ')
      if (/\b0800\b|ifood|localizador/i.test(contexto)) {
        localizadorIfood = linhas[i + 1]
        break
      }
    }
  }

  let nome = ''
  let quantidadePedidos = 0
  let quantidadePedidosEncontrada = false
  let previsaoEntrega = ''
  let estabelecimentoComanda = ''
  let cepComanda = (String(textoOCR || '').match(/\bCEP\s*[:：-]?\s*(\d{5}[-\s]?\d{3})/i) || [])[1] || ''
  let cidadeEntrega = ''
  for (const linha of linhas) {
    const qtd = linha.match(/^(?:quantidade\s+de\s+pedidos|total\s+de\s+pedidos)\s*[:：-]?\s*(\d+)/i)
    if (qtd) { quantidadePedidos = Math.max(0, Number(qtd[1]) || 0); quantidadePedidosEncontrada = true }
    const previsao = linha.match(/^previs[aã]o\s*[:：-]?\s*(.*)$/i)
    if (previsao) {
      previsaoEntrega = limpar(previsao[1])
      if ((!previsaoEntrega || /[-–—]$/.test(previsaoEntrega)) && /^\d{1,2}:\d{2}(?:\s*[-–—].*)?$/.test(limpar(linhas[linhas.indexOf(linha) + 1] || ''))) {
        previsaoEntrega = `${previsaoEntrega} ${limpar(linhas[linhas.indexOf(linha) + 1])}`.trim()
      }
    }
    // Nome do estabelecimento costuma aparecer sozinho, em caixa alta, antes
    // do rodapé de pagamento. Não confundir rótulos comuns com estabelecimento.
    if (/^USHI$/i.test(linha)) estabelecimentoComanda = linha.trim()
  }
  const rotuloNome = /^(?:cliente|nome(?:\s+do\s+cliente)?|destinatário|recebedor)\s*[:：-]?\s*(.*)$/i
  const iCliente = indiceRotulo(rotuloNome)
  if (iCliente >= 0) {
    nome = limpar(linhas[iCliente].replace(rotuloNome, '$1'))
    if (!nome) {
      const proxima = limpar(linhas[iCliente + 1] || '')
      if (proxima && !/^(?:pedido|chat|telefone|tel\.?|celular|whatsapp|contato|fone|endereço|entrega|bairro|complemento|referência|ref|pagamento|produtos|localizador|código)\b/i.test(proxima)) nome = proxima
    }
  }
  if (!nome) {
    const iNome = indiceRotulo(/^(?:nome(?:\s+do\s+cliente)?|destinatário)\s*[:：-]\s*(.+)$/i)
    if (iNome >= 0) nome = limpar(linhas[iNome].replace(/^(?:nome(?:\s+do\s+cliente)?|destinatário)\s*[:：-]?/i, ''))
  }

  let telefone = ''
  let contatoIfood = ''
  const rotuloTelefone = /^(?:telefone(?:\s+do\s+cliente)?|tel\.?|celular|whatsapp|contato|fone|número\s+de\s+contato)\s*[:：-]?\s*(.*)$/i
  const iTelefone = indiceRotulo(rotuloTelefone)
  if (iTelefone >= 0) {
    telefone = limpar(linhas[iTelefone].replace(rotuloTelefone, '$1'))
    if (!telefone && linhas[iTelefone + 1] && /[\d() +.-]{8,}/.test(linhas[iTelefone + 1])) telefone = limpar(linhas[iTelefone + 1])
    // Algumas impressoras quebram o telefone no hífen final: "(83) 99802-" + "5640".
    // Junta a linha seguinte antes de validar o número do WhatsApp.
    const digitosParciais = telefone.replace(/\D/g, '')
    if (telefone && (/[–—-]$/.test(telefone) || digitosParciais.length < 10) && /^\d{3,5}$/.test(limpar(linhas[iTelefone + 1] || ''))) {
      telefone = `${telefone.replace(/[–—-]\s*$/, '')}${limpar(linhas[iTelefone + 1])}`
    }
  }
  // Um 0800 impresso numa comanda do iFood é telefone de contato/central,
  // não necessariamente o telefone pessoal do cliente.
  if (/\b0800\b/.test(telefone)) {
    contatoIfood = telefone.replace(/\s+ID\s*[:：#-]?.*$/i, '').trim()
    telefone = ''
  }
  if (!telefone) {
    const possivel = linhas.find(l => {
      if (!/(?:\(?\d{2}\)?\s*)?9?\d{4}[\s.-]?\d{4}/.test(l)) return false
      if (/0800|localizador|código|\bID\s*[:：#-]?\s*\d|pedido|#\d|CPF|CEP/i.test(l)) return false
      return true
    })
    if (possivel) {
      const m = possivel.match(/(?:\+?55\s*)?(?:\(?\d{2}\)?\s*)?9?\d{4}[\s.-]?\d{4}/)
      if (m) telefone = limpar(m[0])
    }
  }
  if (!contatoIfood) {
    const linhaCentral = linhas.find(l => /\b0800\b/i.test(l) && /ifood|\bID\s*[:：#-]?|localizador/i.test(l))
    if (linhaCentral) contatoIfood = limpar((linhaCentral.match(/\b0800\s*[\d .()-]{7,}/i) || [''])[0]).replace(/\s+ID\b.*$/i, '').trim()
  }
  if (localizadorIfood && telefone.replace(/\D/g, '').includes(localizadorIfood)) telefone = ''
  const digitosTelefone = telefone.replace(/\D/g, '')
  let telefoneWa = digitosTelefone
  if (telefoneWa.length === 11 && telefoneWa.startsWith('0') === false) telefoneWa = `55${telefoneWa}`
  else if (telefoneWa.length === 10) telefoneWa = `55${telefoneWa}`
  const telefoneValido = telefoneWa.length >= 12 && telefoneWa.length <= 13
  let endereco = ''
  let numeroImovel = ''
  let complemento = ''
  let apartamento = ''
  // Apartamento pode estar em linha própria, em Complemento ou colado ao endereço.
  for (let i = 0; i < linhas.length && !apartamento; i++) {
    const inline = linhas[i].match(/\b(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s*[:：#-]?\s*([A-Z0-9]+(?:[-/]\w+)?)/i)
    if (inline && /\d/.test(inline[1])) apartamento = inline[1].trim()
    else if (/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s*[:：-]?$/i.test(linhas[i]) && /^\d+[A-Z]?(?:[-/]\w+)?$/i.test(linhas[i + 1] || '')) apartamento = linhas[i + 1].trim()
  }
  let bairro = ''
  let referencia = ''
  const iNumeroImovel = indiceRotulo(/^n[uú]mero\s*[:：-]?\s*(.*)$/i)
  if (iNumeroImovel >= 0) {
    numeroImovel = limpar(linhas[iNumeroImovel].replace(/^n[uú]mero\s*[:：-]?/i, ''))
    if (!numeroImovel && linhas[iNumeroImovel + 1] && /^\d+[A-Za-z]?(?:[-/]\w+)?$/.test(limpar(linhas[iNumeroImovel + 1]))) numeroImovel = limpar(linhas[iNumeroImovel + 1])
  }
  const iBairroRotulo = indiceRotulo(/^bairro\s*[:：-]?\s*(.*)$/i)
  if (iBairroRotulo >= 0) bairro = limpar(linhas[iBairroRotulo].replace(/^bairro\s*[:：-]?/i, ''))
  const iReferenciaRotulo = indiceRotulo(/^(?:ponto\s+de\s+refer[eê]ncia|refer[eê]ncia|ref)\s*[:：-]?\s*(.*)$/i)
  if (iReferenciaRotulo >= 0) {
    const partesReferenciaOCR = [limpar(linhas[iReferenciaRotulo].replace(/^(?:ponto\s+de\s+refer[eê]ncia|refer[eê]ncia|ref)\s*[:：-]?/i, ''))].filter(Boolean)
    for (let i = iReferenciaRotulo + 1; i < linhas.length; i++) {
      const proxima = limpar(linhas[i])
      if (/^(?:previs[aã]o|impresso\s+em|pagamento|total|subtotal|produtos|itens|cliente|nome|telefone|tel\.?|celular|whatsapp|contato|fone|entrega|endere[cç]o|bairro|cep|n[uú]mero|complemento|localizador|c[oó]digo)\b/i.test(proxima)) break
      if (/^[.·•_=-]{3,}$/.test(proxima)) break
      partesReferenciaOCR.push(proxima)
    }
    referencia = partesReferenciaOCR.join(' ').trim()
  }
  const iComplemento = indiceRotulo(/^(?:complemento|comp\.?)\s*[:：-]?\s*(.*)$/i)
  if (iComplemento >= 0) {
    let valorComplemento = limpar(linhas[iComplemento].replace(/^(?:complemento|comp\.?)\s*[:：-]?/i, ''))
    const proximaLinhaComplemento = limpar(linhas[iComplemento + 1] || '')
    // Em algumas comandas, o OCR separa "Apartamento" e o número da unidade em linhas distintas.
    if (/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)$/i.test(valorComplemento) && /^\d+[A-Za-z]?(?:[-/]\w+)?$/.test(proximaLinhaComplemento)) {
      apartamento = proximaLinhaComplemento
    } else if (/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s+(.+)$/i.test(valorComplemento) && /\d/.test(valorComplemento)) {
      apartamento = limpar(valorComplemento.replace(/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s+/i, ''))
    } else if (/^\d+[A-Za-z]?(?:[-/]\w+)?$/.test(valorComplemento) && /^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)$/i.test(linhas[iComplemento - 1] || '')) {
      apartamento = valorComplemento
    } else if (valorComplemento && !/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)$/i.test(valorComplemento)) {
      complemento = valorComplemento
    }
  }
  // Prioriza o campo explícito "Endereço:". A expressão antiga aceitava
  // qualquer linha iniciada por "Entrega", capturando "Entrega Própria" do
  // cabeçalho do iFood como se fosse o logradouro.
  const iEnderecoExplicito = indiceRotulo(/^(?:endere[cç]o(?: de entrega)?|logradouro)\s*[:：-]\s*(.*)$/i)
  const iEntregaExplicita = indiceRotulo(/^(?:local de entrega|entregar em|entrega)\s*[:：-]\s*(.*)$/i)
  let iEndereco = iEnderecoExplicito >= 0 ? iEnderecoExplicito : iEntregaExplicita
  // No layout Anota, a palavra "Entrega" também pode aparecer antes do bloco
  // do cliente (por exemplo, no resumo de valores). O endereço válido é o
  // rótulo Entrega que aparece depois de Cliente/Quantidade de pedidos.
  const ehLayoutAnotaDetectado = linhas.some(l => /^quantidade\s+de\s+pedidos\s*[:：-]?\s*\d+/i.test(l)) &&
    linhas.some(l => /^pagamento\b/i.test(l))
  if (ehLayoutAnotaDetectado && iCliente >= 0) {
    const iEntregaDepoisCliente = linhas.findIndex((l, i) => i > iCliente && /^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]/i.test(l))
    if (iEntregaDepoisCliente >= 0) iEndereco = iEntregaDepoisCliente
  }
  if (iEndereco >= 0) {
    const primeiraParte = limpar(linhas[iEndereco].replace(/^(?:endere[cç]o(?: de entrega)?|logradouro|local de entrega|entrega|entregar em)\s*[:：-]?/i, ''))
    const partes = primeiraParte ? [primeiraParte] : []
    for (let i = iEndereco + 1; i < linhas.length; i++) {
      if (/^(?:n[uú]mero|complemento|comp\.?|bairro|refer[eê]ncia|ref(?:er[eê]ncia)?|ponto\s+de\s+refer[eê]ncia|previs[aã]o|impresso\s+em|brendi|pagamento|produtos|reportar endere[cç]o inv[aá]lido|mapa|telefone|tel\.?|celular|whatsapp|contato|fone|nome|destinat[aá]rio|localizador|c[oó]digo localizador|id\s*[:：#-]?|cliente|pedido|chat|patos(?:\s*[-,/]?\s*pb)?|cep)\b/i.test(linhas[i])) break
      // Ignora elementos da interface e identificadores do pedido, mas preserva complemento/bairro/cidade.
      if (/^(?:•?\s*)?(?:reportar endere[cç]o inv[aá]lido|m\s*mapa|pagamento na entrega|dinheiro|n[aã]o precisa enviar troco|preparando)$/i.test(linhas[i])) continue
      if (/^#?[A-Z0-9-]{5,}$/.test(linhas[i]) || /^\d{1,2}:\d{2}/.test(linhas[i])) continue
      partes.push(limpar(linhas[i]))
    }
    endereco = partes.join(', ').replace(/\s*,\s*,+/g, ', ').trim()
  }
  // Em comandas impressas com campos próprios, o logradouro fica estritamente
  // entre o rótulo "Endereço" e o rótulo "Número". Não usar linhas da referência
  // como continuação da rua, mesmo quando o OCR mistura blocos ou quebra a rua.
  if (iEndereco >= 0 && iNumeroImovel > iEndereco) {
    const trechoLogradouro = linhas
      .slice(iEndereco, iNumeroImovel)
      .map((linha, indice) => indice === 0
        ? limpar(linha.replace(/^(?:endere[cç]o(?: de entrega)?|logradouro|local de entrega|entrega|entregar em)\s*[:：-]?/i, ''))
        : limpar(linha))
      .filter(Boolean)
      .filter(linha => !/^(?:cep|bairro|refer[eê]ncia|ref|ponto de refer[eê]ncia|previs[aã]o|pagamento|cliente|telefone)\b/i.test(linha));
    const ruaDelimitada = trechoLogradouro.join(' ').replace(/\s+/g, ' ').replace(/[;,|]+$/g, '').trim();
    if (/\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a)\b/i.test(ruaDelimitada)) {
      endereco = ruaDelimitada;
    }
  }
  // Formato de comanda textual/OCR usado pela USHI:
  // "Entrega: Bossuet Wanderley, № 743, Mont azul ap 101 - Bairro: Brasília, Patos | CEP..."
  // Neste layout, "Mont azul" é ruído do endereço e não deve virar rua,
  // complemento ou bairro. O número do imóvel e o apartamento são separados.
  if (iEndereco >= 0 && /^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]/i.test(linhas[iEndereco])) {
    const linhaEntrega = limpar(linhas[iEndereco].replace(/^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]?/i, ''))
    const partesEnderecoEspecial = linhaEntrega.match(/^(.+?)\s*,\s*(?:(?:n[º°o.]?|№)\s*)?(\d+[A-Za-z]?)\s*,?\s*(.*?)\b(?:ap(?:to)?\.?|apartamento)\s*[:：#-]?\s*([A-Z0-9]+(?:[-/]\w+)?)\s*(?:[-,|]\s*)?bairro\s*[:：-]\s*(.*)$/i)
    if (partesEnderecoEspecial) {
      const ruaEspecial = limpar(partesEnderecoEspecial[1])
      numeroImovel = limpar(partesEnderecoEspecial[2])
      apartamento = limpar(partesEnderecoEspecial[4])
      const bairroECidade = limpar(partesEnderecoEspecial[5])
      const cidadeMatch = bairroECidade.match(/[,|]\s*(Patos)(?:\s*[-/]\s*PB)?\s*$/i)
      if (cidadeMatch) cidadeEntrega = 'Patos'
      bairro = limpar(bairroECidade
        .replace(/\s*[|,]\s*CEP\s*[:：-]?.*$/i, '')
        .replace(/\s*[,|]\s*Patos(?:\s*[-/]\s*PB)?\s*$/i, '')
        .replace(/\s*[-/]\s*PB\s*$/i, ''))
      endereco = `${ruaEspecial}, ${numeroImovel}`
    }
  }
  if (!endereco) {
    // Fallback sem rótulo: só aceita uma linha que realmente identifique
    // um tipo de logradouro. Bairro/jardim/cabeçalho não bastam para criar rua.
    const candidatas = linhas.filter(l => /\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a)\b/i.test(l) && l.length >= 5 && l.length <= 180)
    if (candidatas.length) endereco = candidatas.slice(0, 2).join(', ')
  }
  // Não inferir endereço a partir da posição do bairro no texto: isso fazia
  // cabeçalhos, referências e linhas de itens virarem logradouro.
  // Separa logradouro, bairro e ponto de referência. O link do Maps não deve
  // incluir referência visual (ex.: nome de comércio/creche) nem complemento.
  let quadra = ''
  let lote = ''
  // Extrai Quadra e Lote também quando aparecem como campos próprios fora do endereço.
  // Exemplos: "Quadra: 4", "QD 4", "Q.: 4", "Lote: 12", "LT 12".
  const extrairRotuloQuadraLote = (rotulos) => {
    const encontrados = []
    const alternancia = rotulos.join('|')
    const reInline = new RegExp('^\\s*(?:' + alternancia + ')\\s*(?::|：|#|=|-|\\s)\\s*([A-Z0-9]+(?:[-/][A-Z0-9]+)?)\\s*$', 'i')
    const reSoRotulo = new RegExp('^\\s*(?:' + alternancia + ')\\s*[:：#=-]?\\s*$', 'i')
    for (let i = 0; i < linhas.length; i++) {
      const linha = limpar(linhas[i])
      const m = linha.match(reInline)
      if (m) { encontrados.push(m[1].trim()); continue }
      if (reSoRotulo.test(linha)) {
        const proxima = limpar(linhas[i + 1] || '')
        if (/^[A-Z0-9]+(?:[-/][A-Z0-9]+)?$/i.test(proxima)) encontrados.push(proxima)
      }
    }
    return [...new Set(encontrados)].join(', ')
  }
  quadra = extrairRotuloQuadraLote(['quadra', 'qd\\.?', 'q\\.'])
  lote = extrairRotuloQuadraLote(['lote', 'lt\\.?'])
  if (endereco) {
    endereco = endereco.replace(/^entrega\s*[:：-]\s*/i, '').trim()
    // Tira identificadores, CEP e apartamento quando o OCR os juntou à rua.
    // O CEP nunca é enviado como endereço nem entra no link do Google Maps.
    endereco = endereco
      .replace(/\b(?:código\s+)?localizador(?:\s+do\s+pedido)?\s*[:：#-]?\s*\d{6,10}\b/gi, ' ')
      .replace(/\bID\s*[:：#-]?\s*\d{6,10}\b/gi, ' ')
      .replace(/\b(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s*[:：#-]?\s*[A-Z0-9]+(?:[-/]\w+)?/gi, ' ')
      .replace(/\bCEP\s*[:：-]?\s*\d{5}[-\s]?\d{3}\b/gi, ' ')
      .replace(/\b\d{5}-\d{3}\b|\b\d{8}\b/g, ' ')
      .replace(/\s*[-,;]+\s*$/g, '').replace(/\s{2,}/g, ' ').trim()
    // OCR de comandas frequentemente usa pontos/bolinhas como separadores e
    // junta cidade, CEP, bairro e referência na mesma linha. Separe os campos
    // antes da extração para que não contaminem o logradouro nem a busca do Maps.
    endereco = endereco.replace(/[●•·▪]/g, ', ').replace(/\bPatos\s*[,/-]?\s*PB\b/ig, ', Patos, PB')
    endereco = endereco.replace(/\bPatos\s*[,/-]?\s*PB\b/ig, ', ')
    endereco = endereco.replace(/\bPatos\b/ig, ', ')
    endereco = endereco.replace(/\b\d{5}[-\s]?\d{3}\b|\b\d{8}\b/g, ' ')
    endereco = endereco.replace(/\s*[-–—]\s*/g, ', ').replace(/\s*,\s*,+/g, ', ').replace(/^\s*,|,\s*$/g, '').trim()
    // Quadra e lote são campos próprios: extraí-los antes de separar logradouro,
    // bairro e referência, inclusive quando aparecem sem rótulo de campo.
    const extrairCampoNumerado = (rotulo) => {
      const re = new RegExp('\\b' + rotulo + '\\s*[:：#-]?\\s*([A-Z0-9]+(?:[-/][A-Z0-9]+)?)', 'ig')
      const valores = []
      endereco = endereco.replace(re, (_m, valor) => { valores.push(String(valor).trim()); return ' ' })
      return [...new Set(valores)].join(', ')
    }
    // Variação comum em comandas: "N°q 1" / "Nº Q 1" significa Quadra 1.
    // Extrai o valor antes de montar o link para que o marcador não contamine o endereço.
    const extrairQuadraMarcadaPorNQ = () => {
      const valores = []
      const re = /\bN\s*[º°o.]?\s*Q\.?\s*[:：#=-]?\s*([A-Z0-9]+(?:[-/][A-Z0-9]+)?)/ig
      endereco = endereco.replace(re, (_m, valor) => { valores.push(String(valor).trim()); return ' ' })
      return [...new Set(valores)].join(', ')
    }
    quadra = [...new Set([quadra, extrairQuadraMarcadaPorNQ(), extrairCampoNumerado('quadra')].filter(Boolean).flatMap(x => x.split(',').map(v => v.trim())))].join(', ')
    lote = [...new Set([lote, extrairCampoNumerado('lote')].filter(Boolean).flatMap(x => x.split(',').map(v => v.trim())))].join(', ')
    endereco = endereco.replace(/\s*[,;]+\s*/g, ', ').replace(/\s*,\s*,+/g, ', ').replace(/^\s*,|,\s*$/g, '').trim()
    // OCR pode juntar vários campos na mesma linha: "Rua, Comp: Casa, Bairro: ...,
    // Ref: ..., Cidade: ..., CP:, ITENS DO PEDIDO...". Extrai os campos pelo rótulo
    // antes de separar o logradouro, para não contaminar endereço/referência com itens.
    const marcadoresCampo = /(?:^|[,;]\s*)(bairro|comp(?:lemento)?|refer[eê]ncia|ref|ponto\s+de\s+refer[eê]ncia|cidade|cp|cep|itens(?:\s+do\s+pedido)?)\s*[:：-]\s*/ig
    const camposDetectados = []
    let campoMatch
    while ((campoMatch = marcadoresCampo.exec(endereco)) !== null) {
      camposDetectados.push({ inicio: campoMatch.index, valorInicio: marcadoresCampo.lastIndex, tipo: normalizarTexto(campoMatch[1]).replace(/\s+/g, '') })
    }
    if (camposDetectados.length) {
      const primeiroCampo = camposDetectados[0]
      const logradouroLimpo = endereco.slice(0, primeiroCampo.inicio).replace(/[\s,;:–—-]+$/g, '').trim()
      for (let i = 0; i < camposDetectados.length; i++) {
        const campo = camposDetectados[i]
        const fim = i + 1 < camposDetectados.length ? camposDetectados[i + 1].inicio : endereco.length
        let valor = endereco.slice(campo.valorInicio, fim).replace(/^[\s,;:–—-]+|[\s,;:–—-]+$/g, '').trim()
        // Cidade/CEP/itens nunca entram no endereço nem na referência.
        if (['cidade', 'cp', 'cep', 'itensdopedido', 'itens'].includes(campo.tipo)) continue
        valor = valor.replace(/\s*(?:ITENS\s+DO\s+PEDIDO|CIDADE|CP|CEP)\b.*$/i, '').trim()
        if (!valor) continue
        if (campo.tipo === 'bairro' && !bairro) bairro = valor
        else if ((campo.tipo === 'comp' || campo.tipo === 'complemento') && !complemento) complemento = valor
        else if (['ref', 'referencia', 'pontodereferencia'].includes(campo.tipo) && !referencia) referencia = valor
      }
      if (logradouroLimpo) endereco = logradouroLimpo
    }
    const marcadorReferencia = /\s*(?:[-,;]\s*)?(?:pr[oó]ximo\s+a|refer[eê]ncia|ponto\s+de\s+refer[eê]ncia|perto\s+de)\s*[:：-]?\s*/i
    const partesReferencia = endereco.split(marcadorReferencia)
    if (partesReferencia.length > 1) {
      endereco = partesReferencia.shift().replace(/[\s,;–—-]+$/g, '').trim()
      referencia = partesReferencia.join(' ').replace(/^[\s,;:–—-]+|[\s,;]+$/g, '').trim()
    }
    const normalizarParte = valor => String(valor || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/[^a-z0-9 ]/g, ' ').replace(/\s+/g, ' ').trim()
    const bairros = [...new Set([...(typeof listarBairrosPatos === 'function' ? listarBairrosPatos() : (Array.isArray(BAIRROS_PATOS) ? BAIRROS_PATOS : [])), 'Belo Horizonte / Jardim Queiroz'])]
    const partes = endereco.split(/\s*,\s*/).map(limpar).filter(Boolean)
    const logradouroIdx = partes.findIndex(p => /\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|pra[cç]a)\b/i.test(p))
    if (logradouroIdx >= 0 && partes.length > logradouroIdx + 1) {
      const ruaPartes = partes.slice(0, logradouroIdx + 2)
      const demais = partes.slice(logradouroIdx + 2)
      const bairrosEncontrados = []
      const referenciasRestantes = []
      for (let indiceParte = 0; indiceParte < demais.length; indiceParte++) {
        const parte = demais[indiceParte]
        const norm = normalizarParte(parte)
        // Reconhece apartamento mesmo quando aparece no meio da linha de entrega
        // ou quando o OCR separa o rótulo e o número por hífens/linhas.
        const apartamentoCompleto = /^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)\s*[:：#-]?\s*([A-Z0-9]+(?:[-/]\w+)?)$/i.exec(parte)
        if (apartamentoCompleto && /\d/.test(apartamentoCompleto[1])) {
          apartamento = apartamentoCompleto[1].trim()
          continue
        }
        if (/^(?:apartamento|apto|apt|apart|unidade)(?:\.|\b)$/i.test(parte)) {
          const proximaParte = demais[indiceParte + 1] || ''
          if (/^[A-Z0-9]+(?:[-/]\w+)?$/i.test(proximaParte)) {
            apartamento = proximaParte.trim()
            indiceParte++
          } else {
            /* rótulo sem número não é complemento útil */
          }
          continue
        }
        const bairroMatch = bairros.find(b => {
          const nb = normalizarParte(b)
          return nb && (norm === nb || norm.startsWith(nb + ' ') || norm.endsWith(' ' + nb) || norm.includes(' ' + nb + ' '))
        })
        if (bairroMatch) {
          bairrosEncontrados.push(bairroMatch)
          const sobra = parte.replace(new RegExp(bairroMatch.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'i'), '').replace(/^\s*[-,;]+\s*|\s*[-,;]+\s*$/g, '').trim()
          if (sobra && !/^patos(?:\s*[-,/]?\s*pb)?$/i.test(sobra.replace(/^[\s,;–—-]+|[\s,;–—-]+$/g, ''))) referenciasRestantes.push(sobra)
        } else if (/^patos(?:\s*[-,/]?\s*pb)?$/i.test(parte)) {
          // Cidade usada na pesquisa do Maps, não é bairro nem referência.
        } else if (/^(?:casa|apto|apartamento|bloco|fundos|1[ºo] andar)\b/i.test(parte)) {
          complemento = parte
        } else {
          referenciasRestantes.push(parte)
        }
      }
      if (bairrosEncontrados.length) bairro = [...new Set(bairrosEncontrados)].join(', ')
      if (referenciasRestantes.length) referencia = [...new Set([referencia, ...referenciasRestantes].filter(Boolean))].join(', ')
      endereco = ruaPartes.join(', ').replace(/\s*[-,;]\s*Casa\s*$/i, '').trim()
    } else {
      // “Casa” é complemento do imóvel, não parte do logradouro.
      endereco = endereco.replace(/\s*[-,;]\s*Casa\s*$/i, '').trim()
    }
    // Padroniza logradouro + número como "Rua - 285" no texto enviado ao usuário.
    // O link do Maps é normalizado separadamente e recebe apenas esse endereço.
    endereco = endereco.replace(/^(.*?\b(?:rua|r\.?|avenida|av\.?|travessa|tv\.?|alameda|rodovia|estrada|praça)\b[^,]*),\s*(\d+[A-Za-z]?(?:[-/]\w+)?)$/i, '$1 - $2').trim()
  }
  // Padroniza abreviações comuns de logradouro lidas pelo OCR, inclusive comandas
  // sem rótulos. A indicação de ausência de número fica visível, mas fora do link do Maps.
  if (endereco) {
    endereco = endereco
      .replace(/^\s*r\.?(?=\s|$)/i, 'Rua')
      .replace(/^\s*av\.?(?=\s|$)/i, 'Avenida')
      .replace(/^\s*tv\.?(?=\s|$)/i, 'Travessa')
      .replace(/^\s*tr\.?(?=\s|$)/i, 'Travessa')
      .replace(/^\s*al\.?(?=\s|$)/i, 'Alameda')
      .replace(/^\s*rod\.?(?=\s|$)/i, 'Rodovia')
      .replace(/^(Rua|Avenida|Travessa|Alameda|Rodovia)\s+(Do|Da|De|Dos|Das)\b/i, (_m, tipo, particula) => `${tipo} ${particula.toLowerCase()}`)
      .replace(/\s*,\s*(?:sem\s+n[uú]mero|s\s*\/?\s*n\.?|n[uú]mero\s+(?:n[aã]o\s+informado|inexistente)|n[aã]o\s+possui\s+n[uú]mero)\s*$/i, ', Sem número')
      .replace(/\s+/g, ' ').trim()
  }
  // Número do imóvel faz parte do endereço; complemento/apartamento permanece em campo separado.
  if (endereco && numeroImovel && !new RegExp('(?:^|\\D)' + numeroImovel.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '(?:$|\\D)').test(endereco)) {
    endereco = `${endereco.replace(/[\s,;]+$/g, '')} ${numeroImovel}`.trim()
  }
  // Retira sobras comuns do rodapé da comanda, que não são parte do logradouro.
  endereco = endereco.replace(/\s*(?:previs[aã]o|impresso\s+em|brendi)\b.*$/i, '').trim()
  // Consulta a lista de bairros cadastrados antes de preencher o campo Bairro.
  // Primeiro normaliza o valor rotulado; se não houver rótulo útil, procura um nome
  // completo de bairro nas linhas/endereço da própria comanda.
  const bairroBrutoAntesDaLista = String(bairro || '').trim()
  const bairroDaLista = identificarBairroComanda(bairroBrutoAntesDaLista)
  if (bairroDaLista) bairro = bairroDaLista
  else if (!bairroBrutoAntesDaLista) {
    const fontesBairro = [endereco, ...linhas].filter(Boolean)
    for (const fonte of fontesBairro) {
      const encontrado = identificarBairroComanda(fonte)
      if (encontrado) { bairro = encontrado; break }
    }
  }
  // Correção final de segurança: o bairro pode ser reconhecido somente depois
  // da separação inicial dos campos. Remova-o novamente do logradouro antes de
  // montar a mensagem e o link do Maps, inclusive se OCR o misturou na mesma linha.
  const bairrosFinaisParaLimpar = [...new Set([
    ...(typeof listarBairrosPatos === 'function' ? listarBairrosPatos() : (typeof BAIRROS_PATOS !== 'undefined' ? BAIRROS_PATOS : [])),
    ...Object.keys(typeof ALIASES_BAIRROS_PATOS !== 'undefined' ? ALIASES_BAIRROS_PATOS : {}),
    ...Object.values(typeof ALIASES_BAIRROS_PATOS !== 'undefined' ? ALIASES_BAIRROS_PATOS : {}).flatMap(v => Array.isArray(v) ? v : []),
    ...Object.keys(EMPRESA_CONFIG || {}).flatMap(k => Object.keys(empresas[k]?.estado?.mapeamentosBairrosAntigos || {})),
    ...(bairro ? [bairro] : [])
  ].map(v => String(v || '').trim()).filter(v => v.length >= 3))].sort((a, b) => b.length - a.length)
  const regexFlexivelNome = valor => normalizarTexto(valor).split(/\s+/).filter(Boolean).map(p => p.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('\\s+')
  for (const nomeBairro of bairrosFinaisParaLimpar) {
    const padraoBairro = regexFlexivelNome(nomeBairro)
    if (!padraoBairro) continue
    const reBairroFinal = new RegExp('(?<![\\p{L}\\p{N}])' + padraoBairro + '(?![\\p{L}\\p{N}])', 'giu')
    endereco = String(endereco || '').replace(reBairroFinal, ' ')
  }
  endereco = String(endereco || '')
    .replace(/\s*[-,;–—]+\s*(?:Patos(?:\s*[-/]\s*PB)?|PB)\s*$/ig, ' ')
    .replace(/\s{2,}/g, ' ').replace(/\s*[,;]+\s*[,;]+\s*/g, ', ')
    .replace(/^\s*[,;:–—-]+|[,;:–—-]+\s*$/g, '').trim()
  // O OCR da captura pode ler o botão roxo "mapa" como "N mapa" e anexá-lo
  // ao ponto de referência. Esses textos são controles da tela, não referências.
  referencia = String(referencia || '')
    .replace(/\b(?:n\s*)?mapa\b/ig, ' ')
    .replace(/\breportar\s+endere[cç]o\s+inv[aá]lido\b/ig, ' ')
    .replace(/\b(?:pagamento|produtos|preparando|chat|telefone)\b/ig, ' ')
    .replace(/\s{2,}/g, ' ').replace(/^\s*[,;:–—-]+|[,;:–—-]+\s*$/g, '')
    .replace(/\s*[,;]+\s*[,;]+\s*/g, ', ').trim()
  const bairroLidoPeloOCR = String(bairro || '').trim()
  const chaveBairroLido = normalizarChaveAprendizado(bairroLidoPeloOCR)
  if (chaveBairroLido && aliasesBairroAprendidos[chaveBairroLido]) bairro = String(aliasesBairroAprendidos[chaveBairroLido])
  // Reaplica as correções feitas pelo ADM quando a mesma imagem for enviada de novo.
  // Esse mapa é temporário e limitado; não grava nomes, telefones ou endereços em disco.
  const correcoesDaImagem = correcoesPorHashImagem.get(imagemHash)
  if (correcoesDaImagem) {
    if (correcoesDaImagem.nome) nome = correcoesDaImagem.nome
    if (correcoesDaImagem.telefone) telefone = correcoesDaImagem.telefone
    if (correcoesDaImagem.localizadorIfood) localizadorIfood = correcoesDaImagem.localizadorIfood
    if (correcoesDaImagem.endereco) endereco = correcoesDaImagem.endereco
    if (correcoesDaImagem.apartamento) apartamento = correcoesDaImagem.apartamento
    if (correcoesDaImagem.bairro) bairro = correcoesDaImagem.bairro
    if (correcoesDaImagem.complemento) complemento = correcoesDaImagem.complemento
    if (correcoesDaImagem.referencia) referencia = correcoesDaImagem.referencia
    if (correcoesDaImagem.quadra) quadra = correcoesDaImagem.quadra
    if (correcoesDaImagem.lote) lote = correcoesDaImagem.lote
    if (correcoesDaImagem.numeroImovel) numeroImovel = correcoesDaImagem.numeroImovel
  }
  // Validação final do logradouro: rótulos impressos nunca podem virar
  // parte do nome da rua, mesmo quando o OCR cola campos ou perde quebras.
  // Reaplicada depois das correções por imagem para proteger também esse caminho.
  const limparRotulosDoEndereco = valor => String(valor || '')
    .replace(/^\s*(?:(?:endere[cç]o(?:\s+de\s+entrega)?|logradouro|local\s+de\s+entrega)\s*[:：-]\s*)+/i, '')
    .replace(/(^|[,;]\s*)(?:endere[cç]o(?:\s+de\s+entrega)?|logradouro|local\s+de\s+entrega)\s*[:：-]\s*/ig, '$1')
    .replace(/\s{2,}/g, ' ')
    .replace(/^\s*[,;:–—-]+|[,;:–—-]+\s*$/g, '')
    .trim()
  endereco = limparRotulosDoEndereco(endereco)
  referencia = String(referencia || '')
    // Um telefone pode aparecer erroneamente depois de "Ref:"; ele já é
    // tratado separadamente como telefone do cliente e nunca como referência.
    .replace(/(?:\+?55\s*)?(?:\(?\d{2}\)?\s*)?9?\d{4}[\s.-]?\d{4}/g, ' ')
    .replace(/\b(?:cidade|cep)\s*[:：-]?.*$/i, ' ')
    .replace(/\s{2,}/g, ' ').replace(/^\s*[,;:–—-]+|[,;:–—-]+\s*$/g, '').trim()
  // Layout de comanda em que o OCR entrega o endereço em linhas separadas:
  // "Entrega:" / "R. Walter Carvalho - Sem Número" /
  // "Morada Do Sol - QUADRA 24, LOTE 18" / "Primeira Rua...".
  // Neste padrão, a primeira linha é o logradouro, a segunda contém bairro
  // e quadra/lote, e a terceira é referência. Não juntar referência à rua.
  if (iEndereco >= 0 && /^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]?$/i.test(linhas[iEndereco])) {
    const bloco = []
    for (let i = iEndereco + 1; i < linhas.length; i++) {
      const linha = limpar(linhas[i])
      if (!linha) continue
      if (/^(?:patos(?:\s*[-,/]?\s*pb)?|pb)(?:\s*cep\b|\s*\d{5}-?\d{3})?$/i.test(linha) || /\bCEP\s*[:：-]?\s*\d{5}[-\s]?\d{3}/i.test(linha)) break
      if (/^(?:valor|total|subtotal|pagamento|produtos|itens|cliente|telefone|celular|previs[aã]o|pedido)\b/i.test(linha)) break
      if (/\bPatos\s*[-,/]?\s*PB\b/i.test(linha)) break
      bloco.push(linha)
      if (bloco.length >= 4) break
    }
    const idxRua = bloco.findIndex(l => /^(?:r\.?|rua|av\.?|avenida|tv\.?|travessa|alameda|rodovia|estrada|pra[cç]a)\s+/i.test(l))
    if (idxRua >= 0) {
      let rua = bloco[idxRua]
        .replace(/^r\.?\s+/i, 'Rua ')
        .replace(/^av\.?\s+/i, 'Avenida ')
        .replace(/^tv\.?\s+/i, 'Travessa ')
        .replace(/\s+/g, ' ').trim()
      // Mantém "Sem Número" visível na comanda, mas o link do Maps já o exclui.
      rua = rua.replace(/\s*[-–—,]\s*(sem\s+n[uú]mero|s\s*\/?\s*n\.?)\s*$/i, ' - Sem Número')
      let linhaBairro = bloco[idxRua + 1] || ''
      const q = linhaBairro.match(/\b(?:quadra|qd\.?|q\.)\s*[:#-]?\s*(\d+[A-Za-z]?)\b/i)
      const l = linhaBairro.match(/\b(?:lote|lt\.?)\s*[:#-]?\s*(\d+[A-Za-z]?)\b/i)
      if (q) quadra = q[1]
      if (l) lote = l[1]
      linhaBairro = linhaBairro
        .replace(/\b(?:quadra|qd\.?|q\.)\s*[:#-]?\s*\d+[A-Za-z]?\b/ig, ' ')
        .replace(/\b(?:lote|lt\.?)\s*[:#-]?\s*\d+[A-Za-z]?\b/ig, ' ')
        .replace(/[,-]+\s*$/g, '').replace(/\s+/g, ' ').trim()
      const bairroDetectado = identificarBairroComanda(linhaBairro)
      if (bairroDetectado) bairro = bairroDetectado
      const sobrasBairro = bairroDetectado
        ? linhaBairro.replace(new RegExp(bairroDetectado.replace(/[.*+?^${}()|[\\]\\]/g, '\\$&'), 'i'), '').replace(/^[\s,;-]+|[\s,;-]+$/g, '').trim()
        : ''
      const referenciaNova = [sobrasBairro, ...bloco.slice(idxRua + 2)].filter(Boolean).join(' ').replace(/[.\s]+$/g, '').trim()
      if (referenciaNova) referencia = referenciaNova
      endereco = rua
    }
  }


  // Layout Anota: os campos de entrega podem ser quebrados em várias linhas,
  // enquanto produtos e preços aparecem antes do bloco Cliente/Entrega.
  // Neste formato, somente o texto imediatamente após "Entrega:" é endereço;
  // referência e bairro são extraídos dos seus próprios rótulos.
  if (iEndereco >= 0 && /^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]/i.test(linhas[iEndereco]) &&
      linhas.some(l => /quantidade\s+de\s+pedidos/i.test(l)) && linhas.some(l => /^pagamento\b/i.test(l))) {
    const linhaInicialEntrega = limpar(linhas[iEndereco].replace(/^(?:entrega|endere[cç]o(?: de entrega)?)\s*[:：-]?/i, ''));
    const blocoEntrega = [linhaInicialEntrega];
    for (let i = iEndereco + 1; i < linhas.length; i++) {
      const l = limpar(linhas[i]);
      if (/^(?:pagamento|subtotal|total|taxa\s+de|quantidade\s+de\s+pedidos|produtos|itens)\b/i.test(l)) break;
      if (/^(?:cliente|nome|telefone|celular)\s*[:：-]/i.test(l)) break;
      if (/^\d{5}-?\d{3}$/.test(l)) continue;
      blocoEntrega.push(l);
      if (blocoEntrega.length >= 5) break;
    }
    const textoBlocoEntrega = blocoEntrega.join(' ').replace(/\s+/g, ' ').trim();
    const refMatch = textoBlocoEntrega.match(/(?:[-–—]\s*)?refer[eê]ncia\s*[:：-]\s*(.*?)(?=\s+bairro\s*[:：-]|\s+cep\b|$)/i);
    if (refMatch) referencia = limpar(refMatch[1]);
    const bairroMatch = textoBlocoEntrega.match(/\bbairro\s*[:：-]\s*(.*?)(?=\s*,?\s*Patos\b|\s+cep\b|$)/i);
    if (bairroMatch) {
      const bairroTexto = limpar(bairroMatch[1]).replace(/[|,]+$/g, '').trim();
      bairro = identificarBairroComanda(bairroTexto) || bairroTexto;
    }
    let enderecoAnota = linhaInicialEntrega
      .replace(/\s*[-–—]\s*refer[eê]ncia\s*[:：-].*$/i, '')
      .replace(/\s+refer[eê]ncia\s*[:：-].*$/i, '')
      .replace(/\s+bairro\s*[:：-].*$/i, '')
      .replace(/\s*,?\s*Patos(?:\s*[-/]\s*PB)?\s*$/i, '')
      .replace(/\s*\|?\s*CEP\s*[:：-]?.*$/i, '')
      .trim();
    const mEnderecoAnota = enderecoAnota.match(/^(.+?)\s*,\s*(?:(?:n[º°o.]?|№)\s*)?(\d+[A-Za-z]?)\s*(?:,\s*(.*))?$/i);
    if (mEnderecoAnota) {
      endereco = `${limpar(mEnderecoAnota[1])}, ${limpar(mEnderecoAnota[2])}`;
      const compAnota = limpar(mEnderecoAnota[3] || '');
      if (compAnota) complemento = compAnota;
    } else if (enderecoAnota) {
      endereco = enderecoAnota.replace(/\s*,\s*/g, ', ');
    }
  }
  // Releitura determinística dos layouts Continental Patos/iFood.
  // Alguns OCRs entregam o rótulo "Endereço" sem dois-pontos e quebram
  // Quadra/Lote/Referência em linhas distintas. Reprocessa somente o bloco
  // de entrega, sem usar linhas de produtos, valores ou controles da tela.
  {
    const idxRotuloEntregaEstrito = linhas.findIndex((linha, idx) =>
      idx > (iCliente >= 0 ? iCliente : -1) &&
      /^(?:entrega|endere[cç]o(?:\s+de\s+entrega)?)\s*[:：-]?\s*$/i.test(linha)
    );
    if (idxRotuloEntregaEstrito >= 0) {
      const blocoEnderecoEstrito = [];
      for (let i = idxRotuloEntregaEstrito + 1; i < linhas.length; i++) {
        const linha = limpar(linhas[i]);
        if (!linha) continue;
        if (/^(?:patos\s*[-,/]\s*pb|pb)(?:\s*[-,/]?\s*cep\b.*)?$/i.test(linha)) break;
        if (/\bCEP\s*[:：-]?\s*\d{5}[-\s]?\d{3}/i.test(linha)) break;
        if (/^(?:valor|total|subtotal|pagamento|produtos|itens|taxa\s+de|previs[aã]o|pedido|reportar\s+endere[cç]o\s+inv[aá]lido)\b/i.test(linha)) break;
        if (/^(?:mapa|n\s*mapa|chat|preparando|reportar\s+endere[cç]o\s+inv[aá]lido)$/i.test(linha)) continue;
        if (/^\d{5}-?\d{3}$/.test(linha)) break;
        blocoEnderecoEstrito.push(linha);
        if (blocoEnderecoEstrito.length >= 5) break;
      }

      const idxRuaEstrita = blocoEnderecoEstrito.findIndex(linha =>
        /^(?:r\.?|rua|av\.?|avenida|tv\.?|travessa|alameda|rodovia|estrada|pra[cç]a)\s+/i.test(linha)
      );
      if (idxRuaEstrita >= 0) {
        const regexQuadraEstrita = /(?:\bN\s*[º°o.]?\s*Q(?:UADRA)?\.?|\bQUADRA\b|\bQD\.?)\s*[:：#=-]?\s*(\d+[A-Za-z]?)/ig;
        const regexLoteEstrito = /\b(?:LOTE|LT\.?)\s*[:：#=-]?\s*(\d+[A-Za-z]?)/ig;
        const valoresQuadraEstrita = [];
        const valoresLoteEstrito = [];
        const limparMarcadoresEstritos = valor => String(valor || '')
          .replace(regexQuadraEstrita, (_m, n) => { valoresQuadraEstrita.push(n); return ' '; })
          .replace(regexLoteEstrito, (_m, n) => { valoresLoteEstrito.push(n); return ' '; })
          .replace(/\s*[-,;]+\s*[-,;]+\s*/g, ' ')
          .replace(/\s{2,}/g, ' ').trim();

        let ruaEstrita = limparMarcadoresEstritos(blocoEnderecoEstrito[idxRuaEstrita])
          .replace(/[\s,;:]+$/g, '')
          .replace(/^r\.?\s+/i, 'Rua ')
          .replace(/^av\.?\s+/i, 'Avenida ')
          .replace(/^tv\.?\s+/i, 'Travessa ')
          .replace(/\s*[-–—,]\s*(?:sem\s+n[uú]mero|s\s*\/?\s*n\.?)\s*$/i, ' - Sem Número')
          .replace(/\s+/g, ' ').trim();

        const linhasMetaEstritas = blocoEnderecoEstrito.slice(idxRuaEstrita + 1);
        let bairroEstrito = '';
        for (const linhaMeta of linhasMetaEstritas) {
          const encontrado = identificarBairroComanda(linhaMeta);
          if (encontrado) { bairroEstrito = encontrado; break; }
        }
        const referenciaEstrita = [];
        for (const linhaMeta of linhasMetaEstritas) {
          let sobra = limparMarcadoresEstritos(linhaMeta)
            .replace(/\bPatos\s*[-,/]?\s*PB\b/ig, ' ')
            .replace(/\bPatos\b/ig, ' ')
            .replace(/\bPB\b/ig, ' ');
          if (bairroEstrito) {
            const partesBairro = bairroEstrito.split(/\s+/).map(parte => parte.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
            const reBairroEstrito = new RegExp('(?<![\\p{L}\\p{N}])' + partesBairro.join('\\s+') + '(?![\\p{L}\\p{N}])', 'giu');
            sobra = sobra.replace(reBairroEstrito, ' ');
          }
          sobra = sobra
            .replace(/\b(?:n\s*)?mapa\b/ig, ' ')
            .replace(/\breportar\s+endere[cç]o\s+inv[aá]lido\b/ig, ' ')
            .replace(/\s{2,}/g, ' ')
            .replace(/^\s*[,;:–—-]+|[,;:–—-]+\s*$/g, '')
            .trim();
          if (sobra && !/^patos(?:\s*[-,/]?\s*pb)?$/i.test(sobra)) referenciaEstrita.push(sobra);
        }

        endereco = ruaEstrita;
        if (bairroEstrito) bairro = bairroEstrito;
        if (valoresQuadraEstrita.length) quadra = [...new Set(valoresQuadraEstrita)].join(', ');
        if (valoresLoteEstrito.length) lote = [...new Set(valoresLoteEstrito)].join(', ');
        if (referenciaEstrita.length) referencia = [...new Set(referenciaEstrita)].join(' ');
      }
    }

    // Se o OCR quebrou o último sobrenome para uma linha separada, incorpora
    // essa continuação ao nome até encontrar telefone, pedido ou outro campo.
    if (iCliente >= 0) {
      const valorNaLinhaCliente = limpar(linhas[iCliente].replace(rotuloNome, '$1'));
      const partesNomeEstritas = [];
      if (valorNaLinhaCliente) partesNomeEstritas.push(valorNaLinhaCliente);
      let inicioNomeEstrito = iCliente + 1;
      if (!valorNaLinhaCliente) inicioNomeEstrito = iCliente + 1;
      for (let i = inicioNomeEstrito; i < linhas.length; i++) {
        const linha = limpar(linhas[i]);
        if (!linha) continue;
        if (/^(?:telefone|tel\.?|celular|whatsapp|contato|fone|quantidade\s+de\s+pedidos|pedido\s+realizado|entrega|endere[cç]o|bairro|pagamento|produtos|itens|chat)\b/i.test(linha)) break;
        if (/\d/.test(linha) || !/^[\p{L}][\p{L}'’.-]*(?:\s+[\p{L}][\p{L}'’.-]*)*$/u.test(linha)) break;
        if (partesNomeEstritas.length >= 1) partesNomeEstritas.push(linha);
        else partesNomeEstritas.push(linha);
        if (partesNomeEstritas.join(' ').split(/\s+/).length >= 8) break;
      }
      if (partesNomeEstritas.length) nome = partesNomeEstritas.join(' ').replace(/\s+/g, ' ').trim();
    }
  }

  // Evita que o próprio rótulo "Cliente:" seja repetido no nome quando o OCR
  // o inclui no valor capturado.
  nome = String(nome || '').replace(/^\s*(?:cliente|nome(?:\s+do\s+cliente)?)\s*[:：-]\s*/i, '').trim();

  const resumoOCR = linhas.join('\n').slice(0, 2200)
  const saida = []
  if (nome) saida.push(`👤 *Cliente:* ${nome}`)
  if (telefone) {
    const linkWhatsApp = gerarLinkWhatsAppLocalizacao(telefone)
    saida.push(`📞 *Telefone${nome ? ` de ${nome}` : ' do cliente'}:* ${linkWhatsApp || telefone}`)
  }
  if (contatoIfood) saida.push(`☎️ *Contato/central iFood:* ${contatoIfood}`)
  if (localizadorIfood) {
    const codigoIfood = String(localizadorIfood).replace(/\D/g, '')
    const codigoFormatado = codigoIfood.length === 8 ? `${codigoIfood.slice(0, 4)}-${codigoIfood.slice(4)}` : localizadorIfood
    saida.push(`🔎 *Código localizador iFood:* ${codigoFormatado}`)
  }
  if (quantidadePedidosEncontrada) saida.push(`📦 *Quantidade de pedidos:* ${quantidadePedidos}`)
  if (estabelecimentoComanda) saida.push(`🏪 *Estabelecimento:* ${estabelecimentoComanda}`)
  if (cepComanda) saida.push(`📮 *CEP:* ${cepComanda}`)
  if (previsaoEntrega) saida.push(`🕒 *Previsão de entrega:* ${previsaoEntrega}`)
  if (endereco) {
    if (bairro) {
      const normalizarLocal = valor => String(valor || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim()
      const bairroNorm = normalizarLocal(bairro)
      const enderecoNorm = normalizarLocal(endereco)
      if (bairroNorm && enderecoNorm.endsWith(bairroNorm)) {
        const reBairroFinal = new RegExp(`(?:\\s*[,;–—-]\\s*)?${bairro.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*$`, 'i')
        endereco = endereco.replace(reBairroFinal, '').replace(/[\s,;–—-]+$/g, '').trim()
      }
    }
    const consultaMaps = endereco
      // Marcadores de ausência de número são informativos para o entregador,
      // mas não são parte do endereço pesquisável no Google Maps.
      .replace(/(?:\s*[,;–—-]\s*)?(?:sem\s+n[uú]mero|s\s*\/?\s*n\.?|n[uú]mero\s+(?:n[aã]o\s+informado|inexistente)|n[aã]o\s+possui\s+n[uú]mero)(?:\s*\([^)]*\))?/ig, ' ')
      .normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/[^a-zA-Z0-9 ,]/g, ' ').replace(/\s+/g, ' ').replace(/\s*,\s*/g, ', ').replace(/^\s*,|,\s*$/g, '').trim()
    // O Google Maps recebe somente o logradouro e um número real, se houver.
    const url = `https://maps.google.com/?q=${encodeURIComponent(consultaMaps).replace(/%20/g, '+')}`
    saida.push(`📍 *Endereço:* ${endereco}${apartamento ? `\n🏠 *Apartamento:* ${apartamento}` : ''}${bairro ? `\n🏘️ *Bairro:* ${bairro}` : ''}${cidadeEntrega ? `\n🏙️ *Cidade:* ${cidadeEntrega}` : ''}${quadra ? `\n🔢 *Quadra:* ${quadra}` : ''}${lote ? `\n🔢 *Lote:* ${lote}` : ''}${complemento ? `\n🏠 *Complemento:* ${complemento}` : ''}${referencia ? `\n📌 *Ponto de referência:* ${referencia}` : ''}\n🗺️ *Abrir no Google Maps:* ${url}`)
  }
  if (saida.length) {
    const avisoEndereco = !endereco
      ? `\n\nNão consegui identificar o endereço com segurança nesta imagem.`
      : ''
    const idUsuarioOCR = jidNormalizedUser(obterId(msg) || jid)
    const ultimaComanda = { nome, telefone, contatoIfood, localizadorIfood, quantidadePedidos, estabelecimentoComanda, cepComanda, cidadeEntrega, endereco, numeroImovel, complemento, apartamento, bairro, bairroLido: bairroLidoPeloOCR, quadra, lote, referencia, imagemHash, assinaturaLayout: assinaturaLayoutAtual, textoOCRBruto: textoOCR, nomeEstabelecimento: modeloLayoutAtual?.nomeEstabelecimento || estabelecimentoComanda || '' }
    ultimasComandasOCRPorUsuario.set(idUsuarioOCR, ultimaComanda)
    ultimasComandasOCRPorUsuario.set(jid, ultimaComanda)
    // Saída final limpa: não expõe notas técnicas nem instruções internas do OCR.
    await sock.sendMessage(jid, { text: `${saida.join('\n\n')}${avisoEndereco}` })
    return true
  }
  await sock.sendMessage(jid, { text: `🔎 *Texto que consegui ler na imagem:*\n${resumoOCR}\n\nNão consegui identificar com segurança o nome, telefone e endereço. Tente enviar uma imagem mais nítida.` })
  return true
}

async function responderComGeminiNoPrivado(sock, msg) {
  const jid = msg?.key?.remoteJid || ''
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const texto = String(obterTexto(msg) || '').trim()
  if (!texto || texto.length > 1500) return false

  // Respostas locais simples não dependem da API nem de pesquisa externa.
  const normalizado = normalizarTexto(texto)
  const agora = new Date()
  if (/^(que dia e hoje|qual e a data de hoje|data de hoje|que data e hoje)\??$/.test(normalizado)) {
    await sock.sendMessage(jid, { text: `Hoje é ${new Intl.DateTimeFormat('pt-BR', { timeZone: 'America/Fortaleza', weekday: 'long', day: '2-digit', month: 'long', year: 'numeric' }).format(agora)}.` })
    return true
  }
  if (/^(que horas sao|qual e a hora|que horas sao agora|hora atual)\??$/.test(normalizado)) {
    await sock.sendMessage(jid, { text: `Agora são ${new Intl.DateTimeFormat('pt-BR', { timeZone: 'America/Fortaleza', hour: '2-digit', minute: '2-digit' }).format(agora)} (horário de Patos-PB).` })
    return true
  }

  // Endereços recebem um link direto do Maps; não afirmamos que o endereço foi validado.
  if (pareceEnderecoParaMapa(texto)) {
    const endereco = extrairEnderecoParaMapa(texto)
    const url = `https://maps.google.com/?q=${encodeURIComponent(endereco)}`
    await sock.sendMessage(jid, { text: `📍 *Endereço:* ${endereco}\n\n🗺️ *Google Maps:* ${url}` })
    return true
  }

  if (!permitirUsoIAPrivada(jid)) {
    await sock.sendMessage(jid, { text: 'Você atingiu o limite de perguntas à IA por enquanto. Tente novamente mais tarde ou fale com a administração.' })
    return true
  }
  const apiKey = obterChaveIA('gemini')
  if (Date.now() < geminiPrivadaSemCotaAte) {
    console.log('ℹ️ Gemini IA privada temporariamente suspenso após erro de cota; tentando a alternativa sem repetir chamadas.')
    const contextoSemGemini = criarContextoDadosEntregador(jid)
    const promptSemGemini = `Você é um assistente de IA integrado ao Bot Chegô Delivery, em Patos-PB. Responda em português brasileiro natural. Use somente dados reais do contexto e não invente estatísticas. Para fatos atuais, use pesquisa na web se disponível. Não revele dados de outros entregadores nem segredos.\n\nCONTEXTO REAL: ${JSON.stringify(contextoSemGemini)}\n\nMensagem: ${texto}`
    if (await responderComOpenAIReserva(sock, jid, promptSemGemini)) return true
    await sock.sendMessage(jid, { text: 'A IA está temporariamente indisponível por limite de uso ou falta de créditos. Os comandos locais do Bot continuam funcionando; o administrador deve conferir as cotas e o faturamento dos provedores.' })
    return true
  }
  if (!apiKey) {
    console.log('ℹ️ Gemini sem chave configurada; tentando OpenAI como provedor principal disponível.')
    const contextoSemGemini = criarContextoDadosEntregador(jid)
    const promptSemGemini = `Você é um assistente de IA integrado ao Bot Chegô Delivery, em Patos-PB. Responda em português brasileiro natural. Use somente os dados reais do contexto quando a pergunta for sobre entregas e não invente estatísticas. Para fatos atuais, use pesquisa na web se disponível. Não revele dados de outros entregadores nem segredos.\n\nCONTEXTO REAL: ${JSON.stringify(contextoSemGemini)}\n\nMensagem: ${texto}`
    if (await responderComOpenAIReserva(sock, jid, promptSemGemini)) return true
    await sock.sendMessage(jid, { text: 'Ainda não consegui acessar nenhuma IA. O administrador deve configurar uma chave Gemini ou OpenAI válida e conferir os créditos do provedor.' })
    return true
  }

  const contexto = criarContextoDadosEntregador(jid)
  const prompt = `Você é o Gemini integrado ao Bot Chegô Delivery, em Patos-PB. Responda como um assistente de IA conversacional: entenda a intenção mesmo quando a pergunta for informal, responda diretamente e pesquise na internet quando a pergunta depender de informação atual ou desconhecida. Use português brasileiro natural, sem exigir comandos específicos.\n\nREGRAS IMPORTANTES:\n- Se a pergunta for sobre dados pessoais de entregas, use somente o CONTEXTO REAL abaixo; não invente estatísticas, nomes, entregas ou tempos. Se não houver dados suficientes, explique isso claramente.\n- Não revele dados de outros entregadores, ranking de empresas, configurações internas, chaves, segredos ou dados administrativos.\n- Para perguntas gerais, use a Pesquisa Google quando disponível, sintetize os resultados e inclua links úteis quando houver. Se não conseguir pesquisar, responda com o conhecimento disponível e deixe claro quando algo precisar de confirmação.\n- Não diga que fez uma ação externa se apenas forneceu orientação.\n- Mensagens de endereço serão tratadas pelo Bot antes deste pedido.\n- Não responda com mensagem genérica de falha só porque a pergunta não é um comando conhecido.\n\nCONTEXTO REAL DO ENTREGADOR QUE ESTÁ CONVERSANDO (últimos 28 dias):\n${JSON.stringify(contexto)}\n\nMensagem do entregador: ${texto}`

  // O Gemini 2.5 Flash foi descontinuado para novas chaves. Use apenas o modelo atual.
  // Primeiro tenta sem ferramenta de pesquisa para garantir uma resposta básica; depois
  // tenta a Pesquisa Google, necessária para eleições, notícias e outros fatos atuais.
  const modelos = [
    { nome: MODELO_GEMINI, pesquisa: false },
    { nome: MODELO_GEMINI, pesquisa: true }
  ]
  let ultimoErro = ''
  for (const modelo of modelos) {
    try {
      const payload = {
        contents: [{ role: 'user', parts: [{ text: prompt }] }],
        generationConfig: { temperature: 0.4, maxOutputTokens: 900 }
      }
      if (modelo.pesquisa) payload.tools = [{ google_search: {} }]
      const response = await fetch(`https://generativelanguage.googleapis.com/v1beta/models/${modelo.nome}:generateContent`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'x-goog-api-key': apiKey },
        body: JSON.stringify(payload),
        signal: AbortSignal.timeout(25000)
      })
      if (!response.ok) {
        const detalhe = await response.text().catch(() => '')
        ultimoErro = `${response.status}: ${detalhe.slice(0, 500)}`
        console.log(`⚠️ Gemini IA privada (${modelo.nome}, pesquisa=${modelo.pesquisa}) indisponível: ${ultimoErro}`)
        // Se a cota foi esgotada, a versão com pesquisa também falhará: segue direto para o fallback.
        if (response.status === 429 || /RESOURCE_EXHAUSTED|quota exceeded|limit:\s*\d+/i.test(detalhe)) {
          geminiPrivadaSemCotaAte = Date.now() + 6 * 60 * 60 * 1000
          break
        }
        continue
      }
      const data = await response.json()
      const resposta = data?.candidates?.[0]?.content?.parts?.map(p => p.text || '').join('').trim()
      if (!resposta) {
        ultimoErro = 'A API respondeu sem texto.'
        continue
      }
      await enviarTextoCompleto(sock, jid, resposta.slice(0, 5000))
      return true
    } catch (e) {
      ultimoErro = e?.message || String(e)
      console.log(`⚠️ Erro Gemini IA privada (${modelo.nome}, pesquisa=${modelo.pesquisa}): ${ultimoErro}`)
    }
  }
  console.log(`⚠️ Gemini esgotou as tentativas. Último erro: ${ultimoErro}. Acionando OpenAI como reserva.`)
  if (await responderComOpenAIReserva(sock, jid, prompt)) return true
  await sock.sendMessage(jid, { text: 'Não consegui acessar as IAs neste momento. Os comandos do Bot continuam funcionando. O administrador deve conferir as chaves, os limites e o faturamento dos provedores.' })
  return true
}

async function analisarSolicitacaoComGemini(texto) {
  const apiKey = obterChaveIA('gemini')
  if (!String(texto || '').trim()) return null
  if (Date.now() < geminiClassificacaoSemCotaAte) return null
  if (!apiKey) {
    if (!avisoChaveGeminiAusenteExibido) {
      console.log('⚠️ Gemini não acionado: variável GEMINI_API_KEY não está configurada.')
      avisoChaveGeminiAusenteExibido = true
    }
    return null
  }

  console.log('🧠 Gemini acionado para classificar uma mensagem que as regras locais não reconheceram.')

  const listaBairros = listarBairrosPatos().join(', ')
  const prompt = `Você classifica mensagens de grupos de WhatsApp de empresas de delivery em Patos-PB.
Decida se a mensagem é uma solicitação real para chamar/solicitar um entregador ou se é conversa comum.
Regras:
- Considere pedidos escritos informalmente, abreviados ou com erros de digitação.
- Saudações como bom dia/boa noite junto de um pedido não tornam a mensagem social.
- Ignore conversa comum, agradecimentos, boas-vindas, pedidos para chamar alguém no privado e frases como "Bardopeixe, chama ai" quando não indicarem uma entrega.
- A palavra "entrega" ou "entregas" indica solicitação mesmo sem bairro.
- Retorne somente bairros presentes nesta lista; não invente bairros nem nomes de lojas como bairros: ${listaBairros}.
- Se não der para saber, prefira is_delivery=false.
Responda somente JSON válido neste formato: {"is_delivery":true|false,"neighborhoods":["nome exato da lista"],"reason":"curto"}.
Mensagem: ${String(texto).slice(0, 1200)}`

  try {
    const response = await fetch(`https://generativelanguage.googleapis.com/v1beta/models/${MODELO_GEMINI}:generateContent`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'x-goog-api-key': apiKey
      },
      body: JSON.stringify({
        contents: [{ parts: [{ text: prompt }] }],
        generationConfig: { responseMimeType: 'application/json', temperature: 0 }
      }),
      signal: AbortSignal.timeout(10000)
    })
    if (!response.ok) {
      const detalhe = await response.text().catch(() => '')
      console.log(`⚠️ Gemini indisponível (${response.status}): ${detalhe.slice(0, 180)}`)
      if (response.status === 429 || /RESOURCE_EXHAUSTED|quota exceeded|limit:\s*\d+/i.test(detalhe)) {
        // Suspende chamadas de classificação por 6 horas; as regras locais continuam funcionando.
        geminiClassificacaoSemCotaAte = Date.now() + 6 * 60 * 60 * 1000
      }
      return null
    }
    const data = await response.json()
    const resposta = data?.candidates?.[0]?.content?.parts?.map(p => p.text || '').join('').trim()
    if (!resposta) {
      console.log('⚠️ Gemini respondeu sem conteúdo classificável.')
      return null
    }
    const resultado = JSON.parse(resposta.replace(/^```json\s*/i, '').replace(/```\s*$/i, '').trim())
    if (typeof resultado.is_delivery !== 'boolean') {
      console.log('⚠️ Gemini respondeu, mas o formato da classificação foi inválido.')
      return null
    }
    const permitidos = new Set(listarBairrosPatos())
    const neighborhoods = Array.isArray(resultado.neighborhoods)
      ? resultado.neighborhoods.filter(x => permitidos.has(x))
      : []
    const classificacao = resultado.is_delivery ? 'ENTREGA' : 'CONVERSA / NÃO É ENTREGA'
    console.log(`✅ Gemini respondeu. 📦 Resultado: ${classificacao}. Bairros: ${neighborhoods.length ? neighborhoods.join(', ') : 'nenhum identificado'}. Motivo: ${String(resultado.reason || 'não informado').slice(0, 120)}`)
    return { is_delivery: resultado.is_delivery, neighborhoods: [...new Set(neighborhoods)], reason: String(resultado.reason || '').slice(0, 120) }
  } catch (e) {
    console.log('⚠️ Falha ao consultar/processar resposta do Gemini; mantendo regras locais:', e?.message || e)
    return null
  }
}

function obterTextoCitado(msg) {
  const contexto =
    msg?.message?.extendedTextMessage?.contextInfo ||
    msg?.message?.imageMessage?.contextInfo ||
    msg?.message?.videoMessage?.contextInfo ||
    {}

  const citado = contexto.quotedMessage || {}

  return (
    citado.conversation ||
    citado.extendedTextMessage?.text ||
    citado.imageMessage?.caption ||
    citado.videoMessage?.caption ||
    ''
  ).trim()
}

function ehMensagemSocialOuAdministrativa(msg, texto) {
  const atual = normalizarTexto(texto)
  const citado = normalizarTexto(obterTextoCitado(msg))

  if (!atual && !citado) return false

  // Saudações curtas e mensagens compostas apenas por pontuação não são entregas.
  const semPontuacao = atual.replace(/[\s.,!?¡¿;:…。،؟]+/g, '').trim()
  const ehSoPontuacao = !semPontuacao
  const textoSaudacao = atual.replace(/[.!?¡¿,;:…]+$/g, '').trim()
  const ehSaudacaoCurta = /^(oi+|ola+|opa+|eai+|iae+|bom dia|boa tarde|boa noite|bom dia pessoal|boa tarde pessoal|boa noite pessoal|tudo bem|fala|salve|hey|hello|hi|bomdia|boatarde|boanoite)$/.test(textoSaudacao)

  // Boas-vindas/apresentações não são pedidos de entrega.
  const ehBoasVindas = /\b(bem vind[oa]s?|seja[m]? bem vind[oa]s?|seja[m]? bem vindo[s]?)\b/.test(atual)

  // Agradecimentos/conversas sociais isoladas não são pedidos de entrega.
  const ehAgradecimento = /^(obrigad[oa]s?|obg|vlw|valeu|agradeco|agradecida|gratidao)(?:\s+[🙏❤️💜🫶😊🙂😁🥰😍👍👏🎉✨]+)?$/.test(atual)

  // Conversas sobre valores/contato no privado não são pedidos de entrega.
  const ehAdministrativo =
    /\b(passe|passa|mand[ae]|envi[ae]|me passe|me manda|me envie)\b.*\b(valores?|precos?|precos? das entregas?)\b/.test(atual) ||
    /\b(valores?|precos?)\b.*\b(entregas?)\b.*\b(pv|privad[oa]|particular)\b/.test(atual) ||
    /\b(meu|no|para o|pro)\s+pv\b/.test(atual) ||
    /\b(me chama|me mande|me manda|fala comigo|chama no)\b.*\b(pv|privad[oa])\b/.test(atual)

  // Resposta social a uma mensagem de boas-vindas também deve ser ignorada.
  const respondeuBoasVindas = citado && /\b(bem vind[oa]s?|seja[m]? bem vind[oa]s?)\b/.test(citado) &&
    (/^(obrigad[oa]s?|obg|vlw|valeu|agradeco|agradecida|gratidao)\b/.test(atual) || atual.length < 40)

  return ehSoPontuacao || ehSaudacaoCurta || ehBoasVindas || ehAgradecimento || ehAdministrativo || respondeuBoasVindas
}

function extrairFracao(texto) {
  // A marca ✅ só é aceita como variação quando um ADM a habilitou no privado.
  const variacoes = estado?.variacoesEntrega || {}
  let textoFracao = String(texto || '')
  if (variacoes.fracionado || variacoes.entrega) textoFracao = textoFracao.replace(/[\s]*(?:✅|☑️|✔️)+[\s]*$/u, '')
  // Aceita formas comuns de escrever uma entrega fracionada:
  // 1/2, 1 / 2, 1-2, 1)2, 1 de 2, 1 por 2, 1 de um total de 2,
  // "parte 1/2", "fracionado 1 de 2", "1/2 entrega", "1ª de 2".
  let normalizado = normalizarTexto(textoFracao)
    .replace(/[.!?,;:]+$/g, '')
    .trim()

  normalizado = normalizado
    .replace(/^(?:(?:parte|fracionado|fracionada|fracionamento|entrega fracionada)\s*)+/i, '')
    .replace(/\s*(?:(?:parte|fracionado|fracionada|fracionamento|entrega|entregas)\s*)+$/i, '')
    .replace(/^(?:a|n[ºo°.]?\s*)/i, '')
    .trim()

  const padrao = /^(\d+)\s*(?:ª|a|º|o)?\s*(?:\/|\\|\-|\)|\bde\b|\bpor\b|\bde\s+um\s+total\s+de\b)\s*(?:n[ºo°.]?\s*)?(\d+)\s*(?:ª|a|º|o)?$/i
  const m = normalizado.match(padrao)
  if (!m) return null

  const atual = Number(m[1])
  const total = Number(m[2])
  if (!Number.isSafeInteger(atual) || !Number.isSafeInteger(total) || !total || atual < 1 || atual > total) return null
  return { atual, total }
}
function registrarEventoHistoricoEntrega(entrega, quantidade, msg, fracao = null) {
  const agora = Date.now()
  const data = new Date(agora)
  const eventoMensagemId = msg?.key?.id || null
  if (!Array.isArray(estado.historicoEntregas)) estado.historicoEntregas = []

  // Evita contabilizar duas vezes a mesma mensagem, inclusive se ela for
  // reapresentada pelo WhatsApp depois de uma reconexão do Bot.
  if (eventoMensagemId && estado.historicoEntregas.some(item =>
    String(item?.eventoMensagemId || '') === String(eventoMensagemId) &&
    jidNormalizedUser(item?.entregadorId || '') === jidNormalizedUser(entrega?.entregadorId || '') &&
    String(item?.empresaId || '') === String(entrega?.empresaId || '')
  )) {
    return false
  }

  estado.historicoEntregas.push({
    mensagemId: entrega.mensagemId || null,
    eventoMensagemId,
    mensagemIndoRef: entrega.mensagemIndoRef || null,
    mensagensFracionadasRefs: Array.isArray(entrega.fracionado?.mensagensRefs) ? [...entrega.fracionado.mensagensRefs] : [],
    mensagemFinalizacaoRef: entrega.mensagemFinalizacaoRef || null,
    fracaoAtual: fracao?.atual ?? null,
    fracaoTotal: fracao?.total ?? null,
    empresaId: entrega.empresaId || null,
    empresaNome: entrega.empresaNome || 'Empresa',
    entregadorId: entrega.entregadorId,
    entregadorNome: entrega.entregadorNome || 'Entregador',
    quantidade: Math.max(1, Number(quantidade) || 1),
    finalizadasQuantidade: 0,
    // Mantém o horário de contagem existente para não alterar os relatórios atuais.
    concluidaEm: agora,
    iniciadaEm: Number(entrega.aceitoEm || entrega.inicioEntregaEm || agora),
    finalizadaEm: null,
    tempoMinutos: null,
    data: data.toISOString().slice(0, 10),
    hora: data.getHours()
  })
  // Garante que o evento de aceite não se perca se o processo reiniciar antes da conclusão.
  salvar()
  return true
}

function finalizarEntregaAceita(entrega, msg) {
  // Idempotência: o mesmo registro pode chegar aqui por dois caminhos
  // (mensagem final e atualização de fração) durante uma reconexão ou corrida
  // assíncrona. Não repetir status, timestamps nem gravações de conclusão.
  if (!entrega || entrega.concluida === true) return false

  const agora = Date.now()
  entrega.concluida = true
  entrega.concluidaEm = agora
  entrega.conclusaoMensagemId = msg?.key?.id || null
  entrega.mensagemFinalizacaoRef = capturarReferenciaMensagem(msg)

  // Registra o tempo real entre o aceite/INDO e a conclusão, sem mudar
  // o campo concluidaEm usado pelos relatórios de contagem existentes.
  const inicio = Number(entrega.aceitoEm || entrega.inicioEntregaEm || 0)
  const historico = Array.isArray(estado.historicoEntregas) ? estado.historicoEntregas : []
  let evento = historico.find(item =>
    entrega.eventoHistoricoMensagemId &&
    String(item.eventoMensagemId || '') === String(entrega.eventoHistoricoMensagemId) &&
    jidNormalizedUser(item.entregadorId || '') === jidNormalizedUser(entrega.entregadorId || '') &&
    String(item.empresaId || '') === String(entrega.empresaId || '')
  )
  if (!evento) {
    evento = [...historico].reverse().find(item =>
      !item.finalizadaEm &&
      jidNormalizedUser(item.entregadorId || '') === jidNormalizedUser(entrega.entregadorId || '') &&
      // O mesmo ID de mensagem pode existir em empresas diferentes.
      // Normaliza o JID da empresa, mas mantém a correspondência restrita
      // à empresa de origem para nunca finalizar o histórico de outra corrida.
      jidNormalizedUser(item.empresaId || '') === jidNormalizedUser(entrega.empresaId || '') &&
      String(item.mensagemId || '') === String(entrega.mensagemId || '')
    )
  }
  if (evento) {
    evento.mensagemIndoRef = evento.mensagemIndoRef || entrega.mensagemIndoRef || null
    evento.mensagensFracionadasRefs = Array.isArray(entrega.fracionado?.mensagensRefs) ? [...entrega.fracionado.mensagensRefs] : (evento.mensagensFracionadasRefs || [])
    evento.mensagemFinalizacaoRef = entrega.mensagemFinalizacaoRef || null
  }
  if (evento && inicio > 0 && agora >= inicio && !evento.finalizadaEm) {
    evento.iniciadaEm = inicio
    evento.finalizadaEm = agora
    evento.tempoMinutos = Math.round(((agora - inicio) / 60000) * 10) / 10
    evento.finalizadaData = new Date(agora).toISOString().slice(0, 10)
  }
  if (evento) {
    evento.finalizadasQuantidade = entrega.fracionado && Number(entrega.fracionado.ultimoAtual) > 0
      ? Math.max(Number(evento.finalizadasQuantidade) || 0, Number(entrega.fracionado.ultimoAtual) || 0)
      : Math.max(Number(evento.finalizadasQuantidade) || 0, Number(entrega.quantidadeEntregas) || 1)
  }

  // Remove primeiro a entrega finalizada para calcular o status pelo total
  // de entregas que ainda permanecem sem finalização.
  estado.entregasAceitas = (estado.entregasAceitas || []).filter(x => x !== entrega)
  alterarStatusOperacional(entrega.entregadorId, 'conclusao')
  salvar()
  return true
}

function registrarConclusaoEntrega(entrega, quantidade, msg) {
  // Entregas aceitas já foram contabilizadas. Registros antigos, anteriores
  // a esta versão, ainda ganham o evento de histórico ao serem finalizados.
  if (!entrega.contagemRegistrada) {
    const quantidadeFinal = Math.max(1, Number(quantidade) || Number(entrega.quantidadeEntregas) || 1)
    entrega.contagemRegistrada = registrarEventoHistoricoEntrega(entrega, quantidadeFinal, msg)
  }
  finalizarEntregaAceita(entrega, msg)
}

async function apagarMensagemPorLimite(sock, msg, limite, quantidade) {
  try {
    await apagarMensagemControlada(sock, msg)
  } catch (erro) {
    console.log('Não foi possível apagar aceite acima do limite:', erro?.message || erro)
  }
  console.log(`LIMITE DE ENTREGAS | ${jidNormalizedUser(obterId(msg))} | limite ${limite} | tentativa ${quantidade}`)
}

function concluirEntregaPorMensagem(msg) {
  const texto = obterTexto(msg)
  const fracao = extrairFracao(texto)
  const ehFigurinhaFinalizacao = !!msg?.message?.stickerMessage
  // Figurinha só finaliza quando responde à mensagem específica de uma entrega aceita.
  if (!fracao && !ehFigurinhaFinalizacao) return false
  if (ehFigurinhaFinalizacao && !obterMensagemRespondida(msg)) return false

  const usuario = jidNormalizedUser(obterId(msg))
  const respondida = obterMensagemRespondida(msg)
  if (!Array.isArray(estado.entregasAceitas)) estado.entregasAceitas = []
  const ativasDoEntregador = estado.entregasAceitas.filter(x =>
    jidNormalizedUser(x?.entregadorId || '') === usuario && !x?.concluida
  )

  let entrega = null
  if (respondida) {
    // Prioriza estritamente a solicitação citada. Também aceita resposta
    // citando uma fração anterior do mesmo lote.
    entrega = ativasDoEntregador.find(x =>
      x.mensagemId === respondida ||
      (Array.isArray(x.fracionado?.mensagemIds) && x.fracionado.mensagemIds.includes(respondida))
    ) || null

    if (!entrega) {
      // A solicitação citada já pode ter sido concluída. Nesse caso, a
      // figurinha é apenas um aviso à empresa, nunca uma nova entrega.
      const jaRegistrada = (estado.historicoEntregas || []).some(item =>
        jidNormalizedUser(item?.entregadorId || '') === usuario &&
        (item?.mensagemId === respondida || item?.eventoMensagemId === respondida)
      )
      if (jaRegistrada || fracao) return true
      return false
    }
  } else {
    // Uma figurinha enviada logo após 1/4, 2/2 etc. é aviso à empresa,
    // mesmo que o entregador ainda tenha outra solicitação ativa.
    const ultimoEventoFracionado = [...(estado.historicoEntregas || [])]
      .reverse()
      .find(item => jidNormalizedUser(item?.entregadorId || '') === usuario && Number(item?.fracaoTotal) > 0)

    // Sem citação, só é seguro associar quando existe uma única entrega
    // ativa. Com entregas de empresas diferentes, não escolhe uma ao acaso.
    if (ativasDoEntregador.length === 1) {
      entrega = ativasDoEntregador[0]
    } else if (ativasDoEntregador.length > 1) {
      return true
    } else {
      return false
    }
  }

  if (!entrega) return false

  if (ehFigurinhaFinalizacao) {
    finalizarEntregaAceita(entrega, msg)
    return true
  }

  if (fracao) {
    // O total de um lote já iniciado não pode mudar silenciosamente (ex.: 1/4
    // seguido de 2/5). Reiniciar o contador nesse caso faria o histórico somar
    // quantidades incompatíveis e poderia recontar unidades já concluídas.
    if (entrega.fracionado && Number(entrega.fracionado.total) > 0 && Number(entrega.fracionado.total) !== fracao.total) {
      console.log(`FRACIONAMENTO IGNORADO | total divergente | entregador=${usuario} | salvo=${entrega.fracionado.total} | recebido=${fracao.total}`)
      salvar()
      return true
    }
    if (!entrega.fracionado) {
      entrega.fracionado = { total: fracao.total, ultimoAtual: 0, ultimaMensagemEm: 0, mensagemIds: [], mensagensRefs: [] }
    }
    if (!Array.isArray(entrega.fracionado.mensagemIds)) entrega.fracionado.mensagemIds = []
    if (!Array.isArray(entrega.fracionado.mensagensRefs)) entrega.fracionado.mensagensRefs = []

    const refFracao = capturarReferenciaMensagem(msg)
    if (refFracao && !entrega.fracionado.mensagensRefs.some(ref => ref.id === refFracao.id)) entrega.fracionado.mensagensRefs.push(refFracao)

    const ultimoAtual = Math.max(0, Number(entrega.fracionado.ultimoAtual) || 0)
    if (fracao.atual <= ultimoAtual) { salvar(); return true }

    // 1/4 conta uma entrega; 2/4 conta só a nova entrega concluída desde
    // a última atualização. Se pular números, contabiliza a diferença.
    const incremento = fracao.atual - ultimoAtual
    entrega.fracionado.ultimoAtual = fracao.atual
    entrega.fracionado.ultimaMensagemEm = Date.now()
    const idMensagemFracao = msg?.key?.id || null
    if (idMensagemFracao && !entrega.fracionado.mensagemIds.includes(idMensagemFracao)) {
      entrega.fracionado.mensagemIds.push(idMensagemFracao)
      if (entrega.fracionado.mensagemIds.length > 20) entrega.fracionado.mensagemIds.shift()
    }
    // O aceite inicial já cria um evento no histórico. Quando o entregador
    // informa o fracionado (ex.: 1/4 ... 4/4), esse total substitui a
    // quantidade inicial daquela solicitação no ranking; não é somado por
    // cima dela e não cria quatro eventos duplicados.
    const historicoBase = (estado.historicoEntregas || []).find(item =>
      String(item?.mensagemId || '') === String(entrega.mensagemId || '') &&
      jidNormalizedUser(item?.entregadorId || '') === usuario &&
      String(item?.empresaId || '') === String(entrega.empresaId || '')
    )

    if (historicoBase) {
      // O volume total é conhecido já no primeiro fracionamento: 1/4 significa
      // quatro entregas no volume da empresa/entregador, com 1 concluída até então.
      historicoBase.quantidade = Math.max(1, fracao.total)
      historicoBase.finalizadasQuantidade = Math.max(Number(historicoBase.finalizadasQuantidade) || 0, fracao.atual)
      historicoBase.fracaoAtual = fracao.atual
      historicoBase.fracaoTotal = fracao.total
      historicoBase.fracionamentoAtualizadoEm = Date.now()
      // O lote só recebe horário de conclusão quando a última fração chega.
      // Frações intermediárias atualizam o progresso, mas não encerram a entrega.
      if (fracao.atual === fracao.total && !historicoBase.finalizadaEm) {
        const inicio = Number(entrega.aceitoEm || entrega.inicioEntregaEm || 0)
        if (inicio > 0 && Date.now() >= inicio) {
          historicoBase.finalizadaEm = Date.now()
          historicoBase.tempoMinutos = Math.round(((Date.now() - inicio) / 60000) * 10) / 10
          historicoBase.finalizadaData = new Date().toISOString().slice(0, 10)
        }
      }
      historicoBase.mensagemIndoRef = historicoBase.mensagemIndoRef || entrega.mensagemIndoRef || null
      historicoBase.mensagensFracionadasRefs = [...(entrega.fracionado.mensagensRefs || [])]
      entrega.contagemRegistrada = true
      // A empresa também conta o volume completo assim que o lote é identificado.
      const solicitacaoEmpresa = (estado.solicitacoesRelatorio || []).find(item =>
        String(item?.mensagemId || '') === String(entrega.mensagemId || '')
      )
      if (solicitacaoEmpresa) {
        solicitacaoEmpresa.quantidade = Math.max(1, fracao.total)
        solicitacaoEmpresa.fracaoAtual = fracao.atual
        solicitacaoEmpresa.fracaoTotal = fracao.total
      }
    } else if (!entrega.contagemRegistrada) {
      // Compatibilidade com registros antigos sem evento de aceite.
      entrega.contagemRegistrada = registrarEventoHistoricoEntrega(entrega, fracao.total, msg, fracao)
      const eventoNovo = [...(estado.historicoEntregas || [])].reverse().find(item =>
        String(item?.mensagemId || '') === String(entrega.mensagemId || '') &&
        jidNormalizedUser(item?.entregadorId || '') === usuario &&
        String(item?.empresaId || '') === String(entrega.empresaId || '')
      )
      if (eventoNovo) eventoNovo.finalizadasQuantidade = fracao.atual
    }

    // Um lote fracionado representa o total informado, mas a quantidade ativa
    // cai conforme cada unidade é concluída. Isso alimenta status e limite.
    entrega.quantidadeEntregas = Math.max(1, fracao.total)

    if (fracao.atual === fracao.total) {
      finalizarEntregaAceita(entrega, msg)
      const historicoFinal = (estado.historicoEntregas || []).find(item =>
        String(item?.mensagemId || '') === String(entrega.mensagemId || '') &&
        jidNormalizedUser(item?.entregadorId || '') === usuario &&
        String(item?.empresaId || '') === String(entrega.empresaId || '')
      )
      if (historicoFinal) historicoFinal.finalizadasQuantidade = fracao.total
    } else {
      alterarStatusOperacional(usuario, 'fracionado')
      salvar()
    }
    return true
  }

  return false
}

/* =====================================
   PROCESSAR DELIVERY
===================================== */

function registrarLoteFracionadoSemIndo(msg, fracao) {
  const usuario = jidNormalizedUser(obterId(msg))
  if (!usuario || !fracao || obterMensagemRespondida(msg)) return false
  const ativas = (estado.entregasAceitas || []).filter(e =>
    jidNormalizedUser(e?.entregadorId || '') === usuario && !e?.concluida
  )
  // Lotes grandes podem ter sido feitos fora do grupo; eles são registrados
  // separadamente para não se associarem por engano a um INDO ainda aberto.
  // Lotes menores seguem a associação normal quando há uma entrega ativa.
  if (ativas.length && Number(fracao.total) < 5) return false

  const mensagemId = String(msg?.key?.id || '')
  if (!mensagemId) return false
  if ((estado.historicoEntregas || []).some(e =>
    String(e?.eventoMensagemId || '') === mensagemId ||
    (Array.isArray(e?.mensagensFracionadasIds) && e.mensagensFracionadasIds.includes(mensagemId))
  )) return true

  const agora = Date.now()
  const pessoa = (estado.entregadores || []).find(p => jidNormalizedUser(p.id || '') === usuario) ||
    (estado.online || []).find(p => jidNormalizedUser(p.id || '') === usuario) ||
    (estado.espera || []).find(p => jidNormalizedUser(p.id || '') === usuario)
  const empresaNome = EMPRESA_CONFIG[empresaAtual]?.nome || 'Empresa'
  const empresaId = String(msg?.key?.remoteJid || '')
  if (!Array.isArray(estado.historicoEntregas)) estado.historicoEntregas = []

  // Agrupa 1/N, 2/N ... N/N numa única linha de histórico. Sem isso cada
  // atualização gerava uma nova entrega N e inflava a contagem repetidamente.
  const loteRecente = [...estado.historicoEntregas].reverse().find(item => {
    if (item?.origem !== 'lote-fracionado-sem-indo') return false
    if (jidNormalizedUser(item?.entregadorId || '') !== usuario) return false
    if (String(item?.empresaId || '') !== empresaId) return false
    if (Number(item?.fracaoTotal) !== Number(fracao.total)) return false
    if (Number(item?.fracaoAtual) >= Number(item?.fracaoTotal)) return false
    const ultimaAtualizacao = Number(item?.fracionamentoAtualizadoEm || item?.concluidaEm || 0)
    return ultimaAtualizacao > 0 && agora - ultimaAtualizacao <= 90 * 60 * 1000
  })

  // Se o último estágio N/N chegar repetido como uma nova mensagem poucos
  // instantes depois, não abre outro lote idêntico. Um novo lote deve começar
  // por 1/N ou ficar fora dessa curta janela de deduplicação.
  if (!loteRecente && fracao.atual === fracao.total) {
    const concluidoRecentemente = [...estado.historicoEntregas].reverse().find(item =>
      item?.origem === 'lote-fracionado-sem-indo' &&
      jidNormalizedUser(item?.entregadorId || '') === usuario &&
      String(item?.empresaId || '') === empresaId &&
      Number(item?.fracaoTotal) === Number(fracao.total) &&
      Number(item?.fracaoAtual) === Number(item?.fracaoTotal) &&
      Number(item?.finalizadaEm || item?.fracionamentoAtualizadoEm || 0) > 0 &&
      agora - Number(item.finalizadaEm || item.fracionamentoAtualizadoEm) <= 5 * 60 * 1000
    )
    if (concluidoRecentemente) {
      if (!Array.isArray(concluidoRecentemente.mensagensFracionadasIds)) concluidoRecentemente.mensagensFracionadasIds = []
      if (!concluidoRecentemente.mensagensFracionadasIds.includes(mensagemId)) concluidoRecentemente.mensagensFracionadasIds.push(mensagemId)
      if (concluidoRecentemente.mensagensFracionadasIds.length > 50) concluidoRecentemente.mensagensFracionadasIds.shift()
      const referencia = capturarReferenciaMensagem(msg)
      if (!Array.isArray(concluidoRecentemente.mensagensFracionadasRefs)) concluidoRecentemente.mensagensFracionadasRefs = []
      if (referencia && !concluidoRecentemente.mensagensFracionadasRefs.some(ref => ref?.id === referencia.id)) concluidoRecentemente.mensagensFracionadasRefs.push(referencia)
      salvar()
      return true
    }
  }

  if (loteRecente && fracao.atual !== 1) {
    if (!Array.isArray(loteRecente.mensagensFracionadasIds)) loteRecente.mensagensFracionadasIds = []
    if (!Array.isArray(loteRecente.mensagensFracionadasRefs)) loteRecente.mensagensFracionadasRefs = []
    loteRecente.mensagensFracionadasIds.push(mensagemId)
    if (loteRecente.mensagensFracionadasIds.length > 50) loteRecente.mensagensFracionadasIds.shift()
    const referencia = capturarReferenciaMensagem(msg)
    if (referencia && !loteRecente.mensagensFracionadasRefs.some(ref => ref?.id === referencia.id)) {
      loteRecente.mensagensFracionadasRefs.push(referencia)
    }

    if (fracao.atual > Number(loteRecente.fracaoAtual || 0)) {
      loteRecente.fracaoAtual = fracao.atual
      loteRecente.finalizadasQuantidade = Math.max(Number(loteRecente.finalizadasQuantidade) || 0, fracao.atual)
      loteRecente.fracionamentoAtualizadoEm = agora
      if (fracao.atual === fracao.total) {
        loteRecente.finalizadaEm = agora
        loteRecente.finalizadaData = new Date(agora).toISOString().slice(0, 10)
      }
      if (loteRecente.finalizadaEm) loteRecente.finalizadasQuantidade = fracao.total
    }

    const pedidoEmpresa = (estado.solicitacoesRelatorio || []).find(item =>
      String(item?.mensagemId || '') === String(loteRecente.mensagemId || '') &&
      String(item?.empresaId || '') === empresaId &&
      item?.origem === 'lote-fracionado-sem-indo'
    )
    if (pedidoEmpresa) {
      pedidoEmpresa.quantidade = Math.max(1, fracao.total)
      pedidoEmpresa.fracaoAtual = Math.max(Number(pedidoEmpresa.fracaoAtual) || 0, Number(loteRecente.fracaoAtual) || 0)
      pedidoEmpresa.fracaoTotal = fracao.total
    }
    salvar()
    return true
  }

  // Um número menor que o progresso já salvo (sem ser uma nova fração 1/N)
  // é tratado como atualização atrasada, não como uma nova contagem.
  if (loteRecente && fracao.atual !== 1 && fracao.atual <= Number(loteRecente.fracaoAtual || 0)) {
    if (!Array.isArray(loteRecente.mensagensFracionadasIds)) loteRecente.mensagensFracionadasIds = []
    loteRecente.mensagensFracionadasIds.push(mensagemId)
    if (loteRecente.mensagensFracionadasIds.length > 50) loteRecente.mensagensFracionadasIds.shift()
    const referencia = capturarReferenciaMensagem(msg)
    if (!Array.isArray(loteRecente.mensagensFracionadasRefs)) loteRecente.mensagensFracionadasRefs = []
    if (referencia && !loteRecente.mensagensFracionadasRefs.some(ref => ref?.id === referencia.id)) loteRecente.mensagensFracionadasRefs.push(referencia)
    salvar()
    return true
  }

  const registro = {
    mensagemId,
    eventoMensagemId: mensagemId,
    mensagensFracionadasIds: [mensagemId],
    mensagemIndoRef: null,
    mensagensFracionadasRefs: [capturarReferenciaMensagem(msg)].filter(Boolean),
    mensagemFinalizacaoRef: null,
    fracaoAtual: fracao.atual,
    fracaoTotal: fracao.total,
    fracionamentoAtualizadoEm: agora,
    empresaId,
    empresaNome,
    entregadorId: usuario,
    entregadorNome: pessoa?.nome || obterNome(msg) || 'Entregador',
    quantidade: Math.max(1, fracao.total),
    finalizadasQuantidade: Math.max(0, fracao.atual),
    concluidaEm: agora,
    iniciadaEm: null,
    finalizadaEm: fracao.atual === fracao.total ? agora : null,
    finalizadaData: fracao.atual === fracao.total ? new Date(agora).toISOString().slice(0, 10) : null,
    tempoMinutos: null,
    data: new Date(agora).toISOString().slice(0, 10),
    hora: new Date(agora).getHours(),
    origem: 'lote-fracionado-sem-indo'
  }
  if (registro.finalizadaEm) registro.finalizadasQuantidade = fracao.total
  estado.historicoEntregas.push(registro)

  if (!Array.isArray(estado.solicitacoesRelatorio)) estado.solicitacoesRelatorio = []
  if (!(estado.solicitacoesRelatorio || []).some(e =>
    e?.mensagemId === mensagemId && String(e?.empresaId || '') === empresaId && e?.origem === 'lote-fracionado-sem-indo'
  )) {
    estado.solicitacoesRelatorio.push({
      mensagemId,
      empresaId,
      empresaNome,
      quantidade: Math.max(1, fracao.total),
      solicitadaEm: agora,
      data: registro.data,
      origem: 'lote-fracionado-sem-indo',
      fracaoAtual: fracao.atual,
      fracaoTotal: fracao.total
    })
  }
  salvar()
  return true
}

async function processarDelivery(
  sock,
  msg
) {

  const texto =
    obterTexto(msg)

  let comando =
    normalizarTexto(texto).replace(/[.!?]+$/g, '').trim()
  if (estado?.variacoesEntrega?.indo) comando = comando.replace(/[\s]*(?:✅|☑️|✔️)+$/u, '').trim()

  const id =
    obterId(msg)

  // ADM pode atribuir imediatamente uma solicitação citando a mensagem da
  // empresa e mencionando o entregador: @entregador. Só vale no grupo da empresa.
  const mensagemCitadaADM = obterMensagemRespondida(msg)
  const marcadosADM = msg?.message?.extendedTextMessage?.contextInfo?.mentionedJid || []
  if (grupos.g2 && msg?.key?.remoteJid === grupos.g2 && mensagemCitadaADM && marcadosADM.length) {
    let remetenteEhADM = false
    try {
      const meta = await sock.groupMetadata(grupos.g2)
      remetenteEhADM = (meta?.participants || []).some(p =>
        jidNormalizedUser(p.id) === jidNormalizedUser(id) && (p.admin === 'admin' || p.admin === 'superadmin')
      )
    } catch (e) {
      console.log('Não foi possível validar ADM para atribuição de entrega:', e.message)
    }
    if (remetenteEhADM) {
      const corridaADM = (estado.corridas || []).find(item => item.mensagemId === mensagemCitadaADM)
      if (corridaADM) {
        const alvo = jidNormalizedUser(marcadosADM[0])
        const estaOnlineAlvo = estado.online.some(p => jidNormalizedUser(p.id) === alvo)
        const cadastroAlvoExistente = (estado.entregadores || []).find(x => jidNormalizedUser(x.id) === alvo)
        if (estaOnlineAlvo || cadastroAlvoExistente) {
          const rotaADM = estado.rotaAtiva && Date.now() < Number(estado.rotaAtiva.expiraEm || 0) &&
            estado.rotaAtiva.empresaId === corridaADM.empresaId && jidNormalizedUser(estado.rotaAtiva.entregadorId) === alvo
          const limiteAlvo = obterLimiteEntregas(alvo)
          if (excedeLimiteEntregas(alvo, corridaADM.quantidadeEntregas, !!rotaADM)) {
            await apagarMensagemPorLimite(sock, msg, limiteAlvo, corridaADM.quantidadeEntregas)
            return
          }
          // A menção do ADM equivale ao INDO do entregador: registra agora a entrega,
          // inicia a medição de tempo e deixa a mensagem original disponível para figurinha.
          corridaADM.entregadorResponsavelId = alvo
          const cadastroAlvo = (estado.entregadores || []).find(x => jidNormalizedUser(x.id) === alvo)
          const onlineAlvo = estado.online.find(x => jidNormalizedUser(x.id) === alvo)
          corridaADM.entregadorResponsavelNome = cadastroAlvo?.nome || onlineAlvo?.nome || 'Entregador'
          corridaADM.atribuidaPorADM = true
          corridaADM.atribuidaADMEm = Date.now()
          corridaADM.atribuidaADMId = jidNormalizedUser(id)
          corridaADM.disputa = false
          let aceitaPorADM = false
          if (estaOnlineAlvo) {
            aceitaPorADM = aceitarCorrida(alvo, corridaADM.mensagemId, msg?.key?.id || null, msg)
          } else {
            // Mesmo fora da lista online, a atribuição administrativa vale como INDO para os relatórios.
            const registroADM = registrarEntregaAceita(corridaADM, alvo, msg?.key?.id || null, null, false, null, msg)
            if (registroADM) {
              alterarStatusOperacional(alvo, 'aceite')
              registroADM.entregadorNome = cadastroAlvoExistente.nome || corridaADM.entregadorResponsavelNome || 'Entregador'
              const eventoADM = [...(estado.historicoEntregas || [])].reverse().find(item => item.eventoMensagemId === (msg?.key?.id || null) && jidNormalizedUser(item.entregadorId || '') === alvo)
              if (eventoADM) eventoADM.entregadorNome = registroADM.entregadorNome
              estado.corridas = (estado.corridas || []).filter(item => item !== corridaADM)
              aceitaPorADM = true
              salvar()
            }
          }
          if (aceitaPorADM) {
            corridaADM.atribuidaPorADM = false
            corridaADM.aceitaPorADM = true
            corridaADM.aceitaPorADMEm = Date.now()
            salvar()
            console.log('Entrega atribuída e contabilizada imediatamente pela menção do ADM.')
          } else {
            // Se a validação operacional impedir a aceitação, mantém o vínculo para não perder a entrega.
            corridaADM.atribuidaPorADM = true
            salvar()
            console.log('Entrega vinculada por ADM, mas a aceitação imediata não passou pelas validações operacionais.')
          }
          return
        }
      }
    }
  }

  const fracaoSemCitada = extrairFracao(texto)
  if (fracaoSemCitada && !obterMensagemRespondida(msg) && registrarLoteFracionadoSemIndo(msg, fracaoSemCitada)) {
    return
  }

  if (concluirEntregaPorMensagem(msg)) {
    await publicarListasTodasEmpresas(sock)
    return
  }

  /*
    INDO / LNDO

    REGRA DA SOLICITAÇÃO:
      - durante os 2 minutos, somente o entregador reservado pode aceitar;
      - se outro entregador responder "indo" à mesma solicitação,
        o bot apaga a mensagem dele e NÃO altera a fila;
      - após os 2 minutos, a corrida entra em disputa e qualquer
        entregador online pode aceitar;
      - somente o PRIMEIRO que aceitar a corrida vai para o final;
      - os demais "indo" para a mesma solicitação não alteram a fila.

    Se não houver uma solicitação específica, "indo/lndo" continua
    funcionando como comando para ir ao final da fila.
  */

  if (
    ehComandoIndo(comando, msg)
  ) {

    const mensagemRespondidaId =
      obterMensagemRespondida(msg)

    const usuario = jidNormalizedUser(id)

    // Somente quem está na LISTA ONLINE pode mandar "indo" no grupo da empresa.
    // Durante o horário de pico, a mensagem não é apagada: apenas é ignorada.
    const estaOnline = estado.online.some(pessoa => jidNormalizedUser(pessoa.id) === usuario)
    if (!estaOnline) {
      if (!listaSuspensaPico) {
        try {
          await apagarMensagemControlada(sock, msg)
        } catch (erro) {
          console.log('Não foi possível apagar o INDO de quem não está ONLINE:', erro?.message || erro)
        }
      }
      return
    }

    /*
      Se respondeu diretamente a uma solicitação, aplica as regras
      específicas daquela solicitação.
    */
    if (mensagemRespondidaId) {

      let corrida =
        Array.isArray(estado.corridas)
          ? estado.corridas.find(
              item => item.mensagemId === mensagemRespondidaId
            )
          : null

      // Se o bot não reconheceu o bairro e, por isso, não registrou a solicitação,
      // um INDO válido respondido à mensagem original cria uma entrega genérica,
      // conta uma unidade nos relatórios e encaminha a mensagem ao ADM para mapear o bairro.
      if (!corrida) {
        const contexto = msg?.message?.extendedTextMessage?.contextInfo ||
          msg?.message?.imageMessage?.contextInfo || msg?.message?.videoMessage?.contextInfo ||
          msg?.message?.audioMessage?.contextInfo || msg?.message?.stickerMessage?.contextInfo ||
          msg?.message?.documentMessage?.contextInfo || msg?.message?.documentWithCaptionMessage?.message?.documentMessage?.contextInfo || {}
        const mensagemOriginal = contexto.quotedMessage || null
        const textoOriginal = String(
          mensagemOriginal?.conversation ||
          mensagemOriginal?.extendedTextMessage?.text ||
          mensagemOriginal?.imageMessage?.caption ||
          mensagemOriginal?.videoMessage?.caption ||
          mensagemOriginal?.documentMessage?.caption ||
          mensagemOriginal?.audioMessage?.caption || ''
        ).trim()
        const jidGrupoEmpresa = String(msg?.key?.remoteJid || '')
        if (mensagemOriginal && textoOriginal && jidGrupoEmpresa.endsWith('@g.us') &&
            !ehComandoIndo(normalizarTexto(textoOriginal).trim())) {
          const remetenteOriginal = jidNormalizedUser(contexto.participant || '')
          // Só converte uma conversa em entrega genérica quando a mensagem citada
          // veio de alguém que NÃO faz parte do grupo de entregadores da empresa.
          // Mensagens de entregadores sem bairro não devem virar pedidos da empresa.
          const remetenteEhEntregador = Boolean(remetenteOriginal) &&
            (Array.isArray(grupos.g1Participantes) && grupos.g1Participantes.includes(remetenteOriginal))
          if (remetenteOriginal && !remetenteEhEntregador) {
            const msgOriginalFake = {
              key: { remoteJid: jidGrupoEmpresa, id: mensagemRespondidaId, participant: remetenteOriginal, fromMe: false },
              message: mensagemOriginal,
              pushName: 'Empresa'
            }
            corrida = criarCorrida(msgOriginalFake, { is_delivery: true, neighborhoods: [] })
            corrida.bairroNaoIdentificado = true
            corrida.bairrosIdentificados = []
            corrida.quantidadeEntregas = 1
            corrida.entregadorResponsavelId = usuario
            corrida.entregadorResponsavelNome = estado.online.find(p => jidNormalizedUser(p.id) === usuario)?.nome || 'Entregador'
            corrida.disputa = false
            salvar()
            try {
              await avisarAdmBairroNaoIdentificado(sock, msgOriginalFake, jidGrupoEmpresa, mensagemRespondidaId)
              corrida.avisoBairroNaoIdentificadoEnviado = true
              salvar()
            } catch (e) {
              console.log('Falha ao avisar ADM sobre bairro não identificado:', e?.message || e)
            }
          }
        }
      }

      if (corrida && (!Array.isArray(corrida.bairrosIdentificados) || corrida.bairrosIdentificados.length === 0) && !corrida.avisoBairroNaoIdentificadoEnviado) {
        corrida.bairroNaoIdentificado = true
        try {
          const referenciaOriginal = corrida.mensagemOriginalKey && corrida.mensagemOriginalConteudo
            ? { key: corrida.mensagemOriginalKey, message: corrida.mensagemOriginalConteudo }
            : null
          await avisarAdmBairroNaoIdentificado(sock, referenciaOriginal, corrida.mensagemOriginalKey?.remoteJid || '', mensagemRespondidaId)
          corrida.avisoBairroNaoIdentificadoEnviado = true
          salvar()
        } catch (e) {
          console.log('Falha ao avisar ADM sobre bairro não identificado:', e?.message || e)
        }
      }

      /*
        Se essa solicitação já foi aceita pelo primeiro entregador,
        qualquer novo "indo" para ela é apagado e não mexe na fila.
      */
      const solicitacaoJaAceita =
        Array.isArray(estado.entregasAceitas) &&
        estado.entregasAceitas.some(
          entrega => entrega.mensagemId === mensagemRespondidaId
        )

      if (solicitacaoJaAceita) {
        try {
          await apagarMensagemControlada(sock, msg)
        } catch (erro) {
          console.log('Não foi possível apagar o INDO duplicado:', erro?.message || erro)
        }
        return
      }

      if (!corrida) {
        // Mesmo sem reconhecer a mensagem citada como entrega, o INDO respondido
        // deve permanecer no grupo e colocar o entregador no fim da fila.
        // Guardamos a posição e o ID do INDO para restaurá-la se ele apagar a mensagem.
        const posicaoOriginalIndo = estado.online.findIndex(p => jidNormalizedUser(p?.id || '') === usuario)
        const moveuParaFinal = mandarParaFinal(usuario, 'indo-sem-entrega')
        if (moveuParaFinal) {
          if (!Array.isArray(estado.indosSemEntrega)) estado.indosSemEntrega = []
          estado.indosSemEntrega = estado.indosSemEntrega.filter(x => String(x?.mensagemAceiteId || '') !== String(msg?.key?.id || ''))
          estado.indosSemEntrega.push({
            mensagemAceiteId: msg?.key?.id || null,
            entregadorId: usuario,
            entregadorNome: estado.entregadores?.find(p => jidNormalizedUser(p.id) === usuario)?.nome || nome || 'Entregador',
            posicaoOriginal: posicaoOriginalIndo,
            criadoEm: Date.now()
          })
          salvar()
          await publicarLista(sock)
        }
        return
      }

      if (corrida) {
        // Entrega atribuída por ADM só pode ser aceita pelo entregador marcado.
        // A atribuição não conta: a contagem ocorre apenas no INDO válido.
        if (corrida.atribuidaPorADM) {
          const responsavelAtribuido = jidNormalizedUser(corrida.entregadorResponsavelId || '')
          if (responsavelAtribuido !== usuario) {
            if (!listaSuspensaPico) {
              try { await apagarMensagemControlada(sock, msg) }
              catch (erro) { console.log('Não foi possível apagar INDO de entrega atribuída a outro entregador:', erro?.message || erro) }
            }
            return
          }
          const quantidadeAtribuida = Math.max(1, Number(corrida.quantidadeEntregas) || 1)
          const limiteAtribuido = obterLimiteEntregas(usuario)
          if (excedeLimiteEntregas(usuario, quantidadeAtribuida, false)) {
            await apagarMensagemPorLimite(sock, msg, limiteAtribuido, quantidadeAtribuida)
            return
          }
          if (aceitarCorrida(usuario, mensagemRespondidaId, msg?.key?.id || null, msg)) {
            corrida.atribuidaPorADM = false
            corrida.aceitaAposAtribuicaoADM = true
            salvar()
            await publicarListaComAtraso(sock)
          }
          return
        }
        if (listaSuspensaPico) corrida.disputa = true

        /*
          Confere o prazo também no instante em que chega o "indo".
          O temporizador roda a cada segundo, então uma mensagem pode chegar
          depois dos 2 minutos antes da próxima verificação do temporizador.
          Nesse caso, a disputa começa imediatamente e a vez é registrada
          como perdida apenas uma vez.
        */
        if (!corrida.disputa && prazoDeDisputaAtingido(corrida)) {
          await processarPerdaDeVez(sock, corrida)
        }

        /*
          Dentro dos 2 minutos: somente o entregador reservado pode pegar.
          Qualquer outro entregador tem o "indo" apagado e permanece
          exatamente na mesma posição.
        */
        if (!corrida.disputa) {
          const responsavelId = corrida.entregadorResponsavelId
            ? jidNormalizedUser(corrida.entregadorResponsavelId)
            : jidNormalizedUser(estado.online[0]?.id || '')
          if (responsavelId === usuario) {
            const limite = obterLimiteEntregas(usuario)
            const quantidade = Math.max(1, Number(corrida.quantidadeEntregas) || 1)
            const rotaPermitida = !!(estado.rotaAtiva && estado.rotaAtiva.empresaId === corrida.empresaId && jidNormalizedUser(estado.rotaAtiva.entregadorId) === usuario && Date.now() < Number(estado.rotaAtiva.expiraEm || 0))
            if (excedeLimiteEntregas(usuario, quantidade, rotaPermitida)) {
              await apagarMensagemPorLimite(sock, msg, limite, quantidade)
              return
            }
            if (aceitarCorrida(usuario, mensagemRespondidaId, msg?.key?.id || null, msg)) {
              await publicarListaComAtraso(sock)
            } else if (excedeLimiteEntregas(usuario, quantidade, rotaPermitida)) {
              await apagarMensagemPorLimite(sock, msg, limite, quantidade)
            }
            return
          }

          if (!listaSuspensaPico) {
            try {
              await apagarMensagemControlada(sock, msg)
            } catch (erro) {
              console.log('Não foi possível apagar o INDO fora da vez:', erro?.message || erro)
            }
          }
          return
        }

        /*
          Depois dos 2 minutos: qualquer entregador ONLINE pode pegar.
          O primeiro que conseguir aceitar é o único que vai para o final.
        */
        const limiteDisputa = obterLimiteEntregas(usuario)
        const quantidadeDisputa = Math.max(1, Number(corrida.quantidadeEntregas) || 1)
        if (excedeLimiteEntregas(usuario, quantidadeDisputa, false)) {
          await apagarMensagemPorLimite(sock, msg, limiteDisputa, quantidadeDisputa)
          return
        }
        if (aceitarCorrida(usuario, mensagemRespondidaId, msg?.key?.id || null, msg)) {
          await publicarListaComAtraso(sock)
        } else if (excedeLimiteEntregas(usuario, quantidadeDisputa, false)) {
          await apagarMensagemPorLimite(sock, msg, limiteDisputa, quantidadeDisputa)
        }
        return
      }
    }

    /*
      Sem resposta direta a uma solicitação específica, mantém o
      comportamento antigo do comando "indo": aceita a corrida atual
      quando permitido; caso contrário, manda o entregador para o final.
    */
    // INDO solto no grupo de empresas deve ser apagado; só vale responder à solicitação.
    try { await apagarMensagemControlada(sock, msg) }
    catch (erro) { console.log('Não foi possível apagar INDO sem resposta à entrega:', erro?.message || erro) }
    return
  }


  /*
    MENSAGEM DE EMPRESA

    Existem entregadores que também possuem empresa e, por isso,
    participam do grupo das empresas. Nesses casos, uma mensagem
    enviada por um entregador no grupo das empresas deve ser tratada
    como uma NOVA SOLICITAÇÃO DE ENTREGA quando NÃO for:
      - figurinha;
      - fracionamento (ex.: 1/2, 2/2);
      - "indo" / "lndo".

    Assim, o fato de o remetente também ser entregador não impede
    que ele envie uma entrega da própria empresa.
  */

  const usuarioParticipante = jidNormalizedUser(id)
  const ehEntregadorNoGrupo =
    Array.isArray(grupos.g1Participantes) &&
    grupos.g1Participantes.includes(usuarioParticipante)

  const ehFigurinha = !!msg?.message?.stickerMessage
  const ehFracionado = !!extrairFracao(texto)
  const ehIndo = ehComandoIndo(estado?.variacoesEntrega?.indo ? comando.replace(/[\s]*(?:✅|☑️|✔️)+$/u, '').trim() : comando, msg)
  const ehSocialOuAdministrativa = ehMensagemSocialOuAdministrativa(msg, texto)

  const ehEntregaDeEmpresaEnviadaPorEntregador =
    ehEntregadorNoGrupo &&
    !ehFigurinha &&
    !ehFracionado &&
    !ehIndo &&
    !ehSocialOuAdministrativa

  const textoDaSolicitacao = obterTexto(msg)
  const remetentePodeSolicitar = ehEmpresa(msg) || ehEntregaDeEmpresaEnviadaPorEntregador
  // Critério determinístico: no grupo da empresa, mensagem sem bairro reconhecido
  // é conversa, mesmo que contenha palavras como 'entrega' ou 'pedido'. Não usar
  // IA para transformar conversa em entrega. A exceção é o INDO respondido à
  // mensagem sem bairro, tratada acima como entrega genérica vinculada ao rider.
  const temConteudoDeEntrega = !ehFigurinha &&
    Boolean(textoDaSolicitacao) &&
    ehPedidoEntregaPeloConteudo(textoDaSolicitacao)

  if (
    remetentePodeSolicitar &&
    !ehSocialOuAdministrativa &&
    temConteudoDeEntrega
  ) {
    const corridaCriada = criarCorrida(msg, analiseGemini)

    // Aviso privado único quando a entrega é atribuída ao entregador da vez.
    if (!listaSuspensaPico && corridaCriada && corridaCriada.entregadorResponsavelId && !corridaCriada.avisoPrivadoEnviado) {
      try {
        const idResponsavel = jidNormalizedUser(corridaCriada.entregadorResponsavelId)
        await sock.sendMessage(idResponsavel, {
          text: `📦 *ENTREGA LÁ NO GRUPO*\n\nGrupo: *${EMPRESA_CONFIG[empresaDoGrupo(msg.key.remoteJid)]?.g2Nome || EMPRESA_CONFIG[empresaAtual]?.g2Nome || 'grupo da empresa'}*\n\nAbra o grupo indicado e responda *indo* à mensagem da entrega dentro de 2 minutos.`,
          mentions: [idResponsavel]
        }, { quoted: msg })
        corridaCriada.avisoPrivadoEnviado = true
        salvar()
      } catch (e) {
        console.log(`Erro ao avisar entrega no privado (${corridaCriada.entregadorResponsavelNome || corridaCriada.entregadorResponsavelId}):`, e.message)
      }
    }
    return
  }
}


/* =====================================
   APAGAR ÁUDIO DE NÃO-ADM NO GRUPO
===================================== */

function ehAudio(msg) {
  const mensagem = msg?.message || {}
  return !!(
    mensagem.audioMessage ||
    mensagem.viewOnceMessage?.message?.audioMessage ||
    mensagem.viewOnceMessageV2?.message?.audioMessage ||
    mensagem.viewOnceMessageV2Extension?.message?.audioMessage
  )
}

async function apagarAudioSeNaoADM(sock, msg) {
  if (!ehAudio(msg)) return false

  const grupo = msg?.key?.remoteJid
  if (!grupo || !grupos.g1 || grupo !== grupos.g1) return false

  const adm = await ehADM(sock, msg)
  if (adm) return false

  try {
    await apagarMensagemControlada(sock, msg)
    console.log('🔇 ÁUDIO APAGADO: remetente não é ADM')
    return true
  } catch (e) {
    console.log('Erro ao apagar áudio de não-ADM:', e.message)
    return false
  }
}

/* =====================================
   COMANDO PENDÊNCIA (até 2 erros de digitação)
===================================== */

function distanciaEdicao(a, b) {
  const anterior = Array.from(String(a || ''))
  const atual = Array.from(String(b || ''))
  let linhaAnterior = Array.from({ length: atual.length + 1 }, (_, i) => i)

  for (let i = 1; i <= anterior.length; i++) {
    const linhaAtual = [i]
    for (let j = 1; j <= atual.length; j++) {
      const custo = anterior[i - 1] === atual[j - 1] ? 0 : 1
      linhaAtual[j] = Math.min(
        linhaAtual[j - 1] + 1,
        linhaAnterior[j] + 1,
        linhaAnterior[j - 1] + custo
      )
    }
    linhaAnterior = linhaAtual
  }
  return linhaAnterior[atual.length]
}

function ehComandoPendencia(texto) {
  const comando = normalizarTexto(texto)
    .replace(/[.!?,;:]+$/g, '')
    .trim()
  return !!comando && !/\s/.test(comando) && distanciaEdicao(comando, 'pendencia') <= 2
}

async function processarComandoPendencia(sock, msg, grupo) {
  if (!ehComandoPendencia(obterTexto(msg))) return false

  const idRemetente = jidNormalizedUser(obterId(msg))
  const cfg = EMPRESA_CONFIG[empresaAtual] || EMPRESA_CONFIG.SEU_DELIVERY
  let nomeGrupo = mesmoJid(grupo, grupos.g1) ? cfg.g1Nome : cfg.g2Nome
  let ehAdminNoGrupo = false

  try {
    const meta = await sock.groupMetadata(grupo)
    nomeGrupo = meta?.subject || nomeGrupo
    ehAdminNoGrupo = (meta?.participants || [])
      .filter(p => p.admin === 'admin' || p.admin === 'superadmin')
      .some(p => jidNormalizedUser(p.id) === idRemetente)
  } catch (e) {
    // Se a consulta falhar, usa a lista cacheada para o grupo de entregadores.
    if (mesmoJid(grupo, grupos.g1)) {
      ehAdminNoGrupo = Array.isArray(estado.g1Admins) && estado.g1Admins.includes(idRemetente)
    }
    console.log('Não foi possível consultar administradores do grupo para Pendência:', e.message)
  }

  // Uma palavra parecida escrita por não-ADM não deve virar uma solicitação de entrega.
  if (!ehAdminNoGrupo) return true

  const chaveEmpresaPendencia = empresaDoGrupo(grupo) || empresaAtual
  const estadoPendencia = empresas[chaveEmpresaPendencia]?.estado || estado
  // Pendência é enviada exclusivamente a quem aparece ONLINE na lista desta empresa.
  const destinatarios = [...new Set((estadoPendencia.online || [])
    .map(p => jidNormalizedUser(p?.id || p?.phoneNumber || p || ''))
    .filter(id => id && (id.endsWith('@s.whatsapp.net') || id.endsWith('@lid'))))]
  const mensagem = 'Entrega pendente'
  let enviados = 0

  for (const destinatario of destinatarios) {
    try {
      await sock.sendMessage(destinatario, { text: mensagem })
      enviados++
    } catch (e) {
      console.log(`Erro ao enviar aviso de pendência para ${destinatario}:`, e.message)
    }
  }

  console.log(`PENDÊNCIA | ${nomeGrupo} | avisos enviados ${enviados}/${destinatarios.length}`)
  return true
}

/* =====================================
   RELATÓRIOS PRIVADOS DE ENTREGAS
===================================== */

const conversasRelatorio = new Map()
const conversasOnlinePeriodo = new Map()
const conversasEntregasIndividuais = new Map()
const conversasMapeamentoBairroAntigo = new Map()
const conversasTabelaPrecosBairros = new Map()
const historicoNegacoesAcesso = new Map()

async function ehADMEmAlgumaEmpresa(sock, id) {
  const usuario = jidNormalizedUser(id || '')
  if (!usuario) return false
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const dados = empresas[chave]
    const grupoADM = dados?.grupos?.g1
    if (grupoADM) {
      try {
        const meta = await sock.groupMetadata(grupoADM)
        const admins = (meta?.participants || [])
          .filter(p => p.admin === 'admin' || p.admin === 'superadmin')
          .map(p => jidNormalizedUser(p.id)).filter(Boolean)
        dados.estado.g1Admins = admins
        if (admins.includes(usuario)) return true
      } catch {}
    }
    if ((dados?.estado?.g1Admins || []).map(x => jidNormalizedUser(x)).includes(usuario)) return true
  }
  return false
}

function inicioDoPeriodoRelatorio(periodo, agora = new Date()) {
  const inicioHoje = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
  if (periodo === 'hoje') return inicioHoje.getTime()
  const diaSemana = (inicioHoje.getDay() + 6) % 7 // segunda-feira = 0
  const inicioSemana = new Date(inicioHoje)
  inicioSemana.setDate(inicioSemana.getDate() - diaSemana)
  if (periodo === 'essa semana') return inicioSemana.getTime()
  if (periodo === 'semana passada') {
    inicioSemana.setDate(inicioSemana.getDate() - 7)
    return inicioSemana.getTime()
  }
  if (periodo === 'esse mês') return new Date(agora.getFullYear(), agora.getMonth(), 1).getTime()
  if (periodo === 'mês passado') return new Date(agora.getFullYear(), agora.getMonth() - 1, 1).getTime()
  if (periodo === 'últimas 4 semanas') {
    const inicio = new Date(agora)
    inicio.setDate(inicio.getDate() - 28)
    return inicio.getTime()
  }
  return inicioHoje.getTime()
}

function fimDoPeriodoRelatorio(periodo, agora = new Date()) {
  if (periodo === 'mês passado') return new Date(agora.getFullYear(), agora.getMonth(), 1).getTime() - 1
  if (periodo !== 'semana passada') return agora.getTime()
  const hoje = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
  const diaSemana = (hoje.getDay() + 6) % 7
  const inicioSemanaAtual = new Date(hoje)
  inicioSemanaAtual.setDate(inicioSemanaAtual.getDate() - diaSemana)
  return inicioSemanaAtual.getTime() - 1
}

function chaveEntregadorRelatorio(id, nome = '') {
  const valor = String(id || '').trim()
  if (valor.includes('@')) return jidNormalizedUser(valor).toLowerCase()
  const digitos = valor.replace(/\D/g, '')
  if (digitos.length >= 10) return digitos
  return String(nome || valor || 'Entregador').trim().toLocaleLowerCase('pt-BR')
}

function mesmoEntregadorRelatorio(registro, selecionado) {
  const idReg = String(registro?.entregadorId || '').trim()
  const idAlvo = String(selecionado?.id || '').trim()
  if (idReg.includes('@') && idAlvo.includes('@')) return jidNormalizedUser(idReg) === jidNormalizedUser(idAlvo)
  return chaveEntregadorRelatorio(idReg, registro?.entregadorNome) === chaveEntregadorRelatorio(idAlvo, selecionado?.nome)
}

function coletarRegistrosRelatorio(periodo, agora = new Date()) {
  const inicio = inicioDoPeriodoRelatorio(periodo, agora)
  const fim = fimDoPeriodoRelatorio(periodo, agora)
  const registros = []
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const st = empresas[chave]?.estado || {}
    for (const reg of (st.historicoEntregas || [])) {
      const instante = Number(reg.concluidaEm || 0)
      if (!instante || instante < inicio || instante > fim) continue
      registros.push({ ...reg, instante, empresaChave: chave })
    }
  }
  return registros
}

function gerarTextoRelatorioIndividual(entregadorId, entregadorNome, periodo) {
  const alvo = String(entregadorId || entregadorNome || '')
  const alvoEhJid = alvo.includes('@')
  const registros = coletarRegistrosRelatorio(periodo)
    .filter(reg => mesmoEntregadorRelatorio(reg, { id: alvo, nome: entregadorNome }))
  const total = registros.reduce((soma, reg) => soma + Math.max(1, Number(reg.quantidade) || 1), 0)
  const totalFinalizadas = registros.reduce((soma, reg) => soma + Math.max(0, Number(reg.finalizadasQuantidade ?? (reg.finalizadaEm ? 1 : 0)) || 0), 0)
  const porEmpresa = new Map()
  const porDia = new Map()
  for (const reg of registros) {
    const qtd = Math.max(1, Number(reg.quantidade) || 1)
    const empresa = String(reg.empresaNome || 'Empresa').trim()
    porEmpresa.set(empresa, (porEmpresa.get(empresa) || 0) + qtd)
    const dia = String(reg.data || new Date(reg.instante).toISOString().slice(0, 10))
    porDia.set(dia, (porDia.get(dia) || 0) + qtd)
  }
  const empresasTexto = [...porEmpresa.entries()]
    .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0], 'pt-BR'))
    .map(([nome, qtd]) => `• ${nome}: ${qtd}`)
  const diasTexto = [...porDia.entries()]
    .sort((a, b) => a[0].localeCompare(b[0]))
    .map(([dia, qtd]) => `• ${dia.split('-').reverse().join('/')}: ${qtd}`)
  return `📊 *RELATÓRIO INDIVIDUAL DE ENTREGAS*\n\nEntregador: *${entregadorNome}*\nPeríodo: *${periodo.toLocaleUpperCase('pt-BR')}*\n\n🛵 *Volume total: ${total} entrega(s)*\n✅ *Entregas finalizadas: ${totalFinalizadas}*\n\n🏢 *Por empresa*\n${empresasTexto.join('\n') || 'Nenhuma entrega registrada.'}\n\n📅 *Por dia*\n${diasTexto.join('\n') || 'Nenhuma entrega registrada.'}`
}

function dentroPeriodo(ts, periodo, agora = new Date()) {
  const d = new Date(Number(ts)); if (Number.isNaN(d.getTime())) return false
  const hoje = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
  let inicio, fim = new Date(hoje.getTime() + 24*60*60*1000)
  if (periodo === 'hoje') inicio = hoje
  else if (periodo === 'essa semana') { inicio = new Date(hoje); inicio.setDate(inicio.getDate() - ((inicio.getDay()+6)%7)); fim = new Date(inicio); fim.setDate(fim.getDate()+7) }
  else if (periodo === 'semana passada') { inicio = new Date(hoje); inicio.setDate(inicio.getDate() - ((inicio.getDay()+6)%7) - 7); fim = new Date(inicio); fim.setDate(fim.getDate()+7) }
  else if (periodo === 'esse mês') { inicio = new Date(hoje.getFullYear(),hoje.getMonth(),1); fim = new Date(hoje.getFullYear(),hoje.getMonth()+1,1) }
  else if (periodo === 'mês passado') { inicio = new Date(hoje.getFullYear(),hoje.getMonth()-1,1); fim = new Date(hoje.getFullYear(),hoje.getMonth(),1) }
  else { inicio = new Date(hoje); inicio.setDate(inicio.getDate()-28); fim = new Date(hoje.getTime()+24*60*60*1000) }
  return d >= inicio && d < fim
}

function gerarTextoRelatorio(tipo, periodo) {
  // A referência atual é sincronizada antes de somar os dados das duas operações.
  if (empresas[empresaAtual]) {
    empresas[empresaAtual].estado = estado
    empresas[empresaAtual].grupos = grupos
  }
  const chaveNome = tipo === 'empresas' ? 'empresaNome' : 'entregadorNome'
  const totais = new Map()
  let totalGeral = 0
  // Empresas usam o histórico de solicitações; entregadores usam o histórico de aceites.
  // São eventos diferentes: assim o relatório da empresa não fica vazio só porque
  // ainda não há conclusão/aceite registrado para o período.
  const registrosBase = tipo === 'empresas' ? coletarSolicitacoesRelatorio(periodo) : coletarRegistrosRelatorio(periodo)
  for (const reg of registrosBase) {
    const nome = String(reg[chaveNome] || (tipo === 'empresas' ? 'Empresa' : 'Entregador')).trim()
    const id = tipo === 'entregadores' ? chaveEntregadorRelatorio(reg.entregadorId || nome, nome) : nome.toLocaleLowerCase('pt-BR')
    const quantidade = Math.max(1, Number(reg.quantidade) || 1)
    const item = totais.get(id) || { nome, id, quantidade: 0 }
    item.quantidade += quantidade
    totais.set(id, item)
    totalGeral += quantidade
  }
  const ranking = [...totais.values()].sort((a, b) => b.quantidade - a.quantidade || a.nome.localeCompare(b.nome, 'pt-BR'))
  const rotulo = tipo === 'empresas' ? 'EMPRESAS — ENTREGAS ATRIBUÍDAS/REALIZADAS' : 'ENTREGADORES — ENTREGAS ACEITAS'
  const periodoBonito = periodo.toLocaleUpperCase('pt-BR')
  const linhas = ranking.length
    ? ranking.map((item, i) => `${i + 1}. ${item.nome} — ${item.quantidade}`).join('\n')
    : 'Nenhuma entrega registrada neste período.'
  const totalParticipantes = ranking.length
  return `📊 *RANKING COMPLETO DE ENTREGAS*
${rotulo}
Período: *${periodoBonito}*
Participantes no ranking: *${totalParticipantes}*

${linhas}

*Total geral: ${totalGeral}*`
}

function gerarRelatorioVolumeDiario(periodo, agora = new Date()) {
  const inicio = new Date(inicioDoPeriodoRelatorio(periodo, agora))
  const fim = new Date(fimDoPeriodoRelatorio(periodo, agora))
  const totais = new Map()
  for (const reg of coletarRegistrosRelatorio(periodo, agora)) {
    const dia = new Date(reg.instante)
    const chave = `${dia.getFullYear()}-${String(dia.getMonth()+1).padStart(2,'0')}-${String(dia.getDate()).padStart(2,'0')}`
    totais.set(chave, (totais.get(chave) || 0) + Math.max(1, Number(reg.quantidade) || 1))
  }
  const linhas = []
  const cursor = new Date(inicio.getFullYear(), inicio.getMonth(), inicio.getDate())
  const ultimo = new Date(fim.getFullYear(), fim.getMonth(), fim.getDate())
  let totalGeral = 0
  while (cursor <= ultimo) {
    const chave = `${cursor.getFullYear()}-${String(cursor.getMonth()+1).padStart(2,'0')}-${String(cursor.getDate()).padStart(2,'0')}`
    const quantidade = totais.get(chave) || 0
    totalGeral += quantidade
    linhas.push({ data: chave, nome: chave.split('-').reverse().join('/'), quantidade })
    cursor.setDate(cursor.getDate() + 1)
  }
  const inicioFmt = inicio.toLocaleDateString('pt-BR')
  const fimFmt = fim.toLocaleDateString('pt-BR')
  const texto = `📊 *VOLUME DIÁRIO DE ENTREGAS*\nPeríodo: *${periodo.toLocaleUpperCase('pt-BR')}*\nDe ${inicioFmt} até ${fimFmt}\n\n${linhas.map((x,i) => `${i+1}. ${x.nome} — ${x.quantidade} entrega${x.quantidade===1?'':'s'}`).join('\n')}\n\n*Total geral: ${totalGeral}*`
  return { texto, linhas: linhas.map((x,i) => ({ nome:x.nome, valor:x.quantidade, posicao:i+1 })) }
}

// Evita abrir vários Chromiums simultaneamente no Android/Termux, onde isso pode
// encerrar o processo e causar TargetCloseError. A fila libera mesmo quando há erro.
let filaRenderizacaoHTML = Promise.resolve();
async function executarRenderizacaoHTMLSequencial(tarefa) {
  const anterior = filaRenderizacaoHTML;
  let liberar;
  filaRenderizacaoHTML = new Promise(resolve => { liberar = resolve; });
  await anterior.catch(() => {});
  try { return await tarefa(); }
  finally { liberar(); }
}

// Mantém uma única instância do Chromium para evitar encerramentos/reaberturas
// repetidas no Termux. Se o processo morrer, limpa a referência e tenta recriar.
let browserHTMLCompartilhado = null;
async function abrirPaginaHTML(puppeteer, executavel) {
  let ultimoErro;
  for (let tentativa = 1; tentativa <= 2; tentativa++) {
    try {
      if (!browserHTMLCompartilhado || !browserHTMLCompartilhado.isConnected()) {
        browserHTMLCompartilhado = await puppeteer.launch({
          executablePath: executavel,
          headless: true,
          args: ['--no-sandbox','--disable-gpu','--disable-dev-shm-usage','--disable-background-networking','--disable-extensions','--disable-crash-reporter'],
          timeout: 60000,
          protocolTimeout: 120000
        });
        browserHTMLCompartilhado.on('disconnected', () => { browserHTMLCompartilhado = null; });
      }
      const browser = browserHTMLCompartilhado;
      const page = await browser.newPage();
      return { browser, page };
    } catch (erro) {
      ultimoErro = erro;
      const antigo = browserHTMLCompartilhado;
      browserHTMLCompartilhado = null;
      try { if (antigo) await antigo.close(); } catch (_) {}
      if (tentativa < 2) await new Promise(resolve => setTimeout(resolve, 1200));
    }
  }
  throw new Error('Chromium encerrou ao abrir a página HTML, mesmo após 2 tentativas: ' + (ultimoErro?.message || ultimoErro));
}

// Renderização leve de relatórios PNG em JavaScript, sem navegador externo.
function criarTabelaCRC32() {
  const tabela = new Uint32Array(256);
  for (let n=0; n<256; n++) { let c=n; for (let k=0; k<8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1); tabela[n]=c>>>0; }
  return tabela;
}
function criarGraficoBarrasPNGInternoNativo(titulo, subtitulo, linhas, formatoValor = v => String(v), opcoes = {}) {
  // PNG gerado exclusivamente com módulos nativos do Node (zlib/Buffer): sem browser, Java ou dependências extras.
  const zlib = require('zlib');
  const W=1100, margin=32, rowH=78, headerH=178, tableHeadH=40, footerH=58;
  const items=Array.isArray(linhas)?linhas:[];
  const H=Math.max(360,headerH+tableHeadH+Math.max(1,items.length)*rowH+footerH);
  const pixels=Buffer.alloc(W*H*4,255);
  const colors={white:[255,255,255],dark:[25,49,63],muted:[83,96,109],green:[22,101,85],accent:[23,145,112],head:[220,235,229],row:[243,247,245],barbg:[226,233,230],footer:[237,244,240],value:[35,63,75],grid:[215,224,220]};
  const rect=(x,y,w,h,c)=>{x=Math.max(0,Math.floor(x));y=Math.max(0,Math.floor(y));w=Math.min(W-x,Math.ceil(w));h=Math.min(H-y,Math.ceil(h));const a=Array.isArray(c)?c:colors[c]||colors.dark;for(let yy=y;yy<y+h;yy++){let p=(yy*W+x)*4;for(let xx=0;xx<w;xx++,p+=4){pixels[p]=a[0];pixels[p+1]=a[1];pixels[p+2]=a[2];pixels[p+3]=255;}}};
  // Atlas rasterizado a partir dos arquivos Open Sans TrueType incluídos no ZIP.
  // Não requer módulos npm no servidor; mantém antialiasing em tons de cinza.
  const openSansAtlas = require('./opensans-atlas.json');
  const text=(value,x,y,scale,c,maxWidth=0)=>{
    let s=String(value??'');
    const col=Array.isArray(c)?c:(colors[c]||colors.dark);
    const weight=(scale===4 || /ENTREGADOR|VOLUME|TOTAL|CHEGO DELIVERY|RELATORIO GERADO/.test(s))?'b':'r';
    const glyphs=openSansAtlas[String(scale)+weight] || openSansAtlas[String(scale)+'r'];
    let maxW=maxWidth>0?maxWidth:W-x-4;
    // Recorta o texto sem ultrapassar a área disponível.
    let chars=Array.from(s), width=chars.reduce((n,ch)=>n+(glyphs[ch]||glyphs['?']).a,0);
    while(chars.length>1 && width>maxW){ chars.pop(); width=chars.reduce((n,ch)=>n+(glyphs[ch]||glyphs['?']).a,0); }
    if(chars.length<Array.from(s).length && chars.length>0) chars[chars.length-1]='…';
    let xx=x;
    for(const ch of chars){
      const g=glyphs[ch]||glyphs['?']; const mask=Buffer.from(g.m,'base64');
      for(let gy=0;gy<g.h;gy++) for(let gx=0;gx<g.w;gx++){
        const a=mask[gy*g.w+gx]; if(!a) continue;
        const px=Math.floor(xx+g.x+gx), py=Math.floor(y+g.y+gy);
        if(px<0||px>=W||py<0||py>=H) continue;
        const p=(py*W+px)*4, inv=255-a;
        pixels[p]=Math.round((col[0]*a+pixels[p]*inv)/255);
        pixels[p+1]=Math.round((col[1]*a+pixels[p+1]*inv)/255);
        pixels[p+2]=Math.round((col[2]*a+pixels[p+2]*inv)/255); pixels[p+3]=255;
      }
      xx+=g.a;
    }
  };
  const chunk=(type,data)=>{const t=Buffer.from(type),len=Buffer.alloc(4);len.writeUInt32BE(data.length);const crcbuf=Buffer.concat([t,data]);let crc=0xffffffff;for(const b of crcbuf){crc^=b;for(let k=0;k<8;k++)crc=(crc&1)?(0xedb88320^(crc>>>1)):(crc>>>1);}const cb=Buffer.alloc(4);cb.writeUInt32BE((crc^0xffffffff)>>>0);return Buffer.concat([len,t,data,cb]);};
  rect(0,0,W,H,'white');rect(0,0,W,16,'green');text(titulo,margin,42,4,'dark',W-2*margin);text(subtitulo,margin,91,3,'muted',W-2*margin);text('CHEGO DELIVERY',margin,140,2,'accent');
  const ocultarVolume = opcoes?.ocultarVolume === true;
  const layoutTaxas = opcoes?.taxasLayout === true;
  const tableY=headerH;
  if (layoutTaxas) {
    // Colunas alinhadas como uma planilha: VALOR fica em penúltimo e STATUS por último.
    const cols=[{key:'posicao',label:'#',x:margin+8,w:38},{key:'nome',label:'ENTREGADOR',x:margin+52,w:300},{key:'entregas',label:'ENTREGAS',x:margin+365,w:100},{key:'desconto',label:'DESCONTO',x:margin+470,w:112},{key:'valor',label:'VALOR',x:margin+590,w:175},{key:'status',label:'STATUS',x:margin+785,w:185}];
    rect(margin,tableY,W-2*margin,tableHeadH,'head');
    for(const c of cols) text(c.label,c.x,tableY+12,2,'dark',c.w-8);
    for(let i=0;i<Math.max(1,items.length);i++){
      const item=items[i]||{nome:'Sem registros',entregas:0,desconto:0,status:'—',valor:'R$ 0,00'};
      const y=tableY+tableHeadH+i*rowH;
      rect(margin,y,W-2*margin,rowH,i%2?'white':'row'); rect(margin,y,W-2*margin,1,'grid');
      const vals=[String(item.posicao||i+1),String(item.nome||'Sem nome'),String(item.entregas??0),`${Number(item.desconto)||0}%`,String(item.valor??'R$ 0,00'),String(item.status||'—')];
      cols.forEach((c,j)=>text(vals[j],c.x,y+25,j===4?3:2,j===4?'value':'dark',c.w-8));
      rect(margin,y+rowH-1,W-2*margin,1,'grid');
    }
  } else {
    const nameX=margin,barX=ocultarVolume?0:430,barW=ocultarVolume?0:390,valueX=ocultarVolume?850:866;rect(margin,tableY,W-2*margin,tableHeadH,'head');text('ENTREGADOR',nameX+10,tableY+12,2,'dark',(ocultarVolume?valueX:barX)-nameX-30);if(!ocultarVolume)text('VOLUME',barX,tableY+12,2,'dark',barW);text('TOTAL',valueX,tableY+12,2,'dark',155);
    const max=Math.max(1,...items.map(x=>Number(x.valor)||0));for(let i=0;i<Math.max(1,items.length);i++){const item=items[i]||{nome:'Sem registros',valor:0};const y=tableY+tableHeadH+i*rowH;rect(margin,y,W-2*margin,rowH,i%2?'white':'row');rect(margin,y,W-2*margin,1,'grid');text(`${item.posicao||i+1}. ${item.nome||'Sem nome'}`,nameX+10,y+24,2,'dark',(ocultarVolume?valueX:barX)-nameX-38);if(!ocultarVolume){rect(barX,y+28,barW,20,'barbg');const v=Number(item.valor)||0;if(v>0)rect(barX,y+28,Math.max(3,Math.round(barW*v/max)),20,'accent');}let shown='';try{shown=String(formatoValor(item.valor));}catch(_){shown=String(item.valor??'');}text(shown,valueX,y+25,2,'value',155);rect(margin,y+rowH-1,W-2*margin,1,'grid');}
  }
  const fy=H-footerH;rect(0,fy,W,footerH,'footer');text('CHEGO DELIVERY - RELATORIO GERADO AUTOMATICAMENTE',margin,fy+22,2,'muted',W-2*margin);
  const raw=Buffer.alloc(H*(W*4+1));for(let y=0;y<H;y++){const o=y*(W*4+1);raw[o]=0;pixels.copy(raw,o+1,y*W*4,(y+1)*W*4);}const ihdr=Buffer.alloc(13);ihdr.writeUInt32BE(W,0);ihdr.writeUInt32BE(H,4);ihdr[8]=8;ihdr[9]=6;ihdr[10]=0;ihdr[11]=0;ihdr[12]=0;return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),chunk('IHDR',ihdr),chunk('IDAT',zlib.deflateSync(raw)),chunk('IEND',Buffer.alloc(0))]);
}

async function criarGraficoBarrasPNGInterno(titulo, subtitulo, linhas, formatoValor = v => String(v), opcoes = {}) {
  return criarGraficoBarrasPNGInternoNativo(titulo, subtitulo, linhas, formatoValor, opcoes);
}

async function criarGraficoBarrasPNG(titulo, subtitulo, linhas, formatoValor = v => String(v)) {
  return executarRenderizacaoHTMLSequencial(() => criarGraficoBarrasPNGInterno(titulo, subtitulo, linhas, formatoValor));
}
async function enviarGraficosRanking(sock,jid,titulo,subtitulo,linhas,formatoValor,legendaExtra='') {
  if (!Array.isArray(linhas)) return false;
  const caption = [`📊 ${titulo}`, subtitulo, legendaExtra].filter(Boolean).join('\n');
  try {
    const imagem = await criarGraficoBarrasPNG(titulo,subtitulo,linhas,formatoValor);
    await sock.sendMessage(jid,{image:imagem,caption});
  } catch (erroImagem) {
    // O servidor não expõe logs ao usuário: enviar diagnóstico técnico no próprio privado.
    const erroDetalhado = String(erroImagem?.stack || erroImagem?.message || erroImagem || 'Erro desconhecido')
      .replace(/\u001b\[[0-9;]*m/g, '')
      .slice(0, 3500);
    console.error('Falha ao gerar/enviar PNG do relatório:', erroDetalhado);
    const diagnostico = `⚠️ *FALHA AO GERAR/ENVIAR IMAGEM DO RELATÓRIO*\n\nEtapa: geração PNG ou envio pelo WhatsApp\nData/hora: ${new Date().toISOString()}\n\n*Erro técnico:*\n${erroDetalhado}\n\nNenhum relatório em texto foi enviado como substituto. Envie esta mensagem para o suporte.`;
    try {
      // Em uso no privado, o destinatário do relatório recebe também o erro real.
      await sock.sendMessage(jid, { text: diagnostico });
    } catch (erroAviso) {
      console.error('Também falhou o envio do diagnóstico no WhatsApp:', erroAviso?.stack || erroAviso);
    }
    return true;
  }
  return true;
}

// ================= TAXAS SEMANAIS =================
function inicioSemanaTaxas(data = new Date()) {
  const d = new Date(data.getFullYear(), data.getMonth(), data.getDate());
  d.setDate(d.getDate() - ((d.getDay() + 6) % 7)); d.setHours(0,0,0,0); return d;
}
function chaveSemanaTaxas(data) { const d = data instanceof Date ? data : new Date(data); return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`; }
function faixaSemanaTaxas(chave) { const a = new Date(Number(chave.slice(0,4)), Number(chave.slice(5,7))-1, Number(chave.slice(8,10))); a.setHours(0,0,0,0); const b = new Date(a); b.setDate(b.getDate()+7); return {inicio:a.getTime(), fim:b.getTime()}; }
function prazoTaxas(chave) { const f=faixaSemanaTaxas(chave); const d=new Date(f.fim); d.setDate(d.getDate()+1); d.setHours(18,0,0,0); return d.getTime(); }
function coletarDadosTaxas(chave) {
  const faixa=faixaSemanaTaxas(chave), mapa=new Map(), vistos=new Set(), nomes=new Map();
  const guardarNome=(idOriginal,nomeOriginal)=>{
    const id=jidNormalizedUser(idOriginal||'');
    const nome=String(nomeOriginal||'').trim();
    // Nunca tratar JID, @id ou telefone como nome visível.
    if(!id||!nome||nome==='Entregador'||/^\d{8,}$/.test(nome)||/^@?\d{5,}(?:@.+)?$/.test(nome)||/@s\.whatsapp\.net$/i.test(nome)||nome===id||nome===id.split('@')[0]) return;
    const anterior=nomes.get(id);
    if(!anterior || anterior==='Entregador' || anterior===id.split('@')[0] || anterior===id) nomes.set(id,nome);
  };
  // Primeiro usa também o cadastro global principal do bot, que costuma guardar o nome real.
  for(const p of (estado.entregadores||[])) if(p && typeof p==='object') guardarNome(p.id||p.jid||p.numero||p.entregadorId,p.nome||p.name||p.pushName||p.entregadorNome);
  // Depois monta um cadastro global de nomes a partir de todas as empresas e sessões.
  for(const empresa of Object.keys(EMPRESA_CONFIG)) {
    const est=empresas[empresa]?.estado||{};
    for(const p of [...(est.entregadores||[]),...(est.online||[]),...(est.espera||[]),...(est.bloqueados||[]),...(est.bloqueadosSemana||[])]) {
      if(p && typeof p==='object') guardarNome(p.id||p.jid||p.numero||p.entregadorId,p.nome||p.name||p.pushName||p.entregadorNome);
    }
    for(const sessao of (est.sessoesOnline||[])) guardarNome(sessao.entregadorId,sessao.entregadorNome||sessao.nome);
    for(const e of (est.historicoEntregas||[])) guardarNome(e.entregadorId,e.entregadorNome||e.nomeEntregador);
  }
  for (const empresa of Object.keys(EMPRESA_CONFIG)) {
    const est=empresas[empresa]?.estado||{};
    for (const e of (est.historicoEntregas||[])) {
      const ts=Number(e.iniciadaEm||e.concluidaEm||e.finalizadaEm||0); if(!e.entregadorId||ts<faixa.inicio||ts>=faixa.fim) continue;
      const uniq=e.eventoMensagemId ? `msg:${e.eventoMensagemId}` : `${empresa}:${e.mensagemId||''}:${e.entregadorId}:${ts}:${e.fracaoAtual||''}`;
      if(vistos.has(uniq)) continue; vistos.add(uniq);
      const id=jidNormalizedUser(e.entregadorId); if(!id) continue;
      guardarNome(id,e.entregadorNome||e.nomeEntregador);
      const nome=nomes.get(id)||String(e.entregadorNome||e.nomeEntregador||'Entregador');
      const x=mapa.get(id)||{id,nome,entregas:0,diasFimSemana:new Set()};
      x.entregas += Math.max(1,Number(e.quantidade)||1);
      if((!x.nome||x.nome==='Entregador'||x.nome===id.split('@')[0]) && nome) x.nome=nome;
      const d=new Date(ts), dia=d.getDay(), h=d.getHours();
      if((dia===6||dia===0)&&((h>=10&&h<14)||(h>=18&&h<22))) x.diasFimSemana.add(dia);
      mapa.set(id,x);
    }
    for (const p of (est.entregadores||[])) {
      const id=jidNormalizedUser(p.id||p.jid||''); if(!id)continue;
      const nome=nomes.get(id)||String(p.nome||p.name||p.pushName||'Entregador');
      if(!mapa.has(id)) mapa.set(id,{id,nome,entregas:0,diasFimSemana:new Set()});
      else if((!mapa.get(id).nome||mapa.get(id).nome==='Entregador')&&nome) mapa.get(id).nome=nome;
    }
  }
  const agora=Date.now(), prazo=prazoTaxas(chave), atrasou=agora>=prazo;
  const estadoTaxas=empresas.CHEGO_DELIVERY?.estado?.taxasSemanais||{}; const registro=estadoTaxas[chave]||{};
  return [...mapa.values()].map(x=>{
    const pagamento=registro.pagos?.[x.id]; const pago=!!pagamento;
    const pagoNoPrazo=typeof pagamento==='number' && pagamento<=prazo;
    const descontoLiberado=x.entregas>=20&&(!atrasou||pagoNoPrazo);
    let desconto=0; if(descontoLiberado){ if(x.diasFimSemana.size>=1) desconto+=x.diasFimSemana.size>=2?20:10; desconto+=10; }
    const valorBase=x.entregas, valor=Math.round(valorBase*(1-desconto/100)*100)/100;
    return {...x,nome:nomes.get(x.id)||x.nome||'Entregador',desconto,pago,valor,valorBase,atrasou,prazo};
  }).sort((a,b)=>a.nome.localeCompare(b.nome,'pt-BR'));
}
function taxaAtrasadaDoEntregador(id, agora=Date.now()) {
  const usuario=jidNormalizedUser(id); if(!usuario)return false;
  const chaves=new Set();
  for(const empresa of Object.keys(EMPRESA_CONFIG)) for(const e of (empresas[empresa]?.estado?.historicoEntregas||[])) { const ts=Number(e.iniciadaEm||e.concluidaEm||0); if(jidNormalizedUser(e.entregadorId||'')===usuario&&ts) chaves.add(chaveSemanaTaxas(inicioSemanaTaxas(new Date(ts)))); }
  for(const chave of chaves){ if(agora>=prazoTaxas(chave)){ const pagos=empresas.CHEGO_DELIVERY?.estado?.taxasSemanais?.[chave]?.pagos||{}; if(!pagos[usuario]) return true; } }
  return false;
}
function atualizarBloqueiosTaxas() {
  // Bloqueio automático por taxas desativado a pedido do administrador.
  // Mantém o histórico/relatório de taxas, mas nunca bloqueia nem remove
  // entregadores das listas por causa de pagamento pendente.
  for (const empresa of Object.keys(EMPRESA_CONFIG)) {
    const est = empresas[empresa]?.estado
    if (!est) continue
    est.bloqueiosTaxas = []
  }
}

async function criarTabelaTaxasPNGInterno(linhas, chave) {
  // PNG gerado por PureImage: sem Puppeteer, Chromium ou Java.
  // Mantém todos os campos principais das taxas em cada linha do relatório.
  const semana = chave.split('-').reverse().join('/');
  const prazo = new Date(prazoTaxas(chave)).toLocaleString('pt-BR', {dateStyle:'short',timeStyle:'short'});
  const dados = (Array.isArray(linhas) ? linhas : []).map((r, i) => {
    const status = r.pago ? 'PAGO' : (taxaAtrasadaDoEntregador(r.id) ? 'BLOQUEADO' : 'PENDENTE');
    const nome = String(r.nome || 'NOME NÃO CADASTRADO');
    const valor = `R$ ${Number(r.valor || 0).toFixed(2).replace('.', ',')}`;
    return {posicao:i+1, nome:nome, entregas:Number(r.entregas)||0, desconto:Number(r.desconto)||0, status, valor};
  });
  return [await criarGraficoBarrasPNGInterno('TAXAS SEMANAIS', `SEMANA ${semana} | Prazo: ${prazo}`, dados, v => String(v), {taxasLayout:true,ocultarVolume:true})];
}

async function criarTabelaTaxasPNG(linhas, chave) {
  return executarRenderizacaoHTMLSequencial(() => criarTabelaTaxasPNGInterno(linhas, chave));
}

async function enviarTabelaTaxas(sock,jid,chave) {
  atualizarBloqueiosTaxas(); salvar(); const linhas=coletarDadosTaxas(chave);
  // Resolve os nomes no momento em que TAXAS gera a imagem, usando os contatos
  // e participantes dos grupos já conectados; não imprime o JID no lugar do nome.
  const nomesTaxas = new Map();
  const nomeTaxasValido = v => {
    const n=String(v||'').trim();
    if(!n || n==='Entregador' || /@/.test(n) || /^\+?\d[\d .()-]{6,}$/.test(n) || /^\d{5,}$/.test(n)) return false;
    return true;
  };
  const guardarNomeTaxas = (idOriginal,nomeOriginal) => {
    const id=jidNormalizedUser(idOriginal||''); const nome=String(nomeOriginal||'').trim();
    if(id && nomeTaxasValido(nome) && nome!==id && nome!==id.split('@')[0]) nomesTaxas.set(id,nome);
  };
  for(const [id,c] of Object.entries(sock.contacts||{})) guardarNomeTaxas(id,c?.name||c?.notify||c?.pushName);
  for(const empresa of Object.keys(EMPRESA_CONFIG)) {
    const g=empresas[empresa]?.grupos||{};
    for(const grupo of [g.g1,g.g2]) {
      if(!grupo) continue;
      try {
        const meta=await sock.groupMetadata(grupo);
        for(const p of (meta?.participants||[])) {
          const c=sock.contacts?.[p.id]||sock.contacts?.[jidNormalizedUser(p.id)]||{};
          const nome=c.name||c.notify||c.pushName||p.notify||p.name||p.verifiedName;
          guardarNomeTaxas(p.id,nome);
          if(p.phoneNumber) guardarNomeTaxas(p.phoneNumber,nome);
        }
      } catch(_) {}
    }
  }
  for(const linha of linhas) {
    const id=jidNormalizedUser(linha.id||'');
    const nome=nomesTaxas.get(id);
    if(nome) linha.nome=nome;
  }
  if(!linhas.length){await sock.sendMessage(jid,{text:`📊 Não há entregas registradas para a semana ${chave.split('-').reverse().join('/')}.`});return;}
  const legendaTaxas=`💰 TAXAS | Semana ${chave.split('-').reverse().join('/')}\nPrazo dos descontos: terça-feira às 18h. Para registrar pagamento: taxas pago @entregador.`;
  try {
    const imgs=await criarTabelaTaxasPNG(linhas,chave);
    for(const imagem of imgs) await sock.sendMessage(jid,{image:imagem,caption:legendaTaxas});
  } catch (erroImagem) {
    // Sem Chromium no servidor, não perde a informação das taxas: envia a tabela em texto.
    console.log('Tabela de taxas em imagem indisponível; enviando versão textual:', erroImagem?.message || erroImagem);
    const detalhe=linhas.map((r,i)=>`${i+1}. ${r.nome || 'NOME NÃO CADASTRADO'} | ${Number(r.entregas)||0} entregas | desconto ${Number(r.desconto)||0}% | R$ ${Number(r.valor||0).toFixed(2).replace('.',',')} | ${r.pago?'PAGO':(taxaAtrasadaDoEntregador(r.id)?'BLOQUEADO':'PENDENTE')}`).join('\n');
    await sock.sendMessage(jid,{text:`${legendaTaxas}\n\n${detalhe}`});
  }
}
function coletarSolicitacoesRelatorio(periodo, agora = new Date()) {
  const inicio = inicioDoPeriodoRelatorio(periodo, agora)
  const fim = fimDoPeriodoRelatorio(periodo, agora)
  const registros = []
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const est = empresas[chave]?.estado || {}
    for (const reg of (est.solicitacoesRelatorio || [])) {
      const instante = Number(reg.solicitadaEm || 0)
      if (!instante || instante < inicio || instante > fim) continue
      registros.push({ ...reg, instante, empresaChave: chave, quantidade: Math.max(1, Number(reg.quantidade) || 1) })
    }
  }
  return registros
}

function coletarRankingEntregasGrafico(tipo,periodo) {
  const campo=tipo==='empresas'?'empresaNome':'entregadorNome', mapa=new Map()
  const registrosBase = tipo === 'empresas' ? coletarSolicitacoesRelatorio(periodo) : coletarRegistrosRelatorio(periodo)
  for(const reg of registrosBase) {
    const nome=String(reg[campo]||(tipo==='empresas'?'Empresa':'Entregador')).trim()
    const id=tipo==='empresas'?nome.toLocaleLowerCase('pt-BR'):chaveEntregadorRelatorio(reg.entregadorId||nome,nome)
    const item=mapa.get(id)||{nome,valor:0};item.valor+=Math.max(1,Number(reg.quantidade)||1);mapa.set(id,item)
  }
  return [...mapa.values()].sort((a,b)=>b.valor-a.valor||a.nome.localeCompare(b.nome,'pt-BR')).map((x,i)=>({...x,posicao:i+1}))
}
function coletarRankingTempoMedio(agora=Date.now()) {
  const limite=agora-7*24*60*60*1000, mapa=new Map()
  for(const chave of Object.keys(EMPRESA_CONFIG))for(const reg of (empresas[chave]?.estado?.historicoEntregas||[])) {
    const inicio=Number(reg.iniciadaEm||0),fim=Number(reg.finalizadaEm||0),minutos=Number(reg.tempoMinutos)
    if(!inicio||!fim||fim<limite||fim>agora||!Number.isFinite(minutos)||minutos<0)continue
    const id=String(reg.entregadorId||reg.entregadorNome||'').trim();if(!id)continue
    const item=mapa.get(id)||{id,nome:String(reg.entregadorNome||'Entregador').trim(),somaMinutos:0,quantidade:0}
    item.somaMinutos+=minutos;item.quantidade++;mapa.set(id,item)
  }
  return [...mapa.values()].map(x=>({...x,media:x.quantidade?x.somaMinutos/x.quantidade:0})).sort((a,b)=>a.media-b.media||b.quantidade-a.quantidade||a.nome.localeCompare(b.nome,'pt-BR')).map((x,i)=>({...x,posicao:i+1,valor:x.media}))
}

// Envia relatórios/rankings completos, dividindo textos longos sem cortar posições.
async function enviarTextoCompleto(sock, jid, texto, limite = 3500) {
  const linhas = String(texto || '').split('\n')
  const partes = []
  let parte = ''
  for (const linha of linhas) {
    // Se uma única linha exceder o limite, divide essa linha em blocos sem perder conteúdo.
    if (linha.length > limite) {
      if (parte) { partes.push(parte); parte = '' }
      for (let i = 0; i < linha.length; i += limite) partes.push(linha.slice(i, i + limite))
      continue
    }
    const candidata = parte ? `${parte}\n${linha}` : linha
    if (candidata.length > limite) {
      if (parte) partes.push(parte)
      parte = linha
    } else {
      parte = candidata
    }
  }
  if (parte) partes.push(parte)
  if (!partes.length) partes.push('Relatório vazio.')
  for (let i = 0; i < partes.length; i++) {
    const cabecalho = partes.length > 1 ? `📄 *Continuação ${i + 1}/${partes.length}*\n\n` : ''
    await sock.sendMessage(jid, { text: cabecalho + partes[i] })
  }
  console.log(`RELATÓRIO COMPLETO ENVIADO | ${partes.length} mensagem(ns) | ${String(texto || '').split('\n').length} linhas`)
}

function gerarRankingTempoMedioEntregadores(agora = Date.now()) {
  const ranking = coletarRankingTempoMedio(agora)
  if (!ranking.length) return '⏱️ *RANKING DE TEMPO MÉDIO DE ENTREGA*\nPeríodo: *últimos 7 dias*\n\nAinda não há entregas finalizadas com os horários de INDO e conclusão registrados. O Bot começará a formar este ranking a partir desta atualização.'
  const linhas = ranking.map(item => {
    const minutos=Math.floor(item.media),segundos=Math.round((item.media-minutos)*60)
    const mediaTexto=segundos===60?`${minutos+1} min`:(segundos?`${minutos} min ${segundos} s`:`${minutos} min`)
    return `${item.posicao}. *${item.nome}* — média de *${mediaTexto}* (${item.quantidade} entregas)`
  }).join('\n')
  return `⏱️ *RANKING COMPLETO DE TEMPO MÉDIO DE ENTREGA*
Período: *últimos 7 dias*
Ordem: menor média para maior média
Entregadores no ranking: *${ranking.length}*

${linhas}

*Importante:* entram apenas entregas finalizadas com início e conclusão registrados.`
}


function gerarRelatorioEscalaFimDeSemana(agora = new Date()) {
  // Escala considera o sábado e domingo mais recentes e separa cada turno.
  const domingo = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate());
  domingo.setDate(domingo.getDate() - domingo.getDay());
  const sabado = new Date(domingo);
  sabado.setDate(sabado.getDate() - 1);
  const janelas = [
    { nome: '10:00–14:00', inicio: 10, fim: 14 },
    { nome: '18:00–22:00', inicio: 18, fim: 22 }
  ];
  const dias = [{ nome: 'SÁBADO', data: sabado }, { nome: 'DOMINGO', data: domingo }];
  const dataFmt = d => d.toLocaleDateString('pt-BR');
  let texto = `📊 *ESCALA DO FIM DE SEMANA*\nSábado ${dataFmt(sabado)} e domingo ${dataFmt(domingo)}\n`;
  for (const diaInfo of dias) {
    texto += `\n━━━━━━━━━━━━━━━━━━\n🗓️ *${diaInfo.nome} — ${dataFmt(diaInfo.data)}*\n`;
    for (const janela of janelas) {
      const ids = new Map();
      const inicioJanela = new Date(diaInfo.data.getFullYear(), diaInfo.data.getMonth(), diaInfo.data.getDate(), janela.inicio).getTime();
      const fimJanela = new Date(diaInfo.data.getFullYear(), diaInfo.data.getMonth(), diaInfo.data.getDate(), janela.fim).getTime();
      for (const chave of Object.keys(EMPRESA_CONFIG)) {
        const hist = empresas[chave]?.estado?.historicoEntregas || [];
        for (const item of hist) {
          if (!item?.entregadorId) continue;
          // Considera quando a entrega começou (INDO/aceite); fallback para conclusão em registros antigos.
          const ts = Number(item.iniciadaEm || item.concluidaEm || item.finalizadaEm || 0);
          if (ts < inicioJanela || ts >= fimJanela) continue;
          const id = jidNormalizedUser(item.entregadorId);
          if (id) ids.set(id, String(item.entregadorNome || 'Entregador').trim());
        }
      }
      const nomes = [...ids.values()].sort((a,b) => a.localeCompare(b, 'pt-BR'));
      texto += `\n⏰ *${janela.nome}*\n`;
      texto += nomes.length ? nomes.map((nome,i) => `${i+1}. ${nome}`).join('\n') + '\n' : 'Nenhum entregador com entrega iniciada neste horário.\n';
    }
  }
  texto += '\nℹ️ A escala lista somente entregadores com entrega registrada dentro de cada turno; quem rodou apenas fora desses horários não aparece.';
  return texto;
}

function normalizarNomeEscala(nome) {
  return String(nome || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '')
    .replace(/[^a-zA-Z0-9 ]/g, ' ').replace(/\b(entregas?|motoboy|motoboys)\b/gi, ' ')
    .replace(/\s+/g, ' ').trim().toLowerCase();
}

// A rotação usa somente quem consta na escala efetivamente salva para o fim de semana anterior.

function obterDataHoraFortalezaEscala(agora = new Date()) {
  const partes = new Intl.DateTimeFormat('en-CA', {
    timeZone: 'America/Fortaleza', year: 'numeric', month: '2-digit', day: '2-digit',
    hour: '2-digit', minute: '2-digit', second: '2-digit', hourCycle: 'h23'
  }).formatToParts(agora).reduce((o, p) => (o[p.type] = p.value, o), {});
  // Cria uma data com os componentes do relógio de Patos-PB, sem depender do fuso do container.
  return new Date(Number(partes.year), Number(partes.month) - 1, Number(partes.day),
    Number(partes.hour), Number(partes.minute), Number(partes.second), agora.getMilliseconds());
}

function chaveSabadoEscala(data) {
  const d = new Date(data.getFullYear(), data.getMonth(), data.getDate());
  const dia = d.getDay();
  if (dia === 0) d.setDate(d.getDate() - 1); // domingo pertence ao sábado anterior
  else if (dia !== 6) d.setDate(d.getDate() + ((6 - dia + 7) % 7));
  return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`;
}

function sabadoAnteriorEscala(chaveSabado) {
  const [ano, mes, dia] = String(chaveSabado).split('-').map(Number);
  const d = new Date(ano, mes - 1, dia);
  d.setDate(d.getDate() - 7);
  return `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`;
}

async function registrarEscalaManual(sock, msg, grupo) {
  const texto = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim();
  const mencoes = obterMarcados(msg).map(id => jidNormalizedUser(id)).filter(Boolean);
  if (grupo !== grupos.g1 || !texto.includes('escalado') || mencoes.length === 0) return false;
  if (!(await ehADM(sock, msg))) return false;

  const chaveEmpresa = 'CHEGO_DELIVERY';
  const estadoEmpresa = empresas[chaveEmpresa]?.estado;
  if (!estadoEmpresa) return false;
  if (!Array.isArray(estadoEmpresa.escalasManuais)) estadoEmpresa.escalasManuais = [];

  let meta = null;
  try { meta = await sock.groupMetadata(grupo); } catch (_) {}
  const participantes = meta?.participants || [];
  const agora = obterDataHoraFortalezaEscala(new Date(Number(msg.messageTimestamp || 0) ? Number(msg.messageTimestamp) * 1000 : Date.now()));
  const fimSemanaSabado = chaveSabadoEscala(agora);
  const registrados = [];

  for (const id of [...new Set(mencoes)]) {
    const participante = participantes.find(p => jidNormalizedUser(p.id) === id);
    const contato = sock.contacts?.[id] || sock.contacts?.[participante?.id] || {};
    const nome = String(contato.name || contato.notify || contato.pushName || participante?.notify || participante?.name || id.split('@')[0]).trim();
    const registro = { id, nome, fimSemanaSabado, registradoEm: Date.now(), admId: jidNormalizedUser(obterId(msg)) };
    const existente = estadoEmpresa.escalasManuais.findIndex(x => jidNormalizedUser(x.id) === id && x.fimSemanaSabado === fimSemanaSabado);
    if (existente >= 0) estadoEmpresa.escalasManuais[existente] = registro;
    else estadoEmpresa.escalasManuais.push(registro);
    registrados.push(nome);
  }

  // Mantém apenas 12 semanas de histórico para não crescer indefinidamente.
  const limite = Date.now() - 84 * 24 * 60 * 60 * 1000;
  estadoEmpresa.escalasManuais = estadoEmpresa.escalasManuais.filter(x => Number(x.registradoEm || 0) >= limite);
  empresas[chaveEmpresa].estado = estadoEmpresa;
  salvar();
  await sock.sendMessage(grupo, { text: `✅ Escala manual registrada: ${registrados.map(n => `*${n}*`).join(', ')}. Esses entregadores serão considerados na próxima verificação de repetição de escala.` });
  return true;
}

function nomeDaMencaoEscala(id, participantes, sock) {
  const jid = jidNormalizedUser(id);
  const participante = (participantes || []).find(p =>
    jidNormalizedUser(p?.id) === jid || jidNormalizedUser(p?.phoneNumber) === jid
  );
  const contato = sock.contacts?.[jid] || sock.contacts?.[participante?.id] || {};
  return String(
    contato.name || contato.notify || contato.pushName || participante?.notify ||
    participante?.name || participante?.verifiedName ||
    (jid && !jid.endsWith('@lid') ? jid.split('@')[0] : 'Entregador')
  ).trim();
}

async function processarComandoPoliticaEscala(sock, msg, grupo, textoNormalizado) {
  if (grupo !== grupos.g1) return false;
  const comando = String(textoNormalizado || '').replace(/[.!?]+$/g, '').trim();
  const acao = /\bjustificado(?:\s+(sabado|domingo))?$/.exec(comando);
  const folguista = /\bfolguista$/.test(comando);
  const cafeComLeite = /\bcafe\s+com\s+leite$/.test(comando);
  const semEscala = /\bsem\s+escala$/.test(comando) || cafeComLeite;
  if (!acao && !folguista && !semEscala) return false;
  if (!(await ehADM(sock, msg))) {
    await sock.sendMessage(grupo, { text: '⛔ Somente ADM pode alterar as regras da escala.' });
    return true;
  }

  const ids = [...new Set(obterMarcados(msg).map(id => jidNormalizedUser(id)).filter(Boolean))];
  if (!ids.length) {
    await sock.sendMessage(grupo, { text: '⚠️ Marque o entregador na mensagem para registrar o comando.' });
    return true;
  }

  const estadoEmpresa = empresas.CHEGO_DELIVERY?.estado;
  if (!estadoEmpresa) return true;
  if (!Array.isArray(estadoEmpresa.folguistasEscala)) estadoEmpresa.folguistasEscala = [];
  if (!Array.isArray(estadoEmpresa.semEscalaPermanente)) estadoEmpresa.semEscalaPermanente = [];
  if (!Array.isArray(estadoEmpresa.justificativasEscala)) estadoEmpresa.justificativasEscala = [];

  let participantes = [];
  try { participantes = (await sock.groupMetadata(grupo))?.participants || []; } catch (_) {}
  const agora = obterDataHoraFortalezaEscala(new Date(Number(msg.messageTimestamp || 0) ? Number(msg.messageTimestamp) * 1000 : Date.now()));
  const fimSemanaSabado = chaveSabadoEscala(agora);
  const nomes = [];

  for (const id of ids) {
    const nome = nomeDaMencaoEscala(id, participantes, sock);
    const pessoa = { id, nome, atualizadoEm: Date.now(), atualizadoPor: jidNormalizedUser(obterId(msg)) };
    const removerPorIdOuNome = lista => lista.filter(p =>
      jidNormalizedUser(p?.id) !== id && normalizarNomeEscala(p?.nome) !== normalizarNomeEscala(nome)
    );

    // Folguista e café com leite são estados mutuamente exclusivos: o último comando ADM vence.
    if (folguista) {
      estadoEmpresa.semEscalaPermanente = removerPorIdOuNome(estadoEmpresa.semEscalaPermanente);
      if (!estadoEmpresa.folguistasEscala.some(p => jidNormalizedUser(p?.id) === id || normalizarNomeEscala(p?.nome) === normalizarNomeEscala(nome))) {
        estadoEmpresa.folguistasEscala.push(pessoa);
      }
      nomes.push(`*${nome}* — folguista permanente na escala`);
    } else if (semEscala) {
      estadoEmpresa.folguistasEscala = removerPorIdOuNome(estadoEmpresa.folguistasEscala);
      if (!estadoEmpresa.semEscalaPermanente.some(p => jidNormalizedUser(p?.id) === id || normalizarNomeEscala(p?.nome) === normalizarNomeEscala(nome))) {
        estadoEmpresa.semEscalaPermanente.push(pessoa);
      }
      nomes.push(cafeComLeite
        ? `*${nome}* — café com leite; nunca entra na escala de fim de semana`
        : `*${nome}* — nunca entra na escala`);
    } else {
      const dias = acao[1] ? [acao[1] === 'sabado' ? 'sábado' : 'domingo'] : ['sábado', 'domingo'];
      for (const dia of dias) {
        estadoEmpresa.justificativasEscala = estadoEmpresa.justificativasEscala.filter(p =>
          !(jidNormalizedUser(p?.id) === id && p?.fimSemanaSabado === fimSemanaSabado && p?.dia === dia)
        );
        estadoEmpresa.justificativasEscala.push({ ...pessoa, fimSemanaSabado, dia, registradoEm: Date.now() });
      }
      nomes.push(`*${nome}* — ausência justificada ${dias.length === 2 ? 'no sábado e no domingo' : `no ${dias[0]}`}`);
    }
  }

  // Limita o histórico de justificativas a 12 semanas; folguistas e bloqueios permanentes não expiram.
  const limite = Date.now() - 84 * 24 * 60 * 60 * 1000;
  estadoEmpresa.justificativasEscala = estadoEmpresa.justificativasEscala.filter(p => Number(p.registradoEm || 0) >= limite);
  empresas.CHEGO_DELIVERY.estado = estadoEmpresa;
  salvar();

  const avisoJustificativa = acao
    ? '\n\nA justificativa impede a punição somente no(s) dia(s) informado(s). A apuração automática das faltas acontece na segunda-feira às 06h.'
    : '';
  await sock.sendMessage(grupo, { text: `✅ *Configuração de escala atualizada*\n${nomes.join('\n')}${avisoJustificativa}` });
  return true;
}

function proximoFimDeSemana(agora = new Date()) {
  const sabado = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate());
  const dias = (6 - sabado.getDay() + 7) % 7;
  sabado.setDate(sabado.getDate() + (dias === 0 ? 7 : dias));
  const domingo = new Date(sabado); domingo.setDate(domingo.getDate() + 1);
  const chave = d => `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`;
  const fmt = d => d.toLocaleDateString('pt-BR');
  return { sabado, domingo, chave: chave(sabado), sabadoTexto: fmt(sabado), domingoTexto: fmt(domingo) };
}

function deveIncluirNaEscalaAlternada({ id, idGrupo, nomeNormalizado, ehFolguista, escaladoManualmenteParaEsteFim, idsEscaladosAntes, idsManuaisAnteriores, nomesFinaisDaEscalaAnterior }) {
  // Folguista e inclusão manual são exceções; os demais alternam em relação à escala anterior.
  if (ehFolguista || escaladoManualmenteParaEsteFim) return true;
  return !(
    idsEscaladosAntes.has(id) || idsEscaladosAntes.has(idGrupo) ||
    idsManuaisAnteriores.has(id) || idsManuaisAnteriores.has(idGrupo) ||
    nomesFinaisDaEscalaAnterior.has(nomeNormalizado)
  );
}

async function gerarEscalaAutomaticaGrupo(sock, grupo) {
  const chaveEmpresa = 'CHEGO_DELIVERY';
  const estadoEmpresa = empresas[chaveEmpresa]?.estado;
  if (!estadoEmpresa) return;
  // O comando Escala sempre monta o próximo fim de semana. A escala manual
  // salva para o fim de semana vigente é usada como referência para a rotação,
  // evitando repetir automaticamente os mesmos entregadores no próximo.
  const agoraEscala = obterDataHoraFortalezaEscala(new Date());
  const fim = proximoFimDeSemana(agoraEscala);
  const escalaSalva = estadoEmpresa.escalaFimDeSemana || {};
  const manuais = (Array.isArray(estadoEmpresa.escalasManuais) ? estadoEmpresa.escalasManuais : [])
    .filter(p => p && p.fimSemanaSabado === fim.chave);
  const chavePessoa = p => jidNormalizedUser(p?.id || p?.phoneNumber || '');
  const nomePessoa = p => String(p?.nome || p?.name || p?.notify || '').trim();
  const mesclarManuais = lista => {
    const resultado = [...(Array.isArray(lista) ? lista : [])];
    const ids = new Set(resultado.map(chavePessoa).filter(Boolean));
    const nomes = new Set(resultado.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
    for (const manual of manuais) {
      const id = chavePessoa(manual);
      const nome = nomePessoa(manual);
      const nomeNormalizado = normalizarNomeEscala(nome);
      if ((id && ids.has(id)) || (nomeNormalizado && nomes.has(nomeNormalizado))) continue;
      resultado.push({ id: manual.id, nome: nome || (id ? id.split('@')[0] : 'Entregador') });
      if (id) ids.add(id);
      if (nomeNormalizado) nomes.add(nomeNormalizado);
    }
    return resultado;
  };

  // Se a escala deste fim de semana já foi gerada, mantém a lista e acrescenta
  // qualquer entregador que o ADM tenha escalado manualmente depois.
  if (escalaSalva.dataSabado === fim.chave && Array.isArray(escalaSalva.entregadores) && escalaSalva.entregadores.length) {
    const proibidos = Array.isArray(estadoEmpresa.semEscalaPermanente) ? estadoEmpresa.semEscalaPermanente : [];
    const chaveProibida = new Set(proibidos.map(chavePessoa).filter(Boolean));
    const nomesProibidos = new Set(proibidos.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
    const basePermitida = escalaSalva.entregadores.filter(p => {
      const id = chavePessoa(p), nome = normalizarNomeEscala(nomePessoa(p));
      return !(chaveProibida.has(id) || (nome && nomesProibidos.has(nome)));
    });
    const folguistas = Array.isArray(estadoEmpresa.folguistasEscala) ? estadoEmpresa.folguistasEscala : [];
    const atualizada = mesclarManuais([...basePermitida, ...folguistas.map(p => ({ id: p.id, nome: p.nome }))]).filter(p => {
      const id = chavePessoa(p), nome = normalizarNomeEscala(nomePessoa(p));
      return !(chaveProibida.has(id) || (nome && nomesProibidos.has(nome)));
    });
    empresas[chaveEmpresa].estado = estadoEmpresa;
    salvar();
    await enviarEscalaFormatada(sock, grupo, fim, atualizada);
    return;
  }

  let meta;
  try { meta = await sock.groupMetadata(grupo); }
  catch (e) {
    await sock.sendMessage(grupo, { text: 'Não consegui consultar os membros do grupo para montar a escala. Tente novamente.' });
    return;
  }

  // Não descarte participantes @lid: versões recentes do WhatsApp/Baileys
  // podem identificar membros assim. O nome pode estar no próprio participante,
  // no contato ou no número associado ao LID.
  const participantes = (meta?.participants || []).filter(p => p?.id);
  const ultimo = escalaSalva.dataSabado === sabadoAnteriorEscala(fim.chave) && Array.isArray(escalaSalva.entregadores)
    ? escalaSalva.entregadores : [];
  const idsEscaladosAntes = new Set(ultimo.map(chavePessoa).filter(Boolean));
  const nomesEscaladosAntes = ultimo.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean);
  const sabadoAnterior = sabadoAnteriorEscala(fim.chave);
  const escalasManuaisAnteriores = (Array.isArray(estadoEmpresa.escalasManuais) ? estadoEmpresa.escalasManuais : [])
    .filter(p => p.fimSemanaSabado === sabadoAnterior);
  const idsManuaisAnteriores = new Set(escalasManuaisAnteriores.map(chavePessoa).filter(Boolean));
  const nomesManuaisAnteriores = new Set(escalasManuaisAnteriores.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
  const nomesFinaisDaEscalaAnterior = new Set([
    ...nomesEscaladosAntes, ...nomesManuaisAnteriores
  ]);
  const idsManuaisProximo = new Set(manuais.map(chavePessoa).filter(Boolean));
  const nomesManuaisProximo = new Set(manuais.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
  const folguistas = Array.isArray(estadoEmpresa.folguistasEscala) ? estadoEmpresa.folguistasEscala : [];
  const semEscala = Array.isArray(estadoEmpresa.semEscalaPermanente) ? estadoEmpresa.semEscalaPermanente : [];
  const idsFolguistas = new Set(folguistas.map(chavePessoa).filter(Boolean));
  const nomesFolguistas = new Set(folguistas.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
  const idsProibidos = new Set(semEscala.map(chavePessoa).filter(Boolean));
  const nomesProibidos = new Set(semEscala.map(p => normalizarNomeEscala(nomePessoa(p))).filter(Boolean));
  const candidatos = [];
  const vistos = new Set();
  const nomesVistos = new Set();

  for (const participante of participantes) {
    // phoneNumber, quando fornecido pelo Baileys, ajuda a unificar o LID com o JID telefônico.
    const idGrupo = jidNormalizedUser(participante.id);
    const idTelefone = jidNormalizedUser(participante.phoneNumber || participante.id);
    const id = idTelefone || idGrupo;
    if (!id || vistos.has(id) || participante.admin === 'admin' || participante.admin === 'superadmin') continue;
    vistos.add(id);
    const contato = sock.contacts?.[id] || sock.contacts?.[idGrupo] || sock.contacts?.[participante.id] || {};
    const nome = String(
      contato.name || contato.notify || contato.pushName ||
      participante.notify || participante.name || participante.verifiedName ||
      (idGrupo && !idGrupo.endsWith('@lid') ? idGrupo.split('@')[0] : '')
    ).trim();
    if (!nome) continue;
    const nomeNormalizado = normalizarNomeEscala(nome);
    const estaProibido = idsProibidos.has(id) || idsProibidos.has(idGrupo) || nomesProibidos.has(nomeNormalizado);
    if (estaProibido) continue;
    const ehFolguista = idsFolguistas.has(id) || idsFolguistas.has(idGrupo) || nomesFolguistas.has(nomeNormalizado);
    const escaladoManualmenteParaEsteFim = idsManuaisProximo.has(id) || idsManuaisProximo.has(idGrupo) || nomesManuaisProximo.has(nomeNormalizado);
    if (!deveIncluirNaEscalaAlternada({
      id, idGrupo, nomeNormalizado, ehFolguista, escaladoManualmenteParaEsteFim,
      idsEscaladosAntes, idsManuaisAnteriores, nomesFinaisDaEscalaAnterior
    })) continue;
    if (nomesVistos.has(nomeNormalizado)) continue;
    candidatos.push({ id: participante.id, nome });
    nomesVistos.add(nomeNormalizado);
  }

  // Folguistas permanentes entram sempre, mesmo que a metadata do grupo não os retorne.
  const folguistasPermitidos = folguistas.filter(p => {
    const id = chavePessoa(p), nome = normalizarNomeEscala(nomePessoa(p));
    return !(idsProibidos.has(id) || (nome && nomesProibidos.has(nome)));
  }).map(p => ({ id: p.id, nome: p.nome }));
  // Os escalados manualmente para este fim de semana entram mesmo que o WhatsApp
  // não devolva o nome deles na metadata de participantes.
  const completos = mesclarManuais([...candidatos, ...folguistasPermitidos]).filter(p => {
    const id = chavePessoa(p), nome = normalizarNomeEscala(nomePessoa(p));
    return !(idsProibidos.has(id) || (nome && nomesProibidos.has(nome)));
  });
  completos.sort((a,b) => nomePessoa(a).localeCompare(nomePessoa(b), 'pt-BR'));
  if (!completos.length) {
    // Nunca reutiliza a lista do fim de semana anterior como fallback: isso quebraria a alternância.
    await sock.sendMessage(grupo, { text: '⚠️ Não consegui identificar entregadores disponíveis para a próxima escala. Não publiquei uma lista repetida. Confira os participantes do grupo e tente novamente.' });
    return;
  }
  estadoEmpresa.escalaFimDeSemana = { dataSabado: fim.chave, entregadores: completos, geradaEm: Date.now() };
  empresas[chaveEmpresa].estado = estadoEmpresa;
  salvar();
  await enviarEscalaFormatada(sock, grupo, fim, completos);
}

function dataLocalChaveEscala(data) {
  return `${data.getFullYear()}-${String(data.getMonth()+1).padStart(2,'0')}-${String(data.getDate()).padStart(2,'0')}`;
}

function intervaloDiaLocalEscala(chave) {
  const [ano, mes, dia] = String(chave).split('-').map(Number);
  const inicio = new Date(ano, mes - 1, dia).getTime();
  return { inicio, fim: new Date(ano, mes - 1, dia + 1).getTime() };
}

function entregadorTrabalhouNoDiaEscala(estadoEmpresa, pessoa, chaveDia) {
  const id = jidNormalizedUser(pessoa?.id || pessoa?.jid || '');
  const nome = normalizarNomeEscala(pessoa?.nome || pessoa?.name || '');
  if (!id && !nome) return false;
  const faixa = intervaloDiaLocalEscala(chaveDia);
  const sessoes = Array.isArray(estadoEmpresa.sessoesOnline) ? estadoEmpresa.sessoesOnline : [];
  if (sessoes.some(s => {
    const sid = jidNormalizedUser(s.entregadorId || '');
    const sNome = normalizarNomeEscala(s.entregadorNome || '');
    const inicio = Number(s.iniciadaEm || 0);
    const fim = Number(s.finalizadaEm || Date.now());
    return (sid && id && sid === id || sNome && nome && sNome === nome) && inicio < faixa.fim && fim > faixa.inicio;
  })) return true;
  const entregas = Array.isArray(estadoEmpresa.historicoEntregas) ? estadoEmpresa.historicoEntregas : [];
  return entregas.some(e => {
    const eid = jidNormalizedUser(e.entregadorId || '');
    const eNome = normalizarNomeEscala(e.entregadorNome || '');
    const ts = Number(e.iniciadaEm || e.concluidaEm || e.finalizadaEm || 0);
    return (eid && id && eid === id || eNome && nome && eNome === nome) && ts >= faixa.inicio && ts < faixa.fim;
  });
}

async function processarPunicoesEscalaFimDeSemana(sock, grupo) {
  const estadoEmpresa = empresas.CHEGO_DELIVERY?.estado;
  if (!estadoEmpresa || !grupo) return;
  const agora = new Date();
  if (agora.getDay() !== 1 || agora.getHours() < 6) return;
  const chaveSabadoAtual = chaveSabadoEscala(agora);
  const chaveSabadoAvaliar = sabadoAnteriorEscala(chaveSabadoAtual);
  if (estadoEmpresa.ultimaAvaliacaoEscala === chaveSabadoAvaliar) return;
  const escala = estadoEmpresa.escalaFimDeSemana || {};
  // Não pune com base em dados de outra semana ou se a escala anterior não foi salva.
  if (escala.dataSabado !== chaveSabadoAvaliar || !Array.isArray(escala.entregadores)) {
    estadoEmpresa.ultimaAvaliacaoEscala = chaveSabadoAvaliar;
    salvar();
    return;
  }
  if (!Array.isArray(estadoEmpresa.justificativasEscala)) estadoEmpresa.justificativasEscala = [];
  if (!Array.isArray(estadoEmpresa.bloqueiosAutomaticosEscala)) estadoEmpresa.bloqueiosAutomaticosEscala = [];
  const domingoDate = new Date(Number(chaveSabadoAvaliar.slice(0,4)), Number(chaveSabadoAvaliar.slice(5,7))-1, Number(chaveSabadoAvaliar.slice(8,10))+1);
  const chaveDomingo = dataLocalChaveEscala(domingoDate);
  const agoraMs = Date.now();
  const fimBloqueioTresDias = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate() + 3, 6, 0, 0, 0).getTime(); // quinta às 06h: bloqueado segunda, terça e quarta
  const fimBloqueioSemana = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate() + 7, 6, 0, 0, 0).getTime();
  const punições = [];
  for (const pessoa of escala.entregadores) {
    const id = jidNormalizedUser(pessoa?.id || pessoa?.jid || '');
    if (!id) continue;
    const nome = String(pessoa?.nome || pessoa?.name || 'Entregador').trim();
    const statusSabado = obterStatusDiaEscala(id, new Date(Number(chaveSabadoAvaliar.slice(0,4)), Number(chaveSabadoAvaliar.slice(5,7))-1, Number(chaveSabadoAvaliar.slice(8,10))), chaveSabadoAvaliar, agora);
    const statusDomingo = obterStatusDiaEscala(id, domingoDate, chaveSabadoAvaliar, agora);
    const faltaSabado = statusSabado === '❌';
    const faltaDomingo = statusDomingo === '❌';
    if (!faltaSabado && !faltaDomingo) continue;
    const semanal = faltaSabado && faltaDomingo;
    const ate = semanal ? fimBloqueioSemana : fimBloqueioTresDias;
    estadoEmpresa.bloqueiosAutomaticosEscala = estadoEmpresa.bloqueiosAutomaticosEscala.filter(x => jidNormalizedUser(x.id) !== id);
    estadoEmpresa.bloqueiosAutomaticosEscala.push({ id, nome, fimSemanaSabado: chaveSabadoAvaliar, tipo: semanal ? 'semana' : 'tres_dias', criadoEm: agoraMs, ate });
    estadoEmpresa.bloqueados = estadoEmpresa.bloqueados.filter(x => jidNormalizedUser(x) !== id);
    estadoEmpresa.bloqueadosSemana = estadoEmpresa.bloqueadosSemana.filter(x => jidNormalizedUser(x) !== id);
    if (semanal) estadoEmpresa.bloqueadosSemana.push(id);
    else estadoEmpresa.bloqueados.push(id);
    punições.push(`• *${nome}* — ${semanal ? 'faltou sábado e domingo sem justificativa; bloqueado por 1 semana' : `falta injustificada no ${faltaSabado ? 'sábado' : 'domingo'}; bloqueado segunda, terça e quarta (liberação quinta às 06h)`}`);
  }
  estadoEmpresa.ultimaAvaliacaoEscala = chaveSabadoAvaliar;
  salvar();
  if (punições.length) {
    await sock.sendMessage(grupo, { text: `⚠️ *APURAÇÃO AUTOMÁTICA DA ESCALA — ${chaveSabadoAvaliar}*\n\n${punições.join('\n')}\n\nO bloqueio é automático e expira no horário informado.` });
    await publicarLista(sock);
  } else {
    await sock.sendMessage(grupo, { text: `✅ *Apuração da escala concluída*\nNenhuma falta injustificada encontrada para o fim de semana de ${chaveSabadoAvaliar}.` });
  }
}

async function verificarPublicacaoAutomaticaEscala(sock) {
  const agora = obterDataHoraFortalezaEscala(new Date());
  if (agora.getDay() !== 1 || agora.getHours() < 6) return;
  const chaveEmpresa = 'CHEGO_DELIVERY';
  selecionarEmpresa(chaveEmpresa);
  const grupo = empresas[chaveEmpresa]?.grupos?.g1;
  if (!grupo) return;
  const fim = proximoFimDeSemana(agora);
  const estadoEmpresa = empresas[chaveEmpresa]?.estado;
  if (!estadoEmpresa || estadoEmpresa.ultimaEscalaAutomaticaPublicada === fim.chave) return;

  // Se o ADM já publicou manualmente a escala desta data, não manda uma duplicata às 06h.
  const salva = estadoEmpresa.escalaFimDeSemana || {};
  if (salva.dataSabado === fim.chave && Array.isArray(salva.entregadores) && salva.entregadores.length) {
    estadoEmpresa.ultimaEscalaAutomaticaPublicada = fim.chave;
    empresas[chaveEmpresa].estado = estadoEmpresa;
    salvar();
    return;
  }

  await gerarEscalaAutomaticaGrupo(sock, grupo);
  const depois = empresas[chaveEmpresa]?.estado;
  if (depois?.escalaFimDeSemana?.dataSabado === fim.chave && depois.escalaFimDeSemana.entregadores?.length) {
    depois.ultimaEscalaAutomaticaPublicada = fim.chave;
    empresas[chaveEmpresa].estado = depois;
    salvar();
  }
}

async function enviarEscalaFormatada(sock, grupo, fim, entregadores) {
  const linhas = entregadores.map((p, i) => `${i+1}. @${String(p.id).split('@')[0]}`);
  const texto = `*ESCALA DO FINAL DE SEMANA*\n\n*${fim.sabadoTexto}*\n*${fim.domingoTexto}*\n\n*OBS: Escala contará a partir das 10 da manhã, até às 15h e das 18h até terminar o horário de pico*\n\n${linhas.join('\n')}\n\n*OBS: PEDIDO DE TROCA DE ESCALA ATÉ A QUARTA-FEIRA*\n\n*O DESCUMPRIMENTO INJUSTIFICADO DOS HORÁRIOS NÃO SERÁ MAIS TOLERADO E RESULTARÁ EM REMOÇÕES IMEDIATAS.*`;
  const mencoes = entregadores.map(p => jidNormalizedUser(p.id)).filter(Boolean);
  try {
    await sock.sendMessage(grupo, { text: texto, mentions: mencoes });
  } catch (e) {
    console.log('Erro ao publicar escala com marcações:', e.message);
    await enviarTextoCompleto(sock, grupo, texto);
  }
}

function formatarDuracaoOnline(ms) {
  const minutos = Math.max(0, Math.floor((Number(ms) || 0) / 60000));
  const h = Math.floor(minutos / 60), m = minutos % 60;
  return `${h}h ${String(m).padStart(2, '0')}min`;
}
function obterPeriodoOnline(periodo, agora = new Date()) {
  const fim = new Date(agora);
  const inicio = new Date(agora);
  inicio.setHours(0, 0, 0, 0);
  if (periodo === 'essa semana') {
    const dia = inicio.getDay();
    inicio.setDate(inicio.getDate() - ((dia + 6) % 7));
  } else if (periodo === 'semana passada') {
    const dia = inicio.getDay();
    inicio.setDate(inicio.getDate() - ((dia + 6) % 7) - 7);
    fim.setTime(inicio.getTime() + 7 * 24 * 60 * 60 * 1000);
  } else if (periodo === 'esse mês') {
    inicio.setDate(1);
  }
  return { inicio: inicio.getTime(), fim: periodo === 'semana passada' ? fim.getTime() : agora.getTime(), periodo };
}
function coletarTempoOnline(periodo = 'hoje', agora = Date.now()) {
  const faixa = obterPeriodoOnline(periodo, new Date(agora));
  const mapa = new Map();
  const intervalosBrutos = [];
  const idPorNome = new Map();
  const idsPorNome = new Map();
  const nomeChave = nome => normalizarTexto(String(nome || '').trim());
  const obterId = valor => jidNormalizedUser(String(valor || '').trim());
  const ehLid = id => /@lid$/i.test(String(id || ''));

  const registrarPessoa = (idOriginal, nomeOriginal) => {
    const id = obterId(idOriginal);
    if (!id) return;
    const nome = String(nomeOriginal || 'Entregador').trim() || 'Entregador';
    const chaveNome = nomeChave(nome);
    if (!mapa.has(id)) mapa.set(id, { id, nome, ms: 0 });
    else if ((!mapa.get(id).nome || mapa.get(id).nome === 'Entregador') && nome !== 'Entregador') mapa.get(id).nome = nome;
    if (chaveNome && chaveNome !== nomeChave('Entregador')) {
      if (!idsPorNome.has(chaveNome)) idsPorNome.set(chaveNome, new Set());
      idsPorNome.get(chaveNome).add(id);
      if (!idPorNome.has(chaveNome) || (ehLid(idPorNome.get(chaveNome)) && !ehLid(id))) idPorNome.set(chaveNome, id);
    }
  };

  // Primeiro reúne os registros de todas as empresas/grupos e todos os aliases conhecidos.
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const est = empresas[chave]?.estado || {};
    for (const p of (est.entregadores || [])) registrarPessoa(p.id || p.jid || p.numero, p.nome || p.name || p.pushName);
    for (const p of (est.online || [])) registrarPessoa(p.id || p.jid || p.numero, p.nome || p.name || p.pushName);
    for (const p of (est.espera || [])) registrarPessoa(p.id || p.jid || p.numero, p.nome || p.name || p.pushName);
    for (const sessao of (est.sessoesOnline || [])) registrarPessoa(sessao.entregadorId, sessao.entregadorNome || sessao.nome);
    for (const entrega of (est.historicoEntregas || [])) registrarPessoa(entrega.entregadorId, entrega.entregadorNome || entrega.nome);
  }

  // Se o WhatsApp apresentar a mesma pessoa com um ID @lid num grupo e um ID
  // telefônico noutro, unifica esses IDs quando o nome coincide e há um alias @lid.
  const idCanonico = new Map();
  for (const [id, pessoa] of mapa) idCanonico.set(id, id);
  for (const [chaveNome, idsSet] of idsPorNome) {
    const ids = [...idsSet];
    if (ids.length < 2 || !ids.some(ehLid)) continue;
    const canonico = idPorNome.get(chaveNome) || ids[0];
    for (const id of ids) idCanonico.set(id, canonico);
  }

  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const est = empresas[chave]?.estado || {};
    for (const sessao of (est.sessoesOnline || [])) {
      const idOriginal = obterId(sessao.entregadorId || '');
      if (!idOriginal) continue;
      const inicio = Number(sessao.iniciadaEm || 0);
      const fim = Number(sessao.finalizadaEm || agora);
      if (!inicio || fim <= faixa.inicio || inicio >= faixa.fim) continue;
      const a = Math.max(inicio, faixa.inicio);
      const b = Math.min(fim, faixa.fim);
      if (b <= a) continue;
      const nome = String(sessao.entregadorNome || 'Entregador').trim() || 'Entregador';
      const chaveNome = nomeChave(nome);
      const id = idCanonico.get(idOriginal) || (chaveNome && idPorNome.get(chaveNome)) || idOriginal;
      intervalosBrutos.push({ id, nome, a, b });
      if (!mapa.has(id)) mapa.set(id, { id, nome, ms: 0 });
      else if ((!mapa.get(id).nome || mapa.get(id).nome === 'Entregador') && nome !== 'Entregador') mapa.get(id).nome = nome;
    }
  }

  // União matemática dos intervalos: períodos simultâneos em dois grupos contam uma vez.
  const intervalosPorId = new Map();
  for (const item of intervalosBrutos) {
    if (!intervalosPorId.has(item.id)) intervalosPorId.set(item.id, []);
    intervalosPorId.get(item.id).push([item.a, item.b]);
  }
  for (const [id, intervalos] of intervalosPorId) {
    intervalos.sort((a, b) => a[0] - b[0]);
    let inicioAtual = null, fimAtual = null, total = 0;
    for (const [a, b] of intervalos) {
      if (inicioAtual === null) { inicioAtual = a; fimAtual = b; }
      else if (a <= fimAtual) fimAtual = Math.max(fimAtual, b);
      else { total += fimAtual - inicioAtual; inicioAtual = a; fimAtual = b; }
    }
    if (inicioAtual !== null) total += fimAtual - inicioAtual;
    if (mapa.has(id)) mapa.get(id).ms = total;
  }

  // Evita exibir duas linhas para aliases @lid/telefone da mesma pessoa.
  const resultado = [...mapa.values()];
  const vistos = new Set();
  const unicos = [];
  for (const pessoa of resultado) {
    const canonico = idCanonico.get(pessoa.id) || pessoa.id;
    if (vistos.has(canonico)) continue;
    vistos.add(canonico);
    const registro = mapa.get(canonico) || pessoa;
    if (registro !== pessoa && pessoa.ms > registro.ms) registro.ms = pessoa.ms;
    unicos.push(registro);
  }
  return unicos
    .sort((a, b) => b.ms - a.ms || a.nome.localeCompare(b.nome, 'pt-BR'))
    .map((x, i) => ({ ...x, posicao: i + 1, valor: x.ms / 60000 }));
}
function coletarRankingTempoOnline(periodo = 'hoje', agora = Date.now()) {
  // O relatório continua mostrando todos; o ranking inclui apenas quem acumulou 30 min ou mais.
  return coletarTempoOnline(periodo, agora)
    .filter(x => x.ms >= 30 * 60 * 1000)
    .map((x, i) => ({ ...x, posicao: i + 1 }));
}

function coletarTempoOnlineHoje(agora = Date.now()) { return coletarTempoOnline('hoje', agora); }
function gerarRelatorioTempoOnline(periodo = 'hoje') {
  const faixa = obterPeriodoOnline(periodo);
  const titulos = { 'hoje': 'HOJE', 'essa semana': 'ESTA SEMANA', 'semana passada': 'SEMANA PASSADA', 'esse mês': 'ESTE MÊS' };
  const dados = coletarTempoOnline(periodo);
  const titulo = titulos[periodo] || 'HOJE';
  if (!dados.length) return `🕒 *TEMPO ONLINE DOS ENTREGADORES — ${titulo}*\nNenhum entregador cadastrado ou encontrado.`;
  const estaOnlineAgora = id => Object.keys(EMPRESA_CONFIG).some(ch => {
    const est = empresas[ch]?.estado || {};
    return (est.online || []).some(p => jidNormalizedUser(p.id || p.jid || '') === id) ||
      (est.sessoesOnline || []).some(s => jidNormalizedUser(s.entregadorId || '') === id && !s.finalizadaEm);
  });
  return `🕒 *TEMPO ONLINE DE TODOS OS ENTREGADORES — ${titulo}*\nPeríodo: ${new Date(faixa.inicio).toLocaleDateString('pt-BR')} a ${new Date(faixa.fim).toLocaleDateString('pt-BR')}\nAtualizado: ${new Date().toLocaleString('pt-BR')}\nTotal de entregadores: ${dados.length}\n\n` + dados.map(x => `• *${x.nome}* — ${formatarDuracaoOnline(x.ms)}${estaOnlineAgora(x.id) ? ' 🟢 (online agora)' : ''}`).join('\n');
}

function obterStatusDiaEscala(id, dia, chaveSabado, agora = new Date()) {
  const est = empresas.CHEGO_DELIVERY?.estado || {};
  const inicioDia = new Date(dia.getFullYear(), dia.getMonth(), dia.getDate()).getTime();
  const fimDia = new Date(dia.getFullYear(), dia.getMonth(), dia.getDate() + 1).getTime();
  const agoraMs = agora.getTime();
  const hojeInicio = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate()).getTime();
  const nomeDia = dia.getDay() === 6 ? 'sábado' : 'domingo';
  const justificado = (est.justificativasEscala || []).some(j =>
    jidNormalizedUser(j?.id || '') === id && j?.fimSemanaSabado === chaveSabado &&
    normalizarTexto(j?.dia || '') === normalizarTexto(nomeDia)
  );
  if (justificado) return '⚠️';

  const historicos = Object.keys(EMPRESA_CONFIG).flatMap(k => (empresas[k]?.estado?.historicoEntregas || []));
  // Para a escala, entregas fracionadas também contam. Cada registro de
  // histórico representa uma solicitação; em fracionados, `quantidade`
  // guarda o total informado (ex.: 4 em 1/4 ... 4/4), sem duplicar o aceite.
  // Usa o horário de atualização do fracionamento quando disponível, pois
  // a finalização por figurinha pode ocorrer depois da janela de trabalho.
  const eventos = historicos.filter(h => {
    const ts = Number(h?.fracionamentoAtualizadoEm || h?.finalizadaEm || h?.concluidaEm || 0);
    return jidNormalizedUser(h?.entregadorId || '') === id && ts >= inicioDia && ts < fimDia && ts > 0;
  });
  const contarJanela = (inicio, fim) => eventos.reduce((total, h) => {
    const ts = Number(h?.fracionamentoAtualizadoEm || h?.finalizadaEm || h?.concluidaEm || 0);
    const d = new Date(ts);
    const hora = d.getHours() + d.getMinutes() / 60 + d.getSeconds() / 3600;
    if (hora < inicio || hora >= fim) return total;
    const fracaoTotal = Number(h?.fracaoTotal || 0);
    const quantidade = fracaoTotal > 0
      ? Math.max(1, Number(h?.quantidade || h?.fracaoAtual || fracaoTotal) || 1)
      : 1;
    return total + quantidade;
  }, 0);
  const entregasManha = contarJanela(10, 15);
  const entregasPico = contarJanela(18, 24);
  // Cumpre o dia se finalizar pelo menos 5 entregas em qualquer uma das janelas.
  if (entregasManha >= 5 || entregasPico >= 5) return '✅';

  // A janela das 10h às 15h fecha às 15h. A segunda só fecha quando o pico
  // realmente termina; se não houve pico registrado, usa o fim do dia como limite seguro.
  const janelaManhaFechada = agoraMs >= inicioDia + 15 * 60 * 60 * 1000;
  let janelaPicoFechada = inicioDia < hojeInicio || agoraMs >= fimDia;
  if (inicioDia === hojeInicio && agoraMs >= inicioDia + 18 * 60 * 60 * 1000 && agoraMs < fimDia) {
    const inicioPico = Number(est.horarioPicoIniciadoEm || 0);
    const fimPico = Number(est.horarioPicoEncerradoEm || 0);
    const picoComecouHoje = inicioPico >= inicioDia && inicioPico < fimDia;
    const picoTerminouHoje = fimPico >= inicioDia && fimPico < fimDia && (!picoComecouHoje || fimPico >= inicioPico);
    if (picoTerminouHoje) janelaPicoFechada = true;
    else if (picoComecouHoje && !picoTerminouHoje) janelaPicoFechada = false;
    else janelaPicoFechada = agoraMs >= fimDia - 1000;
  }
  return janelaManhaFechada && janelaPicoFechada ? '❌' : '—';
}

function obterChaveSabadoEscalaParaApuracao(agora = new Date()) {
  // No sábado/domingo, apura o fim de semana em andamento, mesmo que já exista
  // uma escala publicada para o próximo fim de semana.
  if (agora.getDay() === 6 || agora.getDay() === 0) return chaveSabadoEscala(agora);
  const est = empresas.CHEGO_DELIVERY?.estado || {};
  const salva = est.escalaFimDeSemana || {};
  if (typeof salva.dataSabado === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(salva.dataSabado)) {
    const [a,m,d] = salva.dataSabado.split('-').map(Number);
    const sab = new Date(a, m - 1, d);
    const dom = new Date(sab); dom.setDate(dom.getDate() + 1);
    const hoje = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate());
    const limite = new Date(hoje); limite.setDate(limite.getDate() - 7);
    if (dom < hoje && dom >= limite) return salva.dataSabado;
    if (sab >= hoje) return salva.dataSabado;
  }
  return chaveSabadoEscala(agora);
}

async function bloquearEscaladosPorCumprimento(sock, jid) {
  const est = empresas.CHEGO_DELIVERY?.estado;
  if (!est) { await sock.sendMessage(jid, { text: '⚠️ Não encontrei os dados da Chegô Delivery.' }); return; }
  const agora = new Date();
  const chaveSabado = obterChaveSabadoEscalaParaApuracao(agora);
  const escalaSalva = est.escalaFimDeSemana || {};
  const pessoas = new Map();
  const adicionar = p => {
    const id = jidNormalizedUser(p?.id || p?.jid || p?.phoneNumber || '');
    if (id && (id.endsWith('@s.whatsapp.net') || id.endsWith('@lid')) && !pessoas.has(id)) {
      pessoas.set(id, { id, nome: String(p?.nome || p?.name || '').trim() || id.split('@')[0] });
    }
  };
  if (escalaSalva.dataSabado === chaveSabado) for (const p of (escalaSalva.entregadores || [])) adicionar(p);
  for (const p of (est.escalasManuais || [])) if (p?.fimSemanaSabado === chaveSabado) adicionar(p);
  if (!pessoas.size) {
    await sock.sendMessage(jid, { text: '⚠️ Não encontrei uma escala salva para este final de semana. Não apliquei nenhum bloqueio.' });
    return;
  }
  const [a,m,d] = chaveSabado.split('-').map(Number);
  const sabado = new Date(a, m - 1, d);
  const domingo = new Date(sabado); domingo.setDate(domingo.getDate() + 1);
  const avaliados = [...pessoas.values()].map(p => ({
    ...p,
    sabado: obterStatusDiaEscala(p.id, sabado, chaveSabado, agora),
    domingo: obterStatusDiaEscala(p.id, domingo, chaveSabado, agora)
  }));
  if (avaliados.some(p => p.sabado === '—' || p.domingo === '—')) {
    await sock.sendMessage(jid, { text: '⚠️ A apuração ainda está em andamento. Nenhum bloqueio foi aplicado.' });
    return;
  }
  if (!Array.isArray(est.bloqueiosAutomaticosEscala)) est.bloqueiosAutomaticosEscala = [];
  const segunda = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate(), 6, 0, 0, 0);
  const diasAteSegunda = (8 - agora.getDay()) % 7;
  if (diasAteSegunda > 0) segunda.setDate(segunda.getDate() + diasAteSegunda);
  else if (agora.getHours() >= 6) segunda.setTime(agora.getTime());
  const bloqueados = [];
  const jaCumpriram = [];
  for (const p of avaliados) {
    const faltaSabado = p.sabado === '❌';
    const faltaDomingo = p.domingo === '❌';
    if (!faltaSabado && !faltaDomingo) { jaCumpriram.push(p.nome); continue; }
    const semanal = faltaSabado && faltaDomingo;
    const inicio = segunda.getTime();
    const ateData = new Date(segunda);
    ateData.setDate(ateData.getDate() + (semanal ? 7 : 3));
    const ate = ateData.getTime(); // libera às 06h da quinta-feira ou da segunda-feira seguinte
    est.bloqueiosAutomaticosEscala = est.bloqueiosAutomaticosEscala.filter(x =>
      !(jidNormalizedUser(x.id) === p.id && x.fimSemanaSabado === chaveSabado)
    );
    est.bloqueiosAutomaticosEscala.push({ id: p.id, nome: p.nome, fimSemanaSabado: chaveSabado,
      tipo: semanal ? 'semana' : 'tres_dias', criadoEm: Date.now(), inicio, ate, aplicadoPorComandoADM: true });
    bloqueados.push(`• *${p.nome}* — ${semanal ? 'faltou sábado e domingo sem justificativa; bloqueio por 1 semana' : `faltou ${faltaSabado ? 'sábado' : 'domingo'} sem justificativa; bloqueio segunda, terça e quarta`}`);
  }
  est.ultimaAvaliacaoEscala = chaveSabado;
  salvar();
  const partes = [`✅ *APURAÇÃO DE BLOQUEIOS DA ESCALA*\nFinal de semana: ${sabado.toLocaleDateString('pt-BR')} e ${domingo.toLocaleDateString('pt-BR')}`];
  partes.push(bloqueados.length ? `\n⛔ *Bloqueios programados*\n${bloqueados.join('\n')}\n\nOs bloqueios começam na segunda-feira às 06h e não bloqueiam antes desse horário.` : '\n✅ Nenhum bloqueio necessário: todos cumpriram a escala ou possuem justificativa.');
  if (jaCumpriram.length) partes.push(`\n\n✅ *Sem bloqueio*\n${jaCumpriram.join(', ')}`);
  await enviarTextoCompleto(sock, jid, partes.join(''));
}

function gerarRelatorioCumprimentoEscala(agora = new Date()) {
  const est = empresas.CHEGO_DELIVERY?.estado || {}
  const escalaSalva = est.escalaFimDeSemana || {}
  let sabado = null
  // Durante sábado/domingo, o resultado pertence ao fim de semana em andamento;
  // não usar por engano uma escala futura já publicada.
  if (agora.getDay() === 6) {
    sabado = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
  } else if (agora.getDay() === 0) {
    sabado = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate() - 1)
  } else if (escalaSalva.dataSabado) {
    const [a,m,d] = escalaSalva.dataSabado.split('-').map(Number)
    const salvo = new Date(a, m - 1, d)
    const domingoSalvo = new Date(salvo); domingoSalvo.setDate(domingoSalvo.getDate() + 1)
    const hoje = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
    const limite = new Date(hoje); limite.setDate(limite.getDate() - 7)
    if (domingoSalvo < hoje && domingoSalvo >= limite) sabado = salvo
    else if (salvo >= hoje) sabado = salvo
  }
  if (!sabado) {
    sabado = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate())
    if (sabado.getDay() === 0) sabado.setDate(sabado.getDate() - 1)
    else if (sabado.getDay() !== 6) sabado.setDate(sabado.getDate() + ((6 - sabado.getDay() + 7) % 7))
  }
  const domingo = new Date(sabado); domingo.setDate(domingo.getDate() + 1)
  const chaveSabado = `${sabado.getFullYear()}-${String(sabado.getMonth()+1).padStart(2,'0')}-${String(sabado.getDate()).padStart(2,'0')}`
  // Resolve os nomes a partir dos cadastros e registros históricos; não exibe o telefone como nome
  // quando o registro da escala foi salvo apenas com o identificador do WhatsApp.
  const nomesPorId = new Map()
  const chaveNomeEscala = valor => normalizarTexto(String(valor || '').trim())
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const estado = empresas[chave]?.estado || {}
    const colecoes = [estado.entregadores, estado.online, estado.espera, estado.historicoEntregas,
      estado.sessoesOnline, estado.escalaFimDeSemana?.entregadores, estado.escalasManuais]
    for (const lista of colecoes) for (const pessoa of (Array.isArray(lista) ? lista : [])) {
      const idPessoa = jidNormalizedUser(pessoa?.id || pessoa?.jid || pessoa?.numero || pessoa?.phoneNumber || pessoa?.entregadorId || '')
      const nomePessoa = String(pessoa?.nome || pessoa?.name || pessoa?.pushName || pessoa?.entregadorNome || '').trim()
      if (idPessoa && nomePessoa && nomePessoa !== idPessoa.split('@')[0]) nomesPorId.set(idPessoa, nomePessoa)
    }
  }
  const resolverNomeEscala = (p, id) => {
    const nomeSalvo = String(p?.nome || p?.name || '').trim()
    if (nomeSalvo && nomeSalvo !== id.split('@')[0] && !/^\d{8,}$/.test(nomeSalvo)) return nomeSalvo
    return nomesPorId.get(id) || nomeSalvo || 'Nome não encontrado no cadastro'
  }
  const escalados = new Map()
  if (escalaSalva.dataSabado === chaveSabado) for (const p of (escalaSalva.entregadores || [])) {
    const id = jidNormalizedUser(p?.id || p?.phoneNumber || '')
    if (id) escalados.set(id, { id, nome: resolverNomeEscala(p, id) })
  }
  for (const p of (est.escalasManuais || [])) if (p?.fimSemanaSabado === chaveSabado) {
    const id = jidNormalizedUser(p.id || p.phoneNumber || '')
    if (id) escalados.set(id, { id, nome: resolverNomeEscala(p, id) })
  }
  if (!escalados.size) return '⚠️ Não encontrei uma escala salva para esse final de semana. Publique/marque a escala primeiro.'
  const janelas = [{inicio:10,fim:15},{inicio:18,fim:23.999}]
  const datas = [sabado, domingo]
  const dataChave = d => `${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,'0')}-${String(d.getDate()).padStart(2,'0')}`
  const historicos = Object.keys(EMPRESA_CONFIG).flatMap(k => (empresas[k]?.estado?.historicoEntregas || []))
  const statusPorDia = (id, dia) => obterStatusDiaEscala(id, dia, chaveSabado, agora);
  const linhas = [...escalados.values()].sort((a,b)=>a.nome.localeCompare(b.nome,'pt-BR')).map((p,i)=>{
    const sab = statusPorDia(p.id, datas[0]), dom = statusPorDia(p.id, datas[1])
    const numeroMen = String(p.id || '').split('@')[0].replace(/[^0-9]/g, '');
    const mencao = numeroMen ? `@${numeroMen}` : p.nome;
    return `${i+1}. ${mencao} — ${p.nome} ${sab}${dom}`
  })
  return `*ESCALA DO FINAL DE SEMANA*\n\n*${sabado.toLocaleDateString('pt-BR')}*\n*${domingo.toLocaleDateString('pt-BR')}*\n\n*OBS: Escala contará a partir das 10 da manhã até às 15h e das 18h até terminar o horário de pico.*\n\n${linhas.join('\n')}\n\n✅✅ Cumpriu sábado e domingo\n✅❌ Cumpriu sábado e faltou domingo\n❌✅ Faltou sábado e cumpriu domingo\n❌❌ Faltou sábado e domingo\n⚠️⚠️ Justificado sábado e domingo\n\n*Nota:* o dia é cumprido ao atingir pelo menos 5 entregas em qualquer uma das janelas. Entregas fracionadas também contam conforme a quantidade informada (ex.: 4/4 conta 4 entregas).`
}

async function processarAvisosAdmPrivado(sock, msg) {
  const jid = msg?.key?.remoteJid || ''
  if ((!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) || msg?.key?.fromMe) return false
  const textoOriginal = String(obterTexto(msg) || '').trim()
  const texto = normalizarTexto(textoOriginal).replace(/[.!?]+$/g, '').trim()
  const linhasAviso = textoOriginal.split(/\r?\n/)
  const comandoAviso = normalizarTexto(String(linhasAviso[0] || '')).replace(/[.!?]+$/g, '').trim() === 'aviso'
  if (comandoAviso) {
    const mensagemAviso = linhasAviso.slice(1).join('\n').trim()
    const usuarioAviso = jidNormalizedUser(jid)
    if (!(await ehADMEmAlgumaEmpresa(sock, usuarioAviso))) {
      await sock.sendMessage(jid, { text: '⛔ Este comando é exclusivo para ADMs.' })
      return true
    }
    if (!mensagemAviso) {
      await sock.sendMessage(jid, { text: 'Envie o aviso em uma única mensagem, com *Aviso* na primeira linha e o texto nas linhas seguintes.' })
      return true
    }
    const destinatariosAviso = new Map()
    for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
      const estAviso = empresas[chaveEmpresa]?.estado || {}
      for (const pessoa of (estAviso.entregadores || [])) {
        const idPessoa = jidNormalizedUser(pessoa?.id || pessoa?.jid || pessoa?.numero || pessoa?.phoneNumber || pessoa?.entregadorId || '')
        if (!idPessoa || (!idPessoa.endsWith('@s.whatsapp.net') && !idPessoa.endsWith('@lid'))) continue
        destinatariosAviso.set(idPessoa, true)
      }
    }
    if (!destinatariosAviso.size) {
      await sock.sendMessage(jid, { text: '⚠️ Não encontrei entregadores cadastrados para enviar o aviso.' })
      return true
    }
    let enviadosAviso = 0
    let falhasAviso = 0
    for (const idPessoa of destinatariosAviso.keys()) {
      try {
        await sock.sendMessage(idPessoa, { text: mensagemAviso })
        enviadosAviso++
      } catch (erroAviso) {
        falhasAviso++
        console.error(`[AVISO] Falha ao enviar para ${idPessoa}:`, erroAviso?.message || erroAviso)
      }
    }
    await sock.sendMessage(jid, { text: `✅ *Aviso concluído.*\nEnviados: ${enviadosAviso}\nFalhas: ${falhasAviso}\nDestinatários: ${destinatariosAviso.size}.` })
    return true
  }
  const ehEscalado = texto === 'escalado'
  const ehQuemNaoCumpriuEscala = texto === 'quem nao cumpriu a escala'
  const ehResultadoEscala = texto === 'resultado da escala' || texto === 'resultado escala'
  const ehBloquearEscalados = texto === 'bloquear escalados'
  const reuniaoData = /^reuniao\s+dia\s+(\d{2}\/\d{2}\/\d{2,4})$/.exec(textoOriginal.normalize('NFD').replace(/[\u0300-\u036f]/g, '').trim())
  const ehReuniaoHoje = texto === 'reuniao'
  if (!ehEscalado && !ehQuemNaoCumpriuEscala && !ehResultadoEscala && !ehBloquearEscalados && !reuniaoData && !ehReuniaoHoje) return false

  const usuario = jidNormalizedUser(jid)
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Este comando é exclusivo para ADMs.' })
    return true
  }

  if (ehQuemNaoCumpriuEscala || ehResultadoEscala) {
    const relatorioEscala = gerarRelatorioCumprimentoEscala()
    const numerosMencionados = [...relatorioEscala.matchAll(/@([0-9]{8,16})/g)].map(m => m[1])
    const mentions = [...new Set(numerosMencionados)].map(n => `${n}@s.whatsapp.net`)
    await sock.sendMessage(jid, { text: relatorioEscala, mentions })
    return true
  }
  if (ehBloquearEscalados) {
    await bloquearEscaladosPorCumprimento(sock, jid)
    return true
  }

  const destinatarios = new Map()
  const adicionar = pessoa => {
    const id = jidNormalizedUser(typeof pessoa === 'string' ? pessoa : (pessoa?.id || pessoa?.jid || ''))
    if (!id || (!id.endsWith('@s.whatsapp.net') && !id.endsWith('@lid'))) return
    const nome = typeof pessoa === 'object' ? String(pessoa.nome || pessoa.name || '').trim() : ''
    if (!destinatarios.has(id)) destinatarios.set(id, nome)
  }
  for (const chave of Object.keys(EMPRESA_CONFIG)) {
    const est = empresas[chave]?.estado || {}
    for (const pessoa of (est.entregadores || [])) adicionar(pessoa)
  }

  if (ehEscalado) {
    const est = empresas.CHEGO_DELIVERY?.estado || {}
    const escala = est.escalaFimDeSemana || {}
    const hoje = new Date()
    const sabadoAlvo = new Date(hoje.getFullYear(), hoje.getMonth(), hoje.getDate())
    if (sabadoAlvo.getDay() === 0) sabadoAlvo.setDate(sabadoAlvo.getDate() - 1)
    else if (sabadoAlvo.getDay() !== 6) sabadoAlvo.setDate(sabadoAlvo.getDate() + ((6 - sabadoAlvo.getDay() + 7) % 7))
    const chaveSabadoAlvo = `${sabadoAlvo.getFullYear()}-${String(sabadoAlvo.getMonth()+1).padStart(2,'0')}-${String(sabadoAlvo.getDate()).padStart(2,'0')}`
    const listaEscalada = (Array.isArray(escala.entregadores) && escala.dataSabado === chaveSabadoAlvo) ? escala.entregadores : []
    for (const pessoa of listaEscalada) adicionar(pessoa)
    for (const pessoa of (est.escalasManuais || [])) if (pessoa?.fimSemanaSabado === chaveSabadoAlvo) adicionar(pessoa)
    // A lista de destinatários é restrita aos escalados do fim de semana vigente.
    const idsEscalados = new Set([...listaEscalada, ...(est.escalasManuais || []).filter(p => p?.fimSemanaSabado === chaveSabadoAlvo)].map(p => jidNormalizedUser(p?.id || '')).filter(Boolean))
    for (const id of [...destinatarios.keys()]) if (!idsEscalados.has(id)) destinatarios.delete(id)
  }

  if (!destinatarios.size) {
    await sock.sendMessage(jid, { text: ehEscalado ? '⚠️ Não encontrei entregadores registrados na escala do próximo final de semana.' : '⚠️ Não encontrei entregadores cadastrados para enviar o aviso.' })
    return true
  }

  let mensagem
  if (ehEscalado) {
    mensagem = 'Só passando para lembrar que você está escalado este final de semana'
  } else if (reuniaoData) {
    const data = reuniaoData[1]
    const partes = data.split('/').map(Number)
    const ano = partes[2] < 100 ? 2000 + partes[2] : partes[2]
    const dataValida = new Date(ano, partes[1] - 1, partes[0])
    if (dataValida.getFullYear() !== ano || dataValida.getMonth() !== partes[1] - 1 || dataValida.getDate() !== partes[0]) {
      await sock.sendMessage(jid, { text: 'Formato de data inválido. Use: *Reunião dia DD/MM/AA*.' })
      return true
    }
    mensagem = `Passando para avisar que dia ${data} teremos reunião e vc está convocado`
  } else {
    mensagem = 'Passando para lembrar que hoje temos reunião e todos estão convocados'
  }

  let enviados = 0, falhas = 0
  for (const [id] of destinatarios) {
    try { await sock.sendMessage(id, { text: mensagem }); enviados++ }
    catch (e) { falhas++; console.log(`Falha ao enviar aviso privado para ${id}:`, e?.message || e) }
  }
  await sock.sendMessage(jid, { text: `✅ Aviso concluído.\nEnviados: ${enviados}\nFalhas: ${falhas}\nDestinatários: ${destinatarios.size}.` })
  return true
}

// Importação de exportações de conversa do WhatsApp enviada por ADM no privado.
const importacoesPendentesADM = new Map()
const loggerDownloadExportacao = pino({ level: 'silent' })

function extrairDataExportacaoWhatsApp(valor) {
  const m = String(valor || '').match(/^(\d{1,2})[\/.-](\d{1,2})[\/.-](\d{2,4}),?\s+(\d{1,2}):(\d{2})(?::(\d{2}))?$/)
  if (!m) return null
  let ano = Number(m[3]); if (ano < 100) ano += 2000
  const d = new Date(ano, Number(m[2])-1, Number(m[1]), Number(m[4]), Number(m[5]), Number(m[6] || 0))
  return Number.isNaN(d.getTime()) ? null : d.getTime()
}

function analisarExportacaoWhatsApp(buffer) {
  const bruto = buffer.toString('utf8').replace(/^\uFEFF/, '').replace(/\r/g, '')
  const linhas = bruto.split('\n')
  const mensagens = []
  let atual = null
  // Compatível com formatos comuns Android/iOS: [dd/mm/aaaa, hh:mm:ss] Nome: texto
  // e dd/mm/aa, hh:mm - Nome: texto.
  const padrao = /^\[?(\d{1,2}[\/.-]\d{1,2}[\/.-]\d{2,4},?\s+\d{1,2}:\d{2}(?::\d{2})?)\]?\s*[-–]?\s*(.*)$/
  for (const linha of linhas) {
    const m = padrao.exec(linha)
    if (m) {
      if (atual) mensagens.push(atual)
      const instante = extrairDataExportacaoWhatsApp(m[1])
      const resto = m[2] || ''
      const separador = resto.indexOf(': ')
      if (separador > 0) atual = { instante, autor: resto.slice(0, separador).trim(), texto: resto.slice(separador + 2).trim() }
      else atual = { instante, autor: '', texto: resto.trim() }
    } else if (atual && linha.trim()) atual.texto += '\n' + linha
  }
  if (atual) mensagens.push(atual)
  return mensagens.filter(m => m.instante && m.autor && m.texto)
}

function nomeDeExportacaoEhComando(texto) {
  return /^(?:on|online|off|offline|indo|ind[oó]|final|último|ultimo|pr[oó]ximo|prox|ocupado|livre|lista|entrega|entreguei|cancelado|cancelada|mensagem apagada|this message was deleted)$/i.test(String(texto || '').trim())
}

function salvarEstadoEmpresaImportado(chave) {
  const anterior = empresaAtual
  selecionarEmpresa(chave)
  salvar()
  if (anterior && empresas[anterior]) selecionarEmpresa(anterior)
}

async function importarExportacaoParaGrupo(buffer, hash, chave, tipoGrupo) {
  const msgs = analisarExportacaoWhatsApp(buffer)
  if (!msgs.length) return { ok: false, mensagem: 'Não consegui interpretar as datas e mensagens desse arquivo .txt. Envie a exportação original do WhatsApp, sem editar o texto.' }
  const est = empresas[chave].estado
  if (!Array.isArray(est.importacoesRelatorio)) est.importacoesRelatorio = []
  const marcador = `${hash}:${tipoGrupo}:${chave}`
  if (est.importacoesRelatorio.includes(marcador)) return { ok: true, duplicada: true, mensagens: 0, entregas: 0, sessoes: 0 }
  let entregas = 0, sessoes = 0, ignoradas = 0
  if (tipoGrupo === 'empresas') {
    if (!Array.isArray(est.solicitacoesRelatorio)) est.solicitacoesRelatorio = []
    for (const m of msgs) {
      const texto = String(m.texto || '').trim()
      const eventoSistema = /^(?:\u200e)?(?:.+) saiu|entrou no grupo|criou o grupo|mudou a descrição|alterou o assunto|adicionou|removeu|mudou o ícone/i.test(texto)
      const temBairro = typeof extrairBairrosPatos === 'function' && extrairBairrosPatos(texto).length > 0
      const parecePedido = /\b(entrega|entregas|entregar|retirada|pedido|cliente|bairro|rua|endereço|endereco|destino|buscar|levar|moto|motoboy)\b/i.test(texto)
      if (!texto || nomeDeExportacaoEhComando(texto) || eventoSistema || (!temBairro && !parecePedido)) { ignoradas++; continue }
      // Só importa mensagens com indício de pedido/entrega; conversa comum não vira entrega.
      const id = `import:${hash}:${m.instante}:${m.autor}:${entregas}`
      if (est.solicitacoesRelatorio.some(r => r.importacaoId === id)) continue
      est.solicitacoesRelatorio.push({ importacaoId: id, mensagemId: id, empresaId: id, empresaNome: m.autor, quantidade: 1, solicitadaEm: m.instante, data: new Date(m.instante).toISOString().slice(0,10), origem: 'exportacao_whatsapp' })
      entregas++
    }
  } else {
    if (!Array.isArray(est.sessoesOnline)) est.sessoesOnline = []
    const abertas = new Map()
    for (const m of msgs) {
      const texto = String(m.texto || '').trim().toLocaleLowerCase('pt-BR').replace(/[.!\s]+$/g, '')
      const entra = /^(?:on|online|estou online|to online|tô online|voltei|livre)$/.test(texto)
      const sai = /^(?:off|offline|estou offline|to offline|tô offline|saindo|fui|encerrar)$/.test(texto)
      if (!entra && !sai) continue
      const pessoa = m.autor.trim()
      if (entra) {
        if (!abertas.has(pessoa)) abertas.set(pessoa, m.instante)
      } else if (abertas.has(pessoa)) {
        const inicio = abertas.get(pessoa)
        if (m.instante >= inicio) {
          est.sessoesOnline.push({ importacaoId: `${hash}:${pessoa}:${inicio}`, entregadorId: `export:${pessoa.toLocaleLowerCase('pt-BR')}`, entregadorNome: pessoa, iniciadaEm: inicio, finalizadaEm: m.instante, origem: 'exportacao_whatsapp' })
          abertas.delete(pessoa); sessoes++
        }
      }
    }
    // Sessões sem mensagem de saída não são inventadas nem fechadas artificialmente.
    for (const [pessoa, inicio] of abertas) {
      est.sessoesOnline.push({ importacaoId: `${hash}:${pessoa}:${inicio}`, entregadorId: `export:${pessoa.toLocaleLowerCase('pt-BR')}`, entregadorNome: pessoa, iniciadaEm: inicio, finalizadaEm: null, origem: 'exportacao_whatsapp' })
      sessoes++
    }
  }
  est.importacoesRelatorio.push(marcador)
  salvarEstadoEmpresaImportado(chave)
  return { ok: true, mensagens: msgs.length, entregas, sessoes, ignoradas }
}

async function processarImportacaoExportacao(sock, msg) {
  const jid = msg?.key?.remoteJid || ''
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const usuario = jidNormalizedUser(jid)
  const texto = normalizarTexto(obterTexto(msg)).trim()
  const pendente = importacoesPendentesADM.get(usuario)
  if (pendente) {
    if (/^(?:cancelar|cancela)$/i.test(texto)) {
      importacoesPendentesADM.delete(usuario)
      await sock.sendMessage(jid, { text: 'Importação cancelada.' }); return true
    }
    const opcoes = {
      '1': { chave: 'SEU_DELIVERY', tipo: 'empresas', nome: 'SEU DELIVERY — empresas' },
      '2': { chave: 'CHEGO_DELIVERY', tipo: 'empresas', nome: 'CHEGÔ DELIVERY — empresas' },
      '3': { chave: 'SEU_DELIVERY', tipo: 'entregadores', nome: 'EQUIPE MOTOBOY — entregadores' },
      '4': { chave: 'CHEGO_DELIVERY', tipo: 'entregadores', nome: 'CHEGÔ ENTREGADORES — entregadores' }
    }
    const escolha = opcoes[texto]
    if (!escolha) {
      await sock.sendMessage(jid, { text: 'Responda com 1, 2, 3 ou 4. Para desistir, digite cancelar.' }); return true
    }
    importacoesPendentesADM.delete(usuario)
    const resultado = await importarExportacaoParaGrupo(pendente.buffer, pendente.hash, escolha.chave, escolha.tipo)
    if (!resultado.ok) { await sock.sendMessage(jid, { text: `❌ ${resultado.mensagem}` }); return true }
    if (resultado.duplicada) { await sock.sendMessage(jid, { text: '⚠️ Essa exportação já foi importada para esse grupo. Não dupliquei os registros.' }); return true }
    await sock.sendMessage(jid, { text: `✅ *IMPORTAÇÃO CONCLUÍDA*\nGrupo: ${escolha.nome}\nMensagens analisadas: ${resultado.mensagens}\nSolicitações de entrega importadas: ${resultado.entregas || 0}\nSessões online importadas: ${resultado.sessoes || 0}\nMensagens ignoradas: ${resultado.ignoradas || 0}\n\nOs registros foram salvos no histórico do bot. Confirme os relatórios, pois a precisão depende dos comandos e horários presentes na exportação.` })
    return true
  }
  const doc = msg.message?.documentMessage || msg.message?.documentWithCaptionMessage?.message?.documentMessage
  if (!doc) return false
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: 'Somente ADM pode importar exportações de conversa.' }); return true
  }
  const nomeArquivo = String(doc.fileName || '').toLowerCase()
  const mime = String(doc.mimetype || '').toLowerCase()
  if (!(nomeArquivo.endsWith('.txt') || mime.includes('text/plain'))) {
    await sock.sendMessage(jid, { text: 'Envie a exportação de conversa em arquivo .txt. Se o WhatsApp gerou um .zip com mídias, extraia o arquivo .txt e envie somente ele.' }); return true
  }
  try {
    const buffer = await downloadMediaMessage(msg, 'buffer', {}, { logger: loggerDownloadExportacao, reuploadRequest: sock.updateMediaMessage })
    if (!buffer || !buffer.length) throw new Error('arquivo vazio')
    if (buffer.length > 15 * 1024 * 1024) { await sock.sendMessage(jid, { text: 'O arquivo é maior que 15 MB. Envie uma exportação menor.' }); return true }
    const hash = crypto.createHash('sha256').update(buffer).digest('hex')
    importacoesPendentesADM.set(usuario, { buffer, hash, arquivo: doc.fileName || 'exportacao.txt' })
    await sock.sendMessage(jid, { text: `📥 Recebi *${doc.fileName || 'exportacao.txt'}*.\n\nDe qual grupo é essa exportação?\n\n1️⃣ SEU DELIVERY — grupo de empresas (relatório de entregas)\n2️⃣ CHEGÔ DELIVERY — grupo de empresas (relatório de entregas)\n3️⃣ EQUIPE MOTOBOY — grupo de entregadores (tempo online)\n4️⃣ CHEGÔ ENTREGADORES — grupo de entregadores (tempo online)\n\nResponda com 1, 2, 3 ou 4. Para cancelar, digite cancelar.` })
  } catch (e) {
    console.error('Erro ao ler exportação de conversa:', e?.message || e)
    await sock.sendMessage(jid, { text: '❌ Não consegui ler o arquivo recebido. Tente exportar novamente como .txt e enviá-lo como documento.' })
  }
  return true
}

async function processarRelatorioPrivado(sock, msg) {

  const jid = msg?.key?.remoteJid || ''
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const texto = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  const usuario = jidNormalizedUser(jid)
  const etapa = conversasRelatorio.get(usuario)
  const periodoOnlinePendente = conversasOnlinePeriodo.has(usuario)
  const etapaEntregas = conversasEntregasIndividuais.get(usuario)
  const ehEntregasIndividual = /^entregas$/.test(texto)
  const comandoAdicionarBairro = /^(?:adicionar bairro|adicione o bairro|adicione bairro)(?:\s+(.+))?$/.exec(texto)
  const ehAdicionarBairro = !!comandoAdicionarBairro
  const ehBairrosSoltos = /^bairros soltos$/.test(texto)
  const ehInicio = /^(?:relatorio|relatorios|me mostra (?:o )?relatorio|gera (?:o )?relatorio|quero (?:ver )?(?:o )?relatorio|preciso (?:do )?relatorio|ranking (?:das? )?empresas?)$/.test(texto)
  const ehEscala = /^escala$/.test(texto)
  const ehRankingTempo = /^(ranking tempo|tempo medio|tempo médio|ranking de tempo|tempo de entrega)$/.test(texto)
  const ehOnline = /^online$/.test(texto)
  const ehEntrega = /^entrega$/.test(texto)
  const ehTaxas = /^(taxas|taxa)(?:\s+.*)?$/.test(texto)

  // Os relatórios devem exibir o nome que está salvo na agenda do WhatsApp,
  // não o pushName temporário capturado quando a entrega foi registrada.
  const nomesAgenda = new Map()
  const nomeAgendaValido = valor => {
    const n = String(valor || '').trim()
    return !!n && n !== 'Entregador' && !/@/.test(n) && !/^\+?\d[\d .()-]{6,}$/.test(n) && !/^\d{5,}$/.test(n)
  }
  for (const [jidContato, contato] of Object.entries(sock.contacts || {})) {
    const idContato = jidNormalizedUser(contato?.id || jidContato)
    const idTelefoneContato = jidNormalizedUser(contato?.phoneNumber || '')
    const nomeContato = String(contato?.name || contato?.notify || contato?.pushName || '').trim()
    if (nomeAgendaValido(nomeContato)) {
      if (idContato) nomesAgenda.set(idContato, nomeContato)
      if (idTelefoneContato) nomesAgenda.set(idTelefoneContato, nomeContato)
    }
  }
  if (nomesAgenda.size && (ehInicio || ehEscala || ehRankingTempo || ehOnline || ehEntrega || ehTaxas || ehEntregasIndividual)) {
    let nomesAlterados = false
    for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
      const estAgenda = empresas[chaveEmpresa]?.estado || {}
      for (const registro of [...(estAgenda.historicoEntregas || []), ...(estAgenda.entregadores || []), ...(estAgenda.sessoesOnline || [])]) {
        const idRegistro = jidNormalizedUser(registro?.entregadorId || registro?.id || registro?.jid || '')
        const nomeSalvoAgenda = nomesAgenda.get(idRegistro)
        if (nomeSalvoAgenda && registro && (registro.entregadorNome !== nomeSalvoAgenda || registro.nome !== nomeSalvoAgenda)) {
          if ('entregadorNome' in registro || 'entregadorId' in registro) registro.entregadorNome = nomeSalvoAgenda
          if ('nome' in registro || 'id' in registro) registro.nome = nomeSalvoAgenda
          nomesAlterados = true
        }
      }
    }
    if (nomesAlterados) salvar()
  }

  // Perguntas naturais sobre o próprio volume diário: respondidas diretamente,
  // sem obrigar o entregador a entrar no menu interativo de relatórios.
  const perguntaEntregasHoje = /(?:quantas?|numero de|total de) entregas?/.test(texto) &&
    /\b(?:eu|minhas|fiz|faca|fazer|tenho)\b/.test(texto) &&
    /\b(?:hoje|agora|ate agora|ate o momento)\b/.test(texto)
  const perguntaRankingEmpresas = /\b(?:ranking|classificacao|top)\b/.test(texto) && /\bempresas?\b/.test(texto)
  if (perguntaEntregasHoje) {
    let nomeEntregador = 'Entregador'
    for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
      const pessoa = (empresas[chaveEmpresa]?.estado?.entregadores || []).find(x => jidNormalizedUser(x.id || '') === usuario)
      if (pessoa?.nome) { nomeEntregador = pessoa.nome; break }
    }
    await enviarTextoCompleto(sock, jid, gerarTextoRelatorioIndividual(usuario, nomeEntregador, 'hoje'))
    return true
  }
  if (perguntaRankingEmpresas && !(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await responderNegacaoAcesso(sock, jid, usuario, 'o ranking das empresas')
    return true
  }
  const bairroOrigemPreco = BAIRROS_PATOS.find(b => normalizarTexto(b) === texto) || null
  const comandoEditarPreco = /^(?:editar|editar bairro|editar preço|editar preco)\s+(.+)$/.exec(texto)
  const bairroEditarPreco = comandoEditarPreco ? BAIRROS_PATOS.find(b => normalizarTexto(b) === normalizarTexto(comandoEditarPreco[1])) || null : null
  const conversaPrecoPendente = conversasTabelaPrecosBairros.get(usuario)
  const ehTabelaPrecosBairro = !!bairroOrigemPreco
  const ehEditarPrecoBairro = !!bairroEditarPreco
  // Relatório individual de entregas: disponível ao próprio entregador no privado, sem exigir ADM.
  if (ehEntregasIndividual) {
    conversasEntregasIndividuais.set(usuario, { aguardandoPeriodo: true })
    await sock.sendMessage(jid, { text: '📦 *SUAS ENTREGAS*\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada' })
    return true
  }
  if (etapaEntregas?.aguardandoPeriodo) {
    const periodos = { '1':'hoje', 'hoje':'hoje', '2':'essa semana', 'essa semana':'essa semana', 'esta semana':'essa semana', '3':'semana passada', 'semana passada':'semana passada' }
    const periodo = periodos[texto]
    if (!periodo) {
      await sock.sendMessage(jid, { text: 'Escolha uma opção válida:\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada' })
      return true
    }
    conversasEntregasIndividuais.delete(usuario)
    let nomeEntregador = 'Entregador'
    for (const chave of Object.keys(EMPRESA_CONFIG)) {
      for (const reg of (empresas[chave]?.estado?.historicoEntregas || [])) {
        if (jidNormalizedUser(reg.entregadorId || '') === usuario && reg.entregadorNome) { nomeEntregador = reg.entregadorNome; break }
      }
      if (nomeEntregador !== 'Entregador') break
    }
    await enviarTextoCompleto(sock, jid, gerarTextoRelatorioIndividual(usuario, nomeEntregador, periodo))
    return true
  }

  if (!ehInicio && !ehRankingTempo && !ehEscala && !ehOnline && !ehEntrega && !ehTaxas && !ehAdicionarBairro && !ehBairrosSoltos && !ehTabelaPrecosBairro && !ehEditarPrecoBairro && !conversaPrecoPendente && !etapa && !periodoOnlinePendente && !conversasMapeamentoBairroAntigo.has(usuario)) {
    if (textoParecePergunta(obterTexto(msg)) || pareceEnderecoParaMapa(obterTexto(msg))) {
      await sock.sendMessage(jid, { text: 'ℹ️ As perguntas gerais à IA estão temporariamente desativadas. Os comandos normais da Chegô Delivery continuam disponíveis.' })
      return true
    }
    return false
  }

  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    conversasRelatorio.delete(usuario)
    conversasOnlinePeriodo.delete(usuario)
    if (ehInicio || ehRankingTempo || ehEscala || ehOnline || ehEntrega || ehTaxas || ehBairrosSoltos || ehTabelaPrecosBairro || ehEditarPrecoBairro || conversaPrecoPendente || etapa || periodoOnlinePendente) {
      await responderNegacaoAcesso(sock, jid, usuario, perguntaRankingEmpresas ? 'o ranking das empresas' : 'essa consulta administrativa')
      return true
    }
    return false
  }


  // Cadastro interativo da tabela de preços por bairro de origem, iniciado
  // quando ADM envia o nome exato de um bairro no privado.
  if (conversaPrecoPendente) {
    const respostaOriginal = obterTexto(msg).trim()
    const resposta = normalizarTexto(respostaOriginal)
    if (resposta === 'cancelar' || resposta === 'finalizar') {
      conversasTabelaPrecosBairros.delete(usuario)
      if (resposta === 'finalizar') {
        await sock.sendMessage(jid, { text: `✅ Cadastro encerrado. Os preços já informados para saídas de *${conversaPrecoPendente.origem}* foram salvos.` })
      } else {
        await sock.sendMessage(jid, { text: 'Cadastro de preços cancelado. Os valores já confirmados continuam salvos.' })
      }
      return true
    }
    if (conversaPrecoPendente.etapa === 'editar-destinos') {
      const numeros = respostaOriginal.replace(/\be\b/gi, ' ').split(/[\s,;]+/).filter(Boolean).map(x => /^\d+$/.test(x) ? Number(x) : NaN)
      const unicos = [...new Set(numeros)]
      if (!unicos.length || unicos.some(n => !Number.isInteger(n) || n < 1 || n > BAIRROS_PATOS.length)) {
        await sock.sendMessage(jid, { text: 'Informe os números dos bairros que deseja alterar, separados por vírgula. Para cancelar, digite cancelar.' })
        return true
      }
      conversaPrecoPendente.selecionados = unicos.map(n => BAIRROS_PATOS[n - 1])
      conversaPrecoPendente.etapa = 'valor'
      await sock.sendMessage(jid, { text: `💰 Qual o novo preço para ${conversaPrecoPendente.selecionados.map(b => `*${b}*`).join(', ')} saindo de *${conversaPrecoPendente.origem}*? Responda em reais (ex.: *7*).` })
      return true
    }
    if (conversaPrecoPendente.etapa === 'bairros') {
      const numeros = respostaOriginal.replace(/\be\b/gi, ' ').split(/[\s,;]+/).filter(Boolean).map(x => /^\d+$/.test(x) ? Number(x) : NaN)
      const unicos = [...new Set(numeros)]
      const disponiveis = BAIRROS_PATOS.filter(b => !conversaPrecoPendente.preenchidos.includes(b))
      if (!unicos.length || unicos.some(n => !Number.isInteger(n) || n < 1 || n > BAIRROS_PATOS.length)) {
        await sock.sendMessage(jid, { text: `Informe os números dos bairros separados por vírgula (ex.: 1, 3, 6, 7, 8).\n\n${BAIRROS_PATOS.map((b, i) => `${i + 1}. ${b}`).join('\n')}\n\nPara encerrar, digite *finalizar*.` })
        return true
      }
      const selecionados = unicos.map(n => BAIRROS_PATOS[n - 1]).filter(b => !conversaPrecoPendente.preenchidos.includes(b))
      if (!selecionados.length) {
        await sock.sendMessage(jid, { text: 'Esses bairros já foram preenchidos nesta sessão. Escolha bairros restantes ou digite *finalizar*.' })
        return true
      }
      conversaPrecoPendente.selecionados = selecionados
      conversaPrecoPendente.etapa = 'valor'
      await sock.sendMessage(jid, { text: `💰 Qual o valor da entrega saindo de *${conversaPrecoPendente.origem}* para estes bairros?\n\n${selecionados.map(b => `• ${b}`).join('\n')}\n\nResponda somente com o valor em reais (ex.: *7*).` })
      return true
    }
    if (conversaPrecoPendente.etapa === 'valor') {
      const valorTexto = respostaOriginal.replace(/^r\$\s*/i, '').replace(',', '.')
      const valor = Number(valorTexto)
      if (!Number.isFinite(valor) || valor < 0 || valor > 10000 || !/^\d+(?:[.,]\d{1,2})?$/.test(valorTexto)) {
        await sock.sendMessage(jid, { text: 'Informe um valor válido em reais, por exemplo *7* ou *7,50*. Para encerrar, digite *finalizar*.' })
        return true
      }
      for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
        const st = empresas[chaveEmpresa].estado
        if (!st.tabelaPrecosBairros || typeof st.tabelaPrecosBairros !== 'object') st.tabelaPrecosBairros = {}
        if (!st.tabelaPrecosBairros[conversaPrecoPendente.origem] || typeof st.tabelaPrecosBairros[conversaPrecoPendente.origem] !== 'object') st.tabelaPrecosBairros[conversaPrecoPendente.origem] = {}
        for (const destino of conversaPrecoPendente.selecionados) st.tabelaPrecosBairros[conversaPrecoPendente.origem][destino] = Math.round(valor * 100) / 100
      }
      const destinosAtualizados = [...conversaPrecoPendente.selecionados]
      if (conversaPrecoPendente.modoEditar) {
        salvar()
        conversasTabelaPrecosBairros.delete(usuario)
        await sock.sendMessage(jid, { text: `✅ *Preço atualizado*\n\nOrigem: *${conversaPrecoPendente.origem}*\nBairros: ${destinosAtualizados.join(', ')}\nNovo valor: *R$ ${valor.toFixed(2).replace('.', ',')}*` })
        return true
      }
      conversaPrecoPendente.ultimosSelecionados = destinosAtualizados.length
      conversaPrecoPendente.preenchidos.push(...destinosAtualizados)
      conversaPrecoPendente.selecionados = []
      conversaPrecoPendente.etapa = 'bairros'
      salvar()
      const restantes = BAIRROS_PATOS.filter(b => !conversaPrecoPendente.preenchidos.includes(b))
      await sock.sendMessage(jid, { text: `✅ *Tabela de preços atualizada*\n\nOrigem: *${conversaPrecoPendente.origem}*\nDestinos atualizados: ${destinosAtualizados.join(', ') || 'salvos'}\nValor: *R$ ${valor.toFixed(2).replace('.', ',')}*\n\n${restantes.length ? `📍 *BAIRROS RESTANTES*\\n${restantes.map(b => `${BAIRROS_PATOS.indexOf(b) + 1}. ${b}`).join('\n')}\\n\\nEnvie os números separados por vírgula. Para encerrar, digite *finalizar*.` : '✅ Todos os bairros oficiais já foram preenchidos. Cadastro encerrado.'}` })
      if (!restantes.length) {
        await sock.sendMessage(jid, { text: 'Todos os bairros foram preenchidos. A tabela de preços foi salva.' })
        conversasTabelaPrecosBairros.delete(usuario)
      }
      return true
    }
  }
  if (ehEditarPrecoBairro) {
    const tabela = empresas.CHEGO_DELIVERY?.estado?.tabelaPrecosBairros?.[bairroEditarPreco] || {}
    const linhas = BAIRROS_PATOS.map((b, i) => `${i + 1}. ${b} — ${Object.prototype.hasOwnProperty.call(tabela, b) ? `R$ ${Number(tabela[b]).toFixed(2).replace('.', ',')}` : 'sem preço cadastrado'}`)
    conversasTabelaPrecosBairros.set(usuario, { origem: bairroEditarPreco, etapa: 'editar-destinos', selecionados: [], preenchidos: [], ultimosSelecionados: 0, modoEditar: true })
    await sock.sendMessage(jid, { text: `✏️ *EDITAR PREÇOS — ${bairroEditarPreco}*\n\n${linhas.join('\n')}\n\nInforme o número de um ou mais bairros cujo preço deseja alterar.` })
    return true
  }

  if (ehTabelaPrecosBairro) {
    const tabelaAtual = empresas.CHEGO_DELIVERY?.estado?.tabelaPrecosBairros?.[bairroOrigemPreco] || {}
    const preenchidos = BAIRROS_PATOS.filter(b => Object.prototype.hasOwnProperty.call(tabelaAtual, b))
    const restantes = BAIRROS_PATOS.filter(b => !preenchidos.includes(b))
    if (!restantes.length) {
      await sock.sendMessage(jid, { text: `✅ Todos os bairros de destino para saídas de *${bairroOrigemPreco}* já possuem preço cadastrado. Para alterar preços, inicie novamente enviando o nome do bairro de origem.` })
      return true
    }
    conversasTabelaPrecosBairros.set(usuario, { origem: bairroOrigemPreco, etapa: 'bairros', selecionados: [], preenchidos, ultimosSelecionados: 0 })
    await sock.sendMessage(jid, { text: `📍 *TABELA DE PREÇOS*\nOrigem das entregas: *${bairroOrigemPreco}*\n\nSelecione os bairros de destino pelos números abaixo. Pode informar vários, separados por vírgula (ex.: *1, 3, 6, 7 e 8*).\n\n${restantes.map(b => `${BAIRROS_PATOS.indexOf(b) + 1}. ${b}`).join('\n')}\n\nPara encerrar antes de preencher todos, digite *finalizar*.` })
    return true
  }

  if (ehTaxas) {
    const sub = texto.replace(/^(taxas|taxa)\s*/,'').trim();
    if (/^(pago|pagar)\b/.test(sub)) {
      const marcados = obterMarcados(msg).map(jidNormalizedUser).filter(Boolean);
      const alvoTexto = sub.replace(/^(pago|pagar)\s*/,'').replace(/[^0-9@.\-]/g,'').replace(/^@/,'');
      const alvo = marcados[0] || (alvoTexto ? jidNormalizedUser(alvoTexto.includes('@') ? alvoTexto : `${alvoTexto}@s.whatsapp.net`) : '');
      if (!alvo) { await sock.sendMessage(jid,{text:'Use: *taxas pago @entregador* (marque o entregador na mensagem).'}); return true; }
      const semana=inicioSemanaTaxas(new Date()); const hoje=new Date();
      // Durante segunda/terça, a quitação se refere à última semana encerrada; nos demais dias, à semana atual.
      let ref=new Date(semana); if(hoje.getDay()===1 || (hoje.getDay()===2 && hoje.getHours()<18)) ref.setDate(ref.getDate()-7);
      const chave=chaveSemanaTaxas(ref); const est=empresas.CHEGO_DELIVERY.estado; if(!est.taxasSemanais)est.taxasSemanais={}; if(!est.taxasSemanais[chave])est.taxasSemanais[chave]={pagos:{}}; if(!est.taxasSemanais[chave].pagos)est.taxasSemanais[chave].pagos={}; est.taxasSemanais[chave].pagos[alvo]=Date.now();
      // Quitar também todas as semanas vencidas do entregador para liberar o bloqueio por débito acumulado.
      const semanasComDebito=new Set(); for(const k of Object.keys(EMPRESA_CONFIG)) for(const e of (empresas[k]?.estado?.historicoEntregas||[])){if(jidNormalizedUser(e.entregadorId||'')!==alvo)continue;const ts=Number(e.iniciadaEm||e.concluidaEm||0);if(ts)semanasComDebito.add(chaveSemanaTaxas(inicioSemanaTaxas(new Date(ts))));}
      for(const semana of semanasComDebito){if(Date.now()>=prazoTaxas(semana)){if(!est.taxasSemanais[semana])est.taxasSemanais[semana]={pagos:{}};if(!est.taxasSemanais[semana].pagos)est.taxasSemanais[semana].pagos={};est.taxasSemanais[semana].pagos[alvo]=Date.now();}}
      atualizarBloqueiosTaxas();
      for(const k of Object.keys(EMPRESA_CONFIG)){const ee=empresas[k]?.estado;if(!ee)continue; const still=(ee.bloqueiosTaxas||[]).some(x=>jidNormalizedUser(x)===alvo); const escalaAtiva=(ee.bloqueiosAutomaticosEscala||[]).some(x=>jidNormalizedUser(x.id)===alvo&&Number(x.inicio||0)<=Date.now()&&Number(x.ate||0)>Date.now()); if(!still&&!escalaAtiva){ee.bloqueadosSemana=(ee.bloqueadosSemana||[]).filter(x=>jidNormalizedUser(x)!==alvo);}}
      salvar(); await sock.sendMessage(jid,{text:`✅ Pagamento de taxas registrado para @${alvo.split('@')[0]} na semana ${chave.split('-').reverse().join('/')}.`,mentions:[alvo]});
      for(const k of Object.keys(EMPRESA_CONFIG)){ if(empresas[k]?.grupos?.g1) await publicarListaEmpresa(sock,k).catch(()=>{}); } return true;
    }
    const agora=new Date(); let ref=inicioSemanaTaxas(agora); if(agora.getDay()===1 || (agora.getDay()===2 && agora.getHours()<18)) ref.setDate(ref.getDate()-7);
    await enviarTabelaTaxas(sock,jid,chaveSemanaTaxas(ref)); return true;
  }

  if (ehBairrosSoltos) {
    const todosAdicionados = [...new Set(Object.keys(EMPRESA_CONFIG).flatMap(k => (empresas[k]?.estado?.bairrosAdicionados || []).map(String)))];
    const associados = new Set(Object.keys(EMPRESA_CONFIG).flatMap(k => Object.keys(empresas[k]?.estado?.mapeamentosBairrosAntigos || {}).map(normalizarTexto)));
    const soltos = todosAdicionados.filter(nome => !associados.has(normalizarTexto(nome)));
    if (!soltos.length) {
      await sock.sendMessage(jid, { text: '✅ Todos os bairros adicionais já estão associados a um bairro oficial.' });
      return true;
    }
    conversasMapeamentoBairroAntigo.set(usuario, { aguardandoBairroSolto: true, bairrosSoltos: soltos });
    await sock.sendMessage(jid, { text: `📍 *BAIRROS AINDA NÃO ASSOCIADOS*\n\n${soltos.map((b, i) => `${i + 1}. ${b}`).join('\n')}\n\nResponda com o *número* do bairro que deseja associar. Para cancelar, digite *cancelar*.` });
    return true;
  }

  const mapeamentoPendenteAtual = conversasMapeamentoBairroAntigo.get(usuario)
  if (mapeamentoPendenteAtual?.aguardandoBairroSolto) {
    if (normalizarTexto(obterTexto(msg).trim()) === 'cancelar') {
      conversasMapeamentoBairroAntigo.delete(usuario);
      await sock.sendMessage(jid, { text: 'Mapeamento cancelado. Nenhuma associação foi alterada.' });
      return true;
    }
    const n = /^\d+$/.test(obterTexto(msg).trim()) ? Number(obterTexto(msg).trim()) : 0;
    const nome = mapeamentoPendenteAtual.bairrosSoltos[n - 1];
    if (!nome) {
      await sock.sendMessage(jid, { text: `Responda com um número entre 1 e ${mapeamentoPendenteAtual.bairrosSoltos.length}, ou digite *cancelar*.` });
      return true;
    }
    conversasMapeamentoBairroAntigo.set(usuario, { nome });
    await sock.sendMessage(jid, { text: `📍 O bairro escolhido foi *${nome}*.\n\nA qual bairro oficial ele pertence?\n\n${BAIRROS_PATOS.map((b, i) => `${i + 1}. ${b}`).join('\n')}\n\nResponda somente com o *número* do bairro oficial. Para cancelar, digite *cancelar*.` });
    return true;
  }

  const mapeamentoPendente = conversasMapeamentoBairroAntigo.get(usuario)
  if (mapeamentoPendente) {
    if (normalizarTexto(obterTexto(msg).trim()) === 'cancelar') {
      conversasMapeamentoBairroAntigo.delete(usuario)
      await sock.sendMessage(jid, { text: 'Mapeamento cancelado. O bairro adicional continua cadastrado, mas ainda não foi associado a um bairro oficial.' })
      return true
    }
    const respostaBairro = obterTexto(msg).trim()
    const numeroBairro = /^\d+$/.test(respostaBairro) ? Number(respostaBairro) : 0
    const bairroOficial = numeroBairro >= 1 && numeroBairro <= BAIRROS_PATOS.length ? BAIRROS_PATOS[numeroBairro - 1] : null
    if (!bairroOficial) {
      await sock.sendMessage(jid, { text: `Responda somente com o *número* do bairro oficial desejado, ou digite *cancelar* para interromper:\n\n${BAIRROS_PATOS.map((b, i) => `${i + 1}. ${b}`).join('\n')}` })
      return true
    }
    for (const chaveEmpresa of Object.keys(EMPRESA_CONFIG)) {
      const st = empresas[chaveEmpresa].estado
      if (!st.mapeamentosBairrosAntigos || typeof st.mapeamentosBairrosAntigos !== 'object') st.mapeamentosBairrosAntigos = {}
      st.mapeamentosBairrosAntigos[mapeamentoPendente.nome] = bairroOficial
    }
    salvar()
    conversasMapeamentoBairroAntigo.delete(usuario)
    await sock.sendMessage(jid, { text: `✅ O bairro *${mapeamentoPendente.nome}* foi associado a *${bairroOficial}*. Quando aparecer com o nome antigo, o bot vai considerar o bairro oficial.` })
    return true
  }

  if (ehAdicionarBairro) {
    const nomeBairro = String(comandoAdicionarBairro[1] || '').replace(/^[(\[]|[)\]]$/g, '').trim()
    if (!nomeBairro) {
      await sock.sendMessage(jid, { text: 'Use: *Adicionar bairro Nome do Bairro*\nExemplo: *Adicionar bairro Jardim das Flores*' })
      return true
    }
    const resultado = adicionarBairroPatos(nomeBairro)
    if (resultado.ok) {
      conversasMapeamentoBairroAntigo.set(usuario, { nome: resultado.nome })
      await sock.sendMessage(jid, { text: `✅ Bairro *${resultado.nome}* adicionado.\n\nA qual bairro oficial ele pertence? Vou considerar os dois nomes como o mesmo bairro nas entregas.\n\n${BAIRROS_PATOS.map((b, i) => `${i + 1}. ${b}`).join('\n')}\n\nResponda somente com o *número* do bairro oficial escolhido. Para cancelar, digite *cancelar*.` })
    } else if (resultado.motivo === 'existe') {
      await sock.sendMessage(jid, { text: `ℹ️ O bairro *${resultado.nome}* já está na lista.` })
    } else {
      await sock.sendMessage(jid, { text: 'Não consegui adicionar. Informe um nome de bairro com até 80 caracteres.' })
    }
    return true
  }

  if (periodoOnlinePendente && !ehOnline) {
    const periodoEscolhido = ({ '1': 'hoje', 'hoje': 'hoje', '2': 'essa semana', 'essa semana': 'essa semana', 'esta semana': 'essa semana', '3': 'semana passada', 'semana passada': 'semana passada', '4': 'esse mês', 'esse mes': 'esse mês', 'esse mês': 'esse mês' })[texto];
    if (!periodoEscolhido) {
      await enviarTextoCompleto(sock, jid, 'Escolha uma opção válida:\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada');
      return true;
    }
    conversasOnlinePeriodo.delete(usuario);
    const dadosOnline = coletarTempoOnline(periodoEscolhido).map((x, i) => ({ ...x, posicao: i + 1, valor: x.ms / 60000 }));
    const titulosGrafico = { 'hoje': 'HOJE', 'essa semana': 'ESTA SEMANA', 'semana passada': 'SEMANA PASSADA', 'esse mês': 'ESTE MÊS' };
    const enviouOnline = await enviarGraficosRanking(sock, jid, 'TEMPO ONLINE POR ENTREGADOR', `${titulosGrafico[periodoEscolhido]} | TEMPO ACUMULADO`, dadosOnline, v => formatarDuracaoOnline(Number(v) * 60000));
    if (!enviouOnline) await enviarTextoCompleto(sock, jid, gerarRelatorioTempoOnline(periodoEscolhido));
    return true;
  }

  // Registra no Termux a função pedida por ADM no privado, sem expor telefone/JID.
  // Para respostas numéricas dentro de um relatório, registra a etapa atual, não o número digitado.
  const funcaoSolicitada = ehEscala ? 'Escala de fim de semana'
    : ehOnline ? 'Relatório de tempo online'
    : ehEntrega ? 'Tempo médio por entrega'
    : ehRankingTempo ? 'Ranking de tempo médio'
    : ehInicio ? 'Relatório de entregas'
    : etapa ? `Relatório de entregas — ${etapa.etapa || 'continuação'}`
    : texto.slice(0, 80)
  const nomeADM = String(msg.pushName || 'ADM sem nome informado').replace(/[\r\n\t]/g, ' ').trim()
  console.log('\n[ADM — SOLICITAÇÃO PRIVADA]')
  console.log(`Data/Hora: ${new Date().toLocaleString('pt-BR')}`)
  console.log(`ADM: ${nomeADM || 'ADM sem nome informado'}`)
  console.log(`Função: ${funcaoSolicitada}`)
  console.log('Origem: Privado do Bot\n')

  if (ehOnline) {
    conversasOnlinePeriodo.set(usuario, true);
    await enviarTextoCompleto(sock, jid, '🕒 *TEMPO ONLINE*\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada\n4️⃣ Esse mês');
    return true;
  }

  if (ehEntrega || ehRankingTempo) {
    conversasRelatorio.delete(usuario)
    const dadosTempo = coletarRankingTempoMedio()
    const enviouTempo = await enviarGraficosRanking(sock, jid, 'TEMPO MÉDIO POR ENTREGADOR', 'ÚLTIMOS 7 DIAS | MENOR MÉDIA PRIMEIRO', dadosTempo, v => `${Number(v).toFixed(1)} MIN`)
    if (!enviouTempo) await enviarTextoCompleto(sock, jid, gerarRankingTempoMedioEntregadores())
    return true
  }

  if (ehEscala) {
    conversasRelatorio.delete(usuario)
    await enviarTextoCompleto(sock, jid, gerarRelatorioEscalaFimDeSemana())
    return true
  }

  if (ehRankingTempo) {
    conversasRelatorio.delete(usuario)
    const dadosTempo = coletarRankingTempoMedio()
    const enviouTempo = await enviarGraficosRanking(sock, jid, 'TEMPO MÉDIO POR ENTREGADOR', 'ÚLTIMOS 7 DIAS | MENOR MÉDIA PRIMEIRO', dadosTempo, v => `${Number(v).toFixed(1)} MIN`)
    if (!enviouTempo) await enviarTextoCompleto(sock, jid, gerarRankingTempoMedioEntregadores())
    return true
  }

  if (ehInicio) {
    conversasRelatorio.set(usuario, { etapa: 'tipo' })
    await sock.sendMessage(jid, { text: `📊 *RELATÓRIO*\n\n1️⃣ Empresas\n2️⃣ Entregadores\n3️⃣ Tempo médio\n4️⃣ Volume diário\n5️⃣ Tempo online\n6️⃣ Taxas\n7️⃣ Bairros` })
    return true
  }

  if (etapa.etapa === 'tipo') {
    if (texto === '7' || texto === 'bairros' || texto === 'bairro') {
      etapa.tipo = 'bairros'
    } else if (texto === '6' || texto === 'taxas' || texto === 'taxa') {
      let ref=inicioSemanaTaxas(new Date()); const hoje=new Date(); if(hoje.getDay()===1 || (hoje.getDay()===2 && hoje.getHours()<18)) ref.setDate(ref.getDate()-7);
      await enviarTabelaTaxas(sock,jid,chaveSemanaTaxas(ref)); return true;
    } else if (texto === '5' || texto === 'tempo online' || texto === 'online') {
      conversasRelatorio.set(usuario, { etapa: 'periodo_online', tipo: 'tempo_online' })
      await sock.sendMessage(jid, { text: '🕒 *TEMPO ONLINE*\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada\n4️⃣ Esse mês' })
      return true
    } else if (texto === '1' || texto === 'empresas' || texto === 'empresa') {
      etapa.tipo = 'empresas'
    } else if (texto === '2' || texto === 'entregadores' || texto === 'entregador' || texto === 'motoboys') {
      etapa.tipo = 'entregadores'
    } else if (texto === '4' || texto === 'volume diario' || texto === 'volume diário') {
      etapa.tipo = 'volume_diario'
      etapa.etapa = 'periodo'
      conversasRelatorio.set(usuario, etapa)
      await sock.sendMessage(jid, { text: `📅 *VOLUME DIÁRIO*\n\n1️⃣ Essa semana\n2️⃣ Semana passada\n3️⃣ Esse mês\n4️⃣ Mês passado` })
      return true
    } else if (texto === '3' || texto === 'tempo medio' || texto === 'tempo médio' || texto === 'ranking tempo') {
      conversasRelatorio.delete(usuario)
      const dadosTempo = coletarRankingTempoMedio()
      const enviouTempo = await enviarGraficosRanking(sock, jid, 'TEMPO MÉDIO POR ENTREGADOR', 'ÚLTIMOS 7 DIAS | MENOR MÉDIA PRIMEIRO', dadosTempo, v => `${Number(v).toFixed(1)} MIN`)
      if (!enviouTempo) await enviarTextoCompleto(sock, jid, gerarRankingTempoMedioEntregadores())
      return true
    } else {
      await sock.sendMessage(jid, { text: 'Escolha uma opção válida:\n\n1️⃣ Empresas\n2️⃣ Entregadores\n3️⃣ Tempo médio\n4️⃣ Volume diário\n5️⃣ Tempo online\n6️⃣ Taxas\n7️⃣ Bairros' })
      return true
    }
    etapa.etapa = 'periodo'
    conversasRelatorio.set(usuario, etapa)
    await sock.sendMessage(jid, { text: `📅 *ESCOLHA O PERÍODO*\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada\n4️⃣ Últimas 4 semanas` })
    return true
  }

  if (etapa.etapa === 'periodo_online') {
    const mapaOnline = { '1':'hoje', 'hoje':'hoje', '2':'essa semana', 'essa semana':'essa semana', 'esta semana':'essa semana', '3':'semana passada', 'semana passada':'semana passada', '4':'esse mês', 'esse mes':'esse mês', 'esse mês':'esse mês', 'este mes':'esse mês', 'este mês':'esse mês' }
    const periodoOnline = mapaOnline[texto]
    if (!periodoOnline) {
      await sock.sendMessage(jid, { text: 'Escolha um período válido:\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada\n4️⃣ Esse mês' })
      return true
    }
    conversasRelatorio.delete(usuario)
    const dadosOnline = coletarTempoOnline(periodoOnline).map((x, i) => ({ ...x, posicao: i + 1, valor: x.ms / 60000 }))
    const titulosOnline = { 'hoje':'HOJE', 'essa semana':'ESTA SEMANA', 'semana passada':'SEMANA PASSADA', 'esse mês':'ESTE MÊS' }
    const enviouOnline = await enviarGraficosRanking(sock, jid, 'TEMPO ONLINE POR ENTREGADOR', `${titulosOnline[periodoOnline]} | TEMPO ACUMULADO`, dadosOnline, v => formatarDuracaoOnline(Number(v) * 60000))
    if (!enviouOnline) await enviarTextoCompleto(sock, jid, gerarRelatorioTempoOnline(periodoOnline))
    return true
  }

  if (etapa.etapa === 'periodo') {
    const mapa = {
      '1': 'hoje', 'hoje': 'hoje',
      '2': 'essa semana', 'essa semana': 'essa semana', 'esta semana': 'essa semana',
      '3': 'semana passada',
      '4': 'últimas 4 semanas', 'ultimas 4 semanas': 'últimas 4 semanas', 'últimas 4 semanas': 'últimas 4 semanas',
      'esse mês': 'esse mês', 'este mês': 'esse mês', 'mês atual': 'esse mês',
      'mês passado': 'mês passado', 'mes passado': 'mês passado'
    }
    const mapaVolume = { '1':'essa semana', 'essa semana':'essa semana', '2':'semana passada', 'semana passada':'semana passada', '3':'esse mês', 'esse mês':'esse mês', 'este mês':'esse mês', '4':'mês passado', 'mês passado':'mês passado', 'mes passado':'mês passado' }
    const periodo = etapa.tipo === 'volume_diario' ? mapaVolume[texto] : mapa[texto]
    if (!periodo) {
      await sock.sendMessage(jid, { text: etapa.tipo === 'volume_diario' ? 'Escolha um período válido:\n\n1️⃣ Essa semana\n2️⃣ Semana passada\n3️⃣ Esse mês\n4️⃣ Mês passado' : 'Escolha um período válido:\n\n1️⃣ Hoje\n2️⃣ Essa semana\n3️⃣ Semana passada\n4️⃣ Últimas 4 semanas' })
      return true
    }
    if (etapa.tipo === 'volume_diario') {
      conversasRelatorio.delete(usuario)
      const volume = gerarRelatorioVolumeDiario(periodo, new Date())
      const enviouVolume = await enviarGraficosRanking(sock, jid, 'VOLUME DIÁRIO DE ENTREGAS', periodo.toLocaleUpperCase('pt-BR'), volume.linhas, v => `${v} ENTREGAS`, `TOTAL DO PERÍODO: ${volume.linhas.reduce((s,x)=>s+(Number(x.valor)||0),0)} ENTREGAS`)
      if (!enviouVolume) await sock.sendMessage(jid, { text: volume.texto })
      return true
    }
    if (etapa.tipo === 'bairros') {
      const mapaBairros = new Map()
      for (const chave of Object.keys(EMPRESA_CONFIG)) {
        const estB = empresas[chave]?.estado || {}
        const corridas = Array.isArray(estB.corridas) ? estB.corridas : []
        for (const reg of (estB.historicoEntregas || [])) {
          const fim = Number(reg.finalizadaEm || 0)
          if (!fim || !dentroPeriodo(fim, periodo, new Date()) || Number(reg.fracaoTotal || reg.fracaoAtual || 0)) continue
          const corrida = corridas.find(c => String(c.mensagemId || '') === String(reg.mensagemId || ''))
          const bairros = [...new Set([...(corrida?.bairrosIdentificados || []), ...(reg.bairrosIdentificados || []), ...(reg.bairro ? [reg.bairro] : [])].map(String).map(x=>x.trim()).filter(Boolean))]
          for (const bairro of bairros) mapaBairros.set(bairro, (mapaBairros.get(bairro) || 0) + 1)
        }
      }
      const rankingBairros = [...mapaBairros.entries()].map(([nome,valor])=>({nome,valor})).sort((a,b)=>b.valor-a.valor||a.nome.localeCompare(b.nome,'pt-BR')).map((x,i)=>({...x,posicao:i+1}))
      conversasRelatorio.delete(usuario)
      const enviado = rankingBairros.length ? await enviarGraficosRanking(sock, jid, 'ENTREGAS FINALIZADAS POR BAIRRO', periodo.toLocaleUpperCase('pt-BR'), rankingBairros, v => `${v} ENTREGAS`, 'Contagem: somente entregas finalizadas por figurinha; entregas fracionadas são excluídas.') : false
      if (!enviado) await enviarTextoCompleto(sock, jid, `📍 *RANKING DE BAIRROS — ENTREGAS FINALIZADAS*\nPeríodo: *${periodo.toLocaleUpperCase('pt-BR')}*\n\n${rankingBairros.length ? rankingBairros.map(x=>`${x.posicao}. ${x.nome} — ${x.valor}`).join('\n') : 'Nenhuma entrega finalizada por figurinha foi encontrada neste período.'}\n\n*Contagem:* cada entrega finalizada por figurinha vale 1; entregas fracionadas não entram.`)
      return true
    }

    if (etapa.tipo === 'entregadores') {
      const agora = new Date()
      const registros = coletarRegistrosRelatorio(periodo, agora)
      const mapa = new Map()
      for (const reg of registros) {
        const idOriginal = String(reg.entregadorId || reg.entregadorNome || '').trim()
        const id = chaveEntregadorRelatorio(idOriginal, reg.entregadorNome)
        const nome = String(reg.entregadorNome || 'Entregador').trim()
        if (!id) continue
        const item = mapa.get(id) || { id: idOriginal, chave: id, nome, quantidade: 0 }
        item.quantidade += Math.max(1, Number(reg.quantidade) || 1)
        mapa.set(id, item)
      }
      const ranking = [...mapa.values()].sort((a, b) => b.quantidade - a.quantidade || a.nome.localeCompare(b.nome, 'pt-BR'))
      if (!ranking.length) {
        conversasRelatorio.delete(usuario)
        await sock.sendMessage(jid, { text: gerarTextoRelatorio('entregadores', periodo) })
        return true
      }
      conversasRelatorio.set(usuario, { etapa: 'selecionar_entregador', tipo: 'entregadores', periodo, ranking })
      const dadosGrafico = coletarRankingEntregasGrafico('entregadores', periodo)
      const enviouRanking = await enviarGraficosRanking(sock, jid, 'ENTREGAS POR ENTREGADOR', periodo.toLocaleUpperCase('pt-BR'), dadosGrafico, v => `${v} ENTREGAS`, 'Digite o número da posição para abrir o relatório individual. Para sair, digite cancelar.')
      if (!enviouRanking) await sock.sendMessage(jid, { text: gerarTextoRelatorio('entregadores', periodo) })
      return true
    }
    const relatorio = gerarTextoRelatorio(etapa.tipo, periodo)
    conversasRelatorio.delete(usuario)
    const dadosGrafico = coletarRankingEntregasGrafico(etapa.tipo, periodo)
    const enviouRelatorio = await enviarGraficosRanking(sock, jid, etapa.tipo === 'empresas' ? 'ENTREGAS POR EMPRESA' : 'ENTREGAS POR ENTREGADOR', periodo.toLocaleUpperCase('pt-BR'), dadosGrafico, v => `${v} ENTREGAS`)
    if (!enviouRelatorio) await enviarTextoCompleto(sock, jid, relatorio)
    return true
  }
  if (etapa.etapa === 'selecionar_entregador') {
    if (texto === 'cancelar') {
      conversasRelatorio.delete(usuario)
      await sock.sendMessage(jid, { text: 'Seleção do relatório cancelada.' })
      return true
    }
    const numero = Number(texto)
    if (!Number.isInteger(numero) || numero < 1 || numero > etapa.ranking.length) {
      await sock.sendMessage(jid, { text: `Digite um número entre 1 e ${etapa.ranking.length}, conforme o ranking exibido.\nPara cancelar, digite cancelar.` })
      return true
    }
    const selecionado = etapa.ranking[numero - 1]
    const relatorioIndividual = gerarTextoRelatorioIndividual(selecionado.id, selecionado.nome, etapa.periodo)
    const registrosIndividuais = coletarRegistrosRelatorio(etapa.periodo).filter(reg => mesmoEntregadorRelatorio(reg, selecionado))
    const porDia = new Map()
    for (const reg of registrosIndividuais) { const dia=String(reg.data || new Date(reg.instante).toISOString().slice(0,10)); porDia.set(dia,(porDia.get(dia)||0)+Math.max(1,Number(reg.quantidade)||1)) }
    const diasOrdenados = [...porDia.entries()].sort((a,b)=>a[0].localeCompare(b[0]))
    const dadosDia = diasOrdenados.map(([dia,valor],i)=>({nome:dia.split('-').reverse().join('/'),valor,posicao:i+1}))
    const totalIndividual = registrosIndividuais.reduce((soma, reg) => soma + Math.max(1, Number(reg.quantidade) || 1), 0)
    conversasRelatorio.set(usuario, { etapa: 'selecionar_dia_entregador', tipo: 'entregadores', periodo: etapa.periodo, entregador: selecionado, dias: diasOrdenados.map(([data, quantidade], i) => ({ data, quantidade, numero: i + 1 })) })
    const enviouIndividual = await enviarGraficosRanking(sock, jid, `ENTREGAS DIÁRIAS - ${selecionado.nome}`, etapa.periodo.toLocaleUpperCase('pt-BR'), dadosDia, v => `${v} ENTREGAS`, 'Digite o número do dia para ver cada entrega e as mensagens citadas. Para sair, digite cancelar.')
    if (!enviouIndividual) await enviarTextoCompleto(sock, jid, `${relatorioIndividual}

Digite o número do dia para ver os detalhes das entregas. Para sair, digite cancelar.`)
    return true
  }
  if (etapa.etapa === 'selecionar_dia_entregador') {
    if (texto === 'cancelar') {
      conversasRelatorio.delete(usuario)
      await sock.sendMessage(jid, { text: 'Seleção do dia cancelada.' })
      return true
    }
    const numeroDia = Number(texto)
    const diaSelecionado = (etapa.dias || []).find(d => d.numero === numeroDia)
    if (!diaSelecionado) {
      await sock.sendMessage(jid, { text: `Digite o número de um dia exibido no gráfico (1 a ${(etapa.dias || []).length}). Para sair, digite cancelar.` })
      return true
    }
    const idEntregador = String(etapa.entregador?.id || etapa.entregador?.nome || '')
    const eventos = []
    for (const chave of Object.keys(EMPRESA_CONFIG)) {
      const hist = empresas[chave]?.estado?.historicoEntregas || []
      for (const reg of hist) {
        if (String(reg.entregadorId || reg.entregadorNome || '') !== idEntregador) continue
        if (String(reg.data || '') !== diaSelecionado.data) continue
        eventos.push({ ...reg, _empresaChave: chave })
      }
    }
    eventos.sort((a,b)=>Number(a.concluidaEm || a.iniciadaEm || 0)-Number(b.concluidaEm || b.iniciadaEm || 0))
    await sock.sendMessage(jid, { text: `🧾 *DETALHES DAS ENTREGAS*

Entregador: *${etapa.entregador.nome}*
Data: *${diaSelecionado.data.split('-').reverse().join('/')}*
Entregas contabilizadas: *${diaSelecionado.quantidade}*

Cada bloco abaixo tenta citar as mensagens originais no grupo.` })
    if (!eventos.length) {
      await sock.sendMessage(jid, { text: 'Não encontrei referências individuais no histórico para esse dia. Isso pode ocorrer com entregas antigas, registradas antes desta função.' })
    }
    let indiceEntrega = 0
    for (const reg of eventos) {
      indiceEntrega++
      const horario = new Date(Number(reg.concluidaEm || reg.iniciadaEm || 0)).toLocaleTimeString('pt-BR', { hour: '2-digit', minute: '2-digit' })
      await sock.sendMessage(jid, { text: `🛵 *ENTREGA ${indiceEntrega}*
Empresa: *${reg.empresaNome || 'Empresa'}*
Horário registrado: *${horario}*
Quantidade contabilizada nesta solicitação: *${Math.max(1, Number(reg.quantidade) || 1)}*` })
      await enviarReferenciaCitada(sock, jid, reg.mensagemIndoRef, 'Mensagem INDO do entregador')
      const fracoes = Array.isArray(reg.mensagensFracionadasRefs) ? reg.mensagensFracionadasRefs : []
      for (const ref of fracoes) {
        const textoFracao = ref.texto || 'etapa fracionada'
        await enviarReferenciaCitada(sock, jid, ref, `Fracionado — ${textoFracao}`)
      }
      if (reg.mensagemFinalizacaoRef && !fracoes.some(ref => ref.id === reg.mensagemFinalizacaoRef.id)) {
        await enviarReferenciaCitada(sock, jid, reg.mensagemFinalizacaoRef, 'Mensagem de finalização da entrega')
      } else if (reg.fracaoTotal && Number(reg.fracaoAtual) === Number(reg.fracaoTotal) && fracoes.length) {
        // O último estágio fracionado (ex.: 4/4) já é a finalização do lote.
        // Evita enviar a mesma mensagem duas vezes.
      } else {
        await sock.sendMessage(jid, { text: 'Mensagem de finalização não está disponível no histórico desta entrega.' })
      }
    }
    await sock.sendMessage(jid, { text: 'Fim dos detalhes. Digite cancelar para encerrar.' })
    return true
  }
  conversasRelatorio.delete(usuario)
  return false
}

/* =====================================
   VARIAÇÕES DE CONTAGEM — COMANDO ADM NO PRIVADO
===================================== */
async function processarAdicionarAliasPrivado(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const texto = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  const match = texto.match(/^adicionar\s+(indo|offline|online|proximo|final|ocupado|livre|lista)\s+(.+)$/)
  if (!match) return false
  const usuario = jidNormalizedUser(obterId(msg))
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Somente ADM pode cadastrar variações de comandos.' })
    return true
  }
  const tipo = match[1]
  const alias = normalizarTexto(match[2]).replace(/[.!?]+$/g, '').trim()
  if (!alias || alias.length > 40 || /\s/.test(alias)) {
    await sock.sendMessage(jid, { text: 'Use uma única palavra como variação. Exemplo: *Adicionar indo indy*.' })
    return true
  }
  if (!aliasesComandos[tipo]) aliasesComandos[tipo] = []
  if (!aliasesComandos[tipo].includes(alias)) aliasesComandos[tipo].push(alias)
  const listas = { indo: COMANDOS_INDO, offline: COMANDOS_OFF, online: COMANDOS_ON, proximo: COMANDOS_PROXIMO, final: COMANDOS_FINAL, ocupado: COMANDOS_OCUPADO, livre: COMANDOS_LIVRE, lista: COMANDOS_LISTA }
  if (listas[tipo] && !listas[tipo].includes(alias)) listas[tipo].push(alias)
  selecionarEmpresa('CHEGO_DELIVERY')
  salvar()
  await sock.sendMessage(jid, { text: `✅ Variação *${alias}* adicionada ao comando *${tipo}* e salva.` })
  return true
}

async function processarComandoVariacaoPrivado(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!jid.endsWith('@s.whatsapp.net') && !jid.endsWith('@lid')) return false
  const textoOriginal = obterTexto(msg)
  const texto = normalizarTexto(textoOriginal).replace(/[.!?]+$/g, '').trim()
  const match = texto.match(/^variacao\s+(entrega|indo|fracionado)(?:\s+(.+))?$/)
  if (!match) return false

  const usuario = jidNormalizedUser(obterId(msg))
  if (!(await ehADMEmAlgumaEmpresa(sock, usuario))) {
    await sock.sendMessage(jid, { text: '⛔ Somente ADM pode cadastrar variações de contabilização.' })
    return true
  }

  // A configuração é persistida no estado principal CHEGÔ DELIVERY.
  selecionarEmpresa('CHEGO_DELIVERY')
  if (!estado.variacoesEntrega || typeof estado.variacoesEntrega !== 'object') {
    estado.variacoesEntrega = { entrega: false, indo: false, fracionado: false }
  }
  const tipo = match[1]
  estado.variacoesEntrega[tipo] = true
  salvar()

  const exemplos = {
    fracionado: 'Exemplo reconhecido nos grupos das empresas: *1/3✅*. Continua significando 1 entrega concluída de um total de 3.',
    entrega: 'Variação habilitada: frações com o marcador de confirmação, como *1/3 entrega✅*. A contagem continua sendo a fração informada.',
    indo: 'Variação habilitada: *indo✅* será tratado como o comando *indo* já existente, sem criar uma entrega extra.'
  }
  await sock.sendMessage(jid, { text: `✅ *VARIAÇÃO HABILITADA: ${tipo.toLocaleUpperCase('pt-BR')}*\n\n${exemplos[tipo]}\n\nA configuração foi salva.` })
  return true
}

/* =====================================
   CADASTRO COMPLETO + DISPONIBILIDADE DE MOTOBOYS
===================================== */
const cadastrosMotoboyEmAndamento = new Map()
const disparosDisponibilidadeADM = new Map()

function ehMensagemPrivada(jid) {
  const id = String(jid || '')
  return id.endsWith('@s.whatsapp.net') || id.endsWith('@lid')
}

function usuarioJaEstaEmGrupoMotoboy(id) {
  const usuario = jidNormalizedUser(id || '')
  if (!usuario) return false
  return Object.values(empresas || {}).some(empresa => {
    const participantes = empresa?.grupos?.g1Participantes
    return Array.isArray(participantes) && participantes.some(p => jidNormalizedUser(p) === usuario)
  })
}

function obterEstadoChego() {
  if (!empresas.CHEGO_DELIVERY) return null
  return empresas.CHEGO_DELIVERY.estado
}

function cpfValido(cpfEntrada) {
  const cpf = String(cpfEntrada || '').replace(/\D/g, '')
  if (cpf.length !== 11 || /^(\d)\1{10}$/.test(cpf)) return false
  let soma = 0
  for (let i = 0; i < 9; i++) soma += Number(cpf[i]) * (10 - i)
  let dig = (soma * 10) % 11; if (dig === 10) dig = 0
  if (dig !== Number(cpf[9])) return false
  soma = 0
  for (let i = 0; i < 10; i++) soma += Number(cpf[i]) * (11 - i)
  dig = (soma * 10) % 11; if (dig === 10) dig = 0
  return dig === Number(cpf[10])
}

function dataHoraFortaleza() {
  const agora = new Date()
  const partes = new Intl.DateTimeFormat('en-CA', { timeZone: 'America/Fortaleza', year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).formatToParts(agora)
  const o = Object.fromEntries(partes.map(p => [p.type, p.value]))
  return { agora: agora.getTime(), data: `${o.year}-${o.month}-${o.day}`, hora: Number(o.hour), minuto: Number(o.minute) }
}

function dataHoraCadastroFortaleza() {
  return new Intl.DateTimeFormat('pt-BR', {
    timeZone: 'America/Fortaleza', day: '2-digit', month: '2-digit', year: 'numeric',
    hour: '2-digit', minute: '2-digit', hourCycle: 'h23'
  }).format(new Date())
}

function diaSemanaFortaleza() {
  const d = new Intl.DateTimeFormat('en-US', { timeZone: 'America/Fortaleza', weekday: 'long' }).format(new Date()).toLowerCase()
  return ({ monday: 'segunda-feira', tuesday: 'terça-feira', wednesday: 'quarta-feira', thursday: 'quinta-feira', friday: 'sexta-feira', saturday: 'sábado', sunday: 'domingo' })[d] || 'segunda-feira'
}

function periodoAtualFortaleza() {
  const { hora } = dataHoraFortaleza()
  if (hora >= 5 && hora < 12) return 'manhã'
  if (hora >= 12 && hora < 18) return 'tarde'
  return 'noite'
}

function disponibilidadeCorrespondeAoHorario(item, dia, horaAtual, periodoLegado = null) {
  if (!item || normalizarTexto(item.dia) !== normalizarTexto(dia)) return false
  const inicio = Number(item.horaInicio)
  const fim = Number(item.horaFim)
  const inicioValido = item.horaInicio !== null && item.horaInicio !== undefined && item.horaInicio !== '' && Number.isInteger(inicio) && (inicio >= 6 && inicio <= 23 || inicio === 0 || inicio === 1)
  if (inicioValido) {
    const fimValido = item.horaFim !== null && item.horaFim !== undefined && item.horaFim !== '' && Number.isInteger(fim) && (fim >= 6 && fim <= 23 || fim === 0 || fim === 1) && fim !== inicio
    if (!fimValido) return horaAtual >= inicio
    // O intervalo inclui o início e exclui o encerramento; horários após meia-noite
    // são verificados também contra a escala do dia anterior.
    return inicio < fim ? horaAtual >= inicio && horaAtual < fim : horaAtual >= inicio
  }
  return !!periodoLegado && Array.isArray(item.periodos) && item.periodos.some(p => normalizarTexto(p) === normalizarTexto(periodoLegado))
}

function cadastroDisponivelNoHorario(cadastro, dia, horaAtual, periodoLegado = null) {
  const escala = Array.isArray(cadastro?.disponibilidade) ? cadastro.disponibilidade : []
  if (escala.some(d => disponibilidadeCorrespondeAoHorario(d, dia, horaAtual, periodoLegado))) return true
  if (horaAtual >= 2) return false
  const indiceDia = DIAS_DISPONIBILIDADE.findIndex(d => normalizarTexto(d) === normalizarTexto(dia))
  const diaAnterior = DIAS_DISPONIBILIDADE[(indiceDia + DIAS_DISPONIBILIDADE.length - 1) % DIAS_DISPONIBILIDADE.length]
  return escala.some(d => normalizarTexto(d.dia) === normalizarTexto(diaAnterior) && Number.isInteger(Number(d.horaInicio)) && Number.isInteger(Number(d.horaFim)) && Number(d.horaInicio) > Number(d.horaFim) && horaAtual < Number(d.horaFim))
}

function ehAdminPrivadoChego(id) {
  const usuario = jidNormalizedUser(id || '')
  const e = obterEstadoChego()
  return !!usuario && Array.isArray(e?.g1Admins) && e.g1Admins.some(a => jidNormalizedUser(a) === usuario)
}

function ehImagemMensagem(msg) {
  const m = msg?.message || {}
  return !!(m.imageMessage || m.viewOnceMessage?.message?.imageMessage || m.viewOnceMessageV2?.message?.imageMessage || m.documentWithCaptionMessage?.message?.imageMessage)
}

async function salvarFotoCadastro(sock, msg, tipo, usuario) {
  const base = path.join(DATA_DIR, 'cadastros_motoboy_media')
  fs.mkdirSync(base, { recursive: true })
  const buffer = await downloadMediaMessage(msg, 'buffer', {}, { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage })
  if (!Buffer.isBuffer(buffer) || !buffer.length) throw new Error('Imagem vazia')
  const nome = `${usuario.replace(/[^a-zA-Z0-9_-]/g, '_')}_${tipo}_${Date.now()}.jpg`
  const destino = path.join(base, nome)
  fs.writeFileSync(destino, buffer)
  return path.relative(DATA_DIR, destino)
}

const DIAS_DISPONIBILIDADE = ['segunda-feira', 'terça-feira', 'quarta-feira', 'quinta-feira', 'sexta-feira', 'sábado', 'domingo']
const PERIODOS_DISPONIBILIDADE = ['manhã', 'tarde', 'noite']
const ETAPAS_CADASTRO = [
  { id: 'nome', pergunta: '✍️ Informe seu *nome completo*.' },
  { id: 'cpf', pergunta: 'Informe seu *CPF* (somente números ou com pontuação). Ele será validado antes de continuar.' },
  { id: 'nascimento', pergunta: 'Informe sua *data de nascimento* no formato DD/MM/AAAA.' },
  { id: 'telefoneReferencia', pergunta: 'Informe o *telefone de uma pessoa de referência* (com DDD).' },
  { id: 'parentesco', pergunta: 'Qual é o *parentesco ou vínculo* com essa pessoa? (ex.: mãe, pai, cônjuge, irmão, amigo).' },
  { id: 'cidade', pergunta: 'Em qual *cidade* você mora?' },
  { id: 'bairro', pergunta: 'Em qual *bairro* você mora?' },
  { id: 'rua', pergunta: 'Qual é o *nome da rua*?' },
  { id: 'numeroCasa', pergunta: 'Qual é o *número da residência*? Se não tiver, responda *S/N*.' },
  { id: 'tipoResidencia', pergunta: 'Sua residência é *casa* ou *apartamento*? Responda uma das opções.' },
  { id: 'modeloMoto', pergunta: 'Qual é o *modelo da sua moto*?' },
  { id: 'placa', pergunta: 'Informe a *placa da moto*.' },
  { id: 'bag', pergunta: 'Você possui *BAG para entregas*? Responda *SIM* ou *NÃO*.' },
  { id: 'suporteCelular', pergunta: 'Você possui *suporte de celular na moto*? Responda *SIM* ou *NÃO*.' },
  { id: 'carregadorMoto', pergunta: 'Você possui *carregador de celular para a moto*? Responda *SIM* ou *NÃO*.' },
  { id: 'habilitacao', pergunta: 'Você possui *CNH categoria A válida*? Responda *SIM* ou *NÃO*.' },
  { id: 'fotoPerfil', pergunta: 'Envie agora uma *foto de perfil* (imagem pelo WhatsApp).', foto: true },
  { id: 'fotoMoto', pergunta: 'Envie uma *foto da sua moto* (imagem pelo WhatsApp).', foto: true },
  { id: 'dias', pergunta: '📅 *DISPONIBILIDADE SEMANAL HABITUAL*\n\nVamos configurar sua escala que se repete toda semana, perguntando dia por dia. Responda *1 — Sim* se costuma trabalhar nesse dia ou *2 — Não* se não costuma trabalhar. Se responder Sim, vou perguntar a que horas você começa.' }
]

function normalizarDiaDisponibilidade(v) {
  const t = normalizarTexto(String(v || '').trim())
  const aliases = { segunda: 'segunda-feira', seg: 'segunda-feira', terca: 'terça-feira', 'terca-feira': 'terça-feira', ter: 'terça-feira', quarta: 'quarta-feira', qua: 'quarta-feira', quinta: 'quinta-feira', qui: 'quinta-feira', sexta: 'sexta-feira', sex: 'sexta-feira', sabado: 'sábado', sab: 'sábado', domingo: 'domingo', dom: 'domingo' }
  return aliases[t] || DIAS_DISPONIBILIDADE.find(d => normalizarTexto(d) === t) || null
}


const HORARIOS_INICIO_DISPONIBILIDADE = [...Array.from({ length: 18 }, (_, i) => i + 6), 0, 1]

function formatarHoraInicioDisponibilidade(hora) {
  if (hora === null || hora === undefined || hora === '') return 'horário não informado'
  const n = Number(hora)
  if (!Number.isInteger(n) || n < 0 || n > 23) return 'horário não informado'
  return `${String(n).padStart(2, '0')}h`
}

function formatarHorarioDisponibilidade(item) {
  return `das ${formatarHoraInicioDisponibilidade(item?.horaInicio)} às ${formatarHoraInicioDisponibilidade(item?.horaFim)}`
}

function perguntaDiaDisponibilidade(dia) {
  return `📅 *DISPONIBILIDADE — ${dia.toLocaleUpperCase('pt-BR')}*\nVocê costuma trabalhar neste dia da semana?\n\n1️⃣ Sim\n2️⃣ Não\n\nEsta será sua escala semanal habitual. Você poderá informar mudanças a um administrador.`
}

function perguntaHoraInicioDisponibilidade(dia) {
  const opcoes = HORARIOS_INICIO_DISPONIBILIDADE.map((hora, i) => `${i + 1}. ${formatarHoraInicioDisponibilidade(hora)}`).join('\n')
  return `🕒 *HORÁRIO DE INÍCIO — ${dia.toLocaleUpperCase('pt-BR')}*\nA que horas você costuma começar a trabalhar neste dia? Escolha uma opção.\n\n${opcoes}\n\nO horário disponível vai das 6h da manhã até 1h da madrugada.`
}

function perguntaHoraFimDisponibilidade(dia, horaInicio) {
  const opcoes = HORARIOS_INICIO_DISPONIBILIDADE.map((hora, i) => `${i + 1}. ${formatarHoraInicioDisponibilidade(hora)}`).join('\n')
  return `🕘 *HORÁRIO DE ENCERRAMENTO — ${dia.toLocaleUpperCase('pt-BR')}*\nAté que horas você costuma trabalhar neste dia?\nSeu início informado foi às ${formatarHoraInicioDisponibilidade(horaInicio)}. Escolha o horário de encerramento.\n\n${opcoes}\n\nSe trabalhar passando da meia-noite, escolha 00h ou 01h. O horário final não pode ser igual ao início.`
}

function avancarDiaDisponibilidade(c) {
  c.indiceDia++
  if (c.indiceDia >= DIAS_DISPONIBILIDADE.length) return 'revisao'
  return 'dias'
}

function proximaEtapaCadastro(c) {
  const idx = ETAPAS_CADASTRO.findIndex(e => e.id === c.etapa)
  return ETAPAS_CADASTRO[idx + 1]?.id || 'revisao'
}

function resumoCadastroMotoboy(c) {
  const disponibilidade = (c.disponibilidade || []).map(x => `• ${x.dia}: ${formatarHorarioDisponibilidade(x)}`).join('\n') || 'Não informada'
  return `📝 *CONFIRA SEU CADASTRO — CHEGÔ DELIVERY*\n\nNome: ${c.nome || '—'}\nCPF: ${c.cpf || '—'}\nNascimento: ${c.nascimento || '—'}\nTelefone de referência: ${c.telefoneReferencia || '—'}\nVínculo da referência: ${c.parentesco || '—'}\nCidade/bairro: ${c.cidade || '—'} / ${c.bairro || '—'}\nEndereço: ${c.rua || '—'}, ${c.numeroCasa || '—'} — ${c.tipoResidencia || '—'}\nMoto: ${c.modeloMoto || '—'} — ${c.placa || '—'}\nBAG: ${c.bag || '—'} | Suporte de celular: ${c.suporteCelular || '—'} | Carregador: ${c.carregadorMoto || '—'}\nCNH A: ${c.habilitacao || '—'}\n\n📅 *DISPONIBILIDADE SEMANAL HABITUAL*\n${disponibilidade}\n\nSe estiver tudo certo, responda *CONFIRMAR*. Para refazer, responda *RECOMEÇAR*. Para desistir, responda *CANCELAR*.`
}

async function avisarAdministradoresNovoCadastro(sock, cadastro) {
  const e = obterEstadoChego()
  const administradores = [...new Set((e?.g1Admins || []).map(id => jidNormalizedUser(id)).filter(Boolean))]
  const texto = `🆕 *NOVO CADASTRO DE MOTOBOY — PENDENTE*\n\nNome: ${cadastro.nome}\nWhatsApp: ${cadastro.id.split('@')[0]}\nCPF: ${cadastro.cpf}\nCidade/bairro: ${cadastro.cidade} / ${cadastro.bairro}\nMoto: ${cadastro.modeloMoto} — ${cadastro.placa}\nCNH A: ${cadastro.habilitacao}\n\nDisponibilidade:\n${(cadastro.disponibilidade || []).map(x => `• ${x.dia}: ${formatarHorarioDisponibilidade(x)}`).join('\n')}\n\nCadastro salvo. Revise os dados do cadastro antes de aprovar.`
  for (const adminId of administradores) {
    try {
      await sock.sendMessage(adminId, { text: texto })
      for (const campo of ['fotoPerfil', 'fotoMoto']) {
        const rel = cadastro[campo]
        if (rel) {
          const ext = path.extname(rel).toLowerCase()
          const mimetype = ({ '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.png': 'image/png', '.webp': 'image/webp' })[ext] || 'application/octet-stream'
          await sock.sendMessage(adminId, { document: { url: path.join(DATA_DIR, rel) }, fileName: `${cadastro.nome.replace(/[^a-z0-9]/gi,'_')}_${campo}${ext}`, mimetype, caption: `Documento de ${cadastro.nome}: ${campo}` })
        }
      }
    } catch (e) { console.log('Não foi possível avisar administrador sobre cadastro:', e?.message || e) }
  }
}

async function processarCadastroMotoboyPrivado(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const usuario = jidNormalizedUser(jid)
  const texto = String(obterTexto(msg) || '').trim()
  const temImagem = ehImagemMensagem(msg)
  if (!usuario || (!texto && !temImagem)) return false

  const comandoCadastro = normalizarTexto(texto).replace(/[.!?]+$/g, '').trim() === 'cadastro'
  // Para administradores, Cadastro sempre inicia um fluxo novo, inclusive se já houver cadastro salvo ou em andamento.
  if (ehAdminPrivadoChego(usuario) && comandoCadastro) {
    cadastrosMotoboyEmAndamento.set(usuario, { id: usuario, etapa: 'nome', iniciadoEm: Date.now(), criadoEm: new Date().toISOString(), dataHoraCadastro: dataHoraCadastroFortaleza(), disponibilidade: [], frequenciaDisponibilidade: 'semanal', diasSelecionados: [], indiceDia: 0 })
    await sock.sendMessage(jid, { text: `👋 *NOVO CADASTRO DE MOTOBOY — CHEGÔ DELIVERY*\n\nVocê iniciou um novo cadastro. Responda às perguntas uma por vez. Fotos devem ser enviadas como imagem no WhatsApp.\n\nPara desistir, digite *CANCELAR*.\n\n${ETAPAS_CADASTRO[0].pergunta}` })
    return true
  }
  // Administradores continuam usando os demais comandos privados normalmente; Cadastro inicia o fluxo explicitamente.
  if (ehAdminPrivadoChego(usuario) && !cadastrosMotoboyEmAndamento.has(usuario) && !comandoCadastro) return false
  const cAtivo = cadastrosMotoboyEmAndamento.get(usuario)
  if (!cAtivo && !comandoCadastro) return false
  if (!cAtivo && usuarioJaEstaEmGrupoMotoboy(usuario) && !comandoCadastro) return false
  if (!cAtivo) {
    const e = obterEstadoChego()
    const existente = e?.cadastrosMotoboy?.find(x => jidNormalizedUser(x.id) === usuario && x.status !== 'reprovado')
    if (existente) {
      await sock.sendMessage(jid, { text: `Você já possui um cadastro na Chegô Delivery com status *${existente.status || 'pendente'}*. Se precisar atualizar seus dados, fale com um administrador.` })
      return true
    }
    cadastrosMotoboyEmAndamento.set(usuario, { id: usuario, etapa: 'nome', iniciadoEm: Date.now(), criadoEm: new Date().toISOString(), dataHoraCadastro: dataHoraCadastroFortaleza(), disponibilidade: [], frequenciaDisponibilidade: 'semanal', diasSelecionados: [], indiceDia: 0 })
    await sock.sendMessage(jid, { text: `👋 *CADASTRO DE MOTOBOY — CHEGÔ DELIVERY*\n\nVou fazer as perguntas uma por vez. Responda cada mensagem para avançar. Fotos devem ser enviadas como imagem no WhatsApp.\n\nApenas administradores autorizados receberão os dados do cadastro.\n\nPara desistir a qualquer momento, digite *CANCELAR*.\n\n${ETAPAS_CADASTRO[0].pergunta}` })
    return true
  }
  let c = cAtivo
  const tn = normalizarTexto(texto).replace(/[.!?]+$/g, '').trim()
  if (tn === 'cancelar') {
    cadastrosMotoboyEmAndamento.delete(usuario)
    await sock.sendMessage(jid, { text: 'Cadastro cancelado. Se quiser começar novamente, envie uma nova mensagem.' })
    return true
  }
  if (tn === 'recomecar' || tn === 'recomeçar') {
    cadastrosMotoboyEmAndamento.set(usuario, { id: usuario, etapa: 'nome', iniciadoEm: Date.now(), criadoEm: new Date().toISOString(), dataHoraCadastro: dataHoraCadastroFortaleza(), disponibilidade: [], frequenciaDisponibilidade: 'semanal', diasSelecionados: [], indiceDia: 0 })
    await sock.sendMessage(jid, { text: 'Vamos recomeçar. Informe seu *nome completo*.' })
    return true
  }
  if (c.etapa === 'revisao') {
    if (tn !== 'confirmar' && tn !== 'sim') {
      await sock.sendMessage(jid, { text: 'Responda *CONFIRMAR* para enviar o cadastro, *RECOMEÇAR* para refazer ou *CANCELAR* para desistir.' })
      return true
    }
    const chaveDestino = empresas.CHEGO_DELIVERY ? 'CHEGO_DELIVERY' : 'SEU_DELIVERY'
    const anterior = empresaAtual
    selecionarEmpresa(chaveDestino)
    if (!Array.isArray(estado.cadastrosMotoboy)) estado.cadastrosMotoboy = []
    const registro = { ...c, status: 'pendente', enviadoEm: new Date().toISOString() }
    const idCadastro = jidNormalizedUser(c.id || usuario)
    registro.id = idCadastro
    const pos = estado.cadastrosMotoboy.findIndex(x => jidNormalizedUser(x.id) === idCadastro)
    if (pos >= 0) estado.cadastrosMotoboy[pos] = registro; else estado.cadastrosMotoboy.push(registro)
    if (!Array.isArray(estado.cadastrosMotoboyPendentes)) estado.cadastrosMotoboyPendentes = []
    estado.cadastrosMotoboyPendentes = estado.cadastrosMotoboyPendentes.filter(x => jidNormalizedUser(x.id) !== idCadastro)
    estado.cadastrosMotoboyPendentes.push({ id: idCadastro, nome: c.nome, solicitadoEm: Date.now(), status: 'pendente' })
    salvar()
    await avisarAdministradoresNovoCadastro(sock, registro)
    selecionarEmpresa(anterior)
    cadastrosMotoboyEmAndamento.delete(usuario)
    await sock.sendMessage(jid, { text: c.cadastradorId ? `📨 *Cadastro manual enviado para análise!*\n\nCadastro de ${c.nome} (${String(c.id).split('@')[0]}) salvo e enviado aos administradores. Status: *pendente de aprovação*.` : '📨 *Cadastro enviado para análise!*\n\nSeus dados foram registrados e os administradores foram avisados. Seu cadastro está *pendente de aprovação*; você ainda não foi adicionado à fila nem aos grupos de entregadores.' })
    return true
  }

  if (c.etapa === 'horarioDia') {
    const escolha = Number(tn)
    if (!Number.isInteger(escolha) || escolha < 1 || escolha > HORARIOS_INICIO_DISPONIBILIDADE.length) {
      await sock.sendMessage(jid, { text: perguntaHoraInicioDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia]) })
      return true
    }
    const horaEscolhida = HORARIOS_INICIO_DISPONIBILIDADE[escolha - 1]
    if (c.etapa === 'horarioDia') {
      c.horaInicioDiaAtual = horaEscolhida
      c.etapa = 'encerramentoDia'
      cadastrosMotoboyEmAndamento.set(usuario, c)
      await sock.sendMessage(jid, { text: perguntaHoraFimDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia], horaEscolhida) })
      return true
    }
    return true
  }

  if (c.etapa === 'encerramentoDia') {
    const escolha = Number(tn)
    if (!Number.isInteger(escolha) || escolha < 1 || escolha > HORARIOS_INICIO_DISPONIBILIDADE.length) {
      await sock.sendMessage(jid, { text: perguntaHoraFimDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia], c.horaInicioDiaAtual) })
      return true
    }
    const horaFim = HORARIOS_INICIO_DISPONIBILIDADE[escolha - 1]
    if (horaFim === Number(c.horaInicioDiaAtual)) {
      await sock.sendMessage(jid, { text: 'O horário de encerramento não pode ser igual ao início. Escolha outro horário.\n\n' + perguntaHoraFimDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia], c.horaInicioDiaAtual) })
      return true
    }
    c.disponibilidade.push({ dia: DIAS_DISPONIBILIDADE[c.indiceDia], horaInicio: Number(c.horaInicioDiaAtual), horaFim, periodos: [] })
    delete c.horaInicioDiaAtual
    c.indiceDia++
    if (c.indiceDia >= DIAS_DISPONIBILIDADE.length) {
      c.etapa = 'revisao'
      cadastrosMotoboyEmAndamento.set(usuario, c)
      await sock.sendMessage(jid, { text: resumoCadastroMotoboy(c) })
    } else {
      c.etapa = 'dias'
      cadastrosMotoboyEmAndamento.set(usuario, c)
      await sock.sendMessage(jid, { text: perguntaDiaDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia]) })
    }
    return true
  }

  const etapa = ETAPAS_CADASTRO.find(x => x.id === c.etapa)
  if (!etapa) return false
  if (etapa.foto) {
    {
      if (!temImagem) { await sock.sendMessage(jid, { text: 'Preciso receber uma *imagem* nesta etapa. Envie a foto como imagem pelo WhatsApp.' }); return true }
      try { c[c.etapa] = await salvarFotoCadastro(sock, msg, c.etapa, usuario) }
      catch (e) { await sock.sendMessage(jid, { text: 'Não consegui baixar essa imagem. Envie novamente como foto normal do WhatsApp.' }); return true }
    }
  } else {
    if (!texto) { await sock.sendMessage(jid, { text: etapa.pergunta }); return true }
    const valor = texto.replace(/\s+/g, ' ').trim()
    if (c.etapa === 'nome' && (valor.length < 3 || valor.length > 100)) { await sock.sendMessage(jid, { text: 'Informe seu nome completo, com pelo menos 3 caracteres.' }); return true }
    if (c.etapa === 'cpf') {
      if (!cpfValido(valor)) { await sock.sendMessage(jid, { text: '❌ CPF inválido. Confira os números e envie novamente.' }); return true }
      c.cpf = valor.replace(/\D/g, '')
    } else if (c.etapa === 'nascimento') {
      const m = valor.match(/^(\d{2})[\/.-](\d{2})[\/.-](\d{4})$/)
      if (!m || Number(m[1]) < 1 || Number(m[1]) > 31 || Number(m[2]) < 1 || Number(m[2]) > 12 || Number(m[3]) < 1900 || new Date(Number(m[3]), Number(m[2])-1, Number(m[1])).getDate() !== Number(m[1]) || new Date(Number(m[3]), Number(m[2])-1, Number(m[1])) > new Date()) { await sock.sendMessage(jid, { text: 'Data inválida. Use DD/MM/AAAA e informe uma data real no passado.' }); return true }
      c.nascimento = `${m[1]}/${m[2]}/${m[3]}`
    } else if (['bag','suporteCelular','carregadorMoto','habilitacao'].includes(c.etapa)) {
      if (!['sim','nao','não'].includes(tn)) { await sock.sendMessage(jid, { text: 'Responda apenas *SIM* ou *NÃO*.' }); return true }
      c[c.etapa] = tn === 'sim' ? 'sim' : 'não'
    } else if (c.etapa === 'tipoResidencia') {
      if (!['casa','apartamento'].includes(tn)) { await sock.sendMessage(jid, { text: 'Responda *CASA* ou *APARTAMENTO*.' }); return true }
      c.tipoResidencia = tn === 'casa' ? 'Casa' : 'Apartamento'
    } else if (c.etapa === 'telefoneReferencia') {
      const nums = valor.replace(/\D/g, '')
      if (nums.length < 10 || nums.length > 13) { await sock.sendMessage(jid, { text: 'Informe um telefone com DDD, com 10 a 13 dígitos.' }); return true }
      c.telefoneReferencia = nums
    } else {
      c[c.etapa] = valor
    }
  }
  if (c.etapa === 'dias') {
    if (!['1','2','sim','não','nao'].includes(tn)) {
      await sock.sendMessage(jid, { text: perguntaDiaDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia]) }); return true
    }
    if (tn === '1' || tn === 'sim') {
      c.etapa = 'horarioDia'
      cadastrosMotoboyEmAndamento.set(usuario, c)
      await sock.sendMessage(jid, { text: perguntaHoraInicioDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia]) })
      return true
    }
    c.indiceDia++
    if (c.indiceDia >= DIAS_DISPONIBILIDADE.length) {
      if (!c.disponibilidade.length) { c.indiceDia = 0; await sock.sendMessage(jid, { text: 'Selecione pelo menos um dia para trabalhar.\n\n' + perguntaDiaDisponibilidade(DIAS_DISPONIBILIDADE[0]) }); cadastrosMotoboyEmAndamento.set(usuario,c); return true }
      c.etapa = 'revisao'
      cadastrosMotoboyEmAndamento.set(usuario, c)
      await sock.sendMessage(jid, { text: resumoCadastroMotoboy(c) })
      return true
    }
    cadastrosMotoboyEmAndamento.set(usuario, c)
    await sock.sendMessage(jid, { text: perguntaDiaDisponibilidade(DIAS_DISPONIBILIDADE[c.indiceDia]) })
    return true
  }

  const next = proximaEtapaCadastro(c)
  c.etapa = next
  cadastrosMotoboyEmAndamento.set(usuario, c)
  if (next === 'dias') {
    c.indiceDia = 0; c.diasSelecionados = []; c.disponibilidade = []; c.periodosDiaAtual = [];
    cadastrosMotoboyEmAndamento.set(usuario, c)
    await sock.sendMessage(jid, { text: perguntaDiaDisponibilidade(DIAS_DISPONIBILIDADE[0]) })
  } else if (next === 'revisao') {
    await sock.sendMessage(jid, { text: resumoCadastroMotoboy(c) })
  } else {
    const proxima = ETAPAS_CADASTRO.find(x => x.id === next)
    await sock.sendMessage(jid, { text: proxima.pergunta })
  }
  return true
}

async function processarComandoDisponibilidadePrivado(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  if (!ehMensagemPrivada(jid) || msg?.key?.fromMe) return false
  const usuario = jidNormalizedUser(obterId(msg) || jid)
  if (!ehAdminPrivadoChego(usuario)) return false
  const texto = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  if (!texto) return false
  const e = obterEstadoChego()
  if (!e) return false
  if (!Array.isArray(e.cadastrosMotoboy)) e.cadastrosMotoboy = []
  const fluxoAdmin = cadastrosMotoboyEmAndamento.get(usuario)
  if (fluxoAdmin?.etapa === 'adminTelefone') {
    const numero = String(obterTexto(msg) || '').replace(/\D/g, '')
    if (numero.length < 10 || numero.length > 13) { await sock.sendMessage(jid, { text: 'Número inválido. Informe o WhatsApp do motoboy com DDD (10 a 13 dígitos).' }); return true }
    const alvoId = `${numero}@s.whatsapp.net`
    const existente = e.cadastrosMotoboy.find(c => jidNormalizedUser(c.id) === jidNormalizedUser(alvoId) && c.status !== 'reprovado')
    if (existente) { cadastrosMotoboyEmAndamento.delete(usuario); await sock.sendMessage(jid, { text: `Esse telefone já possui cadastro com status *${existente.status || 'pendente'}*. Não criei outro cadastro.` }); return true }
    cadastrosMotoboyEmAndamento.set(usuario, { id: alvoId, cadastradorId: usuario, etapa: 'nome', iniciadoEm: Date.now(), criadoEm: new Date().toISOString(), dataHoraCadastro: dataHoraCadastroFortaleza(), disponibilidade: [], frequenciaDisponibilidade: 'semanal', diasSelecionados: [], indiceDia: 0 })
    await sock.sendMessage(jid, { text: `Cadastro manual iniciado para *${numero}*. Vou fazer as perguntas uma por vez. Envie também as fotos solicitadas.\n\n${ETAPAS_CADASTRO[0].pergunta}\n\nDigite *CANCELAR* para desistir.` })
    return true
  }
  const dia = diaSemanaFortaleza()
  const periodo = periodoAtualFortaleza()
  const horaAtual = dataHoraFortaleza().hora
  if (texto === 'cadastro' && !cadastrosMotoboyEmAndamento.has(usuario)) {
    cadastrosMotoboyEmAndamento.set(usuario, { etapa: 'adminTelefone', iniciadoEm: Date.now() })
    await sock.sendMessage(jid, { text: '📝 *CADASTRO MANUAL DE MOTOBOY*\n\nInforme o número de WhatsApp do motoboy que você vai cadastrar, com DDD. Depois vou perguntar os dados um por um. O cadastro ficará pendente de aprovação.' })
    return true
  }
  if (texto === 'lista de cadastros') {
    // Compara todos os cadastros ativos com os participantes dos grupos de entregadores
    // configurados nas duas empresas. Quem não estiver em nenhum grupo aparece primeiro.
    const cadastros = e.cadastrosMotoboy.filter(c => c && c.id && c.status !== 'reprovado')
    const gruposEntregadores = [...new Set(Object.values(empresas || {})
      .map(emp => String(emp?.grupos?.g1 || '').trim())
      .filter(g => g.endsWith('@g.us')))]
    const participantes = new Set()
    for (const grupoId of gruposEntregadores) {
      try {
        const meta = await sock.groupMetadata(grupoId)
        for (const p of (meta?.participants || [])) {
          const id = jidNormalizedUser(p?.id || p?.jid || '')
          if (id) participantes.add(id)
        }
      } catch (err) {
        console.log(`[LISTA-CADASTROS] Não foi possível consultar participantes de ${grupoId}:`, err?.message || err)
        const emp = Object.values(empresas || {}).find(x => String(x?.grupos?.g1 || '') === grupoId)
        for (const idBruto of (emp?.grupos?.g1Participantes || [])) {
          const id = jidNormalizedUser(idBruto)
          if (id) participantes.add(id)
        }
      }
    }
    const normalizarCadastroId = c => jidNormalizedUser(c?.id || c?.jid || c?.numero || '')
    const foraDosGrupos = cadastros.filter(c => !participantes.has(normalizarCadastroId(c)))
    const nosGrupos = cadastros.filter(c => participantes.has(normalizarCadastroId(c)))
    const mencoes = []
    const linhaCadastro = (c, indice, alerta = false) => {
      const id = normalizarCadastroId(c)
      const numero = String(id || c.id || '').split('@')[0].replace(/\D/g, '')
      if (id && !mencoes.includes(id)) mencoes.push(id)
      const nome = String(c.nome || c.name || 'Entregador').trim()
      return `${indice}. *${nome}* — @${numero}${alerta ? ' 🚨' : ''}`
    }
    const linhasFora = foraDosGrupos.map((c, i) => linhaCadastro(c, i + 1, true))
    const linhasDentro = nosGrupos.map((c, i) => linhaCadastro(c, i + foraDosGrupos.length + 1, false))
    const textoLista = `📋 *LISTA DE CADASTROS — ENTREGADORES*\n\n` +
      `🚨 *CADASTRADOS FORA DOS GRUPOS (${foraDosGrupos.length})*\n` +
      `${linhasFora.length ? linhasFora.join('\n') : 'Nenhum.'}\n\n` +
      `👥 *JÁ ESTÃO NOS GRUPOS (${nosGrupos.length})*\n` +
      `${linhasDentro.length ? linhasDentro.join('\n') : 'Nenhum.'}\n\n` +
      `Total de cadastros listados: *${cadastros.length}*`
    await sock.sendMessage(jid, { text: textoLista, mentions: mencoes })
    return true
  }
  if (texto === 'cadastros pendentes') {
    const pendentes = e.cadastrosMotoboy.filter(c => c.status === 'pendente')
    await sock.sendMessage(jid, { text: pendentes.length ? `📝 *CADASTROS PENDENTES*\n\n${pendentes.map((c,i)=>`${i+1}. ${c.nome} — ${String(c.id).split('@')[0]}\n   ${c.cidade || ''} / ${c.bairro || ''}`).join('\n')}\n\nPara aprovar ou reprovar, use *APROVAR <telefone>* ou *REPROVAR <telefone>*.` : 'Não há cadastros pendentes.' })
    return true
  }
  const acaoCadastro = texto.match(/^(aprovar|reprovar)\s+([+\d()\s-]+)$/)
  if (acaoCadastro) {
    const numero = acaoCadastro[2].replace(/\D/g, '')
    const alvo = e.cadastrosMotoboy.find(c => String(c.id || '').split('@')[0].replace(/\D/g, '').endsWith(numero) && c.status === 'pendente')
    if (!alvo) { await sock.sendMessage(jid, { text: 'Não encontrei cadastro pendente com esse telefone. Consulte *CADASTROS PENDENTES* e tente novamente.' }); return true }
    const empresaAnterior = empresaAtual
    selecionarEmpresa('CHEGO_DELIVERY')
    alvo.status = acaoCadastro[1] === 'aprovar' ? 'aprovado' : 'reprovado'
    alvo.statusAtualizadoEm = new Date().toISOString()
    if (Array.isArray(estado.cadastrosMotoboyPendentes)) {
      const pend = estado.cadastrosMotoboyPendentes.find(x => jidNormalizedUser(x.id) === jidNormalizedUser(alvo.id))
      if (pend) pend.status = alvo.status
    }
    salvar()
    selecionarEmpresa(empresaAnterior)
    try { await sock.sendMessage(alvo.id, { text: alvo.status === 'aprovado' ? '✅ Seu cadastro na Chegô Delivery foi *APROVADO*. Aguarde as orientações dos administradores sobre a entrada no grupo e o início das atividades.' : 'Seu cadastro na Chegô Delivery não foi aprovado neste momento. Para mais informações, entre em contato com um administrador.' }) } catch (err) { console.log('Não foi possível avisar candidato sobre decisão:', err?.message || err) }
    await sock.sendMessage(jid, { text: `Cadastro de *${alvo.nome}* marcado como *${alvo.status.toUpperCase('pt-BR')}*.` })
    return true
  }
  if (texto === 'disponivel' || texto === 'disponiveis') {
    const lista = e.cadastrosMotoboy.filter(c => c.status === 'aprovado' && Array.isArray(c.disponibilidade) && cadastroDisponivelNoHorario(c, dia, horaAtual, periodo))
    const cabecalho = `📋 *MOTOBOYS DISPONÍVEIS — ${dia.toLocaleUpperCase('pt-BR')}*\nHorário atual: ${String(horaAtual).padStart(2, '0')}h (America/Fortaleza)\n\n`
    const corpo = lista.length ? lista.map((c,i)=>`${i+1}. *${c.nome}* — wa.me/${String(c.id).split('@')[0]}\n   ${c.cidade || ''}${c.bairro ? ' / '+c.bairro : ''}`).join('\n') : 'Nenhum motoboy aprovado informou disponibilidade compatível com o horário de início neste dia.'
    await sock.sendMessage(jid, { text: cabecalho + corpo + `\n\nTotal: *${lista.length}*\n\nPara preparar um envio a essa lista, digite *ENVIAR DISPONÍVEIS*.` })
    return true
  }
  if (texto === 'enviar disponiveis' || texto === 'enviar mensagem disponiveis') {
    const destinatarios = e.cadastrosMotoboy.filter(c => c.status === 'aprovado' && Array.isArray(c.disponibilidade) && cadastroDisponivelNoHorario(c, dia, horaAtual, periodo))
    if (!destinatarios.length) { await sock.sendMessage(jid, { text: `Não há motoboys aprovados com início de trabalho até o horário atual em ${dia}. Nenhuma mensagem foi enviada.` }); return true }
    disparosDisponibilidadeADM.set(usuario, { destinatarios: destinatarios.map(c=>c.id), dia, periodo, etapa: 'mensagem' })
    await sock.sendMessage(jid, { text: `Você está prestes a enviar uma mensagem privada para *${destinatarios.length} motoboy(s)* com início de trabalho até o horário atual em *${dia}*.\n\nDigite agora o texto da mensagem que deseja enviar. Digite *CANCELAR* para desistir.` })
    return true
  }
  const pendente = disparosDisponibilidadeADM.get(usuario)
  if (pendente?.etapa === 'mensagem') {
    if (texto === 'cancelar') { disparosDisponibilidadeADM.delete(usuario); await sock.sendMessage(jid, { text: 'Disparo cancelado. Nenhuma mensagem foi enviada.' }); return true }
    pendente.mensagem = String(obterTexto(msg) || '').trim()
    pendente.etapa = 'confirmar'
    disparosDisponibilidadeADM.set(usuario, pendente)
    await sock.sendMessage(jid, { text: `📨 *CONFIRME O DISPARO*\n\nDestinatários: ${pendente.destinatarios.length}\nFiltro: ${pendente.dia}, início de trabalho até o horário atual\n\nMensagem:\n${pendente.mensagem}\n\nResponda *CONFIRMAR ENVIO* para disparar ou *CANCELAR* para abortar.` })
    return true
  }
  if (pendente?.etapa === 'confirmar') {
    if (texto !== 'confirmar envio') { if (texto === 'cancelar') { disparosDisponibilidadeADM.delete(usuario); await sock.sendMessage(jid, { text: 'Disparo cancelado. Nenhuma mensagem foi enviada.' }); return true } await sock.sendMessage(jid, { text: 'Responda *CONFIRMAR ENVIO* ou *CANCELAR*.' }); return true }
    disparosDisponibilidadeADM.delete(usuario)
    let enviadas = 0, falhas = 0
    for (const id of pendente.destinatarios) {
      try { await sock.sendMessage(id, { text: pendente.mensagem }); enviadas++ }
      catch (err) { falhas++; console.log('Falha no disparo para motoboy:', err?.message || err) }
      await new Promise(resolve => setTimeout(resolve, 350))
    }
    await sock.sendMessage(jid, { text: `✅ *DISPARO CONCLUÍDO*\n\nFiltro: ${pendente.dia}, início de trabalho até o horário atual\nEnviadas: ${enviadas}\nFalhas: ${falhas}\nTotal: ${pendente.destinatarios.length}` })
    return true
  }
  return false
}

/* =====================================
   PROCESSAR MENSAGEM
===================================== */

function textoMensagemComando(msg, textoNovo) {
  const copia = { ...msg, message: { ...(msg?.message || {}) } }
  if (Object.prototype.hasOwnProperty.call(copia.message, 'conversation')) copia.message.conversation = textoNovo
  else if (copia.message.extendedTextMessage) copia.message.extendedTextMessage = { ...copia.message.extendedTextMessage, text: textoNovo }
  else copia.message.conversation = textoNovo
  return copia
}

function interpretarComandoNaturalGrupo(textoOriginal) {
  const t = normalizarTexto(textoOriginal).replace(/[.!?,;:]+/g, ' ').replace(/\s+/g, ' ').trim()
  if (/^(?:off|offline)\b/.test(t) || /\b(?:vou|vô|to|estou|irei) (?:almocar|almoçar|comer|descansar|sair|ficar off)\b/.test(t)) return 'off'
  if (/^(?:va|vai|vamos|manda|chama) (?:o )?(?:proximo|prox)\b/.test(t) || /\bproximo entregador\b/.test(t)) return 'proximo'
  return null
}

function textoParecePergunta(texto) {
  const t = normalizarTexto(texto)
  return /\?/.test(String(texto || '')) || /^(?:quant[oa]s?\b|quanto\b|qual\b|quais\b|como\b|por que\b|porque\b|quem\b|me diz\b|me fala\b|voce sabe\b|voces sabem\b|tem como\b)/.test(t)
}

async function responderNegacaoAcesso(sock, jid, usuario, assunto = 'essa informação') {
  const chave = `${jidNormalizedUser(usuario)}:${normalizarTexto(assunto)}`
  const quantidade = (historicoNegacoesAcesso.get(chave) || 0) + 1
  historicoNegacoesAcesso.set(chave, quantidade)
  const resposta = quantidade === 1
    ? `Entendi o que você quer consultar, mas ${assunto} é uma informação de acesso exclusivo dos ADMs. Não consigo mostrar isso por aqui.`
    : `Como eu já te expliquei, ${assunto} é exclusivo dos ADMs. Posso ajudar com informações que estão liberadas para você.`
  await sock.sendMessage(jid, { text: resposta })
}

async function processarMensagemInternaBase(sock, msg) {
  if (!msg.message || msg.key.fromMe) return
  const grupo = msg.key.remoteJid
  const comandoDiagnosticoLista = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  if (COMANDOS_ON.includes(comandoDiagnosticoLista) || COMANDOS_LISTA.includes(comandoDiagnosticoLista)) {
    console.log(`[LISTA-DIAG] Comando recebido: texto=${JSON.stringify(comandoDiagnosticoLista)}; empresa=${empresaDoGrupo(grupo) || empresaAtual}; grupo=${grupo}; g1Atual=${grupos.g1}; ehG1=${mesmoJid(grupo, grupos.g1)}; fromMe=${!!msg.key.fromMe}`)
  }
  const jidComandoPrivado = String(grupo || '')
  const textoComandoPrivado = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  const ehConversaPrivadaComando = jidComandoPrivado.endsWith('@s.whatsapp.net') || jidComandoPrivado.endsWith('@lid')
  if (ehConversaPrivadaComando && (textoComandoPrivado === 'nao apagar mensagens' || textoComandoPrivado === 'apagar mensagens')) {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Esse comando é exclusivo do ADM.' })
      return
    }
    if (textoComandoPrivado === 'nao apagar mensagens') {
      naoApagarMensagensEmpresas = !naoApagarMensagensEmpresas
    } else {
      naoApagarMensagensEmpresas = false
    }
    salvar()
    await sock.sendMessage(grupo, { text: naoApagarMensagensEmpresas
      ? `🛑 *Não apagar mensagens ATIVADO.*\n\nNão apagarei mensagens nos grupos das empresas. Envie novamente *não apagar mensagens* para voltar a apagar.`
      : `🗑️ *Exclusão de mensagens ATIVADA.*\n\nO bot voltou a apagar mensagens conforme as regras normais.` })
    return
  }
  if (await processarConfiguracaoChavesIA(sock, msg)) return
  if (await processarAdicionarVariacoesDicionarioComanda(sock, msg)) return
  if (await processarAdicionarAliasPrivado(sock, msg)) return
  if (await processarComandoVariacaoPrivado(sock, msg)) return
  if (await processarAvisosAdmPrivado(sock, msg)) return
  if (await processarImportacaoExportacao(sock, msg)) return
  const jidPrivadoIA = String(msg.key.remoteJid || '')
  const textoPrivadoIA = String(obterTexto(msg) || '').trim()
  const ehPrivadoIA = jidPrivadoIA.endsWith('@s.whatsapp.net') || jidPrivadoIA.endsWith('@lid')
  if (await processarComandoRemovidos(sock, msg)) return
  if (await processarComandoRemoverComanda(sock, msg)) return
  if (await processarNomeEstabelecimentoPendente(sock, msg)) return
  if (await processarCorrecaoComandaAprendizado(sock, msg)) return
  if (ehPrivadoIA && (textoParecePergunta(textoPrivadoIA) || pareceEnderecoParaMapa(textoPrivadoIA)) && await responderComGeminiNoPrivado(sock, msg)) return
  if (await processarRelatorioPrivado(sock, msg)) return
  if (await processarComandoDisponibilidadePrivado(sock, msg)) return
  if (await processarCadastroMotoboyPrivado(sock, msg)) return
  if (ehPrivadoIA && ehImagemMensagem(msg) && await responderImagemPrivadaComIA(sock, msg)) return

  // O comando literal 'online' só vale nos grupos de entregadores;
  // mensagens privadas com esse comando não alteram o estado do entregador.
  const jidRemoto = String(grupo || '')
  const textoOriginalMensagem = obterTexto(msg)
  const comandoPrivado = normalizarTexto(textoOriginalMensagem).replace(/[.!?]+$/g, '').trim()
  if ((jidRemoto.endsWith('@s.whatsapp.net') || jidRemoto.endsWith('@lid')) && comandoPrivado === 'online') return

  // Conversa natural no grupo de entregadores, sem alterar os comandos literais existentes.
  const chaveGrupoInicial = empresaDoGrupo(grupo)
  const grupoInicialEhEntregadores = !!chaveGrupoInicial && grupo === empresas[chaveGrupoInicial]?.grupos?.g1
  if (grupoInicialEhEntregadores) {
    const textoLista = normalizarTexto(textoOriginalMensagem)
    if (/^(?:como (?:esta|ta|tá) a lista|como esta a lista|a lista esta atualizada|a lista ta atualizada|status da lista)\??$/.test(textoLista)) {
      await sock.sendMessage(grupo, { text: 'Vou atualizar a lista que está sendo exibida agora. 😊' })
      await publicarLista(sock, { forcarAtualizacao: true })
      return
    }
    const comandoNatural = interpretarComandoNaturalGrupo(textoOriginalMensagem)
    if (comandoNatural) msg = textoMensagemComando(msg, comandoNatural)
  }

  const chave = empresaDoGrupo(grupo)
  if (!chave) return
  selecionarEmpresa(chave)

  // "Lista correta": o ADM responde a uma lista antiga/selecionada no grupo G1.
  // O bot restaura a ordem e a composição daquela lista no estado canônico e edita
  // a mensagem de lista atualmente publicada, sem criar uma nova mensagem.
  const textoListaCorreta = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  const ehGrupoEntregadoresListaCorreta = mesmoJid(grupo, empresas[chave]?.grupos?.g1)
  if (ehGrupoEntregadoresListaCorreta && textoListaCorreta === 'lista correta') {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Somente um ADM pode usar *lista correta*.' })
      return
    }

    const contextoListaCorreta = msg?.message?.extendedTextMessage?.contextInfo || {}
    const mensagemListaSelecionada = contextoListaCorreta.quotedMessage || null
    const textoListaSelecionada = String(
      mensagemListaSelecionada?.conversation ||
      mensagemListaSelecionada?.extendedTextMessage?.text ||
      mensagemListaSelecionada?.imageMessage?.caption || ''
    ).trim()
    if (!mensagemListaSelecionada || !/lista online/.test(normalizarTexto(textoListaSelecionada)) || !/@\d{6,}/.test(textoListaSelecionada)) {
      await sock.sendMessage(grupo, { text: '⚠️ Para corrigir, responda diretamente à mensagem da lista que está correta e envie *lista correta*.' })
      return
    }
    const linhasListaSelecionada = textoListaSelecionada.split(/\r?\n/)
    const encontrarLinhaCabecalho = (cabecalho, inicio = 0) => {
      const alvo = normalizarTexto(cabecalho)
      return linhasListaSelecionada.findIndex((linha, indice) => indice >= inicio && normalizarTexto(linha).includes(alvo))
    }
    const contextoDaListaSelecionada = mensagemListaSelecionada?.extendedTextMessage?.contextInfo || {}
    const jidsMencionadosOriginais = Array.isArray(contextoDaListaSelecionada.mentionedJid)
      ? contextoDaListaSelecionada.mentionedJid.map(id => jidNormalizedUser(id)).filter(Boolean)
      : []
    const pessoasConhecidas = [
      ...(estado.entregadores || []), ...(estado.online || []), ...(estado.espera || [])
    ]
    const digitosJid = valor => String(valor || '').split('@')[0].split(':')[0].replace(/\D/g, '')
    const idPorToken = new Map()
    const tokensMencionados = [...textoListaSelecionada.matchAll(/@(\d{6,})/g)].map(m => m[1])
    tokensMencionados.forEach((numero, indice) => {
      const porJidDaCitacao = jidsMencionadosOriginais.find(id => digitosJid(id) === numero)
      const idConhecido = pessoasConhecidas.find(p => {
        const id = p?.id || p?.jid || p?.phoneNumber || p?.numero || ''
        return digitosJid(id) === numero || String(p?.telefone || p?.phone || '').replace(/\D/g, '') === numero
      })
      // A lista original pode guardar um JID LID; nesse caso a lista de menções
      // da própria mensagem citada mantém o vínculo entre o @número e o JID real.
      const idMencaoAlinhada = jidsMencionadosOriginais[indice] || ''
      const id = porJidDaCitacao || idConhecido?.id || idConhecido?.jid || idConhecido?.phoneNumber || idMencaoAlinhada
      if (id) idPorToken.set(numero, jidNormalizedUser(id))
    })

    const extrairIdsSecao = (cabecalho, proximosCabecalhos = []) => {
      const inicio = encontrarLinhaCabecalho(cabecalho)
      if (inicio < 0) return []
      let fim = linhasListaSelecionada.length
      for (const proximoCabecalho of proximosCabecalhos) {
        const posFim = encontrarLinhaCabecalho(proximoCabecalho, inicio + 1)
        if (posFim >= 0 && posFim < fim) fim = posFim
      }
      const ids = []
      for (const linha of linhasListaSelecionada.slice(inicio + 1, fim)) {
        const m = linha.match(/^\s*\d+\s*[-.)]\s*@?(\d{6,})(?:\s|$)/)
        const mBloqueado = linha.match(/^\s*@?(\d{6,})\s*$/)
        const numero = m?.[1] || mBloqueado?.[1]
        if (!numero) continue
        const id = idPorToken.get(numero)
        if (id && !ids.includes(id)) ids.push(id)
      }
      return ids
    }

    const idsOnlineCorreta = extrairIdsSecao('LISTA ONLINE', ['LISTA DE ESPERA', 'BLOQUEADOS SEG - TER - QUA', 'BLOQUEADOS POR UMA SEMANA', 'Mantenha a bateria'])
    const idsEsperaCorreta = extrairIdsSecao('LISTA DE ESPERA', ['BLOQUEADOS SEG - TER - QUA', 'BLOQUEADOS POR UMA SEMANA', 'Mantenha a bateria'])
    const idsBloqueadosCorreta = extrairIdsSecao('BLOQUEADOS SEG - TER - QUA', ['BLOQUEADOS POR UMA SEMANA', 'Mantenha a bateria'])
    const idsBloqueadosSemanaCorreta = extrairIdsSecao('BLOQUEADOS POR UMA SEMANA', ['Mantenha a bateria'])
    const idsNaMensagem = tokensMencionados.map(n => idPorToken.get(n)).filter(Boolean)
    if (!idsOnlineCorreta.length && !idsEsperaCorreta.length && !idsBloqueadosCorreta.length && !idsBloqueadosSemanaCorreta.length) {
      await sock.sendMessage(grupo, { text: '⚠️ Não consegui identificar os entregadores nessa lista selecionada. Nenhuma alteração foi feita.' })
      return
    }
    if (idsNaMensagem.length < tokensMencionados.length) {
      await sock.sendMessage(grupo, { text: '⚠️ Não consegui associar todos os entregadores da lista selecionada aos cadastros. Nenhuma alteração foi feita.' })
      return
    }

    const mapaPessoas = new Map()
    for (const pessoa of pessoasConhecidas) {
      const id = jidNormalizedUser(pessoa?.id || pessoa?.jid || pessoa?.phoneNumber || '')
      if (id) mapaPessoas.set(id, pessoa)
    }
    const restaurarPessoas = ids => ids.map(id => {
      const existente = mapaPessoas.get(jidNormalizedUser(id))
      if (existente) return { ...existente, id: jidNormalizedUser(id) }
      const cadastro = registrarEntregador(id, 'Entregador')
      return { ...(cadastro || {}), id: jidNormalizedUser(id), nome: cadastro?.nome || 'Entregador' }
    })
    estado.online = restaurarPessoas(idsOnlineCorreta)
    estado.espera = restaurarPessoas(idsEsperaCorreta).filter(p => !estado.online.some(o => jidNormalizedUser(o.id) === jidNormalizedUser(p.id)))
    estado.bloqueados = idsBloqueadosCorreta
    estado.bloqueadosSemana = idsBloqueadosSemanaCorreta
    sincronizarFilaCompartilhadaComLista()
    salvar()

    const sucessoListaCorreta = await publicarLista(sock, {
      permitirCriarSeSemReferencia: true,
      apenasEditarExistente: true,
      naoPromoverEspera: true,
      naoAjustarLimiteFila: true,
      forcarAtualizacao: true
    })
    if (sucessoListaCorreta) {
      await sock.sendMessage(grupo, { text: '✅ *Lista corrigida.* Editei a lista publicada para usar a ordem da mensagem selecionada.' })
      console.log(`[LISTA-CORRETA] Estado restaurado por ADM; empresa=${chave}; grupo=${grupo}; online=${idsOnlineCorreta.length}; espera=${idsEsperaCorreta.length}`)
    } else {
      await sock.sendMessage(grupo, { text: '⚠️ Restaurei a ordem selecionada no estado da fila, mas não consegui confirmar a edição da mensagem da lista. Confira os logs do servidor.' })
    }
    return
  }

  // Em mensagens de pedido nos grupos das empresas, extrai o logradouro sem
  // confundir bairro, cidade, quadra ou lote com o endereço pesquisado no Maps.
  // Aceita tanto "Endereço: Rua..." quanto "Endereço" seguido na próxima linha.
  const textoPedidoMapa = String(obterTexto(msg) || '')
  if (grupo === empresas[chave]?.grupos?.g2 && textoPedidoMapa.length <= 12000) {
    const linhasPedidoMapa = textoPedidoMapa.split(/\r?\n/).map(l => l.trim()).filter(Boolean)
    let indiceEndereco = -1
    let enderecoInline = ''
    for (let i = 0; i < linhasPedidoMapa.length; i++) {
      const m = linhasPedidoMapa[i].match(/^(?:📍\s*)?(?:endere[cç]o(?: de entrega)?|local de entrega)\s*[:：-]\s*(.*)$/i)
      if (m) { indiceEndereco = i; enderecoInline = (m[1] || '').trim(); break }
      if (/^(?:endere[cç]o(?: de entrega)?|local de entrega)\s*$/i.test(linhasPedidoMapa[i])) {
        indiceEndereco = i; enderecoInline = ''; break
      }
    }
    if (indiceEndereco >= 0) {
      let enderecoPedido = enderecoInline
      if (!enderecoPedido) {
        for (let i = indiceEndereco + 1; i < linhasPedidoMapa.length; i++) {
          const linha = linhasPedidoMapa[i].replace(/^📍\s*/, '').trim()
          if (!linha) continue
          // Uma linha com bairro conhecido, cidade ou condomínio nunca é o logradouro.
          const linhaSemCidade = linha.replace(/\s*[-,]\s*(?:patos|patos\s*[-/]\s*pb|pb)\s*$/i, '').trim()
          const bairroConhecido = (typeof BAIRROS_PATOS !== 'undefined' ? BAIRROS_PATOS : []).some(b => normalizarTexto(linhaSemCidade) === normalizarTexto(b))
          if (bairroConhecido || /^(?:cliente|telefone|whats(?:app)?|pagamento|forma de pagamento|pedido|itens|produtos|bairro|cidade|cep)\s*[:：-]/i.test(linha)) break
          enderecoPedido = linha
          break
        }
      }
      enderecoPedido = String(enderecoPedido || '').replace(/[|]+$/g, '').trim()
      enderecoPedido = enderecoPedido.replace(/\s+(?:cliente|telefone|whats(?:app)?|pagamento|forma de pagamento|pedido|itens|produtos|bairro|cidade|cep)\s*[:：-].*$/i, '').trim()
      // Retira indicações de quadra/lote: são campos separados, não logradouro.
      enderecoPedido = enderecoPedido.replace(/\s*[,;]?[ ]*(?:n[º°.]?\s*q(?:uadra)?|quadra|qd\.?|q\.)\s*[:#º°.-]*\s*[a-z0-9-]+/ig, '').trim()
      enderecoPedido = enderecoPedido.replace(/\s*[,;]?[ ]*(?:lote|lt\.?)\s*[:#º°.-]*\s*[a-z0-9-]+/ig, '').trim()
      // Remove bairro/localidade mesmo quando o OCR mistura na mesma linha do endereço.
      // Inclui nomes oficiais, bairros adicionados, aliases e nomes antigos mapeados pelo ADM.
      const nomesBairroParaRemover = new Set([
        ...(typeof listarBairrosPatos === 'function' ? listarBairrosPatos() : (typeof BAIRROS_PATOS !== 'undefined' ? BAIRROS_PATOS : [])),
        ...Object.entries(typeof ALIASES_BAIRROS_PATOS !== 'undefined' ? ALIASES_BAIRROS_PATOS : {}).filter(([oficial]) => (typeof BAIRROS_PATOS !== 'undefined' ? BAIRROS_PATOS : []).some(b => normalizarTexto(b) === normalizarTexto(oficial))).flatMap(([, aliases]) => aliases || []),
        ...Object.keys(EMPRESA_CONFIG || {}).flatMap(k => Object.keys(empresas[k]?.estado?.mapeamentosBairrosAntigos || {}))
      ].map(x => String(x || '').trim()).filter(x => x.length >= 3))
      const padraoFlexivelBairro = nome => {
        const base = normalizarTexto(nome).replace(/[^a-z0-9]+/g, ' ').trim()
        if (!base) return ''
        const classes = { a: '[aáàâãä]', e: '[eéèêë]', i: '[iíìîï]', o: '[oóòôõö]', u: '[uúùûü]', c: '[cç]' }
        return base.split(/\s+/).map(p => [...p].map(ch => classes[ch] || ch.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('')).join('\\s+')
      }
      for (const nomeBairro of nomesBairroParaRemover.sort((a, b) => b.length - a.length)) {
        const padrao = padraoFlexivelBairro(nomeBairro)
        if (!padrao) continue
        const reBairro = new RegExp(`(?<![\\p{L}\\p{N}])${padrao}(?![\\p{L}\\p{N}])`, 'giu')
        enderecoPedido = enderecoPedido.replace(reBairro, ' ')
      }
      // Remove cidade e separadores que podem sobrar depois da retirada do bairro.
      enderecoPedido = enderecoPedido.replace(/\s*[-,;]\s*(?:patos(?:\s*[-/]\s*pb)?|pb)\s*$/i, '').trim()
      enderecoPedido = enderecoPedido.replace(/\s{2,}/g, ' ').replace(/\s*[,;]\s*[,;]+\s*/g, ', ').replace(/^\s*[,;:-]+|[,;:-]+\s*$/g, '').trim()
      enderecoPedido = enderecoPedido.replace(/\s*[,;]?[ ]*(?:sem número|sem numero|s\s*[/.-]?n)\s*$/i, '').trim()
      enderecoPedido = enderecoPedido.replace(/\s*[,;]+\s*$/g, '').trim()
      if (enderecoPedido.length >= 6 && enderecoPedido.length <= 240) {
        const consultaMaps = `${enderecoPedido}, Patos, PB`
        const urlMapaPedido = `https://www.google.com/maps/search/?api=1&query=${encodeURIComponent(consultaMaps)}`
        await sock.sendMessage(grupo, { text: `📍 *Endereço identificado:*
${enderecoPedido}

🗺️ *Abrir no Google Maps:*
${urlMapaPedido}` })
        return
      }
    }
  }

  const comandoGrupo = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim();

  // Novo dispatcher dos comandos do grupo de entregadores. Comandos antigos
  // que não fazem parte da lista aprovada deixam de ser executados. A rotina
  // de processamento de entregas do grupo das empresas (g2) permanece intacta.
  if (mesmoJid(grupo, grupos.g1) && obterTexto(msg).trim()) {
    const textoComandoNovo = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
    const comandoNovo = textoComandoNovo.replace(/@\S+/g, '').replace(/\s+/g, ' ').trim()
    const temMencaoNovo = obterMarcados(msg).length > 0
    const comandoPermitidoNovo = ehComandoPendencia(obterTexto(msg)) || /^(?:on|online|off|offline|final|ultimo|proximo|prox|ocupado|livre|🟢|🔴|limpar listas|limpar lista|limpar status|limpar bloqueados|limpar lista de bloqueados|limpar espera|limpar fila de espera|suporte|bloqueado|bloqueado por uma semana|desbloqueado|desbloquear|lista|lista correta|indo|indio|indi|indu|horario de pico|feriado|fim feriado|silencio|desfazer|lista limite|limpar limite|pendencia|escala|escalados|justificado|justificado sabado|justificado domingo|escalado|folguista|sem escala|cafe com leite)$/.test(comandoNovo) ||
      Object.values(aliasesComandos || {}).some(lista => Array.isArray(lista) && lista.includes(comandoNovo)) ||
      (temMencaoNovo && (/^(?:on|online|off|offline|\d+|proximo|prox|final|ultimo|ocupado|livre|🟢|🔴|limite \d+|limpar limite|bloqueado|bloqueado por uma semana|desbloqueado|desbloquear|justificado|justificado sabado|justificado domingo|escalado|folguista|sem escala|cafe com leite)$/.test(comandoNovo) || Object.values(aliasesComandos || {}).some(lista => Array.isArray(lista) && lista.includes(comandoNovo))))
    if (!comandoPermitidoNovo) {
      if (textoParecePergunta(obterTexto(msg))) {
        const pergunta = normalizarTexto(obterTexto(msg))
        if (/\b(?:ranking|classificacao|top)\b/.test(pergunta) && /\bempresas?\b/.test(pergunta)) {
          const ehAdmConsulta = await ehADM(sock, msg)
          if (!ehAdmConsulta) await responderNegacaoAcesso(sock, grupo, obterId(msg), 'o ranking das empresas')
          else await sock.sendMessage(grupo, { text: 'Claro! O ranking das empresas é uma consulta administrativa. Me chame no privado com *relatório* para abrir as opções de relatório.' })
        } else {
          // Mensagens/perguntas fora dos comandos reconhecidos não recebem resposta automática.
          return
        }
      }
      return
    }
  }

  // Comandos de política da escala: somente ADM no grupo de entregadores CHEGÔ DELIVERY.
  if (chave === 'CHEGO_DELIVERY' && mesmoJid(grupo, grupos.g1) && await processarComandoPoliticaEscala(sock, msg, grupo, comandoGrupo)) return;

  // Escalas manuais: ADM marca o entregador e escreve, por exemplo, '@entregador escalado'.
  if (chave === 'CHEGO_DELIVERY' && await registrarEscalaManual(sock, msg, grupo)) return;

  // Lembrete privado para todos os participantes registrados na escala deste fim de semana.
  if (chave === 'CHEGO_DELIVERY' && mesmoJid(grupo, grupos.g1) && comandoGrupo === 'escalados') {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Somente ADM pode usar o comando *Escalados*.' });
      return;
    }

    const estadoEscala = empresas.CHEGO_DELIVERY?.estado;
    const escalaAtual = estadoEscala?.escalaFimDeSemana || {};
    const chaveFimSemana = chaveSabadoEscala(new Date());
    // Aceita a escala já publicada para o próximo fim de semana também.
    // Isso é necessário quando o comando Escala é usado no sábado para montar a escala do sábado seguinte.
    const escalaTemDataValida = typeof escalaAtual.dataSabado === 'string' && /^\d{4}-\d{2}-\d{2}$/.test(escalaAtual.dataSabado) && escalaAtual.dataSabado >= chaveFimSemana;
    if (!escalaTemDataValida || !Array.isArray(escalaAtual.entregadores) || escalaAtual.entregadores.length === 0) {
      await sock.sendMessage(grupo, { text: '⚠️ Não encontrei uma escala válida para este ou para o próximo final de semana. Publique a escala primeiro com o comando *Escala*.' });
      return;
    }

    const mensagemEscalados = 'Passando para lembrar que você está escalado para este final de semana\n\nContamos com a participação de todos\n\nAtt. Administração';
    const destinatariosEscala = [...new Set(escalaAtual.entregadores.map(p => jidNormalizedUser(p?.id || p?.phoneNumber || '')).filter(id => id && id.includes('@')))];
    let enviadosEscala = 0;
    let falhasEscala = 0;
    for (const destinatario of destinatariosEscala) {
      try {
        await sock.sendMessage(destinatario, { text: mensagemEscalados });
        enviadosEscala++;
      } catch (erro) {
        falhasEscala++;
        console.log(`Falha ao enviar lembrete de escala para ${destinatario}:`, erro.message);
      }
    }
    await sock.sendMessage(grupo, { text: `📨 *Lembrete da escala enviado.*\nMensagens enviadas: ${enviadosEscala}\nFalhas: ${falhasEscala}` });
    return;
  }

  // Suporte: somente ADM no grupo de entregadores CHEGÔ DELIVERY.
  // Envia a mensagem de apoio no privado de todos os entregadores cadastrados.
  if (chave === 'CHEGO_DELIVERY' && mesmoJid(grupo, grupos.g1) && comandoGrupo === 'suporte') {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Somente ADM pode usar o comando *Suporte*.' });
      return;
    }

    const estadoSuporte = empresas.CHEGO_DELIVERY?.estado;
    const idsOnlineSuporte = new Set((estadoSuporte?.online || []).map(p => jidNormalizedUser(p?.id || p?.phoneNumber || '')).filter(Boolean));
    const destinatariosSuporte = [...new Set((estadoSuporte?.entregadores || [])
      .map(p => jidNormalizedUser(p?.id || p?.phoneNumber || ''))
      .filter(id => id && (id.endsWith('@s.whatsapp.net') || id.endsWith('@lid')) && !idsOnlineSuporte.has(id)))];
    const mensagemSuporte = '🚨 *ALTA DEMANDA* 🚨\n\nEstamos com uma demanda muito alta no momento, muita entrega para pouco entregador\n\nSe puder entrar nem que seja só pra dar uma ajuda, já agradecemos\n\n*Att. Administração*';
    let enviadosSuporte = 0;
    let falhasSuporte = 0;
    for (const destinatario of destinatariosSuporte) {
      try {
        await sock.sendMessage(destinatario, { text: mensagemSuporte });
        enviadosSuporte++;
      } catch (erro) {
        falhasSuporte++;
        console.log(`Falha ao enviar mensagem de suporte para ${destinatario}:`, erro?.message || erro);
      }
    }
    await sock.sendMessage(grupo, { text: `📨 *Mensagem de suporte enviada.*\nMensagens enviadas: ${enviadosSuporte}\nFalhas: ${falhasSuporte}\nTotal de entregadores cadastrados: ${destinatariosSuporte.length}` });
    return;
  }

  // Escala automática: somente ADM no grupo de entregadores CHEGÔ DELIVERY.
  if (chave === 'CHEGO_DELIVERY' && mesmoJid(grupo, grupos.g1) && comandoGrupo === 'escala') {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Somente ADM pode publicar a escala.' });
      return;
    }
    await gerarEscalaAutomaticaGrupo(sock, grupo);
    return;
  }

  // Os comandos antigos de métricas no grupo foram desativados para que
  // "online" seja exclusivamente o comando de entrada na lista, conforme as novas regras.

  // Limpeza administrativa: remove as listas de bloqueados e a lista ONLINE desta empresa.
  // A lista de espera, taxas, históricos e demais dados são preservados.
  if (mesmoJid(grupo, grupos.g1) && comandoGrupo === 'limpar listas') {
    if (!(await ehADM(sock, msg))) {
      await sock.sendMessage(grupo, { text: '⛔ Somente ADM pode usar o comando *Limpar listas*.' });
      return;
    }

    finalizarTodasSessoesOnline();
    estado.online = [];
    estado.espera = [];
    estado.bloqueados = [];
    estado.bloqueadosSemana = [];
    estado.bloqueiosAutomaticosEscala = [];
    estado.bloqueiosTaxas = [];
    sincronizarFilaCompartilhadaComLista();
    // A limpeza altera diretamente a fila única em empresa.estado.
    salvar();
    console.log(`[LISTA-LIMPEZA] limpar listas aplicado | empresa=${empresaAtual} | online=${estado.online.length} | espera=${estado.espera.length} | fonte=empresa.estado`);

    await publicarLista(sock, { forcarAtualizacao: true, naoPromoverEspera: true, naoAjustarLimiteFila: true });
    await sock.sendMessage(grupo, { text: '✅ *Listas limpas!*\n\nLista ONLINE, fila de espera e listas de bloqueados foram zeradas. O histórico de entregas foi preservado.' });
    return;
  }

  // O comando manual Lista é a exceção intencional à edição da mensagem atual:
  // deve publicar uma nova lista mesmo quando o conteúdo não mudou. Isso também
  // recupera a operação quando a referência antiga aponta para uma mensagem que
  // o WhatsApp já não permite editar. A nova chave retornada passa a ser a única
  // referência canônica para as próximas atualizações automáticas.
  if (mesmoJid(grupo, grupos.g1) && COMANDOS_LISTA.includes(normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim())) {
    if (!(await ehADM(sock, msg))) return
    const publicada = await publicarListaEmpresaNoEstadoDoGrupo(sock, empresaAtual, 'g1', {
      forcarAtualizacao: true,
      forcarNova: true,
      permitirCriarSeSemReferencia: true
    })
    if (!publicada) {
      console.error(`[LISTA] Comando manual Lista não conseguiu publicar. empresa=${empresaAtual}; grupo=${grupo}`)
    }
    return
  }

  // Pendência pode ser acionada em qualquer grupo cadastrado da empresa.
  // Envia o alerta privado somente se quem digitou for ADM daquele grupo.
  if (await processarComandoPendencia(sock, msg, grupo)) return

  // Nos dois grupos de entregadores, áudio de não-ADM é apagado.
  // Áudios enviados por ADM continuam normalmente.
  if (mesmoJid(grupo, grupos.g1) && await apagarAudioSeNaoADM(sock, msg)) {
    return
  }

  if (mesmoJid(grupo, grupos.g1)) {
    await processarGrupoMotoboy(sock, msg)
    return
  }

  if (mesmoJid(grupo, grupos.g2)) {
    await processarDelivery(sock, msg)
    return
  }
}


/* =====================================
   SINCRONIZAR LISTA APÓS COMANDOS DO GRUPO MOTOBOY
===================================== */

function comandoGrupoMotoboySolicitaAtualizacaoLista(msg, grupo, chaveEmpresa) {
  if (!msg?.message || msg?.key?.fromMe || !chaveEmpresa) return false
  const grupoEntregadores = empresas[chaveEmpresa]?.grupos?.g1
  if (!grupoEntregadores || grupo !== grupoEntregadores) return false

  const texto = normalizarTexto(obterTexto(msg)).replace(/[.!?]+$/g, '').trim()
  if (!texto) return false
  const comando = texto.replace(/@\S+/g, '').replace(/\s+/g, ' ').trim()
  const mencoes = obterMarcados(msg)

  const comandosOnlineOffline = new Set([
    ...COMANDOS_ON.map(normalizarTexto),
    ...COMANDOS_OFF.map(normalizarTexto),
    ...COMANDOS_INDO.map(normalizarTexto)
  ])
  if (comandosOnlineOffline.has(texto) || comandosOnlineOffline.has(comando) || Object.values(aliasesComandos || {}).some(lista => Array.isArray(lista) && (lista.includes(texto) || lista.includes(comando)))) return true

  // Comandos operacionais e administrativos reconhecidos no grupo de entregadores.
  if (/^(?:ocupado|livre|🟢|🔴|lista(?:\s+.*)?|horario de pico|silencio|desfazer|final|ultimo|prox|proxim|proximoo|prossimo|prossimu|prochimo|prochimu|prosim|prosimu|procsimo|feriado|fim feriado|limpar lista|limpar fila de espera|limpar espera|limpar status|limpar lista de bloqueados|limpar bloqueados|desbloquear|desbloqueado|desbloqueia|desqueado|bloqueado(?:\s+por\s+uma\s+semana)?|limpar limite|lista limite|limite\s+\d+|escala(?:\s+.*)?|relatorios?|online|entrega|pendencia|justificado(?:\s+sabado|\s+domingo)?|folguista|sem escala|cafe com leite|escalado)$/u.test(comando)) return true

  // Comandos que exigem mencionar um entregador, como @entregador 2 ou @entregador ocupado.
  if (mencoes.length && (
    /^\d+$/.test(comando) ||
    /^(?:on|off|ocupado|livre|🟢|🔴|final|ultimo|proximo|prox|limpar status|limpar bloqueados|limite(?:\s+\d+)?|limpar limite|desbloquear|desbloqueado|desbloqueia|desqueado|bloqueado(?:\s+por\s+uma\s+semana)?|justificado(?:\s+sabado|\s+domingo)?|folguista|sem escala|cafe com leite|escalado)$/.test(comando)
  )) return true

  // Variações permitidas pelas rotinas de escala e de status, inclusive quando
  // há texto extra do ADM acompanhando a menção.
  if (mencoes.length && /\b(?:justificado|folguista|sem escala|cafe com leite|escalado|limite|ocupado|livre|bloqueado|desbloquear)\b/.test(comando)) return true
  return false
}

// Isola os comandos operacionais por grupo, mantendo separados online/espera,
// desfazer, último snapshot, lista publicada e estado de horário de pico.
const CAMPOS_ESTADO_POR_GRUPO = ['online', 'espera', 'undoADM', 'historicoUndoLista', 'ultimoSnapshotUndoLista', 'rotaAtiva', 'feriado', 'silencio', 'corridas', 'contadorCorrida', 'entregasAceitas']
function assinaturaEstadoVisivelLista() {
  return JSON.stringify({
    online: estado.online || [],
    espera: estado.espera || [],
    entregadores: (estado.entregadores || []).map(p => ({ id: p.id, nome: p.nome, statusOperacional: p.statusOperacional, statusManual: p.statusManual, ativo: p.ativo })),
    bloqueados: estado.bloqueados || [],
    bloqueadosSemana: estado.bloqueadosSemana || [],
    listaSuspensaPico,
    listaSuspensaADM
  })
}
async function processarMensagemInterna(sock, msg) {
  const jid = String(msg?.key?.remoteJid || '')
  const chaveEmpresa = empresaDoGrupo(jid)
  const ehGrupo = !!chaveEmpresa && jid.endsWith('@g.us')

  // No privado, transforma um telefone enviado isoladamente em link wa.me.
  if (!ehGrupo && (jid.endsWith('@s.whatsapp.net') || jid.endsWith('@lid')) && msg?.message && !msg.key?.fromMe) {
    const textoTelefone = String(obterTexto(msg) || '').trim()
    const candidato = textoTelefone.replace(/[()\s.-]/g, '')
    if (/^0800\d{6,7}$/.test(candidato.replace(/\D/g, ''))) {
      await sock.sendMessage(jid, { text: `☎️ *Telefone:* ${textoTelefone}` })
      return
    }
    if (/^\+?\d{8,15}$/.test(candidato) && !/[a-z]/i.test(candidato)) {
      let digitos = candidato.replace(/\D/g, '')
      if (digitos.startsWith('00')) digitos = digitos.slice(2)
      if (digitos.startsWith('55')) {
        // Mantém o código do país quando já informado.
      } else if (digitos.length === 8 || digitos.length === 9) {
        digitos = '5583' + digitos
      } else if (digitos.length === 10 || digitos.length === 11) {
        if (!digitos.startsWith('83')) digitos = '83' + digitos
        digitos = '55' + digitos
      }
      if (/^55\d{10,11}$/.test(digitos)) {
        await sock.sendMessage(jid, { text: `📲 *Link do WhatsApp:*
https://wa.me/${digitos}` })
        return
      }
    }
  }

  if (!ehGrupo) return await processarMensagemInternaBase(sock, msg)
  selecionarEmpresa(chaveEmpresa)
  const empresa = empresas[chaveEmpresa]
  const chaveGrupo = mesmoJid(empresa?.grupos?.g1, jid) ? 'g1' : 'g2'
  if (!empresa.estadosPorGrupo || typeof empresa.estadosPorGrupo !== 'object') empresa.estadosPorGrupo = {}
  if (!empresa.estadosPorGrupo[chaveGrupo]) empresa.estadosPorGrupo[chaveGrupo] = {}
  const escopo = empresa.estadosPorGrupo[chaveGrupo]
  // Fila única e canônica: ambos os grupos leem e alteram empresa.estado.
  // estadosPorGrupo mantém exclusivamente metadados de publicação/configuração.
  const camposFilaCompartilhada = new Set(['online', 'espera'])
  const estadoBase = {}
  for (const campo of CAMPOS_ESTADO_POR_GRUPO) {
    estadoBase[campo] = estado[campo]
    if (camposFilaCompartilhada.has(campo)) {
      if (!Array.isArray(empresa.estado[campo])) empresa.estado[campo] = []
      estado[campo] = structuredClone(empresa.estado[campo])
      continue
    }
    if (escopo[campo] === undefined) escopo[campo] = structuredClone(estado[campo])
    estado[campo] = structuredClone(escopo[campo])
  }
  const metaCampos = ['ultimaListaPublicada', 'ultimaListaEnviada', 'ultimaListaMensagemKey', 'ultimaListaPublicadaEm', 'listaSuspensaPico', 'listaSuspensaADM', 'bloquearPicoAutomatico', 'statusPicoAnterior']
  const metaAtual = { ultimaListaPublicada, ultimaListaEnviada, ultimaListaMensagemKey, ultimaListaPublicadaEm, listaSuspensaPico, listaSuspensaADM, bloquearPicoAutomatico, statusPicoAnterior }
  const metaBase = {}
  const metaEscopoNoInicio = {}
  for (const campo of metaCampos) {
    metaBase[campo] = campo === 'statusPicoAnterior' ? structuredClone(statusPicoAnterior || {}) : metaAtual[campo]
    if (escopo[campo] === undefined) escopo[campo] = structuredClone(metaBase[campo])
    // Fotografa o valor realmente guardado neste grupo antes de processar a
    // mensagem. Rotinas aninhadas podem publicar/editar uma lista e salvar uma
    // referência nova em estadosPorGrupo.g1 enquanto este handler ainda está ativo.
    metaEscopoNoInicio[campo] = structuredClone(escopo[campo])
  }
  ultimaListaPublicada = escopo.ultimaListaPublicada || ''
  ultimaListaEnviada = escopo.ultimaListaEnviada || ''
  ultimaListaMensagemKey = escopo.ultimaListaMensagemKey || null
  ultimaListaPublicadaEm = Number(escopo.ultimaListaPublicadaEm) || 0
  listaSuspensaPico = !!escopo.listaSuspensaPico
  listaSuspensaADM = !!escopo.listaSuspensaADM
  bloquearPicoAutomatico = !!escopo.bloquearPicoAutomatico
  statusPicoAnterior = structuredClone(escopo.statusPicoAnterior || {})
  const assinaturaListaAntes = assinaturaEstadoVisivelLista()
  let listaFoiAlterada = false
  try {
    return await processarMensagemInternaBase(sock, msg)
  } finally {
    for (const campo of CAMPOS_ESTADO_POR_GRUPO) {
      if (camposFilaCompartilhada.has(campo)) {
        // Grava uma única vez no estado-base da empresa; não cria cópia em g1/g2.
        empresa.estado[campo] = structuredClone(estado[campo])
        estadoBase[campo] = empresa.estado[campo]
      } else {
        escopo[campo] = structuredClone(estado[campo])
      }
      estado[campo] = estadoBase[campo]
    }
    // Sincroniza somente os campos cujo escopo não foi alterado por uma rotina
    // aninhada. Antes, um comando `Lista` publicava uma mensagem e gravava sua
    // nova chave em estadosPorGrupo.g1; ao voltar para cá, os globais restaurados
    // ainda continham a chave antiga e a sobrescreviam. O bot então tentava editar
    // uma mensagem antiga em vez da última publicada.
    const metaGlobalsAoFinal = {
      ultimaListaPublicada,
      ultimaListaEnviada,
      ultimaListaMensagemKey,
      ultimaListaPublicadaEm,
      listaSuspensaPico,
      listaSuspensaADM,
      bloquearPicoAutomatico,
      statusPicoAnterior: structuredClone(statusPicoAnterior || {})
    }
    for (const campo of metaCampos) {
      const valorInicio = JSON.stringify(metaEscopoNoInicio[campo] === undefined ? null : metaEscopoNoInicio[campo])
      const valorEscopoAtual = JSON.stringify(escopo[campo] === undefined ? null : escopo[campo])
      if (valorEscopoAtual === valorInicio) {
        escopo[campo] = structuredClone(metaGlobalsAoFinal[campo])
      } else {
        console.log(`[LISTA-REF] Mantendo metadado atualizado durante rotina aninhada | empresa=${chaveEmpresa} | grupo=${chaveGrupo} | campo=${campo}`)
      }
    }
    listaFoiAlterada = assinaturaListaAntes !== assinaturaEstadoVisivelLista()
    ultimaListaPublicada = metaBase.ultimaListaPublicada
    ultimaListaEnviada = metaBase.ultimaListaEnviada
    ultimaListaMensagemKey = metaBase.ultimaListaMensagemKey
    ultimaListaPublicadaEm = metaBase.ultimaListaPublicadaEm
    listaSuspensaPico = metaBase.listaSuspensaPico
    listaSuspensaADM = metaBase.listaSuspensaADM
    bloquearPicoAutomatico = metaBase.bloquearPicoAutomatico
    statusPicoAnterior = metaBase.statusPicoAnterior
    salvar()

    // Reconciliação pós-processamento: muitos comandos de estado alteram a fila
    // ou as entregas antes de persistir o escopo. As chamadas de edição feitas
    // dentro do handler podiam renderizar um estado transitório e não a fila já
    // consolidada. Depois de salvar, recalcula a lista de g1 no estado canônico
    // e edita a mesma mensagem apenas se o texto visível mudou. Não cria lista.
    if (listaFoiAlterada && !msg?.key?.fromMe && chaveEmpresa && sock?.sendMessage && conectadoWhatsApp) {
      try {
        await publicarListaEmpresaNoEstadoDoGrupo(sock, chaveEmpresa, 'g1', {
          apenasEditarExistente: true,
          forcarAtualizacao: true,
          somenteSeTextoMudou: true
        })
      } catch (erroEdicaoPosProcessamento) {
        console.error(`[LISTA] Falha na sincronização pós-processamento; empresa=${chaveEmpresa}; grupo=${chaveGrupo}:`, erroEdicaoPosProcessamento?.message || erroEdicaoPosProcessamento)
      }
    }
  }
}

// O módulo usa contexto global (empresaAtual/estado/grupos). Serializar TODAS as
// mensagens recebidas impede que dois handlers carreguem snapshots simultâneos e
// que o último a terminar sobrescreva uma alteração mais recente.
let filaProcessamentoMensagens = Promise.resolve()
async function processarMensagem(sock, msg) {
  // Não sincronizar/publicar a lista como efeito colateral de toda mensagem.
  // A rotina interna já atualiza a lista nos comandos/eventos que realmente mudam a fila.
  // Mensagens comuns, conversas e textos sem comando não devem gerar listas.
  const executar = () => processarMensagemInterna(sock, msg)
  const resultado = filaProcessamentoMensagens.then(executar, executar)
  filaProcessamentoMensagens = resultado.then(() => undefined, erro => {
    console.error('[FILA-MENSAGENS] Falha no processamento serializado:', erro?.stack || erro)
  })
  return resultado
}


/* =====================================
   ENCONTRAR OS GRUPOS
===================================== */

async function encontrarGrupos(sock) {
  inicializarEmpresas()

  const chaves = Object.keys(EMPRESA_CONFIG)
  const campos = ['g1', 'g2']
  const jidValido = id => typeof id === 'string' && id.endsWith('@g.us')
  // Normalização tolerante a acentos, espaços duplicados e emojis decorativos.
  // Mantém a seleção restrita aos quatro nomes definidos em EMPRESA_CONFIG.
  const nomeNormalizado = nome => String(nome || '')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toUpperCase()
    .replace(/[^A-Z0-9]/g, '')

  // Primeiro, reutiliza os JIDs já salvos. Assim, nas inicializações normais,
  // o bot consulta somente os quatro grupos configurados, sem enumerar todos
  // os grupos em que o WhatsApp participa.
  let idsSalvosCompletos = chaves.every(chave =>
    campos.every(campo => jidValido(empresas[chave]?.grupos?.[campo]))
  )

  if (idsSalvosCompletos) {
    try {
      for (const chave of chaves) {
        const cfg = EMPRESA_CONFIG[chave]
        const g = empresas[chave].grupos
        const metaG1 = await sock.groupMetadata(g.g1)
        const metaG2 = await sock.groupMetadata(g.g2)

        // Confirma que os IDs salvos ainda correspondem aos nomes esperados.
        if (
          nomeNormalizado(metaG1?.subject) !== nomeNormalizado(cfg.g1Nome) ||
          nomeNormalizado(metaG2?.subject) !== nomeNormalizado(cfg.g2Nome)
        ) {
          idsSalvosCompletos = false
          break
        }

        g.g1Participantes = (metaG1.participants || [])
          .map(p => jidNormalizedUser(p.id)).filter(Boolean)
        empresas[chave].estado.g1Admins = (metaG1.participants || [])
          .filter(p => p.admin === 'admin' || p.admin === 'superadmin')
          .map(p => jidNormalizedUser(p.id)).filter(Boolean)
      }

      if (idsSalvosCompletos) {
        console.log('Grupos configurados: 4 (busca direta pelos IDs salvos)')
        for (const chave of chaves) {
          const cfg = EMPRESA_CONFIG[chave], g = empresas[chave].grupos
          console.log(`${cfg.nome} | ${cfg.g1Nome}:`, g.g1 ? 'OK' : 'NÃO ENCONTRADO')
          console.log(`${cfg.nome} | ${cfg.g2Nome}:`, g.g2 ? 'OK' : 'NÃO ENCONTRADO')
        }
        // Preserve os IDs validados: selecionarEmpresa salva o contexto atual,
        // então a referência global de grupos deve apontar para o mapa recém-validado.
        grupos = empresas[empresaAtual]?.grupos || grupos
        selecionarEmpresa(empresaAtual)
        salvar()
        return
      }
    } catch (erro) {
      // Se um ID salvo não puder ser consultado, tenta redescobrir os grupos.
      console.log('Não foi possível validar os IDs salvos; procurando os grupos configurados uma vez.')
    }
  }

  // Busca geral apenas como recuperação inicial, quando faltam IDs salvos ou
  // quando algum ID não corresponde mais ao grupo configurado.
  const todos = await sock.groupFetchAllParticipating()
  for (const chave of chaves) {
    empresas[chave].grupos = { g1: null, g2: null, g1Participantes: [] }
  }

  const nomesAlvo = new Map()
  for (const chave of chaves) {
    const cfg = EMPRESA_CONFIG[chave]
    nomesAlvo.set(nomeNormalizado(cfg.g1Nome), { chave, campo: 'g1' })
    nomesAlvo.set(nomeNormalizado(cfg.g2Nome), { chave, campo: 'g2' })
  }

  for (const id in todos) {
    const alvo = nomesAlvo.get(nomeNormalizado(todos[id].subject))
    if (!alvo) continue
    const { chave, campo } = alvo
    empresas[chave].grupos[campo] = id
    if (campo === 'g1') {
      empresas[chave].grupos.g1Participantes = (todos[id].participants || [])
        .map(p => jidNormalizedUser(p.id)).filter(Boolean)
      empresas[chave].estado.g1Admins = (todos[id].participants || [])
        .filter(p => p.admin === 'admin' || p.admin === 'superadmin')
        .map(p => jidNormalizedUser(p.id)).filter(Boolean)
    }
  }

  console.log('Grupos configurados: 4 (somente os nomes cadastrados são usados pelo bot)')
  for (const chave of chaves) {
    const cfg = EMPRESA_CONFIG[chave], g = empresas[chave].grupos
    console.log(`${cfg.nome} | ${cfg.g1Nome}:`, g.g1 ? 'OK' : 'NÃO ENCONTRADO')
    console.log(`${cfg.nome} | ${cfg.g2Nome}:`, g.g2 ? 'OK' : 'NÃO ENCONTRADO')
  }
  // Não deixe o contexto global antigo sobrescrever os grupos recém-encontrados.
  grupos = empresas[empresaAtual]?.grupos || grupos
  selecionarEmpresa(empresaAtual)
  salvar()
}


/* =====================================
   ALERTA ENTREGA PENDENTE
===================================== */

async function verificarCorrida(
  sock,
  opcoes = {}
) {

  // Encerra automaticamente a janela da rota após 60 segundos.
  if (
    estado.rotaAtiva &&
    Date.now() >= Number(estado.rotaAtiva.expiraEm || 0)
  ) {
    const rotaEncerrada = estado.rotaAtiva
    console.log(
      `ROTA ENCERRADA: ${rotaEncerrada.entregadorNome} | ${rotaEncerrada.empresaNome}`
    )

    // O fim da janela da rota não altera a posição do entregador.
    estado.rotaAtiva = null
    salvar()
  }

  if (
    !estado.corridas ||
    estado.corridas.length === 0
  ) {

    return
  }

  const agora =
    Date.now()

  /*
    Cada entrega possui
    seu próprio prazo.

    Isso permite que várias
    entregas aguardem ao mesmo
    tempo sem uma substituir
    a outra.
  */

  for (
    const corrida of estado.corridas
  ) {

    /*
      DESCARTAR PENDÊNCIA APÓS 1 HORA
    */

    if (agora - Number(corrida.inicio || agora) >= 60 * 60 * 1000) {
      console.log('Corrida pendente descartada após 1 hora:', corrida.id)
      const indice = estado.corridas.indexOf(corrida)
      if (indice !== -1) estado.corridas.splice(indice, 1)
      salvar()
      continue
    }

    /*
      PRAZO DOS 2 MINUTOS
    */

    if (
      !corrida.disputa &&
      prazoDeDisputaAtingido(corrida, agora)
    ) {
      await processarPerdaDeVez(sock, corrida, opcoes)
    }

    /*
      APÓS 2 MINUTOS
      DE DISPUTA
    */

    if (
      corrida.disputa &&
      corrida.alertaInicio &&
      corrida.alertasEnviados < 3
    ) {

      const doisMinutos =
        2 * 60 * 1000

      const passou =
        agora -
        corrida.alertaInicio

      if (
        passou >= doisMinutos
      ) {
        // O alerta de entrega pendente foi removido.
        // A corrida continua registrada normalmente.
      }
    }
  }
}

/* =====================================
   RECONCILIAÇÃO DAS CORRIDAS NO ESCOPO g2
===================================== */
async function verificarCorridasEmpresaNoGrupoDePedidos(sock, chaveEmpresa) {
  const empresa = empresas?.[chaveEmpresa]
  if (!empresa?.grupos?.g2) return false
  const contextoAnterior = {
    empresaAtual, estado, grupos, ultimaListaPublicada, ultimaListaEnviada,
    ultimaListaMensagemKey, ultimaListaPublicadaEm, listaSuspensaPico,
    listaSuspensaADM, bloquearPicoAutomatico, statusPicoAnterior
  }
  const estadoBase = empresa.estado || estadoVazio()
  const escopoLista = empresa.estadosPorGrupo?.g1 || (empresa.estadosPorGrupo.g1 = {})
  const escopoPedidos = empresa.estadosPorGrupo?.g2 || (empresa.estadosPorGrupo.g2 = {})
  let mudou = false
  try {
    empresaAtual = chaveEmpresa
    grupos = empresa.grupos
    estado = { ...estadoBase }
    for (const campo of CAMPOS_ESTADO_POR_GRUPO) {
      const fonte = ['online', 'espera'].includes(campo) ? escopoLista : escopoPedidos
      if (fonte[campo] === undefined) fonte[campo] = structuredClone(estadoBase[campo])
      estado[campo] = structuredClone(fonte[campo])
    }
    // O controle de pico e a referência da lista pertencem ao g1; a fila é
    // compartilhada, mas corridas/entregas aceitas são processadas no g2.
    ultimaListaPublicada = escopoLista.ultimaListaPublicada || ''
    ultimaListaEnviada = escopoLista.ultimaListaEnviada || ''
    ultimaListaMensagemKey = escopoLista.ultimaListaMensagemKey || null
    ultimaListaPublicadaEm = Number(escopoLista.ultimaListaPublicadaEm) || 0
    listaSuspensaPico = !!escopoLista.listaSuspensaPico
    listaSuspensaADM = !!escopoLista.listaSuspensaADM
    bloquearPicoAutomatico = !!escopoLista.bloquearPicoAutomatico
    statusPicoAnterior = structuredClone(escopoLista.statusPicoAnterior || {})

    const antes = JSON.stringify({ corridas: estado.corridas || [], online: estado.online || [], espera: estado.espera || [] })
    await verificarCorrida(sock, { publicarLista: false })
    const depois = JSON.stringify({ corridas: estado.corridas || [], online: estado.online || [], espera: estado.espera || [] })
    mudou = antes !== depois
  } finally {
    for (const campo of CAMPOS_ESTADO_POR_GRUPO) {
      const destino = ['online', 'espera'].includes(campo) ? escopoLista : escopoPedidos
      destino[campo] = structuredClone(estado[campo])
      if (['online', 'espera'].includes(campo)) estadoBase[campo] = structuredClone(estado[campo])
    }
    // Persistir a empresa a partir do estado-base, nunca da cópia temporária g2.
    empresa.estado = estadoBase
    estado = estadoBase
    grupos = empresa.grupos
    ultimaListaPublicada = escopoLista.ultimaListaPublicada || ''
    ultimaListaEnviada = escopoLista.ultimaListaEnviada || ''
    ultimaListaMensagemKey = escopoLista.ultimaListaMensagemKey || null
    ultimaListaPublicadaEm = Number(escopoLista.ultimaListaPublicadaEm) || 0
    listaSuspensaPico = !!escopoLista.listaSuspensaPico
    listaSuspensaADM = !!escopoLista.listaSuspensaADM
    bloquearPicoAutomatico = !!escopoLista.bloquearPicoAutomatico
    statusPicoAnterior = structuredClone(escopoLista.statusPicoAnterior || {})
    salvar()
    empresaAtual = contextoAnterior.empresaAtual
    estado = contextoAnterior.estado
    grupos = contextoAnterior.grupos
    ultimaListaPublicada = contextoAnterior.ultimaListaPublicada
    ultimaListaEnviada = contextoAnterior.ultimaListaEnviada
    ultimaListaMensagemKey = contextoAnterior.ultimaListaMensagemKey
    ultimaListaPublicadaEm = contextoAnterior.ultimaListaPublicadaEm
    listaSuspensaPico = contextoAnterior.listaSuspensaPico
    listaSuspensaADM = contextoAnterior.listaSuspensaADM
    bloquearPicoAutomatico = contextoAnterior.bloquearPicoAutomatico
    statusPicoAnterior = contextoAnterior.statusPicoAnterior
  }
  if (mudou) {
    await publicarListaEmpresaNoEstadoDoGrupo(sock, chaveEmpresa, 'g1', {
      apenasEditarExistente: true,
      forcarAtualizacao: true
    })
  }
  return mudou
}

/* =====================================
   PÁGINA WEB DE CADASTRO DE MOTOBOYS
===================================== */
function responderJsonCadastro(res, status, objeto) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff' })
  res.end(JSON.stringify(objeto))
}

function validarDataNascimentoCadastro(valor) {
  const m = String(valor || '').match(/^(\d{2})\/(\d{2})\/(\d{4})$/)
  if (!m) return false
  const dia = Number(m[1]), mes = Number(m[2]), ano = Number(m[3])
  if (ano < 1900 || mes < 1 || mes > 12 || dia < 1 || dia > 31) return false
  const d = new Date(ano, mes - 1, dia)
  return d.getFullYear() === ano && d.getMonth() === mes - 1 && d.getDate() === dia && d < new Date()
}

function guardarFotoWebCadastro(dataUrl, numero, campo) {
  const m = String(dataUrl || '').match(/^data:(image\/(?:jpeg|png|webp));base64,([A-Za-z0-9+/=]+)$/)
  if (!m) throw new Error(`A ${campo === 'fotoPerfil' ? 'foto de perfil' : 'foto da moto'} deve ser JPG, PNG ou WEBP.`)
  const mime = m[1]
  const buffer = Buffer.from(m[2], 'base64')
  if (!buffer.length || buffer.length > 2 * 1024 * 1024) throw new Error('Cada foto deve ter no máximo 2 MB.')
  const ext = ({ 'image/jpeg': '.jpg', 'image/png': '.png', 'image/webp': '.webp' })[mime]
  const base = path.join(DATA_DIR, 'cadastros_motoboy_media')
  fs.mkdirSync(base, { recursive: true, mode: 0o700 })
  const nome = `${numero}_${campo}_${Date.now()}_${crypto.randomBytes(4).toString('hex')}${ext}`
  fs.writeFileSync(path.join(base, nome), buffer, { mode: 0o600, flag: 'wx' })
  return path.relative(DATA_DIR, path.join(base, nome))
}

const LIMITE_CORPO_CADASTRO = 6 * 1024 * 1024
const limitesCadastroIP = new Map()
function limiteExcedido(ip, chave, maximo, janelaMs) {
  const agora = Date.now()
  const k = `${chave}:${ip}`
  const lista = (limitesCadastroIP.get(k) || []).filter(t => agora - t < janelaMs)
  if (lista.length >= maximo) { limitesCadastroIP.set(k, lista); return true }
  lista.push(agora); limitesCadastroIP.set(k, lista)
  if (limitesCadastroIP.size > 20000) for (const [kk, v] of limitesCadastroIP) if (!v.length || agora - v[v.length - 1] > 3600 * 1000) limitesCadastroIP.delete(kk)
  return false
}
// Aceita 10–11 dígitos (DDD+número) ou 12–13 com prefixo 55; devolve sempre 55+DDD+número ou null.
function normalizarTelefoneBR(valor) {
  let d = String(valor || '').replace(/\D/g, '')
  if ((d.length === 12 || d.length === 13) && d.startsWith('55')) d = d.slice(2)
  if (d.length !== 10 && d.length !== 11) return null
  if (d.length === 11 && d[2] !== '9') return null
  return '55' + d
}
function iniciarServidorCadastro() {
  if (servidorCadastro) return servidorCadastro
  servidorCadastro = http.createServer(async (req, res) => {
    const url = new URL(req.url || '/', 'http://localhost')
    const ipCliente = (process.env.TRUST_PROXY === 'true' ? String(req.headers['x-forwarded-for'] || '').split(',')[0].trim() : '') || req.socket.remoteAddress || 'desconhecido'
    if (limiteExcedido(ipCliente, 'geral', 120, 60 * 1000)) { responderJsonCadastro(res, 429, { error: 'Muitas requisições. Aguarde um minuto.' }); return }
    if (req.method === 'POST' && limiteExcedido(ipCliente, 'envio', 5, 60 * 60 * 1000)) { responderJsonCadastro(res, 429, { error: 'Limite de envios atingido. Tente novamente mais tarde.' }); return }
    if (req.method === 'GET' && (url.pathname === '/cadastro' || url.pathname === '/cadastro/')) {
      const arquivoHtml = path.join(__dirname, 'cadastro.html')
      if (!fs.existsSync(arquivoHtml)) { res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' }); res.end('Página de cadastro indisponível.'); return }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff', 'Content-Security-Policy': "default-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'" })
      fs.createReadStream(arquivoHtml).pipe(res)
      return
    }
    if (req.method === 'GET' && url.pathname === '/') {
      res.writeHead(302, { Location: '/cadastro', 'Cache-Control': 'no-store' }); res.end(); return
    }
    if (req.method !== 'POST' || url.pathname !== '/api/cadastro-motoboy') {
      responderJsonCadastro(res, 404, { error: 'Página ou endereço não encontrado.' }); return
    }
    const tipo = String(req.headers['content-type'] || '').split(';')[0].trim().toLowerCase()
    if (tipo !== 'application/json') { responderJsonCadastro(res, 415, { error: 'Formato de envio inválido.' }); return }
    if (Number(req.headers['content-length']) > LIMITE_CORPO_CADASTRO) { responderJsonCadastro(res, 413, { error: 'O cadastro enviado é muito grande. Reduza o tamanho das fotos.' }); req.destroy(); return }
    let fotoPerfilSalva = null, fotoMotoSalva = null
    try {
      const partes = []
      let total = 0
      for await (const chunk of req) {
        total += chunk.length
        if (total > LIMITE_CORPO_CADASTRO) { responderJsonCadastro(res, 413, { error: 'O cadastro enviado é muito grande. Reduza o tamanho das fotos.' }); req.destroy(); return }
        partes.push(chunk)
      }
      const d = JSON.parse(Buffer.concat(partes).toString('utf8'))
      // Campo isca (honeypot): pessoas não o veem; robôs costumam preenchê-lo.
      if (d && d.website) { responderJsonCadastro(res, 201, { ok: true, message: 'Cadastro recebido e enviado para análise.' }); return }
      const texto = (v, max = 120) => String(v ?? '').replace(/[\u0000-\u001f\u007f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max)
      const nome = texto(d.nome, 100)
      const telefone = normalizarTelefoneBR(texto(d.telefone, 20))
      const cpf = texto(d.cpf, 20).replace(/\D/g, '')
      const nascimento = texto(d.nascimento, 10)
      const telefoneReferencia = normalizarTelefoneBR(texto(d.telefoneReferencia, 20))
      const parentesco = texto(d.parentesco, 60)
      const cidade = texto(d.cidade, 80), bairro = texto(d.bairro, 80), rua = texto(d.rua, 120)
      const numeroCasa = texto(d.numeroCasa, 20), tipoResidencia = texto(d.tipoResidencia, 20)
      const modeloMoto = texto(d.modeloMoto, 80), placa = texto(d.placa, 10).toUpperCase().replace(/[^A-Z0-9-]/g, '')
      const bag = texto(d.bag, 5).toLowerCase(), suporteCelular = texto(d.suporteCelular, 5).toLowerCase(), carregadorMoto = texto(d.carregadorMoto, 5).toLowerCase(), habilitacao = texto(d.habilitacao, 5).toLowerCase()
      const diasPermitidos = ['segunda-feira', 'terça-feira', 'quarta-feira', 'quinta-feira', 'sexta-feira', 'sábado', 'domingo']
      const periodosPermitidos = ['manhã', 'tarde', 'noite']
      const disponibilidade = Array.isArray(d.disponibilidade) ? d.disponibilidade.map(x => {
        const dia = texto(x?.dia, 30)
        const horaInicio = Number(x?.horaInicio)
        const horaFim = Number(x?.horaFim)
        const periodos = Array.isArray(x?.periodos) ? [...new Set(x.periodos.map(p => texto(p, 20).toLowerCase()).filter(p => periodosPermitidos.includes(p)))] : []
        const horaValida = Number.isInteger(horaInicio) && (horaInicio >= 6 && horaInicio <= 23 || horaInicio === 0 || horaInicio === 1)
        const fimValido = Number.isInteger(horaFim) && (horaFim >= 6 && horaFim <= 23 || horaFim === 0 || horaFim === 1) && horaFim !== horaInicio
        return { dia, horaInicio: horaValida ? horaInicio : null, horaFim: fimValido ? horaFim : null, periodos }
      }).filter(x => diasPermitidos.includes(x.dia) && x.horaInicio !== null && x.horaFim !== null) : []
      if (nome.length < 3) { responderJsonCadastro(res, 400, { error: 'Informe seu nome completo.' }); return }
      if (!telefone) { responderJsonCadastro(res, 400, { error: 'Informe um WhatsApp válido com DDD (10 ou 11 dígitos).' }); return }
      if (!cpfValido(cpf)) { responderJsonCadastro(res, 400, { error: 'CPF inválido. Confira os números digitados.' }); return }
      if (!validarDataNascimentoCadastro(nascimento)) { responderJsonCadastro(res, 400, { error: 'Data de nascimento inválida. Use DD/MM/AAAA e uma data passada.' }); return }
      if (!telefoneReferencia) { responderJsonCadastro(res, 400, { error: 'Informe o telefone de referência com DDD.' }); return }
      if (!parentesco || !cidade || !bairro || !rua || !numeroCasa || !['Casa', 'Apartamento'].includes(tipoResidencia) || !modeloMoto || !placa) { responderJsonCadastro(res, 400, { error: 'Preencha todos os campos obrigatórios.' }); return }
      if (![bag, suporteCelular, carregadorMoto, habilitacao].every(x => ['sim', 'não'].includes(x))) { responderJsonCadastro(res, 400, { error: 'Selecione Sim ou Não em todos os campos de equipamentos e CNH.' }); return }
      if (!disponibilidade.length) { responderJsonCadastro(res, 400, { error: 'Selecione ao menos um dia e informe os horários de início e encerramento.' }); return }
      const id = `${telefone}@s.whatsapp.net`
      await executarSerializado(async () => {
        const anterior = empresaAtual
        const chaveDestino = empresas.CHEGO_DELIVERY ? 'CHEGO_DELIVERY' : 'SEU_DELIVERY'
        selecionarEmpresa(chaveDestino)
        try {
          if (!Array.isArray(estado.cadastrosMotoboy)) estado.cadastrosMotoboy = []
          const existente = estado.cadastrosMotoboy.find(c => (jidNormalizedUser(c.id) === jidNormalizedUser(id) || (c.cpf && String(c.cpf).replace(/\D/g, '') === cpf)) && c.status !== 'reprovado')
          if (existente) { responderJsonCadastro(res, 409, { error: `Este WhatsApp ou CPF já possui cadastro com status "${existente.status || 'pendente'}". Fale com a administração para atualizar seus dados.` }); return }
          const numeroSeguro = telefone.replace(/\D/g, '')
          const registro = {
            id, nome, cpf, nascimento, telefoneReferencia, parentesco, cidade, bairro, rua, numeroCasa, tipoResidencia,
            modeloMoto, placa, bag, suporteCelular, carregadorMoto, habilitacao,
            fotoPerfil: (fotoPerfilSalva = guardarFotoWebCadastro(d.fotoPerfil, numeroSeguro, 'fotoPerfil')),
            fotoMoto: (fotoMotoSalva = guardarFotoWebCadastro(d.fotoMoto, numeroSeguro, 'fotoMoto')),
            disponibilidade, diasSelecionados: disponibilidade.map(x => x.dia), status: 'pendente',
            criadoEm: new Date().toISOString(), dataHoraCadastro: dataHoraCadastroFortaleza(), enviadoEm: new Date().toISOString(), origemCadastro: 'pagina_web'
          }
          estado.cadastrosMotoboy.push(registro)
          if (!Array.isArray(estado.cadastrosMotoboyPendentes)) estado.cadastrosMotoboyPendentes = []
          estado.cadastrosMotoboyPendentes = estado.cadastrosMotoboyPendentes.filter(x => jidNormalizedUser(x.id) !== jidNormalizedUser(id))
          estado.cadastrosMotoboyPendentes.push({ id, nome, solicitadoEm: Date.now(), status: 'pendente' })
          salvar()
          if (socketWhatsAppCadastro) await avisarAdministradoresNovoCadastro(socketWhatsAppCadastro, registro)
          responderJsonCadastro(res, 201, { ok: true, message: 'Cadastro recebido e enviado para análise.' })
        } finally {
          selecionarEmpresa(anterior)
        }
      })
    } catch (err) {
      // Remove fotos órfãs se o cadastro não foi concluído.
      for (const rel of [fotoPerfilSalva, fotoMotoSalva]) { if (rel) { try { fs.unlinkSync(path.join(DATA_DIR, rel)) } catch (_) {} } }
      console.error('Erro no cadastro web de motoboy:', err?.stack || err?.message || err)
      if (!res.headersSent) responderJsonCadastro(res, 400, { error: 'Não foi possível processar o cadastro. Confira os dados e tente novamente.' })
    }
  })
  const porta = Number(process.env.PORT) || 80
  const host = process.env.HOST || '0.0.0.0'
  servidorCadastro.listen(porta, host, () => console.log(`Página de cadastro da Chegô Delivery disponível na porta ${porta} (rota /cadastro).`))
  servidorCadastro.on('error', erro => console.error('Erro no servidor da página de cadastro:', erro?.message || erro))
  return servidorCadastro
}

/* =====================================
   INICIAR BOT
===================================== */

async function iniciarInterno() {

  console.log(
    '\nIniciando bot...\n'
  )

  // Pareamento manual de uso único: configure FORCE_NEW_WHATSAPP_PAIRING=true no painel
  // do servidor para arquivar a sessão antiga antes de carregar as credenciais do Baileys.
  // O marcador fica no DATA_DIR persistente para não apagar a sessão recém-pareada em reinícios.
  const marcadorResetPareamento = path.join(DATA_DIR, '.whatsapp-pairing-reset-done')
  const forcarNovoPareamento = String(process.env.FORCE_NEW_WHATSAPP_PAIRING || '').toLowerCase() === 'true'
  if (forcarNovoPareamento && !fs.existsSync(marcadorResetPareamento)) {
    try {
      fs.mkdirSync(PASTA_BACKUPS_AUTH, { recursive: true })
      if (fs.existsSync(AUTH_DIR) && fs.readdirSync(AUTH_DIR).length) {
        const sessaoPreservada = path.join(PASTA_BACKUPS_AUTH, `preserved-auth-for-pairing-${Date.now()}`)
        fs.renameSync(AUTH_DIR, sessaoPreservada)
        console.warn(`Sessão antiga arquivada para novo pareamento: ${sessaoPreservada}`)
      }
      fs.mkdirSync(AUTH_DIR, { recursive: true })
      fs.writeFileSync(marcadorResetPareamento, new Date().toISOString(), { mode: 0o600 })
      console.log('Sessão antiga separada. O Bot solicitará um novo código de conexão para o número configurado.')
    } catch (e) {
      console.error('Falha ao preparar novo pareamento. A sessão antiga foi mantida sempre que possível:', e.message)
      throw e
    }
  }

  // Recupera a sessão mais recente apenas se AUTH estiver ausente/vazio.
  // Não substitui credenciais existentes nem altera o fluxo dos comandos.
  try {
    const authTemArquivos = fs.existsSync(AUTH_DIR) && fs.readdirSync(AUTH_DIR).length > 0
    if (!authTemArquivos && !fs.existsSync(MARCADOR_SESSAO_REJEITADA)) {
      const snapshot = localizarUltimoSnapshotValido(PASTA_BACKUPS_AUTH, 'auth', 'creds.json')
      if (snapshot) {
        fs.mkdirSync(AUTH_DIR, { recursive: true })
        restaurarDiretorioDeBackup(snapshot, AUTH_DIR)
        console.warn(`♻️ Sessão WhatsApp recuperada antes da inicialização: ${path.basename(snapshot)}`)
      } else {
        console.warn('⚠️ Pasta de autenticação vazia e nenhum backup de sessão disponível. O WhatsApp poderá exigir novo pareamento.')
      }
    }
  } catch (e) {
    console.error('Falha ao recuperar sessão WhatsApp antes da inicialização:', e.message)
  }

  const { state, saveCreds } = await useMultiFileAuthState(AUTH)


    const sock =
    makeWASocket({

      auth: state,

      logger:
        pino({
          level: 'silent'
        }),

      printQRInTerminal:
        false,

      syncFullHistory:
        false,

      // 408: dá mais tempo para o handshake WebSocket em hospedagens lentas.
      connectTimeoutMs: 120000,
      keepAliveIntervalMs: 20000,
      defaultQueryTimeoutMs: 60000,
      retryRequestDelayMs: 2000,

    })

  // Um único socket é considerado proprietário da conexão. Eventos atrasados
  // de sockets antigos não podem disparar novas reconexões nem marcar o bot online.
  global.__chegoSocketAtual = sock
  socketWhatsAppCadastro = sock
  iniciarServidorCadastro()
  // Garante que os arquivos essenciais existem e agenda backups recorrentes.
  recuperarDadosSeNecessario()
  // Deixa o socket iniciar sem cópia síncrona de relatórios no caminho crítico.
  if (!global.__chegoBackupInicialTimer) global.__chegoBackupInicialTimer = setTimeout(() => {
    global.__chegoBackupInicialTimer = null
    try { criarBackupDados(true); criarBackupAuth(false) }
    catch (e) { console.error('Falha no backup inicial:', e.message) }
  }, 1000)
  if (!global.__chegoBackupDadosTimer) global.__chegoBackupDadosTimer = setInterval(() => criarBackupDados(false), INTERVALO_BACKUP_DADOS)
  // A sessão de autenticação é copiada a cada 12 horas, não a cada 5 minutos.
  if (!global.__chegoBackupAuthTimer) global.__chegoBackupAuthTimer = setInterval(() => criarBackupAuth(false), 12 * 60 * 60 * 1000)

  /* ===================================
     VERIFICAR LIMPEZA DAS 06:00
  =================================== */

  if (!global.__chegoRotinaDiariaTimer) global.__chegoRotinaDiariaTimer = setInterval(() => {
    executarSerializado(async () => {
      const empresaAntes = empresaAtual;
      for (const chave of Object.keys(EMPRESA_CONFIG)) {
        selecionarEmpresa(chave)
        // Faz os bloqueios automáticos expirarem mesmo sem tentativa de ficar online.
        for (const b of [...(estado.bloqueiosAutomaticosEscala || [])]) estaBloqueado(b.id)
        verificarZerarLista()
        verificarBackupDiario()
      }
      try {
        selecionarEmpresa('CHEGO_DELIVERY');
        const grupoEscala = empresas.CHEGO_DELIVERY?.grupos?.g1;
        await processarPunicoesEscalaFimDeSemana(sock, grupoEscala);
      } catch (e) { console.log('Erro ao apurar faltas da escala:', e.message); }
      try { await verificarPublicacaoAutomaticaEscala(sock); }
      catch (e) { console.log('Erro ao publicar escala automática de segunda-feira:', e.message); }
      try { atualizarBloqueiosTaxas(); } catch (e) { console.log('Erro ao atualizar bloqueios por taxas:', e.message); }
      selecionarEmpresa(empresaAntes);
      salvar()
    })
  }, 30 * 1000)


  sock.ev.on('creds.update', async () => { try { await saveCreds(); if (!ultimoBackupAuthEm) criarBackupAuth(true) } catch (e) { console.error('Falha ao salvar credenciais WhatsApp:', e.message) } })


/* ===================================
   VERIFICAR LIMPEZA DAS 06:00
=================================== */



  /* ===================================
     CONEXÃO
  =================================== */

  sock.ev.on(
    'connection.update',
    async update => {
      // Ignora eventos atrasados de sockets substituídos por uma reconexão.
      if (global.__chegoSocketAtual !== sock) return

      const {
        connection,
        qr,
        lastDisconnect
      } = update


      /*
        MODO CÓDIGO DE PAREAMENTO: não exibir QR Code nos logs.
        O usuário deve digitar o código numérico/alfanumérico no WhatsApp Business.
        O código é solicitado por sock.requestPairingCode() abaixo.
      */

      if (qr) {
        console.log('O WhatsApp ofereceu QR Code, mas ele foi ocultado. Use o código de conexão exibido nos logs e escolha “Conectar com número de telefone” no WhatsApp Business.');
      }


      /*
        CONECTADO
      */

      if (
        connection === 'open'
      ) {
        conectadoWhatsApp = true
        global.__chegoTentativaReconexao = 0
        if (global.__chegoReconexaoAgendada) { clearTimeout(global.__chegoReconexaoAgendada); global.__chegoReconexaoAgendada = null }
        desconectadoDesde = 0
        restaurouAuthNestaQueda = false
        try { if (fs.existsSync(MARCADOR_SESSAO_REJEITADA)) fs.unlinkSync(MARCADOR_SESSAO_REJEITADA) } catch (e) { console.error('Não foi possível limpar marcador de sessão rejeitada após conexão:', e.message) }
        if (temporizadorRestauracaoAuth) { clearTimeout(temporizadorRestauracaoAuth); temporizadorRestauracaoAuth = null }
        criarBackupAuth(false)

        console.log(
          '\nBOT CONECTADO!\n'
        )


        await encontrarGrupos(
          sock
        )


        let referenciasListaCorrigidas = false
        const normalizarJidReferenciaLista = jid => {
          const valor = String(jid || '').trim()
          if (!valor) return ''
          try { return jidNormalizedUser(valor).toLowerCase() }
          catch { return valor.toLowerCase() }
        }
        for (const chave of Object.keys(EMPRESA_CONFIG)) {
          const empresa = empresas[chave]
          const escopoLista = empresa?.estadosPorGrupo?.g1
          const grupoEsperado = String(empresa?.grupos?.g1 || '')
          const referencia = escopoLista?.ultimaListaMensagemKey
          const referenciaValida = Boolean(
            grupoEsperado.endsWith('@g.us') &&
            referencia?.id &&
            referencia.fromMe === true &&
            referencia.remoteJid &&
            normalizarJidReferenciaLista(referencia.remoteJid) === normalizarJidReferenciaLista(grupoEsperado)
          )

          // Uma referência incompleta, de outro grupo ou que não foi enviada pelo
          // próprio bot nunca pode ser usada na reconexão. Apagamos só a chave
          // inválida (mantendo texto/histórico) e exigimos Lista para criar outra.
          if (referencia && !referenciaValida) {
            escopoLista.ultimaListaMensagemKey = null
            referenciasListaCorrigidas = true
            console.warn(`[LISTA-RECUPERACAO] Referência inválida descartada sem publicar mensagem nova. empresa=${chave}; grupo=${grupoEsperado || 'ausente'}`)
          }

          // Na inicialização/reconexão, nunca criar lista nova automaticamente.
          // Edita apenas a mensagem anterior com chave comprovadamente do grupo.
          if (referenciaValida && escopoLista?.ultimaListaEnviada) {
            await publicarListaEmpresaNoEstadoDoGrupo(sock, chave, 'g1', { apenasEditarExistente: true })
          } else {
            console.log(`${EMPRESA_CONFIG[chave].nome} | lista não editada na reconexão: nenhuma referência válida registrada; use Lista para publicar.`)
          }
        }
        if (referenciasListaCorrigidas) salvar()
        selecionarEmpresa('SEU_DELIVERY')
        salvar()
      }


      /*
        DESCONECTADO
      */

      if (
        connection === 'close'
      ) {
        conectadoWhatsApp = false
        if (!desconectadoDesde) desconectadoDesde = Date.now()

        const codigo =
          lastDisconnect
            ?.error
            ?.output
            ?.statusCode

        // Diagnóstico completo: o status 408 sozinho não revela a causa interna.
        const erroDesconexao = lastDisconnect?.error
        const detalhesDesconexao = {
          horario: new Date().toISOString(),
          statusCode: codigo ?? null,
          disconnectReason: codigo != null ? (DisconnectReason[codigo] || 'desconhecido') : 'sem_status_code',
          name: erroDesconexao?.name || null,
          message: erroDesconexao?.message || null,
          stack: erroDesconexao?.stack || null,
          data: erroDesconexao?.data ?? null,
          output: erroDesconexao?.output ? {
            statusCode: erroDesconexao.output.statusCode ?? null,
            payload: erroDesconexao.output.payload ?? null
          } : null,
          cause: erroDesconexao?.cause ? {
            name: erroDesconexao.cause.name || null,
            message: erroDesconexao.cause.message || String(erroDesconexao.cause),
            code: erroDesconexao.cause.code || null,
            stack: erroDesconexao.cause.stack || null
          } : null,
          tentativaReconexao: Number(global.__chegoTentativaReconexao || 0) + 1
        }
        console.error('DESCONEXÃO WHATSAPP — DIAGNÓSTICO:', JSON.stringify(detalhesDesconexao, (key, value) => {
          if (typeof value === 'bigint') return value.toString()
          if (value instanceof Error) return { name: value.name, message: value.message, stack: value.stack, cause: value.cause }
          return value
        }))
        // 401/loggedOut significa que o WhatsApp rejeitou a sessão. Restaurar o
        // backup nesse caso apenas repetiria a mesma sessão inválida e impediria
        // o pareamento. Preserve a sessão rejeitada como backup e inicie uma nova.
        if (codigo === DisconnectReason.loggedOut) {
          if (!global.__chegoPareamentoReiniciando) {
            global.__chegoPareamentoReiniciando = true
            console.error('⚠️ Sessão WhatsApp rejeitada (401/loggedOut). Preservando backup e preparando novo pareamento por código.')
            try {
              // Registra a rejeição antes de arquivar AUTH. Não criar snapshot
              // regular aqui: isso salvaria a sessão inválida como restaurável.
              fs.writeFileSync(MARCADOR_SESSAO_REJEITADA, new Date().toISOString(), { mode: 0o600 })
              if (fs.existsSync(AUTH_DIR)) {
                fs.mkdirSync(PASTA_BACKUPS_AUTH, { recursive: true })
                const rejeitada = path.join(PASTA_BACKUPS_AUTH, `auth-rejected-${Date.now()}`)
                fs.renameSync(AUTH_DIR, rejeitada)
                console.warn(`Sessão rejeitada preservada em: ${rejeitada}`)
              }
            } catch (e) {
              console.error('Não foi possível arquivar a sessão rejeitada:', e.message)
              global.__chegoPareamentoReiniciando = false
            }
            setTimeout(() => {
              global.__chegoPareamentoReiniciando = false
              iniciar().catch(e => console.error('Falha ao iniciar novo pareamento WhatsApp:', e.message))
            }, 1500)
          }
        } else {
          // Em 408 (perda/timeout de transporte), não restaurar auth automaticamente:
          // as credenciais não foram rejeitadas. Restaurá-las em paralelo às tentativas
          // normais poderia iniciar dois sockets e piorar o ciclo de desconexão.
          // O código 515 é o reinício de fluxo exigido pelo WhatsApp após
          // determinadas etapas do handshake/pareamento. Não restaure um
          // backup antigo: primeiro persista as credenciais recém-atualizadas
          // e reconecte usando o mesmo AUTH.
          if (codigo === 515) {
            try {
              await saveCreds()
              console.log('🔄 Erro 515: credenciais atuais salvas; reiniciando o socket com a mesma sessão, sem apagar AUTH.')
            } catch (e) {
              console.error('Falha ao salvar credenciais antes da recuperação 515:', e?.message || e)
            }
          }

          if (codigo !== 408 && codigo !== 515 && !temporizadorRestauracaoAuth && !restaurouAuthNestaQueda) {
            temporizadorRestauracaoAuth = setTimeout(() => {
              temporizadorRestauracaoAuth = null
              if (conectadoWhatsApp || !desconectadoDesde || Date.now() - desconectadoDesde < 5 * 60 * 1000 || restaurouAuthNestaQueda) return
              restaurouAuthNestaQueda = true
              console.warn('⚠️ WhatsApp permaneceu desconectado por 5 minutos. Tentando restaurar o último backup da sessão.')
              if (restaurarUltimoBackupAuth()) setTimeout(() => iniciar().catch(e => console.error('Falha ao reiniciar após restaurar sessão:', e.message)), 1000)
            }, 5 * 60 * 1000)
          }
          // Agenda somente uma reconexão por vez. Aumenta o intervalo entre
          // tentativas em falhas repetidas (3s, 6s, 12s, 24s e no máximo 30s),
          // evitando criar vários sockets concorrentes durante uma queda.
          if (!global.__chegoReconexaoAgendada) {
            const tentativa = Number(global.__chegoTentativaReconexao || 0)
            // Para 515, o servidor pede explicitamente um restart: use um
            // intervalo curto e fixo, sem restaurar sessão nem solicitar novo
            // código se as credenciais já estiverem registradas.
            const atraso = codigo === 515
              ? 1500
              : Math.min(3000 * (2 ** Math.min(tentativa, 4)), 30000)
            global.__chegoTentativaReconexao = Math.min(tentativa + 1, 5)
            console.log(`Reconectando em ${Math.round(atraso / 1000)}s (tentativa ${global.__chegoTentativaReconexao})...`)
            global.__chegoReconexaoAgendada = setTimeout(() => {
              global.__chegoReconexaoAgendada = null
              if (conectadoWhatsApp) return
              if (codigo === 515) {
                console.log('Reinício 515: reutilizando a sessão AUTH atual. Nenhuma credencial será apagada.')
              }
              iniciar().catch(e => console.error('Falha ao reconectar WhatsApp:', e?.message || e))
            }, atraso)
          } else {
            console.log('Reconexão já agendada; aguardando a tentativa existente.')
          }
        }
  }
  })
  // Pareamento por código para hospedagens sem terminal interativo: mostra o código nos logs do servidor.
  // Por padrão usa o número solicitado pelo usuário; pode ser sobrescrito por WHATSAPP_PHONE_NUMBER.
  // Nunca apaga automaticamente uma sessão existente para evitar perder a conexão atual.
  const pareamentoAtivado = String(process.env.USE_PAIRING_CODE || 'true').toLowerCase() !== 'false';
  const telefonePareamento = String(process.env.WHATSAPP_PHONE_NUMBER || '5584999097976').replace(/\D/g, '');
  if (pareamentoAtivado) {
    if (!state.creds.registered && telefonePareamento) {
      console.log(`\nSolicitando código de conexão do WhatsApp para o número terminado em ${telefonePareamento.slice(-4)}...`);
      setTimeout(async () => {
        try {
          if (!state.creds.registered) {
            const codigo = await sock.requestPairingCode(telefonePareamento);
            console.log('\n========== CÓDIGO DE CONEXÃO WHATSAPP ==========');
            console.log(codigo);
            console.log('NO WHATSAPP BUSINESS: Configurações > Aparelhos conectados > Conectar aparelho > Conectar com número de telefone. Digite este código; não escaneie QR Code.');
            console.log('================================================\n');
          } else {
            console.log('A sessão WhatsApp já está registrada; nenhum novo código foi solicitado.');
          }
        } catch (erroPareamento) {
          console.error('Não foi possível gerar código de conexão. Confira o número e os logs do Baileys:', erroPareamento?.message || erroPareamento);
        }
      }, 3000);
    } else if (state.creds.registered) {
      console.log('Sessão WhatsApp já registrada. Para conectar outro número, faça backup e remova a sessão auth antiga no armazenamento persistente antes de reiniciar.');
    } else {
      console.error('Não foi possível solicitar código: número de pareamento vazio. Configure WHATSAPP_PHONE_NUMBER.');
    }
  }

  sock.ev.on(
    'messages.upsert',
    async ({ messages }) => {

      for (
        const msg of messages
      ) {

        try {

          await executarSerializado(async () => {
            const protocolo = msg?.message?.protocolMessage
            const chave = empresaDoGrupo(msg?.key?.remoteJid)
            if (chave) selecionarEmpresa(chave)

            if (protocolo) {
              const processou = await processarEntregaApagada(sock, msg)
              if (processou) return
            }

            await processarMensagem(sock, msg)
          })

        } catch (e) {

          console.error(
            'Erro ao processar mensagem:',
            e?.stack || e?.message || e
          )
        }
      }
    }
  )

  /*
    Detectar mensagens apagadas.
    O WhatsApp/Baileys pode entregar a exclusão
    pelo evento messages.update.
  */

  sock.ev.on(
    'messages.update',
    async (updates) => {

      for (
        const item of updates
      ) {

        try {
          await executarSerializado(async () => {
            const chave = empresaDoGrupo(item?.key?.remoteJid || item?.update?.key?.remoteJid)
            if (chave) selecionarEmpresa(chave)
            await processarEntregaApagada(sock, item)
          })

        } catch (e) {

          console.log(
            'Erro ao processar exclusão:',
            e.message
          )
        }
      }
    }
  )


  // A cada 10 minutos, verifica se há alteração real e sincroniza a lista por empresa
  // usada pelas atualizações normais. Não força uma mensagem nova: atualiza a
  // última lista daquele grupo, evitando publicar a versão vazia de outro contexto.
  // Durante o horário de pico, a publicação automática continua suspensa.
  if (!global.__chegoPublicacaoPeriodicaListaTimer) global.__chegoPublicacaoPeriodicaListaTimer = setInterval(() => {
    executarSerializado(async () => {
      const empresaAntes = empresaAtual
      try {
        for (const chave of Object.keys(EMPRESA_CONFIG)) {
          const empresa = empresas[chave]
          const escopoLista = empresa?.estadosPorGrupo?.g1 || {}
          const ultimaPublicacao = Number(escopoLista.ultimaListaPublicadaEm ?? empresa?.ultimaListaPublicadaEm) || 0
          const picoSuspenso = escopoLista.listaSuspensaPico === undefined
            ? !!empresa?.listaSuspensaPico
            : !!escopoLista.listaSuspensaPico
          if (!picoSuspenso && empresa?.grupos?.g1 && Date.now() - ultimaPublicacao >= 10 * 60 * 1000) {
            await publicarListaEmpresaNoEstadoDoGrupo(sock, chave, 'g1', { apenasEditarExistente: true, forcarAtualizacao: true, somenteSeTextoMudou: true })
          }
        }
      } catch (e) { console.log('Erro na publicação periódica da lista:', e.message) }
      finally { selecionarEmpresa(empresaAntes) }
    })
  }, 10 * 60 * 1000)

  if (!global.__chegoVerificacaoCorridasTimer) global.__chegoVerificacaoCorridasTimer = setInterval(
    async () => {
      // Não acumula tarefas de verificação na fila serializada se o servidor
      // estiver ocupado. O ciclo anterior também publicava a lista e gravava
      // os dados a cada segundo, mesmo sem nenhuma mudança.
      if (global.__chegoVerificacaoCorridasEmAndamento) return
      global.__chegoVerificacaoCorridasEmAndamento = true
      try {
        await executarSerializado(async () => {
          try {
            for (const chave of Object.keys(EMPRESA_CONFIG)) {
              // A verificação já salva o estado e publica a lista somente se
              // detectar mudança. Não repetir a publicação incondicional aqui.
              await verificarCorridasEmpresaNoGrupoDePedidos(sock, chave)
            }
          } catch (e) {
            console.log('Erro na verificação periódica de corridas:', e.message)
          }
        })
      } finally {
        global.__chegoVerificacaoCorridasEmAndamento = false
      }
    },
    5000
  )
}

// Serializa inicializações concorrentes: uma reconexão e um temporizador de
// recuperação não podem construir dois sockets ao mesmo tempo.
async function iniciar() {
  if (global.__chegoIniciarPromise) {
    console.log('Inicialização do WhatsApp já em andamento; evitando socket duplicado.')
    return global.__chegoIniciarPromise
  }
  const tentativa = iniciarInterno()
  global.__chegoIniciarPromise = tentativa
  try {
    return await tentativa
  } finally {
    if (global.__chegoIniciarPromise === tentativa) global.__chegoIniciarPromise = null
  }
}

iniciar().catch(e => console.error('Falha na inicialização do bot:', e?.stack || e?.message || e))
