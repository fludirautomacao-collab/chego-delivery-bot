# Chegô Delivery — nova instalação para servidor

Projeto novo, criado do zero. Não contém `index.js`, sessão nem credenciais copiadas do Termux.

## Requisitos
- Node.js 20 ou superior
- npm
- Um servidor com processo Node.js persistente
- Uma conta WhatsApp para conectar o bot

## Instalação
1. Envie os arquivos deste projeto para o repositório privado `fludirautomacao-collab/chego-delivery-bot`.
2. No servidor, instale Node.js 20+ e execute `npm install`.
3. Copie `.env.example` para `.env` e configure `ADMIN_NUMBERS` e `WHATSAPP_PHONE_NUMBER`.
4. Execute `npm start`.

## Autenticação WhatsApp
A configuração padrão usa código de pareamento em vez de QR. No primeiro início, informe `WHATSAPP_PHONE_NUMBER` com código do país e DDD, sem `+`, espaços ou hífens. O código será exibido no log do servidor; digite-o no WhatsApp em **Dispositivos conectados → Conectar dispositivo → Conectar com número de telefone** (os nomes podem variar por versão).
A conexão por pareamento ainda exige autorização no celular. A sessão criada fica em `auth/` e deve ser protegida, mantida fora do GitHub e persistida entre reinícios. Não suba a pasta `auth/` para o repositório.

## Grupos
O bot procura os quatro grupos pelo nome exato configurado em `AUTHORIZED_GROUP_NAMES`. Confirme os nomes e ajuste a variável se algum título tiver diferença de acento, espaço ou emoji. Se dois grupos tiverem o mesmo nome, use IDs de grupo em uma versão posterior para evitar ambiguidade.

## Comandos iniciais
- `!menu` — lista os comandos.
- `!online` — no grupo autorizado, adiciona o remetente à lista de entregadores online.
- `!offline` — encerra a sessão online do remetente.
- `!lista online` — mostra quem está online no grupo.
- `!entrega <descrição>` — cria um registro simples de entrega no grupo.
- `!editar <id> <nova descrição>` — edita uma entrega criada por comando no mesmo grupo; administradores podem editar qualquer entrega.
- `!tempo` — mostra o tempo online acumulado da pessoa.
- `!relatorio` — relatório textual simples de atividade, restrito a administradores.

## Segurança e limitações da primeira versão
- `ADMIN_NUMBERS` define administradores por número.
- Comandos de operação só são aceitos nos quatro grupos autorizados, exceto `!tempo` que também responde em privado ao próprio usuário.
- Dados operacionais são gravados em JSON local em `DATA_DIR`. Configure volume/disco persistente no provedor.
- Esta base ainda não implementa os layouts finais de relatórios em imagem nem todos os fluxos de taxas. O Pix continua manual: geração/validação e baixa de taxas devem ser concluídas em etapa própria; não existe confirmação automática de pagamento.
- A sessão Baileys é sensível. Nunca a publique, nem mesmo em repositório privado.
- Esta é uma base inicial para teste controlado, não uma declaração de que todas as funções históricas já estão reproduzidas.
