const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const crypto = require('crypto');

const app = express();
const httpServer = http.createServer(app);
const io = new Server(httpServer);

app.use(express.static(path.join(__dirname, 'public')));

// ── CONSTANTS ────────────────────────────────────────────
const SUITS = ['♠','♥','♦','♣'];
const RANKS = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const RANK_VAL = {2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,10:10,J:11,Q:12,K:13,A:14};
const ROUND_SEQUENCE = [5,6,7,8,9,10,10,9,8,7,6,5];
const BOT_NAMES = ['Ace','Blackwood','Cutthroat','Duchess','Eddie'];
const BOT_THINK_MS = 900;

const rooms = {};

// ── UTILITIES ────────────────────────────────────────────
function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function makeDeck() {
  const deck = [];
  for (const suit of SUITS) for (const rank of RANKS) deck.push({ suit, rank });
  return shuffle(deck);
}

function rankVal(r) { return RANK_VAL[r] || parseInt(r); }

function beats(card, best, trump) {
  if (card.suit === trump && best.suit !== trump) return true;
  if (card.suit !== trump && best.suit === trump) return false;
  if (card.suit !== best.suit) return false;
  return rankVal(card.rank) > rankVal(best.rank);
}

function trickWinner(trick, trump) {
  let best = trick[0];
  for (let i = 1; i < trick.length; i++) {
    if (beats(trick[i].card, best.card, trump)) best = trick[i];
  }
  return best.playerIdx;
}

function isLegalPlay(hand, card, trick) {
  if (trick.length === 0) return true;
  const ledSuit = trick[0].card.suit;
  if (card.suit === ledSuit) return true;
  return !hand.some(c => c.suit === ledSuit);
}

function makeRoomCode() {
  return crypto.randomBytes(3).toString('hex').toUpperCase();
}

// ── BOT AI ───────────────────────────────────────────────
function botBid(hand, trump, totalTricks) {
  let strength = 0;
  for (const card of hand) {
    const rv = rankVal(card.rank);
    if (card.suit === trump) {
      if (rv >= 12) strength += 1;
      else if (rv >= 9) strength += 0.6;
      else strength += 0.3;
    } else {
      if (rv === 14) strength += 0.7;
      else if (rv === 13) strength += 0.4;
    }
  }
  if (strength < 0.8 && Math.random() < 0.5) return 0;
  return Math.min(Math.round(strength + (Math.random() - 0.5)), totalTricks);
}

function getLegal(hand, trick) {
  if (trick.length === 0) return [...hand];
  const ledSuit = trick[0].card.suit;
  const hasSuit = hand.filter(c => c.suit === ledSuit);
  return hasSuit.length > 0 ? hasSuit : [...hand];
}

function currentWinner(trick, trump) {
  if (!trick.length) return null;
  return trickWinner(trick, trump);
}

function botPlayToWin(hand, trick, trump, playerIdx) {
  const legal = getLegal(hand, trick);
  if (trick.length === 0) {
    const trumps = legal.filter(c => c.suit === trump).sort((a,b) => rankVal(b.rank)-rankVal(a.rank));
    if (trumps.length) return trumps[0];
    return legal.sort((a,b) => rankVal(b.rank)-rankVal(a.rank))[0];
  }
  const winnerNow = currentWinner(trick, trump);
  if (winnerNow === playerIdx) return legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  const canWin = legal.filter(c => {
    const fake = [...trick, {playerIdx, card: c}];
    return trickWinner(fake, trump) === playerIdx;
  });
  if (canWin.length) return canWin.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  return legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
}

function botPlayToDuck(hand, trick, trump, playerIdx) {
  const legal = getLegal(hand, trick);
  if (trick.length === 0) {
    const nonTrump = legal.filter(c => c.suit !== trump).sort((a,b) => rankVal(a.rank)-rankVal(b.rank));
    return nonTrump.length ? nonTrump[0] : legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  }
  const losing = legal.filter(c => {
    const fake = [...trick, {playerIdx, card: c}];
    return trickWinner(fake, trump) !== playerIdx;
  });
  if (losing.length) return losing.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  return legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
}

function botPlayTrapper(hand, trick, trump, playerIdx, targetIdx) {
  const legal = getLegal(hand, trick);
  if (trick.length === 0) {
    const nonTrump = legal.filter(c => c.suit !== trump);
    const pool = nonTrump.length ? nonTrump : legal;
    return pool.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  }
  const winnerNow = currentWinner(trick, trump);
  if (winnerNow === targetIdx) {
    const notBeating = legal.filter(c => {
      const fake = [...trick, {playerIdx, card: c}];
      return trickWinner(fake, trump) !== playerIdx;
    });
    if (notBeating.length) return notBeating.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  }
  return botPlayToDuck(hand, trick, trump, playerIdx);
}

function chooseBotCard(s, playerIdx) {
  const hand = s.hands[playerIdx];
  const trick = s.currentTrick;
  const trump = s.trump;
  const bid = s.bids[playerIdx];
  const won = s.tricksWon[playerIdx];
  const n = s.hands.length;

  if (bid === 0) {
    if (won > 0) return botPlayToWin(hand, trick, trump, playerIdx);
    return botPlayToDuck(hand, trick, trump, playerIdx);
  }

  if (won < bid) return botPlayToWin(hand, trick, trump, playerIdx);

  // met bid — trapper mode?
  const totalBid = s.bids.reduce((sum, b) => sum + (b||0), 0);
  const spare = s.totalTricks - s.trickCount - totalBid;
  if (spare >= 1) {
    const zeroBidders = s.bids
      .map((b,i) => ({b,i}))
      .filter(({b,i}) => b === 0 && s.tricksWon[i] === 0)
      .sort((a,b) => {
        // target highest scorer
        return 0; // simplified — just pick first
      });
    if (zeroBidders.length) {
      return botPlayTrapper(hand, trick, trump, playerIdx, zeroBidders[0].i);
    }
  }

  return botPlayToDuck(hand, trick, trump, playerIdx);
}

// ── ROOM MANAGEMENT ──────────────────────────────────────
function getRoom(code) { return rooms[code]; }

function publicRoom(room) {
  return {
    code: room.code,
    phase: room.phase,
    host: room.host,
    players: room.players.map(p => ({
      id: p.id, name: p.name, score: p.score,
      roundScores: p.roundScores, connected: p.connected, isBot: p.isBot||false,
    })),
    state: room.state ? {
      roundIdx: room.state.roundIdx,
      totalTricks: room.state.totalTricks,
      trickCount: room.state.trickCount,
      trump: room.state.trump,
      trumpCard: room.state.trumpCard,
      dealerIdx: room.state.dealerIdx,
      bids: room.state.bids,
      tricksWon: room.state.tricksWon,
      currentTrick: room.state.currentTrick,
      currentTurnIdx: room.state.currentTurnIdx,
      handSizes: room.state.hands.map(h => h.length),
      bidTurnIdx: room.state.bidTurnIdx,
      bidsCollected: room.state.bidsCollected,
      lastTrickWinner: room.state.lastTrickWinner,
      lastTrick: room.state.lastTrick,
      trickLeaderIdx: room.state.trickLeaderIdx,
    } : null,
  };
}

function playerView(room, socketId) {
  const base = publicRoom(room);
  if (!room.state) return base;
  const idx = room.players.findIndex(p => p.id === socketId);
  base.myIdx = idx;
  base.myHand = idx >= 0 ? room.state.hands[idx] : [];
  return base;
}

function openRoomsList() {
  return Object.values(rooms)
    .filter(r => r.phase === 'lobby' && r.players.some(p => !p.isBot))
    .map(r => ({
      code: r.code,
      host: r.players[0]?.name || '?',
      playerCount: r.players.filter(p => !p.isBot).length,
      botCount: r.players.filter(p => p.isBot).length,
      maxPlayers: 5,
    }));
}

function broadcastRoomsList() {
  io.emit('rooms_list', openRoomsList());
}

// ── GAME LOGIC ───────────────────────────────────────────
function dealRound(room) {
  const n = room.players.length;
  const cards = ROUND_SEQUENCE[room.state.roundIdx];
  const deck = makeDeck();
  const hands = [];
  for (let i = 0; i < n; i++) hands.push(deck.splice(0, cards));
  room.state.totalTricks = cards;
  room.state.trickCount = 0;
  room.state.hands = hands;
  room.state.trump = deck[0].suit;
  room.state.trumpCard = deck[0];
  room.state.bids = new Array(n).fill(null);
  room.state.tricksWon = new Array(n).fill(0);
  room.state.currentTrick = [];
  room.state.lastTrickWinner = null;
  room.state.lastTrick = null;
  room.state.bidTurnIdx = (room.state.dealerIdx + 1) % n;
  room.state.bidsCollected = 0;
  room.state.currentTurnIdx = room.state.bidTurnIdx;
  room.phase = 'bid';
}

function recordBid(room, playerIdx, bid) {
  const s = room.state;
  const n = room.players.length;
  s.bids[playerIdx] = bid;
  s.bidsCollected++;
  s.bidTurnIdx = (s.bidTurnIdx + 1) % n;
  s.currentTurnIdx = s.bidTurnIdx;

  if (s.bidsCollected === n) {
    let bestBid = -1, leaderIdx = (s.dealerIdx + 1) % n;
    for (let i = 0; i < n; i++) {
      const idx = ((s.dealerIdx + 1) + i) % n;
      if (s.bids[idx] > bestBid) { bestBid = s.bids[idx]; leaderIdx = idx; }
    }
    s.trickLeaderIdx = leaderIdx;
    s.currentTurnIdx = leaderIdx;
    room.phase = 'play';
  }
}

function recordPlay(room, playerIdx, card) {
  const s = room.state;
  const n = room.players.length;
  const hand = s.hands[playerIdx];
  const i = hand.findIndex(c => c.suit === card.suit && c.rank === card.rank);
  if (i < 0) return false;
  hand.splice(i, 1);
  s.currentTrick.push({ playerIdx, card });

  if (s.currentTrick.length === n) {
    const winner = trickWinner(s.currentTrick, s.trump);
    s.tricksWon[winner]++;
    s.trickCount++;
    s.lastTrickWinner = winner;
    s.lastTrick = s.currentTrick;
    s.currentTrick = [];

    if (s.trickCount >= s.totalTricks) {
      scoreRound(room);
      return 'round_over';
    } else {
      s.trickLeaderIdx = winner;
      s.currentTurnIdx = winner;
      return 'trick_over';
    }
  } else {
    s.currentTurnIdx = (s.trickLeaderIdx + s.currentTrick.length) % n;
    return 'card_played';
  }
}

function scoreRound(room) {
  const s = room.state;
  const n = room.players.length;
  for (let i = 0; i < n; i++) {
    const bid = s.bids[i], won = s.tricksWon[i];
    let delta = 0;
    if (bid === 0) { delta = won === 0 ? 25 : -25; }
    else if (won >= bid) { delta = bid * 10 + (won - bid); if (won === s.totalTricks) delta += 50; }
    else { delta = -(bid * 10); }
    room.players[i].score += delta;
    room.players[i].roundScores.push({ round: s.roundIdx + 1, bid, won, delta });
  }
  s.dealerIdx = (s.dealerIdx + 1) % n;
  s.roundIdx++;
}

function startNextRound(room) {
  if (room.state.roundIdx >= ROUND_SEQUENCE.length) { room.phase = 'gameover'; return false; }
  dealRound(room);
  return true;
}

// ── BOT TURN RUNNER ──────────────────────────────────────
function scheduleBotsIfNeeded(room) {
  const s = room.state;
  if (!s) return;
  const turnPlayer = room.players[s.currentTurnIdx];
  if (!turnPlayer || !turnPlayer.isBot) return;

  setTimeout(() => {
    if (!room.state) return;
    const s = room.state;
    const idx = s.currentTurnIdx;
    const player = room.players[idx];
    if (!player || !player.isBot) return;

    if (room.phase === 'bid') {
      const bid = botBid(s.hands[idx], s.trump, s.totalTricks);
      recordBid(room, idx, bid);
      broadcastViews(room);
      scheduleBotsIfNeeded(room);
    } else if (room.phase === 'play') {
      const card = chooseBotCard(s, idx);
      const result = recordPlay(room, idx, card);
      broadcastViews(room, result);
      if (result === 'round_over') {
        // wait for host to advance (or auto-advance after delay)
        setTimeout(() => {
          if (!room.state) return;
          const allBots = room.players.every(p => p.isBot);
          // auto-advance only if all human players are gone or after delay
          // Let host handle it via next_round event normally
        }, 2000);
      } else if (result === 'trick_over') {
        setTimeout(() => scheduleBotsIfNeeded(room), BOT_THINK_MS);
      } else {
        scheduleBotsIfNeeded(room);
      }
    }
  }, BOT_THINK_MS);
}

// ── SOCKET HANDLERS ──────────────────────────────────────
io.on('connection', (socket) => {

  socket.emit('rooms_list', openRoomsList());

  socket.on('create_room', ({ name }) => {
    const code = makeRoomCode();
    rooms[code] = {
      code, host: socket.id, phase: 'lobby',
      players: [{ id: socket.id, name, score: 0, roundScores: [], connected: true, isBot: false }],
      state: null,
    };
    socket.join(code);
    socket.emit('room_joined', { code, view: playerView(rooms[code], socket.id) });
    broadcastRoomsList();
  });

  socket.on('join_room', ({ code, name }) => {
    const room = getRoom(code.toUpperCase());
    if (!room) { socket.emit('error', 'Room not found.'); return; }
    if (room.phase !== 'lobby') { socket.emit('error', 'Game already in progress.'); return; }
    if (room.players.length >= 5) { socket.emit('error', 'Room is full (max 5 players).'); return; }
    if (room.players.some(p => p.name.toLowerCase() === name.toLowerCase())) {
      socket.emit('error', 'That name is taken. Choose another.'); return;
    }
    room.players.push({ id: socket.id, name, score: 0, roundScores: [], connected: true, isBot: false });
    socket.join(code.toUpperCase());
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
    io.to(room.code).emit('room_update', publicRoom(room));
    broadcastRoomsList();
  });

  socket.on('add_bot', ({ code }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'lobby') return;
    if (room.host !== socket.id) { socket.emit('error', 'Only the host can add bots.'); return; }
    if (room.players.length >= 5) { socket.emit('error', 'Room is full.'); return; }
    const usedNames = new Set(room.players.map(p => p.name));
    const botName = BOT_NAMES.find(n => !usedNames.has(n)) || `Bot${room.players.length}`;
    const botId = 'bot_' + crypto.randomBytes(4).toString('hex');
    room.players.push({ id: botId, name: botName, score: 0, roundScores: [], connected: true, isBot: true });
    io.to(room.code).emit('room_update', publicRoom(room));
    broadcastRoomsList();
  });

  socket.on('remove_bot', ({ code }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'lobby') return;
    if (room.host !== socket.id) { socket.emit('error', 'Only the host can remove bots.'); return; }
    const lastBotIdx = [...room.players].reverse().findIndex(p => p.isBot);
    if (lastBotIdx < 0) return;
    room.players.splice(room.players.length - 1 - lastBotIdx, 1);
    io.to(room.code).emit('room_update', publicRoom(room));
    broadcastRoomsList();
  });

  socket.on('start_game', ({ code }) => {
    const room = getRoom(code);
    if (!room) return;
    if (room.host !== socket.id) { socket.emit('error', 'Only the host can start.'); return; }
    if (room.players.length < 2) { socket.emit('error', 'Need at least 2 players.'); return; }
    const n = room.players.length;
    room.state = {
      roundIdx: 0, dealerIdx: Math.floor(Math.random() * n),
      hands: [], trump: null, trumpCard: null,
      bids: [], tricksWon: [], currentTrick: [],
      trickCount: 0, totalTricks: 0,
      bidTurnIdx: 0, bidsCollected: 0, currentTurnIdx: 0,
      trickLeaderIdx: 0, lastTrickWinner: null, lastTrick: null,
    };
    dealRound(room);
    broadcastViews(room);
    broadcastRoomsList();
    scheduleBotsIfNeeded(room);
  });

  socket.on('place_bid', ({ code, bid }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'bid') return;
    const playerIdx = room.players.findIndex(p => p.id === socket.id);
    if (playerIdx !== room.state.currentTurnIdx) { socket.emit('error', 'Not your turn to bid.'); return; }
    if (bid < 0 || bid > room.state.totalTricks) { socket.emit('error', 'Invalid bid.'); return; }
    recordBid(room, playerIdx, bid);
    broadcastViews(room);
    scheduleBotsIfNeeded(room);
  });

  socket.on('play_card', ({ code, card }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'play') return;
    const playerIdx = room.players.findIndex(p => p.id === socket.id);
    if (playerIdx !== room.state.currentTurnIdx) { socket.emit('error', 'Not your turn.'); return; }
    if (!isLegalPlay(room.state.hands[playerIdx], card, room.state.currentTrick)) {
      socket.emit('error', 'You must follow suit.'); return;
    }
    const result = recordPlay(room, playerIdx, card);
    broadcastViews(room, result);
    if (result !== 'round_over') scheduleBotsIfNeeded(room);
  });

  socket.on('next_round', ({ code }) => {
    const room = getRoom(code);
    if (!room || room.host !== socket.id) return;
    const continues = startNextRound(room);
    if (continues) { broadcastViews(room); scheduleBotsIfNeeded(room); }
    else io.to(room.code).emit('game_over', { players: room.players });
  });

  socket.on('get_rooms', () => {
    socket.emit('rooms_list', openRoomsList());
  });

  socket.on('rejoin_room', ({ code, name }) => {
    const room = getRoom(code.toUpperCase());
    if (!room) { socket.emit('error', 'Room not found.'); return; }
    const p = room.players.find(p => p.name.toLowerCase() === name.toLowerCase() && !p.isBot);
    if (!p) { socket.emit('error', 'Player not found.'); return; }
    p.id = socket.id; p.connected = true;
    socket.join(code.toUpperCase());
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
    io.to(room.code).emit('room_update', publicRoom(room));
  });

  socket.on('disconnect', () => {
    for (const code of Object.keys(rooms)) {
      const room = rooms[code];
      const p = room.players.find(p => p.id === socket.id);
      if (p) { p.connected = false; io.to(room.code).emit('room_update', publicRoom(room)); broadcastRoomsList(); }
    }
  });
});

function broadcastViews(room, result) {
  for (const p of room.players) {
    if (p.isBot) continue;
    const view = playerView(room, p.id);
    if (result) view.lastResult = result;
    io.to(p.id).emit('game_update', view);
  }
}

const PORT = process.env.PORT || 3000;
httpServer.listen(PORT, () => console.log(`Five to Ten server on port ${PORT}`));
