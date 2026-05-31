const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const crypto = require('crypto');

const app = express();
const httpServer = http.createServer(app);
const io = new Server(httpServer);

app.use(express.static(path.join(__dirname, 'public')));

// ── GAME CONSTANTS ──────────────────────────────────────
const SUITS = ['♠','♥','♦','♣'];
const RANKS = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const RANK_VAL = {2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,10:10,J:11,Q:12,K:13,A:14};
const ROUND_SEQUENCE = [5,6,7,8,9,10,10,9,8,7,6,5];

// rooms[roomCode] = { players, state }
const rooms = {};

// ── UTILITIES ───────────────────────────────────────────
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

// ── ROOM MANAGEMENT ─────────────────────────────────────
function getRoom(code) { return rooms[code]; }

function createRoom(hostName, hostSocketId) {
  const code = makeRoomCode();
  rooms[code] = {
    code,
    host: hostSocketId,
    phase: 'lobby', // lobby | bid | play
    players: [{
      id: hostSocketId,
      name: hostName,
      score: 0,
      roundScores: [],
      connected: true,
    }],
    state: null,
  };
  return rooms[code];
}

function publicRoom(room) {
  // send each player only their own hand; others see hand size only
  return {
    code: room.code,
    phase: room.phase,
    players: room.players.map(p => ({
      id: p.id,
      name: p.name,
      score: p.score,
      roundScores: p.roundScores,
      connected: p.connected,
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

// ── GAME LOGIC ──────────────────────────────────────────
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
  room.state.bidTurnIdx = (room.state.dealerIdx + 1) % n;
  room.state.bidsCollected = 0;
  room.state.currentTurnIdx = room.state.bidTurnIdx;
  room.phase = 'bid';
}

function recordBid(room, playerIdx, bid) {
  const s = room.state;
  s.bids[playerIdx] = bid;
  s.bidsCollected++;
  s.bidTurnIdx = (s.bidTurnIdx + 1) % room.players.length;
  s.currentTurnIdx = s.bidTurnIdx;

  if (s.bidsCollected === room.players.length) {
    // determine who leads first trick
    const n = room.players.length;
    let bestBid = -1;
    let leaderIdx = (s.dealerIdx + 1) % n;
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
  const hand = s.hands[playerIdx];
  const i = hand.findIndex(c => c.suit === card.suit && c.rank === card.rank);
  if (i < 0) return false;
  hand.splice(i, 1);
  s.currentTrick.push({ playerIdx, card });

  const n = room.players.length;
  if (s.currentTrick.length === n) {
    // resolve trick
    const winner = trickWinner(s.currentTrick, s.trump);
    s.tricksWon[winner]++;
    s.trickCount++;
    s.lastTrickWinner = winner;
    s.lastTrick = s.currentTrick;
    s.currentTrick = [];

    if (s.trickCount >= s.totalTricks) {
      // end of round — score
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
    const bid = s.bids[i];
    const won = s.tricksWon[i];
    let delta = 0;
    if (bid === 0) {
      delta = won === 0 ? 25 : -25;
    } else {
      if (won >= bid) {
        delta = bid * 10 + (won - bid);
        if (won === s.totalTricks) delta += 50;
      } else {
        delta = -(bid * 10);
      }
    }
    room.players[i].score += delta;
    room.players[i].roundScores.push({ round: s.roundIdx + 1, bid, won, delta });
  }
  s.dealerIdx = (s.dealerIdx + 1) % n;
  s.roundIdx++;
}

function startNextRound(room) {
  if (room.state.roundIdx >= ROUND_SEQUENCE.length) {
    room.phase = 'gameover';
    return false;
  }
  dealRound(room);
  return true;
}

// ── SOCKET HANDLERS ─────────────────────────────────────
io.on('connection', (socket) => {

  socket.on('create_room', ({ name }) => {
    const room = createRoom(name, socket.id);
    socket.join(room.code);
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
  });

  socket.on('join_room', ({ code, name }) => {
    const room = getRoom(code.toUpperCase());
    if (!room) { socket.emit('error', 'Room not found.'); return; }
    if (room.phase !== 'lobby') { socket.emit('error', 'Game already in progress.'); return; }
    if (room.players.length >= 5) { socket.emit('error', 'Room is full (max 5 players).'); return; }
    if (room.players.some(p => p.name.toLowerCase() === name.toLowerCase())) {
      socket.emit('error', 'That name is already taken in this room.'); return;
    }
    room.players.push({ id: socket.id, name, score: 0, roundScores: [], connected: true });
    socket.join(code.toUpperCase());
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
    io.to(room.code).emit('room_update', publicRoom(room));
  });

  socket.on('start_game', ({ code }) => {
    const room = getRoom(code);
    if (!room) return;
    if (room.host !== socket.id) { socket.emit('error', 'Only the host can start the game.'); return; }
    if (room.players.length < 2) { socket.emit('error', 'Need at least 2 players to start.'); return; }
    const n = room.players.length;
    room.state = {
      roundIdx: 0,
      dealerIdx: Math.floor(Math.random() * n),
      hands: [],
      trump: null,
      trumpCard: null,
      bids: [],
      tricksWon: [],
      currentTrick: [],
      trickCount: 0,
      totalTricks: 0,
      bidTurnIdx: 0,
      bidsCollected: 0,
      currentTurnIdx: 0,
      trickLeaderIdx: 0,
      lastTrickWinner: null,
      lastTrick: null,
    };
    dealRound(room);
    broadcastViews(room);
  });

  socket.on('place_bid', ({ code, bid }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'bid') return;
    const playerIdx = room.players.findIndex(p => p.id === socket.id);
    if (playerIdx !== room.state.currentTurnIdx) { socket.emit('error', 'Not your turn to bid.'); return; }
    if (bid < 0 || bid > room.state.totalTricks) { socket.emit('error', 'Invalid bid.'); return; }
    recordBid(room, playerIdx, bid);
    broadcastViews(room);
  });

  socket.on('play_card', ({ code, card }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'play') return;
    const playerIdx = room.players.findIndex(p => p.id === socket.id);
    if (playerIdx !== room.state.currentTurnIdx) { socket.emit('error', 'Not your turn to play.'); return; }
    if (!isLegalPlay(room.state.hands[playerIdx], card, room.state.currentTrick)) {
      socket.emit('error', 'You must follow suit.'); return;
    }
    const result = recordPlay(room, playerIdx, card);
    broadcastViews(room, result);
  });

  socket.on('next_round', ({ code }) => {
    const room = getRoom(code);
    if (!room) return;
    if (room.host !== socket.id) return;
    const continues = startNextRound(room);
    if (continues) broadcastViews(room);
    else io.to(room.code).emit('game_over', { players: room.players });
  });

  socket.on('disconnect', () => {
    for (const code of Object.keys(rooms)) {
      const room = rooms[code];
      const p = room.players.find(p => p.id === socket.id);
      if (p) {
        p.connected = false;
        io.to(room.code).emit('room_update', publicRoom(room));
      }
    }
  });

  socket.on('rejoin_room', ({ code, name }) => {
    const room = getRoom(code.toUpperCase());
    if (!room) { socket.emit('error', 'Room not found.'); return; }
    const p = room.players.find(p => p.name.toLowerCase() === name.toLowerCase());
    if (!p) { socket.emit('error', 'Player not found in room.'); return; }
    p.id = socket.id;
    p.connected = true;
    socket.join(code.toUpperCase());
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
    io.to(room.code).emit('room_update', publicRoom(room));
  });
});

function broadcastViews(room, result) {
  for (const p of room.players) {
    const view = playerView(room, p.id);
    if (result) view.lastResult = result;
    io.to(p.id).emit('game_update', view);
  }
}

const PORT = process.env.PORT || 3000;
httpServer.listen(PORT, () => console.log(`Five to Ten server running on port ${PORT}`));
