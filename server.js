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

const BOT_DIFFICULTY = {
  easy:   { sims: 0,   bidVariance: 1.5, playSmart: false, master: false, playNoise: 0.70 },
  medium: { sims: 75,  bidVariance: 0.7, playSmart: true,  master: false, playNoise: 0.20 },
  hard:   { sims: 200, bidVariance: 0.25,playSmart: true,  master: false, playNoise: 0.05 },
  master: { sims: 600, bidVariance: 0.05,playSmart: true,  master: true,  playNoise: 0.0, displayName: 'STEVIL' },
};
const MAX_ROOMS = 20;              // total open rooms allowed at once
const MAX_ROOMS_PER_IP = 2;        // one person can't hog all slots
const ROOM_IDLE_MS = 30 * 60 * 1000; // auto-delete rooms idle for 30 min

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

// ── BOT AI (STRONG) ──────────────────────────────────────

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

// Build a Set of played card keys from state
function playedSet(s) {
  return new Set((s.playedCards || []).map(c => c.rank + c.suit));
}

// Is this card the highest remaining in its suit?
function isHighestRemaining(card, played) {
  for (const rank of RANKS) {
    if (rankVal(rank) > rankVal(card.rank) && !played.has(rank + card.suit)) return false;
  }
  return true;
}

// Trumps still unplayed
function trumpsLeft(trump, played) {
  return RANKS.filter(r => !played.has(r + trump)).length;
}

// Is this card a sure trick-winner?
function isSureWinner(card, trump, played) {
  if (!isHighestRemaining(card, played)) return false;
  if (card.suit === trump) return true;
  return trumpsLeft(trump, played) === 0;
}

// Minimum card that wins the current trick (cheapest winner)
function minToWin(legal, trick, trump, playerIdx) {
  const canWin = legal.filter(c => {
    const fake = [...trick, { playerIdx, card: c }];
    return trickWinner(fake, trump) === playerIdx;
  });
  if (!canWin.length) return null;
  // prefer cheapest non-trump winner; fall back to cheapest trump
  const nonTrumpWins = canWin.filter(c => c.suit !== trump);
  const pool = nonTrumpWins.length ? nonTrumpWins : canWin;
  return pool.sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
}

// Best lead when trying to win tricks
function bestLeadToWin(hand, trump, played) {
  // Lead sure winners first (highest first to clear the way)
  const sure = hand.filter(c => isSureWinner(c, trump, played))
    .sort((a, b) => {
      if (a.suit === trump && b.suit !== trump) return -1;
      if (a.suit !== trump && b.suit === trump) return 1;
      return rankVal(b.rank) - rankVal(a.rank);
    });
  if (sure.length) return sure[0];
  // Lead highest trump
  const trumpCards = hand.filter(c => c.suit === trump).sort((a, b) => rankVal(b.rank) - rankVal(a.rank));
  if (trumpCards.length) return trumpCards[0];
  // Lead highest card overall
  return hand.slice().sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0];
}

// Best lead when trying to duck (avoid tricks)
function bestLeadToDuck(hand, trump, played) {
  // Lead from a suit where our highest card is low (hard for us to win)
  const nonTrump = hand.filter(c => c.suit !== trump);
  const pool = nonTrump.length ? nonTrump : hand;
  return pool.slice().sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
}

// ── MONTE CARLO BIDDING ──────────────────────────────────
// At bid time the AI only knows: its own hand + which card is trump.
// We simulate many random deals of the remaining cards to estimate
// how many tricks this hand will win on average.

// ── SIMULATION PLAY PROFILES ─────────────────────────────
// profile: 'random' (Easy), 'noisy' (Medium), 'smart' (Hard/Master/Human)

function quickSimBid(hand, trump) {
  let est = 0;
  for (const card of hand) {
    const rv = rankVal(card.rank);
    if (card.suit === trump) {
      if (rv >= 13) est += 0.9; else if (rv >= 11) est += 0.6; else est += 0.25;
    } else {
      if (rv === 14) est += 0.65; else if (rv === 13) est += 0.35;
    }
  }
  return Math.round(est);
}

function simPlaySmart(hand, trick, trump, bid) {
  // Smart: zero bidders duck; everyone else always attacks (extra tricks = +1pt)
  const legal = getLegal(hand, trick);
  if (bid === 0) {
    if (!trick.length) {
      const nt = legal.filter(c => c.suit !== trump).sort((a,b) => rankVal(a.rank)-rankVal(b.rank));
      return nt.length ? nt[0] : legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
    }
    const losing = legal.filter(c => trickWinner([...trick,{playerIdx:99,card:c}],trump) !== 99);
    return losing.length
      ? losing.sort((a,b) => rankVal(b.rank)-rankVal(a.rank))[0]
      : legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  }
  if (!trick.length) {
    const t = legal.filter(c => c.suit === trump).sort((a,b) => rankVal(b.rank)-rankVal(a.rank));
    return t.length ? t[0] : legal.sort((a,b) => rankVal(b.rank)-rankVal(a.rank))[0];
  }
  let bestCard = trick[0].card;
  for (const e of trick) if (beats(e.card, bestCard, trump)) bestCard = e.card;
  const canBeat = legal.filter(c => beats(c, bestCard, trump));
  if (canBeat.length) return canBeat.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
  return legal.sort((a,b) => rankVal(a.rank)-rankVal(b.rank))[0];
}

function simPlayByProfile(hand, trick, trump, bid, profile) {
  const legal = getLegal(hand, trick);
  if (profile === 'random')       return legal[Math.floor(Math.random() * legal.length)];
  if (profile === 'noisy-heavy') {
    if (Math.random() < 0.40) return legal[Math.floor(Math.random() * legal.length)];
    return simPlaySmart(hand, trick, trump, bid);
  }
  if (profile === 'noisy-light') {
    if (Math.random() < 0.10) return legal[Math.floor(Math.random() * legal.length)];
    return simPlaySmart(hand, trick, trump, bid);
  }
  return simPlaySmart(hand, trick, trump, bid); // 'smart'
}

// Map difficulty/type to a sim profile
function playerToProfile(player, botDifficulty) {
  if (!player.isBot) return 'smart'; // humans modeled as Hard
  switch (botDifficulty || 'medium') {
    case 'easy':   return 'random';
    case 'medium': return 'noisy-heavy';  // 40% random
    case 'hard':   return 'noisy-light';  // 10% random
    case 'master':
    default:       return 'smart';
  }
}

// opponentProfiles[i] = profile string for allHands[i+1] (opponents in seat order)
function runOneSimulation(allHands, trump, numPlayers, handSize, opponentProfiles) {
  const hands = allHands.map(h => h.map(c => ({...c})));
  // profiles[0] = bidder (always smart — it's us); profiles[1..n-1] = opponents
  const profiles = ['smart', ...opponentProfiles];
  const simBids = allHands.map(h => quickSimBid(h, trump));
  const simWon  = new Array(numPlayers).fill(0);
  let myTricks = 0, leader = 0;

  for (let t = 0; t < handSize; t++) {
    const trick = [];
    for (let pos = 0; pos < numPlayers; pos++) {
      const pIdx = (leader + pos) % numPlayers;
      const card = simPlayByProfile(hands[pIdx], trick, trump, simBids[pIdx], profiles[pIdx]);
      hands[pIdx].splice(hands[pIdx].findIndex(c => c.rank === card.rank && c.suit === card.suit), 1);
      trick.push({ playerIdx: pIdx, card });
    }
    const winner = trickWinner(trick, trump);
    simWon[winner]++;
    if (winner === 0) myTricks++;
    leader = winner;
  }
  return myTricks;
}

function botBid(hand, trump, totalTricks, numPlayers, trumpCard, numSims = 200, bidVariance = 0.2, opponentProfiles = null) {
  // Build the unseen card pool: full deck minus my hand minus the shown trump card
  const mySet = new Set(hand.map(c => c.rank + c.suit));
  const trumpKey = trumpCard ? trumpCard.rank + trumpCard.suit : null;
  const unseen = [];
  for (const suit of SUITS) {
    for (const rank of RANKS) {
      const key = rank + suit;
      if (!mySet.has(key) && key !== trumpKey) unseen.push({ suit, rank });
    }
  }

  const handSize = hand.length;
  const numOpponents = numPlayers - 1;
  let totalWon = 0;

  for (let sim = 0; sim < numSims; sim++) {
    // Randomly deal handSize cards to each opponent from the unseen pool
    const pool = shuffle([...unseen]);
    const allHands = [hand]; // player 0 = bidder
    for (let i = 0; i < numOpponents; i++) {
      allHands.push(pool.slice(i * handSize, (i + 1) * handSize));
    }
    // default: all opponents modeled as smart if no profiles provided
    const profiles = opponentProfiles || new Array(numPlayers - 1).fill('smart');
    totalWon += runOneSimulation(allHands, trump, numPlayers, handSize, profiles);
  }

  const expected = totalWon / numSims;

  // Zero bid decision: scale probability with how weak the hand looks.
  // At expected=0.0 → always bid 0. At expected=0.9 → 10% chance. Above 0.9 → never.
  if (expected < 0.9) {
    const zeroProbability = Math.max(0, (0.9 - expected) / 0.9);
    if (Math.random() < zeroProbability) return 0;
  }

  // Apply variance — easy bots are noisier, hard bots are precise
  const noise = (Math.random() * 2 - 1) * bidVariance;
  const bid = Math.round(expected + noise);
  return Math.max(0, Math.min(bid, totalTricks));
}

// ── PLAY DECISIONS ───────────────────────────────────────
function chooseBotCard(s, playerIdx, playSmart = true) {
  const hand = s.hands[playerIdx];
  const trick = s.currentTrick;
  const trump = s.trump;
  const bid = s.bids[playerIdx];
  const won = s.tricksWon[playerIdx];
  const played = playedSet(s);
  // Easy bots: just play a random legal card
  const legal = getLegal(hand, trick);
  if (!playSmart) return legal[Math.floor(Math.random() * legal.length)];

  const tricksLeft = s.totalTricks - s.trickCount;
  const stillNeed = bid - won;
  const isLast = trick.length === s.hands.length - 1; // we are last to play

  // ── ZERO BIDDER ─────────────────────────────────────────
  if (bid === 0) {
    if (won > 0) {
      // Already set — go rogue, try to steal from opponents
      return playToWin(legal, trick, trump, playerIdx, played);
    }
    // Desperately avoid winning
    return playToDuck(legal, trick, trump, playerIdx);
  }

  // ── NEED MORE TRICKS ─────────────────────────────────────
  if (stillNeed > 0) {
    if (trick.length === 0) {
      // Leading: lead best winner
      return bestLeadToWin(hand, trump, played);
    }
    // Following: use minimum card that wins, else dump lowest
    const win = minToWin(legal, trick, trump, playerIdx);
    if (win) return win;
    // Can't win — dump lowest non-trump
    const dumpNonTrump = legal.filter(c => c.suit !== trump).sort((a, b) => rankVal(a.rank) - rankVal(b.rank));
    return dumpNonTrump.length ? dumpNonTrump[0] : legal.sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
  }

  // ── MET BID ──────────────────────────────────────────────
  // Check trapper mode
  const players = s.hands; // use for count
  const n = players.length;
  const totalBid = s.bids.reduce((sum, b) => sum + (b || 0), 0);
  const spareTricks = s.totalTricks - s.trickCount - totalBid;

  if (spareTricks >= 1) {
    // Find clean zero-bidders sorted by score (target highest scorer)
    const zeroBidderTargets = s.bids
      .map((b, i) => ({ b, i }))
      .filter(({ b, i }) => b === 0 && s.tricksWon[i] === 0)
      .sort((a, z) => 0); // scores not available here; first found is fine

    if (zeroBidderTargets.length) {
      const targetIdx = zeroBidderTargets[0].i;
      return playTrapper(legal, trick, trump, playerIdx, targetIdx, played);
    }
  }

  // Just duck — shed extra tricks carefully
  if (trick.length === 0) return bestLeadToDuck(hand, trump, played);
  return playToDuck(legal, trick, trump, playerIdx);
}

function playToWin(legal, trick, trump, playerIdx, played) {
  if (trick.length === 0) {
    // Lead sure winners, then high trumps, then highest card
    const sure = legal.filter(c => isSureWinner(c, trump, played)).sort((a, b) => rankVal(b.rank) - rankVal(a.rank));
    if (sure.length) return sure[0];
    const trumpCards = legal.filter(c => c.suit === trump).sort((a, b) => rankVal(b.rank) - rankVal(a.rank));
    if (trumpCards.length) return trumpCards[0];
    return legal.slice().sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0];
  }
  const winnerNow = currentWinner(trick, trump);
  if (winnerNow === playerIdx) {
    // Already winning — play lowest to conserve good cards
    return legal.slice().sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
  }
  const win = minToWin(legal, trick, trump, playerIdx);
  if (win) return win;
  // Can't win — dump lowest
  return legal.slice().sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
}

function playToDuck(legal, trick, trump, playerIdx) {
  if (trick.length === 0) return bestLeadToDuck(legal, trump, null);
  const losing = legal.filter(c => {
    const fake = [...trick, { playerIdx, card: c }];
    return trickWinner(fake, trump) !== playerIdx;
  });
  if (losing.length) return losing.slice().sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0]; // highest losing card (waste big cards safely)
  // Forced to win — play lowest
  return legal.slice().sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
}

function playTrapper(legal, trick, trump, playerIdx, targetIdx, played) {
  if (trick.length === 0) {
    // Lead second-lowest non-trump — looks weak, may force zero bidder to win
    const nonTrump = legal.filter(c => c.suit !== trump).sort((a, b) => rankVal(a.rank) - rankVal(b.rank));
    if (nonTrump.length > 1) return nonTrump[1];
    if (nonTrump.length) return nonTrump[0];
    return legal.slice().sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
  }
  const winnerNow = currentWinner(trick, trump);
  if (winnerNow === targetIdx) {
    // Zero bidder is winning — do NOT rescue them
    const notBeating = legal.filter(c => {
      const fake = [...trick, { playerIdx, card: c }];
      return trickWinner(fake, trump) !== playerIdx;
    });
    if (notBeating.length) return notBeating.slice().sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0];
  }
  return playToDuck(legal, trick, trump, playerIdx);
}

// ── MASTER PLAY ──────────────────────────────────────────
function chooseBotCardMaster(s, playerIdx) {
  const hand = s.hands[playerIdx];
  const trick = s.currentTrick;
  const trump = s.trump;
  const bid = s.bids[playerIdx];
  const won = s.tricksWon[playerIdx];
  const legal = getLegal(hand, trick);
  const ps = playedSet(s);
  const voids = s.voidPlayers || {};
  const n = s.hands.length;

  // Find clean zero bidders sorted by score (highest score = most dangerous)
  const zeroBidderTargets = s.bids
    .map((b, i) => ({ b, i, score: 0 })) // scores not in state but we can rank by bid/won
    .filter(({ b, i }) => b === 0 && s.tricksWon[i] === 0 && i !== playerIdx)
    .sort((a, z) => z.score - a.score);
  const target = zeroBidderTargets.length ? zeroBidderTargets[0].i : null;

  // ── ZERO BIDDER ─────────────────────────────────────────
  if (bid === 0) {
    if (won > 0) return playToWin(legal, trick, trump, playerIdx, ps); // rogue
    if (!trick.length) {
      // Lead lowest card in the suit where we have the most cards (safest exit)
      const suitCounts = {};
      for (const c of hand) suitCounts[c.suit] = (suitCounts[c.suit] || 0) + 1;
      const safeSuit = Object.keys(suitCounts).filter(s => s !== trump)
        .sort((a, b) => suitCounts[b] - suitCounts[a])[0];
      const pool = safeSuit ? legal.filter(c => c.suit === safeSuit) : legal;
      return (pool.length ? pool : legal).sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
    }
    const losing = legal.filter(c => trickWinner([...trick, { playerIdx, card: c }], trump) !== playerIdx);
    return losing.length
      ? losing.sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0]
      : legal.sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
  }

  // ── NEED MORE TRICKS ─────────────────────────────────────
  const stillNeed = bid - won;
  if (stillNeed > 0) {
    if (!trick.length) return bestLeadToWin(hand, trump, ps);
    const win = minToWin(legal, trick, trump, playerIdx);
    if (win) return win;
    const dump = legal.filter(c => c.suit !== trump).sort((a, b) => rankVal(a.rank) - rankVal(b.rank));
    return dump.length ? dump[0] : legal.sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
  }

  // ── MET BID ──────────────────────────────────────────────
  // Always try to win more (extra tricks = +1 pt each)
  // BUT if a clean zero bidder exists, prioritize trapping them

  if (target !== null) {
    // Master trapper: use void knowledge to pick the most dangerous lead
    if (!trick.length) {
      // Find a suit where target is known to be void — leads there force them to trump
      const voidSuits = SUITS.filter(s =>
        s !== trump && voids[s] && voids[s].includes(target)
      );
      if (voidSuits.length) {
        // Lead lowest card in a suit target is void in — they'll have to trump (risk winning)
        const voidLeads = legal.filter(c => voidSuits.includes(c.suit))
          .sort((a, b) => rankVal(a.rank) - rankVal(b.rank));
        if (voidLeads.length) return voidLeads[0];
      }
      // No known void — lead second-lowest non-trump to look weak
      const nonTrump = legal.filter(c => c.suit !== trump).sort((a, b) => rankVal(a.rank) - rankVal(b.rank));
      if (nonTrump.length > 1) return nonTrump[1];
      if (nonTrump.length) return nonTrump[0];
    }

    // Following: if target is currently winning, let them keep it
    const winnerNow = currentWinner(trick, trump);
    if (winnerNow === target) {
      const notBeating = legal.filter(c => trickWinner([...trick, { playerIdx, card: c }], trump) !== playerIdx);
      if (notBeating.length) return notBeating.sort((a, b) => rankVal(b.rank) - rankVal(a.rank))[0];
    }
  }

  // No trap opportunity — just try to win extra tricks (worth +1 each)
  if (!trick.length) return bestLeadToWin(hand, trump, ps);
  const win = minToWin(legal, trick, trump, playerIdx);
  if (win) return win;
  return legal.sort((a, b) => rankVal(a.rank) - rankVal(b.rank))[0];
}

// ── ROOM MANAGEMENT ──────────────────────────────────────
function getRoom(code) { return rooms[code]; }

function publicRoom(room) {
  return {
    code: room.code,
    phase: room.phase,
    host: room.host,
    botDifficulty: room.botDifficulty || 'medium',
    players: room.players.map(p => ({
      id: p.id, name: p.name, score: p.score,
      roundScores: p.roundScores, connected: p.connected, isBot: p.isBot||false,
    })),
    roundTotal: (room.roundSeq || ROUND_SEQUENCE).length,
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
  const seq = room.roundSeq || ROUND_SEQUENCE;
  const cards = seq[room.state.roundIdx];
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
  room.state.playedCards = [];
  room.state.voidPlayers = {}; // voidPlayers[suit] = [playerIdx, ...]
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
  s.playedCards = s.playedCards || [];
  s.playedCards.push(card);

  // Track void suits: if player didn't follow the led suit, they're void in it
  if (s.currentTrick.length > 0) {
    const ledSuit = s.currentTrick[0].card.suit;
    if (card.suit !== ledSuit) {
      s.voidPlayers = s.voidPlayers || {};
      if (!s.voidPlayers[ledSuit]) s.voidPlayers[ledSuit] = [];
      if (!s.voidPlayers[ledSuit].includes(playerIdx)) s.voidPlayers[ledSuit].push(playerIdx);
    }
  }

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
    else if (won >= bid) { delta = bid * 10 + (won - bid); }
    else { delta = -(bid * 10); }
    room.players[i].score += delta;
    room.players[i].roundScores.push({ round: s.roundIdx + 1, bid, won, delta });
  }
  s.dealerIdx = (s.dealerIdx + 1) % n;
  s.roundIdx++;
}

function startNextRound(room) {
  const seq = room.roundSeq || ROUND_SEQUENCE;
  if (room.state.roundIdx >= seq.length) { room.phase = 'gameover'; return false; }
  dealRound(room);
  return true;
}

// If the final round just ended, end the game directly (no host action needed).
function maybeEndGame(room) {
  const seq = room.roundSeq || ROUND_SEQUENCE;
  if (room.state && room.state.roundIdx >= seq.length) {
    room.phase = 'gameover';
    io.to(room.code).emit('game_over', { players: room.players });
    return true;
  }
  return false;
}

// ── BOT TURN RUNNER ──────────────────────────────────────
function scheduleBotsIfNeeded(room) {
  const s = room.state;
  if (!s) return;
  const turnPlayer = room.players[s.currentTurnIdx];
  if (!turnPlayer || !turnPlayer.isBot) return;

  setTimeout(() => {
    if (!room.state) return;
    try {
      runBotTurn(room);
    } catch (err) {
      console.error(`Bot turn error in room ${room.code}:`, err);
      // Never freeze: fall back to a safe legal move so the game keeps going.
      try {
        runBotFallback(room);
      } catch (err2) {
        console.error(`Bot fallback also failed in room ${room.code}:`, err2);
        const s2 = room.state;
        io.to(room.code).emit('game_error', {
          code: `BOT-${room.code}-R${s2 ? s2.roundIdx : '?'}-P${s2 ? s2.currentTurnIdx : '?'}`,
          msg: 'A computer player hit an error. Tap Resync to recover.',
        });
      }
    }
  }, BOT_THINK_MS);
}

// The normal bot move (may throw if AI logic hits a bad state).
function runBotTurn(room) {
  const s = room.state;
  const idx = s.currentTurnIdx;
  const player = room.players[idx];
  if (!player || !player.isBot) return;

  if (room.phase === 'bid') {
    const diff = BOT_DIFFICULTY[room.botDifficulty || 'medium'];
    const n = room.players.length;
    const opponentProfiles = [];
    for (let i = 1; i < n; i++) {
      const oppIdx = (idx + i) % n;
      opponentProfiles.push(playerToProfile(room.players[oppIdx], room.botDifficulty));
    }
    const bid = botBid(s.hands[idx], s.trump, s.totalTricks, n, s.trumpCard, diff.sims, diff.bidVariance, opponentProfiles);
    recordBid(room, idx, bid);
    broadcastViews(room);
    scheduleBotsIfNeeded(room);
  } else if (room.phase === 'play') {
    const diff = BOT_DIFFICULTY[room.botDifficulty || 'medium'];
    let card;
    if (diff.master) {
      card = chooseBotCardMaster(s, idx);
    } else {
      const smartCard = chooseBotCard(s, idx, diff.playSmart);
      if (diff.playNoise > 0 && Math.random() < diff.playNoise) {
        const legal = getLegal(s.hands[idx], s.currentTrick);
        card = legal[Math.floor(Math.random() * legal.length)];
      } else {
        card = smartCard;
      }
    }
    finishBotPlay(room, idx, card);
  }
}

// Safe fallback: a guaranteed-legal move, used if the normal AI throws.
function runBotFallback(room) {
  const s = room.state;
  const idx = s.currentTurnIdx;
  const player = room.players[idx];
  if (!player || !player.isBot) return;

  if (room.phase === 'bid') {
    recordBid(room, idx, 0);
    broadcastViews(room);
    scheduleBotsIfNeeded(room);
  } else if (room.phase === 'play') {
    const legal = getLegal(s.hands[idx], s.currentTrick);
    if (!legal.length) return;
    finishBotPlay(room, idx, legal[Math.floor(Math.random() * legal.length)]);
  }
}

// Shared play-resolution used by both the normal turn and the fallback.
function finishBotPlay(room, idx, card) {
  const result = recordPlay(room, idx, card);
  broadcastViews(room, result);
  if (result === 'round_over') {
    if (room.state.roundIdx >= (room.roundSeq||ROUND_SEQUENCE).length) setTimeout(() => maybeEndGame(room), 2500);
  } else if (result === 'trick_over') {
    setTimeout(() => scheduleBotsIfNeeded(room), BOT_THINK_MS);
  } else {
    scheduleBotsIfNeeded(room);
  }
}

// ── SOCKET HANDLERS ──────────────────────────────────────
io.on('connection', (socket) => {

  socket.emit('rooms_list', openRoomsList());

  socket.on('create_room', ({ name }) => {
    // global room cap
    const openRooms = Object.values(rooms).filter(r => r.phase === 'lobby');
    if (openRooms.length >= MAX_ROOMS) {
      socket.emit('error', 'Server is full — too many open games. Try again later.'); return;
    }
    // per-IP cap
    const ip = socket.handshake.headers['x-forwarded-for']?.split(',')[0].trim() || socket.handshake.address;
    const byThisIP = openRooms.filter(r => r.creatorIP === ip).length;
    if (byThisIP >= MAX_ROOMS_PER_IP) {
      socket.emit('error', 'You already have an open game. Please start or close it first.'); return;
    }
    const code = makeRoomCode();
    rooms[code] = {
      code, host: socket.id, phase: 'lobby', creatorIP: ip, lastActivity: Date.now(),
      players: [{ id: socket.id, name, score: 0, roundScores: [], connected: true, isBot: false }],
      state: null,
      roundSeq: ROUND_SEQUENCE,
    };
    socket.join(code);
    socket.emit('room_joined', { code, view: playerView(rooms[code], socket.id) });
    socket.emit('chat_history', rooms[code].chat || []);
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
    socket.emit('chat_history', room.chat || []);
    io.to(room.code).emit('room_update', publicRoom(room)); // updates all players including host
    broadcastRoomsList();
  });

  socket.on('set_difficulty', ({ code, difficulty }) => {
    const room = getRoom(code);
    if (!room || room.phase !== 'lobby') return;
    if (room.host !== socket.id) return;
    if (!BOT_DIFFICULTY[difficulty]) return;
    room.botDifficulty = difficulty;
    io.to(room.code).emit('room_update', publicRoom(room));
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
    touch(room);
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
    touch(room);
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
    touch(room);
    const playerIdx = room.players.findIndex(p => p.id === socket.id);
    if (playerIdx !== room.state.currentTurnIdx) { socket.emit('error', 'Not your turn.'); return; }
    if (!isLegalPlay(room.state.hands[playerIdx], card, room.state.currentTrick)) {
      socket.emit('error', 'You must follow suit.'); return;
    }
    const result = recordPlay(room, playerIdx, card);
    broadcastViews(room, result);
    if (result === 'round_over') {
      // brief delay so clients can show the round result before the game-over screen
      if (room.state.roundIdx >= (room.roundSeq||ROUND_SEQUENCE).length) setTimeout(() => maybeEndGame(room), 2500);
    } else {
      scheduleBotsIfNeeded(room);
    }
  });

  socket.on('next_round', ({ code }) => {
    const room = getRoom(code);
    if (!room || room.host !== socket.id) return;
    const continues = startNextRound(room);
    if (continues) { broadcastViews(room); scheduleBotsIfNeeded(room); }
    else io.to(room.code).emit('game_over', { players: room.players });
  });

  // Client-requested recovery: re-send state and restart the bot chain if it broke.
  socket.on('resync', ({ code }) => {
    const room = getRoom(code);
    if (!room) { socket.emit('error', 'Room no longer exists.'); return; }
    touch(room);
    room.freezeRecoveries = 0;
    broadcastViews(room);
    try { scheduleBotsIfNeeded(room); } catch (e) { console.error('Resync re-kick failed:', e); }
  });

  socket.on('get_rooms', () => {
    socket.emit('rooms_list', openRoomsList());
  });

  socket.on('chat_message', ({ code, text }) => {
    const room = getRoom(code);
    if (!room) return;
    const player = room.players.find(p => p.id === socket.id);
    if (!player || player.isBot) return;
    const trimmed = text.trim().slice(0, 200); // cap message length
    if (!trimmed) return;
    touch(room);
    const msg = { name: player.name, text: trimmed, ts: Date.now() };
    room.chat = room.chat || [];
    room.chat.push(msg);
    if (room.chat.length > 100) room.chat.shift(); // keep last 100
    io.to(code).emit('chat_message', msg);
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
      if (!p) continue;
      p.connected = false;
      // if host disconnects from lobby, delete the room so the IP slot is freed
      if (room.phase === 'lobby' && room.host === socket.id) {
        io.to(room.code).emit('error', 'Host left — room closed.');
        delete rooms[code];
        broadcastRoomsList();
      } else {
        io.to(room.code).emit('room_update', publicRoom(room));
        broadcastRoomsList();
      }
    }
  });

  // client asks for current room state (used on reconnect)
  socket.on('request_room_state', ({ code, name }) => {
    const room = getRoom(code);
    if (!room) { socket.emit('error', 'Room no longer exists. Please start a new game.'); return; }
    const p = room.players.find(p => p.name.toLowerCase() === name.toLowerCase() && !p.isBot);
    if (!p) { socket.emit('error', 'Could not find you in that room.'); return; }
    // update socket id in case it changed on reconnect
    const wasHost = room.host === p.id;
    p.id = socket.id;
    p.connected = true;
    if (wasHost) room.host = socket.id;
    socket.join(room.code);
    socket.emit('room_joined', { code: room.code, view: playerView(room, socket.id) });
    socket.emit('chat_history', room.chat || []);
    io.to(room.code).emit('room_update', publicRoom(room));
    if (room.phase !== 'lobby') {
      const view = playerView(room, socket.id);
      socket.emit('game_update', view);
    }
  });
});

function broadcastViews(room, result) {
  if (room.state) room.state.lastProgress = Date.now(); // for the freeze watchdog
  room.freezeRecoveries = 0;                            // healthy progress resets recovery count
  for (const p of room.players) {
    if (p.isBot) continue;
    const view = playerView(room, p.id);
    if (result) view.lastResult = result;
    io.to(p.id).emit('game_update', view);
  }
}

// ── IDLE ROOM CLEANUP ────────────────────────────────────
// bump lastActivity on any game action
function touch(room) { if (room) room.lastActivity = Date.now(); }

setInterval(() => {
  const now = Date.now();
  for (const code of Object.keys(rooms)) {
    const room = rooms[code];
    if (now - (room.lastActivity || 0) > ROOM_IDLE_MS) {
      console.log(`Removing idle room ${code}`);
      io.to(code).emit('error', 'Room closed due to inactivity.');
      delete rooms[code];
    }
  }
  broadcastRoomsList();
}, 5 * 60 * 1000); // check every 5 minutes

// ── FREEZE WATCHDOG ──────────────────────────────────────
// If it's a computer player's turn and nothing has progressed for a while,
// the bot chain probably broke. Re-kick it; if it stays stuck, alert clients.
const FREEZE_MS = 8000;

function botTurnPending(room) {
  const s = room.state;
  if (!s) return false;
  if (room.phase === 'bid') {
    const p = room.players[s.currentTurnIdx];
    return !!(p && p.isBot);
  }
  if (room.phase === 'play') {
    if (s.trickCount >= s.totalTricks) return false; // round over, waiting on host — not a freeze
    const p = room.players[s.currentTurnIdx];
    return !!(p && p.isBot);
  }
  return false;
}

setInterval(() => {
  const now = Date.now();
  for (const code of Object.keys(rooms)) {
    const room = rooms[code];
    if (!botTurnPending(room)) continue;
    const since = now - (room.state.lastProgress || 0);
    if (since <= FREEZE_MS) continue;

    room.freezeRecoveries = (room.freezeRecoveries || 0) + 1;
    room.state.lastProgress = now; // avoid re-firing every tick
    console.warn(`Watchdog: room ${code} stuck ${since}ms on bot turn (recovery #${room.freezeRecoveries})`);

    if (room.freezeRecoveries <= 3) {
      try { scheduleBotsIfNeeded(room); }
      catch (e) { console.error('Watchdog re-kick failed:', e); }
    } else {
      io.to(code).emit('game_error', {
        code: `FROZEN-${code}-R${room.state.roundIdx}-P${room.state.currentTurnIdx}`,
        msg: 'The game is stuck on a computer player. Tap Resync to recover.',
      });
    }
  }
}, 3000); // check every 3 seconds

const PORT = process.env.PORT || 3000;
httpServer.listen(PORT, () => console.log(`Five to Ten server on port ${PORT}`));
