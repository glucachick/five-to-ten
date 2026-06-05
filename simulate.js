// ── SIMULATION: Easy vs Medium vs Hard vs Master, 100 games (profile-aware sims) ──
const SUITS = ['♠','♥','♦','♣'];
const RANKS = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const RANK_VAL = {2:2,3:3,4:4,5:5,6:6,7:7,8:8,9:9,10:10,J:11,Q:12,K:13,A:14};
const ROUND_SEQUENCE = [5,6,7,8,9,10,10,9,8,7,6,5];

const BOT_DIFFICULTY = {
  easy:   { sims: 0,   bidVariance: 1.5, playSmart: false, master: false, playNoise: 0.70 },
  medium: { sims: 75,  bidVariance: 0.7, playSmart: true,  master: false, playNoise: 0.20 },
  hard:   { sims: 200, bidVariance: 0.35,playSmart: true,  master: false, playNoise: 0.12 },
  master: { sims: 600, bidVariance: 0.05,playSmart: true,  master: true,  playNoise: 0.0  },
};

const PLAYERS = [
  { name: 'Easy',   difficulty: 'easy'   },
  { name: 'Medium', difficulty: 'medium' },
  { name: 'Hard',   difficulty: 'hard'   },
  { name: 'Master', difficulty: 'master' },
];
const N = PLAYERS.length;
const NUM_GAMES = 500;

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length-1; i > 0; i--) { const j = Math.floor(Math.random()*(i+1)); [a[i],a[j]]=[a[j],a[i]]; }
  return a;
}
function makeDeck() {
  const d = [];
  for (const s of SUITS) for (const r of RANKS) d.push({suit:s,rank:r});
  return shuffle(d);
}
function rv(r) { return RANK_VAL[r]||parseInt(r); }
function beats(card,best,trump) {
  if (card.suit===trump&&best.suit!==trump) return true;
  if (card.suit!==trump&&best.suit===trump) return false;
  if (card.suit!==best.suit) return false;
  return rv(card.rank)>rv(best.rank);
}
function trickWinner(trick,trump) {
  let best=trick[0];
  for (let i=1;i<trick.length;i++) if (beats(trick[i].card,best.card,trump)) best=trick[i];
  return best.playerIdx;
}
function getLegal(hand,trick) {
  if (!trick.length) return [...hand];
  const led=trick[0].card.suit;
  const has=hand.filter(c=>c.suit===led);
  return has.length?has:[...hand];
}
function playedSet(played) { return new Set(played.map(c=>c.rank+c.suit)); }
function isHighestRemaining(card,ps) {
  for (const r of RANKS) if (rv(r)>rv(card.rank)&&!ps.has(r+card.suit)) return false;
  return true;
}
function trumpsLeft(trump,ps) { return RANKS.filter(r=>!ps.has(r+trump)).length; }
function isSureWinner(card,trump,ps) {
  if (!isHighestRemaining(card,ps)) return false;
  if (card.suit===trump) return true;
  return trumpsLeft(trump,ps)===0;
}
function minToWin(legal,trick,trump,pIdx) {
  const canWin=legal.filter(c=>trickWinner([...trick,{playerIdx:pIdx,card:c}],trump)===pIdx);
  if (!canWin.length) return null;
  const nt=canWin.filter(c=>c.suit!==trump);
  return (nt.length?nt:canWin).sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
}
function bestLeadToWin(hand,trump,ps) {
  const sure=hand.filter(c=>isSureWinner(c,trump,ps)).sort((a,b)=>rv(b.rank)-rv(a.rank));
  if (sure.length) return sure[0];
  const t=hand.filter(c=>c.suit===trump).sort((a,b)=>rv(b.rank)-rv(a.rank));
  if (t.length) return t[0];
  return hand.slice().sort((a,b)=>rv(b.rank)-rv(a.rank))[0];
}

function quickSimBid(hand,trump) {
  let est=0;
  for (const c of hand) {
    const r=rv(c.rank);
    if (c.suit===trump) { if(r>=13)est+=0.9; else if(r>=11)est+=0.6; else est+=0.25; }
    else { if(r===14)est+=0.65; else if(r===13)est+=0.35; }
  }
  return Math.round(est);
}
function simPlaySmart(hand,trick,trump,bid) {
  const legal=getLegal(hand,trick);
  if (bid===0) {
    if (!trick.length){const nt=legal.filter(c=>c.suit!==trump).sort((a,b)=>rv(a.rank)-rv(b.rank));return nt.length?nt[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];}
    const losing=legal.filter(c=>trickWinner([...trick,{playerIdx:99,card:c}],trump)!==99);
    return losing.length?losing.sort((a,b)=>rv(b.rank)-rv(a.rank))[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
  }
  if (!trick.length){const t=legal.filter(c=>c.suit===trump).sort((a,b)=>rv(b.rank)-rv(a.rank));return t.length?t[0]:legal.sort((a,b)=>rv(b.rank)-rv(a.rank))[0];}
  let best=trick[0].card;
  for (const e of trick) if (beats(e.card,best,trump)) best=e.card;
  const cb=legal.filter(c=>beats(c,best,trump));
  return cb.length?cb.sort((a,b)=>rv(a.rank)-rv(b.rank))[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
}
function simPlayByProfile(hand,trick,trump,bid,profile) {
  const legal=getLegal(hand,trick);
  if (profile==='random') return legal[Math.floor(Math.random()*legal.length)];
  if (profile==='noisy-heavy') { if(Math.random()<0.40)return legal[Math.floor(Math.random()*legal.length)]; return simPlaySmart(hand,trick,trump,bid); }
  if (profile==='noisy-light') { if(Math.random()<0.10)return legal[Math.floor(Math.random()*legal.length)]; return simPlaySmart(hand,trick,trump,bid); }
  return simPlaySmart(hand,trick,trump,bid);
}
function playerToProfile(player) {
  if (!player.isBot) return 'smart';
  switch(player.difficulty) {
    case 'easy':   return 'random';
    case 'medium': return 'noisy-heavy';
    case 'hard':   return 'noisy-light';
    default:       return 'smart';
  }
}
function runOneSim(allHands,trump,n,handSize,opponentProfiles) {
  const hands=allHands.map(h=>h.map(c=>({...c})));
  const profiles=['smart',...opponentProfiles];
  const simBids=allHands.map(h=>quickSimBid(h,trump));
  const simWon=new Array(n).fill(0);
  let my=0,leader=0;
  for (let t=0;t<handSize;t++) {
    const trick=[];
    for (let pos=0;pos<n;pos++) {
      const pIdx=(leader+pos)%n;
      const card=simPlayByProfile(hands[pIdx],trick,trump,simBids[pIdx],profiles[pIdx]);
      hands[pIdx].splice(hands[pIdx].findIndex(c=>c.rank===card.rank&&c.suit===card.suit),1);
      trick.push({playerIdx:pIdx,card});
    }
    const w=trickWinner(trick,trump); simWon[w]++; if(w===0)my++; leader=w;
  }
  return my;
}
function botBid(hand,trump,totalTricks,numPlayers,trumpCard,numSims,bidVariance,opponentProfiles) {
  if (numSims===0) {
    let e=hand.filter(c=>c.suit===trump).length*0.5;
    if(e<0.8&&Math.random()<0.55)return 0;
    return Math.max(0,Math.min(Math.round(e+(Math.random()*2-1)*bidVariance),totalTricks));
  }
  const mySet=new Set(hand.map(c=>c.rank+c.suit));
  const tKey=trumpCard?trumpCard.rank+trumpCard.suit:null;
  const unseen=[];
  for (const suit of SUITS) for (const rank of RANKS) { const k=rank+suit; if(!mySet.has(k)&&k!==tKey)unseen.push({suit,rank}); }
  const hs=hand.length,no=numPlayers-1; let total=0;
  const profiles=opponentProfiles||new Array(no).fill('smart');
  for (let sim=0;sim<numSims;sim++) {
    const pool=shuffle(unseen);
    const ah=[hand]; for(let i=0;i<no;i++)ah.push(pool.slice(i*hs,(i+1)*hs));
    total+=runOneSim(ah,trump,numPlayers,hs,profiles);
  }
  const exp=total/numSims;
  if (exp < 0.9) {
    const zeroProb = Math.max(0, (0.9 - exp) / 0.9);
    if (Math.random() < zeroProb) return 0;
  }
  return Math.max(0,Math.min(Math.round(exp+(Math.random()*2-1)*bidVariance),totalTricks));
}

function chooseCard(hand,trick,trump,bid,won,played,voids,playerIdx,isMaster) {
  const legal=getLegal(hand,trick);
  const ps=playedSet(played);
  const stillNeed=bid-won;

  // Zero bidder
  if (bid===0) {
    if (won>0) { // rogue
      if(!trick.length){const t=legal.filter(c=>c.suit===trump).sort((a,b)=>rv(b.rank)-rv(a.rank));return t.length?t[0]:legal.sort((a,b)=>rv(b.rank)-rv(a.rank))[0];}
      const w=minToWin(legal,trick,trump,playerIdx); return w||legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
    }
    if (!trick.length){const nt=legal.filter(c=>c.suit!==trump).sort((a,b)=>rv(a.rank)-rv(b.rank));return nt.length?nt[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];}
    const losing=legal.filter(c=>trickWinner([...trick,{playerIdx,card:c}],trump)!==playerIdx);
    return losing.length?losing.sort((a,b)=>rv(b.rank)-rv(a.rank))[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
  }

  // Need tricks
  if (stillNeed>0) {
    if (!trick.length) return bestLeadToWin(hand,trump,ps);
    const w=minToWin(legal,trick,trump,playerIdx); if(w)return w;
    const nt=legal.filter(c=>c.suit!==trump).sort((a,b)=>rv(a.rank)-rv(b.rank)); return nt.length?nt[0]:legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
  }

  // Met bid — trap or win extras
  const zeroBidders=Array.from({length:N},(_,i)=>i).filter(i=>i!==playerIdx&&(PLAYERS[i]?true:false)&&false); // simplified — track via bids array passed in
  // For simulation purposes: always try to win extras (correct behavior)
  if (!trick.length) return bestLeadToWin(hand,trump,ps);
  const w=minToWin(legal,trick,trump,playerIdx); if(w)return w;
  return legal.sort((a,b)=>rv(a.rank)-rv(b.rank))[0];
}

function simulateGame() {
  const scores=new Array(N).fill(0);
  const stats=PLAYERS.map(()=>({bids:0,made:0,set:0,zeroBid:0,zeroBidMade:0,tricksWon:0,tricksBid:0}));
  let dealerIdx=Math.floor(Math.random()*N);

  for (const totalCards of ROUND_SEQUENCE) {
    const deck=makeDeck();
    const hands=[];
    for (let i=0;i<N;i++) hands.push(deck.splice(0,totalCards));
    const trumpCard=deck[0], trump=trumpCard.suit;
    const played=[], voids={};

    const bids=new Array(N).fill(0);
    for (let i=0;i<N;i++) {
      const idx=(dealerIdx+1+i)%N;
      const diff=BOT_DIFFICULTY[PLAYERS[idx].difficulty];
      // Build opponent profiles in seat order from this player's perspective
      const oppProfiles=[];
      for (let j=1;j<N;j++) oppProfiles.push(playerToProfile(PLAYERS[(idx+j)%N]));
      bids[idx]=botBid(hands[idx],trump,totalCards,N,trumpCard,diff.sims,diff.bidVariance,oppProfiles);
      stats[idx].bids++; stats[idx].tricksBid+=bids[idx]; if(bids[idx]===0)stats[idx].zeroBid++;
    }

    let bestBid=-1,leaderIdx=(dealerIdx+1)%N;
    for (let i=0;i<N;i++){const idx=((dealerIdx+1)+i)%N;if(bids[idx]>bestBid){bestBid=bids[idx];leaderIdx=idx;}}

    const tricksWon=new Array(N).fill(0);
    let leader=leaderIdx;
    const currentHands=hands.map(h=>[...h]);

    for (let t=0;t<totalCards;t++) {
      const trick=[];
      for (let pos=0;pos<N;pos++) {
        const pIdx=(leader+pos)%N;
        const diff=BOT_DIFFICULTY[PLAYERS[pIdx].difficulty];
        let card;
        if (diff.playNoise > 0 && Math.random() < diff.playNoise) {
          const legal=getLegal(currentHands[pIdx],trick);
          card=legal[Math.floor(Math.random()*legal.length)];
        } else {
          card=chooseCard(currentHands[pIdx],trick,trump,bids[pIdx],tricksWon[pIdx],played,voids,pIdx,diff.master);
        }
        currentHands[pIdx].splice(currentHands[pIdx].findIndex(c=>c.rank===card.rank&&c.suit===card.suit),1);
        // track voids
        if (trick.length>0){const led=trick[0].card.suit;if(card.suit!==led){if(!voids[led])voids[led]=[];if(!voids[led].includes(pIdx))voids[led].push(pIdx);}}
        played.push(card);
        trick.push({playerIdx:pIdx,card});
      }
      const winner=trickWinner(trick,trump); tricksWon[winner]++; leader=winner;
    }

    for (let i=0;i<N;i++) {
      const bid=bids[i],won=tricksWon[i]; let delta=0;
      if(bid===0){delta=won===0?25:-25;if(won===0)stats[i].zeroBidMade++;}
      else if(won>=bid){delta=bid*10+(won-bid);if(won===totalCards)delta+=50;stats[i].made++;}
      else{delta=-(bid*10);stats[i].set++;}
      scores[i]+=delta; stats[i].tricksWon+=won;
    }
    dealerIdx=(dealerIdx+1)%N;
  }
  return {scores,stats};
}

console.log(`\nRunning ${NUM_GAMES} games: Easy vs Medium vs Hard vs Master...\n`);
const start=Date.now();
const totals=PLAYERS.map(()=>({scores:[],wins:0,bids:0,made:0,set:0,zeroBid:0,zeroBidMade:0,tricksWon:0,tricksBid:0}));

for (let g=0;g<NUM_GAMES;g++) {
  const {scores,stats}=simulateGame();
  const winner=scores.indexOf(Math.max(...scores));
  for (let i=0;i<N;i++) {
    totals[i].scores.push(scores[i]);
    if(i===winner)totals[i].wins++;
    totals[i].bids+=stats[i].bids; totals[i].made+=stats[i].made; totals[i].set+=stats[i].set;
    totals[i].zeroBid+=stats[i].zeroBid; totals[i].zeroBidMade+=stats[i].zeroBidMade;
    totals[i].tricksWon+=stats[i].tricksWon; totals[i].tricksBid+=stats[i].tricksBid;
  }
}

const elapsed=((Date.now()-start)/1000).toFixed(1);
console.log(`Completed in ${elapsed}s\n`);
console.log('═'.repeat(72));
console.log(`${'Player'.padEnd(14)} ${'Wins'.padStart(5)} ${'AvgScore'.padStart(9)} ${'BidAcc%'.padStart(8)} ${'SetRate%'.padStart(9)} ${'0Bid Suc%'.padStart(10)} ${'Tricks/Bid'.padStart(11)}`);
console.log('─'.repeat(72));
for (let i=0;i<N;i++) {
  const t=totals[i];
  const avg=(t.scores.reduce((a,b)=>a+b,0)/NUM_GAMES).toFixed(1);
  const nonZeroBids=t.bids-t.zeroBid;
  const bidAcc=nonZeroBids>0?((t.made/nonZeroBids)*100).toFixed(1):'N/A';
  const setRate=nonZeroBids>0?((t.set/nonZeroBids)*100).toFixed(1):'N/A';
  const zbs=t.zeroBid>0?((t.zeroBidMade/t.zeroBid)*100).toFixed(1):'N/A';
  const tpb=t.tricksBid>0?(t.tricksWon/t.tricksBid).toFixed(2):'N/A';
  const label=`${PLAYERS[i].name} (${PLAYERS[i].difficulty})`;
  console.log(`${label.padEnd(14)} ${String(t.wins).padStart(5)} ${avg.padStart(9)} ${bidAcc.padStart(8)} ${setRate.padStart(9)} ${zbs.padStart(10)} ${tpb.padStart(11)}`);
}
console.log('═'.repeat(72));
