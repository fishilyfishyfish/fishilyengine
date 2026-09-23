
function BokuEngineFactory() {
  "use strict";
  // ---------- 보드 기하 (UI의 CELLS 순서와 동일) ----------
  const WIDTHS = [5, 6, 7, 8, 9, 10, 9, 8, 7, 6, 5], MID = 5;
  const Q = [], Z = [], idx = new Map();
  for (let i = 0; i < WIDTHS.length; i++) {
    const w = WIDTHS[i], z = i - MID, start = -(w - 1);
    for (let j = 0; j < w; j++) { const q = start + 2 * j; idx.set(q + "," + z, Q.length); Q.push(q); Z.push(z); }
  }
  const N = Q.length;
  const DQ = [2, -2, 1, -1, -1, 1], DZ = [0, 0, 1, -1, 1, -1];
  const NBR = new Int16Array(6 * N);
  for (let d = 0; d < 6; d++) for (let i = 0; i < N; i++) {
    const k = (Q[i] + DQ[d]) + "," + (Z[i] + DZ[d]);
    NBR[d * N + i] = idx.has(k) ? idx.get(k) : -1;
  }
  function hexDist(i, j) {
    const a1 = (Q[i] + Z[i]) / 2, b1 = Z[i], a2 = (Q[j] + Z[j]) / 2, b2 = Z[j];
    const da = a1 - a2, db = b1 - b2;
    return Math.max(Math.abs(da), Math.abs(db), Math.abs(da - db));
  }

  // 5칸 창(window)
  const wins = [];
  for (const d of [0, 2, 4]) for (let i = 0; i < N; i++) {
    const cs = [i]; let c = i, ok = true;
    for (let k = 1; k < 5; k++) { c = NBR[d * N + c]; if (c < 0) { ok = false; break; } cs.push(c); }
    if (ok) wins.push(cs);
  }
  const W = wins.length;
  const WC = new Int16Array(W * 5);
  wins.forEach((cs, w) => cs.forEach((c, k) => { WC[w * 5 + k] = c; }));
  const cwTmp = Array.from({ length: N }, () => []);
  wins.forEach((cs, w) => cs.forEach((c) => cwTmp[c].push(w)));
  const CWS = new Int16Array(N + 1), CWL = [];
  for (let i = 0; i < N; i++) { CWS[i] = CWL.length; CWL.push(...cwTmp[i]); }
  CWS[N] = CWL.length;
  const CW = Int16Array.from(CWL);
  // 창 중심성(오프닝용)
  const centrality = cwTmp.map((l) => l.length);

  // 4칸 구간(따먹기 위협 평가용)
  const segs = [];
  for (const d of [0, 2, 4]) for (let i = 0; i < N; i++) {
    const cs = [i]; let c = i, ok = true;
    for (let k = 1; k < 4; k++) { c = NBR[d * N + c]; if (c < 0) { ok = false; break; } cs.push(c); }
    if (ok) segs.push(cs);
  }
  const SG = Int16Array.from(segs.flat()), NS = segs.length;

  // 거리 2 이내 이웃
  const NEAR = [];
  for (let i = 0; i < N; i++) { const l = []; for (let j = 0; j < N; j++) if (j !== i && hexDist(i, j) <= 2) l.push(j); NEAR.push(Int16Array.from(l)); }

  // ---------- 상태 ----------
  const board = new Int8Array(N);
  const cnt = [null, new Int8Array(W), new Int8Array(W)];
  const sc = [0, 0, 0], four = [0, 0, 0];
  let V = [0, 2, 16, 120, 1000, 1000];
  let CAP_THREAT = 70, CAP_BLOCKED = 30, CAP_REVIVE = 5000, CAP_REVIVE_OPP = 2500, CAP_THREAT_OPP = 30;
  const HV = [2, 14, 104, 880, 100000];
  let blocked = -1, stones = 0;

  let seed = 0x9e3779b9 | 0;
  function rnd32() { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return seed | 0; }
  const Z1 = new Int32Array(3 * N), Z2 = new Int32Array(3 * N);
  const B1 = new Int32Array(N), B2 = new Int32Array(N);
  for (let i = 0; i < 3 * N; i++) { Z1[i] = rnd32(); Z2[i] = rnd32(); }
  for (let i = 0; i < N; i++) { B1[i] = rnd32(); B2[i] = rnd32(); }
  const S1 = rnd32(), S2 = rnd32();
  let h1 = 0, h2 = 0;

  function place(i, p) {
    const o = 3 - p, cp = cnt[p], co = cnt[o];
    board[i] = p; stones++;
    h1 ^= Z1[p * N + i]; h2 ^= Z2[p * N + i];
    for (let k = CWS[i], e = CWS[i + 1]; k < e; k++) {
      const w = CW[k], a = cp[w], b = co[w];
      if (b === 0) { sc[p] += V[a + 1] - V[a]; if (a === 3) four[p]++; else if (a === 4) four[p]--; }
      if (a === 0) { sc[o] -= V[b]; if (b === 4) four[o]--; }
      cp[w] = a + 1;
    }
  }
  function unplace(i) {
    const p = board[i], o = 3 - p, cp = cnt[p], co = cnt[o];
    for (let k = CWS[i], e = CWS[i + 1]; k < e; k++) {
      const w = CW[k], a = cp[w], b = co[w];
      cp[w] = a - 1;
      if (b === 0) { sc[p] += V[a - 1] - V[a]; if (a === 4) four[p]--; else if (a === 5) four[p]++; }
      if (a === 1) { sc[o] += V[b]; if (b === 4) four[o]++; }
    }
    board[i] = 0; stones--;
    h1 ^= Z1[p * N + i]; h2 ^= Z2[p * N + i];
  }
  function setBlocked(b) {
    if (blocked >= 0) { h1 ^= B1[blocked]; h2 ^= B2[blocked]; }
    blocked = b;
    if (blocked >= 0) { h1 ^= B1[blocked]; h2 ^= B2[blocked]; }
  }

  // m = i | ((r+1) << 7)
  const blockedStack = new Int16Array(512);
  let bsp = 0;
  function make(m, p) {
    const i = m & 127, r = (m >> 7) - 1;
    place(i, p);
    if (r >= 0) unplace(r);
    blockedStack[bsp++] = blocked;
    setBlocked(r);
    h1 ^= S1; h2 ^= S2;
  }
  function unmake(m, p) {
    const i = m & 127, r = (m >> 7) - 1;
    h1 ^= S1; h2 ^= S2;
    setBlocked(blockedStack[--bsp]);
    if (r >= 0) place(r, 3 - p);
    unplace(i);
  }

  function capList(i, p, out) {
    const o = 3 - p; let n = 0;
    for (let d = 0; d < 6; d++) {
      const a = NBR[d * N + i]; if (a < 0 || board[a] !== o) continue;
      const b = NBR[d * N + a]; if (b < 0 || board[b] !== o) continue;
      const c = NBR[d * N + b]; if (c < 0 || board[c] !== p) continue;
      let ha = false, hb = false;
      for (let k = 0; k < n; k++) { if (out[k] === a) ha = true; if (out[k] === b) hb = true; }
      if (!ha) out[n++] = a;
      if (!hb) out[n++] = b;
    }
    return n;
  }

  function winCells(p, out) {
    const o = 3 - p, cp = cnt[p], co = cnt[o]; let n = 0;
    if (four[p] <= 0) return 0;
    for (let w = 0; w < W; w++) {
      if (cp[w] !== 4 || co[w] !== 0) continue;
      for (let k = 0; k < 5; k++) {
        const c = WC[w * 5 + k];
        if (board[c] === 0) {
          let dup = false; for (let t = 0; t < n; t++) if (out[t] === c) { dup = true; break; }
          if (!dup) out[n++] = c;
          break;
        }
      }
    }
    return n;
  }
  const tmpWin = new Int16Array(128);
  function hasImmediateWin(p) {
    if (four[p] <= 0) return -1;
    const n = winCells(p, tmpWin);
    for (let k = 0; k < n; k++) if (tmpWin[k] !== blocked) return tmpWin[k];
    return -1;
  }

  let atkBias = 1.2;
  function evalStatic(p) {
    const o = 3 - p;
    let e = sc[p] * atkBias - sc[o];
    for (let s = 0; s < NS; s++) {
      const a = board[SG[s * 4]], b = board[SG[s * 4 + 1]], c = board[SG[s * 4 + 2]], d = board[SG[s * 4 + 3]];
      if (b === 0 || b !== c) continue;
      const Y = 3 - b;
      let empty = -1;
      if (a === Y && d === 0) empty = SG[s * 4 + 3];
      else if (d === Y && a === 0) empty = SG[s * 4];
      else continue;
      let rev = 0;
      const X = b, cy = cnt[Y], cx = cnt[X];
      for (let t = 1; t <= 2; t++) {
        const st = SG[s * 4 + t];
        for (let k = CWS[st], ke = CWS[st + 1]; k < ke; k++) { const w = CW[k]; if (cy[w] === 4 && cx[w] === 1) rev = 1; }
      }
      if (Y === p) e += (empty === blocked ? CAP_BLOCKED : rev ? CAP_REVIVE : CAP_THREAT);
      else e -= rev ? CAP_REVIVE_OPP : CAP_THREAT_OPP;
    }
    return Math.round(e + noiseOf());
  }
  let noiseAmp = 0;
  function noiseOf() {
    if (!noiseAmp) return 0;
    let x = (h1 ^ (h2 >>> 7)) | 0; x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
    return ((x & 1023) / 1023 - 0.5) * noiseAmp;
  }

  function heur(i, p) {
    const o = 3 - p, cp = cnt[p], co = cnt[o];
    let att = 0, def = 0;
    for (let k = CWS[i], e = CWS[i + 1]; k < e; k++) {
      const w = CW[k], a = cp[w], b = co[w];
      if (b === 0) att += HV[a];
      if (a === 0) def += HV[b];
    }
    return att + def * 0.9;
  }
  function removeValue(r, p) {
    const o = 3 - p, cp = cnt[p], co = cnt[o];
    let v = 0;
    for (let k = CWS[r], e = CWS[r + 1]; k < e; k++) {
      const w = CW[k];
      if (cp[w] === 0) v += V[co[w]] - V[co[w] - 1];
    }
    return v;
  }

  function reviveValue(r, p) {
    const o = 3 - p, cp = cnt[p], co = cnt[o];
    let v = 0;
    for (let k = CWS[r], e = CWS[r + 1]; k < e; k++) {
      const w = CW[k];
      if (co[w] === 1) { const a = cp[w]; v += a === 4 ? 60000 : a === 3 ? 800 : V[a]; }
    }
    return v;
  }
  const capBuf2 = new Int16Array(16);
  function oppCaptureValue(i, p) {
    const o = 3 - p, nc = capList(i, o, capBuf2);
    if (nc === 0) return 0;
    let best = 0;
    for (let k = 0; k < nc; k++) { const v = removeValue(capBuf2[k], o) + reviveValue(capBuf2[k], o); if (v > best) best = v; }
    return 300 + best;
  }

  const hist = new Int32Array(128 * 82);
  const capBuf = new Int16Array(16);
  const mark = new Int32Array(N); let stamp = 1;

  function pushPlacement(i, p, ms, ss, n, bonus) {
    const h = heur(i, p) + bonus + 0.9 * oppCaptureValue(i, p);
    const nc = capList(i, p, capBuf);
    if (nc === 0) { ms[n] = i; ss[n] = h + Math.min(hist[i], 600); return n + 1; }
    for (let k = 0; k < nc; k++) {
      const r = capBuf[k], m = i | ((r + 1) << 7);
      ms[n] = m; ss[n] = h + 400 + removeValue(r, p) + reviveValue(r, p) + Math.min(hist[m], 600); n++;
    }
    return n;
  }
  function sortMoves(ms, ss, n, first) {
    if (first) for (let k = 0; k < n; k++) if (ms[k] === first) { ss[k] = 1e12; break; }
    for (let a = 1; a < n; a++) {
      const m = ms[a], s = ss[a]; let b = a - 1;
      while (b >= 0 && ss[b] < s) { ms[b + 1] = ms[b]; ss[b + 1] = ss[b]; b--; }
      ms[b + 1] = m; ss[b + 1] = s;
    }
  }
  function genNormal(p, ms, ss) {
    let n = 0; stamp++;
    if (stones === 0) {
      for (let i = 0; i < N; i++) if (i !== blocked) { ms[n] = i; ss[n] = centrality[i]; n++; }
      return n;
    }
    for (let s = 0; s < N; s++) {
      if (board[s] === 0) continue;
      const nl = NEAR[s];
      for (let k = 0; k < nl.length; k++) {
        const c = nl[k];
        if (board[c] !== 0 || c === blocked || mark[c] === stamp) continue;
        mark[c] = stamp;
        n = pushPlacement(c, p, ms, ss, n, 0);
      }
    }
    return n;
  }
  function genForced(p, oppL, nL, ms, ss) {
    let n = 0; stamp++;
    for (let k = 0; k < nL; k++) {
      const c = oppL[k];
      if (c === blocked || board[c] !== 0 || mark[c] === stamp) continue;
      mark[c] = stamp;
      n = pushPlacement(c, p, ms, ss, n, 50000);
    }
    for (let i = 0; i < N; i++) {
      if (board[i] !== 0 || i === blocked || mark[i] === stamp) continue;
      if (capList(i, p, capBuf) > 0) { mark[i] = stamp; n = pushPlacement(i, p, ms, ss, n, 0); }
    }
    return n;
  }
  function genFourMakers(p, ms, ss) {
    const o = 3 - p, cp = cnt[p], co = cnt[o];
    let n = 0; stamp++;
    for (let w = 0; w < W; w++) {
      if (cp[w] !== 3 || co[w] !== 0) continue;
      for (let k = 0; k < 5; k++) {
        const c = WC[w * 5 + k];
        if (board[c] !== 0 || c === blocked || mark[c] === stamp) continue;
        mark[c] = stamp;
        n = pushPlacement(c, p, ms, ss, n, 0);
      }
    }
    // 따먹어서 내 4를 되살리는 수 (제거된 칸은 상대가 바로 못 막음)
    for (let w = 0; w < W; w++) {
      if (cp[w] !== 4 || co[w] !== 1) continue;
      let r = -1;
      for (let k = 0; k < 5; k++) { const c = WC[w * 5 + k]; if (board[c] === o) { r = c; break; } }
      for (let d = 0; d < 6; d++) {
        const a = NBR[d * N + r]; if (a < 0 || board[a] !== o) continue;
        const e1 = NBR[(d ^ 1) * N + r], e2 = NBR[d * N + a];
        if (e1 < 0 || e2 < 0) continue;
        let tgt = -1;
        if (board[e1] === p && board[e2] === 0) tgt = e2;
        else if (board[e2] === p && board[e1] === 0) tgt = e1;
        if (tgt < 0 || tgt === blocked || mark[tgt] === stamp) continue;
        mark[tgt] = stamp;
        n = pushPlacement(tgt, p, ms, ss, n, 0);
      }
    }
    return n;
  }

  // ---------- TT ----------
  const TT_BITS = 19, TT_SIZE = 1 << TT_BITS, TT_MASK = TT_SIZE - 1;
  const tKey = new Int32Array(TT_SIZE), tDepth = new Int8Array(TT_SIZE), tFlag = new Int8Array(TT_SIZE);
  const tScore = new Int32Array(TT_SIZE), tMove = new Int16Array(TT_SIZE);
  const EXACT = 1, LOWER = 2, UPPER = 3;
  function ttClear() { tFlag.fill(0); hist.fill(0); }

  const WIN = 1000000, INF = 2000000000, MAXPLY = 60;
  const isMate = (s) => s > WIN - 1000 || s < -WIN + 1000;
  function toTT(s, ply) { return s > WIN - 1000 ? s + ply : s < -WIN + 1000 ? s - ply : s; }
  function fromTT(s, ply) { return s > WIN - 1000 ? s - ply : s < -WIN + 1000 ? s + ply : s; }

  let nodes = 0, deadline = 0, cfg = null, stopFlag = false;
  const TIMEOUT = { t: 1 };
  const MS = [], SS = [], OL = [];
  for (let i = 0; i < MAXPLY + 20; i++) { MS.push(new Int32Array(1024)); SS.push(new Float64Array(1024)); OL.push(new Int16Array(128)); }

  function tick() {
    if ((++nodes & 1023) === 0 && Date.now() > deadline) throw TIMEOUT;
  }

  function qsearch(alpha, beta, ply, p, qd) {
    tick();
    if (hasImmediateWin(p) >= 0) return WIN - ply;
    const o = 3 - p;
    const ms = MS[ply], ss = SS[ply], ol = OL[ply];
    const nL = four[o] > 0 ? winCells(o, ol) : 0;
    if (nL > 0) {
      const n = genForced(p, ol, nL, ms, ss);
      if (n === 0) return -(WIN - ply - 1);
      if (qd >= cfg.qmax || ply >= MAXPLY) return evalStatic(p) - 400;
      sortMoves(ms, ss, n, 0);
      let best = -INF;
      for (let k = 0; k < n; k++) {
        const m = ms[k];
        make(m, p);
        const s = -qsearch(-beta, -alpha, ply + 1, o, qd + 1);
        unmake(m, p);
        if (s > best) { best = s; if (s > alpha) { alpha = s; if (alpha >= beta) break; } }
      }
      return best;
    }
    const stand = evalStatic(p);
    if (stand >= beta) return stand;
    if (qd >= cfg.qmax || ply >= MAXPLY) return stand;
    if (stand > alpha) alpha = stand;
    let n = genFourMakers(p, ms, ss);
    if (n === 0) return stand;
    sortMoves(ms, ss, n, 0);
    if (n > cfg.qwidth) n = cfg.qwidth;
    let best = stand;
    for (let k = 0; k < n; k++) {
      const m = ms[k];
      make(m, p);
      const s = -qsearch(-beta, -alpha, ply + 1, o, qd + 1);
      unmake(m, p);
      if (s > best) { best = s; if (s > alpha) { alpha = s; if (alpha >= beta) break; } }
    }
    return best;
  }

  function search(depth, alpha, beta, ply, p) {
    tick();
    if (hasImmediateWin(p) >= 0) return WIN - ply;
    if (stones >= N) return 0;
    if (depth <= 0 || ply >= MAXPLY) return qsearch(alpha, beta, ply, p, 0);
    const o = 3 - p;

    const slot = h1 & TT_MASK;
    let ttMove = 0;
    if (tFlag[slot] && tKey[slot] === h2) {
      ttMove = tMove[slot];
      if (tDepth[slot] >= depth) {
        const s = fromTT(tScore[slot], ply), f = tFlag[slot];
        if (f === EXACT) return s;
        if (f === LOWER && s >= beta) return s;
        if (f === UPPER && s <= alpha) return s;
      }
    }

    const ms = MS[ply], ss = SS[ply], ol = OL[ply];
    const nL = four[o] > 0 ? winCells(o, ol) : 0;
    const forced = nL > 0;
    let n = forced ? genForced(p, ol, nL, ms, ss) : genNormal(p, ms, ss);
    if (n === 0) return forced ? -(WIN - ply - 1) : 0;
    sortMoves(ms, ss, n, ttMove);
    if (!forced && n > cfg.beam) n = cfg.beam;
    const newDepth = forced ? depth : depth - 1;

    const a0 = alpha;
    let best = -INF, bestMove = 0;
    for (let k = 0; k < n; k++) {
      const m = ms[k];
      make(m, p);
      let s;
      if (k === 0) s = -search(newDepth, -beta, -alpha, ply + 1, o);
      else {
        s = -search(newDepth, -alpha - 1, -alpha, ply + 1, o);
        if (s > alpha && s < beta) s = -search(newDepth, -beta, -alpha, ply + 1, o);
      }
      unmake(m, p);
      if (s > best) {
        best = s; bestMove = m;
        if (s > alpha) { alpha = s; if (alpha >= beta) { hist[m] += depth * depth; break; } }
      }
    }
    tKey[slot] = h2; tDepth[slot] = depth; tMove[slot] = bestMove;
    tFlag[slot] = best <= a0 ? UPPER : best >= beta ? LOWER : EXACT;
    tScore[slot] = toTT(best, ply);
    return best;
  }

  // 예상 진행: 전치표에 최선수가 남아 있으면 그걸 쓰고, 없으면 얕게 다시 읽어서 이어붙임
  const pvMS = new Int32Array(1024), pvSS = new Float64Array(1024), pvOL = new Int16Array(128);
  function bestReply(p, d) {
    const o = 3 - p;
    const slot = h1 & TT_MASK;
    if (tFlag[slot] && tKey[slot] === h2 && tMove[slot]) {
      const m = tMove[slot], i = m & 127, r = (m >> 7) - 1;
      if (board[i] === 0 && i !== blocked && (r < 0 || board[r] === o)) return m;
    }
    const w = hasImmediateWin(p);
    if (w >= 0) return w;
    const nL = four[o] > 0 ? winCells(o, pvOL) : 0;
    const n = nL > 0 ? genForced(p, pvOL, nL, pvMS, pvSS) : genNormal(p, pvMS, pvSS);
    if (!n) return 0;
    sortMoves(pvMS, pvSS, n, 0);
    let best = 0, bestV = -INF;
    for (let k = 0; k < Math.min(n, 6); k++) {
      const m = pvMS[k];
      make(m, p);
      const v = -search(d - 1, -INF, INF, 1, o);
      unmake(m, p);
      if (v > bestV) { bestV = v; best = m; }
    }
    return best;
  }
  function pvFrom(m0, p0, maxLen) {
    const seq = [], sides = [];
    let side = p0, m = m0;
    for (let k = 0; k < maxLen; k++) {
      const i = m & 127, r = (m >> 7) - 1;
      if (i < 0 || board[i] !== 0 || i === blocked) break;
      if (r >= 0 && board[r] !== 3 - side) break;
      make(m, side); seq.push(m); sides.push(side); side = 3 - side;
      m = bestReply(side, 2);
      if (!m) break;
    }
    for (let k = seq.length - 1; k >= 0; k--) unmake(seq[k], sides[k]);
    return seq.map((mm, k) => ({ i: mm & 127, r: (mm >> 7) - 1, p: sides[k] }));
  }

  function setup(arr, blk) {
    board.fill(0); cnt[1].fill(0); cnt[2].fill(0);
    sc[1] = sc[2] = 0; four[1] = four[2] = 0; stones = 0; h1 = 0; h2 = 0; blocked = -1;
    for (let i = 0; i < N; i++) if (arr[i]) place(i, arr[i]);
    setBlocked(blk);
  }

  // ---------- 위협 분석 ----------
  const tmpA = new Int16Array(128), tmpF = new Int16Array(128);
  // q가 한 수로 "막을 곳 2개 이상인 4"(열린 4·쌍4)를 만들 수 있는 칸 수
  function openFourMakers(q, exclude) {
    const cq = cnt[q], cr = cnt[3 - q];
    let n = 0;
    for (let e = 0; e < N; e++) {
      if (board[e] !== 0 || e === exclude) continue;
      let cand = false;
      for (let k = CWS[e], ke = CWS[e + 1]; k < ke; k++) { const w = CW[k]; if (cq[w] === 3 && cr[w] === 0) { cand = true; break; } }
      if (!cand) continue;
      place(e, q);
      const c = winCells(q, tmpA);
      unplace(e);
      if (c >= 2) n++;
    }
    return n;
  }
  function completesFive(i, p) {
    const cp = cnt[p], co = cnt[3 - p];
    for (let k = CWS[i], ke = CWS[i + 1]; k < ke; k++) { const w = CW[k]; if (cp[w] === 4 && co[w] === 0) return true; }
    return false;
  }
  function winContains(w, i) { for (let k = 0; k < 5; k++) if (WC[w * 5 + k] === i) return true; return false; }

  // 한 수의 "설명용" 특징
  function features(m, p) {
    const o = 3 - p, i = m & 127, r = (m >> 7) - 1, cp = cnt[p], co = cnt[o];
    const f = { i, r, win: false, up: [0, 0, 0, 0, 0, 0], kill: [0, 0, 0, 0, 0, 0], att: 0, def: 0,
      oppFourBefore: 0, block4: false, oppLiveBefore: 0, oppLiveAfter: 0, oppFourAfter: 0,
      myFourAfter: 0, myLiveAfter: 0, capLoss: 0, reviveFour: false };
    for (let k = CWS[i], ke = CWS[i + 1]; k < ke; k++) {
      const w = CW[k], a = cp[w], b = co[w];
      if (b === 0) { f.up[a + 1]++; f.att += V[a + 1] - V[a]; }
      if (a === 0 && b > 0) { f.kill[b]++; f.def += V[b]; }
    }
    f.win = f.up[5] > 0;
    const nOW = winCells(o, tmpF);
    f.oppFourBefore = nOW;
    for (let k = 0; k < nOW; k++) if (tmpF[k] === i) f.block4 = true;
    f.oppLiveBefore = nOW ? 0 : openFourMakers(o, -1);
    if (f.win) return f;
    if (r >= 0) {
      for (let k = CWS[r], ke = CWS[r + 1]; k < ke; k++) {
        const w = CW[k], b = co[w], a = cp[w] + (winContains(w, i) ? 1 : 0);
        if (a === 0) f.capLoss += V[b] - V[b - 1];
        if (b === 1 && a === 4) f.reviveFour = true;
      }
    }
    make(m, p);
    f.myFourAfter = winCells(p, tmpF);
    f.oppFourAfter = winCells(o, tmpF);
    f.oppLiveAfter = f.oppFourAfter ? 0 : openFourMakers(o, blocked);
    f.myLiveAfter = f.myFourAfter ? 0 : openFourMakers(p, -1);
    unmake(m, p);
    return f;
  }

  // ---------- 내장 레벨 (테스트용 문자열 레벨) ----------
  const LEVELS = {
    easy:   { maxDepth: 1, time: 250,  beam: 8,  qmax: 2,  qwidth: 2, noise: 900, pick: 400 },
    normal: { maxDepth: 2, time: 500,  beam: 8,  qmax: 3,  qwidth: 3, noise: 400, pick: 180 },
    hard:   { maxDepth: 40, time: 1500, beam: 14, qmax: 10, qwidth: 6, noise: 0, pick: 0 },
    master: { maxDepth: 40, time: 4000, beam: 16, qmax: 12, qwidth: 8, noise: 0, pick: 0 },
  };
  let lastLevel = null, savedArr = null, savedBlk = -1, savedSide = 1;

  function restoreState() {
    setup(savedArr, savedBlk);
    if (savedSide === 2) { h1 ^= S1; h2 ^= S2; }
    bsp = 0;
  }

  // 루트 수 목록에 대해 반복 심화. R.vd = 마지막으로 끝까지 계산된 값
  let lastSnap = null, prevSnap = null;
  function rootSearch(root, p, t0) {
    const o = 3 - p;
    let doneDepth = 0;
    lastSnap = prevSnap = null;
    for (const R of root) {
      R.v = -INF; R.vd = -INF;
      if (completesFive(R.m & 127, p)) R.five = true;
    }
    const exactRoot = cfg.pick > 0 || !!cfg.exact;
    try {
      for (let d = 1; d <= cfg.maxDepth; d++) {
        let alpha = -INF;
        for (let k = 0; k < root.length; k++) {
          const R = root[k];
          let s;
          if (R.five) s = WIN;
          else {
            make(R.m, p);
            if (k === 0 || exactRoot || alpha === -INF) s = -search(d - 1, -INF, exactRoot ? INF : -alpha, 1, o);
            else {
              s = -search(d - 1, -alpha - 1, -alpha, 1, o);
              if (s > alpha) s = -search(d - 1, -INF, -alpha, 1, o);
            }
            unmake(R.m, p);
          }
          R.v = s;
          if (s > alpha) alpha = s;
        }
        for (const R of root) R.vd = R.v;
        root.sort((a, b) => b.vd - a.vd);
        doneDepth = d;
        // 평가 표시용: 홀수/짧은 깊이는 '한 수 더 둔 쪽'이 유리하게 나와서 값이 출렁임.
        // evenOnly면 짝수 깊이 결과만 보고용으로 저장.
        prevSnap = lastSnap;
        lastSnap = { depth: d, map: new Map(root.map((R) => [R.m, R.vd])) };
        if (isMate(root[0].vd)) break;
        // 고정 깊이 설정(분석·평가 바)은 매번 같은 값이 나오도록 끝까지 돌림.
        // 시간제 설정(대국용)만 남은 시간을 보고 조기 종료.
        if (cfg.maxDepth >= 20 && Date.now() - t0 > cfg.time * 0.45) break;
      }
    } catch (e) {
      if (e !== TIMEOUT) throw e;
      restoreState();
      if (doneDepth > 0) root.sort((a, b) => b.vd - a.vd);
    }
    return doneDepth;
  }

  function think(arr, side, blk, level, opts) {
    opts = opts || {};
    let cfgId;
    if (typeof level === "string") { cfg = Object.assign({}, LEVELS[level] || LEVELS.hard, opts); cfgId = level; }
    else { cfg = Object.assign({}, level); cfgId = level.id || JSON.stringify(level); }
    // 분석·평가 바는 매번 같은 값이 나와야 하므로 캐시를 비우고 처음부터 계산
    if (cfgId !== lastLevel || opts.clear || cfg.freshTT) { ttClear(); lastLevel = cfgId; }
    noiseAmp = cfg.noise || 0;
    atkBias = cfg.atk === undefined ? 1.2 : cfg.atk;
    // 튜닝용: cfg.params 로 평가 점수표를 갈아끼울 수 있음
    if (cfg.params) {
      const P = cfg.params;
      if (P.V) V = [0, P.V[0], P.V[1], P.V[2], P.V[3], P.V[3]];
      if (P.capThreat !== undefined) CAP_THREAT = P.capThreat;
      if (P.capBlocked !== undefined) CAP_BLOCKED = P.capBlocked;
      if (P.capRevive !== undefined) CAP_REVIVE = P.capRevive;
      if (P.capReviveOpp !== undefined) CAP_REVIVE_OPP = P.capReviveOpp;
      if (P.capThreatOpp !== undefined) CAP_THREAT_OPP = P.capThreatOpp;
    } else {
      V = [0, 2, 16, 120, 1000, 1000];
      CAP_THREAT = 70; CAP_BLOCKED = 30; CAP_REVIVE = 5000; CAP_REVIVE_OPP = 2500; CAP_THREAT_OPP = 30;
    }
    hist.fill(0);
    savedArr = arr; savedBlk = blk; savedSide = side;
    restoreState();
    const t0 = Date.now();
    deadline = t0 + (cfg.time || 1000);
    nodes = 0;
    const p = side, o = 3 - p;
    const rolls = [];
    const roll = (name, prob) => {
      if (prob >= 1) return true;
      const r = Math.random(), took = r < prob;
      rolls.push({ name, p: prob, roll: r, took });
      return took;
    };
    const result = (m, rule, extra) => {
      const feat = features(m, p);
      return Object.assign({ i: m & 127, r: (m >> 7) - 1, rule, rolls, feat, nodes, ms: Date.now() - t0 }, extra || {});
    };

    // 수 목록
    const ms = new Int32Array(1024), ss = new Float64Array(1024), ol = new Int16Array(128);
    const listFrom = (n) => { sortMoves(ms, ss, n, 0); const L = []; for (let k = 0; k < n; k++) L.push({ m: ms[k], s: ss[k] }); return L; };

    // ---- 분석 모드 (추천 수) ----
    if (opts.analysis) {
      let n = genNormal(p, ms, ss);
      let root = listFrom(n);
      if (opts.onlyCell >= 0) {
        stamp++; n = pushPlacement(opts.onlyCell, p, ms, ss, 0, 0);
        root = listFrom(n);
      }
      if (!root.length) return { top: [], depth: 0, nodes, ms: 0 };
      let depth = rootSearch(root, p, t0);
      // 값이 같은 수들의 순서를 항상 같게: 중앙에 가까운 쪽 → 칸 번호 순
      const tieSort = (x, y) => (y.v - x.v) || (centrality[y.m & 127] - centrality[x.m & 127]) || ((x.m & 127) - (y.m & 127));
      let list = root.map((R) => ({ m: R.m, v: R.vd })).sort(tieSort);
      // 표시용 안정화: 마지막 두 깊이(홀/짝)의 평균을 씀.
      // 홀수 깊이는 두는 쪽이, 짝수 깊이는 상대가 마지막 수를 둬서 값이 한 칸씩 출렁이기 때문.
      if (cfg.smooth && prevSnap && lastSnap) {
        list = list.map((R) => {
          const a = lastSnap.map.get(R.m), b = prevSnap.map.get(R.m);
          if (a === undefined || b === undefined || isMate(a) || isMate(b)) return R;
          return { m: R.m, v: Math.round((a + b) / 2) };
        }).sort(tieSort);
      }
      const top = list.slice(0, Math.min(3, list.length)).map((R) => ({
        i: R.m & 127, r: (R.m >> 7) - 1, v: R.v, feat: features(R.m, p), pv: pvFrom(R.m, p, 5),
      }));
      return { top, depth, nodes, mover: p, smoothed: !!(cfg.smooth && depth >= 2), ms: Date.now() - t0 };
    }

    if (stones === 0) {
      let bestC = [], bc = -1;
      for (let i = 0; i < N; i++) { if (centrality[i] > bc) { bc = centrality[i]; bestC = [i]; } else if (centrality[i] === bc) bestC.push(i); }
      return result(bestC[Math.floor(Math.random() * bestC.length)], "opening");
    }

    // ---- 규칙 레벨 ----
    if (cfg.rules) {
      let pool = listFrom(genNormal(p, ms, ss));
      if (!pool.length) {
        for (let i = 0; i < N; i++) if (board[i] === 0 && i !== blocked) return result(i, "free");
      }
      const all = pool.slice();
      const without = (set) => pool.filter((R) => !set.has(R.m));
      const choose = (list) => {
        if (cfg.selector === "search" && list.length > 1) {
          const depth = rootSearch(list, p, t0);
          if (cfg.pick > 0 && depth > 0 && !isMate(list[0].vd)) {
            const best = list[0].vd;
            const cand = list.filter((R) => R.vd >= best - cfg.pick && !isMate(R.vd));
            if (cand.length) return { R: cand[Math.floor(Math.random() * cand.length)], depth };
          }
          return { R: list[0], depth };
        }
        if (cfg.selector === "random" || cfg.selector === "greedy") {
          const topN = Math.min(cfg.topN || 3, list.length);
          let tot = 0; for (let k = 0; k < topN; k++) tot += topN - k;
          let x = Math.random() * tot;
          for (let k = 0; k < topN; k++) { x -= topN - k; if (x < 0) return { R: list[k], depth: 0 }; }
        }
        return { R: list[0], depth: 0 };
      };

      // 1) 5목 완성
      const wc = hasImmediateWin(p);
      if (wc >= 0) {
        if (roll("win", cfg.pWin)) {
          const R = pool.find((x) => (x.m & 127) === wc) || { m: wc };
          return result(R.m, "win");
        }
        pool = pool.filter((R) => !completesFive(R.m & 127, p));
      }
      // 2) 상대 4목 막기
      const nL = winCells(o, ol);
      if (nL > 0) {
        const fn = genForced(p, ol, nL, ms, ss);
        const blocks = listFrom(fn);
        const set = new Set(blocks.map((R) => R.m));
        if (blocks.length && roll("block4", cfg.pBlock4)) {
          return result(blocks[0].m, "block4");
        }
        pool = without(set);
      } else {
        // 3) 상대 3목 막기
        if (openFourMakers(o, -1) > 0) {
          const blocks = [];
          for (const R of pool) {
            make(R.m, p);
            const ok = winCells(o, tmpA) === 0 && openFourMakers(o, blocked) === 0;
            unmake(R.m, p);
            if (ok) blocks.push(R);
          }
          if (blocks.length) {
            if (roll("block3", cfg.pBlock3)) {
              const c = choose(blocks.map((R) => ({ m: R.m, s: R.s })));
              return result(c.R.m, "block3", { depth: c.depth, v: c.R.vd });
            }
            pool = without(new Set(blocks.map((R) => R.m)));
          }
        }
      }
      // 4) 샌드위치
      const capsPool = pool.filter((R) => (R.m >> 7) > 0);
      if (capsPool.length) {
        if (roll("sandwich", cfg.pSandwich)) {
          capsPool.sort((a, b) => b.s - a.s);
          if (cfg.selector === "search" && capsPool.length > 1) {
            const c = choose(capsPool.map((R) => ({ m: R.m, s: R.s })));
            return result(c.R.m, "sandwich", { depth: c.depth, v: c.R.vd });
          }
          return result(capsPool[0].m, "sandwich");
        }
        pool = pool.filter((R) => (R.m >> 7) === 0);
      }
      if (!pool.length) pool = all;
      const c = choose(pool.map((R) => ({ m: R.m, s: R.s })));
      return result(c.R.m, "free", { depth: c.depth, v: c.R.vd });
    }

    // ---- 탐색 레벨 ----
    const wcS = hasImmediateWin(p);
    if (wcS >= 0) return result(wcS, "win", { v: WIN, depth: 1 });
    const nL = four[o] > 0 ? winCells(o, ol) : 0;
    const n = nL > 0 ? genForced(p, ol, nL, ms, ss) : genNormal(p, ms, ss);
    if (n === 0) {
      for (let i = 0; i < N; i++) if (board[i] === 0 && i !== blocked) return result(i, "lost", { v: -WIN, depth: 0 });
      return { i: -1, r: -1, rule: "none", rolls, nodes, ms: 0 };
    }
    const root = listFrom(n);
    if (root.length === 1) return result(root[0].m, "only", { depth: 0 });
    const depth = rootSearch(root, p, t0);
    let pickR = root[0];
    if (cfg.pick > 0 && depth > 0 && !isMate(root[0].vd)) {
      const best = root[0].vd;
      const cand = root.filter((R) => R.vd >= best - cfg.pick && !isMate(R.vd));
      if (cand.length) pickR = cand[Math.floor(Math.random() * cand.length)];
    }
    return result(pickR.m, "search", { depth, v: pickR.vd });
  }

  return { think, N, Q, Z, LEVELS, WIN };
}


if (typeof module !== "undefined") module.exports = BokuEngineFactory;
