"use strict";
/* ============================================================
   더배틀 평가 점수표 튜너
   node tune.js <설정파일.json>
   - 기준 점수표 vs 후보 점수표를 자기대국으로 붙여서 이기면 교체 (언덕 오르기)
   - 판마다 결과를 체크포인트에 저장하므로 끊겨도 이어서 돌릴 수 있음
   ============================================================ */
const fs = require("fs");
const path = require("path");
const os = require("os");
const { fork } = require("child_process");
const BokuEngineFactory = require("./engine.js");

/* ---------------- 보드 / 심판 (엔진과 별개 구현) ---------------- */
const WIDTHS = [5, 6, 7, 8, 9, 10, 9, 8, 7, 6, 5];
const CELLS = [], IDX = new Map();
for (let i = 0; i < 11; i++) {
  const w = WIDTHS[i], z = i - 5, s = -(w - 1);
  for (let j = 0; j < w; j++) { IDX.set((s + 2 * j) + "," + z, CELLS.length); CELLS.push({ q: s + 2 * j, z }); }
}
const N = CELLS.length;
const at = (q, z) => (IDX.has(q + "," + z) ? IDX.get(q + "," + z) : -1);
const DQ = [2, -2, 1, -1, -1, 1], DZ = [0, 0, 1, -1, 1, -1];
const NB = CELLS.map((c) => DQ.map((dq, d) => at(c.q + dq, c.z + DZ[d])));

function isWin(b, i, p) {
  for (const d of [0, 2, 4]) {
    let n = 1;
    for (const dd of [d, d + 1]) { let c = NB[i][dd]; while (c >= 0 && b[c] === p) { n++; c = NB[c][dd]; } }
    if (n >= 5) return true;
  }
  return false;
}
function capsAt(b, i, p) {
  const o = 3 - p, out = [];
  for (let d = 0; d < 6; d++) {
    const a = NB[i][d]; if (a < 0 || b[a] !== o) continue;
    const c = NB[a][d]; if (c < 0 || b[c] !== o) continue;
    const e = NB[c][d]; if (e < 0 || b[e] !== p) continue;
    if (!out.includes(a)) out.push(a);
    if (!out.includes(c)) out.push(c);
  }
  return out;
}

/* ---------------- 한 판 ---------------- */
function playGame(engine, cfgA, cfgB, opening, aFirst) {
  const b = new Array(N).fill(0);
  let side = 1, blocked = -1, moves = 0;
  for (const i of opening) { b[i] = side; side = 3 - side; moves++; }
  while (true) {
    if (!b.includes(0)) return 0;
    const cfg = (side === 1) === aFirst ? cfgA : cfgB;
    const res = engine.think(b.slice(), side, blocked, cfg, {});
    const i = res.i, r = res.r;
    if (i < 0 || b[i] !== 0 || i === blocked) throw new Error("불법 수: " + i);
    b[i] = side; moves++;
    if (isWin(b, i, side)) return side;
    const cs = capsAt(b, i, side);
    if (cs.length) {
      if (!cs.includes(r)) throw new Error("잘못된 제거: " + r);
      b[r] = 0; blocked = r;
    } else blocked = -1;
    side = 3 - side;
    if (moves > 200) return 0;
  }
}
function randomOpening(k, rnd) {
  const central = CELLS.map((c, i) => i).filter((i) => Math.abs(CELLS[i].z) <= 2 && Math.abs(CELLS[i].q) <= 5);
  const out = [];
  while (out.length < k) { const i = central[Math.floor(rnd() * central.length)]; if (!out.includes(i)) out.push(i); }
  return out;
}
function mulberry32(a) { return function () { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

/* ---------------- 일꾼 프로세스 ---------------- */
if (process.env.TUNE_WORKER) {
  const engine = BokuEngineFactory();
  process.on("message", (job) => {
    const rnd = mulberry32(job.seed);
    let a = 0, b = 0, d = 0;
    for (let g = 0; g < job.games; g++) {
      const op = randomOpening(job.openK, rnd);
      const aFirst = g % 2 === 0;
      let w;
      try { w = playGame(engine, job.cfgA, job.cfgB, op, aFirst); }
      catch (e) { process.send({ error: String(e) }); return; }
      if (!w) d++;
      else if ((w === 1) === aFirst) a++;
      else b++;
    }
    process.send({ a, b, d });
  });
  return;
}

/* ---------------- 본체 ---------------- */
const CONF = JSON.parse(fs.readFileSync(process.argv[2] || "tune-config.json", "utf8"));
const CKPT = CONF.checkpoint;
const BASE_LEVEL = CONF.engineCfg;          // 대국에 쓸 탐색 설정 (시간/깊이)
const GAMES = CONF.gamesPerCandidate;
const WORKERS = Math.max(1, Math.min(CONF.workers || os.cpus().length, os.cpus().length));  // 0 이면 코어 수만큼

const DEFAULT_PARAMS = { V: [2, 16, 120, 1000], capThreat: 70, capBlocked: 30, capRevive: 5000, capReviveOpp: 2500, capThreatOpp: 30 };
// 후보 만들기: 파라미터 하나를 배수로 바꿔봄
const KNOBS = [
  ["V0", (p, f) => ({ ...p, V: [round(p.V[0] * f), p.V[1], p.V[2], p.V[3]] })],
  ["V1", (p, f) => ({ ...p, V: [p.V[0], round(p.V[1] * f), p.V[2], p.V[3]] })],
  ["V2", (p, f) => ({ ...p, V: [p.V[0], p.V[1], round(p.V[2] * f), p.V[3]] })],
  ["V3", (p, f) => ({ ...p, V: [p.V[0], p.V[1], p.V[2], round(p.V[3] * f)] })],
  ["capThreat", (p, f) => ({ ...p, capThreat: round(p.capThreat * f) })],
  ["capRevive", (p, f) => ({ ...p, capRevive: round(p.capRevive * f) })],
  ["capReviveOpp", (p, f) => ({ ...p, capReviveOpp: round(p.capReviveOpp * f) })],
  ["capThreatOpp", (p, f) => ({ ...p, capThreatOpp: round(p.capThreatOpp * f) })],
];
const FACTORS = [0.6, 0.8, 1.25, 1.6];
const round = (x) => Math.max(1, Math.round(x));

function loadState() {
  if (fs.existsSync(CKPT)) return JSON.parse(fs.readFileSync(CKPT, "utf8"));
  return { best: DEFAULT_PARAMS, tried: [], queue: [], round: 0, log: [] };
}
function saveState(st) {
  fs.mkdirSync(path.dirname(CKPT), { recursive: true });
  fs.writeFileSync(CKPT + ".tmp", JSON.stringify(st, null, 1));
  fs.renameSync(CKPT + ".tmp", CKPT);   // 저장 도중 끊겨도 파일이 깨지지 않게
}
function buildQueue(best) {
  const q = [];
  for (const [name] of KNOBS) for (const f of FACTORS) q.push({ knob: name, factor: f });
  // 섞어서 한 노브에만 시간을 몰지 않게
  for (let i = q.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [q[i], q[j]] = [q[j], q[i]]; }
  return q;
}
function applyKnob(best, item) {
  const fn = KNOBS.find((k) => k[0] === item.knob)[1];
  return fn(best, item.factor);
}

/* 일꾼들에게 판을 나눠서 돌림 */
function runMatch(cfgA, cfgB, games, seed) {
  return new Promise((resolve, reject) => {
    const per = Math.ceil(games / WORKERS);
    let left = WORKERS, a = 0, b = 0, d = 0, failed = null;
    for (let w = 0; w < WORKERS; w++) {
      const child = fork(__filename, [], { env: { ...process.env, TUNE_WORKER: "1" } });
      child.send({ cfgA, cfgB, games: per, openK: CONF.openingStones, seed: seed + w * 7919 });
      child.on("message", (m) => {
        if (m.error) failed = m.error;
        else { a += m.a; b += m.b; d += m.d; }
        child.kill();
        if (--left === 0) (failed ? reject(new Error(failed)) : resolve({ a, b, d }));
      });
      child.on("error", (e) => { failed = String(e); if (--left === 0) reject(new Error(failed)); });
    }
  });
}

const DEADLINE = Date.now() + (CONF.maxMinutes || 350) * 60000;

(async () => {
  const st = loadState();
  console.log(`일꾼 ${WORKERS}개 · 후보당 ${GAMES}판 · 체크포인트 ${CKPT}`);
  console.log("현재 기준:", JSON.stringify(st.best));
  while (true) {
    if (Date.now() > DEADLINE) { console.log("시간 예산 종료. 다음 실행에서 이어감."); saveState(st); break; }
    if (!st.queue.length) {
      st.round++;
      st.queue = buildQueue(st.best);
      st.log.push(`--- ${st.round}회차 시작 (기준: ${JSON.stringify(st.best)})`);
      saveState(st);
    }
    const item = st.queue.shift();
    const cand = applyKnob(st.best, item);
    const keyOf = (p) => JSON.stringify(p);
    if (st.tried.includes(keyOf(cand)) || keyOf(cand) === keyOf(st.best)) { saveState(st); continue; }

    const cfgA = { ...BASE_LEVEL, id: "base", params: st.best };
    const cfgB = { ...BASE_LEVEL, id: "cand", params: cand };
    const t0 = Date.now();
    const { a, b, d } = await runMatch(cfgA, cfgB, GAMES, Date.now() & 0xffff);
    const total = a + b + d || 1;
    const score = (b + d * 0.5) / total;                 // 후보 승률
    const line = `${item.knob}×${item.factor}: 후보 ${b}승 ${a}패 ${d}무 (승률 ${(score * 100).toFixed(0)}%) ${(Date.now() - t0) / 1000}초`;
    console.log(line);
    st.log.push(line);
    st.tried.push(keyOf(cand));
    if (score >= CONF.acceptWinRate) {
      st.best = cand;
      st.tried = [];
      st.queue = [];
      const msg = `>>> 교체: ${JSON.stringify(cand)}`;
      console.log(msg); st.log.push(msg);
    }
    saveState(st);
  }
})();
