// Push-optimal Sokoban solver, room by room. Generated levels are a hallway
// with independent rooms off it (a box pushed out of a door never returns),
// so each room is solved push-optimally alone and the optima add up to the
// level's optimum: full points. BFS over pushes; a state is the boxes plus
// the player's reachable region (named by its lowest square). Prunes: dead
// squares (no pull path to any goal) and frozen 2x2 blocks. Pure work caps,
// never the clock, so two runs write identical bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const MAX = 250_000;
const D: [number, number, string, string][] = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
type L = { w: number; h: number; wall: Uint8Array; goals: number[]; boxes: number[]; player: number };
function parse(t: string): L {
  const rows = t.split('\n').filter((r) => r.length > 0);
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [], boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x]!, i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if ('.*+'.includes(ch)) goals.push(i);
      if ('$*'.includes(ch)) boxes.push(i);
      if ('@+'.includes(ch)) player = i;
    }
  });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++)
    if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}
// Squares a box can be pushed from onto some goal (pull back from goals).
function live(lv: L): Uint8Array {
  const { w, wall, goals } = lv;
  const li = new Uint8Array(wall.length), q = [...goals];
  for (const g of goals) li[g] = 1;
  for (let i = 0; i < q.length; i++) {
    const x = q[i]!;
    for (const [dx, dy] of D) {
      const d = dy * w + dx, y = x - d;
      if (!wall[y] && !wall[y - d] && !li[y]) { li[y] = 1; q.push(y); }
    }
  }
  return li;
}
// Player's reachable region from `from` (occ in the way); lowest square.
function reach(lv: L, occ: Uint8Array, from: number, seen: Int32Array, st: number, stack: Int32Array): number {
  const { w, wall } = lv;
  let low = from, n = 0;
  stack[n++] = from; seen[from] = st;
  while (n > 0) {
    const p = stack[--n]!;
    if (p < low) low = p;
    for (const q of [p - w, p + w, p - 1, p + 1])
      if (!wall[q] && !occ[q] && seen[q] !== st) { seen[q] = st; stack[n++] = q; }
  }
  return low;
}
// Box just pushed to `t` frozen in a 2x2 block of walls/boxes, a box off goal.
function frozen(lv: L, occ: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = lv;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || occ[a]) || !(wall[b] || occ[b]) || !(wall[c] || occ[c]) || !(wall[d] || occ[d])) continue;
    if ((occ[a] && !goal[a]) || (occ[b] && !goal[b]) || (occ[c] && !goal[c]) || (occ[d] && !goal[d])) return true;
  }
  return false;
}
// Shortest walk from `from` to `to` around walls and boxes (lower letters).
function walk(lv: L, occ: Uint8Array, from: number, to: number): string {
  const { w, wall } = lv;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const q = [from];
  prev[from] = from;
  for (let i = 0; i < q.length; i++) {
    const p = q[i]!;
    if (p === to) break;
    for (const [dx, dy, letter] of D) {
      const nq = p + dy * w + dx;
      if (wall[nq] || occ[nq] || prev[nq] !== -1) continue;
      prev[nq] = p; how[nq] = letter; q.push(nq);
    }
  }
  if (prev[to] === -1) throw new Error('push square out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s;
  return s;
}
function endOf(w: number, from: number, m: string): number {
  let p = from;
  for (const ch of m.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}
// Push-optimal solution of lv within max states, or null if it gives up.
function opt(lv: L, max = MAX): { pushes: number; moves: string } | null {
  const { w, wall, goals } = lv;
  const size = wall.length, goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const li = live(lv);
  if (lv.boxes.some((b) => !li[b])) return null;
  const occ = new Uint8Array(size), seen = new Int32Array(size), mark = new Int32Array(size), stack = new Int32Array(size);
  let stamp = 0;
  const solved = (bs: number[]): boolean => bs.every((b) => goal[b]);
  const key = (bs: number[], low: number): number => { let k = low; for (const b of bs) k = k * size + b; return k; };
  const sB: number[][] = [lv.boxes], sP: number[] = [lv.player], par: number[] = [-1];
  const idx = new Map<number, number>();
  for (const b of lv.boxes) occ[b] = 1;
  idx.set(key(lv.boxes, reach(lv, occ, lv.player, seen, ++stamp, stack)), 0);
  for (const b of lv.boxes) occ[b] = 0;
  let found = solved(lv.boxes) ? 0 : -1;
  for (let head = 0; found < 0 && head < sB.length; head++) {
    const boxes = sB[head]!;
    for (const b of boxes) occ[b] = 1;
    reach(lv, occ, sP[head]!, seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi]!;
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || occ[t] || !li[t]) continue;
        occ[b] = 0; occ[t] = 1;
        const frz = frozen(lv, occ, goal, t);
        let k = -1;
        let next: number[] | null = null;
        if (!frz) {
          next = boxes.slice(); next[bi] = t; next.sort((a, c) => a - c);
          k = key(next, reach(lv, occ, b, mark, ++stamp, stack));
        }
        occ[t] = 0; occ[b] = 1;
        if (frz || idx.has(k)) continue;
        if (sB.length >= max) { for (const x of boxes) occ[x] = 0; return null; }
        idx.set(k, sB.length);
        sB.push(next!); sP.push(b); par.push(head);
        if (solved(next!)) { found = sB.length - 1; break; }
      }
    }
    for (const x of boxes) occ[x] = 0;
  }
  if (found < 0) return null;
  const path: number[] = [];
  for (let s = found; s > 0; s = par[s]!) path.push(s);
  path.reverse();
  let moves = '', player = lv.player, boxes = lv.boxes;
  for (const s of path) {
    const nb = sB[s]!;
    const from = boxes.find((b) => !nb.includes(b))!, to = nb.find((b) => !boxes.includes(b))!;
    const d = to - from;
    const dir = D.find(([dx, dy]) => dy * w + dx === d)!;
    for (const b of boxes) occ[b] = 1;
    moves += walk(lv, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += dir[3]; player = from; boxes = nb;
  }
  return { pushes: path.length, moves };
}
// The level's rooms: cut the hallway row's dead squares out of the floor;
// each part left holding boxes is a room. Null when no such split exists.
function rooms(lv: L): { boxes: number[]; goals: number[]; done?: boolean }[] | null {
  const { w, wall, goals, boxes, player } = lv;
  const li = live(lv), row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !li[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rs: { boxes: number[]; goals: number[]; done?: boolean }[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const sq = [s];
    part[s] = rs.length;
    for (let i = 0; i < sq.length; i++)
      for (const [dx, dy] of D) {
        const q = sq[i]! + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rs.length; sq.push(q); }
      }
    rs.push({ boxes: [], goals: [] });
  }
  for (const b of boxes) rs[part[b]!]!.boxes.push(b);
  for (const g of goals) if (part[g]! >= 0) rs[part[g]!]!.goals.push(g);
  if (goals.some((g) => part[g]! < 0) || rs.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rs.filter((r) => r.boxes.length > 0);
}
function solveRooms(lv: L): { pushes: number; moves: string } | null {
  const rs = rooms(lv);
  if (rs === null) return opt(lv);
  let player = lv.player, pushes = 0, moves = '';
  for (const r of rs) {
    const wall = lv.wall.slice();
    for (const o of rs) if (o !== r) for (const b of o.done ? o.goals : o.boxes) wall[b] = 1;
    const s = opt({ w: lv.w, h: lv.h, wall, goals: r.goals.slice().sort((a, b) => a - b), boxes: r.boxes.slice().sort((a, b) => a - b), player });
    if (s === null) return null;
    pushes += s.pushes; moves += s.moves;
    player = endOf(lv.w, player, s.moves); r.done = true;
  }
  return { pushes, moves };
}
function solve(t: string): string {
  try {
    const lv = parse(t);
    const s = solveRooms(lv) ?? opt(lv);
    return s === null ? '' : s.moves;
  } catch { return ''; }
}
for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
