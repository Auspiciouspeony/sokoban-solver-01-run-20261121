// Push-optimal Sokoban solver, room by room. Generated levels are a hallway
// with independent rooms off it (a box pushed out of a door never returns),
// so each room is solved push-optimally alone and the optima add up to the
// level's optimum: full points. BFS over pushes; a state is the boxes plus
// the player's reachable region (named by its lowest square). Prunes: dead
// squares (no pull path to any goal) and frozen 2x2 blocks. Pure work caps,
// never the clock, so two runs write identical bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const M = 250_000;
const D = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
type L = [number, Uint8Array, number[], number[], number];
function parse(t: string): L {
  const r = t.split('\n').filter((x) => x.length > 0), h = r.length, w = Math.max(...r.map((x) => x.length));
  const a = new Uint8Array(w * h).fill(1), g: number[] = [], b: number[] = [];
  let p = -1;
  r.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x]!, i = y * w + x; if (c === '#') continue; a[i] = 0; if ('.*+'.includes(c)) g.push(i); if ('$*'.includes(c)) b.push(i); if ('@+'.includes(c)) p = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) a[y * w + x] = 1;
  return [w, a, g, b.sort((x, y) => x - y), p];
}
function live(w: number, a: Uint8Array, g: number[]): Uint8Array {
  const l = new Uint8Array(a.length), q = [...g];
  for (const x of g) l[x] = 1;
  for (let i = 0; i < q.length; i++) { const x = q[i]!; for (const [dx, dy] of D) { const d = dy * w + dx, y = x - d; if (!a[y] && !a[y - d] && !l[y]) { l[y] = 1; q.push(y); } } }
  return l;
}
function reach(w: number, a: Uint8Array, o: Uint8Array, f: number, s: Int32Array, t: number, k: Int32Array): number {
  let lo = f, n = 0;
  k[n++] = f; s[f] = t;
  while (n > 0) { const p = k[--n]!; if (p < lo) lo = p; for (const q of [p - w, p + w, p - 1, p + 1]) if (!a[q] && !o[q] && s[q] !== t) { s[q] = t; k[n++] = q; } }
  return lo;
}
function frozen(w: number, a: Uint8Array, o: Uint8Array, g: Uint8Array, t: number): boolean {
  for (const x of [t, t - 1, t - w, t - w - 1]) { const b = x + 1, c = x + w, d = c + 1; if (!(a[x] || o[x]) || !(a[b] || o[b]) || !(a[c] || o[c]) || !(a[d] || o[d])) continue; if ((o[x] && !g[x]) || (o[b] && !g[b]) || (o[c] && !g[c]) || (o[d] && !g[d])) return true; }
  return false;
}
function walk(w: number, a: Uint8Array, o: Uint8Array, f: number, t: number): string {
  if (f === t) return '';
  const p = new Int32Array(a.length).fill(-1), h = new Array<string>(a.length), q = [f];
  p[f] = f;
  for (let i = 0; i < q.length; i++) { const x = q[i]!; if (x === t) break; for (const [dx, dy, l] of D) { const n = x + dy * w + dx; if (a[n] || o[n] || p[n] !== -1) continue; p[n] = x; h[n] = l; q.push(n); } }
  if (p[t] === -1) throw new Error('unreachable');
  let s = '';
  for (let x = t; x !== f; x = p[x]!) s = h[x]! + s;
  return s;
}
function opt(v: L, max = M): { n: number; m: string } | null {
  const [w, a, G, B, P] = v, S = a.length, g = new Uint8Array(S);
  for (const x of G) g[x] = 1;
  const li = live(w, a, G);
  if (B.some((b) => !li[b])) return null;
  const o = new Uint8Array(S), s1 = new Int32Array(S), s2 = new Int32Array(S), st = new Int32Array(S);
  let tm = 0;
  const ok = (b: number[]): boolean => b.every((x) => g[x]);
  const key = (b: number[], l: number): number => { let k = l; for (const x of b) k = k * S + x; return k; };
  const SB: number[][] = [B], SP: number[] = [P], pa: number[] = [-1], ix = new Map<number, number>();
  for (const b of B) o[b] = 1;
  ix.set(key(B, reach(w, a, o, P, s1, ++tm, st)), 0);
  for (const b of B) o[b] = 0;
  let fd = ok(B) ? 0 : -1;
  for (let hd = 0; fd < 0 && hd < SB.length; hd++) {
    const b = SB[hd]!;
    for (const x of b) o[x] = 1;
    reach(w, a, o, SP[hd]!, s1, ++tm, st);
    const he = tm;
    for (let bi = 0; bi < b.length && fd < 0; bi++) {
      const x = b[bi]!;
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = x + d;
        if (s1[x - d] !== he || a[t] || o[t] || !li[t]) continue;
        o[x] = 0; o[t] = 1;
        const fr = frozen(w, a, o, g, t);
        let k = -1, nx: number[] | null = null;
        if (!fr) { nx = b.slice(); nx[bi] = t; nx.sort((p, q) => p - q); k = key(nx, reach(w, a, o, x, s2, ++tm, st)); }
        o[t] = 0; o[x] = 1;
        if (fr || ix.has(k)) continue;
        if (SB.length >= max) { for (const y of b) o[y] = 0; return null; }
        ix.set(k, SB.length); SB.push(nx!); SP.push(x); pa.push(hd);
        if (ok(nx!)) { fd = SB.length - 1; break; }
      }
    }
    for (const x of b) o[x] = 0;
  }
  if (fd < 0) return null;
  const ph: number[] = [];
  for (let s = fd; s > 0; s = pa[s]!) ph.push(s);
  ph.reverse();
  let m = '', pl = P, b = B;
  for (const s of ph) {
    const nb = SB[s]!, f = b.find((x) => !nb.includes(x))!, t = nb.find((x) => !b.includes(x))!, d = t - f;
    const dr = D.find(([dx, dy]) => dy * w + dx === d)!;
    for (const x of b) o[x] = 1;
    m += walk(w, a, o, pl, f - d);
    for (const x of b) o[x] = 0;
    m += dr[3]; pl = f; b = nb;
  }
  return { n: ph.length, m };
}
function rooms(v: L): { b: number[]; g: number[]; d?: boolean }[] | null {
  const [w, a, G, B, P] = v, li = live(w, a, G), r = Math.floor(P / w), c = new Uint8Array(a.length);
  for (let i = r * w; i < (r + 1) * w; i++) if (!a[i] && !li[i]) c[i] = 1;
  if (B.some((b) => c[b])) return null;
  const pt = new Int32Array(a.length).fill(-1), rs: { b: number[]; g: number[]; d?: boolean }[] = [];
  for (let s = 0; s < a.length; s++) {
    if (a[s] || c[s] || pt[s] >= 0) continue;
    const q = [s];
    pt[s] = rs.length;
    for (let i = 0; i < q.length; i++) for (const [dx, dy] of D) { const n = q[i]! + dy * w + dx; if (!a[n] && !c[n] && pt[n] < 0) { pt[n] = rs.length; q.push(n); } }
    rs.push({ b: [], g: [] });
  }
  for (const b of B) rs[pt[b]!]!.b.push(b);
  for (const g of G) if (pt[g]! >= 0) rs[pt[g]!]!.g.push(g);
  if (G.some((g) => pt[g]! < 0) || rs.some((x) => x.b.length !== x.g.length)) return null;
  return rs.filter((x) => x.b.length > 0);
}
function solve(t: string): string {
  try {
    const v = parse(t), rs = rooms(v);
    if (rs === null) return opt(v)?.m ?? '';
    let pl = v[4], m = '';
    for (const r of rs) {
      const a = v[1].slice();
      for (const o of rs) if (o !== r) for (const b of o.d ? o.g : o.b) a[b] = 1;
      const s = opt([v[0], a, r.g.slice().sort((x, y) => x - y), r.b.slice().sort((x, y) => x - y), pl]);
      if (s === null) return '';
      m += s.m;
      for (const ch of s.m.toLowerCase()) pl += ch === 'u' ? -v[0] : ch === 'd' ? v[0] : ch === 'l' ? -1 : 1;
      r.d = true;
    }
    return m;
  } catch { return ''; }
}
for (const id of readdirSync(I).sort()) {
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${solve(readFileSync(join(I, id, 'level.txt'), 'utf8'))}\n`);
}
