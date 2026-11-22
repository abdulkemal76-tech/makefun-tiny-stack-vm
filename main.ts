// Tiny stack VM: fast, trap-exact interpreter of make.fun's tiny stack ISA v1.
// Pre-decodes each program once; the hot loop allocates nothing.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const HALT = 0, PUSH8 = 1, PUSH32 = 2, POP = 3, DUP = 4, SWAP = 5, OVER = 6, ROT = 7,
  ADD = 8, SUB = 9, MUL = 10, DIV = 11, MOD = 12, DIVU = 13, MODU = 14, NEG = 15,
  AND = 16, OR = 17, XOR = 18, NOT = 19, SHL = 20, SHR = 21, SHRU = 22, EQ = 23,
  LT = 24, LTU = 25, JMP = 26, JZ = 27, JNZ = 28, CALL = 29, RET = 30, LOAD = 31,
  STORE = 32, PRINT = 33, PUTC = 34, INP = 35, EXIT = 36;
const OP = new Int8Array(256).fill(-1), IL = new Uint8Array(256); // byte -> opcode id; imm lens: PUSH8 1, PUSH32 4, jumps/CALL 2
for (let i = 0; i < 8; i++) {
  OP[i] = i; OP[23 + i] = 15 + i;
  if (i < 7) OP[16 + i] = 8 + i;
  if (i < 5) OP[48 + i] = 26 + i;
  if (i < 4) OP[80 + i] = 33 + i;
  if (i < 3) OP[32 + i] = 23 + i;
}
OP[64] = 31; OP[65] = 32; IL[1] = 1; IL[2] = 4;
for (let i = 48; i < 52; i++) IL[i] = 2;
const POPS = [...'0001122322222221222122222201100121101'].map(Number); // pops per opcode id
const PUSH = [...'0110223311111111111111111100000100010'].map(Number); // pushes per opcode id
function run(p, inp) {
  const n = p.length;
  // Pre-decode every byte position: op, operand (push value / absolute target),
  // next address. -1 = unknown opcode (trap 5), -2 = cut-off immediate (trap 9).
  const op = new Int8Array(n), arg = new Int32Array(n), nx = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const o = OP[p[i]], l = IL[p[i]], m = i + 1 + l;
    nx[i] = m;
    if (o < 0) { op[i] = -1; continue; }
    if (i + l >= n) { op[i] = -2; continue; }
    op[i] = o;
    if (l === 1) arg[i] = (p[i + 1] << 24) >> 24;
    else if (l === 4) arg[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (l === 2) { const w = p[i + 1] | (p[i + 2] << 8); arg[i] = o === CALL ? w : m + ((w << 16) >> 16); }
  }
  const D = new Int32Array(256); let sp = 0;
  const C = new Int32Array(64); let cs = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536); let ol = 0;
  const dig = new Uint8Array(11); // PRINT scratch: at most "-2147483648"
  let ip = 0, pc = 0, steps = 0;
  const end = (c) => ({ out: out.subarray(0, ol), code: c });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const o = op[pc];
    if (o === -1) return end(5);
    if (o === -2) return end(9);
    steps++;
    if (sp < POPS[o]) return end(2);
    if (sp - POPS[o] + PUSH[o] > 256) return end(3);
    const a = arg[pc], n2 = nx[pc];
    switch (o) {
      case HALT: return end(0);
      case PUSH8: case PUSH32: D[sp++] = a; pc = n2; break;
      case POP: sp--; pc = n2; break;
      case DUP: D[sp] = D[sp - 1]; sp++; pc = n2; break;
      case SWAP: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; pc = n2; break; }
      case OVER: D[sp] = D[sp - 2]; sp++; pc = n2; break;
      case ROT: { const t = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t; pc = n2; break; }
      case NEG: D[sp - 1] = -D[sp - 1] | 0; pc = n2; break;
      case NOT: D[sp - 1] = ~D[sp - 1]; pc = n2; break;
      case ADD: case SUB: case MUL: case DIV: case MOD: case DIVU: case MODU:
      case AND: case OR: case XOR: case SHL: case SHR: case SHRU:
      case EQ: case LT: case LTU: {
        const b = D[sp - 1], x = D[sp - 2];
        let r;
        if (o === ADD) r = (x + b) | 0;
        else if (o === SUB) r = (x - b) | 0;
        else if (o === MUL) r = Math.imul(x, b);
        else if (o === DIV) { if (!b) return end(4); r = x === -2147483648 && b === -1 ? x : (x / b) | 0; }
        else if (o === MOD) { if (!b) return end(4); r = b === -1 ? 0 : (x % b) | 0; }
        else if (o === DIVU) { if (!b) return end(4); r = Math.floor((x >>> 0) / (b >>> 0)) | 0; }
        else if (o === MODU) { if (!b) return end(4); r = ((x >>> 0) % (b >>> 0)) | 0; }
        else if (o === AND) r = x & b;
        else if (o === OR) r = x | b;
        else if (o === XOR) r = x ^ b;
        else if (o === SHL) r = x << (b & 31);
        else if (o === SHR) r = x >> (b & 31);
        else if (o === SHRU) r = (x >>> (b & 31)) | 0;
        else if (o === EQ) r = x === b ? 1 : 0;
        else if (o === LT) r = x < b ? 1 : 0;
        else r = (x >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r; pc = n2; break;
      }
      case JMP: pc = a; break;
      case JZ: pc = D[--sp] === 0 ? a : n2; break;
      case JNZ: pc = D[--sp] !== 0 ? a : n2; break;
      case CALL: if (cs === 64) return end(7); C[cs++] = n2; pc = a; break;
      case RET: if (!cs) return end(8); pc = C[--cs]; break;
      case LOAD: { const ad = D[sp - 1]; if (ad < 0 || ad > 255) return end(6); D[sp - 1] = M[ad]; pc = n2; break; }
      case STORE: { const ad = D[sp - 1]; if (ad < 0 || ad > 255) return end(6); M[ad] = D[sp - 2]; sp -= 2; pc = n2; break; }
      case PRINT: {
        const v = D[sp - 1];
        let k = 0, u = v < 0 ? -v : v;
        if (!u) dig[k++] = 48;
        else while (u > 0) { dig[k++] = 48 + (u % 10); u = (u / 10) | 0; }
        if (v < 0) dig[k++] = 45;
        if (ol + k > 65536) return end(11);
        sp--;
        while (k > 0) out[ol++] = dig[--k];
        pc = n2; break;
      }
      case PUTC: if (ol + 1 > 65536) return end(11); out[ol++] = D[--sp] & 255; pc = n2; break;
      case INP: D[sp++] = ip < inp.length ? inp[ip++] : -1; pc = n2; break;
      case EXIT: return end(D[--sp] & 255);
    }
  }
}
for (const id of readdirSync(IN).sort()) {
  const dir = join(IN, id);
  let prog;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { continue; }
  let inp;
  try { inp = readFileSync(join(dir, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const { out, code } = run(prog, inp);
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), out);
  writeFileSync(join(OUT, id, 'exit.txt'), code + '\n');
}
