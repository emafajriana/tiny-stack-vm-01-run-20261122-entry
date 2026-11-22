// tiny-stack-vm: a complete interpreter for make.fun's tiny stack ISA, version 1.
// Runs every /input/<id>/ program.bin on its input.bin and answers in /output/<id>/
// with stdout.bin and exit.txt (its exit code), per ISA.md.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256, CALLS_MAX = 64, STEP_MAX = 1_000_000, OUT_MAX = 65_536;

// Per-opcode facts, packed: immediate bytes | pops << 3 | pushes << 5; -1 = no such
// opcode (trap 5). Rows: [opcode, imm, pops, pushes]. The block 0x10..0x22 pops 2,
// pushes 1, except NEG (0x17) and NOT (0x1b) at 1/1, listed here and so kept.
const META = new Int16Array(256).fill(-1);
{
  const rows = [
    0x00,0,0,0, 0x01,1,0,1, 0x02,4,0,1, 0x03,0,1,0, 0x04,0,1,2, 0x05,0,2,2, 0x06,0,2,3,
    0x07,0,3,3, 0x17,0,1,1, 0x1b,0,1,1, 0x30,2,0,0, 0x31,2,1,0, 0x32,2,1,0, 0x33,2,0,0,
    0x34,0,0,0, 0x40,0,1,1, 0x41,0,2,0, 0x50,0,1,0, 0x51,0,1,0, 0x52,0,0,1, 0x53,0,1,0,
  ];
  for (let k = 0; k < rows.length; k += 4) META[rows[k]] = rows[k + 1] | (rows[k + 2] << 3) | (rows[k + 3] << 5);
  for (let o = 0x10; o <= 0x22; o++) if (META[o] < 0) META[o] = (2 << 3) | (1 << 5);
}

// Runs one program to its end: the bytes it wrote and the code it ended with.
function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(STACK_MAX);
  const C = new Int32Array(CALLS_MAX);
  const M = new Int32Array(256);
  const buf = new Uint8Array(OUT_MAX);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  const done = (code: number) => ({ out: buf.slice(0, olen), code });
  for (;;) {
    // One step, in the ISA's order.
    if (steps === STEP_MAX) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const meta = META[op];
    if (meta < 0) return done(5);
    const imm = meta & 7;
    if (pc + imm >= n) return done(9);
    steps++;
    const pops = (meta >> 3) & 3;
    if (sp < pops) return done(2);
    if (sp - pops + (meta >> 5) > STACK_MAX) return done(3);
    const next = pc + 1 + imm;
    pc = next;
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      // Binary ops ( a b -- r ): /0 traps 4; INT_MIN / -1 wraps; x % -1 is 0;
      // unsigned ops read both operands as unsigned; shift counts are b AND 31.
      const b = D[sp - 1];
      const a = D[sp - 2];
      let r: number;
      if (op >= 0x13 && op <= 0x16 && b === 0) return done(4);
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b); // MUL: low 32 bits of the product
      else if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      else if (op === 0x14) r = b === -1 ? 0 : a % b | 0;
      else if (op === 0x15) r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      else if (op === 0x16) r = (a >>> 0) % (b >>> 0) | 0;
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = a >>> 0 < b >>> 0 ? 1 : 0;
      D[sp - 2] = r;
      sp--;
      continue;
    }
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break; // PUSH32
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG, wraps
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ: target = next + signed offset
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: target = the unsigned immediate
        if (csp === CALLS_MAX) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        M[addr] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII
        const s = String(D[sp - 1]);
        if (olen + s.length > OUT_MAX) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) buf[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > OUT_MAX) return done(11);
        buf[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        D[sp++] = inPos < inp.length ? inp[inPos++] : -1;
        break;
      case 0x53: // EXIT: the code is v AND 255
        return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
