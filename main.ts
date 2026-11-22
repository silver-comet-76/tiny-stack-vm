import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Tiny stack VM, ISA v1. Follows generator/subject/vm.mjs exactly:
// step limit 10, pc trap 9, bad opcode 5, underflow 2, overflow 3,
// div-by-zero 4, memory 6, call depth 7, empty RET 8, output 11.
function run(p: Uint8Array, q: Uint8Array): { o: Uint8Array; c: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (c: number) => ({ o: O.slice(0, ol), c });
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    if (!(op < 8 || (op >= 16 && op <= 30) || (op >= 32 && op <= 34) || (op >= 48 && op <= 52) || (op >= 64 && op <= 65) || (op >= 80 && op <= 83))) return end(5);
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    pc = nx;
    if (op >= 16 && op <= 34 && op !== 23 && op !== 27) {
      if (sp < 2) return end(2);
      const b = D[sp - 1], a = D[sp - 2];
      let r = 0;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2;
      D[sp++] = r;
      continue;
    }
    switch (op) {
      case 0: return end(0);
      case 1:
        if (sp > 255) return end(3);
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 2:
        if (sp > 255) return end(3);
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 3:
        if (sp < 1) return end(2);
        sp--;
        break;
      case 4:
        if (sp < 1) return end(2);
        if (sp > 255) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: {
        if (sp < 2) return end(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6:
        if (sp < 2) return end(2);
        if (sp > 255) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: {
        if (sp < 3) return end(2);
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 23:
        if (sp < 1) return end(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27:
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 48:
        pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16);
        break;
      case 49:
      case 50: {
        if (sp < 1) return end(2);
        const v = D[--sp];
        if ((op === 49) === (v === 0)) pc = nx + (((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16);
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        if (sp < 1) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        if (sp < 2) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 80: {
        // Decimal output, written digit by digit from the end (no string alloc).
        if (sp < 1) return end(2);
        const v = D[sp - 1];
        let x = v < 0 ? -v : v;
        let d = v === 0 ? 1 : 0;
        for (let t = x; t > 0; t = (t / 10) | 0) d++;
        if (v < 0) d++;
        if (ol + d > 65536) return end(11);
        sp--;
        if (x === 0) O[ol] = 48;
        else { let w = ol + d; while (x > 0) { O[--w] = 48 + (x % 10); x = (x / 10) | 0; } }
        if (v < 0) O[ol] = 45;
        ol += d;
        break;
      }
      case 81:
        if (sp < 1) return end(2);
        if (ol + 1 > 65536) return end(11);
        O[ol++] = D[--sp] & 255;
        break;
      case 82:
        if (sp > 255) return end(3);
        D[sp++] = ip < q.length ? q[ip++] : -1;
        break;
      case 83:
        if (sp < 1) return end(2);
        return end(D[--sp] & 255);
      default:
        return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.c + '\n');
}
