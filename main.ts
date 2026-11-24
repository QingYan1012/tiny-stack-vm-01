// tiny-stack-vm-01: an interpreter for make.fun's tiny stack ISA (v1).
//
// For every instance directory in the input dir, run its program.bin against
// its input.bin and write stdout.bin (the exact bytes the program emitted)
// plus exit.txt (its exit code, 0-255; a trap's code when it trapped).
//
// Machine: 32-bit wrapping values, data stack of 256, call stack of 64,
// 256 words of memory, at most 1,000,000 steps and 65,536 output bytes.

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const SRC = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const DST = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Run one program to its end. Returns [output bytes, exit code].
function run(prog, inp) {
  const plen = prog.length;
  const vals = new Int32Array(256); // data stack
  let top = 0;
  const rets = new Int32Array(64); // return addresses
  let depth = 0;
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65536); // everything the program writes
  let used = 0;
  let read = 0; // input cursor
  let pc = 0;
  let steps = 0;

  const end = (code) => [buf.slice(0, used), code];

  for (;;) {
    if (steps >= 1000000) return end(10);
    if (pc < 0 || pc >= plen) return end(9);
    const op = prog[pc];
    const known =
      op < 8 ||
      (op >= 0x10 && op <= 0x1e) ||
      (op >= 0x20 && op <= 0x22) ||
      (op >= 0x30 && op <= 0x34) ||
      op === 0x40 ||
      op === 0x41 ||
      (op >= 0x50 && op <= 0x53);
    if (!known) return end(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= plen) return end(9);
    steps++;
    const next = pc + 1 + imm;
    pc = next;

    if (op < 8) {
      // HALT, PUSH8, PUSH32, POP, DUP, SWAP, OVER, ROT
      if (op === 0) return end(0);
      if (op === 1 || op === 2) {
        if (top === 256) return end(3);
        vals[top++] =
          op === 1
            ? (prog[next - 1] << 24) >> 24
            : prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
      } else if (op === 3) {
        if (top < 1) return end(2);
        top--;
      } else if (op === 4) {
        if (top < 1) return end(2);
        if (top === 256) return end(3);
        vals[top] = vals[top - 1];
        top++;
      } else if (op === 5) {
        if (top < 2) return end(2);
        const t = vals[top - 1];
        vals[top - 1] = vals[top - 2];
        vals[top - 2] = t;
      } else if (op === 6) {
        if (top < 2) return end(2);
        if (top === 256) return end(3);
        vals[top] = vals[top - 2];
        top++;
      } else {
        if (top < 3) return end(2);
        const a = vals[top - 3];
        vals[top - 3] = vals[top - 2];
        vals[top - 2] = vals[top - 1];
        vals[top - 1] = a;
      }
    } else if (op < 0x30) {
      // Arithmetic, logic, shifts, comparisons: binary (a b -- r), plus NEG / NOT (a -- r).
      if (op === 0x17 || op === 0x1b) {
        if (top < 1) return end(2);
        vals[top - 1] = op === 0x17 ? -vals[top - 1] | 0 : ~vals[top - 1];
        continue;
      }
      if (top < 2) return end(2);
      const b = vals[top - 1];
      const a = vals[top - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) {
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return end(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (op === 0x15) {
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 0x16) {
        if (b === 0) return end(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      vals[top - 2] = r;
      top--;
    } else if (op < 0x35) {
      // JMP, JZ, JNZ, CALL, RET
      if (op === 0x34) {
        if (depth === 0) return end(8);
        pc = rets[--depth];
        continue;
      }
      if (op === 0x33) {
        if (depth === 64) return end(7);
        rets[depth++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        continue;
      }
      const off = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
      let go = op === 0x30;
      if (!go) {
        if (top < 1) return end(2);
        const v = vals[--top];
        go = op === 0x31 ? v === 0 : v !== 0;
      }
      if (go) pc = next + off;
    } else if (op < 0x42) {
      // LOAD, STORE
      if (op === 0x40) {
        if (top < 1) return end(2);
        const addr = vals[top - 1];
        if (addr < 0 || addr > 255) return end(6);
        vals[top - 1] = mem[addr];
      } else {
        if (top < 2) return end(2);
        const addr = vals[top - 1];
        if (addr < 0 || addr > 255) return end(6);
        mem[addr] = vals[top - 2];
        top -= 2;
      }
    } else {
      // PRINT, PUTC, IN, EXIT
      if (op === 0x50) {
        if (top < 1) return end(2);
        const s = String(vals[top - 1]);
        if (used + s.length > 65536) return end(11);
        top--;
        for (let i = 0; i < s.length; i++) buf[used++] = s.charCodeAt(i);
      } else if (op === 0x51) {
        if (top < 1) return end(2);
        if (used === 65536) return end(11);
        buf[used++] = vals[--top] & 255;
      } else if (op === 0x52) {
        if (top === 256) return end(3);
        vals[top++] = read < inp.length ? inp[read++] : -1;
      } else {
        if (top < 1) return end(2);
        return end(vals[--top] & 255);
      }
    }
  }
}

for (const id of readdirSync(SRC).sort()) {
  const prog = readFileSync(join(SRC, id, 'program.bin'));
  let inp;
  try {
    inp = readFileSync(join(SRC, id, 'input.bin'));
  } catch {
    inp = Buffer.alloc(0);
  }
  const [bytes, code] = run(prog, inp);
  mkdirSync(join(DST, id), { recursive: true });
  writeFileSync(join(DST, id, 'stdout.bin'), bytes);
  writeFileSync(join(DST, id, 'exit.txt'), code + '\n');
}
