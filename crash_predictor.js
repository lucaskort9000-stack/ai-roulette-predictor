// Crash Game Live Predictor — standalone script
// Replicates the provided Python BLAKE2b provably-fair multiplier math exactly:
//   round_final_hash = blake2b(round_hash + global_seed, digest_size=32)
//   x = int.from_bytes(round_final_hash[:8], 'big') / (2**64 - 1)
//   outcome = clamp(floor(100 * (1 - 0.05) / x) / 100, 1, 1e6)
//   round_hash = blake2b(round_hash, 32)   (chain to next round)
//
// Usage: node crash_predictor.js
//
// Pure-JS BLAKE2b (RFC 7693 / blakejs port) — no external dependencies,
// works in Node and browsers (Web Crypto does not support BLAKE2b).

const BLAKE2B_IV32 = new Uint32Array([
  0xf3bcc908, 0x6a09e667, 0x84caa73b, 0xbb67ae85, 0xfe94f82b, 0x3c6ef372,
  0x5f1d36f1, 0xa54ff53a, 0xade682d1, 0x510e527f, 0x2b3e6c1f, 0x9b05688c,
  0xfb41bd6b, 0x1f83d9ab, 0x137e2179, 0x5be0cd19
]);

const SIGMA8 = [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 14, 10, 4, 8, 9, 15, 13,
  6, 1, 12, 0, 2, 11, 7, 5, 3, 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1,
  9, 4, 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8, 9, 0, 5, 7, 2, 4,
  10, 15, 14, 1, 11, 12, 6, 8, 3, 13, 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5,
  15, 14, 1, 9, 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11, 13, 11, 7,
  14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10, 6, 15, 14, 9, 11, 3, 0, 8, 12, 2,
  13, 7, 1, 4, 10, 5, 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0, 0,
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 14, 10, 4, 8, 9, 15, 13, 6,
  1, 12, 0, 2, 11, 7, 5, 3
];
const SIGMA82 = new Uint8Array(SIGMA8.map(x => x * 2));

function B2B_GET32(arr, i) {
  return arr[i] ^ (arr[i + 1] << 8) ^ (arr[i + 2] << 16) ^ (arr[i + 3] << 24);
}

const v32 = new Uint32Array(32);
const m32 = new Uint32Array(32);

function ADD64AA(a, b) {
  const o0 = v32[a] + v32[b];
  let o1 = v32[a + 1] + v32[b + 1];
  if (o0 >= 0x100000000) o1++;
  v32[a] = o0;
  v32[a + 1] = o1;
}

function ADD64AC(a, b0, b1) {
  let o0 = v32[a] + b0;
  if (b0 < 0) o0 += 0x100000000;
  let o1 = v32[a + 1] + b1;
  if (o0 >= 0x100000000) o1++;
  v32[a] = o0;
  v32[a + 1] = o1;
}

function B2B_G(a, b, c, d, ix, iy) {
  const x0 = m32[ix], x1 = m32[ix + 1];
  const y0 = m32[iy], y1 = m32[iy + 1];
  ADD64AA(a, b);
  ADD64AC(a, x0, x1);
  let xor0 = v32[d] ^ v32[a], xor1 = v32[d + 1] ^ v32[a + 1];
  v32[d] = xor1; v32[d + 1] = xor0;
  ADD64AA(c, d);
  xor0 = v32[b] ^ v32[c]; xor1 = v32[b + 1] ^ v32[c + 1];
  v32[b] = (xor0 >>> 24) ^ (xor1 << 8);
  v32[b + 1] = (xor1 >>> 24) ^ (xor0 << 8);
  ADD64AA(a, b);
  ADD64AC(a, y0, y1);
  xor0 = v32[d] ^ v32[a]; xor1 = v32[d + 1] ^ v32[a + 1];
  v32[d] = (xor0 >>> 16) ^ (xor1 << 16);
  v32[d + 1] = (xor1 >>> 16) ^ (xor0 << 16);
  ADD64AA(c, d);
  xor0 = v32[b] ^ v32[c]; xor1 = v32[b + 1] ^ v32[c + 1];
  v32[b] = (xor1 >>> 31) ^ (xor0 << 1);
  v32[b + 1] = (xor0 >>> 31) ^ (xor1 << 1);
}

function blake2bCompress(ctx, last) {
  let i;
  for (i = 0; i < 16; i++) {
    v32[i] = ctx.h[i];
    v32[i + 16] = BLAKE2B_IV32[i];
  }
  v32[24] = v32[24] ^ ctx.t;
  v32[25] = v32[25] ^ (ctx.t / 0x100000000 | 0);
  if (last) {
    v32[28] = ~v32[28];
    v32[29] = ~v32[29];
  }
  for (i = 0; i < 32; i++) {
    m32[i] = B2B_GET32(ctx.b, 4 * i);
  }
  for (i = 0; i < 12; i++) {
    const base = i * 16;
    B2B_G(0, 8, 16, 24, SIGMA82[base + 0], SIGMA82[base + 1]);
    B2B_G(2, 10, 18, 26, SIGMA82[base + 2], SIGMA82[base + 3]);
    B2B_G(4, 12, 20, 28, SIGMA82[base + 4], SIGMA82[base + 5]);
    B2B_G(6, 14, 22, 30, SIGMA82[base + 6], SIGMA82[base + 7]);
    B2B_G(0, 10, 20, 30, SIGMA82[base + 8], SIGMA82[base + 9]);
    B2B_G(2, 12, 22, 24, SIGMA82[base + 10], SIGMA82[base + 11]);
    B2B_G(4, 14, 16, 26, SIGMA82[base + 12], SIGMA82[base + 13]);
    B2B_G(6, 8, 18, 28, SIGMA82[base + 14], SIGMA82[base + 15]);
  }
  for (i = 0; i < 16; i++) {
    ctx.h[i] = ctx.h[i] ^ v32[i] ^ v32[i + 16];
  }
}

function blake2bInit(outlen) {
  const ctx = {
    b: new Uint8Array(128),
    h: new Uint32Array(16),
    t: 0,
    c: 0,
    outlen
  };
  ctx.h[0] = BLAKE2B_IV32[0] ^ (outlen | 0x01010000);
  for (let i = 1; i < 16; i++) ctx.h[i] = BLAKE2B_IV32[i];
  return ctx;
}

function blake2bUpdate(ctx, input) {
  for (let i = 0; i < input.length; i++) {
    if (ctx.c === 128) {
      ctx.t += ctx.c;
      blake2bCompress(ctx, false);
      ctx.c = 0;
    }
    ctx.b[ctx.c++] = input[i];
  }
}

function blake2bFinal(ctx) {
  ctx.t += ctx.c;
  while (ctx.c < 128) ctx.b[ctx.c++] = 0;
  blake2bCompress(ctx, true);
  const out = new Uint8Array(ctx.outlen);
  for (let i = 0; i < ctx.outlen; i++) {
    out[i] = ctx.h[i >> 2] >> (8 * (i & 3));
  }
  return out;
}

function blake2b(data, outlen = 64) {
  const ctx = blake2bInit(outlen);
  blake2bUpdate(ctx, data);
  return blake2bFinal(ctx);
}

function hexToBytes(hex) {
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
  return bytes;
}

function bytesToHex(bytes) {
  return Array.prototype.map.call(bytes, function (n) {
    return (n < 16 ? '0' : '') + n.toString(16);
  }).join('');
}

// Read first 8 bytes as unsigned 64-bit big-endian (matches Python int.from_bytes(..., 'big'))
function readU64BE(bytes, offset) {
  let v = 0n;
  for (let i = 0; i < 8; i++) v = (v << 8n) | BigInt(bytes[offset + i]);
  return v;
}

// Compute crash outcome for one round, mirroring the Python exactly.
function computeCrashOutcome(roundHashHex, globalSeedHex) {
  const roundHash = hexToBytes(roundHashHex);
  const globalSeed = hexToBytes(globalSeedHex);
  const combined = new Uint8Array(roundHash.length + globalSeed.length);
  combined.set(roundHash);
  combined.set(globalSeed, roundHash.length);
  const finalHash = blake2b(combined, 32);
  const den = Math.pow(2, 64) - 1;
  const x = Number(readU64BE(finalHash, 0)) / den;
  const outcome = Math.min(1e6, Math.max(1.0, Math.floor(100.0 * (1.0 - 0.05) / x) / 100.0));
  return { finalHash, x, outcome };
}

// Chain: next round_hash = blake2b(round_hash, 32)
function nextRoundHash(roundHashHex) {
  return bytesToHex(blake2b(hexToBytes(roundHashHex), 32));
}

// ---- Run ----
const GLOBAL_SEED = 'c8225bd2069844633b47f9a32b12b136400e86f5cb8cbfec29eb617d507ecf40';
let roundHash = '9f78c0bb99661cb49d4f97cd69a01d555caff083614ce3c9b47d2d265de6aec1';

for (let i = 10; i >= 9; i--) {
  const r = computeCrashOutcome(roundHash, GLOBAL_SEED);
  console.log('Round: ', i);
  console.log('Round Hash: ', roundHash);
  console.log('Round Outcome: ', outcomeToString(r.outcome));
  roundHash = nextRoundHash(roundHash);
}

function outcomeToString(v) {
  // Match Python's default float printing (e.g. 2.45, 1.29)
  return v.toFixed(2).replace(/\.0+$/, '').replace(/(\.\d*?[1-9])0+$/, '$1') || '0';
}
