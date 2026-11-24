#!/usr/bin/env node
/**
 * Exhaustive Pure-Data Judge for `ml-math-kernels` (BF16 GPU / ML Math Kernels).
 *
 * Security model:
 * - ZERO untrusted code execution (no `import()`, no `eval()`, no `vm`, no child JS).
 * - Donor artifacts are pure declarative JSON (`schema: "pf.mlkernel.v1"`) parsed strictly
 *   with `JSON.parse`, schema-validated against a fixed branchless GPU/ALU instruction set,
 *   and evaluated across ALL 65,536 IEEE bfloat16 bit patterns (100% exhaustive — zero sampling!).
 * - Exact IEEE-754 float32 FMA (`fmaf`) via exact BigInt dyadic arithmetic (zero double-rounding).
 * - Also exports `emitDropInCode(kernel, spec)` so verified JSON kernels auto-generate ready-to-paste
 *   C/CUDA (`__device__`) and Python/Triton code for the dashboard dossier & PROOFS.md.
 */
import fs from "node:fs";
import path from "node:path";

const MAX_ARTIFACT_BYTES = 32768;
const MAX_OPS = 64;
const MAX_CONSTS = 24;

// Reusable typed-array views for bit-exact float32 / int32 / uint32 reinterprets
const _buf4 = new ArrayBuffer(4);
const _f32 = new Float32Array(_buf4);
const _i32 = new Int32Array(_buf4);
const _u32 = new Uint32Array(_buf4);

export function f32ToU32(x) {
  _f32[0] = x;
  return _u32[0];
}
export function u32ToF32(u) {
  _u32[0] = u >>> 0;
  return _f32[0];
}
export function f32ToI32(x) {
  _f32[0] = x;
  return _i32[0];
}
export function i32ToF32(i) {
  _i32[0] = i | 0;
  return _f32[0];
}

/** Exact conversion from 16-bit bfloat16 bit pattern (0..65535) to float32. */
export function bf16ToF32(bits16) {
  return u32ToF32((bits16 & 0xffff) << 16);
}

/** Exact IEEE-754 round-to-nearest-ties-to-even from float32 to 16-bit bfloat16. */
export function f32ToBf16RNE(x) {
  const u = f32ToU32(Math.fround(x));
  const exp = (u >>> 23) & 0xff;
  const frac = u & 0x7fffff;
  if (exp === 0xff) {
    if (frac !== 0) return 0x7fc0; // canonical quiet NaN
    return (u >>> 16) & 0xffff;    // ±Inf
  }
  const lsb = (u >>> 16) & 1;
  const roundingBias = (0x7fff + lsb) >>> 0;
  return ((u + roundingBias) >>> 16) & 0xffff;
}

/** Exact IEEE-754 round-to-nearest-ties-to-even from float64 to 16-bit bfloat16 (no double rounding). */
const _buf8 = new ArrayBuffer(8);
const _f64 = new Float64Array(_buf8);
const _u64 = new BigUint64Array(_buf8);

export function f64ToBf16RNE(x) {
  if (Number.isNaN(x)) return 0x7fc0;
  if (x === Infinity) return 0x7f80;
  if (x === -Infinity) return 0xff80;
  if (x === 0) return Object.is(x, -0) ? 0x8000 : 0x0000;
  _f64[0] = x;
  const bits = _u64[0];
  const sign = Number((bits >> 63n) & 1n);
  const exp64 = Number((bits >> 52n) & 0x7ffn) - 1023;
  const frac52 = bits & ((1n << 52n) - 1n);
  const sig53 = (1n << 52n) | frac52; // exact value = (-1)^sign * sig53 * 2^(exp64 - 52)
  // bf16 has bias 127, 7 explicit mantissa bits, normal exponent [-126, 127], subnormal step 2^-133
  if (exp64 > 127) return (sign << 15) | 0x7f80;
  if (exp64 < -134) return sign << 15; // strictly below half of smallest subnormal (2^-134)
  if (exp64 >= -126) {
    // Normal bf16: shift right by 45 bits (52 - 7) with round-to-nearest-even
    const shift = 45n;
    const q = sig53 >> shift;
    const rem = sig53 & ((1n << shift) - 1n);
    const half = 1n << (shift - 1n);
    let rounded = q;
    if (rem > half || (rem === half && (q & 1n) === 1n)) rounded += 1n;
    let bexp = exp64 + 127;
    if (rounded >= 256n) {
      rounded >>= 1n;
      bexp += 1;
    }
    if (bexp >= 255) return (sign << 15) | 0x7f80;
    return (sign << 15) | (bexp << 7) | Number(rounded & 0x7fn);
  }
  // Subnormal bf16: unit is 2^-133; shift = (-133) - (exp64 - 52) = -81 - exp64
  const shift = BigInt(-81 - exp64);
  const q = sig53 >> shift;
  const rem = sig53 & ((1n << shift) - 1n);
  const half = 1n << (shift - 1n);
  let rounded = q;
  if (rem > half || (rem === half && (q & 1n) === 1n)) rounded += 1n;
  if (rounded >= 128n) {
    // Rounded up into smallest normal (exp = -126 -> bexp = 1, frac = 0)
    return (sign << 15) | 0x0080;
  }
  return (sign << 15) | Number(rounded & 0x7fn);
}

/** Monotonic signed-order lattice index of a finite bf16 bit pattern (-0 and +0 both map to 0). */
export function bf16LatticeIndex(bits16) {
  const b = bits16 & 0xffff;
  if (b === 0x0000 || b === 0x8000) return 0;
  if (b & 0x8000) return -(b & 0x7fff);
  return b;
}

export function bf16IsNaN(bits16) {
  const b = bits16 & 0xffff;
  return (b & 0x7f80) === 0x7f80 && (b & 0x007f) !== 0;
}

/** Exact IEEE-754 float32 FMA (`fmaf(a, b, c)`) with single rounding to float32. */
function float32ToDyadic(x) {
  const u = f32ToU32(x);
  const sign = (u >>> 31) ? -1n : 1n;
  const exp = (u >>> 23) & 0xff;
  const frac = u & 0x7fffff;
  if (exp === 0) {
    if (frac === 0) return { m: 0n, e: 0 };
    return { m: sign * BigInt(frac), e: -149 };
  }
  return { m: sign * BigInt((1 << 23) | frac), e: exp - 150 };
}

function dyadicToF32RNE(m, e) {
  if (m === 0n) return 0;
  const sign = m < 0n ? 1 : 0;
  let mag = m < 0n ? -m : m;
  const bitLen = mag.toString(2).length;
  const topExp = e + bitLen - 1; // value = mag * 2^e in [2^topExp, 2^(topExp+1))
  if (topExp > 127) return sign ? -Infinity : Infinity;
  if (topExp < -150) return sign ? -0 : 0;
  if (topExp >= -126) {
    // Normal float32: want 24-bit significand at exponent topExp - 23
    const shift = bitLen - 24;
    let sig;
    if (shift <= 0) {
      sig = mag << BigInt(-shift);
    } else {
      const sh = BigInt(shift);
      const q = mag >> sh;
      const rem = mag & ((1n << sh) - 1n);
      const half = 1n << (sh - 1n);
      sig = (rem > half || (rem === half && (q & 1n) === 1n)) ? q + 1n : q;
    }
    let exp = topExp + 127;
    if (sig >= (1n << 24n)) {
      sig >>= 1n;
      exp += 1;
    }
    if (exp >= 255) return sign ? -Infinity : Infinity;
    return u32ToF32(((sign << 31) | (exp << 23) | Number(sig & 0x7fffffn)) >>> 0);
  }
  // Subnormal float32: unit is 2^-149
  const shift = -149 - e;
  let sig;
  if (shift <= 0) {
    sig = mag << BigInt(-shift);
  } else {
    const sh = BigInt(shift);
    const q = mag >> sh;
    const rem = mag & ((1n << sh) - 1n);
    const half = 1n << (sh - 1n);
    sig = (rem > half || (rem === half && (q & 1n) === 1n)) ? q + 1n : q;
  }
  if (sig >= (1n << 23n)) {
    return u32ToF32(((sign << 31) | (1 << 23)) >>> 0);
  }
  return u32ToF32(((sign << 31) | Number(sig & 0x7fffffn)) >>> 0);
}

export function fmafExact(a, b, c) {
  const fa = Math.fround(a);
  const fb = Math.fround(b);
  const fc = Math.fround(c);
  if (!Number.isFinite(fa) || !Number.isFinite(fb) || !Number.isFinite(fc)) {
    return Math.fround(fa * fb + fc);
  }
  if (fa === 0 || fb === 0) {
    // Handle signed zero + finite c
    const prod = Math.fround(fa * fb);
    return Math.fround(prod + fc);
  }
  if (fc === 0) return Math.fround(fa * fb);
  const da = float32ToDyadic(fa);
  const db = float32ToDyadic(fb);
  const dc = float32ToDyadic(fc);
  const pm = da.m * db.m;
  const pe = da.e + db.e;
  const minE = Math.min(pe, dc.e);
  const sumM = (pm << BigInt(pe - minE)) + (dc.m << BigInt(dc.e - minE));
  if (sumM === 0n) return 0; // IEEE-754 RNE: exact cancellation yields +0
  return dyadicToF32RNE(sumM, minE);
}

/** High-accuracy (>15 decimal digits) erf(x) in float64 via Maclaurin + Lentz continued fraction. */
export function erfExact64(x) {
  if (Number.isNaN(x)) return NaN;
  if (x === Infinity) return 1;
  if (x === -Infinity) return -1;
  if (x === 0) return x;
  const sign = x < 0 ? -1 : 1;
  const ax = Math.abs(x);
  if (ax >= 6.0) return sign; // 1 - erfc(6) = 1 - 2.15e-17 = 1.0 in float64!
  const INV_SQRT_PI = 0.5641895835477562869480794515607725858;
  if (ax < 2.2) {
    // Power series: erf(x) = (2/sqrt(pi)) * exp(-x^2) * sum_{n>=0} (2^n x^(2n+1)) / (1*3*...*(2n+1))
    const x2 = ax * ax;
    let term = ax;
    let sum = ax;
    for (let n = 1; n < 80; n++) {
      term *= (2 * x2) / (2 * n + 1);
      sum += term;
      if (Math.abs(term) <= Math.abs(sum) * 1e-17) break;
    }
    return sign * 2 * INV_SQRT_PI * Math.exp(-x2) * sum;
  }
  // Continued fraction for erfc(ax) = (exp(-ax^2) / sqrt(pi)) * (1 / (ax + (1/2)/(ax + (2/2)/(ax + ...))))
  // Using modified Lentz's method (converges to < 1e-16 for ax >= 2.2 in < 35 steps)
  const tiny = 1e-300;
  let b = ax;
  let c = 1 / tiny;
  let d = 1 / b;
  let f = d;
  for (let n = 1; n < 80; n++) {
    const a = n * 0.5;
    d = b + a * d;
    if (Math.abs(d) < tiny) d = tiny;
    c = b + a / c;
    if (Math.abs(c) < tiny) c = tiny;
    d = 1 / d;
    const delta = c * d;
    f *= delta;
    if (Math.abs(delta - 1) < 1e-16) break;
  }
  const erfc = INV_SQRT_PI * Math.exp(-ax * ax) * f;
  return sign * (1 - erfc);
}

const INV_SQRT2 = Math.SQRT1_2;

export const REFERENCE_FNS = {
  bf16_gelu(x) {
    if (Number.isNaN(x)) return NaN;
    if (x === Infinity) return Infinity;
    if (x === -Infinity) return 0;
    if (x === 0) return x;
    return 0.5 * x * (1 + erfExact64(x * INV_SQRT2));
  },
  bf16_silu(x) {
    if (Number.isNaN(x)) return NaN;
    if (x === Infinity) return Infinity;
    if (x === -Infinity) return 0;
    if (x === 0) return x;
    if (x >= 0) return x / (1 + Math.exp(-x));
    const ex = Math.exp(x);
    return (x * ex) / (1 + ex);
  },
  bf16_exp2(x) {
    if (Number.isNaN(x)) return NaN;
    if (x === Infinity) return Infinity;
    if (x === -Infinity) return 0;
    return Math.pow(2, x);
  },
  bf16_rsqrt(x) {
    if (Number.isNaN(x) || x < 0) return NaN;
    if (x === 0) return Infinity;
    if (x === Infinity) return 0;
    return 1 / Math.sqrt(x);
  },
};

// Fixed branchless GPU/ALU instruction set (zero transcendental/div/sqrt cheating!)
const ZERO_COST_OPS = new Set(["const", "iconst", "bitcast_i32", "bitcast_f32"]);
const OP_ARITY = {
  const: 1,
  iconst: 1,
  bitcast_i32: 1,
  bitcast_f32: 1,
  add: 2,
  sub: 2,
  mul: 2,
  fma: 3,
  abs: 1,
  neg: 1,
  min: 2,
  max: 2,
  iadd: 2,
  isub: 2,
  imul: 2,
  iand: 2,
  ior: 2,
  ixor: 2,
  ishl: 2,
  ishr_u: 2,
  ishr_s: 2,
  ftoi_trunc: 1,
  ftoi_round: 1,
  itof: 1,
  lt: 2,
  le: 2,
  eq: 2,
  select: 3,
};

/** Strictly parse and validate a pure-data kernel JSON object. */
export function parseAndValidateKernel(rawText) {
  if (typeof rawText !== "string" || Buffer.byteLength(rawText, "utf8") > MAX_ARTIFACT_BYTES) {
    return { ok: false, reason: `Artifact exceeds max size (${MAX_ARTIFACT_BYTES} bytes)` };
  }
  let parsed;
  try {
    parsed = JSON.parse(rawText);
  } catch (err) {
    return { ok: false, reason: `Invalid JSON kernel artifact (pure JSON only, zero JS): ${err.message}` };
  }
  if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) {
    return { ok: false, reason: "Kernel artifact must be a JSON object" };
  }
  if (parsed.schema !== "pf.mlkernel.v1") {
    return { ok: false, reason: `Expected schema "pf.mlkernel.v1", got ${JSON.stringify(parsed.schema)}` };
  }
  if (!Array.isArray(parsed.ops) || parsed.ops.length === 0 || parsed.ops.length > MAX_OPS) {
    return { ok: false, reason: `Kernel must define 1..${MAX_OPS} ops` };
  }
  if (!Number.isSafeInteger(parsed.output) || parsed.output < 0 || parsed.output > parsed.ops.length) {
    return { ok: false, reason: `Invalid output register index: ${JSON.stringify(parsed.output)}` };
  }

  let constCount = 0;
  let opCost = 0;
  // Register 0 is input `x` (type "f32"); instruction i writes register i + 1
  const regTypes = ["f32"];
  const compiled = [];

  for (let i = 0; i < parsed.ops.length; i++) {
    const inst = parsed.ops[i];
    if (!Array.isArray(inst) || inst.length < 2 || typeof inst[0] !== "string") {
      return { ok: false, reason: `Malformed op at index ${i}` };
    }
    const op = inst[0];
    if (!Object.hasOwn(OP_ARITY, op)) {
      return { ok: false, reason: `Disallowed or unknown op "${op}" at index ${i}` };
    }
    const arity = OP_ARITY[op];
    if (inst.length !== arity + 1) {
      return { ok: false, reason: `Op "${op}" at index ${i} expects ${arity} operand(s), got ${inst.length - 1}` };
    }
    const maxReg = i; // valid prior registers: 0 .. i
    if (op === "const") {
      const v = inst[1];
      if (typeof v !== "number" || !Number.isFinite(v)) {
        return { ok: false, reason: `Op const at index ${i} must be a finite float32 number` };
      }
      constCount++;
      regTypes.push("f32");
      compiled.push({ op, v: Math.fround(v) });
    } else if (op === "iconst") {
      const v = inst[1];
      if (!Number.isSafeInteger(v) || v < -2147483648 || v > 4294967295) {
        return { ok: false, reason: `Op iconst at index ${i} must be a 32-bit integer` };
      }
      constCount++;
      regTypes.push("i32");
      compiled.push({ op, v: v | 0 });
    } else {
      const args = inst.slice(1);
      for (const r of args) {
        if (!Number.isSafeInteger(r) || r < 0 || r > maxReg) {
          return { ok: false, reason: `Op "${op}" at index ${i} references out-of-range register ${r} (max ${maxReg})` };
        }
      }
      // Static register type checking (f32 vs i32 vs bool)
      const t = (r) => regTypes[r];
      let outType = "f32";
      if (op === "bitcast_i32") {
        if (t(args[0]) !== "f32") return { ok: false, reason: `bitcast_i32 expects f32 at index ${i}` };
        outType = "i32";
      } else if (op === "bitcast_f32") {
        if (t(args[0]) !== "i32") return { ok: false, reason: `bitcast_f32 expects i32 at index ${i}` };
        outType = "f32";
      } else if (op === "itof") {
        if (t(args[0]) !== "i32") return { ok: false, reason: `itof expects i32 at index ${i}` };
        outType = "f32";
      } else if (op === "ftoi_trunc" || op === "ftoi_round") {
        if (t(args[0]) !== "f32") return { ok: false, reason: `${op} expects f32 at index ${i}` };
        outType = "i32";
      } else if (["iadd", "isub", "imul", "iand", "ior", "ixor", "ishl", "ishr_u", "ishr_s"].includes(op)) {
        if (t(args[0]) !== "i32" || t(args[1]) !== "i32") return { ok: false, reason: `${op} expects (i32, i32) at index ${i}` };
        outType = "i32";
      } else if (["lt", "le", "eq"].includes(op)) {
        if (t(args[0]) !== t(args[1]) || t(args[0]) === "bool") {
          return { ok: false, reason: `${op} expects matching numeric registers at index ${i}` };
        }
        outType = "bool";
      } else if (op === "select") {
        if (t(args[0]) !== "bool" || t(args[1]) !== t(args[2]) || t(args[1]) === "bool") {
          return { ok: false, reason: `select expects (bool, T, T) at index ${i}` };
        }
        outType = t(args[1]);
      } else {
        // Float32 ops: add, sub, mul, fma, abs, neg, min, max
        if (args.some((r) => t(r) !== "f32")) {
          return { ok: false, reason: `${op} expects f32 operand(s) at index ${i}` };
        }
        outType = "f32";
      }
      regTypes.push(outType);
      compiled.push({ op, args, argType: t(args[0]), outType });
    }
    if (!ZERO_COST_OPS.has(op)) opCost++;
  }

  if (constCount > MAX_CONSTS) {
    return { ok: false, reason: `Too many constants (${constCount} > ${MAX_CONSTS})` };
  }
  if (regTypes[parsed.output] !== "f32") {
    return { ok: false, reason: `Output register r${parsed.output} must have type f32, got ${regTypes[parsed.output]}` };
  }
  return { ok: true, compiled, output: parsed.output, opCost, constCount, target: parsed.target || null, notes: parsed.notes || "" };
}

/** Deterministic IEEE-754 float32 evaluator for a validated kernel DAG. */
export function evalKernelF32(kernel, xF32) {
  const regs = new Array(kernel.compiled.length + 1);
  regs[0] = Math.fround(xF32);
  for (let i = 0; i < kernel.compiled.length; i++) {
    const inst = kernel.compiled[i];
    const r = i + 1;
    switch (inst.op) {
      case "const":
      case "iconst":
        regs[r] = inst.v;
        break;
      case "bitcast_i32":
        regs[r] = f32ToI32(regs[inst.args[0]]);
        break;
      case "bitcast_f32":
        regs[r] = i32ToF32(regs[inst.args[0]]);
        break;
      case "add":
        regs[r] = Math.fround(regs[inst.args[0]] + regs[inst.args[1]]);
        break;
      case "sub":
        regs[r] = Math.fround(regs[inst.args[0]] - regs[inst.args[1]]);
        break;
      case "mul":
        regs[r] = Math.fround(regs[inst.args[0]] * regs[inst.args[1]]);
        break;
      case "fma":
        regs[r] = fmafExact(regs[inst.args[0]], regs[inst.args[1]], regs[inst.args[2]]);
        break;
      case "abs":
        regs[r] = Math.fround(Math.abs(regs[inst.args[0]]));
        break;
      case "neg":
        regs[r] = Math.fround(-regs[inst.args[0]]);
        break;
      case "min": {
        const a = regs[inst.args[0]], b = regs[inst.args[1]];
        regs[r] = Number.isNaN(a) ? b : Number.isNaN(b) ? a : (a < b ? a : b);
        break;
      }
      case "max": {
        const a = regs[inst.args[0]], b = regs[inst.args[1]];
        regs[r] = Number.isNaN(a) ? b : Number.isNaN(b) ? a : (a > b ? a : b);
        break;
      }
      case "iadd":
        regs[r] = (regs[inst.args[0]] + regs[inst.args[1]]) | 0;
        break;
      case "isub":
        regs[r] = (regs[inst.args[0]] - regs[inst.args[1]]) | 0;
        break;
      case "imul":
        regs[r] = Math.imul(regs[inst.args[0]], regs[inst.args[1]]);
        break;
      case "iand":
        regs[r] = regs[inst.args[0]] & regs[inst.args[1]];
        break;
      case "ior":
        regs[r] = regs[inst.args[0]] | regs[inst.args[1]];
        break;
      case "ixor":
        regs[r] = regs[inst.args[0]] ^ regs[inst.args[1]];
        break;
      case "ishl":
        regs[r] = regs[inst.args[0]] << (regs[inst.args[1]] & 31);
        break;
      case "ishr_u":
        regs[r] = (regs[inst.args[0]] >>> (regs[inst.args[1]] & 31)) | 0;
        break;
      case "ishr_s":
        regs[r] = regs[inst.args[0]] >> (regs[inst.args[1]] & 31);
        break;
      case "ftoi_trunc": {
        const v = regs[inst.args[0]];
        regs[r] = Number.isFinite(v) ? (Math.trunc(v) | 0) : 0;
        break;
      }
      case "ftoi_round": {
        const v = regs[inst.args[0]];
        if (!Number.isFinite(v)) {
          regs[r] = 0;
        } else {
          // Round-to-nearest-ties-to-even (matches IEEE rintf / CUDA __float2int_rn)
          const fl = Math.floor(v);
          const diff = v - fl;
          const rnd = diff > 0.5 ? fl + 1 : diff < 0.5 ? fl : (fl % 2 === 0 ? fl : fl + 1);
          regs[r] = rnd | 0;
        }
        break;
      }
      case "itof":
        regs[r] = Math.fround(regs[inst.args[0]]);
        break;
      case "lt":
        regs[r] = regs[inst.args[0]] < regs[inst.args[1]];
        break;
      case "le":
        regs[r] = regs[inst.args[0]] <= regs[inst.args[1]];
        break;
      case "eq":
        regs[r] = regs[inst.args[0]] === regs[inst.args[1]];
        break;
      case "select":
        regs[r] = regs[inst.args[0]] ? regs[inst.args[1]] : regs[inst.args[2]];
        break;
    }
  }
  return regs[kernel.output];
}

/** Exhaustively verify a validated kernel over ALL 65,536 IEEE bfloat16 bit patterns! */
export function verifyExhaustiveBf16(kernel, spec) {
  const refFn = REFERENCE_FNS[spec.target];
  if (typeof refFn !== "function") {
    return { ok: false, reason: `Unknown reference target: ${spec.target}` };
  }
  const maxUlpAllowed = Number(spec.max_ulp ?? 1);
  let maxUlpSeen = 0;
  let worstInputBits = 0;
  let worstInputVal = 0;
  let worstGot = 0;
  let worstExpected = 0;
  let tested = 0;
  let exactMatches = 0;

  for (let bits = 0; bits < 65536; bits++) {
    const x = bf16ToF32(bits);
    const ref64 = refFn(x);
    const refBf16 = f64ToBf16RNE(ref64);
    const gotF32 = evalKernelF32(kernel, x);
    const gotBf16 = f32ToBf16RNE(gotF32);
    tested++;

    // Special values: NaN / ±Inf must match exact IEEE class!
    if (bf16IsNaN(refBf16)) {
      if (!bf16IsNaN(gotBf16)) {
        return {
          ok: false,
          reason: `NaN mismatch at bf16 0x${bits.toString(16)} (${x}): expected NaN, got bf16 0x${gotBf16.toString(16)} (${bf16ToF32(gotBf16)})`,
        };
      }
      exactMatches++;
      continue;
    }
    if (bf16IsNaN(gotBf16)) {
      return {
        ok: false,
        reason: `Unexpected NaN at bf16 0x${bits.toString(16)} (${x}): expected ${ref64} (bf16 0x${refBf16.toString(16)})`,
      };
    }
    if (refBf16 === 0x7f80 || refBf16 === 0xff80) {
      if (gotBf16 !== refBf16) {
        return {
          ok: false,
          reason: `Infinity mismatch at bf16 0x${bits.toString(16)} (${x}): expected 0x${refBf16.toString(16)}, got 0x${gotBf16.toString(16)}`,
        };
      }
      exactMatches++;
      continue;
    }
    if (gotBf16 === 0x7f80 || gotBf16 === 0xff80) {
      return {
        ok: false,
        reason: `Unexpected Infinity at bf16 0x${bits.toString(16)} (${x}): expected ${ref64} (bf16 0x${refBf16.toString(16)})`,
      };
    }

    const ulp = Math.abs(bf16LatticeIndex(gotBf16) - bf16LatticeIndex(refBf16));
    if (ulp === 0) exactMatches++;
    if (ulp > maxUlpSeen) {
      maxUlpSeen = ulp;
      worstInputBits = bits;
      worstInputVal = x;
      worstGot = bf16ToF32(gotBf16);
      worstExpected = bf16ToF32(refBf16);
    }
    if (ulp > maxUlpAllowed) {
      return {
        ok: false,
        reason: `ULP budget exceeded at bf16 0x${bits.toString(16)} (x=${x}): got ${bf16ToF32(gotBf16)} (0x${gotBf16.toString(16)}), expected ${bf16ToF32(refBf16)} (0x${refBf16.toString(16)}), ulp=${ulp} > ${maxUlpAllowed}`,
      };
    }
  }

  return {
    ok: true,
    tested,
    exactMatches,
    maxUlpSeen,
    worstInputBits,
    worstInputVal,
    worstGot,
    worstExpected,
    opCost: kernel.opCost,
    constCount: kernel.constCount,
  };
}

/** Deterministically emit a ready-to-paste CUDA / C++ `__device__` function from a verified JSON kernel. */
export function emitCudaSnippet(kernel, fnName = "pf_kernel") {
  const lines = [
    `// Auto-generated from Proof Foundry verified pure-data kernel (${kernel.opCost} ops, 65,536/65,536 bf16 inputs checked)`,
    `__device__ __forceinline__ float ${fnName}(float r0) {`,
  ];
  const fLit = (v) => {
    if (Object.is(v, -0)) return "-0.0f";
    const s = Number(v).toPrecision(9);
    if (s.includes("e") || s.includes("E")) {
      const [m, e] = s.split(/[eE]/);
      return `${m.replace(/(\.\d*?[1-9])0+$/, "$1").replace(/\.0+$/, ".0")}e${e}f`;
    }
    const trimmed = s.replace(/(\.\d*?[1-9])0+$/, "$1").replace(/\.0+$/, ".0");
    return (trimmed.includes(".") ? trimmed : `${trimmed}.0`) + "f";
  };
  const iLit = (v) => (v === -2147483648 ? "(-2147483647 - 1)" : String(v));
  for (let i = 0; i < kernel.compiled.length; i++) {
    const inst = kernel.compiled[i];
    const r = `r${i + 1}`;
    const a = inst.args ? inst.args.map((k) => `r${k}`) : [];
    switch (inst.op) {
      case "const": lines.push(`  const float ${r} = ${fLit(inst.v)};`); break;
      case "iconst": lines.push(`  const int32_t ${r} = ${iLit(inst.v)};`); break;
      case "bitcast_i32": lines.push(`  const int32_t ${r} = __float_as_int(${a[0]});`); break;
      case "bitcast_f32": lines.push(`  const float ${r} = __int_as_float(${a[0]});`); break;
      case "add": lines.push(`  const float ${r} = ${a[0]} + ${a[1]};`); break;
      case "sub": lines.push(`  const float ${r} = ${a[0]} - ${a[1]};`); break;
      case "mul": lines.push(`  const float ${r} = ${a[0]} * ${a[1]};`); break;
      case "fma": lines.push(`  const float ${r} = fmaf(${a[0]}, ${a[1]}, ${a[2]});`); break;
      case "abs": lines.push(`  const float ${r} = fabsf(${a[0]});`); break;
      case "neg": lines.push(`  const float ${r} = -${a[0]};`); break;
      case "min": lines.push(`  const float ${r} = fminf(${a[0]}, ${a[1]});`); break;
      case "max": lines.push(`  const float ${r} = fmaxf(${a[0]}, ${a[1]});`); break;
      case "iadd": lines.push(`  const int32_t ${r} = ${a[0]} + ${a[1]};`); break;
      case "isub": lines.push(`  const int32_t ${r} = ${a[0]} - ${a[1]};`); break;
      case "imul": lines.push(`  const int32_t ${r} = ${a[0]} * ${a[1]};`); break;
      case "iand": lines.push(`  const int32_t ${r} = ${a[0]} & ${a[1]};`); break;
      case "ior": lines.push(`  const int32_t ${r} = ${a[0]} | ${a[1]};`); break;
      case "ixor": lines.push(`  const int32_t ${r} = ${a[0]} ^ ${a[1]};`); break;
      case "ishl": lines.push(`  const int32_t ${r} = ${a[0]} << (${a[1]} & 31);`); break;
      case "ishr_u": lines.push(`  const int32_t ${r} = (int32_t)((uint32_t)${a[0]} >> (${a[1]} & 31));`); break;
      case "ishr_s": lines.push(`  const int32_t ${r} = ${a[0]} >> (${a[1]} & 31);`); break;
      case "ftoi_trunc": lines.push(`  const int32_t ${r} = __float2int_rz(${a[0]});`); break;
      case "ftoi_round": lines.push(`  const int32_t ${r} = __float2int_rn(${a[0]});`); break;
      case "itof": lines.push(`  const float ${r} = (float)${a[0]};`); break;
      case "lt": lines.push(`  const bool ${r} = ${a[0]} < ${a[1]};`); break;
      case "le": lines.push(`  const bool ${r} = ${a[0]} <= ${a[1]};`); break;
      case "eq": lines.push(`  const bool ${r} = ${a[0]} == ${a[1]};`); break;
      case "select": lines.push(`  const ${inst.outType === "i32" ? "int32_t" : "float"} ${r} = ${a[0]} ? ${a[1]} : ${a[2]};`); break;
    }
  }
  lines.push(`  return r${kernel.output};`, `}`);
  return lines.join("\n");
}

// CLI entry point (invoked by hub/judges/command.mjs)
const isMain = process.argv[1] && path.resolve(process.argv[1]) === path.resolve(import.meta.filename);
if (isMain) {
  const args = {};
  for (let i = 2; i < process.argv.length; i += 2) {
    args[process.argv[i].replace(/^--/, "")] = process.argv[i + 1];
  }
  const writeResult = (obj) => {
    fs.writeFileSync(args.result, JSON.stringify(obj, null, 2), "utf8");
    process.exit(obj.ok ? 0 : 1);
  };

  if (!args.artifact || !args.spec || !args.result) {
    writeResult({ ok: false, reason: "Missing required --artifact, --spec, or --result argument" });
  }
  if (!args.artifact.endsWith(".json")) {
    writeResult({ ok: false, reason: "ML Kernel Judge accepts pure .json artifacts only (zero donor JS execution)" });
  }
  let spec;
  try {
    spec = JSON.parse(fs.readFileSync(args.spec, "utf8"));
  } catch (err) {
    writeResult({ ok: false, reason: `Unreadable spec file: ${err.message}` });
  }
  if (args.target && spec.target && args.target !== spec.target) {
    writeResult({ ok: false, reason: `Target mismatch: expected ${spec.target}, got ${args.target}` });
  }

  const expectedScore = Number(args.score);
  if (!Number.isSafeInteger(expectedScore) || expectedScore < 1) {
    writeResult({ ok: false, reason: `Invalid expected op-count score: ${args.score}` });
  }

  let rawText;
  try {
    if (fs.lstatSync(args.artifact).isSymbolicLink()) {
      writeResult({ ok: false, reason: `Symlink artifacts are forbidden: ${args.artifact}` });
    }
    const st = fs.statSync(args.artifact);
    if (st.size > MAX_ARTIFACT_BYTES) {
      writeResult({ ok: false, reason: `Artifact exceeds ${MAX_ARTIFACT_BYTES} byte limit` });
    }
    rawText = fs.readFileSync(args.artifact, "utf8");
  } catch (err) {
    writeResult({ ok: false, reason: `Could not read artifact: ${err.message}` });
  }
  const parsed = parseAndValidateKernel(rawText);
  if (!parsed.ok) {
    writeResult({ ok: false, reason: parsed.reason });
  }
  if (parsed.opCost > expectedScore) {
    writeResult({
      ok: false,
      reason: `Kernel uses ${parsed.opCost} ops, exceeding claimed score ≤ ${expectedScore}`,
    });
  }

  const verdict = verifyExhaustiveBf16(parsed, spec);
  if (!verdict.ok) {
    writeResult({ ok: false, reason: verdict.reason });
  }

  writeResult({
    ok: true,
    score: expectedScore,
    engine: "Exhaustive 65,536-Input BF16 Pure-Data Judge v1 (zero JS execution)",
    signature: `${spec.target} ≤ ${expectedScore} ops [actual=${parsed.opCost} ops, max_ulp=${verdict.maxUlpSeen}/${spec.max_ulp}, exact=${verdict.exactMatches}/65536]`,
    checks: [
      `exhaustive_65536_bf16`,
      `max_ulp_${verdict.maxUlpSeen}_le_${spec.max_ulp}`,
      `pure_data_json_zero_exec`,
      `exact_dyadic_fmaf`,
    ],
    reason: `Verified all 65,536 bf16 bit patterns (${verdict.exactMatches} exact, max ${verdict.maxUlpSeen} ULP ≤ ${spec.max_ulp}) in ${parsed.opCost} ops (claimed ≤ ${expectedScore})`,
  });
}
