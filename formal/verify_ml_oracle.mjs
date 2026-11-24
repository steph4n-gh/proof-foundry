#!/usr/bin/env node
/**
 * formal/verify_ml_oracle.mjs — Track 3 Formal Verification Differential Harness for `ml-math-kernels`.
 *
 * 1. Builds `formal/oracle` (`PFOracle.BF16Oracle` + `PFOracle.AxiomCheck` + `pf_oracle_check`)
 *    under Lean 4.36.0 `--wfail` (zero `sorry`, standard axioms only, 27 audited theorems).
 * 2. Exhaustively cross-checks ALL 65,536/65,536 IEEE `bfloat16` bit patterns bit-for-bit
 *    against `missions/ml-math-kernels/judge/verify.mjs` (`bf16ToF32`, `f32ToBf16RNE`,
 *    `f64ToBf16RNE`, `bf16LatticeIndex`, `bf16IsNaN`).
 * 3. Cross-checks adversarial `f32ToBf16RNE`, `f64ToBf16RNE` (including double-rounding traps,
 *    subnormal-to-normal carries, overflow-to-Inf, signed zeros, NaN payloads), `fmafExact`
 *    (catastrophic cancellation, exact ties to even/odd, subnormals, signed zero), and
 *    UB-free 32-bit `ishr_s` equivalence.
 * 4. Verifies all 3 committed pure-data ML kernels via the CLI judge.
 * 5. Runs 4 negative mutation self-checks proving the harness catches broken RNE ties,
 *    broken double-rounding, broken `-0` lattice index, and non-fused `fmaf`.
 */
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import * as judge from "../missions/ml-math-kernels/judge/verify.mjs";

const formalDir = fileURLToPath(new URL(".", import.meta.url));
const leanDir = join(formalDir, "oracle");
const missionDir = join(formalDir, "../missions/ml-math-kernels");
const judgePath = join(missionDir, "judge/verify.mjs");
const judgeSource = readFileSync(judgePath, "utf8");

const _buf8 = new ArrayBuffer(8);
const _f64 = new Float64Array(_buf8);
const _u64 = new BigUint64Array(_buf8);
function f64ToU64(x) {
  _f64[0] = x;
  return _u64[0];
}
function u64ToF64(u) {
  _u64[0] = BigInt(u);
  return _f64[0];
}

function buildLean() {
  const elanLake = join(homedir(), ".elan/bin/lake");
  const lake = existsSync(elanLake) ? elanLake : "lake";
  const manifest = join(leanDir, "lake-manifest.json");
  const alreadyHadManifest = existsSync(manifest);
  try {
    const output = execFileSync(lake, ["build", "--wfail", "--no-ansi"], {
      cwd: leanDir,
      encoding: "utf8",
    });
    console.log(output.trim());
  } finally {
    if (!alreadyHadManifest) rmSync(manifest, { force: true });
  }
}

function runLean(requests) {
  const input = requests.map((r) => JSON.stringify(r)).join("\n") + "\n";
  const output = execFileSync(join(leanDir, ".lake/build/bin/pf_oracle_check"), [], {
    input,
    encoding: "utf8",
    maxBuffer: 32 * 1024 * 1024,
  });
  const results = output.trimEnd().split("\n").map((line) => JSON.parse(line));
  assert.equal(results.length, requests.length, "Lean response count");
  return results;
}

async function withMutatedJudge(before, after, fn) {
  const parts = judgeSource.split(before);
  assert.equal(parts.length, 2, `Expected one occurrence of mutant target in verify.mjs`);
  const dir = mkdtempSync(join(tmpdir(), "pf-ml-mutant-"));
  try {
    const file = join(dir, "verify_mutant.mjs");
    writeFileSync(file, parts.join(after), "utf8");
    const mod = await import(pathToFileURL(file).href);
    return await fn(mod);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

buildLean();

// 1. Exhaustive 65,536/65,536 BF16 sweep
const [sweep] = runLean([{ op: "allBf16Sweep" }]);
assert.equal(sweep.f32Bits.length, 65536);
for (let b = 0; b < 65536; b++) {
  const x = judge.bf16ToF32(b);
  if (sweep.isNaN[b]) {
    // IEEE-754 hardware quietens signaling NaNs when widening float32 -> JS float64 Number.
    assert.equal(Number.isNaN(x), true, `bf16ToF32 NaN mismatch at 0x${b.toString(16)}`);
  } else {
    assert.equal(judge.f32ToU32(x), sweep.f32Bits[b], `bf16ToF32 mismatch at 0x${b.toString(16)}`);
  }
  assert.equal(judge.f32ToBf16RNE(x), sweep.rne32[b], `f32ToBf16RNE mismatch at 0x${b.toString(16)}`);
  assert.equal(judge.bf16LatticeIndex(b), sweep.lattice[b], `bf16LatticeIndex mismatch at 0x${b.toString(16)}`);
  assert.equal(judge.bf16IsNaN(b), sweep.isNaN[b], `bf16IsNaN mismatch at 0x${b.toString(16)}`);
}
console.log("Exhaustive BF16 bit-for-bit sweep: 65,536/65,536 (bf16ToF32, f32ToBf16RNE, bf16LatticeIndex, bf16IsNaN)");

// 2. Adversarial float32 -> bf16, float64 -> bf16 (including double-rounding traps), fmafExact, and cppIshrS cases
const requests = [];
const expected = [];
const labels = [];
function check(req, exp, label) {
  requests.push(req);
  expected.push(exp);
  labels.push(label);
}

// 2a. Adversarial f32 -> bf16 RNE cases (halfway ties to even vs odd, subnormals, overflow to Inf, NaN payloads)
const f32Patterns = [
  0x00000000, 0x80000000, 0x00000001, 0x00007fff, 0x00008000, 0x00008001,
  0x00018000, 0x00018001, 0x007f7fff, 0x007f8000, 0x007fffff, // subnormal->normal carry
  0x3f800000, 0x3f807fff, 0x3f808000, 0x3f808001, 0x3f818000, 0x3f817fff,
  0xbf808000, 0xbf818000, 0x7f7f7fff, 0x7f7f8000, 0x7f7fffff, // max finite -> Inf overflow
  0xff7f7fff, 0xff7f8000, 0xff7fffff,
  0x7f800000, 0xff800000, 0x7f800001, 0x7fc00000, 0xffffffff, // Inf & NaN payloads
];
// Add deterministic PRNG coverage across all float32 bit classes
let rng = 0x9e3779b9;
function nextU32() {
  rng = (Math.imul(rng ^ (rng >>> 15), 0x85ebca6b) + 0xc2b2ae35) >>> 0;
  return rng;
}
for (let i = 0; i < 512; i++) f32Patterns.push(nextU32());
for (const [i, u] of f32Patterns.entries()) {
  const x = judge.u32ToF32(u);
  check({ op: "f32ToBf16RNE", u: String(u >>> 0) }, judge.f32ToBf16RNE(x), `f32ToBf16RNE #${i} (0x${(u >>> 0).toString(16)})`);
}

// 2b. Adversarial f64 -> bf16 RNE cases (including DOUBLE-ROUNDING TRAPS where f64 -> f32 -> bf16 is WRONG!)
// Example double-rounding trap: 1.0 + 2^-8 - 2^-35:
//   - Nearest f32 rounds UP to 1.0 + 2^-8 (exact halfway to bf16), then f32->bf16 ties-to-even (stays or rounds up!).
//   - For odd LSB (1 + 2^-7) + 2^-8 - 2^-35: f64->f32 rounds UP to exact halfway (1 + 2^-7 + 2^-8), then f32->bf16 rounds UP to 1 + 2*2^-7 (WRONG!),
//     whereas true f64->bf16 rounds DOWN to 1 + 2^-7!
const doubleRoundingTrap = (1 + 2 ** -7) + 2 ** -8 - 2 ** -35;
assert.notEqual(
  judge.f32ToBf16RNE(Math.fround(doubleRoundingTrap)),
  judge.f64ToBf16RNE(doubleRoundingTrap),
  "Sanity: doubleRoundingTrap must distinguish f64->f32->bf16 from exact f64->bf16"
);
const f64Values = [
  0, -0, Infinity, -Infinity, NaN,
  doubleRoundingTrap, -doubleRoundingTrap,
  (1 + 2 ** -7) + 2 ** -8, (1 + 2 ** -7) + 2 ** -8 + 2 ** -52,
  1.0 + 2 ** -8, 1.0 + 2 ** -8 + 2 ** -52, 1.0 + 2 ** -8 - 2 ** -52,
  2 ** -134, 2 ** -134 + 2 ** -180, 2 ** -134 - 2 ** -180,
  2 ** -133, 1.5 * 2 ** -133, 2.5 * 2 ** -133,
  127.5 * 2 ** -133, 127.5 * 2 ** -133 - 2 ** -170, // subnormal->normal boundary
  2 ** -126, 2 ** -127, 2 ** -140, 2 ** -1022, Number.MIN_VALUE, -Number.MIN_VALUE,
  (2 - 2 ** -7) * 2 ** 127, (2 - 2 ** -8) * 2 ** 127, (2 - 2 ** -8) * 2 ** 127 - 2 ** 90, // overflow boundary
  Number.MAX_VALUE, -Number.MAX_VALUE,
  Math.PI, -Math.E, Math.SQRT2, Math.SQRT1_2,
];
// Also test every single finite bf16 promoted to f64 (spot sample across all exponents + subnormals)
for (let b = 0; b < 65536; b += 63) f64Values.push(judge.bf16ToF32(b));
for (const [i, x] of f64Values.entries()) {
  const u64 = f64ToU64(x);
  check({ op: "f64ToBf16RNE", u: u64.toString() }, judge.f64ToBf16RNE(x), `f64ToBf16RNE #${i} (${x})`);
}

// 2c. Adversarial single-rounding float32 FMA (`fmafExact`) cases
const fmaTriples = [
  [Math.fround(1 + 2 ** -23), Math.fround(1 - 2 ** -23), -1.0], // exact -2^-46 cancellation trap!
  [Math.fround(1 + 2 ** -22), Math.fround(1 - 2 ** -22), -1.0],
  [Math.fround(1 + 2 ** -12), Math.fround(1 - 2 ** -12), -1.0],
  [Math.fround(2 ** -75), Math.fround(2 ** -74), Math.fround(2 ** -149)], // subnormal product + subnormal
  [Math.fround(2 ** -80), Math.fround(2 ** -80), Math.fround(2 ** -149)],
  [Math.fround(2 ** 100), Math.fround(2 ** 50), Math.fround(-(2 ** 127))], // overflow product + finite
  [Math.fround(2 ** 64), Math.fround(2 ** 64), Math.fround(-(2 ** 127))],
  [0.0, 5.0, -0.0], [-0.0, 5.0, -0.0], [-0.0, 5.0, 0.0], [1.0, -1.0, 1.0],
  [Math.fround(1.5), Math.fround(2.5), Math.fround(-3.75)], // exact cancellation -> +0
  [Math.fround(-1.5), Math.fround(2.5), Math.fround(3.75)],
  [Math.fround(1.0), Math.fround(2 ** -24), Math.fround(2 ** -25)], // tie-breaking
  [Math.fround(1 + 2 ** -23), Math.fround(1.0), Math.fround(2 ** -24)], // tie to even (odd LSB)
  [Math.fround(1.0), Math.fround(1.0), Math.fround(2 ** -24)], // tie to even (even LSB)
];
for (let i = 0; i < 128; i++) {
  const a = judge.bf16ToF32(nextU32() & 0xffff);
  const b = judge.bf16ToF32(nextU32() & 0xffff);
  const c = judge.bf16ToF32(nextU32() & 0xffff);
  if (Number.isFinite(a) && Number.isFinite(b) && Number.isFinite(c)) {
    fmaTriples.push([a, b, c]);
  }
}
for (const [i, [a, b, c]] of fmaTriples.entries()) {
  const ua = judge.f32ToU32(a);
  const ub = judge.f32ToU32(b);
  const uc = judge.f32ToU32(c);
  const got = judge.f32ToU32(judge.fmafExact(a, b, c));
  check({ op: "fmafFiniteBits", a: String(ua), b: String(ub), c: String(uc) }, got, `fmafExact #${i}`);
}

// 2d. UB-free C++ `ishr_s` equivalence cases against JS `>>`
const shiftPairs = [
  [0, 0], [-1, 0], [-1, 1], [-1, 31], [-1, 32], [-2147483648, 0], [-2147483648, 1],
  [-2147483648, 31], [-2147483648, 33], [2147483647, 0], [2147483647, 1], [2147483647, 31],
  [-123456789, 7], [123456789, 7], [-2147483648, -1], [0x55555555, 16],
];
for (let i = 0; i < 64; i++) shiftPairs.push([nextU32() | 0, nextU32() | 0]);
for (const [i, [a, b]] of shiftPairs.entries()) {
  const jsOut = (a >> (b & 31)) >>> 0;
  check({ op: "cppIshrS", a: String(a >>> 0), b: String(b >>> 0) }, jsOut, `cppIshrS #${i}`);
}

const results = runLean(requests);
for (let i = 0; i < results.length; i++) {
  assert.equal(results[i], expected[i], `Differential mismatch on ${labels[i]}: Lean=${results[i]} JS=${expected[i]}`);
}
console.log(
  `Adversarial differential checks: ${f32Patterns.length} f32->bf16 + ${f64Values.length} f64->bf16 + ${fmaTriples.length} fmafExact + ${shiftPairs.length} cppIshrS = ${results.length}/${results.length} exact matches`
);

// 3. Certify all 3 committed pure-data ML kernels via the CLI judge
const committed = [
  ["artifacts/ML_rec_bf16_rsqrt_s17.json", "specs/ML_rec_bf16_rsqrt.json", "bf16_rsqrt", 17],
  ["artifacts/ML_rec_bf16_exp2_s18.json", "specs/ML_rec_bf16_exp2.json", "bf16_exp2", 18],
  ["artifacts/ML_rec_bf16_silu_s31.json", "specs/ML_rec_bf16_silu.json", "bf16_silu", 31],
];
const tmpDir = mkdtempSync(join(tmpdir(), "pf-ml-oracle-"));
try {
  for (const [artRel, specRel, target, score] of committed) {
    const outPath = join(tmpDir, `${target}.json`);
    execFileSync(process.execPath, [
      judgePath, "--artifact", join(missionDir, artRel), "--target", target,
      "--result", outPath, "--score", String(score), "--spec", join(missionDir, specRel),
    ]);
    const verdict = JSON.parse(readFileSync(outPath, "utf8"));
    assert.equal(verdict.ok, true, `${target} CLI verdict failed`);
    assert.equal(verdict.score, score, `${target} score mismatch`);
  }
} finally {
  rmSync(tmpDir, { recursive: true, force: true });
}
console.log("Committed ML kernels certified via CLI judge: rsqrt(17), exp2(18), silu(31)");

// 4. Negative mutation self-checks (proving the differential oracle catches real bugs!)
{
  // Mutant 1: break ties-to-even in f32ToBf16RNE (always round half up)
  await withMutatedJudge("const roundingBias = (0x7fff + lsb) >>> 0;", "const roundingBias = 0x8000 >>> 0;", (m1) => {
    const [leanHalfEven] = runLean([{ op: "f32ToBf16RNE", u: String(0x3f808000) }]);
    assert.notEqual(m1.f32ToBf16RNE(judge.u32ToF32(0x3f808000)), leanHalfEven, "Mutant 1 (broken f32 ties-to-even) not caught!");
  });

  // Mutant 2: introduce double rounding in f64ToBf16RNE via Math.fround
  await withMutatedJudge("export function f64ToBf16RNE(x) {", "export function f64ToBf16RNE(x) { return f32ToBf16RNE(Math.fround(x));", (m2) => {
    const [leanTrap] = runLean([{ op: "f64ToBf16RNE", u: f64ToU64(doubleRoundingTrap).toString() }]);
    assert.notEqual(m2.f64ToBf16RNE(doubleRoundingTrap), leanTrap, "Mutant 2 (double rounding in f64ToBf16RNE) not caught!");
  });

  // Mutant 3: break -0 lattice equivalence in bf16LatticeIndex
  await withMutatedJudge("if (b === 0x0000 || b === 0x8000) return 0;", "if (b === 0x0000) return 0;", (m3) => {
    assert.notEqual(m3.bf16LatticeIndex(0x8000), sweep.lattice[0x8000], "Mutant 3 (broken -0 lattice index) not caught!");
  });

  // Mutant 4: replace fused single-rounding fmafExact with unfused float32 mul+add
  await withMutatedJudge("export function fmafExact(a, b, c) {", "export function fmafExact(a, b, c) { return Math.fround(Math.fround(a * b) + c);", (m4) => {
    const a = Math.fround(1 + 2 ** -23);
    const b = Math.fround(1 - 2 ** -23);
    const [leanFma] = runLean([{ op: "fmafFiniteBits", a: String(judge.f32ToU32(a)), b: String(judge.f32ToU32(b)), c: String(judge.f32ToU32(-1.0)) }]);
    assert.notEqual(judge.f32ToU32(m4.fmafExact(a, b, -1.0)), leanFma, "Mutant 4 (unfused fmaf) not caught!");
  });
}
console.log("Negative mutation self-checks: 4/4 mutants caught (f32 RNE ties, f64 double-rounding, -0 lattice, unfused fmaf)");
console.log("ALL ML-MATH-KERNELS FORMAL ORACLE CHECKS PASSED!");
