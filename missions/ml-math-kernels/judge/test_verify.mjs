#!/usr/bin/env node
/**
 * Unit & adversarial security tests for `missions/ml-math-kernels/judge/verify.mjs`.
 * Proves:
 *  - Exact IEEE bfloat16 conversion & roundtrip across all 65,536 bit patterns
 *  - Exact single-rounding float32 FMA (`fmafExact`) vs double-rounding traps
 *  - 15-digit float64 `erfExact64` accuracy against exact mathematical reference values
 *  - Exhaustive 65,536-input verification of committed pure-data JSON kernels
 *  - Deterministic CUDA `__device__` drop-in code generation (no scientific-notation bugs)
 *  - Security rejection of JS code, disallowed ops (div/sqrt/exp), out-of-range regs,
 *    type mismatches, over-budget op counts, and NaN/Inf-violating kernels.
 */
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {
  bf16ToF32,
  bf16IsNaN,
  f32ToBf16RNE,
  f64ToBf16RNE,
  fmafExact,
  erfExact64,
  parseAndValidateKernel,
  verifyExhaustiveBf16,
  emitCudaSnippet,
} from "./verify.mjs";

const MISSION_DIR = path.resolve(import.meta.dirname, "..");

let passed = 0;
function test(name, fn) {
  fn();
  passed++;
  console.log(`  PASS: ${name}`);
}

console.log("Running ml-math-kernels pure-data Judge test suite…");

test("bf16 <-> f32 <-> f64 RNE roundtrip across all 65,536 bit patterns", () => {
  for (let b = 0; b < 65536; b++) {
    const f32 = bf16ToF32(b);
    const r32 = f32ToBf16RNE(f32);
    const r64 = f64ToBf16RNE(f32);
    if (bf16IsNaN(b)) {
      assert.equal(r32, 0x7fc0, `f32 NaN canonicalization failed for 0x${b.toString(16)}`);
      assert.equal(r64, 0x7fc0, `f64 NaN canonicalization failed for 0x${b.toString(16)}`);
    } else {
      assert.equal(r32, b, `f32 roundtrip mismatch for 0x${b.toString(16)}`);
      assert.equal(r64, b, `f64 roundtrip mismatch for 0x${b.toString(16)}`);
    }
  }
});

test("fmafExact avoids float32 double-rounding cancellation", () => {
  // (1 + 2^-23) * (1 - 2^-23) - 1 = -2^-46 exactly.
  // Unfused float32 rounds product to 1.0, yielding 0.0; true fmaf returns -2^-46!
  const a = Math.fround(1 + 2 ** -23);
  const b = Math.fround(1 - 2 ** -23);
  const unfused = Math.fround(Math.fround(a * b) - 1.0);
  const fused = fmafExact(a, b, -1.0);
  assert.equal(unfused, 0, "sanity: unfused float32 cancels to 0");
  assert.equal(fused, Math.fround(-(2 ** -46)), "fmafExact must preserve exact -2^-46");
  assert.equal(fmafExact(2.0, 3.0, 4.0), 10.0);
  assert.ok(Number.isNaN(fmafExact(Infinity, 0.0, 1.0)));
});

test("erfExact64 achieves < 1e-15 accuracy on standard checkpoints", () => {
  const refs = [
    [0.0, 0.0],
    [0.5, 0.5204998778130465],
    [1.0, 0.8427007929497149],
    [2.0, 0.9953222650189527],
    [2.5, 0.999593047982555],
    [3.0, 0.9999779095030014],
    [-1.0, -0.8427007929497149],
  ];
  for (const [x, expected] of refs) {
    const got = erfExact64(x);
    assert.ok(Math.abs(got - expected) < 1e-15, `erf(${x}) got=${got} expected=${expected}`);
  }
  assert.equal(erfExact64(Infinity), 1);
  assert.equal(erfExact64(-Infinity), -1);
  assert.ok(Number.isNaN(erfExact64(NaN)));
});

test("committed pure-data JSON kernels pass exhaustive 65,536-input check", () => {
  const cases = [
    ["artifacts/ML_rec_bf16_rsqrt_s17.json", "specs/ML_rec_bf16_rsqrt.json", 17],
    ["artifacts/ML_rec_bf16_exp2_s18.json", "specs/ML_rec_bf16_exp2.json", 18],
    ["artifacts/ML_rec_bf16_silu_s31.json", "specs/ML_rec_bf16_silu.json", 31],
  ];
  for (const [artRel, specRel, expectedOps] of cases) {
    const raw = fs.readFileSync(path.join(MISSION_DIR, artRel), "utf8");
    const spec = JSON.parse(fs.readFileSync(path.join(MISSION_DIR, specRel), "utf8"));
    const parsed = parseAndValidateKernel(raw);
    assert.equal(parsed.ok, true, `${artRel}: ${parsed.reason}`);
    assert.equal(parsed.opCost, expectedOps, `${artRel} opCost`);
    const v = verifyExhaustiveBf16(parsed, spec);
    assert.equal(v.ok, true, `${artRel} verify failed: ${v.reason}`);
    assert.equal(v.tested, 65536);
    assert.ok(v.maxUlpSeen <= spec.max_ulp);
    const cuda = emitCudaSnippet(parsed, `pf_${spec.target}`);
    assert.ok(cuda.includes(`__device__ __forceinline__ float pf_${spec.target}(float r0)`));
    assert.ok(!/e[+-]\df/.test(cuda.replace(/e-38f/g, "")), "scientific notation exponents must stay intact");
  }
});

test("emitCudaSnippet formats scientific notation and INT32_MIN safely", () => {
  const k = parseAndValidateKernel(JSON.stringify({
    schema: "pf.mlkernel.v1",
    ops: [
      ["const", 1e-10],
      ["iconst", -2147483648],
      ["add", 0, 1],
    ],
    output: 3,
  }));
  assert.equal(k.ok, true);
  const cuda = emitCudaSnippet(k, "pf_test");
  assert.ok(cuda.includes("1e-10f") || cuda.includes("1.0e-10f"), `bad float literal in:\n${cuda}`);
  assert.ok(cuda.includes("(-2147483647 - 1)"), `INT32_MIN not guarded in:\n${cuda}`);
});

test("security: rejects JavaScript code, disallowed ops, bad registers, type mismatches", () => {
  const badInputs = [
    "export const kernel = (x) => Math.exp(x);",
    JSON.stringify({ schema: "wrong.v1", ops: [["const", 1]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["div", 0, 0]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["sqrt", 0]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["add", 0, 99]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["iconst", 1], ["add", 0, 1]], output: 2 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["iconst", 1]], output: 1 }),
  ];
  for (const raw of badInputs) {
    const res = parseAndValidateKernel(raw);
    assert.equal(res.ok, false, `must reject malicious/malformed input: ${raw}`);
  }
});

test("adversarial: rejects kernel that drops NaN propagation on exp2", () => {
  // Clamp x without NaN guard: fminf/fmaxf turns NaN into 128.0!
  const k = parseAndValidateKernel(JSON.stringify({
    schema: "pf.mlkernel.v1",
    ops: [
      ["const", 1.0],
      ["max", 0, 1],
    ],
    output: 2,
  }));
  assert.equal(k.ok, true);
  const v = verifyExhaustiveBf16(k, { target: "bf16_exp2", max_ulp: 1 });
  assert.equal(v.ok, false, "must reject kernel that fails NaN or ULP checks");
});

console.log(`ALL ${passed} ml-math-kernels Judge tests PASSED.`);
