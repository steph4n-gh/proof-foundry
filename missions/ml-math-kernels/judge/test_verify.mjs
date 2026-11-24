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
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { extractDropInArtifact } from "../../../hub/export_dropin.mjs";
import {
  bf16ToF32,
  bf16IsNaN,
  f32ToBf16RNE,
  f64ToBf16RNE,
  fmafExact,
  erfExact64,
  erfcExact64,
  REFERENCE_FNS,
  parseAndValidateKernel,
  evalKernelF32,
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

test("erfcExact64 & bf16_gelu preserve negative-tail precision without cancellation", () => {
  // Exact negative-tail checkpoints verified against Python IEEE float64 math.erfc:
  // x = -8 -> gelu(-8) = -4.976768459417456e-15 (bf16 0xa7b3)
  // x = -9 -> gelu(-9) = -1.0157295653584581e-18 (bf16 0xa196; old 1+erf gave -0 = 0x8000!)
  // x = -12 -> gelu(-12) = -2.1317785344932418e-32 (bf16 0x8add)
  // x = -13.5 -> gelu(-13.5) = -1.0555389862638368e-40 (bf16 0x8001, smallest negative subnormal!)
  const geluM8 = REFERENCE_FNS.bf16_gelu(-8);
  const geluM9 = REFERENCE_FNS.bf16_gelu(-9);
  const geluM12 = REFERENCE_FNS.bf16_gelu(-12);
  const geluM135 = REFERENCE_FNS.bf16_gelu(-13.5);
  assert.ok(Math.abs(geluM8 - (-4.976768459417456e-15)) / 4.976768459417456e-15 < 1e-12, `gelu(-8)=${geluM8}`);
  assert.ok(Math.abs(geluM9 - (-1.0157295653584581e-18)) / 1.0157295653584581e-18 < 1e-12, `gelu(-9)=${geluM9}`);
  assert.ok(Math.abs(geluM12 - (-2.1317785344932418e-32)) / 2.1317785344932418e-32 < 1e-12, `gelu(-12)=${geluM12}`);
  assert.ok(Math.abs(geluM135 - (-1.0555389862638368e-40)) / 1.0555389862638368e-40 < 1e-12, `gelu(-13.5)=${geluM135}`);
  assert.equal(f64ToBf16RNE(geluM8), 0xa7b3);
  assert.equal(f64ToBf16RNE(geluM9), 0xa196, "bf16_gelu(-9) must round to 0xa196, not -0");
  assert.equal(f64ToBf16RNE(geluM12), 0x8add);
  assert.equal(f64ToBf16RNE(geluM135), 0x8001);
  assert.equal(erfcExact64(0), 1);
  assert.equal(erfcExact64(Infinity), 0);
  assert.equal(erfcExact64(-Infinity), 2);
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

test("emitCudaSnippet formats scientific notation, -0 underflow, and INT32_MIN safely", () => {
  const raw = JSON.stringify({
    schema: "pf.mlkernel.v1",
    ops: [
      ["const", 1e-10],
      ["const", -1e-46],
      ["iconst", -2147483648],
      ["add", 0, 1],
    ],
    output: 4,
  });
  const k = parseAndValidateKernel(raw);
  assert.equal(k.ok, true);
  const cuda = emitCudaSnippet(k, "pf_test");
  const dropIn = extractDropInArtifact("ml-math-kernels", { id: "ML-test" }, raw);
  assert.ok(cuda.includes("1e-10f") || cuda.includes("1.0e-10f"), `bad float literal in:\n${cuda}`);
  assert.ok(cuda.includes("const float r2 = -0.0f;"), `-1e-46 must emit -0.0f in verify.mjs:\n${cuda}`);
  assert.ok(dropIn.code.includes("const float r2 = -0.0f;"), `-1e-46 must emit -0.0f in export_dropin.mjs:\n${dropIn.code}`);
  assert.ok(cuda.includes("(-2147483647 - 1)"), `INT32_MIN not guarded in:\n${cuda}`);
});

test("security: rejects JavaScript code, float32-overflow const, bad max_ulp, disallowed ops, bad registers, type mismatches", () => {
  const badInputs = [
    "export const kernel = (x) => Math.exp(x);",
    JSON.stringify({ schema: "wrong.v1", ops: [["const", 1]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 1e300]], output: 1 }),
    JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 1e39]], output: 1 }),
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
  const okK = parseAndValidateKernel(JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 1.0]], output: 1 }));
  assert.equal(verifyExhaustiveBf16(okK, { target: "bf16_exp2", max_ulp: "not-a-number" }).ok, false);
  assert.equal(verifyExhaustiveBf16(okK, { target: "bf16_exp2", max_ulp: -1 }).ok, false);
  // Signed-zero min/max parity with IEEE/CUDA fminf/fmaxf
  const minK = parseAndValidateKernel(JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 0.0], ["min", 0, 1]], output: 2 }));
  const maxK = parseAndValidateKernel(JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 0.0], ["max", 0, 1]], output: 2 }));
  assert.equal(Object.is(evalKernelF32(minK, -0.0), -0.0), true, "min(-0, +0) must be -0");
  assert.equal(Object.is(evalKernelF32(maxK, -0.0), 0.0), true, "max(-0, +0) must be +0");
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

test("drop-in CUDA/C++ emitters use UB-free unsigned 32-bit wrapping and match JS interpreter on all 65,536 bf16 inputs under UBSan", () => {
  const cases = [
    { id: "ML-rec-bf16-exp2", fn: "pf_bf16_exp2", raw: fs.readFileSync(path.join(MISSION_DIR, "artifacts/ML_rec_bf16_exp2_s18.json"), "utf8") },
    { id: "ML-rec-bf16-rsqrt", fn: "pf_bf16_rsqrt", raw: fs.readFileSync(path.join(MISSION_DIR, "artifacts/ML_rec_bf16_rsqrt_s17.json"), "utf8") },
    { id: "ML-rec-bf16-silu", fn: "pf_bf16_silu", raw: fs.readFileSync(path.join(MISSION_DIR, "artifacts/ML_rec_bf16_silu_s31.json"), "utf8") },
    // Adversarial synthetic kernels exercising out-of-range/nonfinite ftoi_trunc, ftoi_round, and signed-zero min/bitcast!
    { id: "ML-adv-ftoi-trunc", fn: "pf_ml_adv_ftoi_trunc", raw: JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["ftoi_trunc", 0], ["itof", 1]], output: 2 }) },
    { id: "ML-adv-ftoi-round", fn: "pf_ml_adv_ftoi_round", raw: JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["ftoi_round", 0], ["itof", 1]], output: 2 }) },
    { id: "ML-adv-min-s0", fn: "pf_ml_adv_min_s0", raw: JSON.stringify({ schema: "pf.mlkernel.v1", ops: [["const", 0.0], ["min", 0, 1], ["bitcast_i32", 2], ["itof", 3]], output: 4 }) },
  ];
  const snippets = [];
  const parsedMap = [];
  for (const c of cases) {
    const raw = c.raw;
    const parsed = parseAndValidateKernel(raw);
    assert.equal(parsed.ok, true);
    const fromVerify = emitCudaSnippet(parsed, c.fn);
    const fromDropIn = extractDropInArtifact("ml-math-kernels", { id: c.id }, raw);
    assert.ok(fromDropIn && fromDropIn.code, `extractDropInArtifact failed for ${c.id}`);
    // Strip the first comment line and verify both emitters produce byte-identical bodies!
    const bodyA = fromVerify.split("\n").slice(1).join("\n");
    const bodyB = fromDropIn.code.split("\n").slice(1).join("\n");
    assert.equal(bodyA, bodyB, `emitCudaSnippet and extractDropInArtifact diverged on ${c.id}`);
    assert.ok(!/const int32_t r\d+ = r\d+ [+\-*<<>>]/.test(bodyA), `raw signed int32_t op found in ${c.id}:\n${bodyA}`);
    snippets.push(bodyB);
    parsedMap.push({ ...c, parsed });
  }

  // Compile and run all 6 emitted functions under UBSan across all 65,536 bf16 bit patterns.
  const cxx = ["c++", "clang++", "g++"].find((bin) => spawnSync(bin, ["--version"], { encoding: "utf8" }).status === 0);
  if (!cxx) {
    console.log("  SKIP: no C++ compiler available for UBSan execution check");
    return;
  }
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pf-ml-ubsan-"));
  try {
    const cppPath = path.join(tmpDir, "check.cpp");
    const binPath = path.join(tmpDir, "check");
    const cpp = `
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cfenv>

#define __device__
#define __forceinline__ inline

// CUDA PTX min.f32 / max.f32 return the non-NaN operand for ALL NaNs (both qNaN and sNaN),
// whereas ARM64 C++ std::fminf (fminnm) propagates sNaN. Keep std::fminf/std::fmaxf for finite/±0!
static inline float pf_ptx_fminf(float a, float b) {
  if (std::isnan(a)) return b;
  if (std::isnan(b)) return a;
  return std::fminf(a, b);
}
static inline float pf_ptx_fmaxf(float a, float b) {
  if (std::isnan(a)) return b;
  if (std::isnan(b)) return a;
  return std::fmaxf(a, b);
}
#define fminf pf_ptx_fminf
#define fmaxf pf_ptx_fmaxf

static inline int32_t __float_as_int(float x) { int32_t u; std::memcpy(&u, &x, 4); return u; }
static inline float __int_as_float(int32_t u) { float x; std::memcpy(&x, &u, 4); return x; }
// Deliberately NO out-of-range fallback here so UBSan catches any unguarded float->int UB!
static inline int32_t __float2int_rz(float x) {
  return static_cast<int32_t>(std::truncf(x));
}
static inline int32_t __float2int_rn(float x) {
  std::fesetround(FE_TONEAREST);
  return static_cast<int32_t>(std::nearbyintf(x));
}
static inline uint16_t f32_to_bf16_rne(float x) {
  uint32_t u;
  std::memcpy(&u, &x, 4);
  uint32_t exp = (u >> 23) & 0xffu;
  uint32_t frac = u & 0x7fffffu;
  if (exp == 0xffu) return frac ? 0x7fc0u : (uint16_t)(u >> 16);
  uint32_t lsb = (u >> 16) & 1u;
  return (uint16_t)((u + 0x7fffu + lsb) >> 16);
}
static inline float bf16_to_f32(uint16_t b) {
  uint32_t u = ((uint32_t)b) << 16;
  float x;
  std::memcpy(&x, &u, 4);
  return x;
}

${snippets.join("\n\n")}

int main() {
  static uint16_t out[${cases.length}][65536];
  for (uint32_t b = 0; b < 65536u; b++) {
    float x = bf16_to_f32((uint16_t)b);
    out[0][b] = f32_to_bf16_rne(pf_bf16_exp2(x));
    out[1][b] = f32_to_bf16_rne(pf_bf16_rsqrt(x));
    out[2][b] = f32_to_bf16_rne(pf_bf16_silu(x));
    out[3][b] = f32_to_bf16_rne(pf_ml_adv_ftoi_trunc(x));
    out[4][b] = f32_to_bf16_rne(pf_ml_adv_ftoi_round(x));
    out[5][b] = f32_to_bf16_rne(pf_ml_adv_min_s0(x));
  }
  std::fwrite(out, sizeof(uint16_t), ${cases.length} * 65536, stdout);
  return 0;
}
`;
    fs.writeFileSync(cppPath, cpp, "utf8");
    const comp = spawnSync(cxx, ["-std=c++20", "-O2", "-fsanitize=undefined", "-fno-sanitize-recover=all", cppPath, "-o", binPath], { encoding: "utf8" });
    assert.equal(comp.status, 0, `UBSan compile failed:\n${comp.stderr}`);
    const run = spawnSync(binPath, [], { maxBuffer: 2 * 1024 * 1024 });
    assert.equal(run.status, 0, `UBSan execution failed (status=${run.status}):\n${run.stderr?.toString("utf8")}`);
    const buf = run.stdout;
    assert.equal(buf.length, cases.length * 65536 * 2);
    for (let k = 0; k < parsedMap.length; k++) {
      let mismatches = 0;
      for (let b = 0; b < 65536; b++) {
        const cppOut = buf.readUInt16LE((k * 65536 + b) * 2);
        const jsOut = f32ToBf16RNE(evalKernelF32(parsedMap[k].parsed, bf16ToF32(b)));
        if (cppOut !== jsOut) {
          mismatches++;
          if (mismatches <= 3) {
            console.error(`Mismatch on ${parsedMap[k].id} bf16=0x${b.toString(16)}: cpp=0x${cppOut.toString(16)} js=0x${jsOut.toString(16)}`);
          }
        }
      }
      assert.equal(mismatches, 0, `${parsedMap[k].id}: ${mismatches} bf16 mismatches between UBSan C++ and JS interpreter`);
    }
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

console.log(`ALL ${passed} ml-math-kernels Judge tests PASSED.`);
