#!/usr/bin/env node
/**
 * Deterministic Judge Harness for Verified Science Kernels (v3 — Child-Process Isolated + Exact Rational Oracle).
 *
 * Security:
 * - Untrusted donor `.mjs` runs strictly inside a child process over stdin/stdout JSON with minimal env
 *   and ZERO access to `resultPath`.
 * - Exact IEEE-754 float64 -> BigInt dyadic rational arithmetic (`num * 2^exp`) lets us verify
 *   TwoSum, Dot2, and Shewchuk orient2d against mathematically exact ground truth!
 */
import fs from "node:fs";
import os from "node:os";
import { spawnSync } from "node:child_process";
import { pathToFileURL } from "node:url";

const args = {};
for (let i = 2; i < process.argv.length; i += 2) {
  args[process.argv[i].replace(/^--/, "")] = process.argv[i + 1];
}

const artifactPath = args.artifact;
const target = args.target;
const resultPath = args.result;

function writeResult(obj) {
  fs.writeFileSync(resultPath, JSON.stringify(obj, null, 2), "utf8");
  process.exit(obj.ok ? 0 : 1);
}

// Exact IEEE-754 float64 -> { m: BigInt, e: number } representing m * 2^e
const _buf = new ArrayBuffer(8);
const _f64 = new Float64Array(_buf);
const _u64 = new BigUint64Array(_buf);

function floatToDyadic(x) {
  if (!Number.isFinite(x)) throw new Error(`Non-finite float: ${x}`);
  if (x === 0) return { m: 0n, e: 0 };
  _f64[0] = x;
  const bits = _u64[0];
  const sign = (bits >> 63n) === 1n ? -1n : 1n;
  const rawExp = Number((bits >> 52n) & 0x7ffn);
  const frac = bits & ((1n << 52n) - 1n);
  if (rawExp === 0) {
    return { m: sign * frac, e: -1074 };
  }
  return { m: sign * ((1n << 52n) | frac), e: rawExp - 1075 };
}

function dyadicAdd(a, b) {
  if (a.m === 0n) return b;
  if (b.m === 0n) return a;
  const e = Math.min(a.e, b.e);
  return { m: (a.m << BigInt(a.e - e)) + (b.m << BigInt(b.e - e)), e };
}

function dyadicSub(a, b) {
  return dyadicAdd(a, { m: -b.m, e: b.e });
}

function dyadicMul(a, b) {
  if (a.m === 0n || b.m === 0n) return { m: 0n, e: 0 };
  return { m: a.m * b.m, e: a.e + b.e };
}

function dyadicEq(a, b) {
  return dyadicSub(a, b).m === 0n;
}

function dyadicSign(a) {
  return a.m > 0n ? 1 : a.m < 0n ? -1 : 0;
}

function exactDot(xs, ys) {
  let acc = { m: 0n, e: 0 };
  for (let i = 0; i < xs.length; i++) {
    acc = dyadicAdd(acc, dyadicMul(floatToDyadic(xs[i]), floatToDyadic(ys[i])));
  }
  return acc;
}

function exactOrient2dSign(ax, ay, bx, by, cx, cy) {
  const dx1 = dyadicSub(floatToDyadic(ax), floatToDyadic(cx));
  const dy1 = dyadicSub(floatToDyadic(ay), floatToDyadic(cy));
  const dx2 = dyadicSub(floatToDyadic(bx), floatToDyadic(cx));
  const dy2 = dyadicSub(floatToDyadic(by), floatToDyadic(cy));
  return dyadicSign(dyadicSub(dyadicMul(dx1, dy2), dyadicMul(dy1, dx2)));
}

function runArtifactInChild(fnName, calls) {
  const modUrl = pathToFileURL(artifactPath).href;
  const runnerCode = `
    const chunks = [];
    for await (const c of process.stdin) chunks.push(c);
    const req = JSON.parse(Buffer.concat(chunks).toString("utf8"));
    const mod = await import(req.modUrl);
    const fn = mod[req.fnName];
    if (typeof fn !== "function") {
      process.stdout.write(JSON.stringify({ ok: false, error: "Missing exported function " + req.fnName }));
      process.exit(0);
    }
    const outputs = req.calls.map((callArgs) => fn(...callArgs));
    process.stdout.write(JSON.stringify({ ok: true, outputs }));
  `;
  const child = spawnSync(process.execPath, ["--input-type=module", "-e", runnerCode], {
    input: JSON.stringify({ modUrl, fnName, calls }),
    encoding: "utf8",
    timeout: 15000,
    env: {
      PATH: process.env.PATH || "/usr/local/bin:/usr/bin:/bin",
      TMPDIR: os.tmpdir(),
    },
  });
  if (child.status !== 0 || !child.stdout) {
    return { ok: false, error: `Isolated artifact runner failed (exit=${child.status}): ${(child.stderr || "").slice(0, 400)}` };
  }
  try {
    return JSON.parse(child.stdout);
  } catch {
    return { ok: false, error: "Artifact polluted stdout or emitted invalid JSON" };
  }
}

if (target === "kahan_compensated_sum") {
  const arr = [1e16];
  for (let i = 0; i < 10000; i++) arr.push(1.0);
  arr.push(-1e16);
  const arr2 = [1.0, 1e100, 1.0, -1e100];

  const res = runArtifactInChild("compensatedSum", [[arr], [arr2]]);
  if (!res.ok) writeResult({ ok: false, reason: res.error });

  const [got, got2] = res.outputs;
  const exact = 10000;
  const ok = typeof got === "number" && typeof got2 === "number" && Math.abs(got - exact) <= 1e-9 && Math.abs(got2 - 2.0) <= 1e-9;
  writeResult({
    ok,
    engine: "Deterministic IEEE-754 Stress Judge v3 (isolated child)",
    signature: "compensatedSum(xs : Float64[]) : preserves exact sum across 1e16 and 1e100 catastrophic cancellation",
    checks: ["catastrophic_1e16_cancel", "neumaier_1e100_cancel"],
    reason: ok
      ? `Passed all IEEE-754 cancellation batteries (got=${got}, neumaier=${got2})`
      : `Precision failure: got=${got} (expected ${exact}), neumaier=${got2} (expected 2)`,
  });
}

if (target === "interval_add_soundness") {
  const cases = [
    [[0.1, 0.1], [0.2, 0.2]],
    [[1e16, 1e16], [1.0, 1.0]],
    [[-1e-16, 1e-16], [1.0, 1.0]],
  ];
  const res = runArtifactInChild("intervalAdd", cases);
  if (!res.ok) writeResult({ ok: false, reason: res.error });

  for (let i = 0; i < cases.length; i++) {
    const [a, b] = cases[i];
    const out = res.outputs[i];
    if (!Array.isArray(out) || out.length !== 2 || typeof out[0] !== "number" || typeof out[1] !== "number") {
      writeResult({ ok: false, reason: `Invalid interval output on case ${i}` });
    }
    const [lo, hi] = out;
    const exactSum = dyadicAdd(floatToDyadic(a[0]), floatToDyadic(b[0]));
    const loOk = dyadicSign(dyadicSub(floatToDyadic(lo), exactSum)) <= 0;
    const hiOk = dyadicSign(dyadicSub(floatToDyadic(hi), exactSum)) >= 0;
    if (!loOk || !hiOk || !(lo <= hi)) {
      writeResult({ ok: false, reason: `Outward rounding violated on ${JSON.stringify([a, b])} -> [${lo}, ${hi}]` });
    }
  }
  const [loBig, hiBig] = res.outputs[1];
  const strictOk = loBig < hiBig && loBig <= 1e16 && hiBig > 1e16;
  writeResult({
    ok: strictOk,
    engine: "Deterministic IEEE-754 Stress Judge v3 (isolated child)",
    signature: "intervalAdd(a, b) : outward-rounded containment for non-representable float64 sums",
    checks: ["outward_rounding_1e16_plus_1", "containment_battery"],
    reason: strictOk
      ? `Verified strict outward bracketing [${loBig}, ${hiBig}]`
      : `Failed strict outward rounding on 1e16 + 1.0: got [${loBig}, ${hiBig}]`,
  });
}

if (target === "two_sum_dot2") {
  const sumPairs = [
    [1e16, 1.0],
    [1.0, 1e16],
    [0.1, 0.2],
    [1e100, -1e100 + 1e84],
    [Math.PI, -3.141592653589793],
    [1e-308, 5e-324],
    [-1e15, 0.3333333333333333],
  ];
  const resSum = runArtifactInChild("twoSum", sumPairs);
  if (!resSum.ok) writeResult({ ok: false, reason: resSum.error });

  for (let i = 0; i < sumPairs.length; i++) {
    const [a, b] = sumPairs[i];
    const out = resSum.outputs[i];
    if (!Array.isArray(out) || out.length !== 2 || !Number.isFinite(out[0]) || !Number.isFinite(out[1])) {
      writeResult({ ok: false, reason: `twoSum invalid output on [${a}, ${b}]` });
    }
    const [s, e] = out;
    if (s !== a + b) {
      writeResult({ ok: false, reason: `twoSum primary sum must equal IEEE-754 (a+b) on [${a}, ${b}]` });
    }
    const lhs = dyadicAdd(floatToDyadic(a), floatToDyadic(b));
    const rhs = dyadicAdd(floatToDyadic(s), floatToDyadic(e));
    if (!dyadicEq(lhs, rhs)) {
      writeResult({ ok: false, reason: `twoSum exact rational invariant a+b == s+e violated on [${a}, ${b}] -> [${s}, ${e}]` });
    }
  }

  const dotCases = [
    [[1e8, 1.0, -1e8], [1e8, 1.0, 1e8]],            // exact = 1.0; naive = 0.0!
    [[1e16, 1.0, -1e16, 2.0], [1.0, 1.0, 1.0, 1.0]], // exact = 3.0; naive = 2.0!
    [[1e7 + 1, -(1e7), 1e-7], [1e7 - 1, 1e7, 1e7]],  // (1e14 - 1) - 1e14 + 1 = 0!
    [[3.0, 1e16, -3.0, -1e16, 0.5], [1.0, 1.0, 1.0, 1.0, 4.0]], // exact = 2.0!
  ];
  const resDot = runArtifactInChild("dot2", dotCases);
  if (!resDot.ok) writeResult({ ok: false, reason: resDot.error });

  for (let i = 0; i < dotCases.length; i++) {
    const [xs, ys] = dotCases[i];
    const got = resDot.outputs[i];
    if (typeof got !== "number" || !Number.isFinite(got)) {
      writeResult({ ok: false, reason: `dot2 non-finite output on case ${i}` });
    }
    const exact = exactDot(xs, ys);
    const diff = dyadicSub(floatToDyadic(got), exact);
    // Must match exact rational dot product within 1e-12 (exact integer answers here!)
    const exactFloat = Number(exact.m) * Math.pow(2, exact.e);
    if (Math.abs(got - exactFloat) > 1e-12 && diff.m !== 0n) {
      writeResult({ ok: false, reason: `dot2 cancellation failure on case ${i}: got=${got}, exact=${exactFloat}` });
    }
  }

  writeResult({
    ok: true,
    engine: "Deterministic IEEE-754 Stress Judge v3 (isolated child)",
    signature: "twoSum(a,b) exact rational invariant + dot2(xs,ys) catastrophic-cancellation resistance",
    checks: ["twosum_exact_rational_battery", "dot2_ill_conditioned_battery"],
    reason: "Passed all exact-rational TwoSum invariants and ill-conditioned Dot2 batteries",
  });
}

if (target === "orient2d_exact") {
  // Shewchuk-style adversarial near-collinear, collinear, and high-magnitude orientation tests
  const cases = [
    [0, 0, 1, 0, 0, 1],                                               // +1 (CCW)
    [0, 0, 0, 1, 1, 0],                                               // -1 (CW)
    [0, 0, 1, 1, 2, 2],                                               //  0 (exact collinear)
    [1e8, 1e8, 1e8 + 1, 1e8 + 1, 1e8 + 2, 1e8 + 2],                   //  0 (collinear at 1e8)
    [1e8, 1e8, 1e8 + 1, 1e8 + 1, 1e8 + 2, 1e8 + 2 + 1e-7],            // +1 (tiny CCW perturbation)
    [1e8, 1e8, 1e8 + 1, 1e8 + 1, 1e8 + 2, 1e8 + 2 - 1e-7],            // -1 (tiny CW perturbation)
    [0.5 + 1e-16, 0.5, 1.0, 1.0, 2.0, 2.0],                           // non-zero sub-ULP diagonal
    [0.5, 0.5 + 1e-16, 1.0, 1.0, 2.0, 2.0],                           // opposite sub-ULP diagonal
    [12.0, 12.0, 24.0, 24.0, 0.5, 0.5 + 2 ** -53],                    // naive float64 collapses to 0!
    [12.0, 12.0, 24.0, 24.0, 0.5, 0.5 - 2 ** -53],                    // opposite sign!
    [1e7, 1e7, 1e7 + 3, 1e7 + 3, 1e7 + 7, 1e7 + 7 + 2 ** -26],        // naive loses low bits!
    [1e7, 1e7, 1e7 + 3, 1e7 + 3, 1e7 + 7, 1e7 + 7 - 2 ** -26],
  ];
  const res = runArtifactInChild("orient2d", cases);
  if (!res.ok) writeResult({ ok: false, reason: res.error });

  for (let i = 0; i < cases.length; i++) {
    const c = cases[i];
    const got = res.outputs[i];
    if (typeof got !== "number" || Number.isNaN(got)) {
      writeResult({ ok: false, reason: `orient2d invalid output on case ${i}: ${got}` });
    }
    const gotSign = got > 0 ? 1 : got < 0 ? -1 : 0;
    const wantSign = exactOrient2dSign(...c);
    if (gotSign !== wantSign) {
      writeResult({
        ok: false,
        reason: `orient2d sign mismatch on case ${i} (${JSON.stringify(c)}): got sign ${gotSign} (val=${got}), exact rational sign ${wantSign}`,
      });
    }
  }

  writeResult({
    ok: true,
    engine: "Deterministic IEEE-754 Stress Judge v3 (isolated child)",
    signature: "orient2d(ax,ay,bx,by,cx,cy) : exact orientation sign under adversarial near-collinear perturbations",
    checks: ["shewchuk_collinear_battery", "sub_ulp_perturbation_battery"],
    reason: `Passed all ${cases.length} exact-rational 2D orientation stress cases`,
  });
}

writeResult({ ok: false, reason: `Unknown target: ${target}` });
