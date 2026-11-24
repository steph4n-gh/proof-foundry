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
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";

const args = {};
for (let i = 2; i < process.argv.length; i += 2) {
  args[process.argv[i].replace(/^--/, "")] = process.argv[i + 1];
}

const artifactPath = args.artifact;
const target = args.target;
const resultPath = args.result;
const expectedScoreArg = args.score;
const specPath = args.spec;

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

function nodePermissionFlag() {
  const [major, minor] = process.versions.node.split(".").map(Number);
  return major > 22 || (major === 22 && minor >= 13) ? "--permission" : "--experimental-permission";
}

/**
 * Transform a pure-JS single-file kernel module (no imports/re-exports) into a strict-mode script
 * that returns the requested exported function inside an isolated V8 `vm` context.
 */
function preparePureKernelSource(raw, fnName) {
  if (!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(String(fnName || ""))) {
    return { ok: false, error: `Invalid target export identifier: ${fnName}` };
  }
  const noComments = stripJsCommentsStrict(raw);
  if (noComments == null) {
    return { ok: false, error: "Unclosed block comment in kernel artifact" };
  }
  if (/(^|[^A-Za-z0-9_$.])import\s*(?:[\s{*'"(]|from\b)/m.test(noComments)) {
    return { ok: false, error: "Executable kernel artifacts cannot use import statements or dynamic import()" };
  }
  if (/\bexport\s+(?:\*|\{[^}]*\})\s+from\b/.test(noComments)) {
    return { ok: false, error: "Executable kernel artifacts cannot re-export external modules" };
  }
  if (/\bexport\s+default\b/.test(noComments)) {
    return { ok: false, error: `Use named export \`export function ${fnName}\` (default export unsupported)` };
  }

  // Track explicit exported identifiers so private helpers cannot impersonate an export.
  const exported = new Set();
  let body = noComments
    .replace(/\bexport\s+(async\s+)?function\s+([A-Za-z_$][A-Za-z0-9_$]*)\b/g, (_m, asyncKw, name) => {
      if (asyncKw) return `export ${asyncKw}function ${name}`; // will fail syntax check cleanly
      exported.add(name);
      return `function ${name}`;
    })
    .replace(/\bexport\s+(const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\b/g, (_m, decl, name) => {
      exported.add(name);
      return `${decl} ${name}`;
    })
    .replace(/\bexport\s*\{([^}]*)\}\s*;?/g, (_m, list) => {
      const aliases = [];
      for (const item of list.split(",")) {
        const t = item.trim();
        if (!t) continue;
        const asMatch = t.match(/^([A-Za-z_$][A-Za-z0-9_$]*)(?:\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*))?$/);
        if (!asMatch) return "/* invalid export list */ export {};";
        exported.add(asMatch[2] || asMatch[1]);
        if (asMatch[2] && asMatch[2] !== asMatch[1]) {
          aliases.push(`const ${asMatch[2]} = ${asMatch[1]};`);
        }
      }
      return aliases.join("\n");
    });

  if (/\bexport\b/.test(body)) {
    return { ok: false, error: "Unsupported export syntax in kernel artifact" };
  }
  if (!exported.has(fnName)) {
    return { ok: false, error: `Missing exported function ${fnName}` };
  }
  return {
    ok: true,
    script: `"use strict";\n(function() {\n${body}\nreturn (typeof ${fnName} === "function") ? ${fnName} : null;\n})();`,
  };
}

/**
 * Execute an untrusted pure-JS numerical kernel inside a double-isolated child process:
 *  1. Node `--permission` with ZERO filesystem, child-process, worker, addon, or WASI permissions
 *     plus `--max-old-space-size=256`.
 *  2. Separate V8 `vm` context (`Object.create(null)`, `codeGeneration: { strings: false, wasm: false }`)
 *     with NO `process`, `console`, `fetch`, `Buffer`, `require`, `import`, or host prototypes.
 *  3. Per-run random 128-bit nonce envelope written by the outer host realm using pre-captured
 *     `process.stdout.write` and `JSON.stringify` over strictly extracted primitive numbers/tuples.
 */
function runArtifactInChild(fnName, calls) {
  let raw;
  try {
    if (fs.lstatSync(artifactPath).isSymbolicLink()) {
      return { ok: false, error: `Symlink artifacts are forbidden: ${artifactPath}` };
    }
    const realArtifact = fs.realpathSync(artifactPath);
    const st = fs.statSync(realArtifact);
    if (st.size > 256 * 1024) return { ok: false, error: "Kernel artifact exceeds 256 KiB limit" };
    raw = fs.readFileSync(realArtifact, "utf8");
  } catch {
    return { ok: false, error: `Artifact not found: ${artifactPath}` };
  }

  const prep = preparePureKernelSource(raw, fnName);
  if (!prep.ok) return { ok: false, error: prep.error };

  const nonce = crypto.randomBytes(16).toString("hex");
  const runnerCode = `
    import vm from "node:vm";
    const _stdoutWrite = process.stdout.write.bind(process.stdout);
    const _jsonStringify = JSON.stringify;
    const _jsonParse = JSON.parse;
    const _isFinite = Number.isFinite;

    const chunks = [];
    for await (const c of process.stdin) chunks.push(c);
    const req = _jsonParse(Buffer.concat(chunks).toString("utf8"));

    try {
      const ctx = vm.createContext(Object.create(null), {
        codeGeneration: { strings: false, wasm: false },
      });
      // Capture pristine VM-realm intrinsics before any untrusted code executes.
      // Extraction produces a primitive JSON string so no VM object ever touches host JS.
      const vmRun = vm.runInContext(\`"use strict";
        (function() {
          const _parse = JSON.parse;
          const _isFin = Number.isFinite;
          const _isInt = Number.isInteger;
          const _isArr = Array.isArray;
          const _getOwn = Object.getOwnPropertyDescriptor;
          const _numStr = Number.prototype.toString;
          const _call = Function.prototype.call;
          const _apply = Function.prototype.apply;
          return function(fn, callsJson) {
            const calls = _parse(callsJson);
            let json = "[";
            for (let i = 0; i < calls.length; i++) {
              if (i > 0) json += ",";
              const v = _call.call(_apply, fn, undefined, calls[i]);
              if (typeof v === "number") {
                if (!_isFin(v)) return "ERR:Non-finite output on case " + i;
                json += _call.call(_numStr, v);
              } else if (_isArr(v)) {
                const len = v.length;
                if (!_isInt(len) || len < 0 || len > 16) return "ERR:Invalid tuple length on case " + i;
                json += "[";
                for (let j = 0; j < len; j++) {
                  if (j > 0) json += ",";
                  const desc = _getOwn(v, j);
                  if (!desc || !("value" in desc) || typeof desc.value !== "number" || !_isFin(desc.value)) {
                    return "ERR:Non-numeric or accessor element on case " + i;
                  }
                  json += _call.call(_numStr, desc.value);
                }
                json += "]";
              } else {
                return "ERR:Non-finite or non-numeric output on case " + i;
              }
            }
            return json + "]";
          };
        })();
      \`, ctx, { timeout: 1000 });
      const fn = vm.runInContext(req.script, ctx, { timeout: 2000, filename: "artifact.vm.js" });
      if (typeof fn !== "function") {
        _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: "Missing exported function " + req.fnName }));
        process.exit(0);
      }
      const rawJson = vmRun(fn, _jsonStringify(req.calls));
      if (typeof rawJson !== "string") {
        _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: "Invalid output envelope from kernel" }));
        process.exit(0);
      }
      if (rawJson.startsWith("ERR:")) {
        _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: rawJson.slice(4) }));
        process.exit(0);
      }
      const outputs = _jsonParse(rawJson);
      if (!Array.isArray(outputs) || outputs.length !== req.calls.length) {
        _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: "Invalid output vector from kernel" }));
        process.exit(0);
      }
      for (let i = 0; i < outputs.length; i++) {
        const v = outputs[i];
        const okVal = typeof v === "number"
          ? _isFinite(v)
          : Array.isArray(v) && v.every((x) => typeof x === "number" && _isFinite(x));
        if (!okVal) {
          _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: "Non-finite output on case " + i }));
          process.exit(0);
        }
      }
      _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: true, outputs }));
    } catch (err) {
      const msg = err && typeof err.message === "string" ? err.message : String(err);
      _stdoutWrite(_jsonStringify({ nonce: req.nonce, ok: false, error: "Sandboxed kernel error: " + msg.slice(0, 300) }));
    }
  `;
  const child = spawnSync(
    process.execPath,
    [nodePermissionFlag(), "--max-old-space-size=256", "--input-type=module", "-e", runnerCode],
    {
      input: JSON.stringify({ nonce, script: prep.script, fnName, calls }),
      encoding: "utf8",
      timeout: 5000,
      env: {
        PATH: process.env.PATH || "/usr/local/bin:/usr/bin:/bin",
        TMPDIR: os.tmpdir(),
      },
    }
  );
  if (child.status !== 0 || !child.stdout) {
    return { ok: false, error: `Isolated artifact runner failed (exit=${child.status}): ${(child.stderr || "").slice(0, 400)}` };
  }
  try {
    const parsed = JSON.parse(child.stdout);
    if (!parsed || parsed.nonce !== nonce) {
      return { ok: false, error: "Runner protocol nonce mismatch (forged stdout rejected)" };
    }
    return parsed;
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

// ---------------------------------------------------------------------------
// King-of-the-Hill Pure-Data Minimax Polynomial Verification (Exact 128-Bit BigInt Oracle)
// ---------------------------------------------------------------------------
const FIX_BITS = 128n;
const FIX_ONE = 1n << FIX_BITS;

function floatToFixed128(x) {
  const d = floatToDyadic(x);
  if (d.m === 0n) return 0n;
  const shift = BigInt(d.e) + FIX_BITS;
  if (shift >= 0n) return d.m << shift;
  return d.m / (1n << -shift);
}

function fixed128Exp(xFix) {
  let term = FIX_ONE;
  let sum = FIX_ONE;
  for (let k = 1n; k <= 34n; k++) {
    term = (term * xFix) / (FIX_ONE * k);
    if (term === 0n) break;
    sum += term;
  }
  return sum;
}

function fixed128Sin(xFix) {
  const x2 = (xFix * xFix) / FIX_ONE;
  let term = xFix;
  let sum = xFix;
  for (let k = 1n; k <= 20n; k++) {
    term = -(term * x2) / (FIX_ONE * (2n * k) * (2n * k + 1n));
    if (term === 0n) break;
    sum += term;
  }
  return sum;
}

/**
 * Pure static parser for minimax polynomial coefficient artifacts (ZERO JS code execution!).
 * Accepts either pure JSON (`[c0, c1, ...]` or `{"coeffs": [...]}`) or a strict data-only
 * ES module (`export const <exportName> = [ <numeric literals> ];`). Rejects imports,
 * expressions, identifiers, function calls, or any executable syntax.
 */
function stripJsCommentsStrict(src) {
  let out = "";
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    const next = src[i + 1];
    if (ch === "/" && next === "/") {
      i += 2;
      while (i < src.length && src[i] !== "\n") i++;
      continue;
    }
    if (ch === "/" && next === "*") {
      i += 2;
      let closed = false;
      while (i + 1 < src.length) {
        if (src[i] === "*" && src[i + 1] === "/") {
          i += 2;
          closed = true;
          break;
        }
        i++;
      }
      if (!closed) return null;
      out += " ";
      continue;
    }
    out += ch;
    i++;
  }
  return out;
}

function readDataExportInChild(exportName) {
  let raw;
  try {
    if (fs.lstatSync(artifactPath).isSymbolicLink()) {
      return { ok: false, error: `Symlink artifacts are forbidden: ${artifactPath}` };
    }
    const realArtifact = fs.realpathSync(artifactPath);
    const st = fs.statSync(realArtifact);
    if (st.size > 256 * 1024) return { ok: false, error: "Data artifact exceeds 256 KiB limit" };
    raw = fs.readFileSync(realArtifact, "utf8");
  } catch (err) {
    return { ok: false, error: `Could not read artifact: ${err?.message || err}` };
  }

  // Path 1: pure JSON array or { [exportName]: [...] }
  const trimmedRaw = raw.trim();
  if (trimmedRaw.startsWith("[") || trimmedRaw.startsWith("{")) {
    try {
      const parsed = JSON.parse(trimmedRaw);
      const arr = Array.isArray(parsed) ? parsed : parsed?.[exportName];
      if (!Array.isArray(arr)) return { ok: false, error: `JSON artifact missing array ${exportName}` };
      if (!arr.every((x) => typeof x === "number" && Number.isFinite(x))) {
        return { ok: false, error: `All elements of ${exportName} must be finite float64 numbers` };
      }
      return { ok: true, value: arr };
    } catch {
      return { ok: false, error: "Invalid JSON in pure-data artifact" };
    }
  }

  // Path 2: strict data-only ESM (`export const <exportName> = [ <numeric literals> ];`) — zero eval/import!
  const clean = stripJsCommentsStrict(raw);
  if (clean == null) return { ok: false, error: "Unclosed block comment in pure-data artifact" };
  const escName = String(exportName || "coeffs").replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const m = clean.trim().match(new RegExp(`^export\\s+const\\s+${escName}\\s*=\\s*\\[([\\s\\S]*)\\]\\s*;?$`));
  if (!m) {
    return {
      ok: false,
      error: `Pure-data artifact must contain ONLY \`export const ${exportName} = [ <numeric literals> ];\` or a JSON array (code execution is forbidden)`,
    };
  }
  const inner = m[1].trim();
  if (!inner) return { ok: true, value: [] };
  const parts = inner.split(",").map((p) => p.trim());
  if (parts.length > 0 && parts[parts.length - 1] === "") parts.pop(); // allow trailing comma
  const NUM_RE = /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/;
  const values = [];
  for (const tok of parts) {
    if (!NUM_RE.test(tok)) {
      return { ok: false, error: `Disallowed non-literal token in ${exportName}: ${JSON.stringify(tok.slice(0, 40))}` };
    }
    const n = Number(tok);
    if (!Number.isFinite(n)) {
      return { ok: false, error: `Non-finite numeric literal in ${exportName}: ${tok}` };
    }
    values.push(n);
  }
  return { ok: true, value: values };
}

if (target === "minimax_exp_deg7" || target === "minimax_sin_deg7") {
  if (!specPath || !fs.existsSync(specPath)) {
    writeResult({ ok: false, reason: `Missing frozen spec file for ${target}` });
  }
  const spec = JSON.parse(fs.readFileSync(specPath, "utf8"));
  if (spec.target !== target) {
    writeResult({ ok: false, reason: `Spec target mismatch: spec has ${spec.target}, expected ${target}` });
  }
  const expectedScore = Number(expectedScoreArg);
  if (!Number.isSafeInteger(expectedScore) || expectedScore < 0) {
    writeResult({ ok: false, reason: `Invalid expected score: ${expectedScoreArg}` });
  }
  const res = readDataExportInChild(spec.export_name || "coeffs");
  if (!res.ok) writeResult({ ok: false, reason: res.error });

  const coeffs = res.value;
  if (coeffs.length !== spec.expected_length) {
    writeResult({ ok: false, reason: `Expected exactly ${spec.expected_length} float64 coefficients, got ${coeffs.length}` });
  }

  const [lo, hi] = spec.domain;
  const gridN = Number(spec.grid_points || 4097);
  const scaleBig = BigInt(Math.round(Number(spec.error_scale)));
  let maxDiffFix = 0n;
  let worstX = 0;

  for (let i = 0; i < gridN; i++) {
    const x = gridN <= 1 ? lo : lo + ((hi - lo) * i) / (gridN - 1);
    let y;
    if (spec.mode === "horner_odd") {
      const x2 = x * x;
      let acc = coeffs[coeffs.length - 1];
      for (let j = coeffs.length - 2; j >= 0; j--) acc = acc * x2 + coeffs[j];
      y = x * acc;
    } else {
      let acc = coeffs[coeffs.length - 1];
      for (let j = coeffs.length - 2; j >= 0; j--) acc = acc * x + coeffs[j];
      y = acc;
    }
    if (!Number.isFinite(y)) {
      writeResult({ ok: false, reason: `Polynomial evaluated to non-finite value at x=${x}` });
    }
    const xFix = floatToFixed128(x);
    const refFix = spec.oracle === "exact_128bit_bigint_sin" ? fixed128Sin(xFix) : fixed128Exp(xFix);
    const yFix = floatToFixed128(y);
    const diff = yFix >= refFix ? yFix - refFix : refFix - yFix;
    if (diff > maxDiffFix) {
      maxDiffFix = diff;
      worstX = x;
    }
  }

  // Exact ceiling integer score in units of 1 / error_scale (deterministic across all CPUs!)
  const measuredScoreBig = (maxDiffFix * scaleBig + (FIX_ONE - 1n)) / FIX_ONE;
  const measuredScore = measuredScoreBig > BigInt(Number.MAX_SAFE_INTEGER) ? Number.MAX_SAFE_INTEGER : Number(measuredScoreBig);
  const ok = measuredScore <= expectedScore;
  writeResult({
    ok,
    score: ok ? expectedScore : measuredScore,
    measured_score: measuredScore,
    engine: "Deterministic 128-Bit BigInt Minimax Judge v4 (isolated child)",
    signature: `${target} ≤ ${expectedScore} (${spec.unit}) [measured=${measuredScore}, worst_x=${worstX.toPrecision(6)}]`,
    checks: [spec.oracle, `grid_${gridN}`, `horner_float64_${spec.mode}`],
    reason: ok
      ? `Verified minimax polynomial error ${measuredScore} ≤ target ${expectedScore} (${spec.unit}) across ${gridN} exact 128-bit reference points`
      : `Error bound missed: measured ${measuredScore} > target ${expectedScore} (${spec.unit}) at x=${worstX.toPrecision(6)}`,
  });
}

writeResult({ ok: false, reason: `Unknown target: ${target}` });
