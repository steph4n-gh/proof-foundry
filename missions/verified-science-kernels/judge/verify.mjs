#!/usr/bin/env node
/**
 * Deterministic Judge Harness for Verified Science Kernels (v2 — Child-Process Isolated).
 *
 * Security (Opus 5.5 P0 #5):
 * - NEVER imports untrusted donor `.mjs` inside the parent harness that holds `--result`!
 * - Spawns an isolated child node process with minimal env (no result path in argv or env!),
 *   sends test payloads via stdin JSON, reads raw numerical outputs over stdout JSON, and
 *   computes + writes the verdict strictly in the trusted parent process.
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

/**
 * Execute untrusted artifact function inside an isolated child process with zero access to resultPath.
 */
function runArtifactInChild(fnName, calls) {
  const modUrl = pathToFileURL(artifactPath).href;
  const runnerCode = `
    import { pathToFileURL } from "node:url";
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
    engine: "Deterministic IEEE-754 Stress Judge v2 (isolated child)",
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
    const exactSum = a[0] + b[0];
    if (!(lo <= exactSum && exactSum <= hi && lo <= hi)) {
      writeResult({ ok: false, reason: `Outward rounding violated on ${JSON.stringify([a, b])} -> [${lo}, ${hi}]` });
    }
  }
  const [loBig, hiBig] = res.outputs[1];
  const strictOk = loBig < hiBig && loBig <= 1e16 && hiBig > 1e16;
  writeResult({
    ok: strictOk,
    engine: "Deterministic IEEE-754 Stress Judge v2 (isolated child)",
    signature: "intervalAdd(a, b) : outward-rounded containment for non-representable float64 sums",
    checks: ["outward_rounding_1e16_plus_1", "containment_battery"],
    reason: strictOk
      ? `Verified strict outward bracketing [${loBig}, ${hiBig}]`
      : `Failed strict outward rounding on 1e16 + 1.0: got [${loBig}, ${hiBig}]`,
  });
}

writeResult({ ok: false, reason: `Unknown target: ${target}` });
