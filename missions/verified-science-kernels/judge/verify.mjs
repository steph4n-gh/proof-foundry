#!/usr/bin/env node
/**
 * Deterministic Judge Harness for Verified Science Kernels.
 * Imports an untrusted submitted artifact module and runs deterministic,
 * adversarial IEEE-754 / combinatorial / algorithmic stress batteries against it.
 */
import fs from "node:fs";
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

const mod = await import(pathToFileURL(artifactPath).href);

if (target === "kahan_compensated_sum") {
  if (typeof mod.compensatedSum !== "function") {
    writeResult({ ok: false, reason: "Missing exported function compensatedSum(arr)" });
  }
  // Adversarial IEEE-754 test: 1e16 + 1e7 copies of 1.0 - 1e16 (naive float64 loses ALL 1.0s -> 0!)
  const arr = [1e16];
  for (let i = 0; i < 10000; i++) arr.push(1.0);
  arr.push(-1e16);
  const got = mod.compensatedSum(arr);
  const exact = 10000;
  // Also test mixed cancellation & Neumaier hard case
  const arr2 = [1.0, 1e100, 1.0, -1e100];
  const got2 = mod.compensatedSum(arr2);
  const ok = Math.abs(got - exact) <= 1e-9 && Math.abs(got2 - 2.0) <= 1e-9;
  writeResult({
    ok,
    engine: "Deterministic IEEE-754 Stress Judge v1",
    signature: "compensatedSum(xs : Float64[]) : preserves exact sum across 1e16 and 1e100 catastrophic cancellation",
    checks: ["catastrophic_1e16_cancel", "neumaier_1e100_cancel"],
    reason: ok
      ? `Passed all IEEE-754 cancellation batteries (got=${got}, neumaier=${got2})`
      : `Precision failure: got=${got} (expected ${exact}), neumaier=${got2} (expected 2)`,
  });
}

if (target === "interval_add_soundness") {
  if (typeof mod.intervalAdd !== "function") {
    writeResult({ ok: false, reason: "Missing exported function intervalAdd([lo1, hi1], [lo2, hi2])" });
  }
  const cases = [
    [[0.1, 0.1], [0.2, 0.2]],
    [[1e16, 1e16], [1.0, 1.0]],
    [[-1e-16, 1e-16], [1.0, 1.0]],
  ];
  for (const [a, b] of cases) {
    const [lo, hi] = mod.intervalAdd(a, b);
    const exactSum = a[0] + b[0];
    if (!(lo <= exactSum && exactSum <= hi && lo <= hi)) {
      writeResult({ ok: false, reason: `Outward rounding violated on ${JSON.stringify([a, b])} -> [${lo}, ${hi}]` });
    }
  }
  // Check strict outward rounding on 1e16 + 1.0 (exact value is NOT representable in float64? Actually 1e16+1 isn't -> must bracket!)
  const [loBig, hiBig] = mod.intervalAdd([1e16, 1e16], [1.0, 1.0]);
  const strictOk = loBig < hiBig && loBig <= 1e16 && hiBig > 1e16;
  writeResult({
    ok: strictOk,
    engine: "Deterministic IEEE-754 Stress Judge v1",
    signature: "intervalAdd(a, b) : outward-rounded containment for non-representable float64 sums",
    checks: ["outward_rounding_1e16_plus_1", "containment_battery"],
    reason: strictOk
      ? `Verified strict outward bracketing [${loBig}, ${hiBig}]`
      : `Failed strict outward rounding on 1e16 + 1.0: got [${loBig}, ${hiBig}]`,
  });
}

writeResult({ ok: false, reason: `Unknown target: ${target}` });
