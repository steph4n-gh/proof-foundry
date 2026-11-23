#!/usr/bin/env node
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { coeffs } from "../missions/verified-science-kernels/artifacts/S_rec_exp_s405.mjs";

const formalDir = fileURLToPath(new URL(".", import.meta.url));
const leanDir = join(formalDir, "oracle");
const mission = join(formalDir, "../missions/verified-science-kernels");
const judgePath = join(mission, "judge/verify.mjs");
const artifactPath = join(mission, "artifacts/S_rec_exp_s405.mjs");
const expSpecPath = join(mission, "specs/S_rec_exp.json");
const sinSpecPath = join(mission, "specs/S_rec_sin.json");
const fixture = (path) => JSON.parse(readFileSync(path, "utf8"));
const abs = (n) => n < 0n ? -n : n;
const wireDyadic = ({ m, e }) => ({ m: String(m), e: String(e) });
const source = readFileSync(judgePath, "utf8");

function replaceOnce(text, before, after) {
  const parts = text.split(before);
  assert.equal(parts.length, 2, `Expected one occurrence of ${before} in the judge`);
  return parts.join(after);
}

function caseArray(text, target, name) {
  const anchor = `if (target === "${target}") {`;
  const start = text.indexOf(anchor);
  assert(start >= 0, `Missing judge target ${target}`);
  const block = text.slice(start).split("\nif (target", 2)[0];
  const match = block.match(new RegExp(`^  const ${name} = (\\[[\\s\\S]*?^  \\]);`, "m"));
  assert(match, `Missing judge cases ${target}/${name}`);
  return match[1];
}

async function loadJudge(text) {
  const scoreLine = text.match(/^  const measuredScoreBig = (.+);$/m);
  assert(scoreLine, "Could not locate the judge's ceiling expression");
  // The judge is a CLI. Expose its private functions in memory, with dispatch disabled.
  const instrumented = replaceOnce(
    text,
    "const target = args.target;",
    "const target = undefined;",
  );
  const module = replaceOnce(
    instrumented,
    'writeResult({ ok: false, reason: `Unknown target: ${target}` });',
    `export { FIX_ONE, floatToDyadic, floatToFixed128, dyadicAdd, dyadicSub, dyadicMul,
      dyadicEq, dyadicSign, exactDot, exactOrient2dSign, fixed128Exp, fixed128Sin };
    export const ceilScore = (maxDiffFix, scaleBig) => ${scoreLine[1]};
    export const twoSumCases = ${caseArray(text, "two_sum_dot2", "sumPairs")};
    export const dotCases = ${caseArray(text, "two_sum_dot2", "dotCases")};
    export const orientationCases = ${caseArray(text, "orient2d_exact", "cases")};`,
  );
  return import(`data:text/javascript;base64,${Buffer.from(module).toString("base64")}`);
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

function runLean(cases) {
  const input = cases.map(({ request }) => JSON.stringify(request)).join("\n") + "\n";
  const output = execFileSync(join(leanDir, ".lake/build/bin/pf_oracle_check"), [], {
    input,
    encoding: "utf8",
    maxBuffer: 8 * 1024 * 1024,
  });
  const results = output.trimEnd().split("\n").map((line) => JSON.parse(line));
  assert.equal(results.length, cases.length, "Lean response count");
  return results;
}

function directJudge(spec) {
  const dir = mkdtempSync(join(tmpdir(), "pf-math-oracle-"));
  try {
    const resultPath = join(dir, "result.json");
    execFileSync(process.execPath, [
      judgePath, "--artifact", artifactPath, "--target", spec.target,
      "--result", resultPath, "--score", "405", "--spec", expSpecPath,
    ]);
    return fixture(resultPath);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

buildLean();
const judge = await loadJudge(source);
const {
  FIX_ONE: Q, floatToDyadic, floatToFixed128, dyadicAdd, dyadicSub, dyadicEq,
  dyadicSign, exactDot, exactOrient2dSign, ceilScore,
} = judge;
assert.equal(Q, 2n ** 128n, "The judge uses the proved fixed-point scale");

const cases = [];
function add(request, expected, label) {
  cases.push({ request, expected, label });
  return cases.length - 1;
}

function fixedCase(op, xFix, label) {
  const output = judge[op](xFix);
  const index = add({ op, x: String(xFix) }, String(output), label);
  return { index, xFix, output };
}

function scoreCase(diffFix, scale, label) {
  return add(
    { op: "measuredScore", diffFix: String(diffFix), scale: String(scale) },
    String(ceilScore(diffFix, scale)),
    label,
  );
}

function floatIsExact(x, xFix) {
  return dyadicEq(floatToDyadic(x), { m: xFix, e: -128 });
}

function grid(spec, op, limit) {
  assert.equal(spec.grid_points, 4097, spec.id);
  const [lo, hi] = spec.domain;
  return Array.from({ length: spec.grid_points }, (_, i) => {
    const x = lo + ((hi - lo) * i) / (spec.grid_points - 1);
    const xFix = floatToFixed128(x);
    assert(abs(xFix) <= limit, `${spec.id} grid point ${i} exceeds the proved domain`);
    assert(floatIsExact(x, xFix), `${spec.id} grid point ${i} changed in conversion`);
    return { x, ...fixedCase(op, xFix, `${spec.id} grid point ${i}`) };
  });
}

const expSpec = fixture(expSpecPath);
const sinSpec = fixture(sinSpecPath);
assert.equal(expSpec.oracle, "exact_128bit_bigint_exp");
assert.equal(sinSpec.oracle, "exact_128bit_bigint_sin");
const expGrid = grid(expSpec, "fixed128Exp", Q / 2n);
const sinGrid = grid(sinSpec, "fixed128Sin", 4n * Q / 5n);
const edgeStart = cases.length;

for (const [i, x] of [
  0, -0, Number.MIN_VALUE, -Number.MIN_VALUE, 2 ** -1022, -(2 ** -1022),
  2 ** -129, -(2 ** -129), 3 * 2 ** -129, -3 * 2 ** -129,
  Number.MAX_VALUE, -Number.MAX_VALUE,
].entries()) {
  const xFix = floatToFixed128(x);
  add({ op: "dyadicToFixed128", a: wireDyadic(floatToDyadic(x)) }, String(xFix), `Float edge ${i}`);
  if (abs(xFix) <= Q / 2n) {
    fixedCase("fixed128Exp", xFix, `Exp float edge ${i}`);
    fixedCase("fixed128Sin", xFix, `Sin float edge ${i}`);
  }
}
for (const [op, limit] of [["fixed128Exp", Q / 2n], ["fixed128Sin", 4n * Q / 5n]]) {
  for (const x of [-limit, -limit + 1n, -2n, -1n, 0n, 1n, 2n, limit - 1n, limit]) {
    fixedCase(op, x, `${op} integer edge ${x}`);
  }
}

const dyadicPairs = [
  ...judge.twoSumCases.map((pair) => pair.map(floatToDyadic)),
  [floatToDyadic(-0), floatToDyadic(Number.MIN_VALUE)],
  [floatToDyadic(Number.MAX_VALUE), floatToDyadic(-Number.MIN_VALUE)],
  [floatToDyadic(0.5), floatToDyadic(-0.5)],
  [{ m: 1n, e: 100 }, { m: 2n, e: 99 }],
  [{ m: 0n, e: 100 }, { m: 0n, e: -100 }],
];
for (const [i, [a, b]] of dyadicPairs.entries()) {
  for (const op of ["dyadicAdd", "dyadicSub", "dyadicMul", "dyadicEq"]) {
    const output = judge[op](a, b);
    add({ op, a: wireDyadic(a), b: wireDyadic(b) },
      op === "dyadicEq" ? output : wireDyadic(output), `${op} pair ${i}`);
  }
  for (const d of [a, b, dyadicSub(a, b), dyadicAdd(a, b)]) {
    add({ op: "dyadicSign", a: wireDyadic(d) }, dyadicSign(d), `dyadicSign pair ${i}`);
  }
}

for (const [i, [xs, ys]] of judge.dotCases.entries()) {
  const pairs = xs.map((x, j) => ({
    a: wireDyadic(floatToDyadic(x)),
    b: wireDyadic(floatToDyadic(ys[j])),
  }));
  add({ op: "exactDot", pairs }, wireDyadic(exactDot(xs, ys)), `Dot2 case ${i}`);
}

const orientations = [
  ...judge.orientationCases,
  [-0, 0, Number.MIN_VALUE, 0, 0, Number.MIN_VALUE],
  [0, 0, -Number.MIN_VALUE, 0, 0, Number.MIN_VALUE],
  [Number.MAX_VALUE, 0, 0, Number.MAX_VALUE, -Number.MAX_VALUE, -Number.MAX_VALUE],
];
for (const [i, coords] of orientations.entries()) {
  const fields = Object.fromEntries(["ax", "ay", "bx", "by", "cx", "cy"].map(
    (name, j) => [name, wireDyadic(floatToDyadic(coords[j]))],
  ));
  add({ op: "orient2d", ...fields }, exactOrient2dSign(...coords), `orient2d case ${i}`);
}

const ceilingCases = [
  [0n, 1n], [1n, 0n], [1n, 1n], [Q - 1n, 1n], [Q, 1n], [Q + 1n, 1n],
  [Q / 2n, 2n], [Q + 1n, Q + 1n],
];
for (const [i, [diff, scale]] of ceilingCases.entries()) {
  scoreCase(diff, scale, `Ceiling case ${i}`);
}
const edgeCount = cases.length - edgeStart;

assert.equal(expSpec.mode, "horner_full");
assert.equal(coeffs.length, expSpec.expected_length);
const scale = BigInt(Math.round(Number(expSpec.error_scale)));
const record = expGrid.map(({ x, output, index }) => {
  let y = coeffs[coeffs.length - 1];
  for (let j = coeffs.length - 2; j >= 0; j--) y = y * x + coeffs[j];
  const yFix = floatToFixed128(y);
  assert(floatIsExact(y, yFix), `Horner result changed in fixed-point conversion at x=${x}`);
  return { index, yFix, diff: abs(yFix - output) };
});
const maxDiff = record.reduce((max, { diff }) => diff > max ? diff : max, 0n);
const scoreIndex = scoreCase(maxDiff, scale, "S-rec-exp measured score");

const results = runLean(cases);
for (const [i, { expected, label }] of cases.entries()) {
  assert.deepEqual(results[i], expected, label);
}
console.log(`Bit-for-bit grid matches: exp ${expGrid.length}/4097, sin ${sinGrid.length}/4097`);
console.log(`Adversarial and ceiling cases: ${edgeCount}/${edgeCount}`);

const leanMaxDiff = record.reduce((max, { index, yFix }) => {
  const diff = abs(yFix - BigInt(results[index]));
  return diff > max ? diff : max;
}, 0n);
assert.equal(leanMaxDiff, maxDiff, "Lean-reference record maximum");
const direct = directJudge(expSpec);
assert.equal(direct.ok, true);
assert.equal(direct.score, 405);
assert.equal(direct.measured_score, 405);
assert.equal(results[scoreIndex], "405");
console.log(`S-rec-exp measured score: JS judge ${direct.measured_score}, Lean ${results[scoreIndex]}`);

for (const [index, margin] of [
  [404n, maxDiff * scale - 404n * Q],
  [405n, 405n * Q - maxDiff * scale],
]) {
  // The margin is margin/(Q*scale); the proved oracle error is below 100/Q.
  assert(margin > 100n * scale * 10n ** 20n, `Insufficient margin to ${index}e-13`);
  const decimal = (Number(margin) / Number(Q * scale)).toExponential(12);
  const ratio = (Number(margin) / Number(100n * scale)).toExponential(6);
  console.log(`Margin to ${index}e-13: ${margin}/${Q * scale} = ${decimal} (${ratio} × 100/2^128)`);
}

const floorJudge = await loadJudge(replaceOnce(source, " + (FIX_ONE - 1n)", ""));
assert.equal(floorJudge.ceilScore(maxDiff, scale), 404n);
assert.notEqual(String(floorJudge.ceilScore(maxDiff, scale)), results[scoreIndex]);
assert.equal(floorJudge.ceilScore(1n, 1n), 0n);
assert.equal(ceilScore(1n, 1n), 1n);
console.log("Floor mutation rejected by the exact ceiling comparison");

const shortExpJudge = await loadJudge(replaceOnce(source, "k <= 34n", "k <= 8n"));
const mismatches = expGrid.filter(({ index, xFix }) => String(shortExpJudge.fixed128Exp(xFix)) !== results[index]);
assert(mismatches.length > 0, "The 8-term exp mutation survived the differential check");
console.log(`8-step exp mutation rejected at ${mismatches.length}/4097 grid points`);
