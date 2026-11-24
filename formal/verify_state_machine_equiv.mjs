#!/usr/bin/env node
// Differential equivalence check: hub/state_machine.mjs against the Lean 4 specification.
//
//   node formal/verify_state_machine_equiv.mjs [--seed=N] [--random=N]
//
// 1. Builds formal/lean with `lake build`. PFFormal.AxiomCheck fails the build if any listed
//    theorem depends on an axiom other than propext, Classical.choice and Quot.sound, which
//    rules out sorryAx and native_decide. The harness then re-runs the check to read the
//    axiom report and scans the Lean sources for escape hatches.
// 2. Generates deterministic random traces and hand-written adversarial traces.
// 3. Sends the whole batch to pf_state_check in one process, runs the real JavaScript on the
//    same inputs, and requires every output field to match exactly.
// 4. Runs mutants of hub/state_machine.mjs from a temporary directory. Each mutant must
//    disagree with the Lean model on at least one trace. Repository files are never written.
//
// Exit status is 0 when every check passes and 1 otherwise.

import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { pathToFileURL } from "node:url";

const ROOT = path.resolve(import.meta.dirname, "..");
const LEAN_DIR = path.join(ROOT, "formal", "lean");
const SM_PATH = path.join(ROOT, "hub", "state_machine.mjs");
const BIN = path.join(LEAN_DIR, ".lake", "build", "bin", "pf_state_check");
const STANDARD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);
// The headline theorems. Each must appear in the axiom report of PFFormal/AxiomCheck.lean.
const REQUIRED_THEOREMS = [
  "koth_monotone_best", "koth_monotone_best_replay", "koth_monotone_refuted", "koth_monotone_refuted_replay",
  "koth_anti_farming_ledger", "koth_anti_farming_record_points", "koth_anti_farming_bound_points",
  "koth_anti_farming_record_points_replay", "koth_contradiction_sticky_step", "koth_contradiction_sticky",
  "koth_contradiction_reachable", "koth_contradiction_replay", "koth_contradiction_order_independent",
  "koth_closed_exact_optimal", "koth_closed_denies", "claim_contradiction_sticky_step", "claim_contradiction_sticky",
  "claim_order_independent_contradiction", "barrier_never_overwrites_verdict", "seat_claim_bijection_release",
  "seat_claim_bijection_releaseClaim", "seat_claim_bijection_assign", "seat_claim_bijection_preserved", "Bij.iff",
  "Bij.single_owner", "trust_seal_and_conquered_sound", "trust_seal_contradiction_iff", "conquered_false_of_bad_seal",
  "conquered_record_default", "conquered_replay_default",
];

const args = Object.fromEntries(process.argv.slice(2).map((a) => {
  const [k, v] = a.replace(/^--/, "").split("=");
  return [k, v ?? true];
}));
const SEED = Number(args.seed ?? 20261123);
const RANDOM_SCALE = Number(args.random ?? 1);

let failures = 0;
function fail(msg) {
  failures++;
  console.error(`FAIL ${msg}`);
}
function info(msg) {
  console.log(msg);
}

// ---------------------------------------------------------------------------
// 1. Build and axiom audit
// ---------------------------------------------------------------------------

function findLake() {
  const candidates = [process.env.LAKE, path.join(os.homedir(), ".elan", "bin", "lake"), "lake"].filter(Boolean);
  for (const c of candidates) {
    const r = spawnSync(c, ["--version"], { encoding: "utf8" });
    if (!r.error && r.status === 0) return c;
  }
  return null;
}

function stripLeanComments(src) {
  let out = "";
  let depth = 0;
  for (let i = 0; i < src.length; i++) {
    if (src.startsWith("/-", i)) { depth++; i++; continue; }
    if (depth > 0 && src.startsWith("-/", i)) { depth--; i++; continue; }
    if (depth > 0) continue;
    if (src.startsWith("--", i)) { while (i < src.length && src[i] !== "\n") i++; out += "\n"; continue; }
    if (src[i] === '"') {
      // Skip string literals so that quoted words are not flagged.
      out += '""';
      i++;
      while (i < src.length && src[i] !== '"') { if (src[i] === "\\") i++; i++; }
      continue;
    }
    out += src[i];
  }
  return out;
}

function buildAndAudit() {
  const lake = findLake();
  if (!lake) {
    fail("lake was not found. Install elan (https://github.com/leanprover/elan) or set LAKE=/path/to/lake.");
    return false;
  }
  const t0 = Date.now();
  const build = spawnSync(lake, ["build"], { cwd: LEAN_DIR, encoding: "utf8", maxBuffer: 64 << 20 });
  if (build.status !== 0) {
    fail(`lake build failed:\n${build.stdout}\n${build.stderr}`);
    return false;
  }
  info(`lake build: ok (${Date.now() - t0} ms)`);

  // Scan the sources for escape hatches that the axiom check would not see in compiled code.
  const leanFiles = ["PFFormal.lean", "PFFormal/StateMachine.lean", "PFFormal/AxiomCheck.lean", "PFFormal/StateMachineCLI.lean"];
  for (const rel of leanFiles) {
    const code = stripLeanComments(fs.readFileSync(path.join(LEAN_DIR, rel), "utf8"));
    for (const word of ["sorry", "admit", "native_decide", "implemented_by", "extern", "unsafe", "partial"]) {
      if (new RegExp(`\\b${word}\\b`).test(code)) fail(`${rel} contains forbidden token \`${word}\``);
    }
    if (/^\s*(private\s+)?axiom\b/m.test(code)) fail(`${rel} declares an axiom`);
  }

  // Re-run the axiom report (the build already failed on any non-standard axiom).
  const report = spawnSync(lake, ["env", "lean", "PFFormal/AxiomCheck.lean"], { cwd: LEAN_DIR, encoding: "utf8", maxBuffer: 64 << 20 });
  if (report.status !== 0) {
    fail(`axiom check failed:\n${report.stdout}\n${report.stderr}`);
    return false;
  }
  const audited = new Map();
  for (const line of report.stdout.split("\n")) {
    const m = line.match(/AXIOMS (\S+): \[(.*)\]/);
    if (!m) continue;
    const axioms = m[2].split(",").map((s) => s.trim()).filter(Boolean);
    for (const ax of axioms) if (!STANDARD_AXIOMS.has(ax)) fail(`${m[1]} depends on non-standard axiom ${ax}`);
    audited.set(m[1], axioms);
  }
  for (const name of REQUIRED_THEOREMS) {
    if (!audited.has(`PF.${name}`)) fail(`required theorem PF.${name} is missing from the axiom audit`);
  }
  const used = [...new Set([...audited.values()].flat())].sort();
  info(`axiom audit: ${audited.size} theorems (${REQUIRED_THEOREMS.length} required by name); axioms used: ${used.join(", ") || "none"}; no sorryAx`);
  if (!fs.existsSync(BIN)) {
    fail(`missing ${BIN}`);
    return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// 2. Trace generation
// ---------------------------------------------------------------------------

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const rng = mulberry32(SEED);
const chance = (p) => rng() < p;
const int = (lo, hi) => lo + Math.floor(rng() * (hi - lo + 1));
const pick = (arr) => arr[Math.floor(rng() * arr.length)];
const clone = (x) => (x === undefined ? undefined : JSON.parse(JSON.stringify(x)));

const SEATS = ["donor-a", "donor-b", "ext-c", "contrib-d", "seat-1", "7"];
const SLUGS = ["erdos", "sn-rec", "m"];
const STMT_FILE = "missions/m/lean/Statement.lean";

// The real JavaScript module, used to build canonical file names and record states.
const real = await import(pathToFileURL(SM_PATH).href);

function genRecordConfig() {
  const record = {};
  const direction = pick(["min", "max", "min", "max", undefined, "sideways"]);
  if (direction !== undefined) record.direction = direction;
  if (chance(0.85)) record.start_target = int(0, 12);
  if (chance(0.5)) record.bound_floor = int(0, 3);
  if (chance(0.3)) record.score_max = int(6, 20);
  if (chance(0.15)) record.allow_bound = pick([true, false, null]);
  if (chance(0.12)) record.file_stem = pick(["Stem", ""]);
  if (chance(0.08)) record.claims_dir = "custom/Claims";
  if (chance(0.08)) record.artifact_ext = pick([".json", ""]);
  if (chance(0.12)) record.theorem_template = pick(["Hunt.{tag}.ok", "{tag}_{tag}", "fixed", ""]);
  if (chance(0.1)) record.literature_best = 3;
  return record;
}

function genRecordLemma({ status } = {}) {
  const lemma = {
    id: pick(["R-1", "HUNT", "sn-rec-13", "R"]),
    kind: "record",
    title: "A record hunt",
    status: status ?? pick(["conjecture", "conjecture", "in_work", "checked", "contradiction", "dead", "refuted", "weird"]),
    statement_file: STMT_FILE,
    record: genRecordConfig(),
  };
  if (chance(0.5)) lemma.claimed_by = pick([...SEATS, null]);
  if (chance(0.3)) lemma.updated_at = "2026-01-01";
  if (chance(0.2)) lemma.rung = int(0, 3);
  if (chance(0.1)) lemma.record = null;
  return lemma;
}

function cfgOf(lemma) {
  const c = lemma.record || {};
  return {
    min: c.direction !== "max",
    start: Number(c.start_target ?? 0),
    floor: Number(c.bound_floor ?? 0),
    scoreMax: Number(c.score_max ?? 100000),
  };
}

/** A canonical, fresh record submission, built with the real computeRecordTargets. */
function mkSub(slug, lemma, kind, score, opts = {}) {
  const t = real.computeRecordTargets(slug, lemma, kind, score);
  const sub = {
    kind,
    lemma_id: lemma.id,
    score,
    file: t.artifactFile,
    theorem: t.theoremName,
    _sub_file: t.submissionBasename,
    at: opts.at ?? `2026-02-${String(int(1, 28)).padStart(2, "0")}`,
    checker: {
      ok: true,
      judge: "lean4",
      by_seat: opts.seat ?? pick(SEATS),
      file_hash: `fh-${kind}-${score}-${int(0, 3)}`,
      statement_hash: "S1",
      core_hash: "C1",
      statement_frozen: true,
      axioms: ["propext", "Quot.sound"],
      duration_ms: int(0, 3) * 100,
    },
  };
  return sub;
}

/** Adversarial perturbations that keep `Number(score)` finite (the sort domain). */
function perturbSub(sub, slug, lemma) {
  const r = rng();
  if (r < 0.04) sub.score = String(sub.score);
  else if (r < 0.06) sub.score = `0${sub.score}`;
  else if (r < 0.07) sub.score = "";
  else if (r < 0.08) sub.score = null;
  else if (r < 0.10) delete sub._sub_file;
  else if (r < 0.11) sub._sub_file = "";
  else if (r < 0.13) sub._sub_file = `${lemma.id}.${sub.kind}.s${Number(sub.score) + 1}.json`;
  else if (r < 0.15) sub.file = `${sub.file}.bak`;
  else if (r < 0.16) delete sub.file;
  else if (r < 0.18) sub.theorem = "Forged.theorem";
  else if (r < 0.20) sub.checker.ok = false;
  else if (r < 0.21) delete sub.checker;
  else if (r < 0.24) sub.checker.statement_hash = pick(["S0-stale", null, ""]);
  else if (r < 0.26) delete sub.checker.core_hash;
  else if (r < 0.27) sub.checker.core_hash = "";
  else if (r < 0.29) sub.checker.by_seat = pick(["", undefined]);
  else if (r < 0.30) sub.at = pick(["", undefined]);
  else if (r < 0.31) delete sub.checker.axioms;
  else if (r < 0.32) sub.checker.duration_ms = pick([null, undefined, 0]);
  else if (r < 0.33) sub.checker.file_hash = pick(["", null, undefined]);
  else if (r < 0.34) {
    // Re-target to a different mission slug: the file names stop being canonical.
    const t = real.computeRecordTargets(slug === "m" ? "erdos" : "m", lemma, sub.kind, Number(sub.score));
    sub.file = t.artifactFile;
  }
  return JSON.parse(JSON.stringify(sub));
}

function genSubs(slug, lemma, n) {
  const { min, start, floor, scoreMax } = cfgOf(lemma);
  // A hidden optimum keeps most receipts consistent, which leads to closures.
  // A few deliberately inconsistent receipts cause contradictions.
  const opt = min ? int(0, Math.max(0, start)) : int(Math.max(start, floor), start + 6);
  const subs = [];
  for (let i = 0; i < n; i++) {
    const kind = chance(0.62) ? "record" : "record_bound";
    let score;
    if (kind === "record") {
      score = min ? int(opt, start + 2) : int(Math.max(0, opt - 6), opt);
      if (chance(0.25)) score = opt;
    } else {
      score = min ? int(Math.max(0, floor - 1), Math.max(0, opt - 1)) : int(opt + 1, opt + 4);
      if (chance(0.3)) score = min ? opt - 1 : opt + 1;
    }
    if (chance(0.08)) score = kind === "record" ? (min ? opt - 1 : opt + 1) : opt; // inconsistent
    if (chance(0.03)) score = pick([-1, scoreMax + 1, 0]);
    if (score < -1) score = -1;
    const sub = mkSub(slug, lemma, kind, score);
    subs.push(chance(0.35) ? perturbSub(sub, slug, lemma) : sub);
  }
  if (chance(0.1) && subs.length) subs.push(clone(pick(subs))); // exact duplicate
  return subs;
}

function genTs(subs) {
  const pairs = [];
  const seen = new Set();
  for (const s of subs) {
    if (!s._sub_file || seen.has(s._sub_file)) continue;
    seen.add(s._sub_file);
    if (chance(0.6)) pairs.push([s._sub_file, int(1, 6) * 1000]);
  }
  if (chance(0.1)) pairs.push(["unrelated.json", 1]);
  return pairs;
}

function genHashes() {
  const r = rng();
  if (r < 0.85) return { statementHashes: { [STMT_FILE]: "S1", other: "S9" }, coreHash: "C1" };
  if (r < 0.90) return { statementHashes: { [STMT_FILE]: "S2" }, coreHash: "C1" };
  if (r < 0.94) return { coreHash: "C1" };
  if (r < 0.97) return { statementHashes: { [STMT_FILE]: "S1" }, coreHash: "" };
  return { statementHashes: { [STMT_FILE]: "S1" } };
}

const cases = [];
const tags = [];
function addCase(tag, c) {
  // A JS Map keeps the last value for a repeated key; send the Lean model the same Map entries.
  if (c.op === "replay") c.gitAddedTs = [...new Map(c.gitAddedTs)];
  cases.push(c);
  tags.push(tag);
}

// --- Hand-written KotH scenarios ------------------------------------------------

function scenario(tag, lemmaPatch, steps, { hashes, slug = "m" } = {}) {
  const lemma = { id: "R-1", kind: "record", title: "Hunt", status: "conjecture", statement_file: STMT_FILE, claimed_by: "donor-a", ...lemmaPatch };
  const ts = [];
  const subs = steps.map(([kind, score, o = {}]) => {
    const sub = mkSub(slug, lemma, kind, score, { seat: o.seat ?? "donor-a", at: o.at ?? "2026-03-01" });
    if (o.ts != null) ts.push([sub._sub_file, o.ts]);
    if (o.mutate) o.mutate(sub);
    return JSON.parse(JSON.stringify(sub));
  });
  addCase(`replay:${tag}`, { op: "replay", slug, lemma, subs, gitAddedTs: ts, currentHashes: hashes ?? { statementHashes: { [STMT_FILE]: "S1" }, coreHash: "C1" } });
}

const MIN = (extra = {}) => ({ record: { direction: "min", start_target: 10, bound_floor: 0, ...extra } });
const MAX = (extra = {}) => ({ record: { direction: "max", start_target: 5, bound_floor: 0, ...extra } });

scenario("min improving chain", MIN(), [["record", 9, { seat: "donor-a", ts: 1 }], ["record", 7, { seat: "donor-b", ts: 2 }], ["record", 3, { seat: "ext-c", ts: 3 }]]);
scenario("max improving chain", MAX(), [["record", 5, { ts: 1 }], ["record", 6, { seat: "donor-b", ts: 2 }], ["record", 9, { seat: "ext-c", ts: 3 }]]);
scenario("initial target accepted exactly", MIN(), [["record", 10]]);
scenario("initial target missed (min)", MIN(), [["record", 11]]);
scenario("initial target missed (max)", MAX(), [["record", 4]]);
scenario("score 0 closes a min hunt", MIN(), [["record", 4, { ts: 1 }], ["record", 0, { seat: "donor-b", ts: 2 }]]);
scenario("score 0 after close is ignored", MIN(), [["record", 0, { ts: 1 }], ["record", 0, { seat: "donor-b", ts: 2, mutate: (s) => { s._sub_file = ""; } }]]);
scenario("exact best+step closure (min)", MIN(), [["record", 5, { ts: 1 }], ["record_bound", 4, { seat: "donor-b", ts: 2 }]]);
scenario("exact best+step closure (min, bound first)", MIN(), [["record_bound", 4, { seat: "donor-b", ts: 1 }], ["record", 5, { ts: 2 }]]);
scenario("exact best+step closure (max)", MAX(), [["record", 7, { ts: 1 }], ["record_bound", 8, { seat: "donor-b", ts: 2 }]]);
scenario("gap of two stays open (min)", MIN(), [["record", 6], ["record_bound", 4]]);
scenario("duplicate score, second seat ignored", MIN(), [["record", 6, { seat: "donor-a", ts: 1 }], ["record", 6, { seat: "donor-b", ts: 2, mutate: (s) => { delete s._sub_file; } }]]);
scenario("duplicate submission file deduplicated", MIN(), [["record", 6, { seat: "donor-a" }], ["record", 6, { seat: "donor-b" }]]);
scenario("non-improving score ignored", MIN(), [["record", 6, { ts: 1 }], ["record", 8, { seat: "donor-b", ts: 2 }]]);
scenario("stale statement hash", MIN(), [["record", 6, { mutate: (s) => { s.checker.statement_hash = "OLD"; } }], ["record", 7]]);
scenario("missing core hash", MIN(), [["record", 6, { mutate: (s) => { delete s.checker.core_hash; } }]]);
scenario("current core hash missing", MIN(), [["record", 6]], { hashes: { statementHashes: { [STMT_FILE]: "S1" } } });
scenario("statement hash table missing", MIN(), [["record", 6]], { hashes: { coreHash: "C1" } });
scenario("crossing record then bound (min)", MIN(), [["record", 5, { ts: 1 }], ["record_bound", 6, { seat: "donor-b", ts: 2 }]]);
scenario("crossing bound then record (min)", MIN(), [["record_bound", 6, { seat: "donor-b", ts: 1 }], ["record", 5, { ts: 2 }]]);
scenario("crossing at equal score (min, rec first)", MIN(), [["record", 5, { ts: 1 }], ["record_bound", 5, { seat: "donor-b", ts: 2 }]]);
scenario("crossing at equal score (min, bound first)", MIN(), [["record_bound", 5, { seat: "donor-b", ts: 1 }], ["record", 5, { ts: 2 }]]);
scenario("crossing record then bound (max)", MAX(), [["record", 8, { ts: 1 }], ["record_bound", 7, { seat: "donor-b", ts: 2 }]]);
scenario("crossing bound then record (max)", MAX(), [["record_bound", 7, { seat: "donor-b", ts: 1 }], ["record", 8, { ts: 2 }]]);
scenario("crossing without timestamps", MIN(), [["record_bound", 6, { seat: "donor-b" }], ["record", 5]]);
scenario("receipts after contradiction", MIN(), [["record", 5, { ts: 1 }], ["record_bound", 6, { ts: 2 }], ["record", 2, { seat: "donor-b", ts: 3 }], ["record_bound", 1, { seat: "ext-c", ts: 4 }]]);
scenario("out-of-order git timestamps beat score order", MIN(), [["record", 3, { seat: "donor-a", ts: 1 }], ["record", 5, { seat: "donor-b", ts: 2 }]]);
scenario("tied timestamps fall back to improving order", MIN(), [["record", 3, { seat: "donor-a", ts: 7 }], ["record", 5, { seat: "donor-b", ts: 7 }]]);
scenario("missing timestamps sort last", MIN(), [["record", 3, { seat: "donor-a" }], ["record", 5, { seat: "donor-b", ts: 9 }]]);
scenario("multi-seat delta awards", MIN(), [["record", 9, { seat: "donor-a", ts: 1 }], ["record", 6, { seat: "donor-b", ts: 2 }], ["record", 4, { seat: "donor-a", ts: 3 }], ["record_bound", 1, { seat: "ext-c", ts: 4 }], ["record_bound", 2, { seat: "donor-b", ts: 5 }]]);
scenario("pre-existing contradiction status", { ...MIN(), status: "contradiction" }, [["record", 9, { ts: 1 }], ["record", 4, { seat: "donor-b", ts: 2 }]]);
scenario("pre-existing contradiction with closure", { ...MIN(), status: "contradiction" }, [["record", 0, { ts: 1 }]]);
scenario("bounds disabled", MIN({ allow_bound: false }), [["record_bound", 3], ["record", 5]]);
scenario("bound only hunt", MIN(), [["record_bound", 2, { ts: 1 }], ["record_bound", 3, { seat: "donor-b", ts: 2 }], ["record_bound", 1, { ts: 3 }]]);
scenario("bound floor credit", MIN({ bound_floor: 2 }), [["record_bound", 2, { ts: 1 }], ["record_bound", 1, { ts: 2 }]]);
scenario("score above score_max", MIN({ score_max: 8 }), [["record", 9], ["record", 8]]);
scenario("string scores", MIN(), [["record", 6, { mutate: (s) => { s.score = "6"; } }], ["record", 5, { mutate: (s) => { s.score = "05"; } }]]);
scenario("negative score", MIN(), [["record", -1]]);
scenario("missing seat credited to unknown", MIN(), [["record", 7, { mutate: (s) => { delete s.checker.by_seat; } }]]);
scenario("forged theorem name", MIN(), [["record", 2, { mutate: (s) => { s.theorem = "R_1_s1.record"; } }]]);
scenario("max hunt with bound floor clamp", MAX({ start_target: 0 }), [["record_bound", 0, { ts: 1 }], ["record", 0, { ts: 2 }]]);
scenario("non-record lemma", { kind: undefined, record: { direction: "min", start_target: 3 } }, [["record", 2]]);
scenario("checked status is reset", { ...MIN(), status: "checked" }, [["record", 9]]);

// --- Random KotH replays -----------------------------------------------------

for (let i = 0; i < 700 * RANDOM_SCALE; i++) {
  const slug = pick(SLUGS);
  const lemma = genRecordLemma();
  const subs = genSubs(slug, lemma, int(0, 9));
  // Shuffle the input order: the replay sort must make it irrelevant except for ties.
  for (let j = subs.length - 1; j > 0; j--) { const k = int(0, j); [subs[j], subs[k]] = [subs[k], subs[j]]; }
  addCase("replay:random", { op: "replay", slug, lemma, subs, gitAddedTs: genTs(subs), currentHashes: genHashes() });
}

// --- Standard claim lifecycle traces ---------------------------------------------

const HASHES = ["h-proof", "h-ref", "h-other"];

function genStdLemma() {
  const lemma = { id: pick(["C-1", "T-001", "L"]), title: "A claim", status: pick(["conjecture", "conjecture", "in_work", "checked", "refuted", "dead", "contradiction", "weird"]), rung: int(0, 4), deps: [] };
  if (chance(0.5)) lemma.claimed_by = pick([...SEATS, null]);
  if (chance(0.5)) lemma.updated_at = pick(["2026-01-01", null]);
  if (chance(0.15)) lemma.kind = pick(["claim", "lemma"]);
  const ck = rng();
  if (ck < 0.4) lemma.checker = { ok: chance(0.8), by_seat: pick(SEATS), ...(chance(0.8) && { file_hash: pick(HASHES) }), ...(chance(0.3) && { statement_frozen: chance(0.7) }) };
  else if (ck < 0.55) lemma.checker = null;
  const rf = rng();
  if (rf < 0.3) lemma.refutation = { by_seat: pick(SEATS), ...(chance(0.8) && { file_hash: pick(HASHES) }) };
  else if (rf < 0.45) lemma.refutation = null;
  const au = rng();
  if (au < 0.35) lemma.audit = { status: pick(["faithful", "flagged", "pending"]), by_seat: "audit-x", ...(chance(0.7) && { file_hash: pick([...HASHES, ""]) }) };
  else if (au < 0.5) lemma.audit = null;
  if (chance(0.2)) lemma.epitaph = pick([null, { wall: "Barrier", by_seat: "seat-1" }]);
  for (const k of ["lean_file", "theorem_name", "registered_statement", "statement", "verified_signature"]) {
    if (chance(0.3)) lemma[k] = pick(["", "x.lean", "Stmt", null]);
  }
  if (chance(0.05)) lemma.record_state = null;
  return lemma;
}

function genStdEvent() {
  const kind = pick(["claim", "claim", "proof", "proof", "refutation", "refutation", "rule_dead", "audit", "audit", "record", "record_bound", "bogus"]);
  const e = { kind, lemma_id: "C-1" };
  if (chance(0.6)) e.at = pick(["2026-05-01", "2026-05-02", null]);
  if (kind === "claim") { if (chance(0.9)) e.seat = pick(SEATS); }
  if (kind === "proof") {
    if (chance(0.92)) e.checker = { ok: chance(0.85), by_seat: pick(SEATS), file_hash: pick(HASHES), ...(chance(0.3) && { statement_frozen: true }) };
    if (chance(0.5)) e.file = pick(["P.lean", ""]);
    if (chance(0.5)) e.theorem = pick(["P.main", ""]);
    if (chance(0.4)) e.signature = pick(["theorem main : True", ""]);
  }
  if (kind === "refutation") {
    const r = rng();
    if (r < 0.85) e.refutation = { by_seat: pick(SEATS), file_hash: pick(HASHES), summary: "counterexample" };
    else if (r < 0.92) e.refutation = null;
  }
  if (kind === "rule_dead") {
    const r = rng();
    if (r < 0.8) e.epitaph = { wall: "Relativization", by_seat: "seat-1" };
    else if (r < 0.9) e.epitaph = null;
  }
  if (kind === "audit") {
    const r = rng();
    if (r < 0.9) e.audit = { status: pick(["faithful", "flagged"]), by_seat: "audit-x", ...(chance(0.85) && { file_hash: pick(HASHES) }) };
    else if (r < 0.95) e.audit = null;
  }
  return e;
}

function genCtx() {
  const r = rng();
  if (r < 0.3) return undefined;
  if (r < 0.4) return {};
  if (r < 0.6) return { mode: "preflight" };
  if (r < 0.9) return { mode: "replay" };
  return { mode: "writeback" };
}

for (let i = 0; i < 450 * RANDOM_SCALE; i++) {
  const steps = [];
  for (let j = int(1, 7); j > 0; j--) steps.push({ event: genStdEvent(), ctx: genCtx() });
  addCase("claim:random", { op: "claimTrace", lemma: genStdLemma(), steps });
}

// Hand-written lifecycle traces.
const PROOF = { kind: "proof", checker: { ok: true, by_seat: "donor-a", file_hash: "h-proof" }, file: "P.lean", theorem: "P.main", signature: "theorem main : True", at: "2026-06-01" };
const REFUTE = { kind: "refutation", refutation: { by_seat: "donor-b", file_hash: "h-ref" }, at: "2026-06-02" };
const DEAD = { kind: "rule_dead", epitaph: { wall: "Barrier", by_seat: "seat-1" }, at: "2026-06-03" };
const AUDIT_OK = { kind: "audit", audit: { status: "faithful", file_hash: "h-proof", by_seat: "audit-x" } };
const AUDIT_BAD = { kind: "audit", audit: { status: "faithful", file_hash: "h-other", by_seat: "audit-x" } };
const CLAIM = (seat) => ({ kind: "claim", seat, at: "2026-06-04" });
const base = { id: "C-1", status: "conjecture", claimed_by: "donor-a", title: "Claim" };
for (const mode of [undefined, "replay", "writeback"]) {
  const ctx = mode && { mode };
  addCase("claim:proof-then-refutation", { op: "claimTrace", lemma: base, steps: [PROOF, REFUTE, PROOF, REFUTE, DEAD, AUDIT_OK, CLAIM("donor-b")].map((event) => ({ event, ctx })) });
  addCase("claim:refutation-then-proof", { op: "claimTrace", lemma: base, steps: [REFUTE, PROOF, REFUTE, DEAD, CLAIM("donor-b"), AUDIT_OK].map((event) => ({ event, ctx })) });
  addCase("claim:barrier-between", { op: "claimTrace", lemma: base, steps: [PROOF, DEAD, REFUTE, DEAD].map((event) => ({ event, ctx })) });
  addCase("claim:dead-then-proof", { op: "claimTrace", lemma: base, steps: [DEAD, PROOF, AUDIT_BAD, AUDIT_OK, REFUTE].map((event) => ({ event, ctx })) });
  addCase("claim:duplicate-receipts", { op: "claimTrace", lemma: base, steps: [PROOF, PROOF, REFUTE, REFUTE].map((event) => ({ event, ctx })) });
}
addCase("claim:preflight-matrix", { op: "claimTrace", lemma: base, steps: [PROOF, REFUTE, DEAD, CLAIM("ext-c")].map((event) => ({ event, ctx: { mode: "preflight" } })) });
for (const status of ["checked", "refuted", "contradiction"]) {
  addCase(`claim:barrier-vs-${status}`, { op: "claimTrace", lemma: { ...base, status }, steps: [{ event: DEAD }, { event: DEAD, ctx: { mode: "replay" } }] });
}

// --- Record lemmas through transitionClaim: preflight and direct replay-mode steps ----

function recordStateLemma() {
  const slug = pick(SLUGS);
  const lemma = genRecordLemma();
  const subs = genSubs(slug, lemma, int(0, 6));
  const ts = new Map(genTs(subs));
  const out = real.replayRecordSubmissions(slug, lemma, subs, { gitAddedTs: ts, currentHashes: genHashes() });
  const l = JSON.parse(JSON.stringify(out));
  // Adversarial edits, including inconsistent flag combinations.
  if (chance(0.15)) l.record_state.contradiction = !l.record_state.contradiction;
  if (chance(0.15)) l.record_state.closed = !l.record_state.closed;
  if (chance(0.2)) l.status = pick(["conjecture", "in_work", "checked", "contradiction"]);
  return { slug, lemma: l };
}

for (let i = 0; i < 350 * RANDOM_SCALE; i++) {
  const { slug, lemma } = recordStateLemma();
  const { min, start } = cfgOf(lemma);
  const steps = [];
  for (let j = int(1, 6); j > 0; j--) {
    const r = rng();
    if (r < 0.55) {
      const kind = chance(0.6) ? "record" : "record_bound";
      const score = Math.max(0, start + int(-6, 3) * (min ? 1 : -1));
      let event = mkSub(slug, lemma, kind, score);
      if (chance(0.3)) event = perturbSub(event, slug, lemma);
      const ctx = { mode: "replay", missionSlug: chance(0.95) ? slug : "other", statementHash: chance(0.9) ? "S1" : pick([undefined, "S2"]), coreHash: chance(0.92) ? "C1" : pick([undefined, ""]), gitTs: chance(0.5) ? int(1, 9) : undefined };
      const opp = rng();
      if (opp < 0.5) ctx.opposingScore = Math.max(0, start + int(-6, 3) * (min ? 1 : -1));
      else if (opp < 0.6) ctx.opposingScore = null;
      steps.push({ event, ctx: JSON.parse(JSON.stringify(ctx)) });
    } else {
      const event = pick([{ kind: "claim", seat: pick(SEATS) }, { kind: "record" }, { kind: "record_bound" }, PROOF, REFUTE, DEAD, AUDIT_OK, { kind: "bogus" }]);
      steps.push({ event, ctx: pick([undefined, { mode: "preflight" }, { mode: "writeback" }, { mode: "replay" }]) });
    }
  }
  addCase("claim:record-hunt", { op: "claimTrace", lemma, steps });
}

// --- Seat assignment traces ----------------------------------------------------

function genSeatState() {
  const nSeats = int(1, 5);
  const nLemmas = int(1, 5);
  const seats = Array.from({ length: nSeats }, (_, i) => ({ id: `donor-${i}`, name: `Seat ${i}`, status: "idle", current_lemma: null }));
  const lemmas = Array.from({ length: nLemmas }, (_, i) => ({ id: `L${i}`, title: `L${i}`, status: pick(["conjecture", "conjecture", "in_work", "checked", "dead", "contradiction", "refuted"]), claimed_by: null }));
  if (chance(0.3)) {
    lemmas.push({ id: "REC", kind: "record", status: "conjecture", record_state: { direction: "min", best: null, refuted: null, next_target: 3, closed: chance(0.5), contradiction: chance(0.3), history: [], points_by_seat: {} } });
  }
  // A consistent partial bijection.
  const free = lemmas.filter((l) => l.status === "in_work" || l.status === "conjecture");
  for (const seat of seats) {
    if (!free.length || chance(0.4)) continue;
    const l = free.splice(int(0, free.length - 1), 1)[0];
    seat.current_lemma = l.id;
    seat.status = pick(["working", "checking"]);
    l.claimed_by = seat.id;
    l.status = "in_work";
  }
  // Adversarial inconsistencies.
  if (chance(0.15)) pick(seats).current_lemma = pick(lemmas).id;
  if (chance(0.1)) pick(lemmas).claimed_by = pick(seats).id;
  if (chance(0.05)) pick(seats).current_lemma = "ghost";
  if (chance(0.05)) seats.push({ ...clone(seats[0]), name: "duplicate id" });
  for (const l of lemmas) if (l.status === "in_work" && chance(0.1)) l.claimed_by = undefined;
  return JSON.parse(JSON.stringify({ seats, lemmas, programs: [{ id: "p" }] }));
}

for (let i = 0; i < 400 * RANDOM_SCALE; i++) {
  const state = genSeatState();
  const seatIds = [...state.seats.map((s) => s.id), "ghost-seat"];
  const lemmaIds = [...state.lemmas.map((l) => l.id), "ghost-claim"];
  const steps = [];
  for (let j = int(1, 8); j > 0; j--) {
    const r = rng();
    if (r < 0.6) steps.push({ fn: "assign", seat: chance(0.95) ? pick(seatIds.slice(0, -1)) : "ghost-seat", lemma: chance(0.95) ? pick(lemmaIds.slice(0, -1)) : "ghost-claim" });
    else if (r < 0.8) steps.push({ fn: "release", seat: chance(0.95) ? pick(seatIds.slice(0, -1)) : "ghost-seat" });
    else steps.push({ fn: "releaseClaim", lemma: pick(lemmaIds) });
  }
  addCase("seat:random", { op: "seatTrace", state, steps });
}
addCase("seat:transfer", {
  op: "seatTrace",
  state: {
    seats: [{ id: "donor-a", current_lemma: "C", status: "checking" }, { id: "donor-b", current_lemma: "D", status: "working" }],
    lemmas: [{ id: "C", status: "in_work", claimed_by: "donor-a" }, { id: "D", status: "in_work", claimed_by: "donor-b" }],
  },
  steps: [{ fn: "assign", seat: "donor-a", lemma: "D" }, { fn: "release", seat: "donor-a" }, { fn: "assign", seat: "absent", lemma: "D" }, { fn: "assign", seat: "donor-a", lemma: "absent" }],
});

// --- Trust seal and rung conquest ---------------------------------------------------

const EXPECTS = ["__undefined__", "proof", "refutation", "either", "record_any", "record_closed", { record_at_most: 4 }, { record_at_most: 9 }, { record_at_least: 6 }, { record_at_least: 2 }, { record_at_most: "5" }, { record_at_most: 2.5 }, { record_at_most: 3, record_at_least: 3 }, {}, [], null, "bogus"];

for (let i = 0; i < 500 * RANDOM_SCALE; i++) {
  let lemma;
  const r = rng();
  if (r < 0.5) lemma = genStdLemma();
  else if (r < 0.95) lemma = recordStateLemma().lemma;
  else lemma = null;
  if (lemma && chance(0.1)) lemma.record_state = { direction: pick(["min", "max", "sideways"]), best: null, refuted: null, next_target: null, closed: chance(0.5), contradiction: chance(0.5), history: [], points_by_seat: {} };
  addCase("seal:random", { op: "seal", lemma, expects: EXPECTS });
}

// Hand-written seal cases: inconsistent flag combinations and every audit/hash variant.
{
  const closed = JSON.parse(JSON.stringify(real.replayRecordSubmissions("m", { id: "R", kind: "record", status: "conjecture", statement_file: STMT_FILE, record: { direction: "min", start_target: 3 } },
    [mkSub("m", { id: "R", kind: "record", record: { direction: "min", start_target: 3 } }, "record", 0, { seat: "donor-a" })],
    { gitAddedTs: new Map(), currentHashes: { statementHashes: { [STMT_FILE]: "S1" }, coreHash: "C1" } })));
  const rsVariants = [
    { closed: true, contradiction: false }, { closed: true, contradiction: true },
    { closed: false, contradiction: true }, { closed: false, contradiction: false },
  ];
  for (const status of ["checked", "contradiction", "conjecture"]) {
    for (const v of rsVariants) {
      addCase("seal:adversarial", { op: "seal", lemma: { ...closed, status, record_state: { ...closed.record_state, ...v } }, expects: EXPECTS });
    }
  }
  for (const status of ["checked", "refuted", "contradiction", "in_work"]) {
    for (const audit of [undefined, { status: "flagged", file_hash: "h-proof" }, { status: "flagged", file_hash: "h-old" }, { status: "flagged" }, { status: "faithful", file_hash: "h-proof" }, { status: "faithful", file_hash: "h-old" }]) {
      for (const frozen of [false, true]) {
        const lemma = { id: "C-1", status, checker: { ok: true, file_hash: "h-proof", statement_frozen: frozen }, ...(audit && { audit }) };
        addCase("seal:adversarial", { op: "seal", lemma, expects: EXPECTS });
      }
    }
  }
}

for (let i = 0; i < 150 * RANDOM_SCALE; i++) {
  addCase("targets:random", { op: "targets", slug: pick(SLUGS), lemma: genRecordLemma(), kind: pick(["record", "record_bound"]), score: int(0, 30) });
}

// ---------------------------------------------------------------------------
// 3. Run both implementations and compare
// ---------------------------------------------------------------------------

const roundtrip = (x) => (x === undefined ? undefined : JSON.parse(JSON.stringify(x)));
function sortKeys(x) {
  if (Array.isArray(x)) return x.map(sortKeys);
  if (x && typeof x === "object") return Object.fromEntries(Object.keys(x).sort().map((k) => [k, sortKeys(x[k])]));
  return x;
}
const canon = (x) => JSON.stringify(sortKeys(x));

function applyOverlay(baseObj, ov) {
  const out = { ...baseObj };
  for (const [k, v] of Object.entries(ov)) if (k !== "_undef") out[k] = v;
  for (const k of ov._undef) delete out[k];
  return out;
}
function applyStateOverlay(baseState, ov) {
  if (ov.seats.length !== baseState.seats.length || ov.lemmas.length !== baseState.lemmas.length) return { length_mismatch: true };
  return { ...baseState, seats: baseState.seats.map((s, i) => applyOverlay(s, ov.seats[i])), lemmas: baseState.lemmas.map((l, i) => applyOverlay(l, ov.lemmas[i])) };
}

/** Run one case through a JavaScript implementation and the Lean result; return the mismatches. */
function compareCase(sm, c, lean) {
  if (lean.error) return [`lean rejected the input: ${lean.error}`];
  const diffs = [];
  const check = (label, actual, expected) => {
    const a = canon(actual);
    const e = canon(expected);
    if (a !== e) diffs.push(`${label}\n    js:   ${a}\n    lean: ${e}`);
  };
  const guard = (label, fn) => {
    try { return { value: fn() }; } catch (err) { diffs.push(`${label}: js threw ${err.message}`); return null; }
  };
  if (c.op === "replay") {
    const r = guard("replay", () => sm.replayRecordSubmissions(c.slug, clone(c.lemma), clone(c.subs), { gitAddedTs: new Map(c.gitAddedTs), currentHashes: clone(c.currentHashes) }));
    if (r) check("replay lemma", roundtrip(r.value), applyOverlay(roundtrip(c.lemma), lean.lemma));
  } else if (c.op === "claimTrace") {
    let jsLemma = clone(c.lemma);
    let expected = roundtrip(c.lemma);
    c.steps.forEach((s, i) => {
      if (diffs.length) return;
      const r = guard(`step ${i}`, () => sm.transitionClaim(jsLemma, clone(s.event), s.ctx === undefined ? undefined : clone(s.ctx)));
      if (!r) return;
      const lo = lean.steps[i];
      expected = applyOverlay(expected, lo.lemma);
      check(`step ${i} (${s.event.kind}, mode ${s.ctx?.mode})`, { ok: r.value.ok, reason: r.value.ok ? null : r.value.reason, lemma: roundtrip(r.value.lemma) }, { ok: lo.ok, reason: lo.reason, lemma: expected });
      jsLemma = r.value.lemma;
    });
  } else if (c.op === "seatTrace") {
    let jsState = clone(c.state);
    let expected = roundtrip(c.state);
    c.steps.forEach((s, i) => {
      if (diffs.length) return;
      const lo = lean.steps[i];
      let actual;
      try {
        const fn = { assign: () => sm.assignSeatClaim(jsState, s.seat, s.lemma), release: () => sm.releaseSeatClaim(jsState, s.seat), releaseClaim: () => sm.releaseClaimSeats(jsState, s.lemma) }[s.fn];
        jsState = fn();
        actual = { ok: true, state: roundtrip(jsState) };
      } catch (err) {
        actual = { ok: false, error: err.message };
      }
      if (lo.ok) expected = applyStateOverlay(expected, lo.state);
      check(`seat step ${i} (${s.fn} ${s.seat ?? ""} ${s.lemma ?? ""})`, actual, lo.ok ? { ok: true, state: expected } : { ok: false, error: lo.error });
    });
  } else if (c.op === "seal") {
    const lemma = clone(c.lemma);
    const seal = lemma ? guard("seal", () => sm.computeTrustSeal(lemma)) : { value: null };
    const conquered = c.expects.map((e, i) => guard(`expect ${i}`, () => (e === "__undefined__" ? sm.isRungConquered(lemma) : sm.isRungConquered(lemma, clone(e))))?.value);
    if (seal) check("seal", { seal: seal.value, conquered }, { seal: lean.seal, conquered: lean.conquered });
  } else if (c.op === "targets") {
    const t = guard("targets", () => sm.computeRecordTargets(c.slug, clone(c.lemma), c.kind, c.score));
    if (t) check("targets", t.value, { tag: lean.tag, artifactFile: lean.artifactFile, submissionBasename: lean.submissionBasename, submissionFile: lean.submissionFile, theoremName: lean.theoremName });
  }
  return diffs;
}

function runLean() {
  const t0 = Date.now();
  const r = spawnSync(BIN, [], { input: JSON.stringify({ cases }), encoding: "utf8", maxBuffer: 1 << 30 });
  if (r.status !== 0) throw new Error(`pf_state_check exited ${r.status}: ${r.stderr}`);
  const results = JSON.parse(r.stdout).results;
  if (results.length !== cases.length) throw new Error("pf_state_check returned the wrong number of results");
  return { results, ms: Date.now() - t0 };
}

function coverage(sm) {
  const stats = { closed: 0, contradiction: 0, accepted: 0, ignored: 0, stale: 0, pointsAwarded: 0 };
  cases.forEach((c) => {
    if (c.op === "replay") {
      const out = sm.replayRecordSubmissions(c.slug, clone(c.lemma), clone(c.subs), { gitAddedTs: new Map(c.gitAddedTs), currentHashes: clone(c.currentHashes) });
      const rs = out.record_state;
      if (rs.closed) stats.closed++;
      if (rs.contradiction) stats.contradiction++;
      for (const h of rs.history) {
        if (h.state === "accepted") stats.accepted++;
        if (h.state === "ignored_non_improving") stats.ignored++;
        if (h.state === "stale_statement") stats.stale++;
        if (h.points > 0) stats.pointsAwarded++;
      }
    }
  });
  return stats;
}

let leanRun;
const totalSteps = cases.reduce((n, c) => n + (c.steps?.length ?? (c.op === "replay" ? c.subs.length : c.expects?.length ?? 1)), 0);

if (buildAndAudit()) {
  leanRun = runLean();
  info(`pf_state_check: ${cases.length} traces (${totalSteps} steps) in ${leanRun.ms} ms`);

  let mismatched = 0;
  const byTag = {};
  cases.forEach((c, i) => {
    const diffs = compareCase(real, c, leanRun.results[i]);
    const tag = tags[i];
    byTag[tag] ??= { n: 0, bad: 0 };
    byTag[tag].n++;
    if (diffs.length) {
      byTag[tag].bad++;
      mismatched++;
      if (mismatched <= 5) fail(`trace #${i} [${tag}] differs:\n  ${diffs.join("\n  ")}\n  input: ${JSON.stringify(c).slice(0, 2000)}`);
    }
  });
  const families = Object.entries(byTag).reduce((acc, [tag, v]) => {
    const fam = tag.split(":")[0];
    acc[fam] ??= { n: 0, bad: 0 };
    acc[fam].n += v.n;
    acc[fam].bad += v.bad;
    return acc;
  }, {});
  for (const [fam, v] of Object.entries(families)) info(`  ${fam.padEnd(8)} ${String(v.n).padStart(5)} traces, ${v.bad} mismatches`);
  if (mismatched) fail(`${mismatched} of ${cases.length} traces differ between hub/state_machine.mjs and the Lean model`);
  else info(`equivalence: all ${cases.length} traces (${totalSteps} steps) match exactly`);
  if (cases.length < 1500) fail(`expected at least 1500 traces, generated ${cases.length}`);

  const cov = coverage(real);
  info(`coverage: ${cov.closed} closed hunts, ${cov.contradiction} contradicted hunts, ${cov.accepted} accepted / ${cov.ignored} ignored / ${cov.stale} stale receipts, ${cov.pointsAwarded} point awards`);
  if (cov.closed < 50 || cov.contradiction < 50 || cov.accepted < 300 || cov.ignored < 50 || cov.stale < 30) fail("random generator coverage is below the required minimums");

  // -------------------------------------------------------------------------
  // 4. Mutation self-checks
  // -------------------------------------------------------------------------
  const MUTANTS = [
    { name: "anti-farming: +1 on every improvement", family: "a", from: "points = margin + (rs[field] ? 0 : 1);", to: "points = margin + 1;" },
    { name: "anti-farming: award the raw score", family: "a", from: "points = margin + (rs[field] ? 0 : 1);", to: "points = score + (rs[field] ? 0 : 1);" },
    { name: "stickiness: drop the contradicted-hunt early return", family: "b", from: "if (rs.contradiction) {", to: "if (false) {" },
    { name: "order independence: bounds ignore earlier records", family: "b", from: 'opposingScore: strongest[record ? "record_bound" : "record"],', to: "opposingScore: record ? strongest.record_bound : null," },
    { name: "claim stickiness: only block claims after contradiction", family: "b", from: 'if (contradiction && kind !== "audit") return deny', to: 'if (contradiction && kind === "claim") return deny' },
    { name: "conquest: contradiction counts as conquered", family: "c", from: 'if (seal === "flagged" || seal === "contradiction") return false;', to: 'if (seal === "flagged") return false;' },
    { name: "conquest: flagged counts as conquered", family: "c", from: 'if (seal === "flagged" || seal === "contradiction") return false;\n  if (lemma.kind === "record") {', to: 'if (seal === "contradiction") return false;\n  if (seal === "flagged") return true;\n  if (lemma.kind === "record") {' },
    { name: "conquest: contradicted hunt state ignored", family: "c", from: "if (!rs || rs.contradiction) return false;", to: "if (!rs) return false;", alsoFrom: 'if (seal === "flagged" || seal === "contradiction") return false;', alsoTo: 'if (seal === "flagged") return false;' },
  ];
  const source = fs.readFileSync(SM_PATH, "utf8");
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "pf-mutant-"));
  const caughtFamilies = new Set();
  try {
    for (const [idx, m] of MUTANTS.entries()) {
      let mutated = source;
      for (const [from, to] of [[m.from, m.to], ...(m.alsoFrom ? [[m.alsoFrom, m.alsoTo]] : [])]) {
        if (mutated.split(from).length !== 2) { fail(`mutant "${m.name}": pattern not found exactly once`); mutated = null; break; }
        mutated = mutated.replace(from, to);
      }
      if (!mutated) continue;
      const dir = path.join(tmp, `m${idx}`);
      fs.mkdirSync(dir);
      const file = path.join(dir, "state_machine.mjs");
      fs.writeFileSync(file, mutated);
      const mod = await import(pathToFileURL(file).href);
      const killedBy = {};
      cases.forEach((c, i) => {
        if (compareCase(mod, c, leanRun.results[i]).length) {
          const fam = tags[i].split(":")[0];
          killedBy[fam] = (killedBy[fam] || 0) + 1;
        }
      });
      const total = Object.values(killedBy).reduce((a, b) => a + b, 0);
      if (total === 0) fail(`mutant (${m.family}) "${m.name}" survived`);
      else {
        caughtFamilies.add(m.family);
        info(`mutant (${m.family}) caught: ${m.name}: ${total} traces differ (${Object.entries(killedBy).map(([k, v]) => `${k} ${v}`).join(", ")})`);
      }
    }
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
  for (const fam of ["a", "b", "c"]) if (!caughtFamilies.has(fam)) fail(`no mutant of family (${fam}) was caught`);
}

// Known divergence (informational): seat names inherited from Object.prototype.
// `points_by_seat[seat] || 0` reads an inherited property, such as `constructor`, so the ledger
// concatenates strings. The Lean model reads own properties only, which is the intended
// semantics. The generator therefore keeps such names out of the differential domain.
if (leanRun) {
  const lemma = { id: "R", kind: "record", status: "conjecture", statement_file: STMT_FILE, record: { direction: "min", start_target: 10 } };
  const c = { op: "replay", slug: "m", lemma, subs: [mkSub("m", lemma, "record", 9, { seat: "constructor" }), mkSub("m", lemma, "record", 7, { seat: "constructor" })].map(clone), gitAddedTs: [], currentHashes: { statementHashes: { [STMT_FILE]: "S1" }, coreHash: "C1" } };
  const r = spawnSync(BIN, [], { input: JSON.stringify({ cases: [c] }), encoding: "utf8" });
  const leanPts = JSON.parse(r.stdout).results[0].lemma.record_state.points_by_seat;
  const jsPts = real.replayRecordSubmissions(c.slug, clone(lemma), clone(c.subs), { gitAddedTs: new Map(), currentHashes: c.currentHashes }).record_state.points_by_seat;
  const same = canon(leanPts) === canon(jsPts);
  info(`known divergence (prototype-key seat "constructor"): spec ${JSON.stringify(leanPts)}, js ${JSON.stringify(jsPts)}${same ? " (now fixed in JS)" : " (product bug, see formal/lean/PFFormal/StateMachine.lean header)"}`);
}

if (failures) {
  console.error(`\nverify_state_machine_equiv: ${failures} failure(s)`);
  process.exit(1);
}
info("\nverify_state_machine_equiv: PASS");
