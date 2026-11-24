#!/usr/bin/env node
/**
 * hub/test_suite.mjs — End-to-end regression suite for:
 *   1. Pure submission derivation & state transitions (contradictions, audit hash-binding, anti-backdate, claim_add sanitization).
 *   2. PR Gate security matrix (Opus 5.5 N1, N3, N4, N5, N10, N11, N12, N14, N15, N16, N17 + multi-claim + piggyback).
 *   3. Frozen Wave 4 Lean 4 statement compilation.
 *   4. Resilient event reader & pure non-mutating build_site.mjs.
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";
import {
  listMissionSlugs,
  loadMission,
  applySubmissionsPure,
  computeTrustSeal,
  deriveMissionState,
  computeRecordTargets,
  isRungConquered,
} from "./missions.mjs";
import { checkCommandArtifact } from "./judges/command.mjs";
import { runJudge } from "./judges/index.mjs";
import { parseGitRawZ, classifyEntries, verifyPrEntries, validateRecordImprovement } from "./pr_gate.mjs";
import { readEvents } from "./build_site.mjs";

let failed = 0;
function assert(cond, label, detail = "") {
  if (cond) {
    console.log(`PASS  ${label}`);
  } else {
    console.error(`FAIL  ${label} -> ${detail}`);
    failed++;
  }
}

// ---------------------------------------------------------------------------
// 1. PURE DERIVATION & STATE TRANSITION INVARIANTS
// ---------------------------------------------------------------------------
const seed = {
  meta: { mission: "test", updated_at: "2026-01-01T00:00:00Z" },
  programs: [{ id: "p1", key: "p1", title: "P1" }],
  seats: [],
  lemmas: [
    {
      id: "T-001",
      program: "p1",
      title: "Claim 1",
      statement: "P",
      theorem_name: "T.p",
      lean_file: "missions/test/lean/T/Claims/T_001.lean",
      status: "conjecture",
      deps: [],
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
  ],
  messages: [],
  whispers: [],
  checker_runs: [],
};

const proofSub = {
  file: "T-001.proof.aaaaaaaaaa.json",
  lemma_id: "T-001",
  kind: "proof",
  at: "2026-02-01T00:00:00Z",
  file_hash: "aaaaaaaaaa0000",
  checker: { ok: true, file_hash: "aaaaaaaaaa0000", by_seat: "donor-a", axioms: [] },
};
const refuteSub = {
  file: "T-001.refutation.bbbbbbbbbb.json",
  lemma_id: "T-001",
  kind: "refutation",
  at: "2026-02-02T00:00:00Z",
  refutation: { file_hash: "bbbbbbbbbb0000", by_seat: "donor-b", summary: "counterexample", axioms: [] },
};
const deadSub = {
  file: "T-001.rule_dead.1.json",
  lemma_id: "T-001",
  kind: "rule_dead",
  at: "2026-02-03T00:00:00Z",
  epitaph: { wall: "Barrier", reason: "dead", by_seat: "seat-1" },
};

// Opposing evidence in BOTH orders & replayed twice stays sticky contradiction preserving BOTH receipts!
const c1 = applySubmissionsPure(seed, [proofSub, refuteSub, deadSub]).state;
const c2 = applySubmissionsPure(seed, [refuteSub, proofSub, deadSub]).state;
const c3 = applySubmissionsPure(c1, [proofSub, refuteSub, deadSub]).state;
for (const [tag, st] of [["proof->refute", c1], ["refute->proof", c2], ["double replay", c3]]) {
  const l = st.lemmas[0];
  assert(
    l.status === "contradiction" && Boolean(l.checker?.ok) && Boolean(l.refutation) && computeTrustSeal(l) === "contradiction",
    `Contradiction sticky & preserves both receipts (${tag})`,
    JSON.stringify(l)
  );
}

// rule_dead cannot overwrite refuted
const onlyRef = applySubmissionsPure(seed, [refuteSub, deadSub]).state;
assert(onlyRef.lemmas[0].status === "refuted", "rule_dead does not overwrite refuted claim", onlyRef.lemmas[0].status);

// claim_add sanitization: forged status/checker stripped
const forgedAdd = {
  file: "T-002.claim_add.1.json",
  lemma_id: "T-002",
  kind: "claim_add",
  at: "2026-02-01T00:00:00Z",
  claim: { title: "Forged", status: "checked", checker: { ok: true, statement_frozen: true } },
};
const addRes = applySubmissionsPure(seed, [forgedAdd]).state;
const added = addRes.lemmas.find((l) => l.id === "T-002");
assert(added && added.status === "conjecture" && added.checker === null, "claim_add sanitized (forged status/checker stripped)", JSON.stringify(added));

// Audit hash-binding: missing hash rejected, mismatched hash rejected, matching hash accepted
const auditNoHash = { file: "a1.json", lemma_id: "T-001", kind: "audit", at: "2026-02-03Z", audit: { status: "faithful", by_seat: "audit-x" } };
const auditBadHash = { file: "a2.json", lemma_id: "T-001", kind: "audit", at: "2026-02-03Z", audit: { status: "faithful", by_seat: "audit-x", file_hash: "wrong" } };
const auditGoodHash = { file: "a3.json", lemma_id: "T-001", kind: "audit", at: "2026-02-03Z", audit: { status: "faithful", by_seat: "audit-x", file_hash: "aaaaaaaaaa0000" } };
assert(computeTrustSeal(applySubmissionsPure(seed, [proofSub, auditNoHash]).state.lemmas[0]) === "provisional", "Audit without file_hash rejected");
assert(computeTrustSeal(applySubmissionsPure(seed, [proofSub, auditBadHash]).state.lemmas[0]) === "provisional", "Audit with mismatched file_hash rejected");
assert(computeTrustSeal(applySubmissionsPure(seed, [proofSub, auditGoodHash]).state.lemmas[0]) === "audited", "Audit with matching file_hash accepted");
// Seal invalidation if artifact hash changes after legacy audit
const staleAuditLemma = { status: "checked", checker: { ok: true, file_hash: "new_hash" }, audit: { status: "faithful", file_hash: "old_hash" } };
assert(computeTrustSeal(staleAuditLemma) === "provisional", "computeTrustSeal invalidates stale audit hash");

// Git commit timestamp overrides backdated `sub.at`
const backdatedProof = {
  file: "T-001.proof.cccccccccc.json",
  lemma_id: "T-001",
  kind: "proof",
  at: "1999-01-01T00:00:00Z",
  checker: { ok: true, file_hash: "cccccccccc0000", by_seat: "donor-backdater", axioms: [] },
};
const gitTs = new Map([
  ["T-001.proof.aaaaaaaaaa.json", 1000],
  ["T-001.proof.cccccccccc.json", 2000],
]);
const ordered = applySubmissionsPure(seed, [backdatedProof, proofSub], { gitAddedTs: gitTs }).state;
assert(ordered.lemmas[0].checker.by_seat === "donor-a", "Trusted git commit timestamp defeats backdated sub.at credit theft", ordered.lemmas[0].checker.by_seat);

// ---------------------------------------------------------------------------
// 2. PR GATE SECURITY MATRIX (Opus 5.5 N1, N3, N4, N5, N10, N11, N12, N14, N15, N16, N17)
// ---------------------------------------------------------------------------
function rawEntry(mode, status, filePath, oldPath = null) {
  if (oldPath) return `:100644 ${mode} 1111111 2222222 ${status}\0${oldPath}\0${filePath}\0`;
  return `:000000 ${mode} 0000000 2222222 ${status}\0${filePath}\0`;
}

// N3: git mv rename (R100) or delete (D) rejected on donor lane
const n3Entries = parseGitRawZ(rawEntry("100644", "R100", "missions/ml-math-kernels/artifacts/x.json", "hub/judges/lean4.mjs"));
const n3Cls = classifyEntries(n3Entries);
assert(n3Cls.lane === "infra" && n3Cls.reasons.some((r) => r.includes("Disallowed git status")), "N3 (git mv rename) blocked from donor lane", JSON.stringify(n3Cls));

// N4: symlink (mode 120000) rejected on donor lane
const n4Entries = parseGitRawZ(rawEntry("120000", "A", "missions/sorting-networks/lean/SortNet/Claims/SN_003.lean"));
const n4Cls = classifyEntries(n4Entries);
assert(n4Cls.lane === "infra" && n4Cls.reasons.some((r) => r.includes("120000")), "N4 (symlink mode 120000) blocked from donor lane", JSON.stringify(n4Cls));

// N5: trailing-space submission filename rejected (NEVER passes with checked:0!)
const n5Entries = parseGitRawZ(rawEntry("100644", "A", "missions/sorting-networks/submissions/SN-003.proof.1234567890.json "));
const n5Res = verifyPrEntries(n5Entries);
assert(!n5Res.ok && !n5Res.eligible_for_auto_merge, "N5 (trailing-space submission / checked:0 bypass) rejected", JSON.stringify(n5Res));

// N5b: valid-looking submission path that is MISSING on disk -> HARD FAIL!
const n5bEntries = parseGitRawZ(rawEntry("100644", "A", "missions/sorting-networks/submissions/SN-003.proof.0000000000.json"));
const n5bRes = verifyPrEntries(n5bEntries);
assert(!n5bRes.ok && n5bRes.reason.includes("missing"), "N5b (missing submission file on disk) rejected with hard failure", JSON.stringify(n5bRes));

// N10: modifying existing submission (status M) rejected (append-only!)
const n10Entries = parseGitRawZ(rawEntry("100644", "M", "missions/sorting-networks/submissions/SN-001.proof.2a05a3bbc5.json"));
const n10Cls = classifyEntries(n10Entries);
assert(n10Cls.lane === "infra" && n10Cls.reasons.some((r) => r.includes("newly added")), "N10 (modify existing submission) blocked by append-only rule", JSON.stringify(n10Cls));

// N17: deleting submission (status D) rejected
const n17Entries = parseGitRawZ(rawEntry("000000", "D", "missions/sorting-networks/submissions/SN-001.proof.2a05a3bbc5.json"));
const n17Cls = classifyEntries(n17Entries);
assert(n17Cls.lane === "infra", "N17 (delete existing submission) blocked", JSON.stringify(n17Cls));

// Temporary submission fixtures for N11, N12, N14, N15, N16
const tmpSubs = [];
function writeTmpSub(relPath, obj) {
  const abs = path.resolve(relPath);
  fs.writeFileSync(abs, JSON.stringify(obj, null, 2));
  tmpSubs.push(abs);
  return parseGitRawZ(rawEntry("100644", "A", relPath));
}
try {
  // N11: duplicate proof for already-checked SN-001 rejected!
  const n11E = writeTmpSub("missions/sorting-networks/submissions/SN-001.proof.2a05a3bbc5.dup.json", {
    schema: "fleet-submission/2",
    mission: "sorting-networks",
    lemma_id: "SN-001",
    kind: "proof",
    file: "missions/sorting-networks/lean/SortNet/Claims/SN_001.lean",
    theorem: "SortNet.Claims.SN_001.zero_one_principle",
    checker: { ok: true, judge: "lean4", file_hash: "2a05a3bbc5", axioms: [], by_seat: "donor-dup" },
  });
  const n11R = verifyPrEntries(n11E);
  assert(!n11R.ok && n11R.reports[0]?.reason?.includes("Duplicate proof"), "N11 (duplicate proof on solved SN-001) rejected", JSON.stringify(n11R));

  // N12: unbound refutation on checked L-lib-000 (no frozen statement) rejected!
  const n12E = writeTmpSub("missions/p-vs-np/submissions/L-lib-000.refutation.0f522adda1.json", {
    schema: "fleet-submission/2",
    mission: "p-vs-np",
    lemma_id: "L-lib-000",
    kind: "refutation",
    file: "lean/PnP/Lemmas/L_lib_001.lean",
    theorem: "PnP.Lemmas.L_lib_001.monotone_circuit_is_monotone",
    refutation: { file_hash: "0f522adda1", axioms: ["propext"], by_seat: "donor-evil" },
  });
  const n12R = verifyPrEntries(n12E);
  assert(!n12R.ok && n12R.reports[0]?.reason?.includes("Unbound refutation"), "N12 (unbound refutation on checked claim) rejected", JSON.stringify(n12R));

  // N15: self-certifying audit JSON rejected on donor lane!
  const n15E = writeTmpSub("missions/sorting-networks/submissions/SN-003.audit.1111111111.json", {
    schema: "fleet-submission/2",
    mission: "sorting-networks",
    lemma_id: "SN-003",
    kind: "audit",
    audit: { status: "faithful", by_seat: "donor-self", file_hash: "1111111111" },
  });
  const n15R = verifyPrEntries(n15E);
  assert(!n15R.ok && n15R.reports[0]?.reason?.includes("maintainer review"), "N15 (self-certifying audit JSON) rejected", JSON.stringify(n15R));

  // N16: mission directory mismatch (sorting-networks dir claiming p-vs-np) rejected!
  const n16E = writeTmpSub("missions/sorting-networks/submissions/L-lib-000.proof.0f522adda1.json", {
    schema: "fleet-submission/2",
    mission: "p-vs-np",
    lemma_id: "L-lib-000",
    kind: "proof",
    file: "lean/PnP/Lemmas/L_lib_000.lean",
    theorem: "PnP.Lemmas.L_lib_000.flipBit_involutive",
    checker: { ok: true, judge: "lean4", file_hash: "0f522adda1", axioms: [], by_seat: "donor-x" },
  });
  const n16R = verifyPrEntries(n16E);
  assert(!n16R.ok && n16R.reports[0]?.reason?.includes("Mission directory mismatch"), "N16 (mission/dir mismatch) rejected", JSON.stringify(n16R));

  // N14 (Proof PR verdict binding on real frozen Lean proof CZ-001 in temp rootDir — excludes own receipt from baseState!):
  const czTmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "pf-proof-bind-"));
  try {
    const czArtRel = "missions/crypto-zk-circuits/lean/Crypto/Claims/CZ_001.lean";
    const czSubRel = "missions/crypto-zk-circuits/submissions/CZ-001.proof.bd354ffcce.json";
    const realCzSub = JSON.parse(fs.readFileSync(path.resolve(czSubRel), "utf8"));
    fs.mkdirSync(path.dirname(path.join(czTmpRoot, czArtRel)), { recursive: true });
    fs.mkdirSync(path.dirname(path.join(czTmpRoot, czSubRel)), { recursive: true });
    fs.copyFileSync(path.resolve(czArtRel), path.join(czTmpRoot, czArtRel));
    const czEntries = parseGitRawZ(rawEntry("100644", "A", czArtRel) + rawEntry("100644", "A", czSubRel));

    // N14: forged statement_frozen:false + internal seat-strat-1 impersonation -> rejected by verdict binding
    const forgedSeatSub = structuredClone(realCzSub);
    forgedSeatSub.checker.statement_frozen = false;
    forgedSeatSub.checker.by_seat = "seat-strat-1";
    fs.writeFileSync(path.join(czTmpRoot, czSubRel), JSON.stringify(forgedSeatSub, null, 2));
    const n14R = verifyPrEntries(czEntries, { rootDir: czTmpRoot });
    assert(
      !n14R.ok && n14R.reports[0]?.reason?.includes("statement_frozen mismatch") && n14R.reports[0]?.reason?.includes("by_seat"),
      "N14 (forged statement_frozen + seat-strat-1 impersonation) rejected by verdict binding",
      JSON.stringify(n14R)
    );

    // N14b: missing core_hash on donor proof PR -> rejected
    const missingCoreSub = structuredClone(realCzSub);
    missingCoreSub.checker.by_seat = "donor-test-ok";
    delete missingCoreSub.checker.core_hash;
    fs.writeFileSync(path.join(czTmpRoot, czSubRel), JSON.stringify(missingCoreSub, null, 2));
    const missingCoreR = verifyPrEntries(czEntries, { rootDir: czTmpRoot });
    assert(
      !missingCoreR.ok && missingCoreR.reports[0]?.reason?.includes("core_hash mismatch"),
      "N14b (missing core_hash on donor proof PR) rejected by verdict binding",
      JSON.stringify(missingCoreR)
    );

    // Positive control: honest CZ-001 donor PR passes verify-pr & is auto-mergeable (frozen statement matched!)
    const honestSub = structuredClone(realCzSub);
    honestSub.checker.by_seat = "donor-test-ok";
    fs.writeFileSync(path.join(czTmpRoot, czSubRel), JSON.stringify(honestSub, null, 2));
    const posR = verifyPrEntries(czEntries, { rootDir: czTmpRoot });
    assert(posR.ok && posR.checked === 1 && posR.eligible_for_auto_merge, "Positive control: honest frozen CZ-001 donor PR passes verify-pr", JSON.stringify(posR));

    // N14e-omit (Daybreak P3): omitting required signature on donor proof PR rejected (fail-closed)
    const omitSigSub = structuredClone(honestSub);
    delete omitSigSub.signature;
    fs.writeFileSync(path.join(czTmpRoot, czSubRel), JSON.stringify(omitSigSub, null, 2));
    const omitSigR = verifyPrEntries(czEntries, { rootDir: czTmpRoot });
    assert(
      !omitSigR.ok && omitSigR.reports[0]?.reason?.includes("signature mismatch"),
      "N14e-omit (Daybreak P3: omitted sub.signature on donor proof PR rejected fail-closed)",
      JSON.stringify(omitSigR)
    );

    // N14e (Daybreak P2-1): forged sub.signature + forged statement_hash rejected by verdict binding!
    const forgedMetaSub = structuredClone(honestSub);
    forgedMetaSub.signature = "FORGED_SIGNATURE_CLAIMING_DIFFERENT_THEOREM";
    forgedMetaSub.checker.statement_hash = "forged_statement_hash_0000";
    fs.writeFileSync(path.join(czTmpRoot, czSubRel), JSON.stringify(forgedMetaSub, null, 2));
    const forgedMetaR = verifyPrEntries(czEntries, { rootDir: czTmpRoot });
    assert(
      !forgedMetaR.ok &&
        forgedMetaR.reports[0]?.reason?.includes("signature mismatch") &&
        forgedMetaR.reports[0]?.reason?.includes("statement_hash mismatch"),
      "N14e (P2-1 forged sub.signature + forged statement_hash) rejected by verdict binding",
      JSON.stringify(forgedMetaR)
    );
  } finally {
    fs.rmSync(czTmpRoot, { recursive: true, force: true });
  }

  // N14f (Daybreak P2-1/P3): forged and omitted record signature rejected fail-closed on donor record PR
  // Dynamically select the live winning incumbent for ML-rec-bf16-exp2 so future record ratchets never rot this test!
  const mlRecTmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "pf-rec-sig-"));
  try {
    const exp2Best = deriveMissionState("ml-math-kernels").state.lemmas.find((l) => l.id === "ML-rec-bf16-exp2")?.record_state?.best;
    assert(Boolean(exp2Best?.file && exp2Best?.submission), "N14f setup: ML-rec-bf16-exp2 has a live winning record");
    const mlArtRel = exp2Best.file;
    const mlSubRel = `missions/ml-math-kernels/submissions/${exp2Best.submission}`;
    const realSub = JSON.parse(fs.readFileSync(path.resolve(mlSubRel), "utf8"));
    fs.mkdirSync(path.dirname(path.join(mlRecTmpRoot, mlArtRel)), { recursive: true });
    fs.mkdirSync(path.dirname(path.join(mlRecTmpRoot, mlSubRel)), { recursive: true });
    fs.copyFileSync(path.resolve(mlArtRel), path.join(mlRecTmpRoot, mlArtRel));
    const mlEntries = parseGitRawZ(rawEntry("100644", "A", mlArtRel) + rawEntry("100644", "A", mlSubRel));

    // Forged signature on record PR -> rejected
    const forgedRecSub = { ...realSub, signature: "FORGED_RECORD_SIGNATURE" };
    fs.writeFileSync(path.join(mlRecTmpRoot, mlSubRel), JSON.stringify(forgedRecSub, null, 2));
    const forgedRecR = verifyPrEntries(mlEntries, { rootDir: mlRecTmpRoot });
    assert(
      !forgedRecR.ok && forgedRecR.reports[0]?.reason?.includes("signature mismatch"),
      "N14f-forged (Daybreak P2-1: forged record sub.signature rejected by verdict binding)",
      JSON.stringify(forgedRecR)
    );

    // Omitted signature on record PR -> rejected fail-closed
    const omittedRecSub = { ...realSub };
    delete omittedRecSub.signature;
    fs.writeFileSync(path.join(mlRecTmpRoot, mlSubRel), JSON.stringify(omittedRecSub, null, 2));
    const omittedRecR = verifyPrEntries(mlEntries, { rootDir: mlRecTmpRoot });
    assert(
      !omittedRecR.ok && omittedRecR.reports[0]?.reason?.includes("signature mismatch"),
      "N14f-omit (Daybreak P3: omitted record sub.signature rejected fail-closed)",
      JSON.stringify(omittedRecR)
    );
  } finally {
    fs.rmSync(mlRecTmpRoot, { recursive: true, force: true });
  }

  // N14d: Pure-data ML kernel judge rejects executable JS imports/code without ever executing it!
  const evilRecRel = "missions/ml-math-kernels/artifacts/ML_rec_bf16_exp2_s99.json";
  const evilRecAbs = path.resolve(evilRecRel);
  fs.writeFileSync(
    evilRecAbs,
    `import fs from "node:fs";
fs.writeFileSync("/tmp/should_never_exist_pf", "pwn");
`
  );
  tmpSubs.push(evilRecAbs);
  const evilRecRes = runJudge(loadMission("ml-math-kernels"), {
    file: evilRecRel,
    target: "bf16_exp2",
    kind: "record",
    expectedScore: 99,
    statementFile: "missions/ml-math-kernels/specs/ML_rec_bf16_exp2.json",
  });
  assert(
    !evilRecRes.ok && !fs.existsSync("/tmp/should_never_exist_pf"),
    "N14d (Pure-data ML kernel judge rejects executable JS with zero code execution)",
    JSON.stringify(evilRecRes)
  );
} finally {
  for (const f of tmpSubs) {
    try { fs.unlinkSync(f); } catch {}
  }
}

// ---------------------------------------------------------------------------
// 3. RESILIENT EVENT READER & PURE NON-MUTATING BUILD
// ---------------------------------------------------------------------------
const tmpEvDir = fs.mkdtempSync(path.join(os.tmpdir(), "pf-ev-"));
try {
  const evFile = path.join(tmpEvDir, "events.ndjson");
  fs.writeFileSync(evFile, `{"id":"1","type":"a"}\n{CORRUPT JSON\n{"id":"2","type":"b"}\n`);
  const evs = readEvents(evFile);
  assert(evs.length === 2 && evs[0].id === "2" && evs[1].id === "1", "readEvents preserves valid events around corrupt NDJSON line", JSON.stringify(evs));
} finally {
  fs.rmSync(tmpEvDir, { recursive: true, force: true });
}

// Verify build_site.mjs --offline leaves tracked state.json byte-identical!
const beforeSortNet = fs.readFileSync("missions/sorting-networks/state.json", "utf8");
const buildRun = spawnSync("node", ["hub/build_site.mjs", "--offline"], { encoding: "utf8" });
const afterSortNet = fs.readFileSync("missions/sorting-networks/state.json", "utf8");
assert(buildRun.status === 0 && beforeSortNet === afterSortNet && fs.existsSync("dist/PROOFS.md"), "build_site.mjs is pure (state.json byte-identical) & emits dist/PROOFS.md", buildRun.stderr);

// Dynamically verify ALL Lean missions: Core builds, ALL frozen Statements/*.lean compile, AND ALL Lean KotH `Record_mono` type-check in exact direction!
for (const slug of listMissionSlugs()) {
  const m = loadMission(slug);
  if (m.judge?.type !== "lean4") continue;
  const absLeanDir = path.resolve(m.judge.lean_dir);
  const target = m.judge.lake_target;
  const b = spawnSync("lake", ["build", target], { cwd: absLeanDir, encoding: "utf8" });
  assert(b.status === 0, `Core library builds cleanly: ${target} (${slug})`, (b.stdout || "") + (b.stderr || ""));

  const stmtDir = `${target}/Statements`;
  const absStmtDir = path.join(absLeanDir, stmtDir);
  if (fs.existsSync(absStmtDir)) {
    const files = fs.readdirSync(absStmtDir).filter((f) => f.endsWith(".lean") && !f.startsWith("_Test")).sort();
    for (const f of files) {
      const rel = path.join(stmtDir, f);
      const r = spawnSync("lake", ["env", "lean", rel], { cwd: absLeanDir, encoding: "utf8" });
      assert(r.status === 0, `Frozen statement compiles cleanly: ${target}/${f}`, (r.stdout || "") + (r.stderr || ""));
    }
  }

  // Verify every registered Lean KotH hunt exports exact direction-appropriate `Record_mono`!
  const { state: ms } = deriveMissionState(slug);
  for (const l of ms.lemmas || []) {
    if (l.kind !== "record" || !l.statement_file?.endsWith(".lean")) continue;
    const isMax = l.record?.direction === "max";
    const mod = l.statement_def.replace(/\.Record$/, "");
    const src = fs.readFileSync(path.resolve(l.statement_file), "utf8");
    const monoSig = isMax
      ? `∀ {a b : Nat}, a ≤ b → ${mod}.Record b → ${mod}.Record a`
      : `∀ {a b : Nat}, a ≤ b → ${mod}.Record a → ${mod}.Record b`;
    const code = `${src}\nexample : ${monoSig} := @${mod}.Record_mono\n`;
    const r = spawnSync("lake", ["env", "lean", "--stdin"], { cwd: absLeanDir, input: code, encoding: "utf8" });
    assert(r.status === 0, `KotH Record_mono (${isMax ? "max/downward" : "min/upward"}) verified in Lean 4: ${mod}`, (r.stdout || "") + (r.stderr || ""));
  }
}

// Sanity check deriveMissionState idempotence across active missions
const d1 = deriveMissionState("sorting-networks").state;
const d2 = deriveMissionState("sorting-networks").state;
assert(JSON.stringify(d1) === JSON.stringify(d2), "deriveMissionState is deterministic & byte-identical across runs");

// ---------------------------------------------------------------------------
// 4. KING OF THE HILL: PURE STATE MACHINE (MIN + MAX), COMMAND-JUDGE KOTH & PR GATE MATRIX
// ---------------------------------------------------------------------------

// 4b. Pure KotH derivation: ratchet, delta anti-farming points, non-improving ignored, closure, zero-closure, contradiction, stale hash, git order, replay idempotence
const recSeed = {
  meta: { mission: "sorting-networks", updated_at: "2026-01-01T00:00:00Z" },
  programs: [{ id: "record_hunt", key: "rec", title: "Record Hunt" }],
  seats: [],
  lemmas: [
    {
      id: "SN-rec-013",
      kind: "record",
      program: "record_hunt",
      title: "13-Wire Hunt",
      statement_file: "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean",
      statement_def: "SortNet.Statements.SN_rec_013.Record",
      record: {
        direction: "min",
        unit: "comparators",
        start_target: 46,
        literature_best: 45,
        literature_lower_bound: 43,
        bound_floor: 41,
        score_max: 1000,
        file_stem: "SN_rec_013",
        claims_dir: "missions/sorting-networks/lean/SortNet/Claims",
        theorem_template: "SortNet.Claims.SN_rec_013_{tag}.record",
      },
      status: "conjecture",
      deps: [],
    },
  ],
  messages: [],
  whispers: [],
  checker_runs: [],
};

function mkRecSub(kind, score, seat, { stmtHash = "stmt_ok", at = "2026-02-01T00:00:00Z" } = {}) {
  const t = computeRecordTargets("sorting-networks", recSeed.lemmas[0], kind, score);
  return {
    _sub_file: t.submissionBasename,
    schema: "pf.record.v1",
    mission: "sorting-networks",
    lemma_id: "SN-rec-013",
    kind,
    score,
    file: t.artifactFile,
    theorem: t.theoremName,
    at,
    checker: { ok: true, by_seat: seat, file_hash: `fh_${kind}_${score}`, statement_hash: stmtHash, core_hash: "core_ok", axioms: ["propext"] },
  };
}

const curHashes = {
  coreHash: "core_ok",
  statementHashes: { "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean": "stmt_ok" },
};
const r46 = mkRecSub("record", 46, "donor-a", { at: "2026-02-01T00:00:00Z" });
const r44 = mkRecSub("record", 44, "donor-b", { at: "2026-02-02T00:00:00Z" });
const r45Late = mkRecSub("record", 45, "donor-late", { at: "1999-01-01T00:00:00Z" }); // backdated sub.at!
const rStale = mkRecSub("record", 43, "donor-stale", { stmtHash: "stmt_OLD" });
const b42 = mkRecSub("record_bound", 42, "donor-c");
const b43 = mkRecSub("record_bound", 43, "donor-d");
const recGitTs = new Map([
  [r46._sub_file, 1000],
  [r44._sub_file, 2000],
  [r45Late._sub_file, 3000],
  [rStale._sub_file, 3500],
  [b42._sub_file, 4000],
  [b43._sub_file, 5000],
]);

// Before closing (46 -> 44 -> 45 ignored -> stale ignored -> bound 42)
const midState = applySubmissionsPure(recSeed, [r45Late, r44, r46, rStale, b42], {
  missionSlug: "sorting-networks",
  gitAddedTs: recGitTs,
  currentHashes: curHashes,
}).state;
const midL = midState.lemmas[0];
assert(
  midL.record_state.best?.score === 44 &&
    midL.record_state.best?.seat === "donor-b" &&
    midL.record_state.next_target === 43 &&
    midL.record_state.refuted?.score === 42 &&
    midL.record_state.refuted?.inclusive_bound === 43 &&
    !midL.record_state.closed &&
    computeTrustSeal(midL) === "record" &&
    midL.record_state.points_by_seat["donor-a"] === 1 &&
    midL.record_state.points_by_seat["donor-b"] === 2 &&
    !midL.record_state.points_by_seat["donor-late"] &&
    !midL.record_state.points_by_seat["donor-stale"] &&
    midL.record_state.history.find((h) => h.score === 45)?.state === "ignored_non_improving" &&
    midL.record_state.history.find((h) => h.score === 43)?.state === "stale_statement" &&
    isRungConquered(midL, { record_at_most: 45 }) === true &&
    isRungConquered(midL, { record_at_most: 43 }) === false,
  "KotH pure derivation: ratchet, git-order defeats backdated sub.at, delta points, stale hash & objective rung",
  JSON.stringify(midL.record_state)
);

// Closing at refuted + 1 == best (bound 43 closes against best 44 -> seal === frozen!)
const closedState = applySubmissionsPure(recSeed, [r46, r44, b42, b43], {
  missionSlug: "sorting-networks",
  gitAddedTs: recGitTs,
  currentHashes: curHashes,
}).state;
const closedL = closedState.lemmas[0];
assert(
  closedL.record_state.closed === true &&
    closedL.record_state.next_target === null &&
    computeTrustSeal(closedL) === "frozen" &&
    closedL.record_state.points_by_seat["donor-d"] === 1,
  "KotH exact closure when refuted + 1 == best (seal -> frozen, next_target -> null)",
  JSON.stringify(closedL.record_state)
);

// Replay idempotence: feeding derived state back into applySubmissionsPure NEVER duplicates history or points!
const replayed = applySubmissionsPure(closedState, [r46, r44, b42, b43], {
  missionSlug: "sorting-networks",
  gitAddedTs: recGitTs,
  currentHashes: curHashes,
}).state;
assert(
  JSON.stringify(replayed.lemmas[0].record_state) === JSON.stringify(closedL.record_state),
  "KotH replay idempotence: zero history duplication or double points",
  JSON.stringify(replayed.lemmas[0].record_state)
);

// Best == 0 closes immediately without needing a lower bound
const r0 = mkRecSub("record", 0, "donor-zero");
const zeroState = applySubmissionsPure(recSeed, [r0], { missionSlug: "sorting-networks", currentHashes: curHashes }).state;
assert(
  zeroState.lemmas[0].record_state.closed === true && zeroState.lemmas[0].record_state.next_target === null,
  "KotH closes automatically when best score reaches 0",
  JSON.stringify(zeroState.lemmas[0].record_state)
);

// record_bound before any record is valid and does not close
const boundOnly = applySubmissionsPure(recSeed, [b42], { missionSlug: "sorting-networks", currentHashes: curHashes }).state;
assert(
  boundOnly.lemmas[0].record_state.best === null &&
    boundOnly.lemmas[0].record_state.refuted?.inclusive_bound === 43 &&
    boundOnly.lemmas[0].record_state.closed === false &&
    boundOnly.lemmas[0].record_state.next_target === 46,
  "KotH accepts record_bound before first incumbent cleanly",
  JSON.stringify(boundOnly.lemmas[0].record_state)
);

// Sticky contradiction in BOTH orders (record 44 + record_bound 44), AND out-of-range contradiction (47 + ¬47), zero points!
const b44Conflict = mkRecSub("record_bound", 44, "donor-conflict");
const con1 = applySubmissionsPure(recSeed, [r44, b44Conflict], {
  missionSlug: "sorting-networks",
  gitAddedTs: new Map([[r44._sub_file, 100], [b44Conflict._sub_file, 200]]),
  currentHashes: curHashes,
}).state;
const con2 = applySubmissionsPure(recSeed, [b44Conflict, r44], {
  missionSlug: "sorting-networks",
  gitAddedTs: new Map([[b44Conflict._sub_file, 100], [r44._sub_file, 200]]),
  currentHashes: curHashes,
}).state;
const r47Out = mkRecSub("record", 47, "donor-out1");
const b47Out = mkRecSub("record_bound", 47, "donor-out2");
const con3 = applySubmissionsPure(recSeed, [r47Out, b47Out], {
  missionSlug: "sorting-networks",
  gitAddedTs: new Map([[r47Out._sub_file, 100], [b47Out._sub_file, 200]]),
  currentHashes: curHashes,
}).state;
assert(
  con1.lemmas[0].record_state.contradiction === true &&
    !con1.lemmas[0].record_state.closed &&
    computeTrustSeal(con1.lemmas[0]) === "contradiction" &&
    Object.keys(con1.lemmas[0].record_state.points_by_seat).length === 0 &&
    con1.seats.every((s) => (s.counts?.record_points || 0) === 0) &&
    con2.lemmas[0].record_state.contradiction === true &&
    !con2.lemmas[0].record_state.closed &&
    computeTrustSeal(con2.lemmas[0]) === "contradiction" &&
    con3.lemmas[0].record_state.contradiction === true &&
    Object.keys(con3.lemmas[0].record_state.points_by_seat).length === 0,
  "KotH sticky contradiction detected in both orders + out-of-range scores, with consistent zero points",
  JSON.stringify({ con1: con1.lemmas[0].record_state, con3: con3.lemmas[0].record_state })
);

// Missing or mismatched statement/core hashes mark receipts stale (NEVER awarded, scored, or conquered!)
const noStmtHashRes = applySubmissionsPure(recSeed, [r44], {
  missionSlug: "sorting-networks",
  currentHashes: { coreHash: "core_ok", statementHashes: {} },
}).state.lemmas[0];
const noCoreHashRes = applySubmissionsPure(recSeed, [r44], {
  missionSlug: "sorting-networks",
  currentHashes: { coreHash: null, statementHashes: curHashes.statementHashes },
}).state.lemmas[0];
const staleCoreRes = applySubmissionsPure(recSeed, [r44], {
  missionSlug: "sorting-networks",
  currentHashes: { coreHash: "core_NEW_REVISED", statementHashes: curHashes.statementHashes },
}).state.lemmas[0];
assert(
  noStmtHashRes.record_state.best === null &&
    noStmtHashRes.record_state.history[0]?.state === "stale_statement" &&
    noCoreHashRes.record_state.best === null &&
    noCoreHashRes.record_state.history[0]?.state === "stale_core" &&
    staleCoreRes.record_state.best === null &&
    staleCoreRes.record_state.history[0]?.state === "stale_core" &&
    Object.keys(staleCoreRes.record_state.points_by_seat).length === 0 &&
    isRungConquered(staleCoreRes, { record_at_most: 45 }) === false,
  "KotH rejects missing AND mismatched core_hash/statement_hash receipts as stale with zero points",
  JSON.stringify({ noStmt: noStmtHashRes.record_state, noCore: noCoreHashRes.record_state, staleCore: staleCoreRes.record_state })
);

// Missing git timestamps fallback sorts in improving score order (45 before 44 -> points split 2 + 1!)
const r45Fresh = mkRecSub("record", 45, "donor-45");
const fallbackOrder = applySubmissionsPure(recSeed, [r44, r45Fresh], {
  missionSlug: "sorting-networks",
  gitAddedTs: new Map(),
  currentHashes: curHashes,
}).state.lemmas[0];
assert(
  fallbackOrder.record_state.best?.score === 44 &&
    fallbackOrder.record_state.points_by_seat["donor-45"] === 2 &&
    fallbackOrder.record_state.points_by_seat["donor-b"] === 1,
  "KotH missing-git fallback replays improving scores deterministically (45 -> 44 splits points 2 + 1)",
  JSON.stringify(fallbackOrder.record_state.points_by_seat)
);

// 4c. Direction = "max" KotH pure derivation, closure, breakthrough guard & Command-Judge KotH!
const maxSeed = {
  meta: { mission: "error-correcting-codes", updated_at: "2026-01-01T00:00:00Z" },
  programs: [{ id: "record_hunt", key: "rec", title: "Record Hunt" }],
  seats: [],
  lemmas: [
    {
      id: "EC-rec-17-6",
      kind: "record",
      program: "record_hunt",
      title: "A(17,6) Max Hunt",
      statement_file: "missions/error-correcting-codes/lean/Codes/Statements/EC_rec_17_6.lean",
      statement_def: "Codes.Statements.EC_rec_17_6.Record",
      record: {
        direction: "max",
        unit: "codewords",
        start_target: 36,
        literature_best: 42,
        literature_upper_bound: 47,
        bound_floor: 48,
        score_max: 500,
        file_stem: "EC_rec_17_6",
        claims_dir: "missions/error-correcting-codes/lean/Codes/Claims",
        theorem_template: "Codes.Claims.EC_rec_17_6_{tag}.record",
      },
      status: "conjecture",
      deps: [],
    },
  ],
  messages: [],
  whispers: [],
  checker_runs: [],
};
function mkMaxSub(kind, score, seat) {
  const t = computeRecordTargets("error-correcting-codes", maxSeed.lemmas[0], kind, score);
  return {
    _sub_file: t.submissionBasename,
    schema: "pf.record.v1",
    mission: "error-correcting-codes",
    lemma_id: "EC-rec-17-6",
    kind,
    score,
    file: t.artifactFile,
    theorem: t.theoremName,
    at: "2026-02-01T00:00:00Z",
    checker: { ok: true, by_seat: seat, file_hash: `fh_${kind}_${score}`, statement_hash: "max_stmt", core_hash: "core_ok", axioms: [] },
  };
}
const maxHashes = {
  coreHash: "core_ok",
  statementHashes: { "missions/error-correcting-codes/lean/Codes/Statements/EC_rec_17_6.lean": "max_stmt" },
};
const m38 = mkMaxSub("record", 38, "donor-m1");
const m42 = mkMaxSub("record", 42, "donor-m2");
const m48Ub = mkMaxSub("record_bound", 48, "donor-u1");
const m43Ub = mkMaxSub("record_bound", 43, "donor-u2");
const maxState = applySubmissionsPure(maxSeed, [m42, m38, m48Ub, m43Ub], {
  missionSlug: "error-correcting-codes",
  gitAddedTs: new Map(), // also exercises missing-git max fallback ordering (38 before 42, 48 before 43!)
  currentHashes: maxHashes,
}).state.lemmas[0];
assert(
  maxState.record_state.best?.score === 42 &&
    maxState.record_state.refuted?.score === 43 &&
    maxState.record_state.refuted?.inclusive_bound === 42 &&
    maxState.record_state.closed === true &&
    maxState.record_state.next_target === null &&
    computeTrustSeal(maxState) === "frozen" &&
    maxState.record_state.points_by_seat["donor-m1"] === 3 &&
    maxState.record_state.points_by_seat["donor-m2"] === 4 &&
    maxState.record_state.points_by_seat["donor-u1"] === 1 &&
    maxState.record_state.points_by_seat["donor-u2"] === 5 &&
    isRungConquered(maxState, { record_at_least: 42 }) === true &&
    isRungConquered(maxState, { record_at_least: 43 }) === false,
  "KotH direction=max: ratchet up, delta points, upper-bound closure (42 vs ¬43), fallback ordering & record_at_least",
  JSON.stringify(maxState.record_state)
);
const maxBrk = validateRecordImprovement(maxSeed.lemmas[0], "record", 43);
const maxUbBrk = validateRecordImprovement(maxSeed.lemmas[0], "record_bound", 47);
assert(
  maxBrk.ok && maxBrk.requiresMaintainer === true && maxUbBrk.ok && maxUbBrk.requiresMaintainer === true,
  "KotH direction=max breakthrough guards fire on > literature_best (43>42) and < literature_upper_bound (46<47)",
  JSON.stringify({ maxBrk, maxUbBrk })
);

// Command-Judge pure-data exhaustive BF16 KotH test (ML-rec-bf16-rsqrt)
const mlMission = loadMission("ml-math-kernels");
const mlSpecRel = "missions/ml-math-kernels/specs/ML_rec_bf16_rsqrt.json";
const mlArtPath = path.resolve("missions/ml-math-kernels/artifacts/ML_rec_bf16_rsqrt_s17.json");
const rCmdPass = checkCommandArtifact(mlArtPath, "bf16_rsqrt", {
  judgeConfig: mlMission.judge,
  kind: "record",
  statementFile: mlSpecRel,
  expectedScore: 17,
});
const rCmdFail = checkCommandArtifact(mlArtPath, "bf16_rsqrt", {
  judgeConfig: mlMission.judge,
  kind: "record",
  statementFile: mlSpecRel,
  expectedScore: 10,
});
const rCmdBound = checkCommandArtifact(mlArtPath, "bf16_rsqrt", {
  judgeConfig: mlMission.judge,
  kind: "record_bound",
  statementFile: mlSpecRel,
  expectedScore: 10,
});
assert(
  rCmdPass.ok && rCmdPass.score === 17 && rCmdPass.statement_frozen === true && !rCmdFail.ok && !rCmdBound.ok,
  "Command-Judge KotH (ML-rec-bf16-rsqrt exhaustive 65,536-input judge): passes ≤17, rejects ≤10, rejects record_bound",
  JSON.stringify({ rCmdPass, rCmdFail, rCmdBound })
);

// 4d. Breakthrough literature guard in validateRecordImprovement
const brk = validateRecordImprovement(recSeed.lemmas[0], "record", 44);
assert(brk.ok && brk.requiresMaintainer === true, "KotH breakthrough past literature_best (44 < 45) sets requiresMaintainer=true", JSON.stringify(brk));
const nonBrk = validateRecordImprovement(recSeed.lemmas[0], "record", 45);
assert(nonBrk.ok && nonBrk.requiresMaintainer === false, "KotH matching literature_best (45 == 45) stays auto-mergeable", JSON.stringify(nonBrk));
const badScoreImp = validateRecordImprovement(recSeed.lemmas[0], "record", 47);
assert(!badScoreImp.ok, "KotH rejects score worse than start_target (47 > 46)", JSON.stringify(badScoreImp));

// 4d. PR Gate KotH matrix (SAFE non-colliding high scores 998/999 + non-overwrite guard so donor work is NEVER touched!)
const tmpKoth = [];
const kothSalt = `${process.pid}_${Date.now()}`;
function safeWriteTmpKoth(relPath, content) {
  const abs = path.resolve(relPath);
  if (fs.existsSync(abs)) {
    throw new Error(`Refusing to overwrite existing workspace file in test fixture: ${relPath}`);
  }
  fs.writeFileSync(abs, content);
  tmpKoth.push(abs);
  return relPath;
}
try {
  // Cross-kind rejection: `proof` on record hunt SN-rec-013
  const kProofArt = safeWriteTmpKoth(`missions/sorting-networks/lean/SortNet/Claims/SN_rec_013_test_${kothSalt}.lean`, "import SortNet.Core\n");
  const kProofSub = safeWriteTmpKoth(
    `missions/sorting-networks/submissions/SN-rec-013.proof.test${kothSalt}.json`,
    JSON.stringify({
      schema: "fleet-submission/2",
      mission: "sorting-networks",
      lemma_id: "SN-rec-013",
      kind: "proof",
      file: kProofArt,
      theorem: `SortNet.Claims.SN_rec_013_test_${kothSalt}.record`,
      checker: { ok: true, judge: "lean4", file_hash: "00", by_seat: "donor-x" },
    })
  );
  const rCross1 = verifyPrEntries(parseGitRawZ(rawEntry("100644", "A", kProofArt) + rawEntry("100644", "A", kProofSub)));
  assert(!rCross1.ok && rCross1.reports[0]?.reason?.includes("King-of-the-Hill"), "PR Gate KotH: rejects `proof` on record hunt", JSON.stringify(rCross1));

  // Cross-kind rejection: `record` on normal claim SN-001
  const kRecOnNormArt = safeWriteTmpKoth(`missions/sorting-networks/lean/SortNet/Claims/SN_001_s999_${kothSalt}.lean`, "import SortNet.Core\n");
  const kRecOnNormSub = safeWriteTmpKoth(
    `missions/sorting-networks/submissions/SN-001.record.s999_${kothSalt}.json`,
    JSON.stringify({
      schema: "pf.record.v1",
      mission: "sorting-networks",
      lemma_id: "SN-001",
      kind: "record",
      score: 999,
      file: kRecOnNormArt,
      theorem: `SortNet.Claims.SN_001_s999_${kothSalt}.record`,
      checker: { ok: true, judge: "lean4", file_hash: "00", by_seat: "donor-x" },
    })
  );
  const rCross2 = verifyPrEntries(parseGitRawZ(rawEntry("100644", "A", kRecOnNormArt) + rawEntry("100644", "A", kRecOnNormSub)));
  assert(!rCross2.ok && rCross2.reports[0]?.reason?.includes("not a King-of-the-Hill"), "PR Gate KotH: rejects `record` on normal claim", JSON.stringify(rCross2));

  // Status M edit on record artifact blocked (uses safe non-real score 999 <= score_max 1000!)
  const k999Art = safeWriteTmpKoth("missions/sorting-networks/lean/SortNet/Claims/SN_rec_013_s999.lean", "import SortNet.Core\n");
  const k999Sub = safeWriteTmpKoth(
    "missions/sorting-networks/submissions/SN-rec-013.record.s999.json",
    JSON.stringify({
      schema: "pf.record.v1",
      mission: "sorting-networks",
      lemma_id: "SN-rec-013",
      kind: "record",
      score: 999,
      file: k999Art,
      theorem: "SortNet.Claims.SN_rec_013_s999.record",
      checker: { ok: true, judge: "lean4", file_hash: "00", statement_hash: "00", core_hash: "00", by_seat: "donor-x" },
    })
  );
  const rMod = verifyPrEntries(parseGitRawZ(rawEntry("100644", "M", k999Art) + rawEntry("100644", "A", k999Sub)));
  assert(!rMod.ok && rMod.reports[0]?.reason?.includes("newly added"), "PR Gate KotH: rejects status M edit to record artifact", JSON.stringify(rMod));

  // Non-improving score (998 > 46) rejected before Judge
  const k998Art = safeWriteTmpKoth("missions/sorting-networks/lean/SortNet/Claims/SN_rec_013_s998.lean", "import SortNet.Core\n");
  const k998Sub = safeWriteTmpKoth(
    "missions/sorting-networks/submissions/SN-rec-013.record.s998.json",
    JSON.stringify({
      schema: "pf.record.v1",
      mission: "sorting-networks",
      lemma_id: "SN-rec-013",
      kind: "record",
      score: 998,
      file: k998Art,
      theorem: "SortNet.Claims.SN_rec_013_s998.record",
      checker: { ok: true, judge: "lean4", file_hash: "00", statement_hash: "00", core_hash: "00", by_seat: "donor-x" },
    })
  );
  const rNonImp = verifyPrEntries(parseGitRawZ(rawEntry("100644", "A", k998Art) + rawEntry("100644", "A", k998Sub)));
  assert(!rNonImp.ok && rNonImp.reports[0]?.reason?.includes("does not improve"), "PR Gate KotH: rejects non-improving score 998 > 46", JSON.stringify(rNonImp));

  // 2 record submissions in one PR rejected (BOTH on donor lane AND under --allow-meta!)
  const twoEntries = parseGitRawZ(
    rawEntry("100644", "A", k999Art) +
      rawEntry("100644", "A", k999Sub) +
      rawEntry("100644", "A", k998Art) +
      rawEntry("100644", "A", k998Sub)
  );
  const rTwo = verifyPrEntries(twoEntries);
  const rTwoMeta = verifyPrEntries(twoEntries, { allowInfra: true, allowMeta: true });
  assert(
    !rTwo.ok &&
      rTwo.reason.includes("exactly 1 claim and 1 submission") &&
      !rTwoMeta.ok &&
      rTwoMeta.reports.some((r) => r.reason?.includes("Duplicate or conflicting record submission")),
    "PR Gate KotH: rejects 2 record submissions in one PR (donor AND --allow-meta)",
    JSON.stringify({ rTwo, rTwoMeta })
  );

  // Frozen Statements/SN_rec_013.lean mutation blocked once record history > 0!
  const stmtMut = classifyEntries(parseGitRawZ(rawEntry("100644", "M", "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean")));
  assert(
    stmtMut.frozenStatementMutations.length === 1 && stmtMut.frozenStatementMutations[0].lemma_id === "SN-rec-013",
    "PR Gate KotH: freezes Statements/SN_rec_013.lean once record history > 0",
    JSON.stringify(stmtMut)
  );

  // Deleting a single frozen statement inside a surviving mission STILL fails closed!
  const stmtDelSingle = classifyEntries(parseGitRawZ(rawEntry("000000", "D", "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean")));
  assert(
    stmtDelSingle.lane === "infra" && stmtDelSingle.frozenStatementMutations.length === 1 && stmtDelSingle.retiredMissions.length === 0,
    "PR Gate KotH: deleting a frozen statement in a surviving mission is blocked",
    JSON.stringify(stmtDelSingle)
  );

  // Partial mission retirement (deleting mission.json + state.json while modifying a frozen statement) STILL fails closed!
  const partialRetire = classifyEntries(
    parseGitRawZ(
      rawEntry("000000", "D", "missions/sorting-networks/mission.json") +
        rawEntry("000000", "D", "missions/sorting-networks/state.json") +
        rawEntry("100644", "M", "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean")
    )
  );
  assert(
    partialRetire.lane === "infra" && partialRetire.frozenStatementMutations.length === 1 && partialRetire.retiredMissions.length === 0,
    "PR Gate KotH: partial mission retirement with modified frozen statement is blocked",
    JSON.stringify(partialRetire)
  );

  // Whole-mission retirement (deleting mission.json + state.json + all touched mission files) routes to infra lane cleanly!
  const fullRetire = classifyEntries(
    parseGitRawZ(
      rawEntry("000000", "D", "missions/sorting-networks/mission.json") +
        rawEntry("000000", "D", "missions/sorting-networks/state.json") +
        rawEntry("000000", "D", "missions/sorting-networks/lean/SortNet/Statements/SN_rec_013.lean")
    )
  );
  assert(
    fullRetire.lane === "infra" &&
      fullRetire.frozenStatementMutations.length === 0 &&
      fullRetire.retiredMissions.length === 1 &&
      fullRetire.retiredMissions[0] === "sorting-networks",
    "PR Gate KotH: whole-mission retirement routes to maintainer infra lane with 0 frozen mutations",
    JSON.stringify(fullRetire)
  );
} finally {
  for (const f of tmpKoth) {
    try { fs.unlinkSync(f); } catch {}
  }
}

// ---------------------------------------------------------------------------
// 7. FLEET NEXT CONTEXT, COMMAND-JUDGE (.json) FIX, CHAMPION DIAGNOSTICS & SEARCH-LEMMAS
// ---------------------------------------------------------------------------
{
  const runFleetJson = (args) => {
    const res = spawnSync(process.execPath, ["hub/fleet.mjs", ...args], {
      cwd: path.resolve(import.meta.dirname, ".."),
      encoding: "utf8",
    });
    assert(res.status === 0, `fleet ${args.join(" ")} exits 0`, res.stderr || res.stdout);
    return JSON.parse(res.stdout);
  };

  const mlStateBefore = fs.readFileSync(path.resolve(import.meta.dirname, "..", "missions/ml-math-kernels/state.json"), "utf8");
  const snStateBefore = fs.readFileSync(path.resolve(import.meta.dirname, "..", "missions/sorting-networks/state.json"), "utf8");
  const mlDerived = deriveMissionState("ml-math-kernels").state;
  const rsqrtLive = mlDerived.lemmas.find((l) => l.id === "ML-rec-bf16-rsqrt")?.record_state?.best;
  assert(Boolean(rsqrtLive?.score && rsqrtLive?.file), "fleet next setup: ML-rec-bf16-rsqrt has a live incumbent");

  // 7a. ml-math-kernels pure-data JSON instructions (regression for broken `artifact_ext === ".mjs"` check!)
  // Score-agnostic: works whether ml-math-kernels hunts are unclaimed or already have incumbents.
  const mlNextFirst = runFleetJson(["next", "--mission", "ml-math-kernels", "--offline"]);
  assert(
    mlNextFirst.ok &&
      mlNextFirst.mission === "ml-math-kernels" &&
      mlNextFirst.claim?.record?.artifact_ext === ".json" &&
      mlNextFirst.instructions.some((l) => l.includes("pure-data .json") && l.includes(".json")) &&
      mlNextFirst.instructions.every((l) => !l.includes("Prove `theorem")) &&
      Array.isArray(mlNextFirst.context?.reusable_lemmas) &&
      mlNextFirst.context.reusable_lemmas.length >= 3,
    "fleet next (ml-math-kernels): emits pure-data .json instructions (never Lean theorem) + reusable sister kernels",
    JSON.stringify({ id: mlNextFirst.claim?.id, instructions: mlNextFirst.instructions, reusable: mlNextFirst.context?.reusable_lemmas?.length })
  );

  // 7b. ml-math-kernels incumbent champion + live AlphaEvolve-style BF16 worst-ULP diagnostics
  const excludeExceptRsqrt = mlDerived.lemmas.filter((l) => l.id !== "ML-rec-bf16-rsqrt").map((l) => l.id).join(",");
  const mlNextRsqrt = runFleetJson(["next", "--mission", "ml-math-kernels", "--exclude", excludeExceptRsqrt, "--offline"]);
  assert(
    mlNextRsqrt.ok &&
      mlNextRsqrt.claim?.id === "ML-rec-bf16-rsqrt" &&
      mlNextRsqrt.context?.champion?.score === rsqrtLive.score &&
      mlNextRsqrt.context?.champion?.artifact_file === rsqrtLive.file &&
      mlNextRsqrt.context?.champion?.diagnostics?.tested === 65536 &&
      mlNextRsqrt.context?.champion?.diagnostics?.op_cost <= rsqrtLive.score &&
      /^0x[0-9a-f]{4}$/.test(mlNextRsqrt.context?.champion?.diagnostics?.worst_input_bits || "") &&
      mlNextRsqrt.instructions.some((l) => l.includes(rsqrtLive.file) && l.includes("mutate from")),
    "fleet next (ml-math-kernels incumbent): exposes live champion artifact + 65,536-input BF16 diagnostics & mutation instructions",
    JSON.stringify(mlNextRsqrt.context?.champion)
  );

  // 7c. sorting-networks updated Tomar 2026 bounds: SN-rec-013 at S(13)=45 routes to record-bound 44 + context.champion.phase === "needs_bound"
  const snDerived = deriveMissionState("sorting-networks").state;
  const sn013Live = snDerived.lemmas.find((l) => l.id === "SN-rec-013");
  if (sn013Live && !sn013Live.record_state?.closed && sn013Live.record_state?.best?.score === 45 && !sn013Live.record_state?.refuted) {
    const excludeExceptSn013 = snDerived.lemmas.filter((l) => l.id !== "SN-rec-013").map((l) => l.id).join(",");
    const snNext = runFleetJson(["next", "--mission", "sorting-networks", "--exclude", excludeExceptSn013, "--offline"]);
    assert(
      snNext.ok &&
        snNext.claim?.id === "SN-rec-013" &&
        snNext.context?.champion?.score === 45 &&
        snNext.context?.champion?.literature_bound === 45 &&
        snNext.context?.champion?.phase === "needs_bound" &&
        snNext.instructions.some((l) => l.includes("record-bound") && l.includes("--score 44")) &&
        Array.isArray(snNext.context?.reusable_lemmas) &&
        snNext.context.reusable_lemmas.some((l) => l.id === "SN-001"),
      "fleet next (sorting-networks SN-rec-013): Tomar 2026 S(13)=45 routes to record-bound 44 with reusable lemmas",
      JSON.stringify({ id: snNext.claim?.id, champion: snNext.context?.champion, instructions: snNext.instructions })
    );
  }

  // 7d. p-vs-np includes graveyard_dead_ends (refuted + dead claims digest)
  const pnpNext = runFleetJson(["next", "--mission", "p-vs-np", "--offline"]);
  assert(
    pnpNext.ok &&
      Array.isArray(pnpNext.context?.graveyard_dead_ends) &&
      pnpNext.context.graveyard_dead_ends.length >= 2 &&
      pnpNext.context.graveyard_dead_ends.some((d) => d.status === "refuted") &&
      pnpNext.context.graveyard_dead_ends.some((d) => d.status === "dead"),
    "fleet next (p-vs-np): surfaces graveyard_dead_ends digest of refuted claims and barriers",
    JSON.stringify(pnpNext.context?.graveyard_dead_ends)
  );

  // 7e. fleet search-lemmas: natural-language/keyword discovery over verified lemmas & incumbents
  const searchRsqrt = runFleetJson(["search-lemmas", "--mission", "all", "--query", "rsqrt rmsnorm"]);
  assert(
    searchRsqrt.ok &&
      searchRsqrt.total_matches >= 1 &&
      searchRsqrt.lemmas[0]?.id === "ML-rec-bf16-rsqrt" &&
      searchRsqrt.lemmas[0]?.best_score === rsqrtLive.score &&
      searchRsqrt.lemmas[0]?.file === rsqrtLive.file,
    "fleet search-lemmas: finds ML-rec-bf16-rsqrt live incumbent by natural-language query 'rsqrt rmsnorm'",
    JSON.stringify(searchRsqrt)
  );

  const searchAscon = runFleetJson(["search-lemmas", "--mission", "crypto-zk-circuits", "--query", "ascon"]);
  assert(
    searchAscon.ok &&
      searchAscon.lemmas.some((l) => l.id === "CZ-001") &&
      searchAscon.lemmas.some((l) => l.id === "CZ-rec-ascon-gates"),
    "fleet search-lemmas: finds verified Lean claims & KotH incumbents in crypto-zk-circuits",
    JSON.stringify(searchAscon.lemmas.map((l) => l.id))
  );

  const searchDead = runFleetJson(["search-lemmas", "--mission", "p-vs-np", "--status", "dead", "--query", "natural proofs"]);
  assert(
    searchDead.ok && searchDead.total_matches >= 1 && searchDead.lemmas.every((l) => l.status === "dead"),
    "fleet search-lemmas: supports --status dead barrier lookup",
    JSON.stringify(searchDead)
  );

  // Pure in-memory guarantee: neither fleet next nor fleet search-lemmas mutates state.json!
  assert(
    fs.readFileSync(path.resolve(import.meta.dirname, "..", "missions/ml-math-kernels/state.json"), "utf8") === mlStateBefore &&
      fs.readFileSync(path.resolve(import.meta.dirname, "..", "missions/sorting-networks/state.json"), "utf8") === snStateBefore,
    "fleet next + fleet search-lemmas leave state.json byte-identical"
  );
}

if (failed > 0) {
  console.error(`\n${failed} suite test(s) failed!`);
  process.exit(1);
}
console.log("\nALL REGRESSION, SECURITY-MATRIX, KING-OF-THE-HILL & BUILD TESTS PASSED!");
