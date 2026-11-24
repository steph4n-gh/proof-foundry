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
const n3Entries = parseGitRawZ(rawEntry("100644", "R100", "missions/erdos-combinatorics/artifacts/x.mjs", "hub/judges/lean4.mjs"));
const n3Cls = classifyEntries(n3Entries);
assert(n3Cls.lane === "infra" && n3Cls.reasons.some((r) => r.includes("Disallowed git status")), "N3 (git mv rename) blocked from donor lane", JSON.stringify(n3Cls));

// N4: symlink (mode 120000) rejected on donor lane
const n4Entries = parseGitRawZ(rawEntry("120000", "A", "missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_004.lean"));
const n4Cls = classifyEntries(n4Entries);
assert(n4Cls.lane === "infra" && n4Cls.reasons.some((r) => r.includes("120000")), "N4 (symlink mode 120000) blocked from donor lane", JSON.stringify(n4Cls));

// N5: trailing-space submission filename rejected (NEVER passes with checked:0!)
const n5Entries = parseGitRawZ(rawEntry("100644", "A", "missions/erdos-combinatorics/submissions/E-sch-004.proof.1234567890.json "));
const n5Res = verifyPrEntries(n5Entries);
assert(!n5Res.ok && !n5Res.eligible_for_auto_merge, "N5 (trailing-space submission / checked:0 bypass) rejected", JSON.stringify(n5Res));

// N5b: valid-looking submission path that is MISSING on disk -> HARD FAIL!
const n5bEntries = parseGitRawZ(rawEntry("100644", "A", "missions/erdos-combinatorics/submissions/E-sch-004.proof.0000000000.json"));
const n5bRes = verifyPrEntries(n5bEntries);
assert(!n5bRes.ok && n5bRes.reason.includes("missing"), "N5b (missing submission file on disk) rejected with hard failure", JSON.stringify(n5bRes));

// N10: modifying existing submission (status M) rejected (append-only!)
const n10Entries = parseGitRawZ(rawEntry("100644", "M", "missions/erdos-combinatorics/submissions/E-ram-001.proof.36697e8874.json"));
const n10Cls = classifyEntries(n10Entries);
assert(n10Cls.lane === "infra" && n10Cls.reasons.some((r) => r.includes("newly added")), "N10 (modify existing submission) blocked by append-only rule", JSON.stringify(n10Cls));

// N17: deleting submission (status D) rejected
const n17Entries = parseGitRawZ(rawEntry("000000", "D", "missions/erdos-combinatorics/submissions/E-ram-001.proof.36697e8874.json"));
const n17Cls = classifyEntries(n17Entries);
assert(n17Cls.lane === "infra", "N17 (delete existing submission) blocked", JSON.stringify(n17Cls));

// Temporary submission fixtures inside missions/erdos-combinatorics/submissions for N11, N12, N14, N15, N16
const tmpSubs = [];
function writeTmpSub(relPath, obj) {
  const abs = path.resolve(relPath);
  fs.writeFileSync(abs, JSON.stringify(obj, null, 2));
  tmpSubs.push(abs);
  return parseGitRawZ(rawEntry("100644", "A", relPath));
}
try {
  // N11: duplicate proof for already-checked E-ram-001 rejected!
  const n11E = writeTmpSub("missions/erdos-combinatorics/submissions/E-ram-001.proof.36697e8874.dup.json", {
    schema: "fleet-submission/2",
    mission: "erdos-combinatorics",
    lemma_id: "E-ram-001",
    kind: "proof",
    file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_001.lean",
    theorem: "Erdos.Claims.E_ram_001.ramsey33_gt_five",
    checker: { ok: true, judge: "lean4", file_hash: "36697e8874dc55cde871392d0bb97878b0bedd8c27b25152cc7b16e4ff89c350", axioms: [], by_seat: "donor-dup" },
  });
  const n11R = verifyPrEntries(n11E);
  assert(!n11R.ok && n11R.reports[0]?.reason?.includes("Duplicate proof"), "N11 (duplicate proof on solved E-ram-001) rejected", JSON.stringify(n11R));

  // N12: unbound refutation on checked E-ram-001 citing E_ram_002 rejected!
  const n12E = writeTmpSub("missions/erdos-combinatorics/submissions/E-ram-001.refutation.cf46d9f005.json", {
    schema: "fleet-submission/2",
    mission: "erdos-combinatorics",
    lemma_id: "E-ram-001",
    kind: "refutation",
    file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_002.lean",
    theorem: "Erdos.Claims.E_ram_002.ramsey33_le_six",
    refutation: { file_hash: "cf46d9f005", axioms: ["propext"], by_seat: "donor-evil" },
  });
  const n12R = verifyPrEntries(n12E);
  assert(!n12R.ok && n12R.reports[0]?.reason?.includes("Unbound refutation"), "N12 (unbound refutation on checked claim) rejected", JSON.stringify(n12R));

  // N15: self-certifying audit JSON rejected on donor lane!
  const n15E = writeTmpSub("missions/erdos-combinatorics/submissions/E-erd128-003.audit.1111111111.json", {
    schema: "fleet-submission/2",
    mission: "erdos-combinatorics",
    lemma_id: "E-erd128-003",
    kind: "audit",
    audit: { status: "faithful", by_seat: "donor-self", file_hash: "1111111111" },
  });
  const n15R = verifyPrEntries(n15E);
  assert(!n15R.ok && n15R.reports[0]?.reason?.includes("maintainer review"), "N15 (self-certifying audit JSON) rejected", JSON.stringify(n15R));

  // N16: mission directory mismatch (erdos dir claiming p-vs-np) rejected!
  const n16E = writeTmpSub("missions/erdos-combinatorics/submissions/L-lib-000.proof.0f522adda1.json", {
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

  // N14: forged checker.statement_frozen:true & impersonated by_seat:"seat-strat-1" on real valid artifact S_num_001 -> rejected by verdict binding!
  // Test on unsolved S-num-002 using a temp valid artifact copy!
  const sciArtRel = "missions/verified-science-kernels/artifacts/S_num_002.mjs";
  const sciArtAbs = path.resolve(sciArtRel);
  const hadS2 = fs.existsSync(sciArtAbs);
  if (!hadS2) {
    fs.writeFileSync(
      sciArtAbs,
      `const buf = new ArrayBuffer(8), f64 = new Float64Array(buf), i64 = new BigInt64Array(buf);
function nextUp(x){ if(!Number.isFinite(x)) return x; if(x===0) return Number.MIN_VALUE; f64[0]=x; i64[0]+=(x>0?1n:-1n); return f64[0]; }
function nextDown(x){ if(!Number.isFinite(x)) return x; if(x===0) return -Number.MIN_VALUE; f64[0]=x; i64[0]+=(x>0?-1n:1n); return f64[0]; }
export function intervalAdd([a,b],[c,d]){ return [nextDown(a+c), nextUp(b+d)]; }
`
    );
    tmpSubs.push(sciArtAbs);
    const s2Hash = crypto.createHash("sha256").update(fs.readFileSync(sciArtAbs)).digest("hex");
    const n14SubRel = `missions/verified-science-kernels/submissions/S-num-002.proof.${s2Hash.slice(0, 10)}.json`;
    const n14Entries = parseGitRawZ(
      rawEntry("100644", "A", sciArtRel) + rawEntry("100644", "A", n14SubRel)
    );
    fs.writeFileSync(
      path.resolve(n14SubRel),
      JSON.stringify({
        schema: "fleet-submission/2",
        mission: "verified-science-kernels",
        lemma_id: "S-num-002",
        kind: "proof",
        file: sciArtRel,
        theorem: "interval_add_soundness",
        checker: {
          ok: true,
          judge: "command",
          file_hash: s2Hash,
          statement_frozen: true, // FORGED! command judge does not set statement_frozen:true
          axioms: ["outward_rounding_1e16_plus_1", "containment_battery"],
          by_seat: "seat-strat-1", // FORGED internal seat impersonation!
        },
      })
    );
    tmpSubs.push(path.resolve(n14SubRel));
    const n14R = verifyPrEntries(n14Entries);
    assert(
      !n14R.ok && n14R.reports[0]?.reason?.includes("statement_frozen mismatch") && n14R.reports[0]?.reason?.includes("by_seat"),
      "N14 (forged statement_frozen:true + seat-strat-1 impersonation) rejected by verdict binding",
      JSON.stringify(n14R)
    );

    // Positive control on S-num-002 with honest fields (including core_hash) -> PASSES!
    const sciCoreHash = crypto
      .createHash("sha256")
      .update(fs.readFileSync(path.resolve("missions/verified-science-kernels/judge/verify.mjs")))
      .digest("hex");

    // N14b: missing core_hash on donor proof PR -> rejected!
    fs.writeFileSync(
      path.resolve(n14SubRel),
      JSON.stringify({
        schema: "fleet-submission/2",
        mission: "verified-science-kernels",
        lemma_id: "S-num-002",
        kind: "proof",
        file: sciArtRel,
        theorem: "interval_add_soundness",
        checker: {
          ok: true,
          judge: "command",
          file_hash: s2Hash,
          statement_frozen: false,
          axioms: ["containment_battery", "outward_rounding_1e16_plus_1"],
          by_seat: "donor-test-ok",
        },
      })
    );
    const missingCoreR = verifyPrEntries(n14Entries);
    assert(
      !missingCoreR.ok && missingCoreR.reports[0]?.reason?.includes("core_hash mismatch"),
      "N14b (missing core_hash on donor proof PR) rejected by verdict binding",
      JSON.stringify(missingCoreR)
    );

    fs.writeFileSync(
      path.resolve(n14SubRel),
      JSON.stringify({
        schema: "fleet-submission/2",
        mission: "verified-science-kernels",
        lemma_id: "S-num-002",
        kind: "proof",
        file: sciArtRel,
        theorem: "interval_add_soundness",
        signature: "intervalAdd(a, b) : outward-rounded containment for non-representable float64 sums",
        checker: {
          ok: true,
          judge: "command",
          file_hash: s2Hash,
          core_hash: sciCoreHash,
          statement_frozen: false,
          axioms: ["containment_battery", "outward_rounding_1e16_plus_1"],
          by_seat: "donor-test-ok",
        },
      })
    );
    const posR = verifyPrEntries(n14Entries);
    assert(posR.ok && posR.checked === 1 && !posR.eligible_for_auto_merge, "Positive control: honest S-num-002 donor PR passes verify-pr (non-frozen -> not auto-mergeable)", JSON.stringify(posR));

    // N14e-omit (Daybreak P3): omitting required signature on donor proof PR rejected (fail-closed)
    fs.writeFileSync(
      path.resolve(n14SubRel),
      JSON.stringify({
        schema: "fleet-submission/2",
        mission: "verified-science-kernels",
        lemma_id: "S-num-002",
        kind: "proof",
        file: sciArtRel,
        theorem: "interval_add_soundness",
        checker: {
          ok: true,
          judge: "command",
          file_hash: s2Hash,
          core_hash: sciCoreHash,
          statement_frozen: false,
          axioms: ["containment_battery", "outward_rounding_1e16_plus_1"],
          by_seat: "donor-test-ok",
        },
      })
    );
    const omitSigR = verifyPrEntries(n14Entries);
    assert(
      !omitSigR.ok && omitSigR.reports[0]?.reason?.includes("signature mismatch"),
      "N14e-omit (Daybreak P3: omitted sub.signature on donor proof PR rejected fail-closed)",
      JSON.stringify(omitSigR)
    );

    // N14e (Daybreak P2-1): forged sub.signature or forged checker.statement_hash rejected by verdict binding!
    fs.writeFileSync(
      path.resolve(n14SubRel),
      JSON.stringify({
        schema: "fleet-submission/2",
        mission: "verified-science-kernels",
        lemma_id: "S-num-002",
        kind: "proof",
        file: sciArtRel,
        theorem: "interval_add_soundness",
        signature: "FORGED_SIGNATURE_CLAIMING_DIFFERENT_THEOREM",
        checker: {
          ok: true,
          judge: "command",
          file_hash: s2Hash,
          core_hash: sciCoreHash,
          statement_hash: "forged_statement_hash_0000",
          statement_frozen: false,
          axioms: ["containment_battery", "outward_rounding_1e16_plus_1"],
          by_seat: "donor-test-ok",
        },
      })
    );
    const forgedMetaR = verifyPrEntries(n14Entries);
    assert(
      !forgedMetaR.ok &&
        forgedMetaR.reports[0]?.reason?.includes("signature mismatch") &&
        forgedMetaR.reports[0]?.reason?.includes("statement_hash mismatch"),
      "N14e (P2-1 forged sub.signature + forged statement_hash) rejected by verdict binding",
      JSON.stringify(forgedMetaR)
    );

    // N14f (Daybreak P2-1/P3): forged and omitted record signature rejected fail-closed on donor record PR
    const mlRecTmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "pf-rec-sig-"));
    try {
      const mlArtRel = "missions/ml-math-kernels/artifacts/ML_rec_bf16_exp2_s18.json";
      const mlSubRel = "missions/ml-math-kernels/submissions/ML-rec-bf16-exp2.record.s18.json";
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

    // N14c: Command-Judge double sandbox blocks untrusted import/fs escape attempts inside untrusted .mjs!
    fs.writeFileSync(
      sciArtAbs,
      `import fs from "node:fs";
fs.readFileSync("/etc/hosts", "utf8");
export function intervalAdd([a,b],[c,d]){ return [a+c, b+d]; }
`
    );
    const s2Escape = runJudge(loadMission("verified-science-kernels"), {
      file: sciArtRel,
      target: "interval_add_soundness",
      kind: "proof",
    });
    assert(
      !s2Escape.ok && /cannot use import|ERR_ACCESS_DENIED|Isolated artifact runner failed/.test(s2Escape.reason || ""),
      "N14c (Command-Judge double sandbox blocks untrusted import/fs escape)",
      JSON.stringify(s2Escape)
    );

    // N14d: Pure-data minimax parser rejects executable JS imports/code without ever executing it!
    const evilRecRel = "missions/verified-science-kernels/artifacts/S_rec_exp_s449.mjs";
    const evilRecAbs = path.resolve(evilRecRel);
    fs.writeFileSync(
      evilRecAbs,
      `import fs from "node:fs";
fs.writeFileSync("/tmp/should_never_exist_pf", "pwn");
export const coeffs = [1, 1, 0.5, 0.16666667, 0.04166667, 0.00833333, 0.00138889, 0.00019841];
`
    );
    tmpSubs.push(evilRecAbs);
    const evilRecRes = runJudge(loadMission("verified-science-kernels"), {
      file: evilRecRel,
      target: "minimax_exp_deg7",
      kind: "record",
      expectedScore: 449,
      statementFile: "missions/verified-science-kernels/specs/S_rec_exp.json",
    });
    assert(
      !evilRecRes.ok && !fs.existsSync("/tmp/should_never_exist_pf"),
      "N14d (Pure-data minimax parser rejects executable JS with zero code execution)",
      JSON.stringify(evilRecRes)
    );
  }
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
const beforeErdos = fs.readFileSync("missions/erdos-combinatorics/state.json", "utf8");
const buildRun = spawnSync("node", ["hub/build_site.mjs", "--offline"], { encoding: "utf8" });
const afterErdos = fs.readFileSync("missions/erdos-combinatorics/state.json", "utf8");
assert(buildRun.status === 0 && beforeErdos === afterErdos && fs.existsSync("dist/PROOFS.md"), "build_site.mjs is pure (state.json byte-identical) & emits dist/PROOFS.md", buildRun.stderr);

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

// Sanity check deriveMissionState idempotence across all missions
const d1 = deriveMissionState("erdos-combinatorics").state;
const d2 = deriveMissionState("erdos-combinatorics").state;
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
  meta: { mission: "erdos-combinatorics", updated_at: "2026-01-01T00:00:00Z" },
  programs: [{ id: "ramsey", key: "ram", title: "Ramsey" }],
  seats: [],
  lemmas: [
    {
      id: "E-rec-r55",
      kind: "record",
      program: "ramsey",
      title: "R(5,5) Max Hunt",
      statement_file: "missions/erdos-combinatorics/lean/Erdos/Statements/E_rec_r55.lean",
      statement_def: "Erdos.Statements.E_rec_r55.Record",
      record: {
        direction: "max",
        unit: "vertices",
        start_target: 36,
        literature_best: 42,
        literature_upper_bound: 47,
        bound_floor: 48,
        score_max: 100,
        file_stem: "E_rec_r55",
        claims_dir: "missions/erdos-combinatorics/lean/Erdos/Claims",
        theorem_template: "Erdos.Claims.E_rec_r55_{tag}.record",
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
  const t = computeRecordTargets("erdos-combinatorics", maxSeed.lemmas[0], kind, score);
  return {
    _sub_file: t.submissionBasename,
    schema: "pf.record.v1",
    mission: "erdos-combinatorics",
    lemma_id: "E-rec-r55",
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
  statementHashes: { "missions/erdos-combinatorics/lean/Erdos/Statements/E_rec_r55.lean": "max_stmt" },
};
const m38 = mkMaxSub("record", 38, "donor-m1");
const m42 = mkMaxSub("record", 42, "donor-m2");
const m48Ub = mkMaxSub("record_bound", 48, "donor-u1");
const m43Ub = mkMaxSub("record_bound", 43, "donor-u2");
const maxState = applySubmissionsPure(maxSeed, [m42, m38, m48Ub, m43Ub], {
  missionSlug: "erdos-combinatorics",
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

// Command-Judge pure-data minimax KotH test (S-rec-exp)
const sciMission = loadMission("verified-science-kernels");
const tmpSciDir = fs.mkdtempSync(path.join(os.tmpdir(), "pf-sci-koth-"));
try {
  const expArt = path.join(tmpSciDir, "S_rec_exp_s450.mjs");
  // Degree-7 Chebyshev coefficients on [-ln2/2, ln2/2] (max error ~413 * 1e-13)
  fs.writeFileSync(
    expArt,
    `export const coeffs = [1.0000000000040923, 0.9999999999944174, 0.4999999990773131, 0.1666666668018312, 0.0416666898932322, 0.0083333301573068, 0.0013887439344572, 0.0001984316503399];\n`
  );
  // Wait: compute exact Chebyshev inside the test so rounding never drifts!
  const M = 64, a = Math.LN2 / 2, deg = 7, c = new Array(deg + 1).fill(0);
  for (let j = 0; j <= deg; j++) {
    let s = 0;
    for (let k = 0; k < M; k++) { const th = (Math.PI * (k + 0.5)) / M; s += Math.exp(a * Math.cos(th)) * Math.cos(j * th); }
    c[j] = (2 / M) * s;
  }
  c[0] /= 2;
  const mono = new Array(deg + 1).fill(0);
  let Tprev = [1], Tcur = [0, 1 / a];
  for (let j = 0; j <= deg; j++) {
    const T = j === 0 ? Tprev : j === 1 ? Tcur : (() => {
      const nxt = new Array(j + 1).fill(0);
      for (let k = 0; k < Tcur.length; k++) nxt[k + 1] += (2 / a) * Tcur[k];
      for (let k = 0; k < Tprev.length; k++) nxt[k] -= Tprev[k];
      Tprev = Tcur; Tcur = nxt; return nxt;
    })();
    for (let k = 0; k < T.length; k++) mono[k] += c[j] * T[k];
  }
  fs.writeFileSync(expArt, `export const coeffs = ${JSON.stringify(mono)};\n`);
  const rCmdPass = checkCommandArtifact(expArt, "minimax_exp_deg7", {
    judgeConfig: sciMission.judge,
    kind: "record",
    statementFile: "missions/verified-science-kernels/specs/S_rec_exp.json",
    expectedScore: 450,
    allowTempForTests: true,
  });
  const rCmdFail = checkCommandArtifact(expArt, "minimax_exp_deg7", {
    judgeConfig: sciMission.judge,
    kind: "record",
    statementFile: "missions/verified-science-kernels/specs/S_rec_exp.json",
    expectedScore: 100,
    allowTempForTests: true,
  });
  const rCmdBound = checkCommandArtifact(expArt, "minimax_exp_deg7", {
    judgeConfig: sciMission.judge,
    kind: "record_bound",
    statementFile: "missions/verified-science-kernels/specs/S_rec_exp.json",
    expectedScore: 390,
    allowTempForTests: true,
  });
  assert(
    rCmdPass.ok && rCmdPass.score === 450 && rCmdPass.statement_frozen === true && !rCmdFail.ok && !rCmdBound.ok,
    "Command-Judge KotH (S-rec-exp 128-bit BigInt oracle): passes ≤450, rejects ≤100, rejects record_bound",
    JSON.stringify({ rCmdPass, rCmdFail, rCmdBound })
  );
} finally {
  fs.rmSync(tmpSciDir, { recursive: true, force: true });
}

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

  // Cross-kind rejection: `record` on normal claim E-ram-001
  const kRecOnNormArt = safeWriteTmpKoth(`missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_001_s999_${kothSalt}.lean`, "import Erdos.Core\n");
  const kRecOnNormSub = safeWriteTmpKoth(
    `missions/erdos-combinatorics/submissions/E-ram-001.record.s999_${kothSalt}.json`,
    JSON.stringify({
      schema: "pf.record.v1",
      mission: "erdos-combinatorics",
      lemma_id: "E-ram-001",
      kind: "record",
      score: 999,
      file: kRecOnNormArt,
      theorem: `Erdos.Claims.E_ram_001_s999_${kothSalt}.record`,
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
} finally {
  for (const f of tmpKoth) {
    try { fs.unlinkSync(f); } catch {}
  }
}

if (failed > 0) {
  console.error(`\n${failed} suite test(s) failed!`);
  process.exit(1);
}
console.log("\nALL REGRESSION, SECURITY-MATRIX, KING-OF-THE-HILL & BUILD TESTS PASSED!");
