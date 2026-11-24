#!/usr/bin/env node
/**
 * hub/pr_gate.mjs — Single-Source-of-Truth PR Diff Classifier, Safe Stager & Submission Verifier (v4).
 *
 * Supports both fixed frozen bounties (`proof`/`refutation`) AND King-of-the-Hill auto-ratcheting
 * record hunts (`record`/`record_bound`) with full P0/P1 security invariants from Opus 5.5 + Astra 6.2.
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { ROOT, loadMission, deriveMissionState, computeRecordTargets } from "./missions.mjs";
import { sha256RelFile } from "./state_machine.mjs";
import { runJudge } from "./judges/index.mjs";
import { validateCanonicalNatScore } from "./judges/lean4.mjs";

export const ALLOWED_SUBMISSION_RE = /^missions\/([a-z0-9-_]+)\/submissions\/([A-Za-z0-9_.-]+)\.json$/;
export const ALLOWED_ARTIFACT_RE =
  /^(missions\/([a-z0-9-_]+)\/(artifacts\/[A-Za-z0-9_.-]+|lean\/[A-Za-z0-9_]+\/Claims\/[A-Za-z0-9_]+\.lean)|lean\/PnP\/Lemmas\/[A-Za-z0-9_]+\.lean)$/;
export const DONOR_SEAT_RE = /^(donor|ext|contrib)-[a-z0-9-_]{1,32}$/;

export function parseGitRawZ(rawBufOrStr) {
  const str = Buffer.isBuffer(rawBufOrStr) ? rawBufOrStr.toString("utf8") : String(rawBufOrStr || "");
  if (!str) return [];
  const tokens = str.split("\0");
  const entries = [];
  let i = 0;
  while (i < tokens.length) {
    const meta = tokens[i];
    if (!meta) {
      i++;
      continue;
    }
    const m = meta.match(/^:(\d{6})\s+(\d{6})\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([A-Z]\d*)$/);
    if (!m) {
      throw new Error(`Malformed git raw -z metadata token: ${JSON.stringify(meta)}`);
    }
    const status = m[5];
    if (status.startsWith("R") || status.startsWith("C")) {
      const oldPath = tokens[i + 1] ?? "";
      const newPath = tokens[i + 2] ?? "";
      entries.push({ oldMode: m[1], newMode: m[2], oldSha: m[3], newSha: m[4], status, path: newPath, oldPath });
      i += 3;
    } else {
      const filePath = tokens[i + 1] ?? "";
      entries.push({ oldMode: m[1], newMode: m[2], oldSha: m[3], newSha: m[4], status, path: filePath });
      i += 2;
    }
  }
  return entries;
}

export function entriesFromPaths(paths) {
  return paths
    .filter((p) => p.length > 0)
    .map((p) => ({ oldMode: "000000", newMode: "100644", oldSha: "0", newSha: "0", status: "A", path: p }));
}

function missionSlugFromPath(p) {
  const m = p.match(/^missions\/([a-z0-9-_]+)\//);
  if (m) return m[1];
  if (p.startsWith("lean/PnP/")) return "p-vs-np";
  return null;
}

/**
 * Pure data-only PR diff classification (NEVER executes PR code!).
 * Freezes `Statements/*.lean` once a claim has ANY accepted proof, refutation, OR record history!
 */
export function classifyEntries(entries) {
  const reasons = [];
  const submissionEntries = [];
  const artifactEntries = [];
  const missionsTouched = new Set();
  const frozenStatementMutations = [];

  if (!entries.length) {
    return {
      lane: "infra",
      reasons: ["Empty diff"],
      submissionEntries: [],
      artifactEntries: [],
      needsLean: false,
      frozenStatementMutations: [],
    };
  }

  for (const e of entries) {
    const p = e.path;
    const ms = missionSlugFromPath(p);
    if (ms) missionsTouched.add(ms);

    if ((/\/Statements\/[A-Za-z0-9_]+\.lean$/.test(p) || /\/specs\/[A-Za-z0-9_]+\.json$/.test(p)) && e.status !== "A") {
      if (ms) {
        try {
          const { state } = deriveMissionState(ms);
          const matched = (state.lemmas || []).find(
            (l) =>
              l.statement_file === p &&
              (l.status === "checked" ||
                l.status === "refuted" ||
                l.status === "contradiction" ||
                (l.record_state?.history?.length || 0) > 0)
          );
          if (matched) {
            frozenStatementMutations.push({ path: p, lemma_id: matched.id });
          }
        } catch (err) {
          frozenStatementMutations.push({ path: p, lemma_id: "unverifiable-base-state" });
          reasons.push(`Could not verify frozen-statement immutability for ${p}: ${err?.message || err}`);
        }
      }
    }

    if (p.includes("..") || p !== p.trim() || /[\r\n\t]/.test(p)) {
      reasons.push(`Invalid or whitespace-padded path: ${JSON.stringify(p)}`);
      continue;
    }
    if (e.status !== "A" && e.status !== "M") {
      reasons.push(`Disallowed git status "${e.status}" on ${p} (renames, deletions, typechanges forbidden on donor lane)`);
      continue;
    }
    if (e.newMode !== "100644") {
      reasons.push(`Disallowed git mode "${e.newMode}" on ${p} (only regular 100644 files allowed; symlinks/submodules forbidden)`);
      continue;
    }
    if (ALLOWED_SUBMISSION_RE.test(p)) {
      if (e.status !== "A") {
        reasons.push(`Submission file ${p} must be newly added (status A), not modified (${e.status})`);
        continue;
      }
      submissionEntries.push(e);
      continue;
    }
    if (ALLOWED_ARTIFACT_RE.test(p)) {
      artifactEntries.push(e);
      continue;
    }
    reasons.push(`Path outside donor allowlist: ${p}`);
  }

  let needsLean = false;
  for (const ms of missionsTouched) {
    try {
      const m = loadMission(ms);
      if (m.judge?.type === "lean4") needsLean = true;
    } catch {}
  }
  if (entries.some((e) => e.path.endsWith(".lean"))) needsLean = true;

  const isDonor = reasons.length === 0 && submissionEntries.length > 0;
  return {
    lane: isDonor ? "donor" : "infra",
    reasons,
    submissionEntries,
    artifactEntries,
    needsLean,
    frozenStatementMutations,
  };
}

export function stageAllowlistedEntries(entries, gitRef = "pr-head", rootDir = ROOT) {
  const staged = [];
  for (const e of entries) {
    if ((e.status !== "A" && e.status !== "M") || e.newMode !== "100644") continue;
    if (e.path.includes("..") || e.path !== e.path.trim()) continue;
    if (!ALLOWED_SUBMISSION_RE.test(e.path) && !ALLOWED_ARTIFACT_RE.test(e.path)) continue;

    const show = spawnSync("git", ["show", `${gitRef}:${e.path}`], { cwd: rootDir, maxBuffer: 20 * 1024 * 1024 });
    if (show.status !== 0) {
      throw new Error(`Failed to stage ${e.path} from ${gitRef}: ${(show.stderr || "").toString("utf8")}`);
    }
    const dst = path.resolve(rootDir, e.path);
    if (!dst.startsWith(path.resolve(rootDir) + path.sep)) {
      throw new Error(`Path escape blocked while staging ${e.path}`);
    }
    fs.mkdirSync(path.dirname(dst), { recursive: true });
    fs.writeFileSync(dst, show.stdout);
    staged.push(e.path);
  }
  return staged;
}

function sameSortedStrings(a, b) {
  const sa = [...(Array.isArray(a) ? a : [])].map(String).sort();
  const sb = [...(Array.isArray(b) ? b : [])].map(String).sort();
  return sa.length === sb.length && sa.every((v, i) => v === sb[i]);
}

export function validateRecordImprovement(registered, kind, score) {
  const cfg = registered.record || {};
  const dir = cfg.direction === "max" ? "max" : "min";
  const startTarget = Number(cfg.start_target ?? 0);
  const boundFloor = Number(cfg.bound_floor ?? 0);
  const scoreMax = Number(cfg.score_max ?? 100000);
  const rs = registered.record_state || { best: null, refuted: null, closed: false, contradiction: false };

  if (kind === "record_bound" && cfg.allow_bound === false) {
    return { ok: false, requiresMaintainer: false, reason: `Bound proofs (record_bound) are not supported on ${registered.id}` };
  }
  if (!Number.isSafeInteger(score) || score < 0 || score > scoreMax) {
    return { ok: false, requiresMaintainer: false, reason: `Score ${score} out of allowed bounds [0, ${scoreMax}]` };
  }
  if (rs.closed || rs.contradiction) {
    return { ok: false, requiresMaintainer: true, reason: `Record hunt ${registered.id} is already ${rs.contradiction ? "in contradiction" : "closed (exact optimal)"}` };
  }

  let requiresMaintainer = false;
  if (kind === "record") {
    const improves =
      dir === "min"
        ? rs.best
          ? score < rs.best.score
          : score <= startTarget
        : rs.best
        ? score > rs.best.score
        : score >= startTarget;
    if (!improves) {
      const want = rs.best ? (dir === "min" ? `< ${rs.best.score}` : `> ${rs.best.score}`) : (dir === "min" ? `≤ ${startTarget}` : `≥ ${startTarget}`);
      return { ok: false, requiresMaintainer: false, reason: `Score ${score} does not improve current record (need ${want})` };
    }
    if (rs.refuted && (dir === "min" ? score <= rs.refuted.score : score >= rs.refuted.score)) {
      return {
        ok: false,
        requiresMaintainer: true,
        reason: `Score ${score} contradicts verified lower bound ¬ Record ${rs.refuted.score} — requires maintainer audit`,
      };
    }
    // Breakthrough guard (Opus 5.5 #10): beating literature_best triggers maintainer + cross-model audit!
    if (cfg.literature_best != null && (dir === "min" ? score < cfg.literature_best : score > cfg.literature_best)) {
      requiresMaintainer = true;
    }
  } else if (kind === "record_bound") {
    const improves =
      dir === "min"
        ? rs.refuted
          ? score > rs.refuted.score
          : score >= boundFloor
        : rs.refuted
        ? score < rs.refuted.score
        : score <= boundFloor;
    if (!improves) {
      const want = rs.refuted ? (dir === "min" ? `> ${rs.refuted.score}` : `< ${rs.refuted.score}`) : (dir === "min" ? `≥ ${boundFloor}` : `≤ ${boundFloor}`);
      return { ok: false, requiresMaintainer: false, reason: `Bound ¬ Record ${score} does not improve current bound (need ${want})` };
    }
    if (rs.best && (dir === "min" ? score >= rs.best.score : score <= rs.best.score)) {
      return {
        ok: false,
        requiresMaintainer: true,
        reason: `Bound ¬ Record ${score} contradicts current incumbent score ${rs.best.score} — requires maintainer audit`,
      };
    }
    if (cfg.literature_lower_bound != null && dir === "min" && score + 1 > cfg.literature_lower_bound) {
      requiresMaintainer = true;
    }
    if (cfg.literature_upper_bound != null && dir === "max" && score - 1 < cfg.literature_upper_bound) {
      requiresMaintainer = true;
    }
  }
  return { ok: true, requiresMaintainer, reason: "" };
}

/**
 * Pure data-only auto-merge eligibility check (NEVER executes PR files!).
 */
export function evaluateAutoMergeDataOnly(entries, gitRef = "pr-head", rootDir = ROOT) {
  const cls = classifyEntries(entries);
  if (cls.lane !== "donor") {
    return { eligible: false, reasons: [`Not a pure donor PR (${cls.reasons.join("; ")})`] };
  }
  if (cls.submissionEntries.length !== 1 || cls.artifactEntries.length !== 1) {
    return { eligible: false, reasons: [`Auto-merge requires exactly 1 submission JSON and 1 artifact file`] };
  }

  const sf = cls.submissionEntries[0].path;
  const af = cls.artifactEntries[0];
  const sm = sf.match(ALLOWED_SUBMISSION_RE);
  const dirSlug = sm[1];

  const show = spawnSync("git", ["show", `${gitRef}:${sf}`], { cwd: rootDir, encoding: "utf8", maxBuffer: 5 * 1024 * 1024 });
  if (show.status !== 0) return { eligible: false, reasons: [`Could not read ${sf} from ${gitRef}`] };

  let sub;
  try {
    sub = JSON.parse(show.stdout);
  } catch {
    return { eligible: false, reasons: [`Invalid JSON in ${sf}`] };
  }

  if (sub.mission !== dirSlug) {
    return { eligible: false, reasons: [`Mission mismatch: JSON says "${sub.mission}", path says "${dirSlug}"`] };
  }

  const { state: baseState } = deriveMissionState(dirSlug);
  const registered = baseState.lemmas.find((l) => l.id === sub.lemma_id);
  if (!registered) {
    return { eligible: false, reasons: [`Unknown claim ID "${sub.lemma_id}" in "${dirSlug}"`] };
  }
  if (!registered.statement_file || !registered.statement_def) {
    return { eligible: false, reasons: [`Claim "${sub.lemma_id}" is not a frozen-statement bounty`] };
  }

  // King-of-the-Hill record branch (data-only)
  if (sub.kind === "record" || sub.kind === "record_bound") {
    if (registered.kind !== "record") {
      return { eligible: false, reasons: [`Claim "${sub.lemma_id}" is not a record hunt`] };
    }
    if (af.status !== "A") {
      return { eligible: false, reasons: [`Record artifact ${af.path} must be newly added (status A)`] };
    }
    const scoreStr = validateCanonicalNatScore(sub.score);
    if (typeof sub.score !== "number" || !Number.isSafeInteger(sub.score) || scoreStr === null || String(sub.score) !== scoreStr) {
      return { eligible: false, reasons: [`Invalid canonical score ${JSON.stringify(sub.score)}`] };
    }
    const score = Number(scoreStr);
    const expected = computeRecordTargets(dirSlug, registered, sub.kind, score);
    if (path.basename(sf) !== expected.submissionBasename || af.path !== expected.artifactFile || sub.file !== expected.artifactFile || sub.theorem !== expected.theoremName) {
      return { eligible: false, reasons: [`Record paths/theorem do not match canonical score-stamped names`] };
    }
    if (!DONOR_SEAT_RE.test(String(sub.checker?.by_seat || ""))) {
      return { eligible: false, reasons: [`Donor seat "${sub.checker?.by_seat}" must match donor-/ext-/contrib- prefix`] };
    }
    const check = validateRecordImprovement(registered, sub.kind, score);
    if (!check.ok) return { eligible: false, reasons: [check.reason] };
    if (check.requiresMaintainer) {
      return { eligible: false, reasons: [`Breakthrough past literature bound requires maintainer + cross-model audit`] };
    }
    return { eligible: true, mission: dirSlug, lemma_id: sub.lemma_id, kind: sub.kind, score, reasons: [] };
  }

  if (sub.kind !== "proof" && sub.kind !== "refutation") {
    return { eligible: false, reasons: [`Metadata submission kind "${sub.kind}" is never auto-mergeable`] };
  }
  if (registered.kind === "record") {
    return { eligible: false, reasons: [`Use record/record_bound for record hunt "${sub.lemma_id}"`] };
  }
  if (registered.status !== "conjecture" && registered.status !== "in_work") {
    return { eligible: false, reasons: [`Claim "${sub.lemma_id}" is already ${registered.status} on main`] };
  }
  if (af.path !== sub.file || (sub.kind === "proof" && sub.file !== registered.lean_file)) {
    return { eligible: false, reasons: [`Artifact path mismatch on ${af.path}`] };
  }
  const bySeat = sub.kind === "proof" ? sub.checker?.by_seat : sub.refutation?.by_seat;
  if (!DONOR_SEAT_RE.test(String(bySeat || ""))) {
    return { eligible: false, reasons: [`Donor seat "${bySeat}" must match donor-/ext-/contrib- prefix`] };
  }

  return { eligible: true, mission: dirSlug, lemma_id: sub.lemma_id, kind: sub.kind, reasons: [] };
}

/**
 * Full mechanical Judge verification of PR entries on a staged trusted base checkout.
 */
export function verifyPrEntries(entries, { allowInfra = false, allowMeta = false, rootDir = ROOT } = {}) {
  const cls = classifyEntries(entries);
  const reasons = [];

  if (cls.frozenStatementMutations.length > 0) {
    return {
      ok: false,
      eligible_for_auto_merge: false,
      requires_maintainer: true,
      checked: 0,
      reports: [],
      reason: `Immutable frozen statement(s) already have accepted proofs or record history and cannot be modified: ${cls.frozenStatementMutations.map((x) => `${x.path} (${x.lemma_id})`).join(", ")}`,
    };
  }

  if (!allowInfra && cls.lane !== "donor") {
    return {
      ok: false,
      eligible_for_auto_merge: false,
      requires_maintainer: true,
      checked: 0,
      reports: [],
      reason: `PR violates strict donor allowlist: ${cls.reasons.join("; ")}`,
      disallowed: cls.reasons,
    };
  }

  const subEntries = cls.submissionEntries;
  if (!subEntries.length) {
    if (allowInfra) {
      return { ok: true, eligible_for_auto_merge: false, requires_maintainer: false, checked: 0, reports: [], message: "Infra PR with no submissions" };
    }
    return {
      ok: false,
      eligible_for_auto_merge: false,
      requires_maintainer: false,
      checked: 0,
      reports: [],
      reason: "Donor PR must include at least one newly added missions/<slug>/submissions/*.json record",
    };
  }

  for (const e of [...subEntries, ...cls.artifactEntries]) {
    const abs = path.resolve(rootDir, e.path);
    if (!fs.existsSync(abs) || fs.lstatSync(abs).isSymbolicLink()) {
      return {
        ok: false,
        eligible_for_auto_merge: false,
        requires_maintainer: false,
        checked: 0,
        reports: [],
        reason: `Listed PR file missing or symlink on disk: ${e.path}`,
      };
    }
  }

  const prSubBasenamesByMission = {};
  for (const se of subEntries) {
    const m = se.path.match(ALLOWED_SUBMISSION_RE);
    const dirSlug = m[1];
    (prSubBasenamesByMission[dirSlug] = prSubBasenamesByMission[dirSlug] || []).push(path.basename(se.path));
  }
  const baseStates = {};
  const getBaseState = (slug) => {
    if (!baseStates[slug]) {
      baseStates[slug] = deriveMissionState(slug, { excludeSubmissionFiles: prSubBasenamesByMission[slug] || [] }).state;
    }
    return baseStates[slug];
  };

  // Block `M` edits to ANY solved claim artifact OR ANY historical record artifact!
  for (const ae of cls.artifactEntries) {
    if (ae.status === "M" && !allowInfra) {
      const ms = missionSlugFromPath(ae.path);
      if (ms) {
        const bState = getBaseState(ms);
        const solvedOwner = bState.lemmas.find(
          (l) =>
            (l.lean_file === ae.path || l.refutation?.counterexample_file === ae.path) &&
            (l.status === "checked" || l.status === "refuted" || l.status === "contradiction")
        );
        const recordOwner = bState.lemmas.find(
          (l) => l.kind === "record" && (l.record_state?.history || []).some((h) => h.file === ae.path)
        );
        if (solvedOwner || recordOwner) {
          return {
            ok: false,
            eligible_for_auto_merge: false,
            requires_maintainer: true,
            checked: 0,
            reports: [],
            reason: `Cannot overwrite historical artifact ${ae.path} belonging to ${(solvedOwner || recordOwner).id}`,
          };
        }
      }
    }
  }

  const reports = [];
  let allOk = true;
  let allFrozenMatched = true;
  let requiresMaintainer = false;
  const uniqueClaims = new Set();
  const referencedArtifacts = new Set();
  const batchClaimKinds = new Set();
  const batchRecordLemmas = new Set();
  let hasRecordSubmission = false;

  for (const se of subEntries) {
    const sf = se.path;
    const sm = sf.match(ALLOWED_SUBMISSION_RE);
    const dirSlug = sm[1];
    const abs = path.resolve(rootDir, sf);

    let sub;
    try {
      sub = JSON.parse(fs.readFileSync(abs, "utf8"));
    } catch {
      allOk = false;
      allFrozenMatched = false;
      reports.push({ submission: sf, ok: false, reason: "Invalid JSON syntax" });
      continue;
    }

    if (sub.mission !== dirSlug) {
      allOk = false;
      allFrozenMatched = false;
      reports.push({
        submission: sf,
        lemma_id: sub.lemma_id,
        ok: false,
        reason: `Mission directory mismatch: path is "${dirSlug}" but submission JSON declares "${sub.mission}"`,
      });
      continue;
    }

    const m = loadMission(dirSlug);
    const baseState = getBaseState(dirSlug);
    const registered = baseState.lemmas.find((l) => l.id === sub.lemma_id);

    if (!registered && sub.kind !== "claim_add") {
      allOk = false;
      allFrozenMatched = false;
      reports.push({ submission: sf, lemma_id: sub.lemma_id, ok: false, reason: `Unknown claim ID "${sub.lemma_id}" in mission "${dirSlug}"` });
      continue;
    }

    uniqueClaims.add(`${dirSlug}/${sub.lemma_id}`);

    // King-of-the-Hill record & record_bound branch (Opus 5.5 + Astra 6.2 strict rules!)
    if (sub.kind === "record" || sub.kind === "record_bound") {
      hasRecordSubmission = true;
      if (registered.kind !== "record") {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Claim "${sub.lemma_id}" is not a King-of-the-Hill record hunt` });
        continue;
      }
      if (!allowMeta && (subEntries.length !== 1 || cls.artifactEntries.length !== 1)) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Record PR must contain exactly 1 submission JSON and 1 newly added artifact file` });
        continue;
      }
      const scoreStr = validateCanonicalNatScore(sub.score);
      if (scoreStr === null || typeof sub.score !== "number" || String(sub.score) !== scoreStr) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Invalid canonical integer score: ${JSON.stringify(sub.score)}` });
        continue;
      }
      const score = Number(scoreStr);
      // Prevent duplicate/conflicting record submissions for the same lemma in one PR (even under --allow-meta!)
      const recBatchKey = `${dirSlug}/${sub.lemma_id}`;
      if (batchRecordLemmas.has(recBatchKey)) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Duplicate or conflicting record submission for ${sub.lemma_id} in the same PR` });
        continue;
      }
      batchRecordLemmas.add(recBatchKey);

      const expected = computeRecordTargets(dirSlug, registered, sub.kind, score);
      if (path.basename(sf) !== expected.submissionBasename) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Record submission filename must be "${expected.submissionBasename}", got "${path.basename(sf)}"` });
        continue;
      }
      if (sub.file !== expected.artifactFile) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Record file must be "${expected.artifactFile}", got "${sub.file}"` });
        continue;
      }
      if (sub.theorem !== expected.theoremName) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Record theorem must be "${expected.theoremName}", got "${sub.theorem}"` });
        continue;
      }
      // Enforce status === "A" on record artifact (NEVER allow overwriting an existing score file!)
      const artEntry = cls.artifactEntries.find((ae) => ae.path === sub.file);
      if (!artEntry || artEntry.status !== "A") {
        allOk = false;
        allFrozenMatched = false;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: `Record artifact ${sub.file} must be newly added (status A), never modified` });
        continue;
      }

      const imp = validateRecordImprovement(registered, sub.kind, score);
      if (!imp.ok) {
        allOk = false;
        allFrozenMatched = false;
        if (imp.requiresMaintainer) requiresMaintainer = true;
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, score, ok: false, reason: imp.reason });
        continue;
      }
      if (imp.requiresMaintainer) requiresMaintainer = true;

      referencedArtifacts.add(sub.file);
      const judgeCoreRel = m.judge?.core_file || m.judge?.harness_file || null;
      const preJudgeCoreHash = judgeCoreRel ? sha256RelFile(judgeCoreRel) : null;
      const verdict = runJudge(m, {
        file: sub.file,
        target: sub.theorem,
        kind: sub.kind,
        statementFile: registered.statement_file,
        statementDef: registered.statement_def,
        expectedScore: score,
      });
      const postJudgeCoreHash = judgeCoreRel ? sha256RelFile(judgeCoreRel) : null;

      const bindErrors = [];
      if (preJudgeCoreHash && postJudgeCoreHash !== preJudgeCoreHash) {
        bindErrors.push(`Judge core/harness file "${judgeCoreRel}" changed during execution (tampering detected)`);
      }
      if (verdict.ok) {
        const rec = sub.checker;
        if (!rec || typeof rec !== "object") {
          bindErrors.push("Missing checker block in record submission JSON");
        } else {
          if (rec.ok !== true) bindErrors.push("checker.ok must be true");
          if (rec.judge && rec.judge !== verdict.judge) bindErrors.push(`checker.judge mismatch`);
          if (verdict.score !== score) bindErrors.push(`verdict.score mismatch: got ${verdict.score}, expected ${score}`);
          if (rec.file_hash !== verdict.file_hash) bindErrors.push(`file_hash mismatch`);
          if (rec.statement_hash !== verdict.statement_hash) bindErrors.push(`statement_hash mismatch`);
          if (rec.core_hash !== verdict.core_hash) bindErrors.push(`core_hash mismatch`);
          if (verdict.signature && ((!allowMeta && !sub.signature) || (sub.signature != null && String(sub.signature).trim() !== String(verdict.signature).trim()))) {
            bindErrors.push(`signature mismatch: JSON does not match verified Judge signature`);
          }
          if (rec.statement_frozen !== true || verdict.statement_frozen !== true) bindErrors.push(`statement_frozen must be true`);
          if (!sameSortedStrings(rec.axioms, verdict.axioms)) bindErrors.push(`axioms mismatch`);
          if (!allowMeta && !DONOR_SEAT_RE.test(String(rec.by_seat || ""))) {
            bindErrors.push(`by_seat "${rec.by_seat}" must use donor-/ext-/contrib- prefix`);
          }
        }
      }

      const itemOk = verdict.ok && bindErrors.length === 0;
      if (!itemOk) allOk = false;
      if (!verdict.statement_frozen) allFrozenMatched = false;
      reports.push({
        submission: sf,
        mission: m.slug,
        lemma_id: sub.lemma_id,
        kind: sub.kind,
        score,
        ok: itemOk,
        statement_frozen: Boolean(verdict.statement_frozen),
        requires_maintainer: imp.requiresMaintainer,
        duration_ms: verdict.duration_ms,
        axioms: verdict.axioms,
        file_hash: verdict.file_hash,
        statement_hash: verdict.statement_hash,
        core_hash: verdict.core_hash,
        signature: verdict.signature || "",
        reason: bindErrors.length ? `Record submission binding failed: ${bindErrors.join("; ")}` : verdict.reason,
      });
      continue;
    }

    // Reject ordinary proof/refutation against a King-of-the-Hill record claim!
    if (registered?.kind === "record" && (sub.kind === "proof" || sub.kind === "refutation")) {
      allOk = false;
      allFrozenMatched = false;
      reports.push({
        submission: sf,
        lemma_id: sub.lemma_id,
        kind: sub.kind,
        ok: false,
        reason: `Claim "${sub.lemma_id}" is a King-of-the-Hill record hunt — submit kind "record" or "record_bound" instead of "${sub.kind}"`,
      });
      continue;
    }

    const batchKey = `${dirSlug}/${sub.lemma_id}/${sub.kind}`;
    if (batchClaimKinds.has(batchKey)) {
      allOk = false;
      allFrozenMatched = false;
      reports.push({ submission: sf, lemma_id: sub.lemma_id, ok: false, reason: `Duplicate ${sub.kind} submission for ${sub.lemma_id} in the same PR` });
      continue;
    }
    batchClaimKinds.add(batchKey);

    if (sub.kind === "proof" || sub.kind === "refutation") {
      if (sub.kind === "proof" && (registered.status === "checked" || registered.status === "contradiction")) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({
          submission: sf,
          lemma_id: sub.lemma_id,
          ok: false,
          reason: `Duplicate proof rejected: ${sub.lemma_id} is already ${registered.status} on base`,
        });
        continue;
      }
      if (sub.kind === "refutation" && (registered.status === "refuted" || registered.status === "contradiction")) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({
          submission: sf,
          lemma_id: sub.lemma_id,
          ok: false,
          reason: `Duplicate refutation rejected: ${sub.lemma_id} is already ${registered.status} on base`,
        });
        continue;
      }
      if (
        (sub.kind === "proof" && registered.status === "refuted") ||
        (sub.kind === "refutation" && registered.status === "checked")
      ) {
        requiresMaintainer = true;
        allFrozenMatched = false;
      }

      if (sub.kind === "proof") {
        if (registered.lean_file && sub.file !== registered.lean_file) {
          allOk = false;
          allFrozenMatched = false;
          reports.push({
            submission: sf,
            lemma_id: sub.lemma_id,
            ok: false,
            reason: `File binding mismatch: expected "${registered.lean_file}", got "${sub.file}"`,
          });
          continue;
        }
        if (registered.theorem_name && sub.theorem !== registered.theorem_name) {
          allOk = false;
          allFrozenMatched = false;
          reports.push({
            submission: sf,
            lemma_id: sub.lemma_id,
            ok: false,
            reason: `Theorem binding mismatch: expected "${registered.theorem_name}", got "${sub.theorem}"`,
          });
          continue;
        }
      } else {
        const hasFrozen = Boolean(registered.statement_file && registered.statement_def);
        const hasRefThm = Boolean(registered.refutation_theorem);
        if (!hasFrozen && !hasRefThm && !allowMeta) {
          allOk = false;
          allFrozenMatched = false;
          reports.push({
            submission: sf,
            lemma_id: sub.lemma_id,
            ok: false,
            reason: `Unbound refutation rejected: ${sub.lemma_id} has no frozen statement or registered refutation_theorem (requires maintainer review)`,
          });
          continue;
        }
        if (hasRefThm && sub.theorem !== registered.refutation_theorem) {
          allOk = false;
          allFrozenMatched = false;
          reports.push({
            submission: sf,
            lemma_id: sub.lemma_id,
            ok: false,
            reason: `Refutation theorem mismatch: expected "${registered.refutation_theorem}", got "${sub.theorem}"`,
          });
          continue;
        }
      }

      referencedArtifacts.add(sub.file);
      const judgeCoreRel = m.judge?.core_file || m.judge?.harness_file || null;
      const preJudgeCoreHash = judgeCoreRel ? sha256RelFile(judgeCoreRel) : null;
      const verdict = runJudge(m, {
        file: sub.file,
        target: sub.theorem,
        kind: sub.kind,
        statementFile: registered.statement_file || null,
        statementDef: registered.statement_def || null,
      });
      const postJudgeCoreHash = judgeCoreRel ? sha256RelFile(judgeCoreRel) : null;

      const bindErrors = [];
      if (preJudgeCoreHash && postJudgeCoreHash !== preJudgeCoreHash) {
        bindErrors.push(`Judge core/harness file "${judgeCoreRel}" changed during execution (tampering detected)`);
      }
      if (verdict.ok) {
        const baseName = path.basename(sf);
        const expectedPrefix = `${sub.lemma_id}.${sub.kind}.${String(verdict.file_hash || "").slice(0, 10)}.json`;
        if (baseName !== expectedPrefix) {
          bindErrors.push(`Submission filename must be "${expectedPrefix}", got "${baseName}"`);
        }

        const rec = sub.kind === "proof" ? sub.checker : sub.refutation;
        if (!rec || typeof rec !== "object") {
          bindErrors.push(`Missing "${sub.kind === "proof" ? "checker" : "refutation"}" block in submission JSON`);
        } else {
          if (sub.kind === "proof" && rec.ok !== true) bindErrors.push(`checker.ok must be true`);
          if (sub.kind === "proof" && rec.judge && rec.judge !== verdict.judge) {
            bindErrors.push(`checker.judge mismatch: JSON="${rec.judge}", judge="${verdict.judge}"`);
          }
          if (rec.file_hash !== verdict.file_hash) {
            bindErrors.push(`file_hash mismatch: JSON="${rec.file_hash}", computed="${verdict.file_hash}"`);
          }
          if (verdict.core_hash && ((!allowMeta && rec.core_hash !== verdict.core_hash) || (rec.core_hash != null && rec.core_hash !== verdict.core_hash))) {
            bindErrors.push(`core_hash mismatch: JSON="${rec.core_hash}", computed="${verdict.core_hash}"`);
          }
          if (verdict.statement_hash) {
            if ((!allowMeta && rec.statement_hash !== verdict.statement_hash) || (rec.statement_hash != null && rec.statement_hash !== verdict.statement_hash)) {
              bindErrors.push(`statement_hash mismatch: JSON="${rec.statement_hash}", computed="${verdict.statement_hash}"`);
            }
          } else if (rec.statement_hash != null) {
            bindErrors.push(`statement_hash mismatch: JSON="${rec.statement_hash}", computed=null`);
          }
          if (sub.kind === "proof" && verdict.signature && ((!allowMeta && !sub.signature) || (sub.signature != null && String(sub.signature).trim() !== String(verdict.signature).trim()))) {
            bindErrors.push(`signature mismatch: JSON does not match verified Judge signature`);
          }
          if (sub.kind === "refutation" && verdict.signature && ((!allowMeta && !rec.signature) || (rec.signature != null && String(rec.signature).trim() !== String(verdict.signature).trim()))) {
            bindErrors.push(`refutation.signature mismatch: JSON does not match verified Judge signature`);
          }
          if (sub.kind === "refutation" && verdict.signature && sub.signature != null && String(sub.signature).trim() !== String(verdict.signature).trim()) {
            bindErrors.push(`signature mismatch: JSON does not match verified Judge signature`);
          }
          if (Boolean(rec.statement_frozen) !== Boolean(verdict.statement_frozen)) {
            bindErrors.push(`statement_frozen mismatch: JSON=${Boolean(rec.statement_frozen)}, judge=${Boolean(verdict.statement_frozen)}`);
          }
          if (!sameSortedStrings(rec.axioms, verdict.axioms)) {
            bindErrors.push(`axioms mismatch: JSON=${JSON.stringify(rec.axioms)}, judge=${JSON.stringify(verdict.axioms)}`);
          }
          if (!allowMeta && !DONOR_SEAT_RE.test(String(rec.by_seat || ""))) {
            bindErrors.push(`by_seat "${rec.by_seat}" must use donor-/ext-/contrib- prefix in donor PRs`);
          }
        }
      }

      const itemOk = verdict.ok && bindErrors.length === 0;
      if (!itemOk) allOk = false;
      if (!verdict.statement_frozen) allFrozenMatched = false;

      reports.push({
        submission: sf,
        mission: m.slug,
        lemma_id: sub.lemma_id,
        kind: sub.kind,
        ok: itemOk,
        statement_frozen: Boolean(verdict.statement_frozen),
        duration_ms: verdict.duration_ms,
        axioms: verdict.axioms,
        file_hash: verdict.file_hash,
        signature: verdict.signature || "",
        reason: bindErrors.length ? `Submission binding failed: ${bindErrors.join("; ")}` : verdict.reason,
      });
    } else {
      allFrozenMatched = false;
      requiresMaintainer = true;
      if (!allowMeta) {
        allOk = false;
        reports.push({
          submission: sf,
          lemma_id: sub.lemma_id,
          kind: sub.kind,
          ok: false,
          reason: `Metadata submission kind "${sub.kind}" requires maintainer review (cannot self-certify via donor PR)`,
        });
      } else {
        if (sub.kind === "audit" && (!sub.audit?.file_hash || !sub.audit?.status)) {
          allOk = false;
          reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: false, reason: "Audit submission must include file_hash and status" });
        } else {
          reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: true, reason: "Metadata validated" });
        }
      }
    }
  }

  if (!allowMeta && !allowInfra) {
    if (uniqueClaims.size > 1 || (hasRecordSubmission && subEntries.length > 1)) {
      allOk = false;
      allFrozenMatched = false;
      reasons.push(`Donor PR must target exactly 1 claim and 1 submission (found ${uniqueClaims.size} claims, ${subEntries.length} submissions)`);
    }
    const unreferenced = cls.artifactEntries.filter((ae) => !referencedArtifacts.has(ae.path));
    if (unreferenced.length > 0) {
      allOk = false;
      allFrozenMatched = false;
      reasons.push(`PR includes unreferenced artifact file(s): ${unreferenced.map((a) => a.path).join(", ")}`);
    }
  }

  if (reports.length !== subEntries.length || reports.length === 0) {
    allOk = false;
    allFrozenMatched = false;
    reasons.push(`Internal completeness check failed: checked ${reports.length} of ${subEntries.length} submissions`);
  }

  const eligibleForAutoMerge =
    allOk &&
    allFrozenMatched &&
    !requiresMaintainer &&
    !allowInfra &&
    !allowMeta &&
    uniqueClaims.size === 1 &&
    reports.length === subEntries.length &&
    reports.length > 0;

  return {
    ok: allOk,
    eligible_for_auto_merge: eligibleForAutoMerge,
    requires_maintainer: requiresMaintainer,
    checked: reports.length,
    reports,
    ...(reasons.length ? { reason: reasons.join("; ") } : {}),
  };
}
