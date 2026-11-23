#!/usr/bin/env node
/**
 * hub/pr_gate.mjs — Single-Source-of-Truth PR Diff Classifier, Safe Stager & Submission Verifier.
 *
 * Implements every P0/P1 invariant from Claude Opus 5.5 + GPT-6.2 Astra audits:
 * - Parses `git diff -z --no-renames --raw` (never trims filenames, catches renames/deletions/symlinks).
 * - Enforces mode `100644`, append-only `submissions/*.json` (`A` only), and no `M` on solved claims.
 * - Derives base mission state in memory excluding the PR's own submissions (no stale `state.json` bugs!).
 * - Strictly binds every submission JSON field (`mission`, filename hash, `file`, `theorem`, `checker`/`refutation`
 *   `file_hash`, `statement_frozen`, sorted `axioms`, `judge`, `by_seat`) to the live mechanical Judge verdict.
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { ROOT, loadMission, deriveMissionState } from "./missions.mjs";
import { runJudge } from "./judges/index.mjs";

export const ALLOWED_SUBMISSION_RE = /^missions\/([a-z0-9-_]+)\/submissions\/([A-Za-z0-9_.-]+)\.json$/;
export const ALLOWED_ARTIFACT_RE =
  /^(missions\/([a-z0-9-_]+)\/(artifacts\/[A-Za-z0-9_.-]+|lean\/[A-Za-z0-9_]+\/Claims\/[A-Za-z0-9_]+\.lean)|lean\/PnP\/Lemmas\/[A-Za-z0-9_]+\.lean)$/;
export const DONOR_SEAT_RE = /^(donor|ext|contrib)-[a-z0-9-_]{1,32}$/;

/**
 * Parse raw NUL-delimited output of `git diff -z --no-renames --raw <base>...<head>`.
 * Format per entry: `:<oldMode> <newMode> <oldSha> <newSha> <status>\0<path>\0`
 */
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

/**
 * Convert plain newline/CSV file lists (local CLI convenience) into synthetic `A`/`100644` entries.
 * NEVER trims trailing spaces (preserves exact path so trailing-space exploits fail allowlist!).
 */
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

    // Check frozen statement immutability: once a claim has an accepted submission in base,
    // Statements/*.lean must not be modified or deleted!
    if (/\/Statements\/[A-Za-z0-9_]+\.lean$/.test(p) && e.status !== "A") {
      if (ms) {
        try {
          const { state } = deriveMissionState(ms);
          const matched = (state.lemmas || []).find(
            (l) => l.statement_file === p && (l.status === "checked" || l.status === "refuted" || l.status === "contradiction")
          );
          if (matched) {
            frozenStatementMutations.push({ path: p, lemma_id: matched.id });
          }
        } catch {}
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

  // Derive needsLean dynamically from touched mission judge configs (never hardcoded!)
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

/**
 * Safely materialize ONLY verified allowlisted `100644` files from `gitRef` (e.g. `pr-head`)
 * onto the trusted base checkout (using Node `git show`, zero shell interpolation!).
 */
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

/**
 * Pure data-only auto-merge eligibility check (used by auto-merge.yml `decide` job —
 * NEVER executes Lean, node `.mjs` artifacts, or PR workflows!).
 */
export function evaluateAutoMergeDataOnly(entries, gitRef = "pr-head", rootDir = ROOT) {
  const cls = classifyEntries(entries);
  if (cls.lane !== "donor") {
    return { eligible: false, reasons: [`Not a pure donor PR (${cls.reasons.join("; ")})`] };
  }
  if (cls.submissionEntries.length !== 1) {
    return { eligible: false, reasons: [`Auto-merge requires exactly 1 submission JSON per PR (got ${cls.submissionEntries.length})`] };
  }

  const sf = cls.submissionEntries[0].path;
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
  if (sub.kind !== "proof" && sub.kind !== "refutation") {
    return { eligible: false, reasons: [`Metadata submission kind "${sub.kind}" is never auto-mergeable`] };
  }

  // Derive base state from trusted `main` (never executes PR code!)
  const { state: baseState } = deriveMissionState(dirSlug);
  const registered = baseState.lemmas.find((l) => l.id === sub.lemma_id);
  if (!registered) {
    return { eligible: false, reasons: [`Unknown claim ID "${sub.lemma_id}" in "${dirSlug}"`] };
  }
  if (!registered.statement_file || !registered.statement_def) {
    return { eligible: false, reasons: [`Claim "${sub.lemma_id}" is not a frozen-statement bounty (requires cross-model audit before merge)`] };
  }
  if (registered.status !== "conjecture" && registered.status !== "in_work") {
    return { eligible: false, reasons: [`Claim "${sub.lemma_id}" is already ${registered.status} on main`] };
  }
  // Ensure every artifact touched in the PR belongs solely to this claim
  const expectedArtifact = sub.file;
  if (!expectedArtifact || !cls.artifactEntries.every((a) => a.path === expectedArtifact)) {
    return { eligible: false, reasons: [`PR modifies unrelated artifact files outside ${expectedArtifact}`] };
  }
  if (sub.kind === "proof" && sub.file !== registered.lean_file) {
    return { eligible: false, reasons: [`Proof file "${sub.file}" does not match registered "${registered.lean_file}"`] };
  }
  const bySeat = sub.kind === "proof" ? sub.checker?.by_seat : sub.refutation?.by_seat;
  if (!DONOR_SEAT_RE.test(String(bySeat || ""))) {
    return { eligible: false, reasons: [`Donor seat "${bySeat}" must match donor-/ext-/contrib- prefix`] };
  }

  return {
    eligible: true,
    mission: dirSlug,
    lemma_id: sub.lemma_id,
    kind: sub.kind,
    reasons: [],
  };
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
      reason: `Immutable frozen statement(s) already have accepted proofs and cannot be modified: ${cls.frozenStatementMutations.map((x) => `${x.path} (${x.lemma_id})`).join(", ")}`,
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

  // Every listed submission & artifact MUST exist on disk (missing file = HARD FAIL; fixes checked=0 bypass!)
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

  // Group submission basenames per mission so deriveMissionState excludes the PR's own files!
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

  // Reject any `M` modification to an artifact belonging to an already-solved claim!
  for (const ae of cls.artifactEntries) {
    if (ae.status === "M") {
      const ms = missionSlugFromPath(ae.path);
      if (ms) {
        const bState = getBaseState(ms);
        const solvedOwner = bState.lemmas.find(
          (l) =>
            (l.lean_file === ae.path || l.refutation?.counterexample_file === ae.path) &&
            (l.status === "checked" || l.status === "refuted" || l.status === "contradiction")
        );
        if (solvedOwner && !allowInfra) {
          return {
            ok: false,
            eligible_for_auto_merge: false,
            requires_maintainer: true,
            checked: 0,
            reports: [],
            reason: `Cannot overwrite artifact ${ae.path} belonging to already-${solvedOwner.status} claim ${solvedOwner.id}`,
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

    // Prevent two submissions for the same claim+kind in one batch
    const batchKey = `${dirSlug}/${sub.lemma_id}/${sub.kind}`;
    if (batchClaimKinds.has(batchKey)) {
      allOk = false;
      allFrozenMatched = false;
      reports.push({ submission: sf, lemma_id: sub.lemma_id, ok: false, reason: `Duplicate ${sub.kind} submission for ${sub.lemma_id} in the same PR` });
      continue;
    }
    batchClaimKinds.add(batchKey);

    if (sub.kind === "proof" || sub.kind === "refutation") {
      // Duplicate & contradiction rules against base derived state
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

      // Bind file & theorem
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
        // Refutations MUST be bound to a frozen statement OR an explicit registered refutation_theorem (unless --allow-meta)
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
      const verdict = runJudge(m, {
        file: sub.file,
        target: sub.theorem,
        kind: sub.kind,
        statementFile: registered.statement_file || null,
        statementDef: registered.statement_def || null,
      });

      const bindErrors = [];
      if (verdict.ok) {
        // Bind filename hash prefix & ID & kind
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

  // Enforce single claim per donor PR & no piggybacked unreferenced artifacts
  if (!allowMeta && !allowInfra) {
    if (uniqueClaims.size > 1) {
      allOk = false;
      allFrozenMatched = false;
      reasons.push(`Donor PR must target exactly 1 claim (found ${uniqueClaims.size}: ${[...uniqueClaims].join(", ")})`);
    }
    const unreferenced = cls.artifactEntries.filter((ae) => !referencedArtifacts.has(ae.path));
    if (unreferenced.length > 0) {
      allOk = false;
      allFrozenMatched = false;
      reasons.push(`PR includes unreferenced artifact file(s): ${unreferenced.map((a) => a.path).join(", ")}`);
    }
  }

  // Hard guard: every submission MUST have produced a report!
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
