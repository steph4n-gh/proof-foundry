#!/usr/bin/env node
/**
 * hub/missions.mjs — Multi-mission registry, trust-seal computation,
 * and PURE deterministic conflict-free submission derivation (v4 — with King of the Hill Records).
 *
 * Hardened per Opus 5.5 + Astra 6.2 audits:
 * - Keeps `_sub_file` distinct from `sub.file` (artifact path) so trusted git commit timestamps work!
 * - Recomputes `record_state` cleanly from scratch from `submissions/*.json` on every derive (never duplicates).
 * - Orders record entries by trusted git commit first-added time, then `_sub_file` (never donor `sub.at`).
 * - Delta-based anti-farming points (`prev_best - score`, `score - prev_refuted`), sticky contradictions,
 *   closure at `refuted + 1 == best` or `best == 0`, and `stale_statement` hash tracking.
 */
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";

export const ROOT = path.resolve(import.meta.dirname, "..");
export const MISSIONS_DIR = path.join(ROOT, "missions");
export const DEFAULT_MISSION = "erdos-combinatorics";

export function listMissionSlugs() {
  if (!fs.existsSync(MISSIONS_DIR)) return [];
  return fs
    .readdirSync(MISSIONS_DIR, { withFileTypes: true })
    .filter((d) => d.isDirectory() && fs.existsSync(path.join(MISSIONS_DIR, d.name, "mission.json")))
    .map((d) => d.name)
    .sort();
}

export function getMissionPaths(slug = DEFAULT_MISSION) {
  if (!/^[a-z0-9][a-z0-9-_]{0,63}$/.test(slug)) {
    throw new Error(`Invalid mission slug: ${slug}`);
  }
  const dir = path.join(MISSIONS_DIR, slug);
  return {
    slug,
    dir,
    missionFile: path.join(dir, "mission.json"),
    stateFile: path.join(dir, "state.json"),
    eventsFile: path.join(dir, "events.ndjson"),
    submissionsDir: path.join(dir, "submissions"),
    lockDir: path.join(dir, ".state.lock"),
  };
}

export function loadMission(slug = DEFAULT_MISSION) {
  const paths = getMissionPaths(slug);
  if (!fs.existsSync(paths.missionFile)) {
    throw new Error(`Mission "${slug}" not found at ${paths.missionFile}`);
  }
  const config = JSON.parse(fs.readFileSync(paths.missionFile, "utf8"));
  return { ...config, slug, paths };
}

export function sha256RelFile(relPath) {
  if (!relPath) return null;
  const abs = path.isAbsolute(relPath) ? relPath : path.resolve(ROOT, relPath);
  if (!fs.existsSync(abs)) return null;
  return crypto.createHash("sha256").update(fs.readFileSync(abs)).digest("hex");
}

/**
 * Single source of truth for canonical hashless King-of-the-Hill paths & theorem names!
 * Hashless filenames give a FREE git add/add concurrency lock on duplicate scores.
 */
export function computeRecordTargets(missionSlug, lemma, kind, score) {
  const rec = lemma?.record || {};
  const tag = kind === "record_bound" ? `not_s${score}` : `s${score}`;
  const stem = rec.file_stem || lemma.id.replace(/-/g, "_");
  const claimsDir = rec.claims_dir || `missions/${missionSlug}/lean/Claims`;
  const ext = rec.artifact_ext || ".lean";
  const artifactFile = `${claimsDir}/${stem}_${tag}${ext}`;
  const submissionBasename = `${lemma.id}.${kind}.s${score}.json`;
  const submissionFile = `missions/${missionSlug}/submissions/${submissionBasename}`;
  const tpl = rec.theorem_template || `${stem}_{tag}.record`;
  const theoremName = tpl.replace(/\{tag\}/g, tag);
  return { tag, artifactFile, submissionBasename, submissionFile, theoremName };
}

/**
 * Compute explicit trust seal for a claim (keeps receipt trust, hunt availability, and objectives clean!):
 *   contradiction | flagged | frozen | record | audited | provisional | refuted | dead | in_work | open
 */
export function computeTrustSeal(lemma) {
  if (lemma.status === "contradiction" || lemma.record_state?.contradiction) return "contradiction";
  if (lemma.kind === "record") {
    const rs = lemma.record_state;
    if (rs?.closed) return "frozen";
    if (rs?.best) return "record";
    return "open";
  }

  const currentHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
  const auditHashMismatch =
    Boolean(lemma.audit?.file_hash) && Boolean(currentHash) && lemma.audit.file_hash !== currentHash;

  if (lemma.audit?.status === "flagged" && !auditHashMismatch) return "flagged";
  if (lemma.status === "checked") {
    if (lemma.checker?.statement_frozen) return "frozen";
    if (lemma.audit?.status === "faithful" && !auditHashMismatch) return "audited";
    return "provisional";
  }
  if (lemma.status === "refuted") return "refuted";
  if (lemma.status === "dead") return "dead";
  if (lemma.status === "in_work") return "in_work";
  return "open";
}

export function normalizeObjectiveReqs(obj) {
  if (Array.isArray(obj.required)) {
    return obj.required.map((r) =>
      typeof r === "string" ? { id: r, expect: "proof" } : { id: r.id, expect: r.expect || "proof" }
    );
  }
  return (obj.required_claims || []).map((id) => ({
    id,
    expect: obj.accept_refutation ? "either" : "proof",
  }));
}

export function isRungConquered(lemma, expect = "proof") {
  if (!lemma) return false;
  const seal = computeTrustSeal(lemma);
  if (seal === "flagged" || seal === "contradiction") return false;
  if (lemma.kind === "record") {
    const rs = lemma.record_state;
    if (!rs || rs.contradiction) return false;
    if (expect === "record_any") return Boolean(rs.best);
    if (expect && typeof expect === "object" && Number.isSafeInteger(expect.record_at_most)) {
      return rs.direction === "min" && Boolean(rs.best) && rs.best.score <= expect.record_at_most;
    }
    if (expect && typeof expect === "object" && Number.isSafeInteger(expect.record_at_least)) {
      return rs.direction === "max" && Boolean(rs.best) && rs.best.score >= expect.record_at_least;
    }
    // Default ("proof" / "record_closed"): conquered only when exact optimal is closed!
    return Boolean(rs.closed);
  }
  if (expect === "refutation") return lemma.status === "refuted";
  if (expect === "either") return seal === "audited" || seal === "frozen" || lemma.status === "refuted";
  return seal === "audited" || seal === "frozen";
}

export function loadAllMissionsSummary() {
  return listMissionSlugs().map((slug) => {
    const m = loadMission(slug);
    let counts = {
      lemmas: 0,
      checked: 0,
      trusted: 0,
      flagged: 0,
      records_active: 0,
      records_closed: 0,
      in_work: 0,
      conjecture: 0,
      refuted: 0,
      dead: 0,
      contradiction: 0,
    };
    let objSummary = { total: (m.objectives || []).length, conquered: 0 };
    try {
      const { state: st } = deriveMissionState(slug);
      counts.lemmas = st.lemmas?.length || 0;
      for (const l of st.lemmas || []) {
        if (l.kind === "record") {
          if (l.record_state?.contradiction) counts.contradiction++;
          else if (l.record_state?.closed) {
            counts.records_closed++;
            counts.checked++;
            counts.trusted++;
          } else {
            counts.records_active++;
            counts.conjecture++;
          }
          continue;
        }
        counts[l.status] = (counts[l.status] || 0) + 1;
        const seal = computeTrustSeal(l);
        if (seal === "audited" || seal === "frozen") counts.trusted++;
        if (seal === "flagged") counts.flagged++;
      }
      for (const obj of m.objectives || []) {
        const reqs = normalizeObjectiveReqs(obj);
        const done = reqs.every((r) => isRungConquered(st.lemmas.find((x) => x.id === r.id), r.expect));
        if (reqs.length > 0 && done) objSummary.conquered++;
      }
    } catch {}
    return {
      slug,
      brand: m.brand || m.title,
      title: m.title,
      tagline: m.tagline || "",
      question: m.question,
      judge_type: m.judge?.type || "lean4",
      judge_label: m.judge?.label || m.judge?.type || "Judge",
      counts,
      objectives: objSummary,
    };
  });
}

export function allowedArtifactDirsForMission(mission) {
  const dirs = mission.judge?.allowed_dirs || [];
  return dirs.map((d) => (path.isAbsolute(d) ? d : path.resolve(ROOT, d)));
}

export function readMissionStatementFile(mission, relPath) {
  if (!relPath || typeof relPath !== "string") return null;
  const candidate = path.resolve(ROOT, relPath);
  if (!candidate.endsWith(".lean") && !candidate.endsWith(".json")) return null;
  const allowedDirs = [
    ...allowedArtifactDirsForMission(mission),
    path.join(mission.paths.dir, "specs"),
  ];
  try {
    if (fs.lstatSync(candidate).isSymbolicLink()) return null;
    const real = fs.realpathSync(candidate);
    const ok = allowedDirs.some((dir) => {
      try {
        const realDir = fs.realpathSync(dir);
        return real.startsWith(realDir + path.sep);
      } catch {
        return false;
      }
    });
    if (!ok) return null;
    return fs.readFileSync(real, "utf8");
  } catch {
    return null;
  }
}

export function readAllowedArtifactFile(mission, relPath) {
  if (!relPath || typeof relPath !== "string") return null;
  const candidate = path.resolve(ROOT, relPath);
  const exts = mission.judge?.allowed_extensions || [".lean", ".mjs", ".js", ".py", ".rs", ".tla", ".txt", ".md"];
  if (!exts.some((ext) => candidate.endsWith(ext))) return null;
  const allowedDirs = allowedArtifactDirsForMission(mission);
  try {
    if (fs.lstatSync(candidate).isSymbolicLink()) return null;
    const real = fs.realpathSync(candidate);
    const ok = allowedDirs.some((dir) => {
      try {
        const realDir = fs.realpathSync(dir);
        return real.startsWith(realDir + path.sep);
      } catch {
        return false;
      }
    });
    if (!ok) return null;
    return fs.readFileSync(real, "utf8");
  } catch {
    return null;
  }
}

/**
 * Trusted git first-added timestamp map for submission basenames in a directory.
 */
function gitFirstAddedMap(relDir) {
  const map = new Map();
  try {
    const res = spawnSync(
      "git",
      ["log", "--diff-filter=A", "--name-only", "--pretty=format:__COMMIT__%ct", "--", relDir],
      { cwd: ROOT, encoding: "utf8", timeout: 5000 }
    );
    if (res.status !== 0 || !res.stdout) return map;
    let curTs = 0;
    for (const line of res.stdout.split(/\r?\n/)) {
      if (line.startsWith("__COMMIT__")) {
        curTs = Number(line.slice(10)) || 0;
      } else if (line.trim()) {
        const base = path.basename(line.trim());
        const prev = map.get(base);
        if (prev === undefined || curTs < prev) map.set(base, curTs);
      }
    }
  } catch {}
  return map;
}

function ensureDerivedSeat(state, seatId, program, roleHint, whisper, at) {
  if (!seatId || state.seats.some((s) => s.id === seatId)) return;
  state.seats.push({
    id: seatId,
    name: seatId,
    role: roleHint,
    program,
    provider: "Community",
    model: "Token Donor",
    badge: roleHint === "record_holder" ? "♛" : "TD",
    color: roleHint === "refuter" ? "#DC2626" : "#0D9488",
    status: "idle",
    current_lemma: null,
    current_whisper: whisper,
    sessions: 1,
    last_seen: at || state.meta?.updated_at || "",
    counts: { checked: 0, refuted: 0, blocked: 0, record_points: 0, attempts: 1, messages: 0 },
  });
}

/**
 * Pure scratch recomputation of a King-of-the-Hill claim's `record_state`.
 * Ignores any pre-existing derived `record_state` in seed so replays NEVER duplicate history!
 */
function deriveRecordStateForLemma(missionSlug, lemma, subs, { gitAddedTs = new Map(), currentHashes = {} } = {}) {
  const cfg = lemma.record || {};
  const dir = cfg.direction === "max" ? "max" : "min";
  const startTarget = Number(cfg.start_target ?? 0);
  const boundFloor = Number(cfg.bound_floor ?? 0);
  const scoreMax = Number(cfg.score_max ?? 100000);

  // Order strictly by trusted git first-added timestamp; when git timestamps match/are missing,
  // sort deterministically in improving score order so shallow/local replays stay consistent (NEVER donor `sub.at`!)
  const ordered = [...subs].sort((a, b) => {
    const ka = a._sub_file || "";
    const kb = b._sub_file || "";
    const ga = gitAddedTs.has(ka) ? gitAddedTs.get(ka) : Number.MAX_SAFE_INTEGER;
    const gb = gitAddedTs.has(kb) ? gitAddedTs.get(kb) : Number.MAX_SAFE_INTEGER;
    if (ga !== gb) return ga - gb;
    if (a.kind !== b.kind) return a.kind === "record" ? -1 : 1;
    const sa = Number(a.score);
    const sb = Number(b.score);
    if (Number.isFinite(sa) && Number.isFinite(sb) && sa !== sb) {
      if (a.kind === "record") return dir === "min" ? sb - sa : sa - sb;
      return dir === "min" ? sa - sb : sb - sa;
    }
    return ka.localeCompare(kb);
  });

  let best = null;
  let refuted = null;
  let bestVerifiedRecordScore = null;
  let bestVerifiedBoundScore = null;
  let contradiction = false;
  const history = [];
  const pointsBySeat = {};
  const seenFiles = new Set();

  const curStmtHash = currentHashes.statementHashes?.[lemma.statement_file] || null;
  const curCoreHash = currentHashes.coreHash || null;

  for (const sub of ordered) {
    const subBase = sub._sub_file || "";
    if (subBase && seenFiles.has(subBase)) continue;
    if (subBase) seenFiles.add(subBase);

    const score = Number(sub.score);
    if (!Number.isSafeInteger(score) || score < 0 || score > scoreMax || String(score) !== String(sub.score)) continue;
    if (!sub.checker?.ok) continue;

    const expected = computeRecordTargets(missionSlug, lemma, sub.kind, score);
    if (subBase && subBase !== expected.submissionBasename) continue;
    if (sub.file !== expected.artifactFile) continue;
    if (sub.theorem !== expected.theoremName) continue;

    const seat = sub.checker.by_seat || "unknown";
    const gitTs = gitAddedTs.has(subBase) ? gitAddedTs.get(subBase) : null;
    // Require BOTH current statement/core files AND exact statement_hash match (missing hash => stale!).
    // Additive Core.lean edits for later waves do NOT invalidate historical records whose statement_hash still matches.
    const stmtValid =
      Boolean(curStmtHash) &&
      Boolean(sub.checker.statement_hash) &&
      sub.checker.statement_hash === curStmtHash &&
      Boolean(curCoreHash) &&
      Boolean(sub.checker.core_hash);

    if (!stmtValid) {
      history.push({
        kind: sub.kind,
        score,
        seat,
        file: sub.file,
        file_hash: sub.checker.file_hash || null,
        submission: subBase,
        points: 0,
        git_ts: gitTs,
        at: sub.at || null,
        state: "stale_statement",
      });
      continue;
    }

    if (sub.kind === "record") {
      if (bestVerifiedRecordScore === null || (dir === "min" ? score < bestVerifiedRecordScore : score > bestVerifiedRecordScore)) {
        bestVerifiedRecordScore = score;
      }
      const improves =
        dir === "min"
          ? best
            ? score < best.score
            : score <= startTarget
          : best
          ? score > best.score
          : score >= startTarget;

      // Sticky contradiction check against ALL verified bounds (even outside bound_floor/start_target)!
      const conflictsBound =
        (refuted && (dir === "min" ? score <= refuted.score : score >= refuted.score)) ||
        (bestVerifiedBoundScore !== null && (dir === "min" ? score <= bestVerifiedBoundScore : score >= bestVerifiedBoundScore));
      if (conflictsBound) contradiction = true;

      if (improves) {
        const pts =
          dir === "min"
            ? best
              ? best.score - score
              : startTarget + 1 - score
            : best
            ? score - best.score
            : score - startTarget + 1;
        const safePts = Math.max(0, pts);
        best = {
          score,
          seat,
          file: sub.file,
          theorem: sub.theorem,
          file_hash: sub.checker.file_hash || null,
          statement_hash: sub.checker.statement_hash || null,
          core_hash: sub.checker.core_hash || null,
          axioms: sub.checker.axioms || [],
          duration_ms: sub.checker.duration_ms || null,
          submission: subBase,
          git_ts: gitTs,
          at: sub.at || null,
        };
        if (!contradiction) {
          pointsBySeat[seat] = (pointsBySeat[seat] || 0) + safePts;
        }
        history.push({
          kind: "record",
          score,
          seat,
          file: sub.file,
          file_hash: sub.checker.file_hash || null,
          submission: subBase,
          points: contradiction ? 0 : safePts,
          git_ts: gitTs,
          at: sub.at || null,
          state: contradiction ? "contradiction" : "accepted",
        });
      } else {
        history.push({
          kind: "record",
          score,
          seat,
          file: sub.file,
          file_hash: sub.checker.file_hash || null,
          submission: subBase,
          points: 0,
          git_ts: gitTs,
          at: sub.at || null,
          state: conflictsBound ? "contradiction" : "ignored_non_improving",
        });
      }
    } else if (sub.kind === "record_bound") {
      if (bestVerifiedBoundScore === null || (dir === "min" ? score > bestVerifiedBoundScore : score < bestVerifiedBoundScore)) {
        bestVerifiedBoundScore = score;
      }
      // For min: ¬ Record b certifies inclusive lower bound (b + 1). Larger b is stronger!
      const improves =
        dir === "min"
          ? refuted
            ? score > refuted.score
            : score >= boundFloor
          : refuted
          ? score < refuted.score
          : score <= boundFloor;

      const conflictsBest =
        (best && (dir === "min" ? score >= best.score : score <= best.score)) ||
        (bestVerifiedRecordScore !== null && (dir === "min" ? score >= bestVerifiedRecordScore : score <= bestVerifiedRecordScore));
      if (conflictsBest) contradiction = true;

      if (improves) {
        const pts =
          dir === "min"
            ? refuted
              ? score - refuted.score
              : score - boundFloor + 1
            : refuted
            ? refuted.score - score
            : boundFloor - score + 1;
        const safePts = Math.max(0, pts);
        refuted = {
          score,
          inclusive_bound: dir === "min" ? score + 1 : Math.max(0, score - 1),
          seat,
          file: sub.file,
          theorem: sub.theorem,
          file_hash: sub.checker.file_hash || null,
          statement_hash: sub.checker.statement_hash || null,
          core_hash: sub.checker.core_hash || null,
          axioms: sub.checker.axioms || [],
          duration_ms: sub.checker.duration_ms || null,
          submission: subBase,
          git_ts: gitTs,
          at: sub.at || null,
        };
        if (!contradiction) {
          pointsBySeat[seat] = (pointsBySeat[seat] || 0) + safePts;
        }
        history.push({
          kind: "record_bound",
          score,
          seat,
          file: sub.file,
          file_hash: sub.checker.file_hash || null,
          submission: subBase,
          points: contradiction ? 0 : safePts,
          git_ts: gitTs,
          at: sub.at || null,
          state: contradiction ? "contradiction" : "accepted",
        });
      } else {
        history.push({
          kind: "record_bound",
          score,
          seat,
          file: sub.file,
          file_hash: sub.checker.file_hash || null,
          submission: subBase,
          points: 0,
          git_ts: gitTs,
          at: sub.at || null,
          state: conflictsBest ? "contradiction" : "ignored_non_improving",
        });
      }
    }
  }

  const closed =
    !contradiction &&
    Boolean(best) &&
    (dir === "min"
      ? best.score === 0 || (Boolean(refuted) && refuted.score + 1 === best.score)
      : Boolean(refuted) && refuted.score === best.score + 1);

  const nextTarget =
    closed || contradiction
      ? null
      : best
      ? dir === "min"
        ? best.score - 1
        : best.score + 1
      : startTarget;

  return {
    direction: dir,
    best,
    refuted,
    next_target: nextTarget,
    closed,
    contradiction,
    history,
    points_by_seat: contradiction ? {} : pointsBySeat,
  };
}

/**
 * Pure deterministic derivation: (seedState, submissions[]) -> { applied, state }.
 */
export function applySubmissionsPure(seedState, rawSubs, { gitAddedTs = new Map(), missionSlug = null, currentHashes = {} } = {}) {
  const state = structuredClone(seedState);
  const slug = missionSlug || state.meta?.mission || DEFAULT_MISSION;
  const subs = rawSubs.filter((s) => s && s.lemma_id && s.kind);

  const nonRecordSubs = subs.filter((s) => s.kind !== "record" && s.kind !== "record_bound");
  const recordSubsByLemma = new Map();
  for (const s of subs) {
    if (s.kind === "record" || s.kind === "record_bound") {
      if (!recordSubsByLemma.has(s.lemma_id)) recordSubsByLemma.set(s.lemma_id, []);
      recordSubsByLemma.get(s.lemma_id).push(s);
    }
  }

  const kindOrder = { claim_add: 0, proof: 1, refutation: 1, rule_dead: 2, audit: 3 };
  nonRecordSubs.sort((a, b) => {
    const ko = (kindOrder[a.kind] ?? 9) - (kindOrder[b.kind] ?? 9);
    if (ko !== 0) return ko;
    const ka = a._sub_file || a.file || "";
    const kb = b._sub_file || b.file || "";
    const ga = gitAddedTs.has(ka) ? gitAddedTs.get(ka) : Number.MAX_SAFE_INTEGER;
    const gb = gitAddedTs.has(kb) ? gitAddedTs.get(kb) : Number.MAX_SAFE_INTEGER;
    if (ga !== gb) return ga - gb;
    const t = String(a.at || "").localeCompare(String(b.at || ""));
    if (t !== 0) return t;
    return ka.localeCompare(kb);
  });

  const seenProof = new Set();
  const seenRefute = new Set();
  let applied = 0;

  for (const l of state.lemmas || []) {
    if (l.kind === "record") {
      // ALWAYS discard any stale derived record_state from seed!
      delete l.record_state;
      continue;
    }
    if (l.checker?.ok) seenProof.add(l.id);
    if (l.refutation) seenRefute.add(l.id);
    if (l.checker?.ok && l.refutation) l.status = "contradiction";
  }

  for (const sub of nonRecordSubs) {
    let lemma = state.lemmas.find((l) => l.id === sub.lemma_id);
    if (!lemma && sub.kind === "claim_add" && sub.claim) {
      const c = sub.claim;
      state.lemmas.push({
        id: String(sub.lemma_id),
        program: String(c.program || state.programs?.[0]?.id || "general"),
        title: String(c.title || sub.lemma_id),
        statement: String(c.statement || ""),
        registered_statement: String(c.registered_statement || c.statement || ""),
        verified_signature: null,
        statement_file: c.statement_file || null,
        statement_def: c.statement_def || null,
        refutation_theorem: c.refutation_theorem || null,
        theorem_name: String(c.theorem_name || ""),
        lean_file: String(c.lean_file || ""),
        status: "conjecture",
        aims_at: String(c.aims_at || "neutral"),
        deps: Array.isArray(c.deps) ? c.deps.map(String) : [],
        rung: c.rung != null ? Number(c.rung) : null,
        proposed_by: String(c.proposed_by || "community"),
        claimed_by: null,
        paper_notes: String(c.paper_notes || ""),
        created_at: String(sub.at || ""),
        updated_at: String(sub.at || ""),
        checker: null,
        refutation: null,
        epitaph: null,
        audit: null,
      });
      applied++;
      continue;
    }
    if (!lemma || lemma.kind === "record") continue;

    if (sub.kind === "proof" && sub.checker?.ok) {
      if (!seenProof.has(lemma.id)) {
        seenProof.add(lemma.id);
        lemma.lean_file = sub.file || lemma.lean_file;
        lemma.theorem_name = sub.theorem || lemma.theorem_name;
        if (!lemma.registered_statement) lemma.registered_statement = lemma.statement || "";
        if (sub.signature) {
          lemma.verified_signature = sub.signature;
          lemma.statement = sub.signature;
        }
        lemma.checker = sub.checker;
        lemma.updated_at = sub.at || lemma.updated_at;
        if (seenRefute.has(lemma.id) || lemma.status === "refuted" || lemma.status === "contradiction") {
          lemma.status = "contradiction";
        } else {
          lemma.status = "checked";
        }
        ensureDerivedSeat(state, sub.checker.by_seat, lemma.program, "donor", `Verified ${lemma.id}`, sub.at);
        applied++;
      } else if (lemma.status === "refuted") {
        lemma.status = "contradiction";
      }
    } else if (sub.kind === "refutation" && sub.refutation) {
      if (!seenRefute.has(lemma.id)) {
        seenRefute.add(lemma.id);
        lemma.refutation = sub.refutation;
        lemma.updated_at = sub.at || lemma.updated_at;
        if (seenProof.has(lemma.id) || lemma.status === "checked" || lemma.status === "contradiction") {
          lemma.status = "contradiction";
        } else {
          lemma.status = "refuted";
        }
        ensureDerivedSeat(state, sub.refutation.by_seat, lemma.program, "refuter", `Refuted ${lemma.id}`, sub.at);
        applied++;
      } else if (lemma.status === "checked") {
        lemma.status = "contradiction";
      }
    } else if (sub.kind === "rule_dead" && sub.epitaph) {
      if (lemma.status !== "checked" && lemma.status !== "refuted" && lemma.status !== "contradiction") {
        lemma.status = "dead";
        lemma.epitaph = sub.epitaph;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      }
    } else if (sub.kind === "audit" && sub.audit) {
      const currentHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
      if (sub.audit.file_hash && currentHash && sub.audit.file_hash === currentHash) {
        lemma.audit = sub.audit;
        applied++;
      }
    }
  }

  // Recompute every King-of-the-Hill record hunt cleanly from scratch!
  for (const lemma of state.lemmas || []) {
    if (lemma.kind !== "record") continue;
    const rSubs = recordSubsByLemma.get(lemma.id) || [];
    const rs = deriveRecordStateForLemma(slug, lemma, rSubs, { gitAddedTs, currentHashes });
    lemma.record_state = rs;
    if (rs.contradiction) lemma.status = "contradiction";
    else if (rs.closed) lemma.status = "checked";
    else lemma.status = "conjecture";

    if (rs.best) {
      lemma.lean_file = rs.best.file;
      lemma.theorem_name = rs.best.theorem;
      ensureDerivedSeat(state, rs.best.seat, lemma.program, "record_holder", `Record ${rs.best.score} on ${lemma.id}`, rs.best.at);
    }
    if (rs.refuted) {
      ensureDerivedSeat(state, rs.refuted.seat, lemma.program, "donor", `Lower bound ${rs.refuted.inclusive_bound} on ${lemma.id}`, rs.refuted.at);
    }
    for (const h of rs.history) {
      if (h.state === "accepted") {
        ensureDerivedSeat(state, h.seat, lemma.program, "donor", `${h.kind} s=${h.score} on ${lemma.id}`, h.at);
        applied++;
      }
    }
  }

  // Recompute per-seat counts (record_points kept distinct from checked proofs — zero double-counting!)
  const recordPointsBySeat = {};
  for (const l of state.lemmas || []) {
    if (l.kind === "record" && l.record_state && !l.record_state.contradiction && l.record_state.points_by_seat) {
      for (const [seatId, pts] of Object.entries(l.record_state.points_by_seat)) {
        recordPointsBySeat[seatId] = (recordPointsBySeat[seatId] || 0) + pts;
      }
    }
  }

  for (const s of state.seats || []) {
    s.counts = {
      ...(s.counts || {}),
      checked: state.lemmas.filter((l) => l.kind !== "record" && l.status === "checked" && l.checker?.by_seat === s.id).length,
      refuted: state.lemmas.filter((l) => l.kind !== "record" && l.status === "refuted" && l.refutation?.by_seat === s.id).length,
      blocked: state.lemmas.filter((l) => l.kind !== "record" && l.status === "dead" && l.epitaph?.by_seat === s.id).length,
      record_points: recordPointsBySeat[s.id] || 0,
    };
  }

  return { applied, state };
}

/**
 * Pure in-memory mission state derivation from disk seed + submissions/*.json.
 */
export function deriveMissionState(slug = DEFAULT_MISSION, { excludeSubmissionFiles = [] } = {}) {
  const mission = loadMission(slug);
  const { stateFile, submissionsDir } = mission.paths;
  if (!fs.existsSync(stateFile)) {
    throw new Error(`No base state.json for mission "${slug}"`);
  }
  const seed = JSON.parse(fs.readFileSync(stateFile, "utf8"));

  const statementHashes = {};
  for (const l of seed.lemmas || []) {
    if (l.statement_file) statementHashes[l.statement_file] = sha256RelFile(l.statement_file);
  }
  const currentHashes = {
    coreHash: sha256RelFile(mission.judge?.core_file || mission.judge?.harness_file),
    statementHashes,
  };

  if (!fs.existsSync(submissionsDir)) {
    return applySubmissionsPure(seed, [], { missionSlug: slug, currentHashes });
  }

  const excludeSet = new Set(excludeSubmissionFiles.map((f) => path.basename(f)));
  const rawSubs = fs
    .readdirSync(submissionsDir)
    .filter((f) => f.endsWith(".json") && !excludeSet.has(f))
    .map((f) => {
      try {
        const parsed = JSON.parse(fs.readFileSync(path.join(submissionsDir, f), "utf8"));
        // Keep `_sub_file` strictly distinct from `parsed.file` (the artifact path)!
        return { ...parsed, _sub_file: f };
      } catch {
        return null;
      }
    })
    .filter(Boolean);

  const relDir = path.relative(ROOT, submissionsDir);
  const gitAddedTs = gitFirstAddedMap(relDir);
  return applySubmissionsPure(seed, rawSubs, { gitAddedTs, missionSlug: slug, currentHashes });
}

/**
 * Explicit disk write (only invoked by `fleet compile`). Strips derived `record_state` before writing
 * so `state.json` never feeds derived record history back into itself on replay!
 */
export function compileSubmissionsIntoState(slug = DEFAULT_MISSION) {
  const mission = loadMission(slug);
  const { stateFile } = mission.paths;
  const prevRaw = fs.existsSync(stateFile) ? fs.readFileSync(stateFile, "utf8") : "";
  const prevSeed = prevRaw ? JSON.parse(prevRaw) : null;
  const prevLemmaById = new Map((prevSeed?.lemmas || []).map((l) => [l.id, l]));
  const { applied, state } = deriveMissionState(slug);
  const toPersist = structuredClone(state);
  // Keep record seed entries 100% pure: never persist derived record_state, status, lean_file, or theorem_name!
  toPersist.lemmas = (toPersist.lemmas || []).map((l) => {
    if (l.kind !== "record") return l;
    const orig = prevLemmaById.get(l.id);
    if (orig) return structuredClone(orig);
    const clean = { ...l };
    delete clean.record_state;
    return clean;
  });
  const nextRaw = JSON.stringify(toPersist, null, 2) + "\n";
  if (nextRaw !== prevRaw) {
    const tmp = `${stateFile}.tmp.${process.pid}.${Date.now()}`;
    const fd = fs.openSync(tmp, "w");
    try {
      fs.writeSync(fd, nextRaw, undefined, "utf8");
      fs.fsyncSync(fd);
    } finally {
      fs.closeSync(fd);
    }
    fs.renameSync(tmp, stateFile);
  }
  return { applied, state, changed: nextRaw !== prevRaw };
}
