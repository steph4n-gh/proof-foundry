#!/usr/bin/env node
/**
 * hub/missions.mjs — Multi-mission registry, trust-seal computation,
 * and PURE deterministic conflict-free submission derivation (v3).
 *
 * Hardened per Opus 5.5 + Astra 6.2 reviews:
 * - `deriveMissionState(slug, opts)` is PURE (never mutates `state.json`, deterministic output!).
 * - `claim_add` submissions are sanitized (forced to conjecture, all result fields cleared).
 * - Contradictions are sticky & preserve BOTH receipts (replaying opposing proof+refutation in any order).
 * - `rule_dead` never overwrites `checked`, `refuted`, or `contradiction`.
 * - Audit submissions require a non-empty `file_hash` matching the current artifact hash;
 *   `computeTrustSeal` also invalidates stale audits if `audit.file_hash !== currentHash`.
 * - Proof/refutation tie-breaking uses trusted git commit first-added time on main when available.
 */
import fs from "node:fs";
import path from "node:path";
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

/**
 * Compute explicit 3-tier trust seal for a claim:
 *   contradiction | flagged | frozen | audited | provisional | refuted | dead | in_work | open
 */
export function computeTrustSeal(lemma) {
  if (lemma.status === "contradiction") return "contradiction";
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
  if (expect === "refutation") return lemma.status === "refuted";
  if (expect === "either") return seal === "audited" || seal === "frozen" || lemma.status === "refuted";
  return seal === "audited" || seal === "frozen";
}

export function loadAllMissionsSummary() {
  return listMissionSlugs().map((slug) => {
    const m = loadMission(slug);
    let counts = { lemmas: 0, checked: 0, trusted: 0, flagged: 0, in_work: 0, conjecture: 0, refuted: 0, dead: 0, contradiction: 0 };
    let objSummary = { total: (m.objectives || []).length, conquered: 0 };
    try {
      const { state: st } = deriveMissionState(slug);
      counts.lemmas = st.lemmas?.length || 0;
      for (const l of st.lemmas || []) {
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
 * Trusted git first-added timestamp map for submissions in a directory (prevents backdated `sub.at` credit theft).
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
        // Keep earliest commit timestamp for this filename
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
    badge: "TD",
    color: roleHint === "refuter" ? "#DC2626" : "#0D9488",
    status: "idle",
    current_lemma: null,
    current_whisper: whisper,
    sessions: 1,
    last_seen: at || state.meta?.updated_at || "",
    counts: { checked: 0, refuted: 0, blocked: 0, attempts: 1, messages: 0 },
  });
}

/**
 * Pure deterministic derivation: (seedState, submissions[]) -> { applied, state }.
 * Can be called directly in tests without touching disk!
 */
export function applySubmissionsPure(seedState, rawSubs, { gitAddedTs = new Map() } = {}) {
  const state = structuredClone(seedState);
  const subs = rawSubs.filter((s) => s && s.lemma_id && s.kind);

  const kindOrder = { claim_add: 0, proof: 1, refutation: 1, rule_dead: 2, audit: 3 };
  subs.sort((a, b) => {
    const ko = (kindOrder[a.kind] ?? 9) - (kindOrder[b.kind] ?? 9);
    if (ko !== 0) return ko;
    // Order proofs/refutations by trusted git commit first-added time when available (anti-backdate)
    const ga = gitAddedTs.has(a.file) ? gitAddedTs.get(a.file) : Number.MAX_SAFE_INTEGER;
    const gb = gitAddedTs.has(b.file) ? gitAddedTs.get(b.file) : Number.MAX_SAFE_INTEGER;
    if (ga !== gb) return ga - gb;
    const t = String(a.at || "").localeCompare(String(b.at || ""));
    if (t !== 0) return t;
    return String(a.file || "").localeCompare(String(b.file || ""));
  });

  const seenProof = new Set();
  const seenRefute = new Set();
  let applied = 0;

  // Pre-seed seen sets from genesis state so contradictions are sticky across replays
  for (const l of state.lemmas || []) {
    if (l.checker?.ok) seenProof.add(l.id);
    if (l.refutation) seenRefute.add(l.id);
    if (l.checker?.ok && l.refutation) l.status = "contradiction";
  }

  for (const sub of subs) {
    let lemma = state.lemmas.find((l) => l.id === sub.lemma_id);
    if (!lemma && sub.kind === "claim_add" && sub.claim) {
      // Sanitize claim_add: NEVER allow forged status/checker/audit!
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
    if (!lemma) continue;

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
        // Sticky contradiction if a refutation also exists!
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
        // Sticky contradiction if a proof also exists!
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
      // Strictly require non-empty file_hash matching current artifact hash!
      const currentHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
      if (sub.audit.file_hash && currentHash && sub.audit.file_hash === currentHash) {
        lemma.audit = sub.audit;
        applied++;
      }
    }
  }

  for (const s of state.seats || []) {
    s.counts = {
      ...(s.counts || {}),
      checked: state.lemmas.filter((l) => l.status === "checked" && l.checker?.by_seat === s.id).length,
      refuted: state.lemmas.filter((l) => l.status === "refuted" && l.refutation?.by_seat === s.id).length,
      blocked: state.lemmas.filter((l) => l.status === "dead" && l.epitaph?.by_seat === s.id).length,
    };
  }

  return { applied, state };
}

/**
 * Pure in-memory mission state derivation from disk seed + submissions/*.json.
 * Never mutates `state.json` on disk!
 */
export function deriveMissionState(slug = DEFAULT_MISSION, { excludeSubmissionFiles = [] } = {}) {
  const mission = loadMission(slug);
  const { stateFile, submissionsDir } = mission.paths;
  if (!fs.existsSync(stateFile)) {
    throw new Error(`No base state.json for mission "${slug}"`);
  }
  const seed = JSON.parse(fs.readFileSync(stateFile, "utf8"));
  if (!fs.existsSync(submissionsDir)) return { applied: 0, state: seed };

  const excludeSet = new Set(excludeSubmissionFiles.map((f) => path.basename(f)));
  const rawSubs = fs
    .readdirSync(submissionsDir)
    .filter((f) => f.endsWith(".json") && !excludeSet.has(f))
    .map((f) => {
      try {
        return { file: f, ...JSON.parse(fs.readFileSync(path.join(submissionsDir, f), "utf8")) };
      } catch {
        return null;
      }
    })
    .filter(Boolean);

  const relDir = path.relative(ROOT, submissionsDir);
  const gitAddedTs = gitFirstAddedMap(relDir);
  return applySubmissionsPure(seed, rawSubs, { gitAddedTs });
}

/**
 * Explicit disk write (only invoked by `fleet compile`). Byte-identical when nothing changed!
 */
export function compileSubmissionsIntoState(slug = DEFAULT_MISSION) {
  const mission = loadMission(slug);
  const { stateFile } = mission.paths;
  const prevRaw = fs.existsSync(stateFile) ? fs.readFileSync(stateFile, "utf8") : "";
  const { applied, state } = deriveMissionState(slug);
  const nextRaw = JSON.stringify(state, null, 2) + "\n";
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
