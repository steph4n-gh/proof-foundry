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
import { spawnSync } from "node:child_process";

import {
  ROOT,
  projectClaimView,
  projectMissionSnapshot,
  releaseClaimSeats,
  replayRecordSubmissions,
  sha256RelFile,
  transitionClaim,
} from "./state_machine.mjs";

export { ROOT, computeRecordTargets, computeTrustSeal, isRungConquered, normalizeObjectiveReqs, sha256RelFile } from "./state_machine.mjs";
export const MISSIONS_DIR = path.join(ROOT, "missions");
export const DEFAULT_MISSION = "crypto-zk-circuits";

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

export function loadAllMissionsSummary(snapshots = []) {
  const bySlug = new Map(snapshots.map((snap) => [snap.mission.slug, snap]));
  return listMissionSlugs().map((slug) => {
    const mission = loadMission(slug);
    let counts = {
      lemmas: 0, checked: 0, trusted: 0, flagged: 0, records_active: 0, records_closed: 0,
      in_work: 0, conjecture: 0, refuted: 0, dead: 0, contradiction: 0,
    };
    let objectivesDetail = [];
    let snap = bySlug.get(slug);
    try {
      if (!snap) {
        const { state } = deriveMissionState(slug, { project: false });
        snap = projectMissionSnapshot(mission, state);
      }
      for (const key of Object.keys(counts)) counts[key] = snap.counts[key];
      objectivesDetail = snap.mission.objectives.map((obj) => ({
        id: obj.id,
        title: obj.title,
        tier: obj.tier || "",
        conquered: obj.conquered,
        rungs: obj.items.map((item) => ({ id: item.id, conquered: item.done, seal: item.seal })),
      }));
    } catch {}
    return {
      slug,
      brand: mission.brand || mission.title,
      title: mission.title,
      tagline: mission.tagline || "",
      question: mission.question,
      description: mission.description || "",
      judge_type: mission.judge?.type || "lean4",
      judge_label: mission.judge?.label || mission.judge?.type || "Judge",
      impact: mission.impact || null,
      counts,
      objectives: {
        total: (mission.objectives || []).length,
        conquered: objectivesDetail.filter((obj) => obj.conquered).length,
      },
      objectives_detail: objectivesDetail,
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
 * Pure deterministic derivation: (seedState, submissions[]) -> { applied, state }.
 */
export function applySubmissionsPure(seedState, rawSubs, { gitAddedTs = new Map(), missionSlug = null, currentHashes = {} } = {}) {
  let state = structuredClone(seedState);
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

  let applied = 0;

  for (const l of state.lemmas || []) {
    if (l.kind !== "record" && l.checker?.ok && l.refutation) l.status = "contradiction";
  }

  for (const sub of nonRecordSubs) {
    const idx = state.lemmas.findIndex((l) => l.id === sub.lemma_id);
    const lemma = state.lemmas[idx];
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
    if (!lemma || lemma.kind === "record" || !Object.hasOwn(kindOrder, sub.kind) || sub.kind === "claim_add") continue;

    const result = transitionClaim(lemma, sub, { mode: "replay" });
    if (!result.ok || result.lemma === lemma) continue;

    state.lemmas[idx] = result.lemma;
    if (sub.kind !== "audit") state = releaseClaimSeats(state, lemma.id);
    if (sub.kind === "proof") {
      ensureDerivedSeat(state, sub.checker.by_seat, lemma.program, "donor", `Verified ${lemma.id}`, sub.at);
    }
    if (sub.kind === "refutation") {
      ensureDerivedSeat(state, sub.refutation.by_seat, lemma.program, "refuter", `Refuted ${lemma.id}`, sub.at);
    }
    applied++;
  }

  for (let idx = 0; idx < state.lemmas.length; idx++) {
    const seedLemma = state.lemmas[idx];
    if (seedLemma.kind !== "record") continue;
    const rSubs = recordSubsByLemma.get(seedLemma.id) || [];
    const lemma = replayRecordSubmissions(slug, seedLemma, rSubs, { gitAddedTs, currentHashes });
    const rs = lemma.record_state;
    state.lemmas[idx] = lemma;

    if (rs.best) {
      lemma.lean_file = rs.best.file;
      lemma.theorem_name = rs.best.theorem;
      ensureDerivedSeat(state, rs.best.seat, lemma.program, "record_holder", `Record ${rs.best.score} on ${lemma.id}`, rs.best.at);
    }
    if (rs.refuted) {
      ensureDerivedSeat(state, rs.refuted.seat, lemma.program, "donor", `Bound ${rs.refuted.inclusive_bound} on ${lemma.id}`, rs.refuted.at);
    }
    if (rs.closed || rs.contradiction) state = releaseClaimSeats(state, lemma.id);
    for (const h of rs.history) {
      if (h.state === "accepted") {
        ensureDerivedSeat(state, h.seat, lemma.program, "donor", `${h.kind} s=${h.score} on ${lemma.id}`, h.at);
        applied++;
      }
    }
  }

  // Recompute per-seat counts (record_points kept distinct from checked proofs — zero double-counting!)
  const recordPointsBySeat = Object.create(null);
  for (const l of state.lemmas || []) {
    if (l.kind === "record" && l.record_state && !l.record_state.contradiction && l.record_state.points_by_seat) {
      for (const [seatId, pts] of Object.entries(l.record_state.points_by_seat)) {
        const prev = Object.hasOwn(recordPointsBySeat, seatId) ? recordPointsBySeat[seatId] : 0;
        recordPointsBySeat[seatId] = prev + pts;
      }
    }
  }

  for (const s of state.seats || []) {
    s.counts = {
      ...(s.counts || {}),
      checked: state.lemmas.filter((l) => l.kind !== "record" && l.status === "checked" && l.checker?.by_seat === s.id).length,
      refuted: state.lemmas.filter((l) => l.kind !== "record" && l.status === "refuted" && l.refutation?.by_seat === s.id).length,
      blocked: state.lemmas.filter((l) => l.kind !== "record" && l.status === "dead" && l.epitaph?.by_seat === s.id).length,
      record_points: Object.hasOwn(recordPointsBySeat, s.id) ? recordPointsBySeat[s.id] : 0,
    };
  }

  return { applied, state };
}

/**
 * Pure in-memory mission state derivation from disk seed + submissions/*.json.
 */
export function deriveMissionState(slug = DEFAULT_MISSION, { excludeSubmissionFiles = [], project = true } = {}) {
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

  const excludeSet = new Set(excludeSubmissionFiles.map((f) => path.basename(f)));
  const files = fs.existsSync(submissionsDir) ? fs.readdirSync(submissionsDir) : [];
  const rawSubs = files
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
  const gitAddedTs = rawSubs.length ? gitFirstAddedMap(relDir) : new Map();
  const result = applySubmissionsPure(seed, rawSubs, { gitAddedTs, missionSlug: slug, currentHashes });
  if (project) {
    result.state.lemmas = result.state.lemmas.map((lemma) => projectClaimView(mission, lemma, currentHashes.coreHash));
  }
  return result;
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
  const { applied, state } = deriveMissionState(slug, { project: false });
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
