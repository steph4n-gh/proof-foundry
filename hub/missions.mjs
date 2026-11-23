#!/usr/bin/env node
/**
 * hub/missions.mjs — Multi-mission registry, path resolver, trust-seal computation,
 * and deterministic conflict-free submission compiler (fixes sort/contradiction/audit-hash bugs).
 */
import fs from "node:fs";
import path from "node:path";

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
 * Compute explicit 3-tier trust seal for a claim (Opus 5.5 design):
 *   contradiction | flagged | frozen | audited | provisional | refuted | dead | in_work | open
 */
export function computeTrustSeal(lemma) {
  if (lemma.status === "contradiction") return "contradiction";
  if (lemma.audit?.status === "flagged") return "flagged";
  if (lemma.status === "checked") {
    if (lemma.checker?.statement_frozen) return "frozen";
    if (lemma.audit?.status === "faithful") return "audited";
    return "provisional";
  }
  if (lemma.status === "refuted") return "refuted";
  if (lemma.status === "dead") return "dead";
  if (lemma.status === "in_work") return "in_work";
  return "open";
}

export function loadAllMissionsSummary() {
  return listMissionSlugs().map((slug) => {
    const m = loadMission(slug);
    let counts = { lemmas: 0, checked: 0, trusted: 0, flagged: 0, in_work: 0, conjecture: 0, refuted: 0, dead: 0 };
    let objSummary = { total: (m.objectives || []).length, conquered: 0 };
    try {
      const st = JSON.parse(fs.readFileSync(m.paths.stateFile, "utf8"));
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

/**
 * Only non-flagged, trusted (audited or frozen-matched) proofs — or verified refutations when expected —
 * count toward conquering an Objective!
 */
export function isRungConquered(lemma, expect = "proof") {
  if (!lemma) return false;
  const seal = computeTrustSeal(lemma);
  if (seal === "flagged" || seal === "contradiction") return false;
  if (expect === "refutation") return lemma.status === "refuted";
  if (expect === "either") return seal === "audited" || seal === "frozen" || lemma.status === "refuted";
  return seal === "audited" || seal === "frozen";
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
 * Deterministic compiler from `missions/<slug>/submissions/*.json` into `state.json`.
 * - Applies in strict phase order: claim_add -> proof/refutation/rule_dead (timestamp asc) -> audit (hash-bound).
 * - Surfaces opposing verified proof + refutation as explicit `contradiction` (never silently drops one!).
 */
export function compileSubmissionsIntoState(slug = DEFAULT_MISSION) {
  const mission = loadMission(slug);
  const { stateFile, submissionsDir } = mission.paths;
  if (!fs.existsSync(stateFile)) {
    throw new Error(`No base state.json for mission "${slug}"`);
  }
  const state = JSON.parse(fs.readFileSync(stateFile, "utf8"));
  if (!fs.existsSync(submissionsDir)) return { applied: 0, state };

  const rawSubs = fs
    .readdirSync(submissionsDir)
    .filter((f) => f.endsWith(".json"))
    .map((f) => {
      try {
        return { file: f, ...JSON.parse(fs.readFileSync(path.join(submissionsDir, f), "utf8")) };
      } catch {
        return null;
      }
    })
    .filter((s) => s && s.lemma_id && s.kind);

  const kindOrder = { claim_add: 0, proof: 1, refutation: 1, rule_dead: 2, audit: 3 };
  rawSubs.sort((a, b) => {
    const ko = (kindOrder[a.kind] ?? 9) - (kindOrder[b.kind] ?? 9);
    if (ko !== 0) return ko;
    const t = String(a.at || "").localeCompare(String(b.at || ""));
    if (t !== 0) return t;
    return String(a.file).localeCompare(String(b.file));
  });

  // Track seen proof vs refutation per claim to surface contradictions explicitly
  const seenProof = new Set();
  const seenRefute = new Set();

  let applied = 0;
  for (const sub of rawSubs) {
    let lemma = state.lemmas.find((l) => l.id === sub.lemma_id);
    if (!lemma && sub.kind === "claim_add" && sub.claim) {
      state.lemmas.push(sub.claim);
      applied++;
      continue;
    }
    if (!lemma) continue;

    if (sub.kind === "proof" && sub.checker?.ok) {
      // First verified proof wins credit; if a refutation also exists -> CONTRADICTION!
      if (seenRefute.has(lemma.id) || lemma.status === "refuted") {
        lemma.status = "contradiction";
        lemma.checker = sub.checker;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      } else if (!seenProof.has(lemma.id)) {
        seenProof.add(lemma.id);
        lemma.status = "checked";
        lemma.lean_file = sub.file || lemma.lean_file;
        lemma.theorem_name = sub.theorem || lemma.theorem_name;
        if (!lemma.registered_statement) lemma.registered_statement = lemma.statement || "";
        if (sub.signature) {
          lemma.verified_signature = sub.signature;
          lemma.statement = sub.signature;
        }
        lemma.checker = sub.checker;
        lemma.updated_at = sub.at || lemma.updated_at;
        // Auto-register community donor seat if missing
        const seatId = sub.checker.by_seat;
        if (seatId && !state.seats.some((s) => s.id === seatId)) {
          state.seats.push({
            id: seatId,
            name: seatId,
            role: "donor",
            program: lemma.program,
            provider: "Community",
            model: "Token Donor",
            badge: "TD",
            color: "#0D9488",
            status: "idle",
            current_lemma: lemma.id,
            current_whisper: `Verified ${lemma.id}`,
            sessions: 1,
            last_seen: sub.at || new Date().toISOString(),
            counts: { checked: 0, refuted: 0, blocked: 0, attempts: 1, messages: 0 },
          });
        }
        applied++;
      }
    } else if (sub.kind === "refutation" && sub.refutation) {
      if (seenProof.has(lemma.id) || lemma.status === "checked") {
        lemma.status = "contradiction";
        lemma.refutation = sub.refutation;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      } else if (!seenRefute.has(lemma.id)) {
        seenRefute.add(lemma.id);
        lemma.status = "refuted";
        lemma.refutation = sub.refutation;
        lemma.updated_at = sub.at || lemma.updated_at;
        const rSeat = sub.refutation.by_seat;
        if (rSeat && !state.seats.some((s) => s.id === rSeat)) {
          state.seats.push({
            id: rSeat,
            name: rSeat,
            role: "donor",
            program: lemma.program,
            provider: "Community",
            model: "Token Donor",
            badge: "TD",
            color: "#DC2626",
            status: "idle",
            current_lemma: lemma.id,
            current_whisper: `Refuted ${lemma.id}`,
            sessions: 1,
            last_seen: sub.at || new Date().toISOString(),
            counts: { checked: 0, refuted: 0, blocked: 0, attempts: 1, messages: 0 },
          });
        }
        applied++;
      }
    } else if (sub.kind === "rule_dead" && sub.epitaph) {
      if (lemma.status !== "checked" && lemma.status !== "contradiction") {
        lemma.status = "dead";
        lemma.epitaph = sub.epitaph;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      }
    } else if (sub.kind === "audit" && sub.audit) {
      // Hash-bind audit to current artifact hash if specified
      const currentHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
      if (!sub.audit.file_hash || !currentHash || sub.audit.file_hash === currentHash) {
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

  state.meta.updated_at = new Date().toISOString();
  const tmp = `${stateFile}.tmp.${process.pid}.${Date.now()}`;
  const fd = fs.openSync(tmp, "w");
  try {
    fs.writeSync(fd, JSON.stringify(state, null, 2) + "\n", undefined, "utf8");
    fs.fsyncSync(fd);
  } finally {
    fs.closeSync(fd);
  }
  fs.renameSync(tmp, stateFile);
  return { applied, state };
}
