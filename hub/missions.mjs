#!/usr/bin/env node
/**
 * hub/missions.mjs — Multi-mission registry, path resolver, and conflict-free submission compiler.
 *
 * Each mission lives in `missions/<slug>/`:
 *   mission.json         — title, question, judge config, programs, seats, optional tug-of-war axis
 *   state.json           — compiled live snapshot (never hand-edited in GitHub PRs!)
 *   events.ndjson        — append-only local event log
 *   submissions/*.json   — conflict-free per-claim PR records (one immutable file per submission)
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

export function loadAllMissionsSummary() {
  return listMissionSlugs().map((slug) => {
    const m = loadMission(slug);
    let counts = { lemmas: 0, checked: 0, in_work: 0, conjecture: 0, refuted: 0, dead: 0 };
    try {
      const st = JSON.parse(fs.readFileSync(m.paths.stateFile, "utf8"));
      counts.lemmas = st.lemmas?.length || 0;
      for (const l of st.lemmas || []) counts[l.status] = (counts[l.status] || 0) + 1;
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
 * Compile all conflict-free `missions/<slug>/submissions/*.json` files into state.json.
 * Idempotent: re-running produces the exact same state.
 */
export function compileSubmissionsIntoState(slug = DEFAULT_MISSION) {
  const mission = loadMission(slug);
  const { stateFile, submissionsDir } = mission.paths;
  if (!fs.existsSync(stateFile)) {
    throw new Error(`No base state.json for mission "${slug}"`);
  }
  const state = JSON.parse(fs.readFileSync(stateFile, "utf8"));
  if (!fs.existsSync(submissionsDir)) return { applied: 0, state };

  const files = fs
    .readdirSync(submissionsDir)
    .filter((f) => f.endsWith(".json"))
    .sort();

  let applied = 0;
  for (const f of files) {
    const sub = JSON.parse(fs.readFileSync(path.join(submissionsDir, f), "utf8"));
    if (!sub || !sub.lemma_id || !sub.kind) continue;
    let lemma = state.lemmas.find((l) => l.id === sub.lemma_id);
    if (!lemma && sub.kind === "claim_add" && sub.claim) {
      state.lemmas.push(sub.claim);
      applied++;
      continue;
    }
    if (!lemma) continue;

    if (sub.kind === "proof" && sub.checker?.ok) {
      if (lemma.status !== "refuted" && lemma.status !== "dead") {
        lemma.status = "checked";
        lemma.lean_file = sub.file || lemma.lean_file;
        lemma.theorem_name = sub.theorem || lemma.theorem_name;
        if (sub.signature) {
          lemma.verified_signature = sub.signature;
          lemma.statement = sub.signature;
        }
        lemma.checker = sub.checker;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      }
    } else if (sub.kind === "refutation" && sub.refutation) {
      if (lemma.status !== "checked") {
        lemma.status = "refuted";
        lemma.refutation = sub.refutation;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      }
    } else if (sub.kind === "audit" && sub.audit) {
      lemma.audit = sub.audit;
      applied++;
    } else if (sub.kind === "rule_dead" && sub.epitaph) {
      if (lemma.status !== "checked") {
        lemma.status = "dead";
        lemma.epitaph = sub.epitaph;
        lemma.updated_at = sub.at || lemma.updated_at;
        applied++;
      }
    }
  }

  // Recompute seat counts deterministically from lemmas
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
