#!/usr/bin/env node
/**
 * hub/build_site.mjs — Compiles a static GitHub Pages bundle in `dist/` containing
 * all missions, snapshots, and lemma/artifact dossiers so the exact same editorial dashboard
 * runs for free on GitHub Pages with zero server required.
 */
import fs from "node:fs";
import path from "node:path";
import {
  ROOT,
  listMissionSlugs,
  loadMission,
  loadAllMissionsSummary,
  readAllowedArtifactFile,
  compileSubmissionsIntoState,
} from "./missions.mjs";

const DIST = path.join(ROOT, "dist");
const PUBLIC_DIR = path.join(ROOT, "web", "public");

function copyDir(src, dst) {
  fs.mkdirSync(dst, { recursive: true });
  for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, entry.name);
    const d = path.join(dst, entry.name);
    if (entry.isDirectory()) copyDir(s, d);
    else fs.copyFileSync(s, d);
  }
}

function readEvents(eventsPath, limit = 160) {
  try {
    const lines = fs.readFileSync(eventsPath, "utf8").trim().split("\n").filter(Boolean);
    return lines.slice(-limit).reverse().map((l) => JSON.parse(l));
  } catch {
    return [];
  }
}

export function buildMissionSnapshot(mission) {
  const state = JSON.parse(fs.readFileSync(mission.paths.stateFile, "utf8"));
  const events = readEvents(mission.paths.eventsFile, 160);
  const leftKey = mission.tug_of_war?.left_key || "p_neq_np";
  const rightKey = mission.tug_of_war?.right_key || "p_eq_np";

  const counts = {
    lemmas: state.lemmas.length,
    checked: 0,
    audited_faithful: 0,
    in_work: 0,
    conjecture: 0,
    refuted: 0,
    dead: 0,
    aims_left_checked: 0,
    aims_right_checked: 0,
    aims_neutral_checked: 0,
    agents_working: 0,
    agents_checking: 0,
  };

  let frontier = null;
  for (const l of state.lemmas) {
    counts[l.status] = (counts[l.status] || 0) + 1;
    if (l.audit?.status === "faithful") counts.audited_faithful++;
    if (l.status === "checked") {
      if (l.aims_at === leftKey) counts.aims_left_checked++;
      else if (l.aims_at === rightKey) counts.aims_right_checked++;
      else counts.aims_neutral_checked++;

      const score = (l.rung || 0) * 10 + (l.deps?.length || 0) * 5;
      const bestScore = frontier ? (frontier.rung || 0) * 10 + (frontier.deps?.length || 0) * 5 : -1;
      if (
        !frontier ||
        score > bestScore ||
        (score === bestScore && (l.checker?.checked_at || "") > (frontier.checker?.checked_at || ""))
      ) {
        frontier = l;
      }
    }
  }
  for (const s of state.seats || []) {
    if (s.status === "working") counts.agents_working++;
    if (s.status === "checking") counts.agents_checking++;
  }
  const justIn =
    events.find((e) => ["checker_accepted", "claim_refuted", "approach_dead"].includes(e.type)) ||
    null;

  const objectives = (mission.objectives || []).map((obj) => {
    const req = obj.required_claims || [];
    const items = req.map((id) => {
      const l = state.lemmas.find((x) => x.id === id);
      return {
        id,
        title: l?.title || id,
        status: l?.status || "conjecture",
        done: l?.status === "checked" || (obj.accept_refutation && l?.status === "refuted"),
      };
    });
    const completed = items.filter((i) => i.done).length;
    const total = items.length;
    return {
      ...obj,
      items,
      completed,
      total,
      pct: total > 0 ? Math.round((completed / total) * 100) : 0,
      conquered: total > 0 && completed === total,
    };
  });

  return {
    ready: true,
    mission: {
      slug: mission.slug,
      brand: mission.brand,
      title: mission.title,
      tagline: mission.tagline,
      question: mission.question,
      description: mission.description,
      tug_of_war: mission.tug_of_war,
      judge: { type: mission.judge?.type, label: mission.judge?.label },
      github_repo: mission.github_repo || "steph4n-gh/proof-foundry",
      objectives,
    },
    ...state,
    counts,
    frontier,
    just_in: justIn,
    events,
  };
}

if (import.meta.url === `file://${process.argv[1]}`) {
  fs.rmSync(DIST, { recursive: true, force: true });
  copyDir(PUBLIC_DIR, DIST);
  const dataDir = path.join(DIST, "data");
  fs.mkdirSync(dataDir, { recursive: true });

  const slugs = listMissionSlugs();
  for (const slug of slugs) {
    compileSubmissionsIntoState(slug);
    const mission = loadMission(slug);
    const snap = buildMissionSnapshot(mission);
    const mDir = path.join(dataDir, slug);
    const lDir = path.join(mDir, "lemmas");
    fs.mkdirSync(lDir, { recursive: true });
    fs.writeFileSync(path.join(mDir, "state.json"), JSON.stringify(snap), "utf8");

    for (const l of snap.lemmas) {
      const dossier = {
        lemma: l,
        leanSource: readAllowedArtifactFile(mission, l.lean_file),
        refutationSource: readAllowedArtifactFile(mission, l.refutation?.counterexample_file),
        relatedMessages: (snap.messages || []).filter((m) => m.lemma_id === l.id),
        relatedRuns: (snap.checker_runs || []).filter((r) => r.lemma_id === l.id),
        dependents: snap.lemmas
          .filter((o) => (o.deps || []).includes(l.id))
          .map((o) => ({ id: o.id, title: o.title, status: o.status })),
      };
      fs.writeFileSync(path.join(lDir, `${l.id}.json`), JSON.stringify(dossier), "utf8");
    }
  }

  fs.writeFileSync(
    path.join(dataDir, "missions.json"),
    JSON.stringify({ missions: loadAllMissionsSummary(), static: true }, null, 2),
    "utf8"
  );
  console.log(`Built static GitHub Pages dashboard in dist/ for ${slugs.length} missions: ${slugs.join(", ")}`);
}
