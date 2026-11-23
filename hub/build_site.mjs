#!/usr/bin/env node
/**
 * hub/build_site.mjs — Compiles:
 *   1. Static GitHub Pages dashboard (`dist/`) across all missions (with live GitHub open-PR snapshot!).
 *   2. Canonical human-readable master catalog (`PROOFS.md`) in the repository root.
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import {
  ROOT,
  listMissionSlugs,
  loadMission,
  loadAllMissionsSummary,
  readAllowedArtifactFile,
  compileSubmissionsIntoState,
  computeTrustSeal,
  normalizeObjectiveReqs,
  isRungConquered,
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

/**
 * Fetch open PRs from GitHub (non-fatal offline fallback) so Pages & local UI show live PR badges.
 */
export function fetchOpenPRs(repo = "steph4n-gh/proof-foundry") {
  const fetchedAt = new Date().toISOString();
  try {
    const res = spawnSync(
      "gh",
      ["pr", "list", "--repo", repo, "--state", "open", "--limit", "50", "--json", "number,title,url,headRefName,updatedAt,files"],
      { encoding: "utf8", timeout: 8000 }
    );
    if (res.status !== 0 || !res.stdout) return { ok: false, fetched_at: fetchedAt, by_claim: {} };
    const prs = JSON.parse(res.stdout);
    const byClaim = {};
    for (const pr of prs) {
      const ids = new Set();
      const titleMatches = String(pr.title || "").matchAll(/\b([A-Z]-[a-z0-9]+-\d+)\b/g);
      for (const m of titleMatches) ids.add(m[1]);
      for (const f of pr.files || []) {
        const m = String(f.path || "").match(/submissions\/([A-Z]-[a-z0-9]+-\d+)\./);
        if (m) ids.add(m[1]);
      }
      for (const id of ids) {
        (byClaim[id] = byClaim[id] || []).push({
          number: pr.number,
          title: pr.title,
          url: pr.url,
          branch: pr.headRefName,
          updated_at: pr.updatedAt,
        });
      }
    }
    return { ok: true, fetched_at: fetchedAt, by_claim: byClaim };
  } catch {
    return { ok: false, fetched_at: fetchedAt, by_claim: {} };
  }
}

export function buildMissionSnapshot(mission, prSnap = null) {
  const state = JSON.parse(fs.readFileSync(mission.paths.stateFile, "utf8"));
  const events = readEvents(mission.paths.eventsFile, 160);
  const leftKey = mission.tug_of_war?.left_key || "p_neq_np";
  const rightKey = mission.tug_of_war?.right_key || "p_eq_np";
  const openPrMap = prSnap?.by_claim || {};

  const counts = {
    lemmas: state.lemmas.length,
    checked: 0,
    trusted: 0,
    audited_faithful: 0,
    frozen_matched: 0,
    flagged: 0,
    contradiction: 0,
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
  const enrichedLemmas = state.lemmas.map((l) => {
    const seal = computeTrustSeal(l);
    const open_prs = openPrMap[l.id] || [];
    counts[l.status] = (counts[l.status] || 0) + 1;
    if (seal === "audited") counts.audited_faithful++;
    if (seal === "frozen") counts.frozen_matched++;
    if (seal === "audited" || seal === "frozen") counts.trusted++;
    if (seal === "flagged") counts.flagged++;
    if (l.status === "checked") {
      if (l.aims_at === leftKey) counts.aims_left_checked++;
      else if (l.aims_at === rightKey) counts.aims_right_checked++;
      else counts.aims_neutral_checked++;

      if (seal !== "flagged") {
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
    return { ...l, seal, open_prs };
  });

  for (const s of state.seats || []) {
    if (s.status === "working") counts.agents_working++;
    if (s.status === "checking") counts.agents_checking++;
  }

  const justIn =
    events.find((e) => ["checker_accepted", "claim_refuted", "approach_dead", "lemma_audited"].includes(e.type)) ||
    null;

  const objectives = (mission.objectives || []).map((obj) => {
    const reqs = normalizeObjectiveReqs(obj);
    const items = reqs.map((r) => {
      const l = enrichedLemmas.find((x) => x.id === r.id);
      const done = isRungConquered(l, r.expect);
      return {
        id: r.id,
        expect: r.expect,
        title: l?.title || r.id,
        status: l?.status || "conjecture",
        seal: l?.seal || "open",
        open_prs: l?.open_prs || [],
        done,
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
    snapshot_at: new Date().toISOString(),
    pr_sync: prSnap ? { ok: prSnap.ok, fetched_at: prSnap.fetched_at } : null,
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
    lemmas: enrichedLemmas,
    counts,
    frontier,
    just_in: justIn,
    events,
  };
}

/**
 * Generate master human-readable `PROOFS.md` catalog in the repository root.
 */
export function writeMasterProofsMarkdown(snapshots) {
  const sealIcons = {
    frozen: "◆ Frozen",
    audited: "✓ Audited",
    provisional: "◇ Provisional",
    flagged: "⚠ Flagged",
    refuted: "✕ Refuted",
    dead: "☠ Barrier",
    contradiction: "⛔ Contradiction",
  };
  let totalChecked = 0;
  let totalRefuted = 0;
  let totalAudited = 0;
  for (const s of snapshots) {
    totalChecked += s.counts.checked;
    totalRefuted += s.counts.refuted;
    totalAudited += s.counts.trusted;
  }

  const lines = [
    "# Proof Foundry — Master Verified Catalog",
    "",
    `> Auto-generated from conflict-free mission records. **${totalChecked} Judge-verified proofs** (${totalAudited} cross-model audited / frozen-matched) and **${totalRefuted} Judge-verified refutations** across ${snapshots.length} open-science missions.`,
    "",
    "**Trust Seal Legend:** `◆ Frozen` (kernel type-matched against frozen statement) · `✓ Audited` (independent cross-model faithfulness audit passed) · `◇ Provisional` (kernel verified, audit pending) · `⚠ Flagged` (audit found statement/title gap — does NOT count toward Objective completion) · `✕ Refuted` (Judge-verified counterexample).",
    "",
  ];

  for (const snap of snapshots) {
    lines.push(`## ${snap.mission.title} (\`${snap.mission.slug}\`)`);
    lines.push(`*Judge: ${snap.mission.judge?.label}*\n`);
    const verified = snap.lemmas.filter((l) => l.status === "checked" || l.status === "refuted");
    if (!verified.length) {
      lines.push("_No verified claims yet._\n");
      continue;
    }
    lines.push("| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |");
    lines.push("|---|---|---|---|---|---|");
    for (const l of verified) {
      const file = l.status === "refuted" ? l.refutation?.counterexample_file : l.lean_file;
      const hash = (l.status === "refuted" ? l.refutation?.file_hash : l.checker?.file_hash) || "";
      const ax = (l.status === "refuted" ? l.refutation?.axioms : l.checker?.axioms) || [];
      const link = file ? `[${path.basename(file)}](./${file})` : "—";
      const safeTitle = String(l.title || "").replace(/\|/g, "\\|");
      lines.push(
        `| \`${l.id}\` | ${sealIcons[l.seal] || l.status} | ${safeTitle} | ${link} | ${ax.length ? `\`${ax.join(", ")}\`` : "`none`"} | \`${hash.slice(0, 10)}\` |`
      );
    }
    lines.push("");
  }

  fs.writeFileSync(path.join(ROOT, "PROOFS.md"), lines.join("\n") + "\n", "utf8");
}

if (import.meta.url === `file://${process.argv[1]}`) {
  fs.rmSync(DIST, { recursive: true, force: true });
  copyDir(PUBLIC_DIR, DIST);
  const dataDir = path.join(DIST, "data");
  fs.mkdirSync(dataDir, { recursive: true });

  const prSnap = fetchOpenPRs();
  const slugs = listMissionSlugs();
  const snaps = [];

  for (const slug of slugs) {
    compileSubmissionsIntoState(slug);
    const mission = loadMission(slug);
    const snap = buildMissionSnapshot(mission, prSnap);
    snaps.push(snap);

    const mDir = path.join(dataDir, slug);
    const lDir = path.join(mDir, "lemmas");
    fs.mkdirSync(lDir, { recursive: true });
    fs.writeFileSync(path.join(mDir, "state.json"), JSON.stringify(snap), "utf8");

    for (const l of snap.lemmas) {
      const dossier = {
        lemma: l,
        leanSource: readAllowedArtifactFile(mission, l.lean_file),
        refutationSource: readAllowedArtifactFile(mission, l.refutation?.counterexample_file),
        statementSource: l.statement_file ? readAllowedArtifactFile(mission, l.statement_file) : null,
        relatedMessages: (snap.messages || []).filter((m) => m.lemma_id === l.id),
        relatedRuns: (snap.checker_runs || []).filter((r) => r.lemma_id === l.id),
        dependents: snap.lemmas
          .filter((o) => (o.deps || []).includes(l.id))
          .map((o) => ({ id: o.id, title: o.title, status: o.status, seal: o.seal })),
      };
      fs.writeFileSync(path.join(lDir, `${l.id}.json`), JSON.stringify(dossier), "utf8");
    }
  }

  writeMasterProofsMarkdown(snaps);

  fs.writeFileSync(
    path.join(dataDir, "missions.json"),
    JSON.stringify({ missions: loadAllMissionsSummary(), static: true, snapshot_at: new Date().toISOString() }, null, 2),
    "utf8"
  );
  console.log(`Built static GitHub Pages dashboard in dist/ + PROOFS.md for ${slugs.length} missions: ${slugs.join(", ")}`);
}
