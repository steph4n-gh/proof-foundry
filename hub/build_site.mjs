#!/usr/bin/env node
/**
 * hub/build_site.mjs — Pure static site & PROOFS.md builder (v3).
 *
 * Hardened per Opus 5.5 + Astra 6.2 reviews:
 * - Pure derivation (`deriveMissionState`): NEVER mutates tracked `state.json` on disk!
 * - Always publishes fresh `dist/PROOFS.md` directly on GitHub Pages; only writes repo-root
 *   `PROOFS.md` when invoked with `--sync-root-proofs`.
 * - Per-line resilient NDJSON event reader (one corrupt line never wipes event history).
 * - Mission-scoped PR map (`by_mission_claim` + `by_claim`) paginating up to 200 open PRs.
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
  deriveMissionState,
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

export function readEvents(eventsPath, limit = 160) {
  try {
    const lines = fs.readFileSync(eventsPath, "utf8").split(/\r?\n/).filter(Boolean);
    const parsed = [];
    for (let i = Math.max(0, lines.length - limit); i < lines.length; i++) {
      try {
        parsed.push(JSON.parse(lines[i]));
      } catch {
        // Skip malformed event line without losing the rest of the audit log
      }
    }
    return parsed.reverse();
  } catch {
    return [];
  }
}

/**
 * Fetch up to 200 open PRs from GitHub (non-fatal offline fallback) keyed by BOTH
 * `mission/claimId` (from changed submission paths) and bare `claimId` (from title fallback).
 */
export function fetchOpenPRs(repo = "steph4n-gh/proof-foundry") {
  const fetchedAt = new Date().toISOString();
  try {
    const res = spawnSync(
      "gh",
      ["pr", "list", "--repo", repo, "--state", "open", "--limit", "200", "--json", "number,title,url,headRefName,updatedAt,files"],
      { encoding: "utf8", timeout: 10000 }
    );
    if (res.status !== 0 || !res.stdout) {
      return { ok: false, fetched_at: fetchedAt, by_mission_claim: {}, by_claim: {} };
    }
    const prs = JSON.parse(res.stdout);
    const byMissionClaim = {};
    const byClaim = {};
    for (const pr of prs) {
      const info = {
        number: pr.number,
        title: pr.title,
        url: pr.url,
        branch: pr.headRefName,
        updated_at: pr.updatedAt,
      };
      const scopedKeys = new Set();
      const bareIds = new Set();

      for (const f of pr.files || []) {
        const m = String(f.path || "").match(/^missions\/([a-z0-9-_]+)\/submissions\/([A-Z]-[a-z0-9]+-\d+)\./);
        if (m) scopedKeys.add(`${m[1]}/${m[2]}`);
      }
      if (scopedKeys.size === 0) {
        const titleMatches = String(pr.title || "").matchAll(/\b([A-Z]-[a-z0-9]+-\d+)\b/g);
        for (const m of titleMatches) bareIds.add(m[1]);
      }

      for (const key of scopedKeys) {
        (byMissionClaim[key] = byMissionClaim[key] || []).push(info);
      }
      for (const id of bareIds) {
        (byClaim[id] = byClaim[id] || []).push(info);
      }
    }
    return { ok: true, fetched_at: fetchedAt, by_mission_claim: byMissionClaim, by_claim: byClaim };
  } catch {
    return { ok: false, fetched_at: fetchedAt, by_mission_claim: {}, by_claim: {} };
  }
}

export function buildMissionSnapshot(mission, prSnap = null) {
  const { state } = deriveMissionState(mission.slug);
  const events = readEvents(mission.paths.eventsFile, 160);
  const leftKey = mission.tug_of_war?.left_key || "p_neq_np";
  const rightKey = mission.tug_of_war?.right_key || "p_eq_np";
  const scopedPrMap = prSnap?.by_mission_claim || {};
  const barePrMap = prSnap?.by_claim || {};

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
    const scoped = scopedPrMap[`${mission.slug}/${l.id}`] || [];
    const bare = barePrMap[l.id] || [];
    const seenPrNums = new Set();
    const open_prs = [...scoped, ...bare].filter((p) => {
      if (seenPrNums.has(p.number)) return false;
      seenPrNums.add(p.number);
      return true;
    });

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
    pr_sync: prSnap ? { ok: prSnap.ok, fetched_at: prSnap.fetched_at } : { ok: false, fetched_at: null },
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

export function renderMasterProofsMarkdown(snapshots) {
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
    const verified = snap.lemmas.filter((l) => l.status === "checked" || l.status === "refuted" || l.status === "contradiction");
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
      const link = file ? `[${path.basename(file)}](https://github.com/${snap.mission.github_repo}/blob/main/${file})` : "—";
      const safeTitle = String(l.title || "").replace(/\|/g, "\\|");
      lines.push(
        `| \`${l.id}\` | ${sealIcons[l.seal] || l.status} | ${safeTitle} | ${link} | ${ax.length ? `\`${ax.join(", ")}\`` : "`none`"} | \`${hash.slice(0, 10)}\` |`
      );
    }
    lines.push("");
  }

  return lines.join("\n") + "\n";
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const syncRootProofs = process.argv.includes("--sync-root-proofs");
  const offline = process.argv.includes("--offline");

  fs.rmSync(DIST, { recursive: true, force: true });
  copyDir(PUBLIC_DIR, DIST);
  const dataDir = path.join(DIST, "data");
  fs.mkdirSync(dataDir, { recursive: true });

  const prSnap = offline ? { ok: false, fetched_at: null, by_mission_claim: {}, by_claim: {} } : fetchOpenPRs();
  const slugs = listMissionSlugs();
  const snaps = [];

  for (const slug of slugs) {
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

  const proofsMd = renderMasterProofsMarkdown(snaps);
  fs.writeFileSync(path.join(DIST, "PROOFS.md"), proofsMd, "utf8");
  if (syncRootProofs) {
    fs.writeFileSync(path.join(ROOT, "PROOFS.md"), proofsMd, "utf8");
  }

  fs.writeFileSync(
    path.join(dataDir, "missions.json"),
    JSON.stringify({ missions: loadAllMissionsSummary(), static: true, snapshot_at: new Date().toISOString() }, null, 2),
    "utf8"
  );
  console.log(`Built static GitHub Pages dashboard in dist/ (including dist/PROOFS.md) for ${slugs.length} missions: ${slugs.join(", ")}`);
}
