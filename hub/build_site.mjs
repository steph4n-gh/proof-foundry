#!/usr/bin/env node
/**
 * hub/build_site.mjs — Pure static site & PROOFS.md builder (v4 — with King of the Hill Scoreboards).
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
  readMissionStatementFile,
  deriveMissionState,
} from "./missions.mjs";
import { projectGlobalRecords, projectMissionSnapshot } from "./state_machine.mjs";
import { extractDropInArtifact } from "./export_dropin.mjs";

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
      } catch {}
    }
    return parsed.reverse();
  } catch {
    return [];
  }
}

function allKnownClaimIds() {
  const ids = new Set();
  for (const slug of listMissionSlugs()) {
    try {
      const m = loadMission(slug);
      if (fs.existsSync(m.paths.stateFile)) {
        const st = JSON.parse(fs.readFileSync(m.paths.stateFile, "utf8"));
        for (const l of st.lemmas || []) if (l.id) ids.add(l.id);
      }
    } catch {}
  }
  return ids;
}

function prCheckState(rollup) {
  if (!Array.isArray(rollup) || !rollup.length) return "pending";
  const failures = new Set(["FAILURE", "ERROR", "CANCELLED", "TIMED_OUT", "ACTION_REQUIRED", "STARTUP_FAILURE", "STALE"]);
  const successes = new Set(["SUCCESS", "NEUTRAL", "SKIPPED"]);
  const results = rollup.map((check) => check?.conclusion || check?.state || check?.status);
  if (results.some((result) => failures.has(result))) return "needs_fix";
  return results.every((result) => successes.has(result)) ? "passing" : "pending";
}

/**
 * Fetch up to 200 open PRs keyed by `mission/claimId` and bare `claimId`
 * (matches every registered claim ID including MM-rec-4x4-f2, CZ-rec-aes-and, ML-rec-bf16-exp2, EC-rec-*, etc.!).
 */
export function fetchOpenPRs(repo = "steph4n-gh/proof-foundry") {
  const fetchedAt = new Date().toISOString();
  try {
    const res = spawnSync(
      "gh",
      ["pr", "list", "--repo", repo, "--state", "open", "--limit", "200", "--json", "number,title,url,headRefName,updatedAt,files,statusCheckRollup"],
      { encoding: "utf8", timeout: 10000 }
    );
    if (res.status !== 0 || !res.stdout) {
      return { ok: false, fetched_at: fetchedAt, by_mission_claim: {}, by_claim: {} };
    }
    const prs = JSON.parse(res.stdout);
    const knownIds = allKnownClaimIds();
    const byMissionClaim = {};
    const byClaim = {};
    for (const pr of prs) {
      const info = {
        number: pr.number,
        title: pr.title,
        url: pr.url,
        branch: pr.headRefName,
        updated_at: pr.updatedAt,
        check_state: prCheckState(pr.statusCheckRollup),
      };
      const scopedKeys = new Set();
      const bareIds = new Set();

      for (const f of pr.files || []) {
        const m = String(f.path || "").match(/^missions\/([a-z0-9-_]+)\/submissions\/([A-Za-z0-9-]+)\./);
        if (m) scopedKeys.add(`${m[1]}/${m[2]}`);
      }
      if (scopedKeys.size === 0) {
        const titleMatches = String(pr.title || "").matchAll(/\b([A-Z]{1,3}-[a-zA-Z0-9]+(?:-[a-zA-Z0-9]+)*)\b/g);
        for (const m of titleMatches) {
          if (knownIds.size === 0 || knownIds.has(m[1])) bareIds.add(m[1]);
        }
      }

      for (const key of scopedKeys) (byMissionClaim[key] = byMissionClaim[key] || []).push(info);
      for (const id of bareIds) (byClaim[id] = byClaim[id] || []).push(info);
    }
    return { ok: true, fetched_at: fetchedAt, by_mission_claim: byMissionClaim, by_claim: byClaim };
  } catch {
    return { ok: false, fetched_at: fetchedAt, by_mission_claim: {}, by_claim: {} };
  }
}

export function buildMissionSnapshot(mission, prSnap = null) {
  const { state } = deriveMissionState(mission.slug, { project: false });
  const events = readEvents(mission.paths.eventsFile, 160);
  const projected = projectMissionSnapshot(mission, state, prSnap);
  return {
    ...projected,
    mission: {
      ...projected.mission,
      impact: mission.impact || null,
    },
    ready: true,
    snapshot_at: new Date().toISOString(),
    pr_sync: prSnap ? { ok: prSnap.ok, fetched_at: prSnap.fetched_at } : { ok: false, fetched_at: null },
    just_in: events.find((e) => ["checker_accepted", "claim_refuted", "approach_dead", "lemma_audited"].includes(e.type)) || null,
    events,
  };
}

export function renderMasterProofsMarkdown(snapshots) {
  const sealIcons = {
    frozen: "◆ Frozen",
    record: "♛ Record",
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
  const allRecords = [];

  for (const s of snapshots) {
    totalChecked += s.counts.checked;
    totalRefuted += s.counts.refuted;
    totalAudited += s.counts.trusted;
    for (const l of s.lemmas) {
      if (l.kind === "record") allRecords.push({ mission: s.mission, lemma: l });
    }
  }

  const lines = [
    "# Proof Foundry — Master Verified Catalog",
    "",
    `> Auto-generated from conflict-free mission records. **${totalChecked} Judge-verified proofs** (${totalAudited} cross-model audited / frozen-matched), **${totalRefuted} Judge-verified refutations**, and **${allRecords.length} King-of-the-Hill auto-ratcheting record hunts** across ${snapshots.length} open-science missions.`,
    "",
    "**Trust Seal Legend:** `◆ Frozen` (kernel type-matched against frozen statement) · `♛ Record` (active King-of-the-Hill holder — open to beat!) · `✓ Audited` (cross-model faithfulness audit passed) · `◇ Provisional` (kernel verified, audit pending) · `⚠ Flagged` (audit found statement/title gap) · `✕ Refuted` (Judge-verified counterexample).",
    "",
  ];

  const impactOrder = { direct_production: 0, research_frontier: 1, foundational: 2 };
  const impactSnaps = [...snapshots].sort(
    (a, b) => (impactOrder[a.mission.impact?.tier] ?? 9) - (impactOrder[b.mission.impact?.tier] ?? 9) || a.mission.slug.localeCompare(b.mission.slug)
  );
  if (impactSnaps.some((s) => s.mission.impact)) {
    lines.push("## Where Verified Proofs Ship (Direct Real-World Impact)");
    lines.push("");
    lines.push("> Full real-world impact breakdown & drop-in integration examples: [docs/REAL_WORLD_IMPACT.md](./docs/REAL_WORLD_IMPACT.md).");
    lines.push("");
    lines.push("| Mission | Impact Tier | Ships Directly To | What One Step Buys |");
    lines.push("|---|---|---|---|");
    for (const s of impactSnaps) {
      const imp = s.mission.impact;
      if (!imp) continue;
      const safeShips = String(imp.ships_to || "").replace(/\|/g, "\\|");
      const safeGain = String(imp.what_one_step_buys || "").replace(/\|/g, "\\|");
      lines.push(`| \`${s.mission.slug}\` | **${imp.tier_label || imp.tier}** | ${safeShips} | ${safeGain} |`);
    }
    lines.push("");
  }

  if (allRecords.length) {
    lines.push("## King of the Hill — Live Auto-Ratcheting Record Hunts");
    lines.push("");
    lines.push("| Mission | ID | Target | Current Best | Next Target | Proven Bound | Holder | Status |");
    lines.push("|---|---|---|---|---|---|---|---|");
    for (const { mission, lemma: l } of allRecords) {
      const meta = l.record_meta;
      const isMax = meta.direction === "max";
      const boundOp = isMax ? "≤" : "≥";
      const bestTxt = meta.best_score != null
        ? `**${meta.best_score}** ${meta.unit}`
        : `*(unclaimed, ${isMax ? "floor" : "ceiling"} ${meta.start_target})*`;
      const nextTxt = meta.contradiction ? "Halted (Contradiction)"
        : meta.closed ? "Exact Optimal ✓" : `\`${meta.op} ${meta.next_target}\``;
      const lbTxt = meta.proven_bound != null ? `${boundOp} ${meta.proven_bound}`
        : meta.literature_bound != null ? `*(lit. ${boundOp} ${meta.literature_bound})*` : "—";
      const holder = meta.best_seat ? `\`${meta.best_seat}\`` : "—";
      const status = meta.contradiction ? "⛔ Contradiction" : meta.closed ? "◆ Closed Optimal"
        : meta.best_score != null ? "♛ Active Hunt" : "○ Open Hunt";
      const safeTitle = String(l.title || "").replace(/\|/g, "\\|");
      lines.push(`| \`${mission.slug}\` | \`${l.id}\` | ${safeTitle} | ${bestTxt} | ${nextTxt} | ${lbTxt} | ${holder} | ${status} |`);
    }
    lines.push("");
  }

  for (const snap of snapshots) {
    lines.push(`## ${snap.mission.title} (\`${snap.mission.slug}\`)`);
    lines.push(`*Judge: ${snap.mission.judge?.label}*`);
    if (snap.mission.impact) {
      lines.push(`*${snap.mission.impact.tier_label || snap.mission.impact.tier} · Ships to: ${snap.mission.impact.ships_to}*\n`);
    } else {
      lines.push("");
    }
    const verified = snap.lemmas.filter((l) => l.kind !== "record" && (l.status === "checked" || l.status === "refuted" || l.status === "contradiction"));
    if (!verified.length) {
      lines.push("_No closed proofs yet (see King of the Hill hunts above or open bounties on the dashboard)._\n");
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
      const activeFile = l.kind === "record" ? l.record_state?.best?.file : l.lean_file;
      const leanSource = readAllowedArtifactFile(mission, activeFile);
      const dossier = {
        lemma: l,
        leanSource,
        dropInArtifact: extractDropInArtifact(slug, l, leanSource),
        refutationSource: readAllowedArtifactFile(mission, l.kind === "record" ? l.record_state?.refuted?.file : l.refutation?.counterexample_file),
        statementSource: l.statement_file ? readMissionStatementFile(mission, l.statement_file) : null,
        relatedMessages: (snap.messages || []).filter((m) => m.lemma_id === l.id),
        relatedRuns: (snap.checker_runs || []).filter((r) => r.lemma_id === l.id),
        dependents: snap.lemmas
          .filter((o) => (o.deps || []).includes(l.id))
          .map((o) => ({ id: o.id, title: o.title, status: o.status, seal: o.seal })),
      };
      fs.writeFileSync(path.join(lDir, `${l.id}.json`), JSON.stringify(dossier), "utf8");
    }
  }

  fs.writeFileSync(path.join(dataDir, "records.json"), JSON.stringify(projectGlobalRecords(snaps, new Date().toISOString()), null, 2), "utf8");

  const proofsMd = renderMasterProofsMarkdown(snaps);
  fs.writeFileSync(path.join(DIST, "PROOFS.md"), proofsMd, "utf8");
  if (syncRootProofs) {
    fs.writeFileSync(path.join(ROOT, "PROOFS.md"), proofsMd, "utf8");
  }

  const claimsIndex = [];
  for (const snap of snaps) {
    for (const l of snap.lemmas || []) {
      if (l.kind === "record") continue;
      claimsIndex.push({
        id: l.id,
        title: l.title || l.id,
        mission: snap.mission.slug,
        mission_title: snap.mission.title,
        seal: l.seal || "open",
        status: l.status || "conjecture",
        theorem_name: l.theorem_name || "",
      });
    }
  }

  fs.writeFileSync(
    path.join(dataDir, "missions.json"),
    JSON.stringify({ missions: loadAllMissionsSummary(snaps), claims: claimsIndex, static: true, snapshot_at: new Date().toISOString() }, null, 2),
    "utf8"
  );
  console.log(`Built static GitHub Pages dashboard in dist/ (including dist/PROOFS.md) for ${slugs.length} missions: ${slugs.join(", ")}`);
}
