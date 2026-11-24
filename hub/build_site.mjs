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
 * (matches every registered claim ID including MM-rec-4x4-f2, E-rec-r55, S-rec-exp, EC-rec-*, etc.!).
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

function tsMs(iso) {
  const n = Date.parse(String(iso || ""));
  return Number.isFinite(n) ? n : 0;
}

export function synthesizeSubmissionActivity(state, diskEvents = [], limit = 160) {
  const mergedEvents = [...diskEvents];
  const mergedRuns = [...(state.checker_runs || [])];

  const seenEventIds = new Set(mergedEvents.map((e) => e?.id).filter(Boolean));
  const seenFixedEvents = new Set(
    mergedEvents.filter((e) => e?.type && e?.lemma_id).map((e) => `${e.type}:${e.lemma_id}`)
  );
  const seenRecordEvents = new Set(
    mergedEvents
      .filter((e) => e?.type && e?.lemma_id && e?.at)
      .map((e) => `${e.type}:${e.lemma_id}:${e.at}`)
  );

  const seenFixedRuns = new Set(
    mergedRuns.filter((r) => r?.lemma_id).map((r) => `${r.lemma_id}:${r.kind || "proof"}`)
  );
  const seenHashRuns = new Set(
    mergedRuns
      .filter((r) => r?.lemma_id && r?.file_hash)
      .map((r) => `${r.lemma_id}:${r.kind || "proof"}:${r.file_hash}`)
  );

  const pushEvent = (ev) => {
    if (!ev.id || seenEventIds.has(ev.id)) return;
    seenEventIds.add(ev.id);
    mergedEvents.push(ev);
  };

  for (const l of state.lemmas || []) {
    if (l.kind === "record") {
      const rs = l.record_state;
      const unit = l.record?.unit ? ` ${l.record.unit}` : "";
      for (const h of rs?.history || []) {
        if (h.state !== "accepted") continue;
        const at = h.at || (h.git_ts ? new Date(h.git_ts * 1000).toISOString() : "");
        const receipt =
          h.kind === "record" && rs.best?.file_hash === h.file_hash
            ? rs.best
            : h.kind === "record_bound" && rs.refuted?.file_hash === h.file_hash
              ? rs.refuted
              : null;
        const evKey = `checker_accepted:${l.id}:${at}`;
        if (!seenRecordEvents.has(evKey)) {
          seenRecordEvents.add(evKey);
          const detail =
            h.kind === "record"
              ? `Verified record ${h.score}${unit}`
              : `Verified optimality bound (¬ Record ${h.score})`;
          pushEvent({
            id: `ev-sub-${l.id}-${h.kind}-${h.score}-${String(h.file_hash || "").slice(0, 8)}`,
            at,
            type: "checker_accepted",
            lemma_id: l.id,
            program: l.program,
            seat: h.seat || "unknown",
            title: `${l.title} — ${detail}`,
            detail,
          });
        }
        const runKey = `${l.id}:${h.kind}:${h.file_hash || ""}`;
        if (!seenHashRuns.has(runKey)) {
          seenHashRuns.add(runKey);
          mergedRuns.push({
            id: `chk-sub-${l.id}-${h.kind}-${h.score}-${String(h.file_hash || "").slice(0, 8)}`,
            at,
            kind: h.kind,
            lemma_id: l.id,
            seat: h.seat || "unknown",
            theorem: receipt?.theorem || l.theorem_name || "",
            file: h.file || "",
            ok: true,
            duration_ms: receipt?.duration_ms ?? 0,
            axioms: receipt?.axioms || [],
            reason:
              h.kind === "record"
                ? `Verified record ${h.score}${unit}`
                : `Verified optimality bound (¬ Record ${h.score})`,
            file_hash: h.file_hash || null,
            core_hash: receipt?.core_hash || null,
          });
        }
      }
      continue;
    }

    if (l.checker?.ok) {
      const at = l.checker.checked_at || l.updated_at || "";
      if (!seenFixedEvents.has(`checker_accepted:${l.id}`)) {
        seenFixedEvents.add(`checker_accepted:${l.id}`);
        pushEvent({
          id: `ev-sub-proof-${l.id}-${String(l.checker.file_hash || "").slice(0, 8)}`,
          at,
          type: "checker_accepted",
          lemma_id: l.id,
          program: l.program,
          seat: l.checker.by_seat || "unknown",
          title: l.title,
          detail: l.checker.reason || "Verified by Judge",
        });
      }
      if (!seenFixedRuns.has(`${l.id}:proof`)) {
        seenFixedRuns.add(`${l.id}:proof`);
        mergedRuns.push({
          id: `chk-sub-proof-${l.id}-${String(l.checker.file_hash || "").slice(0, 8)}`,
          at,
          kind: "proof",
          lemma_id: l.id,
          seat: l.checker.by_seat || "unknown",
          theorem: l.theorem_name || "",
          file: l.lean_file || "",
          ok: true,
          duration_ms: l.checker.duration_ms ?? 0,
          axioms: l.checker.axioms || [],
          reason: l.checker.reason || "Verified by Judge",
          file_hash: l.checker.file_hash || null,
          core_hash: l.checker.core_hash || null,
        });
      }
    }

    if (l.refutation) {
      const at = l.refutation.at || l.updated_at || "";
      if (!seenFixedEvents.has(`claim_refuted:${l.id}`)) {
        seenFixedEvents.add(`claim_refuted:${l.id}`);
        pushEvent({
          id: `ev-sub-refute-${l.id}-${String(l.refutation.file_hash || "").slice(0, 8)}`,
          at,
          type: "claim_refuted",
          lemma_id: l.id,
          program: l.program,
          seat: l.refutation.by_seat || "unknown",
          title: l.title,
          detail: l.refutation.summary || "Judge-verified counterexample",
        });
      }
      if (!seenFixedRuns.has(`${l.id}:refutation`)) {
        seenFixedRuns.add(`${l.id}:refutation`);
        mergedRuns.push({
          id: `chk-sub-refute-${l.id}-${String(l.refutation.file_hash || "").slice(0, 8)}`,
          at,
          kind: "refutation",
          lemma_id: l.id,
          seat: l.refutation.by_seat || "unknown",
          theorem: l.refutation.theorem_name || l.refutation_theorem || "",
          file: l.refutation.counterexample_file || l.lean_file || "",
          ok: true,
          duration_ms: l.refutation.duration_ms ?? 0,
          axioms: l.refutation.axioms || [],
          reason: l.refutation.summary || "Judge-verified counterexample",
          file_hash: l.refutation.file_hash || null,
          core_hash: l.refutation.core_hash || null,
        });
      }
    }

    if (l.audit && !seenFixedEvents.has(`lemma_audited:${l.id}`)) {
      seenFixedEvents.add(`lemma_audited:${l.id}`);
      const at = l.audit.at || l.updated_at || "";
      pushEvent({
        id: `ev-sub-audit-${l.id}`,
        at,
        type: "lemma_audited",
        lemma_id: l.id,
        program: l.program,
        seat: l.audit.by_seat || "unknown",
        title: l.title,
        detail: `${l.audit.verdict || "audited"}: ${l.audit.notes || ""}`.trim(),
      });
    }
  }

  mergedEvents.sort((a, b) => tsMs(b.at) - tsMs(a.at) || String(b.id || "").localeCompare(String(a.id || "")));
  mergedRuns.sort((a, b) => tsMs(b.at) - tsMs(a.at) || String(b.id || "").localeCompare(String(a.id || "")));

  return {
    events: mergedEvents.slice(0, limit),
    checker_runs: mergedRuns,
  };
}

export function buildMissionSnapshot(mission, prSnap = null) {
  const { state } = deriveMissionState(mission.slug, { project: false });
  const diskEvents = readEvents(mission.paths.eventsFile, 160);
  const { events, checker_runs } = synthesizeSubmissionActivity(state, diskEvents, 160);
  return {
    ...projectMissionSnapshot(mission, state, prSnap),
    checker_runs,
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
    lines.push(`*Judge: ${snap.mission.judge?.label}*\n`);
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
      const dossier = {
        lemma: l,
        leanSource: readAllowedArtifactFile(mission, activeFile),
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
