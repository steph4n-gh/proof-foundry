#!/usr/bin/env node
/**
 * hub/fleet.mjs — Hardened Multi-Mission Open-Science Fleet CLI (v2).
 *
 * Upgrades from Opus 5.5 + Sol 6.2 review:
 * - Strict allowlist in `verify-pr` (only Claims/*.lean, artifacts/*, submissions/*.json) + `--files-list <path>`
 *   (zero bash filename interpolation!).
 * - Frozen-statement binding (`statement_file` + `statement_def`) passed straight to Lean 4 Judge.
 * - Re-checks state-transition guards inside writeback lock on `verify` and `refute`.
 * - `fleet next` skips claims that already have an active GitHub PR (<72h) or unmet dependencies!
 */
import fs from "node:fs";
import path from "node:path";
import {
  ROOT,
  DEFAULT_MISSION,
  loadMission,
  loadAllMissionsSummary,
  getMissionPaths,
  compileSubmissionsIntoState,
  computeTrustSeal,
} from "./missions.mjs";
import { fetchOpenPRs } from "./build_site.mjs";
import { runJudge } from "./judges/index.mjs";

function sleepMs(ms) {
  const arr = new Int32Array(new SharedArrayBuffer(4));
  Atomics.wait(arr, 0, 0, ms);
}

function withMissionLock(lockDir, fn) {
  const deadline = Date.now() + 20000;
  while (true) {
    try {
      fs.mkdirSync(lockDir);
      break;
    } catch (err) {
      if (err.code !== "EEXIST") throw err;
      try {
        const st = fs.statSync(lockDir);
        if (Date.now() - st.mtimeMs > 25000) {
          const tomb = `${lockDir}.stale.${process.pid}.${Date.now()}`;
          try {
            fs.renameSync(lockDir, tomb);
            fs.rmSync(tomb, { recursive: true, force: true });
          } catch {}
          continue;
        }
      } catch {}
      if (Date.now() > deadline) throw new Error("Timed out waiting for mission state lock");
      sleepMs(25 + Math.floor(Math.random() * 45));
    }
  }
  try {
    return fn();
  } finally {
    try {
      fs.rmSync(lockDir, { recursive: true, force: true });
    } catch {}
  }
}

function loadState(mission) {
  if (!fs.existsSync(mission.paths.stateFile)) {
    throw new Error(`State missing for mission "${mission.slug}" at ${mission.paths.stateFile}`);
  }
  return JSON.parse(fs.readFileSync(mission.paths.stateFile, "utf8"));
}

function saveState(mission, state) {
  state.meta.updated_at = new Date().toISOString();
  const statePath = mission.paths.stateFile;
  const tmp = `${statePath}.tmp.${process.pid}.${Date.now()}`;
  const fd = fs.openSync(tmp, "w");
  try {
    fs.writeSync(fd, JSON.stringify(state, null, 2) + "\n", undefined, "utf8");
    fs.fsyncSync(fd);
  } finally {
    fs.closeSync(fd);
  }
  fs.renameSync(tmp, statePath);
}

function appendEvent(mission, event) {
  const full = {
    id: `ev-${Date.now()}-${Math.random().toString(36).slice(2, 6)}`,
    at: new Date().toISOString(),
    ...event,
  };
  fs.appendFileSync(mission.paths.eventsFile, JSON.stringify(full) + "\n", "utf8");
  return full;
}

function ensureSeat(state, seatId) {
  if (!seatId) return null;
  let seat = state.seats.find((s) => s.id === seatId);
  if (!seat) {
    if (/^(donor|contrib|ext|audit)-[a-z0-9-_]{1,32}$/.test(seatId)) {
      seat = {
        id: seatId,
        name: seatId,
        role: seatId.startsWith("audit-") ? "auditor" : "donor",
        program: state.programs?.[0]?.id || "general",
        provider: "Community",
        model: seatId.startsWith("audit-") ? "Cross-Model Auditor" : "Token Donor",
        badge: seatId.startsWith("audit-") ? "AU" : "TD",
        color: "#0D9488",
        status: "working",
        current_lemma: null,
        current_whisper: "Donating tokens to open science",
        sessions: 0,
        last_seen: new Date().toISOString(),
        counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
      };
      state.seats.push(seat);
    } else {
      throw new Error(`Unknown seat: ${seatId} (community donors may use prefix donor-<handle>)`);
    }
  }
  return seat;
}

function addWhisper(state, seatId, text, lemmaId = null) {
  const seat = state.seats.find((s) => s.id === seatId);
  if (seat) {
    seat.current_whisper = text;
    seat.last_seen = new Date().toISOString();
  }
  state.whispers.unshift({
    id: `w-${Date.now()}-${Math.random().toString(36).slice(2, 5)}`,
    seat: seatId,
    lemma_id: lemmaId,
    text,
    at: new Date().toISOString(),
  });
  state.whispers = state.whispers.slice(0, 60);
}

function parseArgs(argv) {
  const [cmd, ...rest] = argv;
  const flags = {};
  for (let i = 0; i < rest.length; i++) {
    const tok = rest[i];
    if (tok.startsWith("--")) {
      const key = tok.slice(2);
      const next = rest[i + 1];
      if (next === undefined || next.startsWith("--")) {
        flags[key] = true;
      } else {
        flags[key] = next;
        i++;
      }
    }
  }
  return { cmd, flags };
}

const { cmd, flags } = parseArgs(process.argv.slice(2));
const missionSlug = String(flags.mission || process.env.FLEET_MISSION || DEFAULT_MISSION);

if (!cmd || cmd === "help") {
  console.log(`Proof Foundry Fleet CLI (v2)
Commands: missions | new | next | status | claim-add | claim | whisper | msg | verify | refute | rule-dead | audit | export-submission | compile | verify-pr | strategy-note | seat-state`);
  process.exit(0);
}

if (cmd === "missions") {
  console.log(JSON.stringify(loadAllMissionsSummary(), null, 2));
  process.exit(0);
}

if (cmd === "new") {
  const slug = String(flags.slug || "");
  if (!slug || !flags.title || !flags.question) {
    console.error("Required: --slug, --title, --question");
    process.exit(2);
  }
  const mp = getMissionPaths(slug);
  if (fs.existsSync(mp.missionFile)) {
    console.error(`Mission "${slug}" already exists.`);
    process.exit(1);
  }
  const judgeType = flags.judge === "command" ? "command" : "lean4";
  const now = new Date().toISOString();
  fs.mkdirSync(mp.submissionsDir, { recursive: true });
  fs.mkdirSync(path.join(mp.dir, "artifacts"), { recursive: true });

  const missionConfig = {
    slug,
    brand: flags.brand || `PROOF FOUNDRY · ${slug.toUpperCase()}`,
    title: flags.title,
    tagline: flags.tagline || "Open-science token-donation fleet",
    question: flags.question,
    description: flags.description || "Donate spare AI tokens to advance verifiable open science.",
    verdict: "open, accepting token donations.",
    github_repo: "steph4n-gh/proof-foundry",
    objectives: [],
    tug_of_war: { enabled: false },
    judge:
      judgeType === "lean4"
        ? {
            type: "lean4",
            label: "Lean 4.36.0 kernel · zero sorry",
            lean_dir: `missions/${slug}/lean`,
            lake_target: "MissionCore",
            core_file: `missions/${slug}/lean/MissionCore/Core.lean`,
            core_olean: `missions/${slug}/lean/.lake/build/lib/lean/MissionCore/Core.olean`,
            allowed_dirs: [`missions/${slug}/lean/MissionCore/Claims`, `missions/${slug}/lean/MissionCore/Statements`],
            allowed_extensions: [".lean"],
            allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
          }
        : {
            type: "command",
            label: flags["judge-label"] || "Deterministic Verification Harness",
            harness_file: `missions/${slug}/judge/verify.mjs`,
            command: ["node", `missions/${slug}/judge/verify.mjs`],
            allowed_dirs: [`missions/${slug}/artifacts`],
            allowed_extensions: [".mjs", ".js", ".py", ".json"],
            timeout_ms: 60000,
          },
  };

  const initState = {
    meta: { mission: slug, title: missionConfig.title, verdict: missionConfig.verdict, started_at: now, updated_at: now, sessions_total: 0, checker_runs_total: 0, checker_runs_passed: 0, strategy_note: { seat: "seat-strat-1", text: `Mission "${missionConfig.title}" initialized.`, mentions: [], at: now } },
    programs: [{ id: "main_front", key: "main", title: "Primary Frontier", aims_at: "neutral", color: "#2F6B4F", goal: "Core verifiable claims.", target_summary: "Primary milestones." }],
    seats: [{ id: "seat-strat-1", name: "Strategy Desk", role: "strategy", program: "main_front", provider: "Antigravity", model: "Gemini 4 Neon", badge: "G4", color: "#3B82F6", status: "idle", current_lemma: null, current_whisper: "Ready", sessions: 0, last_seen: now, counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 } }],
    lemmas: [],
    messages: [],
    whispers: [],
    checker_runs: [],
  };

  fs.writeFileSync(mp.missionFile, JSON.stringify(missionConfig, null, 2) + "\n");
  fs.writeFileSync(mp.stateFile, JSON.stringify(initState, null, 2) + "\n");
  fs.writeFileSync(mp.eventsFile, JSON.stringify({ id: `ev-init-${Date.now()}`, at: now, type: "fleet_started", seat: "seat-strat-1", detail: `Mission "${missionConfig.title}" scaffolded.` }) + "\n");
  console.log(JSON.stringify({ ok: true, slug }, null, 2));
  process.exit(0);
}

const mission = loadMission(missionSlug);

function writeSubmissionFile(lemma, kind, payload) {
  fs.mkdirSync(mission.paths.submissionsDir, { recursive: true });
  const hashPart = String(payload.file_hash || payload.checker?.file_hash || payload.refutation?.file_hash || payload.audit?.file_hash || Date.now()).slice(0, 10);
  const fname = `${lemma.id}.${kind}.${hashPart}.json`;
  const fpath = path.join(mission.paths.submissionsDir, fname);
  const record = {
    schema: "fleet-submission/2",
    mission: mission.slug,
    lemma_id: lemma.id,
    kind,
    at: new Date().toISOString(),
    ...payload,
  };
  fs.writeFileSync(fpath, JSON.stringify(record, null, 2) + "\n", "utf8");
  return path.relative(ROOT, fpath);
}

if (cmd === "status") {
  const state = loadState(mission);
  const counts = { checked: 0, trusted: 0, flagged: 0, in_work: 0, conjecture: 0, refuted: 0, dead: 0 };
  for (const l of state.lemmas) {
    counts[l.status] = (counts[l.status] || 0) + 1;
    const seal = computeTrustSeal(l);
    if (seal === "audited" || seal === "frozen") counts.trusted++;
    if (seal === "flagged") counts.flagged++;
  }
  console.log(JSON.stringify({ mission: mission.slug, title: mission.title, counts }, null, 2));
  process.exit(0);
}

if (cmd === "next") {
  // Compile any merged submissions first, then query open GitHub PRs to avoid collision!
  const { state } = compileSubmissionsIntoState(mission.slug);
  const prSnap = flags.offline ? { ok: false, by_claim: {} } : fetchOpenPRs(mission.github_repo);
  const nowMs = Date.now();
  const STALE_PR_MS = 72 * 3600 * 1000;
  const byId = Object.fromEntries(state.lemmas.map((l) => [l.id, l]));

  const skippedActivePr = [];
  const candidates = state.lemmas
    .filter((l) => l.status === "conjecture" && (!flags.program || l.program === flags.program))
    .filter((l) => {
      // Skip if an active PR (<72h) already targets this claim
      const prs = (prSnap.by_claim[l.id] || []).filter((p) => nowMs - new Date(p.updated_at).getTime() < STALE_PR_MS);
      if (prs.length > 0) {
        skippedActivePr.push({ id: l.id, prs: prs.map((p) => `#${p.number}`) });
        return false;
      }
      // Prefer claims whose dependencies are already checked/refuted
      return (l.deps || []).every((d) => !byId[d] || byId[d].status === "checked" || byId[d].status === "refuted");
    })
    .sort((a, b) => (b.statement_file ? 1 : 0) - (a.statement_file ? 1 : 0) || (a.rung || 99) - (b.rung || 99));

  if (!candidates.length) {
    console.log(
      JSON.stringify(
        {
          ok: true,
          mission: mission.slug,
          pr_sync_ok: prSnap.ok,
          skipped_active_prs: skippedActivePr,
          next: null,
          message: "No unclaimed open bounties right now (check skipped_active_prs or open a New Claim issue!).",
        },
        null,
        2
      )
    );
    process.exit(0);
  }
  const pick = candidates[0];
  console.log(
    JSON.stringify(
      {
        ok: true,
        mission: mission.slug,
        pr_sync_ok: prSnap.ok,
        skipped_active_prs: skippedActivePr,
        claim: pick,
        instructions: [
          `1. Read ${mission.judge?.core_file || mission.judge?.harness_file}${pick.statement_file ? ` AND frozen statement ${pick.statement_file}` : ""}`,
          `2. Write your isolated artifact in ${pick.lean_file}`,
          `3. Verify locally: node hub/fleet.mjs verify --mission ${mission.slug} --lemma ${pick.id} --seat donor-<handle> --file ${pick.lean_file} --theorem ${pick.theorem_name} --export`,
          `4. Open a PR with ONLY ${pick.lean_file} and missions/${mission.slug}/submissions/${pick.id}.*.json (never edit state.json!).`,
        ],
      },
      null,
      2
    )
  );
  process.exit(0);
}

if (cmd === "lemma-add" || cmd === "claim-add") {
  const result = withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const id = flags.id;
    if (!id || !flags.program || !flags.title) throw new Error("Required: --id, --program, --title");
    if (state.lemmas.some((l) => l.id === id)) throw new Error(`Claim ${id} already exists`);
    const prog = state.programs.find((p) => p.id === flags.program);
    if (!prog) throw new Error(`Unknown program: ${flags.program}`);
    const deps = flags.deps ? flags.deps.split(",").map((s) => s.trim()).filter(Boolean) : [];
    const defaultDir = mission.judge?.allowed_dirs?.[0] || `missions/${mission.slug}/artifacts`;
    const defaultExt = mission.judge?.type === "lean4" ? ".lean" : ".mjs";
    const lemma = {
      id,
      program: flags.program,
      title: flags.title,
      statement: flags.statement || "",
      registered_statement: flags.statement || "",
      verified_signature: null,
      statement_file: flags["statement-file"] || null,
      statement_def: flags["statement-def"] || null,
      theorem_name: flags.theorem || "",
      lean_file: flags.file || `${defaultDir}/${id.replace(/-/g, "_")}${defaultExt}`,
      status: "conjecture",
      aims_at: flags.aims || prog.aims_at || "neutral",
      deps,
      rung: flags.rung ? Number(flags.rung) : null,
      proposed_by: flags.seat || "seat-strat-1",
      claimed_by: null,
      paper_notes: flags.paper || "",
      created_at: new Date().toISOString(),
      updated_at: new Date().toISOString(),
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    };
    state.lemmas.push(lemma);
    if (flags.seat) {
      ensureSeat(state, flags.seat);
      addWhisper(state, flags.seat, `Stated bounty ${id}: ${flags.title}`, id);
    }
    saveState(mission, state);
    appendEvent(mission, { type: "lemma_stated", lemma_id: id, program: lemma.program, seat: lemma.proposed_by, title: lemma.title });
    return lemma;
  });
  console.log(JSON.stringify({ ok: true, mission: mission.slug, lemma: result }, null, 2));
  process.exit(0);
}

if (cmd === "claim") {
  const res = withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    if (!lemma) throw new Error(`Unknown claim: ${flags.lemma}`);
    if (lemma.status !== "conjecture" && lemma.status !== "in_work") {
      throw new Error(`Cannot claim ${lemma.id} (status=${lemma.status})`);
    }
    const seat = ensureSeat(state, flags.seat);
    lemma.status = "in_work";
    lemma.claimed_by = seat.id;
    lemma.updated_at = new Date().toISOString();
    seat.status = "working";
    seat.current_lemma = lemma.id;
    seat.sessions = (seat.sessions || 0) + 1;
    seat.counts.attempts = (seat.counts.attempts || 0) + 1;
    state.meta.sessions_total = (state.meta.sessions_total || 0) + 1;
    const whisper = flags.whisper || `Claimed ${lemma.id}: ${lemma.title}`;
    addWhisper(state, seat.id, whisper, lemma.id);
    saveState(mission, state);
    appendEvent(mission, { type: "attempt_started", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: lemma.title, detail: whisper });
    return { lemma_id: lemma.id, seat: seat.id, status: lemma.status };
  });
  console.log(JSON.stringify({ ok: true, ...res }, null, 2));
  process.exit(0);
}

if (cmd === "whisper") {
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    ensureSeat(state, flags.seat);
    addWhisper(state, flags.seat, flags.text || "", flags.lemma || null);
    saveState(mission, state);
  });
  console.log(JSON.stringify({ ok: true }));
  process.exit(0);
}

if (cmd === "msg") {
  const msg = withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const fromSeat = ensureSeat(state, flags.from);
    fromSeat.counts.messages = (fromSeat.counts.messages || 0) + 1;
    const entry = {
      id: `m-${Date.now()}-${Math.random().toString(36).slice(2, 5)}`,
      from: flags.from,
      to: flags.to || "all",
      kind: flags.kind || "report",
      lemma_id: flags.lemma || null,
      text: flags.text || "",
      at: new Date().toISOString(),
    };
    state.messages.unshift(entry);
    state.messages = state.messages.slice(0, 120);
    addWhisper(state, flags.from, `→ ${entry.to}: ${entry.text.slice(0, 110)}`, entry.lemma_id);
    saveState(mission, state);
    appendEvent(mission, { type: "seat_message", seat: entry.from, to: entry.to, kind: entry.kind, lemma_id: entry.lemma_id, detail: entry.text });
    return entry;
  });
  console.log(JSON.stringify({ ok: true, message: msg }, null, 2));
  process.exit(0);
}

if (cmd === "verify") {
  if (!flags.lemma || !flags.seat || !flags.file || !flags.theorem) {
    console.error("Required: --lemma --seat --file --theorem");
    process.exit(2);
  }
  let stmtMeta = { statementFile: flags["statement-file"] || null, statementDef: flags["statement-def"] || null };
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    if (!lemma) throw new Error(`Unknown claim: ${flags.lemma}`);
    if (lemma.status === "refuted" || lemma.status === "dead" || lemma.status === "contradiction") {
      throw new Error(`State guard: cannot verify ${lemma.id} (status is "${lemma.status}")`);
    }
    if (lemma.theorem_name && lemma.theorem_name !== flags.theorem) {
      throw new Error(`Binding guard: registered target is "${lemma.theorem_name}", not "${flags.theorem}"`);
    }
    if (!stmtMeta.statementFile && lemma.statement_file) {
      stmtMeta = { statementFile: lemma.statement_file, statementDef: lemma.statement_def };
    }
    const seat = ensureSeat(state, flags.seat);
    seat.status = "checking";
    seat.current_lemma = flags.lemma;
    addWhisper(state, seat.id, `Submitting ${flags.lemma} to ${mission.judge?.label || "Judge"}…`, flags.lemma);
    saveState(mission, state);
  });

  const verdict = runJudge(mission, {
    file: flags.file,
    target: flags.theorem,
    kind: "proof",
    statementFile: stmtMeta.statementFile,
    statementDef: stmtMeta.statementDef,
  });

  let exportedFile = null;
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    const seat = ensureSeat(state, flags.seat);
    const run = {
      id: `chk-${Date.now()}-${Math.random().toString(36).slice(2, 5)}`,
      at: new Date().toISOString(),
      kind: "proof",
      lemma_id: lemma.id,
      seat: seat.id,
      theorem: flags.theorem,
      file: verdict.file,
      ok: verdict.ok,
      duration_ms: verdict.duration_ms,
      axioms: verdict.axioms,
      reason: verdict.reason,
      file_hash: verdict.file_hash,
      core_hash: verdict.core_hash,
      statement_frozen: Boolean(verdict.statement_frozen),
    };
    state.checker_runs.unshift(run);
    state.checker_runs = state.checker_runs.slice(0, 100);
    state.meta.checker_runs_total = (state.meta.checker_runs_total || 0) + 1;
    if (verdict.ok) state.meta.checker_runs_passed = (state.meta.checker_runs_passed || 0) + 1;
    if (flags.paper) lemma.paper_notes = flags.paper;

    let ev;
    if (verdict.ok) {
      // Re-check transition guard inside writeback lock!
      if (lemma.status === "refuted") {
        lemma.status = "contradiction";
      } else {
        const wasChecked = lemma.status === "checked";
        lemma.status = "checked";
        if (!wasChecked) seat.counts.checked = (seat.counts.checked || 0) + 1;
      }
      lemma.lean_file = verdict.file;
      lemma.theorem_name = flags.theorem;
      if (!lemma.registered_statement) lemma.registered_statement = lemma.statement || "";
      if (verdict.signature) {
        lemma.verified_signature = verdict.signature;
        lemma.statement = verdict.signature;
      }
      lemma.checker = {
        ok: true,
        judge: verdict.judge,
        checked_at: run.at,
        duration_ms: verdict.duration_ms,
        axioms: verdict.axioms,
        lean_version: verdict.lean_version,
        file_hash: verdict.file_hash,
        core_hash: verdict.core_hash,
        statement_frozen: Boolean(verdict.statement_frozen),
        statement_hash: verdict.statement_hash || null,
        by_seat: seat.id,
      };
      lemma.updated_at = run.at;
      seat.status = "working";
      addWhisper(state, seat.id, `CHECKED ${lemma.id} in ${verdict.duration_ms}ms`, lemma.id);
      ev = { type: "checker_accepted", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: lemma.title, duration_ms: verdict.duration_ms, axioms: verdict.axioms, file_hash: verdict.file_hash };
      if (flags.export) {
        exportedFile = writeSubmissionFile(lemma, "proof", {
          file: verdict.file,
          theorem: flags.theorem,
          signature: verdict.signature,
          checker: lemma.checker,
        });
      }
    } else {
      seat.status = "working";
      addWhisper(state, seat.id, `Judge rejected ${lemma.id}: ${verdict.reason}`, lemma.id);
      ev = { type: "checker_rejected", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: lemma.title, detail: verdict.reason, duration_ms: verdict.duration_ms };
    }
    saveState(mission, state);
    appendEvent(mission, ev);
  });

  console.log(JSON.stringify({ ...verdict, exported_submission: exportedFile }, null, 2));
  process.exit(verdict.ok ? 0 : 1);
}

if (cmd === "refute") {
  if (!flags.lemma || !flags.seat || !flags.file || !flags.theorem || !flags.summary) {
    console.error("Required: --lemma --seat --file --theorem --summary");
    process.exit(2);
  }
  let stmtMeta = { statementFile: flags["statement-file"] || null, statementDef: flags["statement-def"] || null };
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    if (!lemma) throw new Error(`Unknown claim: ${flags.lemma}`);
    if (lemma.status === "checked") throw new Error(`State guard: ${lemma.id} is already CHECKED`);
    if (!stmtMeta.statementFile && lemma.statement_file) {
      stmtMeta = { statementFile: lemma.statement_file, statementDef: lemma.statement_def };
    }
    const seat = ensureSeat(state, flags.seat);
    seat.status = "checking";
    seat.current_lemma = flags.lemma;
    addWhisper(state, seat.id, `Submitting counterexample for ${flags.lemma}…`, flags.lemma);
    saveState(mission, state);
  });

  const verdict = runJudge(mission, {
    file: flags.file,
    target: flags.theorem,
    kind: "refutation",
    statementFile: stmtMeta.statementFile,
    statementDef: stmtMeta.statementDef,
  });

  let exportedFile = null;
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    const seat = ensureSeat(state, flags.seat);
    const run = {
      id: `chk-${Date.now()}-${Math.random().toString(36).slice(2, 5)}`,
      at: new Date().toISOString(),
      kind: "refutation",
      lemma_id: lemma.id,
      seat: seat.id,
      theorem: flags.theorem,
      file: verdict.file,
      ok: verdict.ok,
      duration_ms: verdict.duration_ms,
      axioms: verdict.axioms,
      reason: verdict.reason,
      file_hash: verdict.file_hash,
      core_hash: verdict.core_hash,
    };
    state.checker_runs.unshift(run);
    state.checker_runs = state.checker_runs.slice(0, 100);
    state.meta.checker_runs_total = (state.meta.checker_runs_total || 0) + 1;
    if (verdict.ok) state.meta.checker_runs_passed = (state.meta.checker_runs_passed || 0) + 1;

    let ev;
    if (verdict.ok) {
      if (lemma.status === "checked") {
        lemma.status = "contradiction";
      } else {
        const wasRef = lemma.status === "refuted";
        lemma.status = "refuted";
        if (!wasRef) seat.counts.refuted = (seat.counts.refuted || 0) + 1;
      }
      lemma.refutation = {
        by_seat: seat.id,
        summary: flags.summary,
        counterexample_file: verdict.file,
        theorem_name: flags.theorem,
        signature: verdict.signature || "",
        axioms: verdict.axioms,
        file_hash: verdict.file_hash,
        core_hash: verdict.core_hash,
        statement_frozen: Boolean(verdict.statement_frozen),
        duration_ms: verdict.duration_ms,
        at: run.at,
      };
      lemma.updated_at = run.at;
      seat.status = "working";
      addWhisper(state, seat.id, `REFUTED ${lemma.id}: ${flags.summary}`, lemma.id);
      ev = { type: "claim_refuted", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: lemma.title, detail: flags.summary, duration_ms: verdict.duration_ms, file_hash: verdict.file_hash };
      if (flags.export) {
        exportedFile = writeSubmissionFile(lemma, "refutation", { file: verdict.file, theorem: flags.theorem, refutation: lemma.refutation });
      }
    } else {
      seat.status = "working";
      addWhisper(state, seat.id, `Counterexample for ${lemma.id} rejected: ${verdict.reason}`, lemma.id);
      ev = { type: "checker_rejected", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: `Refutation on ${lemma.id}`, detail: verdict.reason, duration_ms: verdict.duration_ms };
    }
    saveState(mission, state);
    appendEvent(mission, ev);
  });

  console.log(JSON.stringify({ ...verdict, exported_submission: exportedFile }, null, 2));
  process.exit(verdict.ok ? 0 : 1);
}

if (cmd === "rule-dead") {
  if (!flags.lemma || !flags.seat || !flags.wall || !flags.reason) {
    console.error("Required: --lemma --seat --wall --reason");
    process.exit(2);
  }
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    if (!lemma) throw new Error(`Unknown claim: ${flags.lemma}`);
    if (lemma.status === "checked") throw new Error(`State guard: cannot rule CHECKED claim ${lemma.id} dead`);
    const seat = ensureSeat(state, flags.seat);
    const wasDead = lemma.status === "dead";
    lemma.status = "dead";
    lemma.epitaph = { wall: flags.wall, reason: flags.reason, by_seat: seat.id, editorial: true, at: new Date().toISOString() };
    lemma.updated_at = lemma.epitaph.at;
    if (!wasDead) seat.counts.blocked = (seat.counts.blocked || 0) + 1;
    addWhisper(state, seat.id, `Ruled ${lemma.id} DEAD — hits ${flags.wall}`, lemma.id);
    saveState(mission, state);
    appendEvent(mission, { type: "approach_dead", lemma_id: lemma.id, program: lemma.program, seat: seat.id, title: lemma.title, wall: flags.wall, detail: flags.reason });
    if (flags.export) writeSubmissionFile(lemma, "rule_dead", { epitaph: lemma.epitaph });
  });
  console.log(JSON.stringify({ ok: true }));
  process.exit(0);
}

if (cmd === "audit") {
  if (!flags.lemma || !flags.seat || !flags.verdict) {
    console.error("Required: --lemma --seat --verdict <faithful|flagged> [--notes <text>] [--model <name>]");
    process.exit(2);
  }
  let exportedFile = null;
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const lemma = state.lemmas.find((l) => l.id === flags.lemma);
    if (!lemma) throw new Error(`Unknown claim: ${flags.lemma}`);
    const authorSeat = lemma.checker?.by_seat || lemma.refutation?.by_seat || lemma.claimed_by;
    if (authorSeat && authorSeat === flags.seat) {
      throw new Error(`Independence guard: auditor "${flags.seat}" cannot audit their own proof on ${lemma.id}`);
    }
    const artifactHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
    lemma.audit = {
      status: flags.verdict,
      by_seat: flags.seat,
      by_model: flags.model || flags.seat,
      notes: flags.notes || "",
      file_hash: artifactHash,
      at: new Date().toISOString(),
    };
    saveState(mission, state);
    appendEvent(mission, { type: "lemma_audited", lemma_id: lemma.id, seat: flags.seat, detail: `${flags.verdict}: ${flags.notes || ""}` });
    if (flags.export) exportedFile = writeSubmissionFile(lemma, "audit", { audit: lemma.audit });
  });
  console.log(JSON.stringify({ ok: true, exported_submission: exportedFile }, null, 2));
  process.exit(0);
}

if (cmd === "compile") {
  const res = compileSubmissionsIntoState(mission.slug);
  console.log(JSON.stringify({ ok: true, mission: mission.slug, applied: res.applied }, null, 2));
  process.exit(0);
}

if (cmd === "verify-pr") {
  // Read changed paths safely from --files-list <file> OR --files <csv>
  let rawFiles = [];
  if (flags["files-list"]) {
    rawFiles = fs
      .readFileSync(flags["files-list"], "utf8")
      .split(/\r?\n/)
      .map((s) => s.trim())
      .filter(Boolean);
  } else if (flags.files) {
    rawFiles = String(flags.files)
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);
  }

  if (!rawFiles.length) {
    console.log(JSON.stringify({ ok: true, checked: 0, message: "No files changed." }, null, 2));
    process.exit(0);
  }

  // STRICT ALLOWLIST (Opus 5.5 security fix: never rely on a denylist!)
  const ALLOWED_PR_PATH =
    /^(missions\/[a-z0-9-_]+\/(submissions\/[A-Za-z0-9_.-]+\.json|artifacts\/[A-Za-z0-9_.-]+|lean\/[A-Za-z0-9_]+\/Claims\/[A-Za-z0-9_]+\.lean)|lean\/PnP\/Lemmas\/[A-Za-z0-9_]+\.lean)$/;

  const disallowed = rawFiles.filter((f) => !ALLOWED_PR_PATH.test(f) || f.includes(".."));
  if (disallowed.length > 0 && !flags["allow-infra"]) {
    console.log(
      JSON.stringify(
        {
          ok: false,
          reason: `PR modifies files outside the strict donor allowlist (only Claims/*.lean, artifacts/*, and submissions/*.json are allowed in donor PRs): ${disallowed.join(", ")}`,
          disallowed,
        },
        null,
        2
      )
    );
    process.exit(1);
  }

  const subFiles = rawFiles.filter((f) => /^missions\/[^/]+\/submissions\/[^/]+\.json$/.test(f));
  if (!subFiles.length) {
    console.log(JSON.stringify({ ok: false, reason: "Donor PR must include at least one exported missions/<slug>/submissions/*.json record" }, null, 2));
    process.exit(1);
  }

  const reports = [];
  let allOk = true;
  let allFrozenMatched = true;

  for (const sf of subFiles) {
    const abs = path.resolve(ROOT, sf);
    if (!fs.existsSync(abs)) continue;
    const sub = JSON.parse(fs.readFileSync(abs, "utf8"));
    const m = loadMission(sub.mission);
    const mState = loadState(m);
    const registered = mState.lemmas.find((l) => l.id === sub.lemma_id);
    if (!registered) {
      allOk = false;
      allFrozenMatched = false;
      reports.push({ submission: sf, ok: false, reason: `Unknown claim ID "${sub.lemma_id}" in mission "${m.slug}"` });
      continue;
    }

    if (sub.kind === "proof" || sub.kind === "refutation") {
      // Enforce registered theorem binding on proofs
      if (sub.kind === "proof" && registered.theorem_name && sub.theorem !== registered.theorem_name) {
        allOk = false;
        allFrozenMatched = false;
        reports.push({
          submission: sf,
          lemma_id: sub.lemma_id,
          ok: false,
          reason: `Theorem binding mismatch: expected "${registered.theorem_name}", got "${sub.theorem}"`,
        });
        continue;
      }

      const verdict = runJudge(m, {
        file: sub.file,
        target: sub.theorem,
        kind: sub.kind,
        statementFile: registered.statement_file || null,
        statementDef: registered.statement_def || null,
      });
      if (!verdict.ok) allOk = false;
      if (!verdict.statement_frozen) allFrozenMatched = false;
      reports.push({
        submission: sf,
        mission: m.slug,
        lemma_id: sub.lemma_id,
        kind: sub.kind,
        ok: verdict.ok,
        statement_frozen: Boolean(verdict.statement_frozen),
        duration_ms: verdict.duration_ms,
        axioms: verdict.axioms,
        file_hash: verdict.file_hash,
        signature: verdict.signature || "",
        reason: verdict.reason,
      });
    } else {
      // Non-proof metadata PRs (audit / rule_dead / claim_add) are NEVER auto-mergeable
      allFrozenMatched = false;
      if (!flags["allow-meta"]) {
        allOk = false;
        reports.push({
          submission: sf,
          lemma_id: sub.lemma_id,
          kind: sub.kind,
          ok: false,
          reason: `Metadata submission kind "${sub.kind}" requires maintainer review (cannot self-certify via donor PR)`,
        });
      } else {
        reports.push({ submission: sf, lemma_id: sub.lemma_id, kind: sub.kind, ok: true, reason: "Metadata validated" });
      }
    }
  }

  console.log(JSON.stringify({ ok: allOk, eligible_for_auto_merge: allOk && allFrozenMatched, checked: reports.length, reports }, null, 2));
  process.exit(allOk ? 0 : 1);
}

if (cmd === "strategy-note") {
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const seat = ensureSeat(state, flags.seat || "seat-strat-1");
    const mentions = flags.mentions ? flags.mentions.split(",").map((s) => s.trim()).filter(Boolean) : [];
    state.meta.strategy_note = { seat: seat.id, text: flags.text || "", mentions, at: new Date().toISOString() };
    addWhisper(state, seat.id, `Published strategy dispatch (${mentions.length} claims cited)`);
    saveState(mission, state);
    appendEvent(mission, { type: "strategy_update", seat: seat.id, detail: flags.text || "", mentions });
  });
  console.log(JSON.stringify({ ok: true }));
  process.exit(0);
}

if (cmd === "seat-state") {
  withMissionLock(mission.paths.lockDir, () => {
    const state = loadState(mission);
    const seat = ensureSeat(state, flags.seat);
    if (flags.status) seat.status = flags.status;
    if (flags.lemma !== undefined) seat.current_lemma = flags.lemma || null;
    if (flags.whisper) addWhisper(state, seat.id, flags.whisper, seat.current_lemma);
    seat.last_seen = new Date().toISOString();
    saveState(mission, state);
  });
  console.log(JSON.stringify({ ok: true }));
  process.exit(0);
}

console.error(`Unknown command: ${cmd}`);
process.exit(2);
