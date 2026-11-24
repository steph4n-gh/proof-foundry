import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { once } from "node:events";
import fs from "node:fs";
import net from "node:net";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { buildMissionSnapshot } from "./build_site.mjs";
import { ROOT, applySubmissionsPure, deriveMissionState, listMissionSlugs, loadAllMissionsSummary, loadMission } from "./missions.mjs";
import {
  assignSeatClaim,
  computeClaimFreshness,
  computeRecordTargets,
  isRungConquered,
  projectClaimView,
  projectGlobalRecords,
  projectMissionSnapshot,
  releaseSeatClaim,
  sha256RelFile,
  transitionClaim,
} from "./state_machine.mjs";

const at = "2026-01-01T00:00:00.000Z";
const proof = { kind: "proof", lemma_id: "C", checker: { ok: true, by_seat: "donor-a", file_hash: "proof" }, at };
const refutation = { kind: "refutation", lemma_id: "C", refutation: { by_seat: "donor-b", file_hash: "refutation" }, at };
const barrier = { kind: "rule_dead", lemma_id: "C", epitaph: { by_seat: "donor-c", wall: "Barrier" }, at };

function tempDir(t) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "proof-foundry-state-"));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function runNode(args, options = {}) {
  const result = spawnSync(process.execPath, args, { cwd: ROOT, encoding: "utf8", timeout: 20_000, ...options });
  if (result.error) throw result.error;
  return result;
}

test("opposing evidence creates a sticky contradiction in both orders", () => {
  const initial = { id: "C", status: "conjecture" };
  for (const [first, second] of [[proof, refutation], [refutation, proof]]) {
    const done = transitionClaim(initial, first).lemma;
    assert.equal(transitionClaim(done, second, { mode: "preflight" }).ok, false);
    const conflict = transitionClaim(done, second).lemma;
    assert.equal(conflict.status, "contradiction");
    assert.deepEqual(conflict.checker, proof.checker);
    assert.deepEqual(conflict.refutation, refutation.refutation);
    for (const event of [proof, refutation, barrier, { kind: "claim", seat: "donor-c" }, { kind: "record" }, { kind: "record_bound" }]) {
      const result = transitionClaim(conflict, event);
      assert.equal(result.ok, false);
      assert.deepEqual(result.lemma, conflict);
    }
    const seed = { lemmas: [conflict], seats: [] };
    assert.deepEqual(applySubmissionsPure(seed, [proof, refutation, barrier]).state.lemmas, [conflict]);
  }
  assert.deepEqual(initial, { id: "C", status: "conjecture" });
});

test("editorial barriers cannot replace a verified or contradictory verdict", () => {
  for (const status of ["checked", "refuted", "contradiction"]) {
    const lemma = { id: "C", status };
    const result = transitionClaim(lemma, barrier);
    assert.equal(result.ok, false);
    assert.match(result.reason, new RegExp(status));
    assert.deepEqual(applySubmissionsPure({ lemmas: [lemma], seats: [] }, [barrier]).state.lemmas, [lemma]);
  }
  const initial = { id: "C", status: "in_work", claimed_by: "donor-a" };
  const seed = { lemmas: [initial], seats: [{ id: "donor-a", status: "working", current_lemma: "C" }] };
  const closed = applySubmissionsPure(seed, [barrier]).state;
  assert.equal(closed.lemmas[0].status, "dead");
  assert.equal(closed.lemmas[0].claimed_by, null);
  assert.equal(closed.seats[0].status, "idle");
  assert.equal(closed.seats[0].current_lemma, null);
});

test("seat reassignment releases both old links and maintains one owner per claim", () => {
  const seed = {
    lemmas: [
      { id: "C", status: "in_work", claimed_by: "donor-a" },
      { id: "D", status: "in_work", claimed_by: "donor-b" },
    ],
    seats: [
      { id: "donor-a", current_lemma: "C", status: "checking" },
      { id: "donor-b", current_lemma: "D", status: "working" },
    ],
  };
  const original = structuredClone(seed);
  const state = assignSeatClaim(seed, "donor-a", "D");
  assert.deepEqual(seed, original);
  assert.deepEqual(state.lemmas.map(({ id, status, claimed_by }) => [id, status, claimed_by]), [
    ["C", "conjecture", null],
    ["D", "in_work", "donor-a"],
  ]);
  assert.deepEqual(state.seats, [
    { id: "donor-a", current_lemma: "D", status: "working" },
    { id: "donor-b", current_lemma: null, status: "idle" },
  ]);

  const released = releaseSeatClaim(state, "donor-a");
  assert.ok(released.seats.every((seat) => seat.current_lemma === null));
  assert.ok(released.lemmas.every((lemma) => lemma.status === "conjecture" && lemma.claimed_by === null));

  const shared = { ...seed, seats: seed.seats.map((seat) => ({ ...seat, current_lemma: "C" })) };
  const oneOwner = releaseSeatClaim(shared, "donor-a");
  assert.equal(oneOwner.lemmas[0].status, "in_work");
  assert.equal(oneOwner.lemmas[0].claimed_by, "donor-b");
  assert.equal(oneOwner.lemmas[1].status, "in_work");
  assert.throws(() => assignSeatClaim(seed, "donor-a", "absent"), /Unknown claim/);
  assert.throws(() => assignSeatClaim(seed, "absent", "D"), /Unknown seat/);
});

test("freshness checks both frozen statements and Core or harness receipts", (t) => {
  const dir = tempDir(t);
  const statement = path.join(dir, "statement.lean");
  const core = path.join(dir, "core.lean");
  fs.writeFileSync(statement, "original statement");
  fs.writeFileSync(core, "original core");

  const receipt = { statement_hash: sha256RelFile(statement), core_hash: sha256RelFile(core), ok: true, statement_frozen: true };
  const fixed = { id: "C", status: "checked", statement_file: statement, checker: receipt };
  const record = {
    id: "R", kind: "record", status: "conjecture", statement_file: statement,
    record_state: { best: { ...receipt, score: 5 }, history: [{ state: "accepted" }] },
  };
  const fixedMission = { slug: "test", judge: { core_file: core } };
  const recordMission = { slug: "test", judge: { harness_file: core } };
  assert.equal(computeClaimFreshness(fixedMission, fixed), "fresh");
  assert.equal(computeClaimFreshness(recordMission, record), "fresh");
  const boundOnly = { ...record, record_state: { refuted: receipt } };
  assert.equal(computeClaimFreshness(recordMission, boundOnly), "fresh");

  fs.appendFileSync(core, "\nnew Core definitions");
  const refreshedRecord = projectClaimView(recordMission, record);
  const refreshedFixed = projectClaimView(fixedMission, fixed);
  assert.equal(computeClaimFreshness(fixedMission, fixed), "stale_core");
  assert.equal(refreshedFixed.seal, "stale");
  assert.equal(isRungConquered(refreshedFixed), false);
  assert.equal(refreshedRecord.freshness, "stale_core");
  assert.equal(isRungConquered(refreshedRecord, "record_any"), false);
  assert.equal(refreshedRecord.record_meta.best_score, 5);
  assert.deepEqual(refreshedRecord.record_state.history, [{ state: "accepted" }]);
  assert.equal(computeClaimFreshness(recordMission, boundOnly), "stale_core");

  // Snapshot counts & latest_verified exclude stale_core claims
  const snap = projectMissionSnapshot(fixedMission, { meta: {}, programs: [], seats: [], lemmas: [fixed] }, []);
  assert.equal(snap.counts.trusted, 0);
  assert.equal(snap.counts.frozen_matched, 0);
  assert.equal(projectGlobalRecords([snap], at).totals.trusted_proofs, 0);
  assert.equal(projectGlobalRecords([snap], at).latest_verified, null);

  fs.appendFileSync(statement, "\nstatement edit");
  assert.equal(computeClaimFreshness(fixedMission, fixed), "stale_statement");
  assert.equal(computeClaimFreshness(recordMission, record), "stale_statement");
  assert.equal(computeClaimFreshness(recordMission, boundOnly), "stale_statement");

  const targets = computeRecordTargets("test", record, "record", 5);
  const derived = applySubmissionsPure({
    lemmas: [{ ...record, record: { start_target: 6 } }], seats: [],
  }, [{
    kind: "record", lemma_id: "R", score: 5, file: targets.artifactFile,
    theorem: targets.theoremName, checker: receipt, at,
  }], {
    missionSlug: "test",
    currentHashes: { coreHash: sha256RelFile(core), statementHashes: { [statement]: sha256RelFile(statement) } },
  }).state.lemmas[0];
  assert.equal(derived.record_state.best, null);
  assert.equal(projectClaimView(recordMission, derived).freshness, "stale_statement");
});

test("later record receipts cannot replace the results that contradicted each other", () => {
  const lemma = {
    id: "R", kind: "record", status: "conjecture", statement_file: "record.lean",
    record: { direction: "min", start_target: 10, bound_floor: 0 },
  };
  const events = [["record", 8], ["record_bound", 8], ["record", 6], ["record_bound", 9]].map(([kind, score]) => {
    const targets = computeRecordTargets("test", lemma, kind, score);
    return {
      kind, score, lemma_id: "R", _sub_file: targets.submissionBasename,
      file: targets.artifactFile, theorem: targets.theoremName,
      checker: { ok: true, statement_hash: "statement", core_hash: "core" },
    };
  });
  const ctx = {
    missionSlug: "test",
    gitAddedTs: new Map(events.map((event, index) => [event._sub_file, index + 1])),
    currentHashes: { statementHashes: { "record.lean": "statement" }, coreHash: "core" },
  };
  const state = applySubmissionsPure({ lemmas: [lemma], seats: [] }, events, ctx).state;
  const result = state.lemmas[0];
  assert.equal(result.status, "contradiction");
  assert.equal(result.record_state.best.score, 8);
  assert.equal(result.record_state.refuted.score, 8);
  assert.deepEqual(result.record_state.points_by_seat, {});
  assert.equal(result.record_state.history.length, 4);
  assert.deepEqual(applySubmissionsPure(state, events, ctx).state.lemmas, state.lemmas);
});

test("claim views project PR checks, hash-bound seals, and record actions", () => {
  const mission = { slug: "test" };
  const lemma = { id: "C", status: "conjecture" };
  for (const [checkStates, expected] of [
    [[], "none"], [["pending"], "open"], [[undefined], "open"],
    [["needs_fix", "pending"], "needs_fix"], [["passing", "needs_fix"], "passing"],
  ]) {
    const open_prs = checkStates.map((check_state) => ({ check_state }));
    const view = projectClaimView(mission, { ...lemma, open_prs });
    assert.equal(view.pr_state, expected);
    assert.deepEqual(view.actions, { can_attempt: true, can_bound: false, can_refute: true, can_audit: false, reason: null });
  }
  const checked = { ...lemma, status: "checked", checker: proof.checker, audit: { status: "flagged", file_hash: "old-proof" } };
  assert.equal(projectClaimView(mission, checked).seal, "provisional");
  const audited = projectClaimView(mission, { ...checked, audit: { status: "faithful", file_hash: "proof" } });
  assert.equal(audited.seal, "audited");
  assert.equal(audited.actions.can_audit, true);
  assert.equal(audited.actions.can_attempt, false);

  for (const [direction, op, start_target, best, bound_floor, literature, proven, gap] of [
    ["min", "≤", 30, 28, 23, 24, 25, 3],
    ["max", "≥", 256, 258, 341, 340, 300, 42],
  ]) {
    const record = {
      id: "R", kind: "record", status: "conjecture",
      record: { direction, start_target, bound_floor, literature_lower_bound: 24, literature_upper_bound: 340 },
    };
    const open = projectClaimView(mission, record);
    assert.equal(open.record_meta.op, op);
    assert.equal(open.record_meta.gap, Math.abs(start_target - literature));
    assert.equal(open.record_meta.literature_bound, literature);
    assert.equal(open.record_meta.next_target, start_target);
    assert.equal(open.actions.can_bound, true);
    assert.equal(projectClaimView(mission, { ...record, record: { ...record.record, allow_bound: false } }).actions.can_bound, false);

    record.record_state = { best: { score: best }, refuted: { inclusive_bound: proven } };
    const improved = projectClaimView(mission, record);
    assert.equal(improved.record_meta.gap, gap);
    assert.equal(improved.record_meta.proven_bound, proven);

    record.record_state.closed = true;
    const closed = projectClaimView(mission, record);
    assert.equal(closed.record_meta.gap, 0);
    assert.equal(closed.record_meta.next_target, null);
    assert.equal(closed.seal, "frozen");
    assert.equal(closed.actions.can_bound, false);
    assert.equal(closed.actions.can_attempt, false);

    record.record_state.contradiction = true;
    const conflict = projectClaimView(mission, record);
    assert.equal(conflict.record_meta.contradiction, true);
    assert.equal(conflict.record_meta.closed, false);
    assert.equal(conflict.seal, "contradiction");
    assert.equal(conflict.actions.can_attempt, false);
  }
});

test("CLI rejects lifecycle conflicts and moves actual seat claims", (t) => {
  const dir = tempDir(t);
  fs.cpSync(path.join(ROOT, "hub"), path.join(dir, "hub"), { recursive: true });
  const missionDir = path.join(dir, "missions/test");
  const submissionsDir = path.join(missionDir, "submissions");
  fs.mkdirSync(submissionsDir, { recursive: true });
  const science = loadMission("verified-science-kernels");
  fs.cpSync(science.paths.dir, path.join(dir, "missions", science.slug), { recursive: true });
  const { judge } = science;
  fs.writeFileSync(path.join(missionDir, "mission.json"), JSON.stringify({ title: "Test", judge }));
  const stateFile = path.join(missionDir, "state.json");
  const state = {
    meta: {}, whispers: [], checker_runs: [],
    seats: [
      { id: "donor-a", status: "working", current_lemma: "A", counts: {} },
      { id: "donor-b", status: "working", current_lemma: "B", counts: {} },
    ],
    lemmas: [
      { id: "A", status: "in_work", claimed_by: "donor-a" },
      { id: "B", status: "in_work", claimed_by: "donor-b" },
      { id: "C", status: "conjecture" },
      { id: "D", status: "refuted" },
      { id: "E", status: "contradiction" },
      { id: "R", kind: "record", status: "contradiction" },
    ],
  };
  fs.writeFileSync(stateFile, JSON.stringify(state));
  fs.writeFileSync(path.join(submissionsDir, "C.proof.json"), JSON.stringify(proof));
  const cli = (command, id, ...args) => runNode(
    ["hub/fleet.mjs", command, "--mission", "test", "--seat", "donor-a", "--lemma", id, ...args], { cwd: dir },
  );

  for (const [id, status] of [["C", "checked"], ["D", "refuted"], ["E", "contradiction"]]) {
    const result = cli("rule-dead", id, "--wall", "Barrier", "--reason", "No");
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, new RegExp(status));
  }
  for (const command of ["claim", "verify", "refute", "record", "record-bound"]) {
    const id = command.startsWith("record") ? "R" : "E";
    const result = cli(command, id, "--file", "no-such-file", "--theorem", "Test.claim", "--summary", "Test", "--score", "3", "--force-judge");
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /status is "contradiction"/);
  }
  assert.deepEqual(JSON.parse(fs.readFileSync(stateFile, "utf8")), state);

  const result = cli("claim", "B");
  assert.equal(result.status, 0, result.stderr);
  const moved = JSON.parse(fs.readFileSync(stateFile, "utf8"));
  assert.deepEqual(moved.seats.map((s) => s.current_lemma), ["B", null]);
  assert.deepEqual(moved.lemmas.slice(0, 2).map((l) => [l.status, l.claimed_by]), [
    ["conjecture", null], ["in_work", "donor-a"],
  ]);

  const artifact = `missions/${science.slug}/artifacts/S_num_001.mjs`;
  const verified = cli("verify", "B", "--file", artifact, "--theorem", "kahan_compensated_sum", "--export");
  assert.equal(verified.status, 0, verified.stderr || verified.stdout);
  const persisted = JSON.parse(fs.readFileSync(stateFile, "utf8"));
  const checked = persisted.lemmas.find((lemma) => lemma.id === "B");
  const { exported_submission } = JSON.parse(verified.stdout);
  const submission = JSON.parse(fs.readFileSync(path.join(dir, exported_submission), "utf8"));
  assert.equal(checked.status, "checked");
  assert.equal(checked.claimed_by, null);
  assert.equal(checked.checker.file_hash, sha256RelFile(artifact));
  assert.deepEqual(checked.checker, submission.checker);
  assert.ok(persisted.seats.every((seat) => seat.current_lemma == null && seat.status === "idle"));
});

test("global records project all missions and live hunts", () => {
  const slugs = listMissionSlugs();
  const snapshots = slugs.map((slug) => {
    const mission = loadMission(slug);
    const snap = buildMissionSnapshot(mission);
    return snap;
  });
  const expectedRecords = snapshots.reduce((sum, s) => sum + s.lemmas.filter((l) => l.kind === "record").length, 0);
  const records = projectGlobalRecords(snapshots, at);
  assert.equal(records.generated_at, at);
  assert.equal(records.totals.missions, slugs.length);
  assert.ok(slugs.length >= 9, `expected >= 9 missions, got ${slugs.length}`);
  assert.equal(records.records.length, expectedRecords);
  assert.ok(expectedRecords >= 35, `expected >= 35 record hunts, got ${expectedRecords}`);
  assert.equal(records.totals.records_active + records.totals.records_closed, expectedRecords);
  assert.ok(records.totals.trusted_proofs > 0);
  assert.ok(records.latest_verified?.file);
  assert.ok(records.latest_verified?.at);
  assert.equal(new Set(records.records.map((r) => `${r.mission}/${r.id}`)).size, expectedRecords);
  const min = records.records.find((r) => r.id === "SN-rec-013");
  assert.equal(min.literature_bound, 43);
  assert.equal(min.gap, min.closed ? 0 : Math.max(0, (min.best_score ?? min.start_target) - (min.proven_bound ?? min.literature_bound)));
  const max = records.records.find((r) => r.id === "EC-rec-17-6");
  assert.equal(max.literature_bound, 340);
  assert.equal(max.gap, max.closed ? 0 : Math.max(0, (max.proven_bound ?? max.literature_bound) - (max.best_score ?? max.start_target)));

  const missions = loadAllMissionsSummary(snapshots);
  assert.equal(missions.length, slugs.length);
  for (const mission of missions) {
    assert.ok(mission.description);
    assert.ok(mission.impact?.tier && mission.impact?.ships_to, `mission ${mission.slug} missing impact metadata`);
    assert.equal(mission.objectives_detail.length, mission.objectives.total);
    for (const objective of mission.objectives_detail) {
      assert.ok(objective.id && objective.title && objective.tier);
      assert.ok(objective.rungs.every((r) => r.id && r.seal && typeof r.conquered === "boolean"));
      assert.equal(objective.conquered, objective.rungs.length > 0 && objective.rungs.every((r) => r.conquered));
    }
  }
});

test("static records, live API and SSE share the projected schema", { timeout: 30_000 }, async (t) => {
  const dir = tempDir(t);
  const repo = "sorting-networks";
  const [passing, failed, pending] = [
    { number: 11, claim: "SN-rec-013", statusCheckRollup: [{ conclusion: "SUCCESS" }, { state: "SUCCESS" }] },
    { number: 12, claim: "SN-001", statusCheckRollup: [{ state: "PENDING" }, { conclusion: "FAILURE" }] },
    { number: 13, claim: "SN-002" },
  ];
  const prs = [passing, failed, pending].map(({ claim, ...pr }) => ({
    ...pr,
    files: [{ path: `missions/${repo}/submissions/${claim}.proof.test.json` }],
    title: claim,
    url: `https://example.test/pull/${pr.number}`,
    updatedAt: at,
  }));
  const fixture = path.join(dir, "prs.json");
  fs.writeFileSync(fixture, JSON.stringify(prs));
  const gh = path.join(dir, "gh");
  fs.writeFileSync(gh, `#!/bin/sh
case "$*" in
  *statusCheckRollup*) cat "$PF_TEST_PR_FIXTURE" ;;
  *) exit 1 ;;
esac
`, { mode: 0o755 });
  const env = { ...process.env, PATH: `${dir}${path.delimiter}${process.env.PATH}`, PF_TEST_PR_FIXTURE: fixture };

  const missionStateFiles = listMissionSlugs().map((slug) => loadMission(slug).paths.stateFile);
  const prior = missionStateFiles.map((file) => fs.readFileSync(file, "utf8"));
  const build = runNode(["hub/build_site.mjs"], { env });
  assert.equal(build.status, 0, build.stderr);
  assert.deepEqual(missionStateFiles.map((file) => fs.readFileSync(file, "utf8")), prior);
  const staticRecords = JSON.parse(fs.readFileSync(path.join(ROOT, "dist/data/records.json"), "utf8"));
  const staticState = JSON.parse(fs.readFileSync(path.join(ROOT, `dist/data/${repo}/state.json`), "utf8"));

  const server = spawn(process.execPath, ["web/server.mjs"], { cwd: ROOT, env: { ...env, PORT: "0" }, stdio: ["ignore", "pipe", "pipe"] });
  const serverExit = once(server, "exit");
  t.after(async () => {
    server.kill();
    await serverExit;
  });
  const [started] = await once(server.stdout, "data", { signal: AbortSignal.timeout(5000) });
  const address = started.toString().match(/http:\/\/127\.0\.0\.1:\d+/)?.[0];
  assert.ok(address, started.toString());

  const response = await fetch(`${address}/api/records`, { signal: AbortSignal.timeout(5000) });
  assert.equal(response.status, 200);
  assert.match(response.headers.get("content-type"), /application\/json/);
  const { generated_at: liveAt, ...liveRecords } = await response.json();
  const { generated_at: staticAt, ...siteRecords } = staticRecords;
  assert.ok(Number.isFinite(Date.parse(liveAt)) && Number.isFinite(Date.parse(staticAt)));
  assert.deepEqual(liveRecords, siteRecords);
  assert.ok(liveRecords.records.length >= 37, `expected >= 37 live records, got ${liveRecords.records.length}`);
  assert.equal(liveRecords.records.find((r) => r.id === passing.claim).open_prs[0].check_state, "passing");

  async function json(url) {
    const result = await fetch(`${address}${url}`, { signal: AbortSignal.timeout(5000) });
    assert.equal(result.status, 200);
    return result.json();
  }
  const liveState = await json(`/api/missions/${repo}/state`);
  const legacyState = await json(`/api/state?mission=${repo}`);
  assert.equal(liveState.mission.slug, repo);
  assert.deepEqual(liveState.lemmas, staticState.lemmas);
  assert.deepEqual(liveState.lemmas, legacyState.lemmas);
  for (const [pr, state, check] of [
    [passing, "passing", "passing"], [failed, "needs_fix", "needs_fix"], [pending, "open", "pending"],
  ]) {
    const lemma = liveState.lemmas.find((l) => l.id === pr.claim);
    assert.equal(lemma.pr_state, state);
    assert.equal(lemma.freshness, "fresh");
    assert.equal(lemma.open_prs[0].check_state, check);
    assert.equal(typeof lemma.actions.can_attempt, "boolean");
    assert.equal(typeof lemma.seal, "string");
    if (lemma.kind === "record") assert.equal(lemma.record_meta.direction, "min");
  }
  assert.equal((await fetch(`${address}/api/missions/missing/state`)).status, 404);

  const stream = await fetch(`${address}/api/stream?mission=${repo}`, { signal: AbortSignal.timeout(5000) });
  assert.match(stream.headers.get("content-type"), /text\/event-stream/);
  const reader = stream.body.getReader();
  const decoder = new TextDecoder();
  let frame = "";
  try {
    while (!frame.includes("\n\n")) {
      const { value, done } = await reader.read();
      assert.equal(done, false);
      frame += decoder.decode(value, { stream: true });
    }
  } finally {
    await reader.cancel();
  }
  assert.match(frame, /^event: snapshot\ndata: /);
  const sseSnapshot = JSON.parse(frame.split("\n")[1].slice("data: ".length));
  assert.deepEqual(sseSnapshot.lemmas, liveState.lemmas);
});

test("fleet next supports --mission all, --exclude, --exclude-file, ranking, PR filtering, and clean errors", (t) => {
  // Compute expected open eligible count dynamically from mission state (never hardcoded)
  let expectedTotal = 0;
  for (const slug of listMissionSlugs()) {
    const st = deriveMissionState(slug).state;
    const byId = Object.fromEntries(st.lemmas.map((l) => [l.id, l]));
    for (const l of st.lemmas) {
      const open = l.kind === "record" ? !l.record_state?.closed && !l.record_state?.contradiction : l.status === "conjecture";
      if (!open) continue;
      const depsOk = (l.deps || []).every((d) => !byId[d] || byId[d].status === "checked" || byId[d].status === "refuted" || byId[d].record_state?.best);
      if (depsOk) expectedTotal++;
    }
  }

  // Snapshot every state.json hash before running `next` to verify zero mutation
  const stateFiles = listMissionSlugs().map((slug) => loadMission(slug).paths.stateFile);
  const hashesBefore = stateFiles.map((f) => sha256RelFile(f));

  const first = runNode(["hub/fleet.mjs", "next", "--mission", "all", "--offline"]);
  assert.equal(first.status, 0, first.stderr);
  const p1 = JSON.parse(first.stdout);
  assert.equal(p1.ok, true);
  assert.equal(p1.scope, "all");
  assert.ok(p1.mission && p1.claim?.id);
  assert.equal(p1.remaining_count, expectedTotal);
  assert.ok(p1.claim.kind !== "record" && p1.claim.statement_file, "frozen fixed bounty ranks first");
  assert.ok(Array.isArray(p1.instructions) && p1.instructions.length >= 5);
  assert.match(p1.instructions[0], /git checkout -B /);
  assert.match(p1.instructions[4], /git restore --worktree --staged/);

  // Uppercase ALL + bare `--exclude` (no value) treated cleanly as empty exclusion list
  const bareEx = runNode(["hub/fleet.mjs", "next", "--mission", "ALL", "--offline", "--exclude"]);
  assert.equal(bareEx.status, 0, bareEx.stderr);
  const pb = JSON.parse(bareEx.stdout);
  assert.deepEqual(pb.excluded, []);
  assert.equal(pb.claim.id, p1.claim.id);

  // Comma-separated `--exclude` and scoped `slug/ID` exclusion
  const second = runNode(["hub/fleet.mjs", "next", "--mission", "all", "--offline", "--exclude", p1.claim.id]);
  assert.equal(second.status, 0, second.stderr);
  const p2 = JSON.parse(second.stdout);
  assert.equal(p2.ok, true);
  assert.ok(p2.claim?.id && p2.claim.id !== p1.claim.id);
  assert.equal(p2.remaining_count, p1.remaining_count - 1);
  assert.deepEqual(p2.excluded, [p1.claim.id]);

  const scoped = runNode(["hub/fleet.mjs", "next", "--mission", "all", "--offline", "--exclude", `${p1.mission}/${p1.claim.id}`]);
  assert.equal(scoped.status, 0, scoped.stderr);
  assert.notEqual(JSON.parse(scoped.stdout).claim.id, p1.claim.id);

  // `--exclude-file` skips newline/comma-listed IDs and ignores comments
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pf-next-test-"));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const exFile = path.join(dir, "done.txt");
  fs.writeFileSync(exFile, `# session log\n${p1.claim.id}\n${p2.claim.id}\n`, "utf8");
  const fromFile = runNode(["hub/fleet.mjs", "next", "--mission", "all", "--offline", "--exclude-file", exFile]);
  assert.equal(fromFile.status, 0, fromFile.stderr);
  const pf = JSON.parse(fromFile.stdout);
  assert.notEqual(pf.claim.id, p1.claim.id);
  assert.notEqual(pf.claim.id, p2.claim.id);
  assert.equal(pf.remaining_count, p1.remaining_count - 2);

  // `--program` works with `--mission all` (e.g. only record_hunt across missions)
  const progAll = runNode(["hub/fleet.mjs", "next", "--mission", "all", "--program", "record_hunt", "--offline"]);
  assert.equal(progAll.status, 0, progAll.stderr);
  const pp = JSON.parse(progAll.stdout);
  assert.equal(pp.claim.program, "record_hunt");
  assert.equal(pp.claim.kind, "record");

  // Ranking + open-PR handling via fake `gh` stub:
  // Dynamically pick an actually open fixed claim and an open KotH hunt so solved bounties never break this test.
  const snAll = deriveMissionState("sorting-networks").state.lemmas;
  const snById = Object.fromEntries(snAll.map((l) => [l.id, l]));
  const openFixed = snAll.find(
    (l) =>
      l.kind !== "record" &&
      l.status === "conjecture" &&
      (l.deps || []).every((d) => !snById[d] || snById[d].status === "checked" || snById[d].status === "refuted")
  );
  const openRecs = snAll.filter((l) => l.kind === "record" && !l.record_state?.closed && !l.record_state?.contradiction);
  assert.ok(openFixed && openRecs.length >= 2, "sorting-networks has an open fixed claim and at least two open KotH hunts");
  const openRec = openRecs[0];
  const binDir = path.join(dir, "bin");
  fs.mkdirSync(binDir, { recursive: true });
  const fakeGh = path.join(binDir, "gh");
  const fakePrs = [
    { number: 501, title: `${openFixed.id} witness`, url: "https://example.test/501", headRefName: `donor/${openFixed.id.toLowerCase()}`, updatedAt: new Date().toISOString(), statusCheckRollup: [] },
    { number: 502, title: `${openRec.id} record attempt`, url: "https://example.test/502", headRefName: `donor/${openRec.id.toLowerCase()}-s46`, updatedAt: new Date().toISOString(), statusCheckRollup: [] },
  ];
  fs.writeFileSync(fakeGh, `#!/bin/sh\nprintf '%s\\n' '${JSON.stringify(fakePrs)}'\n`, { mode: 0o755 });
  const ghEnv = { ...process.env, PATH: `${binDir}${path.delimiter}${process.env.PATH}` };

  const snWithPr = runNode(["hub/fleet.mjs", "next", "--mission", "sorting-networks"], { env: ghEnv });
  assert.equal(snWithPr.status, 0, snWithPr.stderr);
  const snp = JSON.parse(snWithPr.stdout);
  assert.equal(snp.pr_sync_ok, true);
  assert.ok(snp.skipped_active_prs.some((x) => x.id === openFixed.id), "fixed claim with open PR skipped");
  assert.ok(snp.active_record_prs.some((x) => x.id === openRec.id), "KotH hunt with open PR reported");
  assert.notEqual(snp.claim.id, openFixed.id);

  // Exclude all fixed claims in sorting-networks AND all other KotH hunts except openRec -> openRec STILL served!
  const exExceptRec = snAll.filter((l) => l.id !== openRec.id).map((l) => l.id).join(",");
  const recServed = runNode(["hub/fleet.mjs", "next", "--mission", "sorting-networks", "--exclude", exExceptRec], { env: ghEnv });
  assert.equal(recServed.status, 0, recServed.stderr);
  const rps = JSON.parse(recServed.stdout);
  assert.equal(rps.claim.id, openRec.id);
  assert.ok(rps.active_record_prs.some((x) => x.id === openRec.id));

  // Exclude only fixed claims in sorting-networks -> unclaimed KotH hunt WITHOUT open PR ranks ahead of openRec (active PR)
  const exFixedOnly = snAll.filter((l) => l.kind !== "record").map((l) => l.id).join(",");
  const recRanked = runNode(["hub/fleet.mjs", "next", "--mission", "sorting-networks", "--exclude", exFixedOnly], { env: ghEnv });
  assert.equal(recRanked.status, 0, recRanked.stderr);
  assert.notEqual(JSON.parse(recRanked.stdout).claim.id, openRec.id, "uncontested KotH hunt ranks ahead of contested KotH hunt");

  // Clean exhaustion
  const allSortNetIds = snAll.map((l) => l.id).join(",");
  const exhausted = runNode(["hub/fleet.mjs", "next", "--mission", "sorting-networks", "--offline", "--exclude", allSortNetIds]);
  assert.equal(exhausted.status, 0, exhausted.stderr);
  const pe = JSON.parse(exhausted.stdout);
  assert.equal(pe.ok, true);
  assert.equal(pe.claim, null);
  assert.equal(pe.next, null);
  assert.equal(pe.remaining_count, 0);

  // Clean JSON errors for invalid/missing `--mission` and missing `--exclude-file`
  for (const args of [
    ["hub/fleet.mjs", "next", "--mission", "nope", "--offline"],
    ["hub/fleet.mjs", "next", "--mission", "../escape", "--offline"],
    ["hub/fleet.mjs", "next", "--mission", "--offline"],
    ["hub/fleet.mjs", "next", "--mission", "all", "--offline", "--exclude-file", path.join(dir, "does-not-exist.txt")],
  ]) {
    const bad = runNode(args);
    assert.equal(bad.status, 1);
    const body = JSON.parse(bad.stdout);
    assert.equal(body.ok, false);
    assert.ok(typeof body.error === "string" && body.error.length > 0);
  }

  // `next` never mutated any tracked state.json
  assert.deepEqual(stateFiles.map((f) => sha256RelFile(f)), hashesBefore);
});

test("direct replay transitionClaim enforces top-level contradiction guard before transitionRecord (P3-4)", () => {
  const lemma = {
    id: "R",
    kind: "record",
    status: "contradiction",
    statement_file: "record.lean",
    record: { direction: "min", start_target: 10, bound_floor: 0 },
    record_state: { direction: "min", best: null, refuted: null, next_target: 10, closed: false, contradiction: false, history: [], points_by_seat: {} },
  };
  const targets = computeRecordTargets("test", lemma, "record", 8);
  const ev = {
    kind: "record",
    score: 8,
    lemma_id: "R",
    _sub_file: targets.submissionBasename,
    file: targets.artifactFile,
    theorem: targets.theoremName,
    checker: { ok: true, statement_hash: "S1", core_hash: "C1", by_seat: "donor-a" },
  };
  const res = transitionClaim(lemma, ev, { mode: "replay", missionSlug: "test", statementHash: "S1", coreHash: "C1" });
  assert.equal(res.ok, false);
  assert.match(res.reason, /status is "contradiction"/);
  assert.deepEqual(res.lemma, lemma);
});

test("web server rejects missing Host, supports IPv6 [::1]:port, and blocks symlinks in web/public (P3-1/P3-2)", { timeout: 15_000 }, async (t) => {
  const server = spawn(process.execPath, ["web/server.mjs"], { cwd: ROOT, env: { ...process.env, PORT: "0" }, stdio: ["ignore", "pipe", "pipe"] });
  const serverExit = once(server, "exit");
  t.after(async () => {
    server.kill();
    await serverExit;
  });
  const [started] = await once(server.stdout, "data", { signal: AbortSignal.timeout(5000) });
  const port = Number(started.toString().match(/http:\/\/127\.0\.0\.1:(\d+)/)?.[1]);
  assert.ok(Number.isInteger(port) && port > 0, started.toString());

  async function rawHttp(rawReq) {
    return new Promise((resolve, reject) => {
      const sock = net.createConnection({ host: "127.0.0.1", port }, () => sock.write(rawReq));
      let data = "";
      sock.setEncoding("utf8");
      sock.on("data", (chunk) => { data += chunk; });
      sock.on("end", () => resolve(data));
      sock.on("error", reject);
      sock.setTimeout(3000, () => { sock.destroy(); reject(new Error("rawHttp timeout")); });
    });
  }

  // Missing Host header on HTTP/1.0 -> 403 Forbidden (fail closed!)
  const noHost = await rawHttp("GET /api/records HTTP/1.0\r\nConnection: close\r\n\r\n");
  assert.match(noHost, /^HTTP\/1\.1 403 /);

  // Non-loopback Host header -> 403 Forbidden
  const evilHost = await rawHttp("GET /api/records HTTP/1.1\r\nHost: evil.example:443\r\nConnection: close\r\n\r\n");
  assert.match(evilHost, /^HTTP\/1\.1 403 /);

  // Bracketed IPv6 loopback Host: [::1]:<port> -> 200 OK
  const ipv6Host = await rawHttp(`GET /api/records HTTP/1.1\r\nHost: [::1]:${port}\r\nConnection: close\r\n\r\n`);
  assert.match(ipv6Host, /^HTTP\/1\.1 200 /);

  // Symlink inside web/public -> 403 Forbidden (never follows symlink outside web/public!)
  const symName = `.test-symlink-${process.pid}-${Date.now()}.txt`;
  const symPath = path.join(ROOT, "web/public", symName);
  fs.symlinkSync(path.join(ROOT, "package.json"), symPath);
  t.after(() => { try { fs.unlinkSync(symPath); } catch {} });
  const symRes = await fetch(`http://127.0.0.1:${port}/${symName}`, { signal: AbortSignal.timeout(5000) });
  assert.equal(symRes.status, 403);
});

test("fleet compile recovers dead-PID stale locks without clobbering live owners (P2-5)", (t) => {
  const dir = tempDir(t);
  fs.cpSync(path.join(ROOT, "hub"), path.join(dir, "hub"), { recursive: true });
  const missionDir = path.join(dir, "missions/locktest");
  fs.mkdirSync(path.join(missionDir, "submissions"), { recursive: true });
  fs.writeFileSync(path.join(missionDir, "mission.json"), JSON.stringify({ title: "Lock Test", judge: { type: "command" } }));
  fs.writeFileSync(path.join(missionDir, "state.json"), JSON.stringify({ meta: {}, seats: [], lemmas: [], messages: [], whispers: [], checker_runs: [] }));
  fs.writeFileSync(path.join(missionDir, "events.ndjson"), "");

  // Plant a stale lock owned by a dead PID (>1s old) -> compile reclaims cleanly and succeeds!
  const lockDir = path.join(missionDir, ".state.lock");
  fs.mkdirSync(lockDir);
  fs.writeFileSync(path.join(lockDir, "owner.json"), JSON.stringify({ pid: 99999999, token: "dead-owner", created_at: Date.now() - 5000 }));
  const past = new Date(Date.now() - 5000);
  fs.utimesSync(lockDir, past, past);

  const ok = runNode(["hub/fleet.mjs", "compile", "--mission", "locktest"], { cwd: dir });
  assert.equal(ok.status, 0, ok.stderr || ok.stdout);
  assert.equal(fs.existsSync(lockDir), false, "lock cleaned up after compile");
});

test("dashboard URL sanitizers reject non-HTTPS and non-GitHub PR schemes (P3-3)", () => {
  const appSrc = fs.readFileSync(path.join(ROOT, "web/public/app.js"), "utf8");
  const fnGithub = appSrc.match(/function safeGithubUrl[\s\S]*?\n\}/)?.[0];
  const fnHttps = appSrc.match(/function safeHttpsUrl[\s\S]*?\n\}/)?.[0];
  assert.ok(fnGithub && fnHttps, "safeGithubUrl and safeHttpsUrl exist in web/public/app.js");
  const { safeGithubUrl, safeHttpsUrl } = new Function(`${fnGithub}\n${fnHttps}\nreturn { safeGithubUrl, safeHttpsUrl };`)();

  for (const bad of ["javascript:alert(1)", "data:text/html,<script>alert(1)</script>", "http://github.com/org/repo/pull/1", "https://evil.github.com/org/repo/pull/1", "https://example.com/pull/1", ""]) {
    assert.equal(safeGithubUrl(bad), null, `safeGithubUrl must reject ${bad}`);
  }
  assert.equal(safeGithubUrl("https://github.com/steph4n-gh/proof-foundry/pull/46"), "https://github.com/steph4n-gh/proof-foundry/pull/46");

  for (const bad of ["javascript:alert(1)", "data:text/html,x", "http://insecure.example/docs", "ftp://example.com/file"]) {
    assert.equal(safeHttpsUrl(bad), null, `safeHttpsUrl must reject ${bad}`);
  }
  assert.equal(safeHttpsUrl("https://arxiv.org/abs/2401.00001"), "https://arxiv.org/abs/2401.00001");
});
