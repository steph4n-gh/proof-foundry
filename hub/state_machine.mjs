import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";

export const ROOT = path.resolve(import.meta.dirname, "..");

const _frozenBodyCache = new Map();

export function extractFrozenStatementBody(relPath, statementDef = null) {
  if (!relPath || !String(relPath).endsWith(".lean")) return null;
  const key = `${relPath}::${statementDef || ""}`;
  if (_frozenBodyCache.has(key)) return _frozenBodyCache.get(key);
  const abs = path.isAbsolute(relPath) ? relPath : path.resolve(ROOT, relPath);
  if (!fs.existsSync(abs)) {
    _frozenBodyCache.set(key, null);
    return null;
  }
  const src = fs.readFileSync(abs, "utf8");
  const shortName = statementDef ? String(statementDef).split(".").pop() : null;
  const escaped = shortName ? shortName.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") : "Claim|Record";
  const re = new RegExp(`^((?:def|abbrev)\\s+(?:${escaped})\\b[\\s\\S]*?)(?=\\n(?:end\\s+|def\\s+|theorem\\s+|lemma\\s+|/--|$))`, "m");
  const m = src.match(re);
  const body = m ? m[1].trim() : null;
  _frozenBodyCache.set(key, body);
  return body;
}

export function sha256RelFile(relPath) {
  if (!relPath) return null;
  const abs = path.isAbsolute(relPath) ? relPath : path.resolve(ROOT, relPath);
  if (!fs.existsSync(abs)) return null;
  return crypto.createHash("sha256").update(fs.readFileSync(abs)).digest("hex");
}

/**
 * Single source of truth for canonical hashless King-of-the-Hill paths & theorem names!
 * Hashless filenames give a FREE git add/add concurrency lock on duplicate scores.
 */
export function computeRecordTargets(missionSlug, lemma, kind, score) {
  const tag = kind === "record_bound" ? `not_s${score}` : `s${score}`;
  const { fileStem: stem, claimsDir, artifactExt: ext, theoremTemplate } = recordPaths(missionSlug, lemma);
  const artifactFile = `${claimsDir}/${stem}_${tag}${ext}`;
  const submissionBasename = `${lemma.id}.${kind}.s${score}.json`;
  const submissionFile = `missions/${missionSlug}/submissions/${submissionBasename}`;
  const theoremName = theoremTemplate.replace(/\{tag\}/g, tag);
  return { tag, artifactFile, submissionBasename, submissionFile, theoremName };
}

function recordPaths(missionSlug, lemma) {
  const cfg = lemma.record || {};
  const fileStem = cfg.file_stem || lemma.id.replace(/-/g, "_");
  return {
    fileStem,
    claimsDir: cfg.claims_dir || `missions/${missionSlug}/lean/Claims`,
    artifactExt: cfg.artifact_ext || ".lean",
    theoremTemplate: cfg.theorem_template || `${fileStem}_{tag}.record`,
  };
}

/**
 * Compute explicit trust seal for a claim (keeps receipt trust, hunt availability, and objectives clean!):
 *   contradiction | flagged | frozen | record | audited | provisional | refuted | dead | in_work | open
 */
export function computeTrustSeal(lemma) {
  if (lemma.status === "contradiction" || lemma.record_state?.contradiction) return "contradiction";
  if (lemma.kind === "record") {
    const rs = lemma.record_state;
    if (rs?.closed) return "frozen";
    if (rs?.best) return "record";
    return "open";
  }

  const currentHash = lemma.checker?.file_hash || lemma.refutation?.file_hash || null;
  // Legacy seeded audits predate receipt hashes. Check the binding whenever a hash was recorded.
  const auditHashMismatch = Boolean(lemma.audit?.file_hash) && lemma.audit.file_hash !== currentHash;

  if (lemma.audit?.status === "flagged" && !auditHashMismatch) return "flagged";
  if (lemma.status === "checked") {
    if (lemma.checker?.statement_frozen) return "frozen";
    if (lemma.audit?.status === "faithful" && !auditHashMismatch) return "audited";
    return "provisional";
  }
  if (lemma.status === "refuted") return "refuted";
  if (lemma.status === "dead") return "dead";
  if (lemma.status === "in_work") return "in_work";
  return "open";
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

export function isRungConquered(lemma, expect = "proof") {
  if (!lemma) return false;
  const seal = computeTrustSeal(lemma);
  if (seal === "flagged" || seal === "contradiction") return false;
  if (lemma.kind === "record") {
    const rs = lemma.record_state;
    if (!rs || rs.contradiction) return false;
    if (expect === "record_any") return Boolean(rs.best);
    if (expect && typeof expect === "object" && Number.isSafeInteger(expect.record_at_most)) {
      return rs.direction === "min" && Boolean(rs.best) && rs.best.score <= expect.record_at_most;
    }
    if (expect && typeof expect === "object" && Number.isSafeInteger(expect.record_at_least)) {
      return rs.direction === "max" && Boolean(rs.best) && rs.best.score >= expect.record_at_least;
    }
    // Default ("proof" / "record_closed"): conquered only when exact optimal is closed!
    return Boolean(rs.closed);
  }
  if (expect === "refutation") return lemma.status === "refuted";
  if (expect === "either") return seal === "audited" || seal === "frozen" || lemma.status === "refuted";
  return seal === "audited" || seal === "frozen";
}

const openStatuses = new Set(["conjecture", "in_work"]);

function refused(lemma, reason) {
  return { ok: false, lemma, reason };
}

// Preflight checks an attempted action before judging. A verified receipt can
// record opposing evidence if another result arrived while the judge ran.
export function transitionClaim(lemma, event, ctx = {}) {
  const { kind, at } = event;
  const isRecord = lemma.kind === "record";
  const recordEvent = kind === "record" || kind === "record_bound";
  const contradiction = lemma.status === "contradiction" || lemma.record_state?.contradiction;
  const deny = (reason = `status is "${lemma.status}"`) => refused(lemma, `Cannot apply ${kind} to ${lemma.id}: ${reason}`);

  if (recordEvent && !isRecord) return deny("claim is not a record hunt");
  if (kind === "record_bound" && lemma.record?.allow_bound === false) return deny("bound proofs are not supported");
  if (recordEvent && ctx.mode === "replay") return transitionRecord(lemma, event, ctx);
  if (contradiction && kind !== "audit") return deny('status is "contradiction"');

  if (kind === "claim") {
    if (!openStatuses.has(lemma.status) || lemma.record_state?.closed) return deny();
    return { ok: true, lemma: { ...lemma, status: "in_work", claimed_by: event.seat, updated_at: at ?? lemma.updated_at } };
  }

  if (recordEvent) {
    if (lemma.record_state?.closed || lemma.status === "checked") return deny("record hunt is closed");
    return { ok: true, lemma };
  }

  if (isRecord) return deny("use record or record-bound for a record hunt");

  if (kind === "rule_dead") {
    if (lemma.status === "checked" || lemma.status === "refuted") return deny();
    if (!event.epitaph) return deny("missing epitaph");
    return { ok: true, lemma: { ...lemma, status: "dead", claimed_by: null, epitaph: event.epitaph, updated_at: at ?? lemma.updated_at } };
  }

  if (kind === "audit") {
    const hash = lemma.checker?.file_hash || lemma.refutation?.file_hash;
    if (!hash || event.audit?.file_hash !== hash) return deny("audit does not match the artifact hash");
    return { ok: true, lemma: { ...lemma, audit: event.audit } };
  }

  if (kind !== "proof" && kind !== "refutation") return deny("unknown event");
  const proof = kind === "proof";
  const conflicts = proof
    ? lemma.status === "refuted" || Boolean(lemma.refutation)
    : lemma.status === "checked" || Boolean(lemma.checker?.ok);
  if (ctx.mode === "preflight") return conflicts || (proof && lemma.status === "dead") ? deny() : { ok: true, lemma };

  if (proof ? !event.checker?.ok : !event.refutation) return deny("missing verified receipt");
  const existing = proof ? lemma.checker?.ok : lemma.refutation;
  if (ctx.mode === "replay" && existing && !conflicts) return { ok: true, lemma };
  const next = {
    ...lemma,
    status: conflicts ? "contradiction" : proof ? "checked" : "refuted",
    claimed_by: null,
    updated_at: at ?? lemma.updated_at,
  };
  if (ctx.mode === "replay" && existing) return { ok: true, lemma: next };
  if (proof) {
    next.lean_file = event.file || lemma.lean_file;
    next.theorem_name = event.theorem || lemma.theorem_name;
    next.registered_statement = lemma.registered_statement || lemma.statement || "";
    if (event.signature) {
      next.verified_signature = event.signature;
      next.statement = event.signature;
    }
    next.checker = event.checker;
  } else {
    next.refutation = event.refutation;
  }
  return { ok: true, lemma: next };
}

export function releaseSeatClaim(state, seatId) {
  const seat = state.seats.find((s) => s.id === seatId);
  if (!seat) throw new Error(`Unknown seat: ${seatId}`);
  const seats = state.seats.map((s) => s === seat ? { ...s, status: "idle", current_lemma: null } : s);
  const lemmas = state.lemmas.map((l) => {
    if (l.id !== seat.current_lemma && !(l.status === "in_work" && l.claimed_by === seatId)) return l;
    const other = seats.find((s) => s.current_lemma === l.id);
    return {
      ...l,
      status: l.status === "in_work" && !other ? "conjecture" : l.status,
      claimed_by: other?.id ?? null,
    };
  });
  return { ...state, seats, lemmas };
}

export function releaseClaimSeats(state, lemmaId) {
  for (const seat of state.seats) {
    if (seat.current_lemma === lemmaId) state = releaseSeatClaim(state, seat.id);
  }
  return state;
}

export function assignSeatClaim(state, seatId, lemmaId) {
  const lemma = state.lemmas.find((l) => l.id === lemmaId);
  if (!lemma) throw new Error(`Unknown claim: ${lemmaId}`);
  const event = { kind: "claim", seat: seatId };
  const result = transitionClaim(lemma, event);
  if (!result.ok) throw new Error(result.reason);

  const released = releaseClaimSeats(releaseSeatClaim(state, seatId), lemmaId);
  return {
    ...released,
    seats: released.seats.map((s) => s.id === seatId ? { ...s, status: "working", current_lemma: lemmaId } : s),
    lemmas: released.lemmas.map((l) => l.id === lemmaId ? result.lemma : l),
  };
}

function getRecordConfig(lemma) {
  const cfg = lemma.record || {};
  return {
    direction: cfg.direction === "max" ? "max" : "min",
    startTarget: Number(cfg.start_target ?? 0),
    boundFloor: Number(cfg.bound_floor ?? 0),
    scoreMax: Number(cfg.score_max ?? 100000),
  };
}

function transitionRecord(lemma, event, { statementHash, coreHash, opposingScore, gitTs, missionSlug }) {
  const { direction, startTarget, boundFloor, scoreMax } = getRecordConfig(lemma);
  const score = Number(event.score);
  if (!Number.isSafeInteger(score) || score < 0 || score > scoreMax || String(score) !== String(event.score) || !event.checker?.ok) {
    return refused(lemma, "invalid record receipt");
  }
  const targets = computeRecordTargets(missionSlug, lemma, event.kind, score);
  if ((event._sub_file && targets.submissionBasename !== event._sub_file) || event.file !== targets.artifactFile || event.theorem !== targets.theoremName) {
    return refused(lemma, "non-canonical record receipt");
  }

  const rs = lemma.record_state;
  const entry = {
    kind: event.kind,
    score,
    seat: event.checker.by_seat || "unknown",
    file: event.file,
    file_hash: event.checker.file_hash || null,
    submission: event._sub_file || "",
    points: 0,
    git_ts: gitTs ?? null,
    at: event.at || null,
  };
  if (!statementHash || event.checker.statement_hash !== statementHash || !coreHash || !event.checker.core_hash) {
    const history = [...rs.history, {
      ...entry,
      statement_hash: event.checker.statement_hash ?? null,
      core_hash: event.checker.core_hash ?? null,
      state: "stale_statement",
    }];
    return { ok: true, lemma: { ...lemma, record_state: { ...rs, history } } };
  }

  if (rs.contradiction) {
    const history = [...rs.history, { ...entry, state: "contradiction" }];
    return { ok: true, lemma: { ...lemma, record_state: { ...rs, history } } };
  }

  const record = event.kind === "record";
  const field = record ? "best" : "refuted";
  const step = direction === "min" ? -1 : 1;
  const margin = (score - (rs[field]?.score ?? (record ? startTarget : boundFloor))) * (record ? step : -step);
  const improves = rs[field] ? margin > 0 : margin >= 0;
  const contradiction = opposingScore != null && (score - opposingScore) * (record ? step : -step) >= 0;
  const next = { ...rs, contradiction };
  let points = 0;

  if (improves) {
    const { kind, points: _points, ...receipt } = entry;
    next[field] = {
      ...receipt,
      theorem: event.theorem,
      statement_hash: event.checker.statement_hash,
      core_hash: event.checker.core_hash,
      axioms: event.checker.axioms || [],
      duration_ms: event.checker.duration_ms || null,
    };
    if (!record) next.refuted.inclusive_bound = Math.max(0, score - step);
    if (!contradiction) {
      points = margin + (rs[field] ? 0 : 1);
      const prevPoints = Object.hasOwn(rs.points_by_seat, entry.seat) ? rs.points_by_seat[entry.seat] : 0;
      next.points_by_seat = { ...rs.points_by_seat, [entry.seat]: prevPoints + points };
    }
  }

  if (contradiction) next.points_by_seat = {};
  next.closed = !contradiction && Boolean(next.best) && (
    (step === -1 && next.best.score === 0) || (Boolean(next.refuted) && next.refuted.score === next.best.score + step)
  );
  next.next_target = next.closed || contradiction ? null : next.best ? next.best.score + step : startTarget;
  const historyState = contradiction ? "contradiction" : improves ? "accepted" : "ignored_non_improving";
  next.history = [...rs.history, { ...entry, points, state: historyState }];
  const status = contradiction ? "contradiction" : next.closed ? "checked" : lemma.status;
  return { ok: true, lemma: {
    ...lemma,
    status,
    ...((contradiction || next.closed) && { claimed_by: null }),
    record_state: next,
  } };
}

export function replayRecordSubmissions(missionSlug, lemma, subs, { gitAddedTs, currentHashes }) {
  const { direction, startTarget } = getRecordConfig(lemma);
  const step = direction === "min" ? -1 : 1;
  // Trusted git timestamps win. When absent or tied, replay in improving score order.
  const ordered = [...subs].sort((a, b) => {
    const ka = a._sub_file || "";
    const kb = b._sub_file || "";
    const timeDiff = (gitAddedTs.get(ka) ?? Number.MAX_SAFE_INTEGER) - (gitAddedTs.get(kb) ?? Number.MAX_SAFE_INTEGER);
    if (timeDiff !== 0) return timeDiff;
    if (a.kind !== b.kind) return a.kind === "record" ? -1 : 1;
    const scoreDiff = Number(a.score) - Number(b.score);
    if (Number.isFinite(scoreDiff) && scoreDiff !== 0) return (a.kind === "record" ? step : -step) * scoreDiff;
    return ka.localeCompare(kb);
  });

  let next = {
    ...lemma,
    status: openStatuses.has(lemma.status) ? lemma.status : "conjecture",
    record_state: {
      direction, best: null, refuted: null, next_target: startTarget,
      closed: false, contradiction: false, history: [], points_by_seat: {},
    },
  };
  const seenFiles = new Set();
  const strongest = { record: null, record_bound: null };

  for (const sub of ordered) {
    if (sub._sub_file && seenFiles.has(sub._sub_file)) continue;
    if (sub._sub_file) seenFiles.add(sub._sub_file);
    const record = sub.kind === "record";
    const result = transitionClaim(next, sub, {
      missionSlug,
      mode: "replay",
      gitTs: gitAddedTs.get(sub._sub_file),
      statementHash: currentHashes.statementHashes?.[lemma.statement_file],
      coreHash: currentHashes.coreHash,
      opposingScore: strongest[record ? "record_bound" : "record"],
    });
    if (!result.ok) continue;
    next = result.lemma;
    if (next.record_state.history.at(-1).state === "stale_statement") continue;
    const score = Number(sub.score);
    const prev = strongest[sub.kind];
    if (prev == null || (score - prev) * (record ? step : -step) > 0) strongest[sub.kind] = score;
  }
  if (lemma.status === "contradiction" && !next.record_state.contradiction) {
    next.status = "contradiction";
    next.claimed_by = null;
    Object.assign(next.record_state, { contradiction: true, closed: false, next_target: null, points_by_seat: {} });
  }
  return next;
}

export function computeClaimFreshness(mission, lemma, currentCoreHash = sha256RelFile(mission.judge?.core_file || mission.judge?.harness_file)) {
  const rs = lemma.record_state;
  const receipts = (lemma.kind === "record" ? [rs?.best, rs?.refuted] : [lemma.checker, lemma.refutation]).filter(Boolean);
  const staleHistory = rs?.history?.filter((h) => h.state === "stale_statement") || [];
  const evidence = receipts.length ? receipts : staleHistory;
  if (lemma.statement_file && evidence.length) {
    const statementHash = sha256RelFile(lemma.statement_file);
    if (!statementHash || evidence.some((r) => r.statement_hash !== statementHash)) return "stale_statement";
  }
  if (evidence.some((r) => r.core_hash != null && r.core_hash !== currentCoreHash)) return "stale_core";
  return "fresh";
}

function projectRecordMeta(mission, lemma) {
  const cfg = lemma.record || {};
  const rs = lemma.record_state || {};
  const { direction, startTarget, boundFloor, scoreMax } = getRecordConfig(lemma);
  const min = direction === "min";
  const literatureBound = (min ? cfg.literature_lower_bound : cfg.literature_upper_bound) ?? null;
  const best = rs.best?.score ?? null;
  const proven = rs.refuted?.inclusive_bound ?? null;
  const difference = (best ?? startTarget) - (proven ?? literatureBound ?? boundFloor);
  const contradiction = rs.contradiction || lemma.status === "contradiction";
  const closed = Boolean(rs.closed && !contradiction);
  const { fileStem, claimsDir, artifactExt, theoremTemplate } = recordPaths(mission.slug, lemma);
  return {
    direction,
    op: min ? "≤" : "≥",
    unit: cfg.unit || "",
    start_target: startTarget,
    best_score: best,
    best_seat: rs.best?.seat ?? null,
    best_at: rs.best?.at ?? null,
    next_target: closed || contradiction ? null : rs.next_target ?? (best == null ? startTarget : best + (min ? -1 : 1)),
    proven_bound: proven,
    literature_best: cfg.literature_best ?? null,
    literature_bound: literatureBound,
    bound_floor: boundFloor,
    score_max: scoreMax,
    gap: closed ? 0 : Math.max(0, min ? difference : -difference),
    closed,
    contradiction,
    allow_bound: cfg.allow_bound !== false,
    artifact_ext: artifactExt,
    file_stem: fileStem,
    claims_dir: claimsDir,
    theorem_template: theoremTemplate,
  };
}

export function projectClaimView(mission, lemma, currentCoreHash) {
  const seal = computeTrustSeal(lemma);
  const recordMeta = lemma.kind === "record" ? projectRecordMeta(mission, lemma) : null;
  const openPrs = lemma.open_prs || [];
  const prState = openPrs.some((pr) => pr.check_state === "passing") ? "passing"
    : openPrs.some((pr) => pr.check_state === "needs_fix") ? "needs_fix"
    : openPrs.length ? "open" : "none";
  const canAttempt = transitionClaim(lemma, { kind: recordMeta ? "record" : "claim" }, { mode: "preflight" }).ok;
  const canBound = Boolean(recordMeta && transitionClaim(lemma, { kind: "record_bound" }, { mode: "preflight" }).ok);
  const canRefute = !recordMeta && openStatuses.has(lemma.status) && transitionClaim(lemma, { kind: "refutation" }, { mode: "preflight" }).ok;
  const canAudit = !recordMeta && seal !== "contradiction" && Boolean(lemma.checker?.file_hash || lemma.refutation?.file_hash);
  const reason = canAttempt ? null : seal === "contradiction" ? "Conflicting verified results require review."
    : recordMeta?.closed ? "The exact optimum is verified."
    : lemma.status === "dead" ? "An editorial barrier closed this approach."
    : "This claim already has a verdict.";

  const frozenBody = lemma.statement_file ? extractFrozenStatementBody(lemma.statement_file, lemma.statement_def) : null;
  return {
    ...lemma,
    seal,
    freshness: computeClaimFreshness(mission, lemma, currentCoreHash),
    pr_state: prState,
    actions: { can_attempt: canAttempt, can_bound: canBound, can_refute: canRefute, can_audit: canAudit, reason },
    ...(frozenBody && { frozen_statement_body: frozenBody }),
    ...(recordMeta && { record_meta: recordMeta }),
  };
}

export function projectMissionSnapshot(mission, state, openPrs = null) {
  const currentCoreHash = sha256RelFile(mission.judge?.core_file || mission.judge?.harness_file);
  const leftKey = mission.tug_of_war?.left_key || "p_neq_np";
  const rightKey = mission.tug_of_war?.right_key || "p_eq_np";
  const scopedPrMap = openPrs?.by_mission_claim || {};
  const barePrMap = openPrs?.by_claim || {};

  const counts = {
    lemmas: state.lemmas.length,
    checked: 0,
    trusted: 0,
    audited_faithful: 0,
    frozen_matched: 0,
    records_active: 0,
    records_closed: 0,
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
  const enrichedLemmas = state.lemmas.map((lemma) => {
    const scoped = scopedPrMap[`${mission.slug}/${lemma.id}`] || [];
    const bare = barePrMap[lemma.id] || [];
    const seenPrNums = new Set();
    const open_prs = (openPrs ? [...scoped, ...bare] : lemma.open_prs || []).filter((p) => {
      if (seenPrNums.has(p.number)) return false;
      seenPrNums.add(p.number);
      return true;
    });

    const l = projectClaimView(mission, { ...lemma, open_prs }, currentCoreHash);
    const { seal } = l;
    if (l.kind === "record") {
      if (l.record_meta.contradiction) counts.contradiction++;
      else if (l.record_meta.closed) {
        counts.records_closed++;
        counts.checked++;
        counts.frozen_matched++;
        counts.trusted++;
      } else {
        counts.records_active++;
        counts.conjecture++;
      }
      if (l.record_state?.best && !l.record_meta.contradiction) {
        if (l.aims_at === leftKey) counts.aims_left_checked++;
        else if (l.aims_at === rightKey) counts.aims_right_checked++;
        else counts.aims_neutral_checked++;
      }
      return l;
    }

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
    return l;
  });

  for (const s of state.seats || []) {
    if (s.status === "working") counts.agents_working++;
    if (s.status === "checking") counts.agents_checking++;
  }

  const objectives = (mission.objectives || []).map((obj) => {
    const reqs = normalizeObjectiveReqs(obj);
    const items = reqs.map((r) => {
      const l = enrichedLemmas.find((x) => x.id === r.id);
      const done = isRungConquered(l, r.expect);
      return {
        id: r.id,
        expect: r.expect,
        kind: l?.kind || "claim",
        title: l?.title || r.id,
        status: l?.status || "conjecture",
        seal: l?.seal || "open",
        record_state: l?.record_state || null,
        record: l?.record || null,
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
    ...state,
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
    lemmas: enrichedLemmas,
    counts,
    frontier,
  };
}

export function projectGlobalRecords(snapshots, generatedAt = snapshots.at(-1)?.snapshot_at ?? null) {
  const totals = {
    missions: snapshots.length,
    trusted_proofs: 0,
    checked_total: 0,
    refuted: 0,
    barriers: 0,
    records_active: 0,
    records_closed: 0,
    open_bounties: 0,
    objectives_conquered: 0,
    objectives_total: 0,
  };
  let latestVerified = null;
  const records = [];
  for (const { mission, counts, lemmas } of snapshots) {
    const objectiveList = mission.objectives || [];
    totals.trusted_proofs += counts.trusted;
    totals.checked_total += counts.checked;
    totals.refuted += counts.refuted;
    totals.barriers += counts.dead;
    totals.records_active += counts.records_active;
    totals.records_closed += counts.records_closed;
    totals.objectives_conquered += objectiveList.filter((obj) => obj.conquered).length;
    totals.objectives_total += objectiveList.length;
    for (const lemma of lemmas) {
      if (lemma.actions.can_attempt && lemma.status !== "in_work") totals.open_bounties++;
      const identity = { mission: mission.slug, mission_title: mission.title, id: lemma.id, title: lemma.title };
      if (lemma.kind === "record") {
        const { score_max, file_stem, claims_dir, theorem_template, ...recordMeta } = lemma.record_meta;
        records.push({
          ...identity,
          statement_file: lemma.statement_file ?? null,
          statement_def: lemma.statement_def ?? null,
          ...recordMeta,
          open_prs: lemma.open_prs,
          history: lemma.record_state?.history || [],
        });
      }
      if (lemma.status !== "checked" || lemma.seal === "flagged" || lemma.seal === "contradiction") continue;
      const best = lemma.record_state?.best;
      if (!best && !lemma.checker?.ok) continue;
      const at = (best ? best.at : lemma.checker?.checked_at) || lemma.updated_at;
      const file = best?.file || lemma.lean_file;
      if (!at || !file || (latestVerified && at <= latestVerified.at)) continue;
      const baseStatement = lemma.verified_signature || lemma.registered_statement || lemma.statement || "";
      const unfoldedStatement =
        lemma.frozen_statement_body && baseStatement && !baseStatement.includes(":=")
          ? `${baseStatement}\n\n${lemma.frozen_statement_body}`
          : baseStatement || lemma.frozen_statement_body || "";
      latestVerified = {
        ...identity,
        statement: unfoldedStatement,
        seal: lemma.seal,
        judge_label: mission.judge?.label || mission.judge?.type || "Judge",
        by_seat: best?.seat || lemma.checker?.by_seat || null,
        at,
        file,
      };
    }
  }
  return { generated_at: generatedAt, totals, latest_verified: latestVerified, records };
}
