#!/usr/bin/env node
/**
 * formal/verify_ui_machine.mjs — Executable formal property, trace, route, and
 * adapter verifier against the real `web/public/ui_machine.js` ES module.
 *
 *   1. Randomized + adversarial trace fuzzer (250 seeded runs × 40 steps =
 *      10,000 transitions + deterministic multi-race scenarios), checking all
 *      protocol invariants after every single transition.
 *   2. Exhaustive URL route round-trip, idempotency, legacy alias, and
 *      malicious-input sanitization check across 16,000+ combinations.
 *   3. Dense snapshot-adapter invariant grid (pre-projection fallbacks +
 *      projected payloads + live repository mission snapshots).
 *   4. Negative mutation self-checks proving the invariant checkers catch
 *      corrupted transitions and adapter violations.
 *
 * Zero external dependencies. Exits 0 on pass, nonzero on fail.
 */

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

import {
  VIEWS,
  LEDGER_TABS,
  DEFAULT_LEDGER_TAB,
  DEFAULT_MISSION,
  LEGACY_HASH_ALIASES,
  TRANSPORT_STATUSES,
  OVERLAY_KINDS,
  HARNESSES,
  QUEUE_MODES,
  NO_OVERLAY,
  sanitizeSlug,
  sanitizeClaimId,
  normalizeRoute,
  parseRouteFromLocation,
  serializeRouteToLocation,
  initialTransport,
  initialUIState,
  reduceUI,
  acceptsSnapshot,
  isCurrentMissionRequest,
  createUIMachine,
  sealOf,
  freshnessOf,
  prStateOf,
  recordMetaOf,
  computeGap,
  actionsOf,
  isAttemptable,
  statusOf,
  recordRowFromLemma,
  normalizeRecordRow,
  normalizeRecordsPayload,
  synthesizeRecordsPayload,
  mergeSnapshotIntoRecords,
  sortRecords,
  pickHotRecords,
  boundIntervalGeometry,
  ratchetSeries,
} from "../web/public/ui_machine.js";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

let passedChecks = 0;
let failedChecks = 0;

function check(cond, label, detail = "") {
  if (cond) {
    passedChecks++;
  } else {
    failedChecks++;
    console.error(`FAIL  ${label}${detail ? ` -> ${detail}` : ""}`);
  }
}

function deepEqual(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

function sameKeySet(obj, expectedKeys) {
  if (!obj || typeof obj !== "object") return false;
  const actual = Object.keys(obj).sort();
  const want = [...expectedKeys].sort();
  return actual.length === want.length && actual.every((k, i) => k === want[i]);
}

// Deterministic Mulberry32 PRNG for reproducible trace fuzzing.
function mulberry32(seed) {
  let a = seed >>> 0;
  return function nextRand() {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function pick(rng, arr) {
  return arr[Math.floor(rng() * arr.length)];
}

// ===========================================================================
// Invariant Oracles
// ===========================================================================

const VALID_TONES = new Set(["muted", "ink", "accent", "alarm", "struck"]);
const PROBE_MISSIONS = ["", "erdos-combinatorics", "p-vs-np", "sorting-networks", "m1", "m2"];

/**
 * Checks all single-state and step-transition invariants for `(prev, ev) -> next`.
 * Throws an Error naming the exact violated invariant if any property breaks.
 */
export function assertStepInvariants(prev, ev, next) {
  if (!next || typeof next !== "object") {
    throw new Error("State must be a non-null object");
  }

  // 1. SingleOverlayKind & strict per-kind field shape (no leftover fields)
  const o = next.overlay;
  if (!o || !OVERLAY_KINDS.includes(o.kind)) {
    throw new Error(`SingleOverlayKind: invalid overlay.kind=${JSON.stringify(o?.kind)}`);
  }
  if (o.kind === "none") {
    if (!sameKeySet(o, ["kind"]) || "status" in o || "reqSeq" in o) {
      throw new Error(`SingleOverlayKind: 'none' overlay leaked extra fields: ${JSON.stringify(o)}`);
    }
  } else if (o.kind === "dossier") {
    if (!sameKeySet(o, ["kind", "claimId", "mission", "status", "reqSeq", "data", "error"])) {
      throw new Error(`SingleOverlayKind: 'dossier' overlay has unexpected keys: ${Object.keys(o).join(",")}`);
    }
    if (!["loading", "ready", "error"].includes(o.status)) {
      throw new Error(`SingleOverlayKind: invalid dossier status=${JSON.stringify(o.status)}`);
    }
    if (!Number.isInteger(o.reqSeq) || o.reqSeq < 1 || o.reqSeq > next.seq.dossier) {
      throw new Error(`SingleOverlayKind: invalid dossier reqSeq=${o.reqSeq} vs seq.dossier=${next.seq.dossier}`);
    }
    if (sanitizeClaimId(o.claimId) !== o.claimId) {
      throw new Error(`SingleOverlayKind: unsanitized dossier claimId=${JSON.stringify(o.claimId)}`);
    }
    if (o.mission !== "" && sanitizeSlug(o.mission) !== o.mission) {
      throw new Error(`SingleOverlayKind: unsanitized dossier mission=${JSON.stringify(o.mission)}`);
    }
  } else if (o.kind === "attempt") {
    if (!sameKeySet(o, ["kind", "claimId", "mission", "harness", "handle", "queueMode", "recKind", "recScore"])) {
      throw new Error(`SingleOverlayKind: 'attempt' overlay has unexpected keys: ${Object.keys(o).join(",")}`);
    }
    if ("status" in o || "reqSeq" in o) {
      throw new Error("SingleOverlayKind: 'attempt' overlay leaked dossier status/reqSeq");
    }
    if (!HARNESSES.includes(o.harness) || !QUEUE_MODES.includes(o.queueMode) || o.handle.length > 39) {
      throw new Error(`SingleOverlayKind: invalid attempt fields: ${JSON.stringify(o)}`);
    }
    if (sanitizeClaimId(o.claimId) !== o.claimId) {
      throw new Error(`SingleOverlayKind: unsanitized attempt claimId=${JSON.stringify(o.claimId)}`);
    }
  } else if (o.kind === "search") {
    if (!sameKeySet(o, ["kind", "query", "activeIndex"])) {
      throw new Error(`SingleOverlayKind: 'search' overlay has unexpected keys: ${Object.keys(o).join(",")}`);
    }
    if ("status" in o || "reqSeq" in o || "claimId" in o || "mission" in o) {
      throw new Error("SingleOverlayKind: 'search' overlay leaked dossier/attempt fields");
    }
    if (typeof o.query !== "string" || !Number.isInteger(o.activeIndex) || o.activeIndex < 0) {
      throw new Error(`SingleOverlayKind: invalid search fields: ${JSON.stringify(o)}`);
    }
  }

  // 2. Monotonic sequence counters
  const t = next.transport;
  if (!TRANSPORT_STATUSES.includes(t.status)) {
    throw new Error(`Transport: invalid status=${JSON.stringify(t.status)}`);
  }
  if (t.reqSeq < prev.transport.reqSeq) {
    throw new Error(`Monotonicity: transport.reqSeq regressed ${prev.transport.reqSeq} -> ${t.reqSeq}`);
  }
  if (next.seq.dossier < prev.seq.dossier) {
    throw new Error(`Monotonicity: seq.dossier regressed ${prev.seq.dossier} -> ${next.seq.dossier}`);
  }

  // 3. HealthyStreamSurvivesFailedSwitch & committed mission persistence
  if (prev.transport.activeMission && !t.activeMission) {
    throw new Error(`HealthyStreamSurvivesFailedSwitch: committed activeMission ${prev.transport.activeMission} was wiped`);
  }
  if (t.activeMission && t.status === "error") {
    throw new Error(
      `HealthyStreamSurvivesFailedSwitch: activeMission=${t.activeMission} entered transport.status='error' on ${ev?.type}`
    );
  }
  if (ev?.type === "MISSION_FAILED" && prev.transport.activeMission) {
    if (t.activeMission !== prev.transport.activeMission || t.status !== prev.transport.status) {
      throw new Error(
        `HealthyStreamSurvivesFailedSwitch: failed switch mutated activeMission/status (${prev.transport.activeMission}/${prev.transport.status} -> ${t.activeMission}/${t.status})`
      );
    }
  }
  if (ev?.type === "MISSION_REQUESTED" && prev.transport.activeMission) {
    if (t.activeMission !== prev.transport.activeMission || t.status !== prev.transport.status) {
      throw new Error("HealthyStreamSurvivesFailedSwitch: in-flight switch disturbed active stream status");
    }
  }

  // 4. RouteMissionTracksActiveMission & stability until MISSION_LOADED commit
  const r = next.route;
  if (!VIEWS.includes(r.view) || !LEDGER_TABS.includes(r.ledgerTab)) {
    throw new Error(`Route: invalid view/tab ${JSON.stringify(r)}`);
  }
  if (t.activeMission && r.mission !== t.activeMission) {
    throw new Error(
      `RouteMissionTracksActiveMission: activeMission=${t.activeMission} !== route.mission=${r.mission}`
    );
  }
  const missionJustCommitted = ev?.type === "MISSION_LOADED" && t !== prev.transport;
  if (!missionJustCommitted && r.mission !== prev.route.mission) {
    throw new Error(
      `RouteMissionStability: route.mission moved (${prev.route.mission} -> ${r.mission}) on ${ev?.type} without MISSION_LOADED commit`
    );
  }

  // 5. Stale response & stale SSE immutability (strict === reference identity)
  if ((ev?.type === "MISSION_LOADED" || ev?.type === "MISSION_FAILED") && ev.reqSeq !== prev.transport.reqSeq) {
    if (next !== prev) {
      throw new Error(
        `StaleMissionResponseIgnored: stale ${ev.type} (reqSeq=${ev.reqSeq} !== ${prev.transport.reqSeq}) mutated state reference`
      );
    }
  }
  if (
    (ev?.type === "DOSSIER_LOADED" || ev?.type === "DOSSIER_FAILED") &&
    (prev.overlay.kind !== "dossier" || ev.reqSeq !== prev.overlay.reqSeq)
  ) {
    if (next !== prev) {
      throw new Error(
        `StaleDossierResponseIgnored: stale ${ev.type} (reqSeq=${ev.reqSeq}, kind=${prev.overlay.kind}, cur=${prev.overlay.reqSeq}) mutated state reference`
      );
    }
  }
  if (
    (ev?.type === "SSE_OPEN" || ev?.type === "SSE_SNAPSHOT" || ev?.type === "SSE_ERROR") &&
    (prev.transport.mode !== "live" || ev.mission !== prev.transport.activeMission)
  ) {
    if (next !== prev) {
      throw new Error(
        `StaleSseIgnored: SSE event ${ev.type} for mission=${ev.mission} (mode=${prev.transport.mode}, active=${prev.transport.activeMission}) mutated state`
      );
    }
  }
  if ((ev?.type === "ESCAPE" || ev?.type === "CLOSE_OVERLAY") && prev.overlay.kind === "none") {
    if (next !== prev) {
      throw new Error(`IdempotentClose: ${ev.type} with no open overlay mutated state reference`);
    }
  }

  // 6. acceptsSnapshot & isCurrentMissionRequest soundness
  for (const probe of PROBE_MISSIONS) {
    const expectedAccept = t.mode === "live" && Boolean(probe) && probe === t.activeMission;
    if (acceptsSnapshot(next, probe) !== expectedAccept) {
      throw new Error(`acceptsSnapshot soundness failed for probe=${probe}`);
    }
  }
  if (!isCurrentMissionRequest(next, t.reqSeq)) {
    throw new Error(`isCurrentMissionRequest(${t.reqSeq}) returned false for current reqSeq`);
  }
  if (isCurrentMissionRequest(next, t.reqSeq + 1) || (t.reqSeq > 0 && isCurrentMissionRequest(next, t.reqSeq - 1))) {
    throw new Error(`isCurrentMissionRequest accepted non-current reqSeq around ${t.reqSeq}`);
  }

  // 7. NoCrossMissionOverlayAfterCommit
  if (missionJustCommitted) {
    if ((o.kind === "dossier" || o.kind === "attempt") && o.mission && o.mission !== t.activeMission) {
      throw new Error(
        `NoCrossMissionOverlayAfterCommit: overlay (${o.kind}, mission=${o.mission}) survived commit of ${t.activeMission}`
      );
    }
  }

  // 8. DossierRouteClaimSync
  const routeOwnsClaim = ev?.type === "MISSION_LOADED" || ev?.type === "ROUTE_SYNC";
  if (o !== prev.overlay && !routeOwnsClaim) {
    if (o.kind === "dossier") {
      const expectedClaim = !o.mission || o.mission === r.mission ? o.claimId : null;
      if (r.claim !== expectedClaim) {
        throw new Error(
          `DossierRouteClaimSync: OPEN_DOSSIER expected route.claim=${expectedClaim}, got ${r.claim}`
        );
      }
    } else if (o.kind === "attempt" || o.kind === "search" || o.kind === "none") {
      if (r.claim !== null) {
        throw new Error(
          `DossierRouteClaimSync: overlay=${o.kind} (from ${prev.overlay.kind} via ${ev?.type}) left route.claim=${r.claim}`
        );
      }
    }
  }
  if (ev?.type === "ROUTE_SYNC" && !sanitizeClaimId(ev.route?.claim) && prev.overlay.kind === "dossier") {
    if (o.kind !== "none" || r.claim !== null) {
      throw new Error("DossierRouteClaimSync: claim-less ROUTE_SYNC failed to close open dossier");
    }
  }
}

/**
 * Checks all snapshot adapter invariants on a single lemma/record object.
 * Throws an Error naming the exact violated invariant if any property breaks.
 */
export function assertAdapterInvariants(lemma) {
  const seal = sealOf(lemma);
  if (typeof seal !== "string" || !seal) {
    throw new Error(`sealOf returned invalid seal=${JSON.stringify(seal)}`);
  }

  const st = statusOf(lemma);
  if (!st || typeof st !== "object" || !VALID_TONES.has(st.tone)) {
    throw new Error(`statusOf tone=${JSON.stringify(st?.tone)} outside allowed grammar`);
  }
  if (!st.key || !st.glyph || !st.label) {
    throw new Error(`statusOf missing key/glyph/label: ${JSON.stringify(st)}`);
  }
  if ((seal === "contradiction" || seal === "flagged") && st.tone !== "alarm") {
    throw new Error(`statusOf: ${seal} must carry 'alarm' tone, got ${st.tone}`);
  }
  if (seal === "refuted" && lemma?.kind !== "record" && st.tone !== "ink") {
    throw new Error(`statusOf: refuted claim must carry 'ink' tone, got ${st.tone}`);
  }
  if (seal === "dead" && lemma?.kind !== "record" && st.tone !== "struck") {
    throw new Error(`statusOf: barrier/dead claim must carry 'struck' tone, got ${st.tone}`);
  }

  const fresh = freshnessOf(lemma);
  if (!["fresh", "stale_core", "stale_statement"].includes(fresh)) {
    throw new Error(`freshnessOf returned invalid value=${JSON.stringify(fresh)}`);
  }
  const pr = prStateOf(lemma);
  if (!["none", "open", "passing", "needs_fix"].includes(pr)) {
    throw new Error(`prStateOf returned invalid value=${JSON.stringify(pr)}`);
  }

  const acts = actionsOf(lemma);
  if (typeof acts.can_attempt !== "boolean" || typeof acts.can_bound !== "boolean") {
    throw new Error(`actionsOf returned non-boolean flags: ${JSON.stringify(acts)}`);
  }
  if (isAttemptable(lemma) !== acts.can_attempt) {
    throw new Error("isAttemptable disagreed with actionsOf(lemma).can_attempt");
  }

  if (lemma?.kind === "record") {
    const rm = recordMetaOf(lemma);
    if (!rm || (rm.direction !== "min" && rm.direction !== "max")) {
      throw new Error(`recordMetaOf returned invalid direction: ${JSON.stringify(rm)}`);
    }
    if (rm.op !== (rm.direction === "max" ? "≥" : "≤") && !lemma.record_meta?.op) {
      throw new Error(`recordMetaOf returned mismatched operator=${rm.op} for direction=${rm.direction}`);
    }
    const directGap = computeGap(rm);
    if (directGap !== null && (!Number.isFinite(directGap) || directGap < 0)) {
      throw new Error(`computeGap returned invalid/negative gap=${directGap}`);
    }
    if (rm.gap !== null && (!Number.isFinite(rm.gap) || rm.gap < 0)) {
      throw new Error(`recordMetaOf.gap invalid/negative=${rm.gap}`);
    }
    if (rm.closed) {
      if (directGap !== 0 || rm.gap !== 0) {
        throw new Error(`Closed record must have gap=0 (computeGap=${directGap}, rm.gap=${rm.gap})`);
      }
      if (acts.can_attempt || acts.can_bound) {
        throw new Error(`Closed record must never allow can_attempt/can_bound: ${JSON.stringify(acts)}`);
      }
    }
    if (rm.contradiction || seal === "contradiction") {
      if (acts.can_attempt || acts.can_bound) {
        throw new Error(`Contradiction record must never allow can_attempt/can_bound: ${JSON.stringify(acts)}`);
      }
    }
    if (!rm.allow_bound && acts.can_bound) {
      throw new Error("Record with allow_bound=false returned can_bound=true");
    }
  } else {
    if (recordMetaOf(lemma) !== null) {
      throw new Error("recordMetaOf on non-record lemma must be null");
    }
    if (seal === "contradiction" && (acts.can_attempt || acts.can_bound || acts.can_refute)) {
      throw new Error(`Contradiction lemma allowed actions: ${JSON.stringify(acts)}`);
    }
  }
}

// ===========================================================================
// 1. Randomized + Adversarial Trace Fuzzer
// ===========================================================================
console.log("— 1. Randomized + Adversarial Trace Fuzzer —");

const FUZZ_MISSIONS = ["erdos-combinatorics", "p-vs-np", "sorting-networks", "fast-matrix-mul"];
const BAD_MISSIONS = ["", "../../etc/passwd", "<script>", "-bad-slug"];
const FUZZ_CLAIMS = ["E-ram-001", "L-rec-005", "SN-rec-013", "MM-001"];
const BAD_CLAIMS = ["", "<img onerror=1>", "../secret", "-bad"];

const NUM_SEEDS = 250;
const STEPS_PER_SEED = 44; // 11,000 randomized steps + scripted adversarial traces
let totalFuzzSteps = 0;
const eventCounts = new Map();

function recordDispatch(state, ev) {
  const next = reduceUI(state, ev);
  assertStepInvariants(state, ev, next);
  totalFuzzSteps++;
  eventCounts.set(ev.type, (eventCounts.get(ev.type) || 0) + 1);
  return next;
}

for (let seed = 1; seed <= NUM_SEEDS; seed++) {
  const rng = mulberry32(seed * 0x9e3779b9);
  const initMission = pick(rng, FUZZ_MISSIONS);
  let state = initialUIState({
    route: {
      view: pick(rng, VIEWS),
      ledgerTab: pick(rng, LEDGER_TABS),
      mission: initMission,
      claim: null,
    },
    defaultMission: DEFAULT_MISSION,
  });
  assertStepInvariants(state, { type: "INIT" }, state);

  const missionReqs = []; // [{ reqSeq, mission }]
  const dossierReqs = []; // [reqSeq]

  for (let step = 0; step < STEPS_PER_SEED; step++) {
    // Boot phase transitions (matching app.js boot() lifecycle)
    if (state.transport.status === "boot" && rng() < 0.7) {
      if (rng() < 0.75) {
        state = recordDispatch(state, {
          type: "CATALOG_LOADED",
          mode: rng() < 0.75 ? "live" : "static",
        });
      } else {
        state = recordDispatch(state, { type: "CATALOG_FAILED", error: "network timeout" });
      }
      continue;
    }

    const roll = rng();
    if (roll < 0.06) {
      state = recordDispatch(state, { type: "RETRY" });
    } else if (roll < 0.10) {
      state = recordDispatch(state, { type: "DISMISS_ERROR" });
    } else if (roll < 0.24 && state.transport.status !== "boot" && state.transport.status !== "error") {
      const m = rng() < 0.88 ? pick(rng, FUZZ_MISSIONS) : pick(rng, BAD_MISSIONS);
      // Standard user switch passes claim: null; deep-link switch passes claim when no modal owns screen
      const deepClaim =
        (state.overlay.kind === "none" || state.overlay.kind === "dossier") && rng() < 0.25
          ? pick(rng, FUZZ_CLAIMS)
          : null;
      const intent =
        rng() < 0.85
          ? { view: pick(rng, VIEWS), ledgerTab: pick(rng, LEDGER_TABS), claim: deepClaim }
          : { view: pick(rng, VIEWS), claim: null };
      const prevSeq = state.transport.reqSeq;
      state = recordDispatch(state, { type: "MISSION_REQUESTED", mission: m, intent });
      if (state.transport.reqSeq > prevSeq) {
        missionReqs.push({ reqSeq: state.transport.reqSeq, mission: sanitizeSlug(m) });
      }
    } else if (roll < 0.36 && missionReqs.length > 0) {
      // Pick either latest or an arbitrary older/superseded request (out-of-order delivery!)
      const entry =
        rng() < 0.55 ? missionReqs[missionReqs.length - 1] : pick(rng, missionReqs);
      if (rng() < 0.65) {
        state = recordDispatch(state, {
          type: "MISSION_LOADED",
          mission: entry.mission,
          reqSeq: entry.reqSeq,
        });
      } else {
        state = recordDispatch(state, {
          type: "MISSION_FAILED",
          mission: entry.mission,
          reqSeq: entry.reqSeq,
          error: "HTTP 502",
        });
      }
    } else if (roll < 0.47) {
      const m =
        state.transport.activeMission && rng() < 0.55
          ? state.transport.activeMission
          : pick(rng, FUZZ_MISSIONS);
      const sseType = pick(rng, ["SSE_OPEN", "SSE_SNAPSHOT", "SSE_ERROR"]);
      state = recordDispatch(state, { type: sseType, mission: m });
    } else if (roll < 0.59) {
      const claimId = rng() < 0.88 ? pick(rng, FUZZ_CLAIMS) : pick(rng, BAD_CLAIMS);
      const mission =
        rng() < 0.6
          ? state.route.mission
          : rng() < 0.85
            ? pick(rng, FUZZ_MISSIONS)
            : "";
      const prevDossierSeq = state.seq.dossier;
      state = recordDispatch(state, { type: "OPEN_DOSSIER", claimId, mission });
      if (state.seq.dossier > prevDossierSeq) {
        dossierReqs.push(state.seq.dossier);
      }
    } else if (roll < 0.70 && dossierReqs.length > 0) {
      // Deliver fresh or stale/closed dossier responses out of order
      const seq =
        state.overlay.kind === "dossier" && rng() < 0.55
          ? state.overlay.reqSeq
          : pick(rng, dossierReqs);
      if (rng() < 0.65) {
        state = recordDispatch(state, {
          type: "DOSSIER_LOADED",
          reqSeq: seq,
          data: { lemma: { id: "E-ram-001" } },
        });
      } else {
        state = recordDispatch(state, {
          type: "DOSSIER_FAILED",
          reqSeq: seq,
          error: "HTTP 404",
        });
      }
    } else if (roll < 0.78) {
      const claimId = rng() < 0.9 ? pick(rng, FUZZ_CLAIMS) : pick(rng, BAD_CLAIMS);
      const mission = rng() < 0.6 ? state.route.mission : pick(rng, FUZZ_MISSIONS);
      state = recordDispatch(state, {
        type: "OPEN_ATTEMPT",
        claimId,
        mission,
        harness: rng() < 0.8 ? pick(rng, HARNESSES) : "invalid-harness",
        handle: rng() < 0.8 ? "donor_ada" : "h".repeat(65),
        queueMode: rng() < 0.8 ? pick(rng, QUEUE_MODES) : "invalid-mode",
        recKind: rng() < 0.5 ? "record" : "record_bound",
        recScore: 42,
      });
    } else if (roll < 0.82) {
      state = recordDispatch(state, {
        type: "ATTEMPT_UPDATE",
        patch: {
          harness: rng() < 0.7 ? pick(rng, HARNESSES) : "bogus",
          handle: "updated-handle-" + "x".repeat(40),
          queueMode: rng() < 0.7 ? pick(rng, QUEUE_MODES) : "bogus",
          recKind: rng() < 0.5 ? "record_bound" : "record",
          recScore: 41,
        },
      });
    } else if (roll < 0.88) {
      if (state.overlay.kind === "search" && rng() < 0.65) {
        const subEv = pick(rng, [
          { type: "SEARCH_QUERY", query: "ramsey" },
          { type: "SEARCH_MOVE", delta: pick(rng, [-3, -1, 1, 2]), count: pick(rng, [0, 1, 7]) },
          { type: "SEARCH_SET_INDEX", index: pick(rng, [-2, 0, 3, 12]), count: pick(rng, [0, 5]) },
        ]);
        state = recordDispatch(state, subEv);
      } else {
        state = recordDispatch(state, { type: "OPEN_SEARCH", query: rng() < 0.5 ? "" : "erdos" });
      }
    } else if (roll < 0.94) {
      state = recordDispatch(state, { type: rng() < 0.5 ? "ESCAPE" : "CLOSE_OVERLAY" });
    } else if (roll < 0.97) {
      state = recordDispatch(state, {
        type: "ROUTE_NAVIGATE",
        route: {
          view: pick(rng, VIEWS),
          ledgerTab: pick(rng, LEDGER_TABS),
          mission: pick(rng, FUZZ_MISSIONS), // must be ignored by ROUTE_NAVIGATE
          claim: null,
        },
      });
    } else {
      // ROUTE_SYNC from popstate: claim-less closes dossier; non-null claim pairs with OPEN_DOSSIER as in app.js:2083-2085
      const syncClaim = rng() < 0.75 ? null : pick(rng, FUZZ_CLAIMS);
      state = recordDispatch(state, {
        type: "ROUTE_SYNC",
        route: {
          view: pick(rng, VIEWS),
          ledgerTab: pick(rng, LEDGER_TABS),
          mission: pick(rng, FUZZ_MISSIONS), // must be ignored by ROUTE_SYNC
          claim: syncClaim,
        },
      });
      if (syncClaim && !(state.overlay.kind === "dossier" && state.overlay.claimId === syncClaim)) {
        const prevSeq = state.seq.dossier;
        state = recordDispatch(state, {
          type: "OPEN_DOSSIER",
          claimId: syncClaim,
          mission: state.transport.activeMission || state.route.mission,
        });
        if (state.seq.dossier > prevSeq) dossierReqs.push(state.seq.dossier);
      }
    }
  }
}

// Deterministic adversarial multi-race script:
// 3-way out-of-order mission race + failed switch on healthy stream + cross-mission overlay eviction + 3-way dossier race
{
  let s = initialUIState({ route: { view: "missions", mission: "erdos-combinatorics" } });
  s = recordDispatch(s, { type: "CATALOG_LOADED", mode: "live" });
  s = recordDispatch(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics", intent: { view: "control", claim: null } });
  const mSeq1 = s.transport.reqSeq;
  s = recordDispatch(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "bounties", claim: null } });
  const mSeq2 = s.transport.reqSeq;
  s = recordDispatch(s, { type: "MISSION_REQUESTED", mission: "sorting-networks", intent: { view: "ledger", ledgerTab: "fleet", claim: null } });
  const mSeq3 = s.transport.reqSeq;

  // Out-of-order: seq 1 & seq 2 arrive before and after seq 3 commits
  const beforeStale1 = s;
  s = recordDispatch(s, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: mSeq1 });
  check(s === beforeStale1, "adversarial: superseded MISSION_LOADED seq=1 strictly ignored");
  s = recordDispatch(s, { type: "MISSION_LOADED", mission: "sorting-networks", reqSeq: mSeq3 });
  s = recordDispatch(s, { type: "SSE_OPEN", mission: "sorting-networks" });
  const afterCommit3 = s;
  s = recordDispatch(s, { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: mSeq2, error: "late 500" });
  check(s === afterCommit3, "adversarial: late MISSION_FAILED seq=2 after seq=3 commit strictly ignored");

  // Open cross-mission dossier & attempt on erdos-combinatorics while sorting-networks is active
  s = recordDispatch(s, { type: "OPEN_DOSSIER", claimId: "E-ram-001", mission: "erdos-combinatorics" });
  const dSeq1 = s.overlay.reqSeq;
  check(s.route.claim === null, "adversarial: cross-mission dossier leaves route.claim null");
  s = recordDispatch(s, { type: "OPEN_DOSSIER", claimId: "SN-rec-013", mission: "sorting-networks" });
  const dSeq2 = s.overlay.reqSeq;
  check(s.route.claim === "SN-rec-013", "adversarial: routed-mission dossier sets route.claim");
  const beforeStaleDossier = s;
  s = recordDispatch(s, { type: "DOSSIER_LOADED", reqSeq: dSeq1, data: { lemma: { id: "E-ram-001" } } });
  check(s === beforeStaleDossier, "adversarial: stale DOSSIER_LOADED seq=1 strictly ignored");
  s = recordDispatch(s, { type: "DOSSIER_LOADED", reqSeq: dSeq2, data: { lemma: { id: "SN-rec-013" } } });

  // Failed switch to p-vs-np keeps sorting-networks stream live_connected
  s = recordDispatch(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "control", claim: null } });
  s = recordDispatch(s, { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: s.transport.reqSeq, error: "503" });
  check(
    s.transport.status === "live_connected" && s.transport.activeMission === "sorting-networks",
    "adversarial: failed mission switch preserves healthy live_connected stream"
  );

  // Committed switch to p-vs-np evicts sorting-networks attempt modal
  s = recordDispatch(s, { type: "OPEN_ATTEMPT", claimId: "SN-rec-013", mission: "sorting-networks" });
  s = recordDispatch(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "control", claim: null } });
  s = recordDispatch(s, { type: "MISSION_LOADED", mission: "p-vs-np", reqSeq: s.transport.reqSeq });
  check(s.overlay === NO_OVERLAY && s.route.mission === "p-vs-np", "adversarial: MISSION_LOADED evicts cross-mission attempt modal");
}

check(
  totalFuzzSteps >= 5000,
  `trace fuzzer executed ${totalFuzzSteps} verified steps across ${NUM_SEEDS} seeded runs (≥ 5,000 required)`
);
for (const reqEv of [
  "CATALOG_LOADED",
  "CATALOG_FAILED",
  "MISSION_REQUESTED",
  "MISSION_LOADED",
  "MISSION_FAILED",
  "SSE_OPEN",
  "SSE_ERROR",
  "RETRY",
  "OPEN_DOSSIER",
  "DOSSIER_LOADED",
  "DOSSIER_FAILED",
  "OPEN_ATTEMPT",
  "OPEN_SEARCH",
  "ESCAPE",
  "ROUTE_NAVIGATE",
  "ROUTE_SYNC",
]) {
  check((eventCounts.get(reqEv) || 0) > 0, `fuzzer exercised ${reqEv} (${eventCounts.get(reqEv) || 0} dispatches)`);
}
console.log(`PASS  Trace fuzzer: ${totalFuzzSteps} steps across ${NUM_SEEDS} seeds (0 invariant violations)`);

// ===========================================================================
// 2. Exhaustive URL Route Round-Trip & Sanitization Check
// ===========================================================================
console.log("\n— 2. Exhaustive URL Route Round-Trip & Sanitization Check —");

const TEST_VIEWS = [...VIEWS, "", "unknown-view", "LEDGER"];
const TEST_TABS = [...LEDGER_TABS, "", "bogus-tab", "<script>"];
const VALID_SLUGS = ["erdos-combinatorics", "p-vs-np", "sorting-networks", "a", "m-0123456789"];
const MALICIOUS_SLUGS = [
  "",
  "../../etc/passwd",
  "<script>alert(1)</script>",
  "-leading-dash",
  "UPPERCASE",
  "slug with spaces",
  "javascript:alert(1)",
  "a".repeat(65),
  "semi;colon&claim=evil",
];
const VALID_CLAIMS = [null, "E-ram-001", "L-rec-005", "MM_001.v2", "A"];
const MALICIOUS_CLAIMS = [
  "",
  "../../etc/passwd",
  "<img src=x onerror=alert(1)>",
  ".leading-dot",
  "-leading-dash",
  "_leading_underscore",
  "claim?mission=x#ledger",
  "c".repeat(97),
];
const PATHNAMES = ["/", "/proof-foundry/"];

function locFromSerialized(serialized) {
  const u = new URL(serialized, "https://proof-foundry.example");
  return { pathname: u.pathname, search: u.search, hash: u.hash };
}

let routeChecks = 0;
let routeViolations = 0;

for (const s of VALID_SLUGS) {
  if (sanitizeSlug(s) !== s) routeViolations++;
}
for (const s of MALICIOUS_SLUGS) {
  if (sanitizeSlug(s) !== "") routeViolations++;
}
for (const c of VALID_CLAIMS) {
  const expected = c === null ? null : c;
  if (sanitizeClaimId(c) !== expected) routeViolations++;
}
for (const c of MALICIOUS_CLAIMS) {
  if (sanitizeClaimId(c) !== null) routeViolations++;
}

for (const pathname of PATHNAMES) {
  for (const view of TEST_VIEWS) {
    for (const ledgerTab of TEST_TABS) {
      for (const mission of [...VALID_SLUGS, ...MALICIOUS_SLUGS]) {
        for (const claim of [...VALID_CLAIMS, ...MALICIOUS_CLAIMS]) {
          const rawRoute = { view, ledgerTab, mission, claim };
          const normEmpty = normalizeRoute(rawRoute, "");
          const serialized = serializeRouteToLocation(rawRoute, { pathname });
          const loc = locFromSerialized(serialized);

          if (loc.pathname !== pathname) routeViolations++;
          if (MALICIOUS_SLUGS.includes(mission) && normEmpty.mission !== "") routeViolations++;
          if (MALICIOUS_CLAIMS.includes(claim) && normEmpty.claim !== null) routeViolations++;

          const parsedEmpty = parseRouteFromLocation(loc, { defaultMission: "" });
          // In the URL format `#view` vs `#ledger/<tab>`, ledgerTab is carried in the URL iff view === "ledger".
          const canonical =
            normEmpty.view === "ledger" ? normEmpty : { ...normEmpty, ledgerTab: DEFAULT_LEDGER_TAB };
          if (!deepEqual(parsedEmpty, canonical)) {
            routeViolations++;
            if (routeViolations <= 3) {
              console.error("Route mismatch:", { rawRoute, serialized, parsedEmpty, canonical });
            }
          }

          // Strict round-trip equality `parseRouteFromLocation(serializeRouteToLocation(r)) === normalizeRoute(r)`
          // for every canonical route (where non-ledger views hold DEFAULT_LEDGER_TAB and mission is valid or defaulted).
          const normDefault = normalizeRoute(rawRoute, DEFAULT_MISSION);
          if (normDefault.view === "ledger" || normDefault.ledgerTab === DEFAULT_LEDGER_TAB) {
            const rt = parseRouteFromLocation(
              locFromSerialized(serializeRouteToLocation(normDefault, { pathname })),
              { defaultMission: DEFAULT_MISSION }
            );
            if (!deepEqual(rt, normDefault)) {
              routeViolations++;
            }
          }

          // Universal idempotency: parse(serialize(parse(serialize(r)))) === parse(serialize(r))
          const parsedDefault = parseRouteFromLocation(loc, { defaultMission: DEFAULT_MISSION });
          const reserialized = serializeRouteToLocation(parsedDefault, { pathname });
          const reparsed = parseRouteFromLocation(locFromSerialized(reserialized), {
            defaultMission: DEFAULT_MISSION,
          });
          if (!deepEqual(reparsed, parsedDefault) || !deepEqual(normalizeRoute(parsedDefault), parsedDefault)) {
            routeViolations++;
          }

          routeChecks++;
        }
      }
    }
  }
}

// Exhaustive LEGACY_HASH_ALIASES check across hash forms & malicious query params
let aliasChecks = 0;
for (const [aliasKey, target] of Object.entries(LEGACY_HASH_ALIASES)) {
  const expectedView = target.view;
  const expectedTab = target.ledgerTab || DEFAULT_LEDGER_TAB;
  for (const hashForm of [`#${aliasKey}`, `#/${aliasKey}`, `#${aliasKey.toUpperCase()}`]) {
    for (const [search, wantMission, wantClaim] of [
      ["", DEFAULT_MISSION, null],
      ["?mission=p-vs-np&claim=L-rec-005", "p-vs-np", "L-rec-005"],
      ["?mission=../../etc/passwd&claim=<script>alert(1)</script>", DEFAULT_MISSION, null],
    ]) {
      const parsed = parseRouteFromLocation({ hash: hashForm, search }, { defaultMission: DEFAULT_MISSION });
      const expected = { view: expectedView, ledgerTab: expectedTab, mission: wantMission, claim: wantClaim };
      if (!deepEqual(parsed, expected)) routeViolations++;
      const canonicalUrl = serializeRouteToLocation(parsed, { pathname: "/" });
      const roundTripped = parseRouteFromLocation(locFromSerialized(canonicalUrl), {
        defaultMission: DEFAULT_MISSION,
      });
      if (!deepEqual(roundTripped, expected)) routeViolations++;
      aliasChecks++;
    }
  }
}

check(
  routeViolations === 0,
  `URL route round-trip & sanitization across ${routeChecks} grid cases + ${aliasChecks} legacy alias cases`,
  `violations=${routeViolations}`
);
console.log(
  `PASS  URL routes: ${routeChecks} Cartesian round-trips + ${aliasChecks} legacy alias cases verified`
);

// ===========================================================================
// 3. Snapshot Adapter Invariant Check
// ===========================================================================
console.log("\n— 3. Snapshot Adapter Invariant Check —");

let adapterChecks = 0;
let adapterViolations = 0;

function verifyLemma(lemma) {
  try {
    assertAdapterInvariants(lemma);
    adapterChecks++;
  } catch (err) {
    adapterViolations++;
    if (adapterViolations <= 5) console.error("Adapter violation:", err.message, JSON.stringify(lemma));
  }
}

verifyLemma(null);
verifyLemma(undefined);
verifyLemma({});

// 3a. Dense pre-projection + projected record grid
for (const direction of ["min", "max", undefined]) {
  for (const start_target of [null, 0, 12, 46]) {
    for (const bestScore of [null, 10, 45]) {
      for (const provenBound of [null, 9, 46]) {
        for (const litBound of [null, 8, 48]) {
          for (const boundFloor of [null, 5, 50]) {
            for (const closed of [false, true]) {
              for (const contradiction of [false, true]) {
                for (const allow_bound of [true, false, undefined]) {
                  const cfg = {
                    direction,
                    start_target,
                    allow_bound,
                    ...(direction === "max"
                      ? { literature_upper_bound: litBound }
                      : { literature_lower_bound: litBound }),
                    bound_floor: boundFloor,
                    literature_best: 20,
                    unit: "gates",
                  };
                  const rs = {
                    direction,
                    best: bestScore != null ? { score: bestScore, seat: "donor-a", at: "2026-11-23T00:00:00Z" } : null,
                    refuted:
                      provenBound != null
                        ? { score: direction === "max" ? provenBound + 1 : provenBound - 1, inclusive_bound: provenBound }
                        : null,
                    next_target: closed || contradiction ? null : bestScore != null ? bestScore - 1 : start_target,
                    closed: contradiction ? false : closed,
                    contradiction,
                    history: bestScore != null ? [{ kind: "record", score: bestScore, state: "accepted", at: "2026-11-23T00:00:00Z" }] : [],
                  };
                  // Pre-projection fallback state (no seal, no record_meta, no actions)
                  const rawRecord = {
                    id: "R-grid",
                    kind: "record",
                    status: contradiction ? "contradiction" : closed ? "checked" : "conjecture",
                    record: cfg,
                    record_state: rs,
                  };
                  verifyLemma(rawRecord);

                  // Row & geometry invariants
                  const row = recordRowFromLemma(rawRecord, { slug: "sorting-networks", title: "Sorting Networks" });
                  if (!row || (row.gap !== null && row.gap < 0) || (row.closed && row.gap !== 0)) {
                    adapterViolations++;
                  }
                  const geom = boundIntervalGeometry(row);
                  if (geom) {
                    const pctOk = (v) => v === null || (Number.isFinite(v) && v >= 0 && v <= 100);
                    if (!pctOk(geom.currentPct) || !pctOk(geom.boundPct) || !pctOk(geom.literaturePct)) {
                      adapterViolations++;
                    }
                  }
                  if (!Array.isArray(ratchetSeries(row))) adapterViolations++;
                }
              }
            }
          }
        }
      }
    }
  }
}

// 3b. Dense non-record lemma grid (pre-projection + projected)
for (const status of ["conjecture", "in_work", "checked", "refuted", "dead", "contradiction", undefined]) {
  for (const statement_frozen of [false, true]) {
    for (const auditStatus of [null, "faithful", "flagged"]) {
      for (const freshness of [undefined, "fresh", "stale_core", "stale_statement"]) {
        for (const pr_state of [undefined, "none", "open", "passing", "needs_fix"]) {
          for (const explicitSeal of [undefined, "open", "in_work", "provisional", "audited", "frozen", "refuted", "dead", "flagged", "contradiction"]) {
            const isContradiction = status === "contradiction" || explicitSeal === "contradiction";
            const rawLemma = {
              id: "L-grid",
              status: isContradiction ? "contradiction" : status,
              ...(explicitSeal && { seal: explicitSeal }),
              ...(statement_frozen && { checker: { statement_frozen: true, checked_at: "2026-11-23T00:00:00Z" } }),
              ...(auditStatus && { audit: { status: auditStatus } }),
              ...(freshness && { freshness }),
              ...(pr_state && { pr_state }),
              open_prs: pr_state === "open" ? [{ number: 1, url: "https://example.test/pr/1" }] : [],
            };
            verifyLemma(rawLemma);
          }
        }
      }
    }
  }
}

// 3c. Live repository 6-mission snapshots (both projected and stripped pre-projection forms)
{
  const missionsMod = await import(pathToFileURL(path.join(ROOT, "hub", "missions.mjs")).href);
  const siteMod = await import(pathToFileURL(path.join(ROOT, "hub", "build_site.mjs")).href);
  const catalog = missionsMod.loadAllMissionsSummary();
  const slugs = missionsMod.listMissionSlugs();
  const snaps = slugs.map((slug) => siteMod.buildMissionSnapshot(missionsMod.loadMission(slug), null));

  for (const snap of snaps) {
    for (const lemma of snap.lemmas) {
      verifyLemma(lemma);
      // Also strip backend-projected fields to verify fallback derivation on every real claim!
      const { seal: _s, actions: _a, record_meta: _rm, freshness: _f, pr_state: _p, ...unprojected } = lemma;
      verifyLemma(unprojected);
    }
  }

  const synth = synthesizeRecordsPayload(snaps, catalog);
  const norm = normalizeRecordsPayload({
    records: synth.records,
    totals: synth.totals,
    latest_verified: synth.latest_verified,
  });
  check(Boolean(norm && norm.records.length === synth.records.length), "records payload synthesis + lossless normalization");
  for (const snap of snaps) {
    const merged = mergeSnapshotIntoRecords(norm, snap);
    if (!merged || merged.records.length !== norm.records.length) adapterViolations++;
  }
  const hot = pickHotRecords(synth.records, 5);
  if (hot.some((r) => r.closed || r.contradiction)) adapterViolations++;
  const sortedGap = sortRecords(synth.records, "gap").filter((r) => r.gap !== null && !r.closed && !r.contradiction);
  if (!sortedGap.every((r, i) => i === 0 || sortedGap[i - 1].gap <= r.gap)) adapterViolations++;
  if (normalizeRecordRow(null) !== null || normalizeRecordsPayload({ records: "bad" }) !== null) {
    adapterViolations++;
  }
}

check(
  adapterViolations === 0,
  `snapshot adapters verified across ${adapterChecks} lemma/record states (projected + pre-projection + real missions)`,
  `violations=${adapterViolations}`
);
console.log(`PASS  Snapshot adapters: ${adapterChecks} states verified (0 invariant violations)`);

// ===========================================================================
// 4. Negative Mutation Self-Checks
// ===========================================================================
console.log("\n— 4. Negative Mutation Self-Checks —");

function expectThrows(fn, label) {
  let caught = null;
  try {
    fn();
  } catch (err) {
    caught = err;
  }
  check(Boolean(caught), `self-check catches ${label}`, caught ? caught.message : "DID NOT THROW");
}

// Self-check 1: Failed switch wiping activeMission or setting status='error'
{
  let s = initialUIState();
  s = reduceUI(s, { type: "CATALOG_LOADED", mode: "live" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics" });
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: s.transport.reqSeq });
  s = reduceUI(s, { type: "SSE_OPEN", mission: "erdos-combinatorics" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np" });
  const failEv = { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: s.transport.reqSeq, error: "500" };
  const realNext = reduceUI(s, failEv);

  expectThrows(
    () =>
      assertStepInvariants(s, failEv, {
        ...realNext,
        transport: { ...realNext.transport, status: "error" },
      }),
    "mutation #1a: failed switch dropping healthy stream to status='error'"
  );
  expectThrows(
    () =>
      assertStepInvariants(s, failEv, {
        ...realNext,
        transport: { ...realNext.transport, activeMission: "" },
      }),
    "mutation #1b: failed switch wiping committed activeMission"
  );
}

// Self-check 2: Stale MISSION_LOADED mutating state
{
  let s = initialUIState();
  s = reduceUI(s, { type: "CATALOG_LOADED", mode: "live" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics" });
  const staleSeq = s.transport.reqSeq;
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np" });
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "p-vs-np", reqSeq: s.transport.reqSeq });
  const staleEv = { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: staleSeq };

  expectThrows(
    () =>
      assertStepInvariants(s, staleEv, {
        ...s,
        transport: { ...s.transport, activeMission: "erdos-combinatorics" },
        route: { ...s.route, mission: "erdos-combinatorics" },
      }),
    "mutation #2: stale MISSION_LOADED overwriting committed mission"
  );
}

// Self-check 3: Leftover dossier fields on search overlay + cross-mission dossier surviving commit
{
  let s = initialUIState();
  s = reduceUI(s, { type: "CATALOG_LOADED", mode: "live" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics" });
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: s.transport.reqSeq });

  expectThrows(
    () =>
      assertStepInvariants(
        s,
        { type: "OPEN_SEARCH", query: "q" },
        { ...s, overlay: { kind: "search", query: "q", activeIndex: 0, status: "loading", reqSeq: 1 } }
      ),
    "mutation #3a: leftover dossier status/reqSeq on search overlay"
  );

  s = reduceUI(s, { type: "OPEN_DOSSIER", claimId: "E-ram-001", mission: "erdos-combinatorics" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "control", claim: null } });
  const loadEv = { type: "MISSION_LOADED", mission: "p-vs-np", reqSeq: s.transport.reqSeq };
  const validCommit = reduceUI(s, loadEv);
  expectThrows(
    () => assertStepInvariants(s, loadEv, { ...validCommit, overlay: s.overlay }),
    "mutation #3b: cross-mission dossier surviving MISSION_LOADED commit"
  );
}

// Self-check 4: Contradiction & closed records returning can_attempt=true, negative gap, or illegal tone
{
  expectThrows(
    () =>
      assertAdapterInvariants({
        id: "R-bad-1",
        kind: "record",
        seal: "contradiction",
        record: { direction: "min", start_target: 10 },
        record_state: { contradiction: true, closed: false },
        actions: { can_attempt: true, can_bound: false, can_refute: false, can_audit: false, reason: null },
      }),
    "mutation #4a: contradiction record returning can_attempt=true"
  );
  expectThrows(
    () =>
      assertAdapterInvariants({
        id: "R-bad-2",
        kind: "record",
        record: { direction: "min", start_target: 10 },
        record_state: { closed: true, contradiction: false, best: { score: 10 } },
        actions: { can_attempt: false, can_bound: true, can_refute: false, can_audit: false, reason: null },
      }),
    "mutation #4b: closed record returning can_bound=true"
  );
  expectThrows(
    () =>
      assertAdapterInvariants({
        id: "R-bad-3",
        kind: "record",
        record: { direction: "min", start_target: 10 },
        record_state: { closed: false, contradiction: false },
        record_meta: { direction: "min", op: "≤", gap: -3, closed: false, contradiction: false, allow_bound: true },
      }),
    "mutation #4c: negative gap in record_meta"
  );
  // Also verifies real legacy pre-projection discrepancy: status='contradiction' with record_state.contradiction=false
  expectThrows(
    () =>
      assertAdapterInvariants({
        id: "R-legacy-unrepaired",
        kind: "record",
        status: "contradiction",
        record: { direction: "min", start_target: 10 },
        record_state: { contradiction: false, closed: false },
      }),
    "mutation #4d: unprojected legacy record with status='contradiction' & record_state.contradiction=false"
  );
  // Real edge-case reproducer A: closing 'search' or 'attempt' via ESCAPE after route.claim was
  // repopulated mid-overlay (e.g. boot deep-link MISSION_LOADED intent.claim or raw ROUTE_SYNC)
  // leaves route.claim non-null in ui_machine.js:370 — verify our step oracle catches it!
  {
    let s0 = initialUIState({ route: { view: "control", mission: "erdos-combinatorics", claim: "E-ram-001" } });
    s0 = reduceUI(s0, { type: "CATALOG_LOADED", mode: "live" });
    s0 = reduceUI(s0, {
      type: "MISSION_REQUESTED",
      mission: "erdos-combinatorics",
      intent: { view: "control", ledgerTab: "map", claim: "E-ram-001" },
    });
    s0 = reduceUI(s0, { type: "OPEN_SEARCH", query: "" });
    const sMid = reduceUI(s0, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: s0.transport.reqSeq });
    const escEv = { type: "ESCAPE" };
    const sAfterEsc = reduceUI(sMid, escEv);
    expectThrows(
      () => assertStepInvariants(sMid, escEv, sAfterEsc),
      "real edge-case witness: ESCAPE on search after mid-flight deep-link MISSION_LOADED leaves dangling route.claim"
    );
  }
}

console.log("PASS  All negative mutation self-checks caught corrupted transitions & adapter states");

// ===========================================================================
// Summary
// ===========================================================================
console.log(`\nSummary: ${passedChecks} checks passed, ${failedChecks} failed`);
if (failedChecks > 0) {
  process.exit(1);
}
console.log("ALL UI_MACHINE FORMAL VERIFICATION CHECKS PASSED!");
