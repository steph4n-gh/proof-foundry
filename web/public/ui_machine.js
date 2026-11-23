/**
 * web/public/ui_machine.js — Proof Foundry explicit frontend state machine.
 *
 * Pure, zero-dependency ES module. Loaded by the browser (imported from app.js via
 * <script type="module">) AND imported directly by Node tests (hub/test_design_and_ui.mjs).
 * Nothing in here touches window, document, fetch, or EventSource.
 *
 * Three orthogonal finite state machines live in one state object:
 *
 *   transport  boot → live_connecting → live_connected ⇄ live_reconnecting
 *              boot → static_loading → static_ready
 *              any  → error (only while no mission has ever been committed)
 *              A failed mission switch NEVER drops the healthy stream of the
 *              previously committed mission: status/activeMission stay as they were.
 *
 *   route      { view, ledgerTab, mission, claim } — serialisable to/from location.
 *              route.mission only moves when a mission load commits (MISSION_LOADED).
 *
 *   overlay    STRICTLY one of: none | dossier | attempt | search.
 *              Opening any overlay replaces whatever was open. Esc closes it.
 *
 * Out-of-order responses are dropped by sequence number: transport.reqSeq for
 * mission loads, overlay.reqSeq (from the monotonic seq.dossier counter) for dossiers.
 *
 * The second half of the file holds pure snapshot adapters: they read the
 * backend-projected fields (lemma.seal, freshness, pr_state, actions, record_meta)
 * and only fall back to a minimal local derivation for older snapshots.
 */

export const VIEWS = Object.freeze(["missions", "records", "bounties", "control", "ledger"]);
export const LEDGER_TABS = Object.freeze(["map", "leaderboard", "refutations", "fleet", "audit"]);
export const DEFAULT_LEDGER_TAB = "map";
export const DEFAULT_MISSION = "erdos-combinatorics";

/** Backwards-compatible hash aliases from the v2 dashboard (keys are hash heads without the leading mark). */
export const LEGACY_HASH_ALIASES = Object.freeze({
  live: { view: "ledger", ledgerTab: "fleet" },
  fleet: { view: "ledger", ledgerTab: "fleet" },
  map: { view: "ledger", ledgerTab: "map" },
  leaderboard: { view: "ledger", ledgerTab: "leaderboard" },
  graveyard: { view: "ledger", ledgerTab: "refutations" },
  refutations: { view: "ledger", ledgerTab: "refutations" },
  feed: { view: "ledger", ledgerTab: "audit" },
  audit: { view: "ledger", ledgerTab: "audit" },
  hub: { view: "missions" },
  overview: { view: "control" },
});

export const TRANSPORT_STATUSES = Object.freeze([
  "boot",
  "live_connecting",
  "live_connected",
  "live_reconnecting",
  "static_loading",
  "static_ready",
  "error",
]);
export const OVERLAY_KINDS = Object.freeze(["none", "dossier", "attempt", "search"]);
export const HARNESSES = Object.freeze(["claude", "codex", "gemini", "t3"]);
export const QUEUE_MODES = Object.freeze(["single", "mission", "all"]);

const SLUG_RE = /^[a-z0-9][a-z0-9-]{0,63}$/;
const CLAIM_RE = /^[A-Za-z0-9][A-Za-z0-9._-]{0,95}$/;

export function sanitizeSlug(raw) {
  const s = String(raw ?? "").trim();
  return SLUG_RE.test(s) ? s : "";
}
export function sanitizeClaimId(raw) {
  const s = String(raw ?? "").trim();
  return CLAIM_RE.test(s) ? s : null;
}

// ---------------------------------------------------------------------------
// Route
// ---------------------------------------------------------------------------

export function normalizeRoute(route = {}, fallbackMission = "") {
  const view = VIEWS.includes(route.view) ? route.view : "missions";
  const ledgerTab = LEDGER_TABS.includes(route.ledgerTab) ? route.ledgerTab : DEFAULT_LEDGER_TAB;
  const mission = sanitizeSlug(route.mission) || sanitizeSlug(fallbackMission) || "";
  const claim = sanitizeClaimId(route.claim);
  return { view, ledgerTab, mission, claim };
}

function routesEqual(a, b) {
  return a.view === b.view && a.ledgerTab === b.ledgerTab && a.mission === b.mission && a.claim === b.claim;
}

/**
 * Parse { hash, search } (a Location or any object with those fields) into a route.
 * Accepted hash forms: #missions #records #bounties #control #ledger #ledger/<tab>
 * plus legacy aliases (#live, #map, #leaderboard, #graveyard, #feed …).
 */
export function parseRouteFromLocation(loc = {}, { defaultMission = DEFAULT_MISSION } = {}) {
  const rawHash = String(loc.hash ?? "").replace(/^#\/?/, "").trim().toLowerCase();
  const params = new URLSearchParams(String(loc.search ?? "").replace(/^\?/, ""));
  const missionParam = sanitizeSlug(params.get("mission"));
  const claim = sanitizeClaimId(params.get("claim"));
  const [head = "", sub = ""] = rawHash.split("/");

  let view = "missions";
  let ledgerTab = DEFAULT_LEDGER_TAB;
  if (!head) {
    view = missionParam ? "control" : "missions";
  } else if (VIEWS.includes(head)) {
    view = head;
    if (head === "ledger" && LEDGER_TABS.includes(sub)) ledgerTab = sub;
  } else if (Object.prototype.hasOwnProperty.call(LEGACY_HASH_ALIASES, head)) {
    const alias = LEGACY_HASH_ALIASES[head];
    view = alias.view;
    if (alias.ledgerTab) ledgerTab = alias.ledgerTab;
  }
  return normalizeRoute({ view, ledgerTab, mission: missionParam || defaultMission, claim });
}

/** Serialise a route to "<pathname>?mission=…&claim=…#view[/tab]". */
export function serializeRouteToLocation(route, { pathname = "/" } = {}) {
  const r = normalizeRoute(route);
  const params = new URLSearchParams();
  if (r.mission) params.set("mission", r.mission);
  if (r.claim) params.set("claim", r.claim);
  const qs = params.toString();
  const hash = r.view === "ledger" ? `ledger/${r.ledgerTab}` : r.view;
  return `${pathname}${qs ? `?${qs}` : ""}#${hash}`;
}

// ---------------------------------------------------------------------------
// Initial state
// ---------------------------------------------------------------------------

export function initialTransport() {
  return {
    status: "boot",
    mode: "unknown",
    reqSeq: 0,
    activeMission: "",
    pendingMission: null,
    pendingIntent: null,
    error: null,
  };
}

export const NO_OVERLAY = Object.freeze({ kind: "none" });

export function initialUIState({ route = {}, defaultMission = DEFAULT_MISSION } = {}) {
  return {
    transport: initialTransport(),
    route: normalizeRoute(route, defaultMission),
    overlay: NO_OVERLAY,
    seq: { dossier: 0 },
  };
}

// ---------------------------------------------------------------------------
// Sub-reducers (each returns the same reference when nothing changes)
// ---------------------------------------------------------------------------

function patch(obj, changes) {
  for (const k of Object.keys(changes)) {
    if (obj[k] !== changes[k]) return { ...obj, ...changes };
  }
  return obj;
}

function reduceTransport(t, ev) {
  switch (ev.type) {
    case "CATALOG_LOADED": {
      const mode = ev.mode === "static" ? "static" : "live";
      return patch(t, { mode, status: mode === "static" ? "static_loading" : "live_connecting", error: null });
    }
    case "CATALOG_FAILED":
      return patch(t, { status: "error", error: String(ev.error || "Catalog unavailable") });
    case "MISSION_REQUESTED": {
      const mission = sanitizeSlug(ev.mission);
      if (!mission) return t;
      const next = {
        ...t,
        reqSeq: t.reqSeq + 1,
        pendingMission: mission,
        pendingIntent: ev.intent && typeof ev.intent === "object" ? { ...ev.intent } : null,
      };
      // Only show a loading status when nothing is committed yet; a healthy stream stays healthy.
      if (!t.activeMission) {
        next.status = t.mode === "static" ? "static_loading" : t.mode === "live" ? "live_connecting" : t.status;
      }
      return next;
    }
    case "MISSION_LOADED": {
      if (ev.reqSeq !== t.reqSeq) return t; // stale / out-of-order response
      const mission = sanitizeSlug(ev.mission);
      if (!mission) return t;
      return {
        ...t,
        activeMission: mission,
        pendingMission: null,
        pendingIntent: null,
        error: null,
        status: t.mode === "static" ? "static_ready" : "live_connecting",
      };
    }
    case "MISSION_FAILED": {
      if (ev.reqSeq !== t.reqSeq) return t;
      return {
        ...t,
        pendingMission: null,
        pendingIntent: null,
        error: String(ev.error || "Mission failed to load"),
        // Keep the previous healthy status (and its stream) when a mission is already committed.
        status: t.activeMission ? t.status : "error",
      };
    }
    case "SSE_OPEN":
    case "SSE_SNAPSHOT":
      if (t.mode !== "live" || ev.mission !== t.activeMission) return t;
      return patch(t, { status: "live_connected" });
    case "SSE_ERROR":
      if (t.mode !== "live" || ev.mission !== t.activeMission) return t;
      return patch(t, { status: "live_reconnecting" });
    case "DISMISS_ERROR":
      return patch(t, { error: null });
    case "RETRY":
      if (t.status !== "error") return patch(t, { error: null });
      return { ...t, status: "boot", mode: t.activeMission ? t.mode : "unknown", error: null };
    default:
      return t;
  }
}

function clampIndex(i, count) {
  if (!count || count <= 0) return 0;
  return ((i % count) + count) % count;
}

function reduceOverlay(o, ev, seq) {
  switch (ev.type) {
    case "OPEN_DOSSIER": {
      const claimId = sanitizeClaimId(ev.claimId);
      if (!claimId) return { overlay: o, seq };
      const nextSeq = { ...seq, dossier: seq.dossier + 1 };
      return {
        overlay: {
          kind: "dossier",
          claimId,
          mission: sanitizeSlug(ev.mission),
          status: "loading",
          reqSeq: nextSeq.dossier,
          data: null,
          error: null,
        },
        seq: nextSeq,
      };
    }
    case "DOSSIER_LOADED":
      if (o.kind !== "dossier" || ev.reqSeq !== o.reqSeq) return { overlay: o, seq };
      return { overlay: { ...o, status: "ready", data: ev.data ?? null, error: null }, seq };
    case "DOSSIER_FAILED":
      if (o.kind !== "dossier" || ev.reqSeq !== o.reqSeq) return { overlay: o, seq };
      return { overlay: { ...o, status: "error", data: null, error: String(ev.error || "Failed to load") }, seq };
    case "OPEN_ATTEMPT": {
      const claimId = sanitizeClaimId(ev.claimId);
      if (!claimId) return { overlay: o, seq };
      return {
        overlay: {
          kind: "attempt",
          claimId,
          mission: sanitizeSlug(ev.mission),
          harness: HARNESSES.includes(ev.harness) ? ev.harness : "claude",
          handle: String(ev.handle ?? "").slice(0, 39),
          queueMode: QUEUE_MODES.includes(ev.queueMode) ? ev.queueMode : "single",
          recKind: ev.recKind === "record_bound" ? "record_bound" : "record",
          recScore: ev.recScore ?? null,
        },
        seq,
      };
    }
    case "ATTEMPT_UPDATE": {
      if (o.kind !== "attempt") return { overlay: o, seq };
      const p = ev.patch || {};
      const changes = {};
      if (p.harness !== undefined && HARNESSES.includes(p.harness)) changes.harness = p.harness;
      if (p.handle !== undefined) changes.handle = String(p.handle).slice(0, 39);
      if (p.queueMode !== undefined && QUEUE_MODES.includes(p.queueMode)) changes.queueMode = p.queueMode;
      if (p.recKind !== undefined) changes.recKind = p.recKind === "record_bound" ? "record_bound" : "record";
      if (p.recScore !== undefined) changes.recScore = p.recScore;
      return { overlay: patch(o, changes), seq };
    }
    case "OPEN_SEARCH":
      return { overlay: { kind: "search", query: String(ev.query ?? ""), activeIndex: 0 }, seq };
    case "SEARCH_QUERY":
      if (o.kind !== "search") return { overlay: o, seq };
      return { overlay: patch(o, { query: String(ev.query ?? ""), activeIndex: 0 }), seq };
    case "SEARCH_MOVE":
      if (o.kind !== "search") return { overlay: o, seq };
      return { overlay: patch(o, { activeIndex: clampIndex(o.activeIndex + (Number(ev.delta) || 0), Number(ev.count) || 0) }), seq };
    case "SEARCH_SET_INDEX":
      if (o.kind !== "search") return { overlay: o, seq };
      return { overlay: patch(o, { activeIndex: clampIndex(Number(ev.index) || 0, Number(ev.count) || 0) }), seq };
    case "CLOSE_OVERLAY":
    case "ESCAPE":
      return { overlay: o.kind === "none" ? o : NO_OVERLAY, seq };
    default:
      return { overlay: o, seq };
  }
}

// ---------------------------------------------------------------------------
// Root reducer
// ---------------------------------------------------------------------------

export function reduceUI(state, ev) {
  if (!ev || typeof ev.type !== "string") return state;
  const transport = reduceTransport(state.transport, ev);
  let { overlay, seq } = reduceOverlay(state.overlay, ev, state.seq);
  let route = state.route;

  switch (ev.type) {
    case "ROUTE_NAVIGATE": {
      const p = ev.route || {};
      const next = normalizeRoute(
        {
          view: p.view ?? route.view,
          ledgerTab: p.ledgerTab ?? route.ledgerTab,
          mission: route.mission, // missions only move through MISSION_LOADED
          claim: p.claim !== undefined ? p.claim : route.claim,
        },
        route.mission
      );
      route = routesEqual(next, route) ? route : next;
      break;
    }
    case "ROUTE_SYNC": {
      // From popstate / hashchange. Mission is left alone; the app requests it if it differs.
      const p = normalizeRoute(ev.route || {}, route.mission);
      const next = { ...p, mission: route.mission };
      route = routesEqual(next, route) ? route : next;
      if (!next.claim && overlay.kind === "dossier") overlay = NO_OVERLAY;
      break;
    }
    case "MISSION_LOADED": {
      if (transport === state.transport) break; // ignored (stale)
      const intent = state.transport.pendingIntent || {};
      const next = normalizeRoute(
        {
          view: intent.view ?? route.view,
          ledgerTab: intent.ledgerTab ?? route.ledgerTab,
          mission: transport.activeMission,
          claim: intent.claim !== undefined ? intent.claim : route.claim,
        },
        transport.activeMission
      );
      route = routesEqual(next, route) ? route : next;
      // A dossier/attempt bound to another mission cannot survive a committed switch,
      // unless the intent explicitly deep-links into that claim.
      if ((overlay.kind === "dossier" || overlay.kind === "attempt") && overlay.mission && overlay.mission !== transport.activeMission) {
        overlay = NO_OVERLAY;
      }
      break;
    }
    default:
      break;
  }

  // route.claim mirrors an open dossier of the routed mission; other overlays clear it.
  // (Route-driven events own the claim themselves: MISSION_LOADED intent / ROUTE_SYNC.)
  const routeOwnsClaim = ev.type === "MISSION_LOADED" || ev.type === "ROUTE_SYNC";
  if (overlay !== state.overlay && !routeOwnsClaim) {
    let claim = route.claim;
    if (overlay.kind === "dossier") claim = !overlay.mission || overlay.mission === route.mission ? overlay.claimId : null;
    else if (state.overlay.kind === "dossier" || overlay.kind !== "none") claim = null;
    if (claim !== route.claim) route = { ...route, claim };
  }

  if (transport === state.transport && route === state.route && overlay === state.overlay && seq === state.seq) return state;
  return { transport, route, overlay, seq };
}

/** True when an SSE snapshot for `mission` should be applied to the visible state. */
export function acceptsSnapshot(state, mission) {
  const t = state.transport;
  return t.mode === "live" && Boolean(mission) && mission === t.activeMission;
}

/** True when a mission fetch issued with `reqSeq` is still the latest request. */
export function isCurrentMissionRequest(state, reqSeq) {
  return state.transport.reqSeq === reqSeq;
}

export function createUIMachine(initial = initialUIState()) {
  let state = initial;
  const listeners = new Set();
  return {
    getState: () => state,
    dispatch(event) {
      const prev = state;
      const next = reduceUI(prev, event);
      if (next === prev) return prev;
      state = next;
      for (const fn of [...listeners]) {
        try {
          fn(next, prev, event);
        } catch (err) {
          // A broken listener must never wedge the machine.
          if (typeof console !== "undefined") console.error(err);
        }
      }
      return next;
    },
    subscribe(fn) {
      listeners.add(fn);
      return () => listeners.delete(fn);
    },
  };
}

// ===========================================================================
// Snapshot adapters (pure). Prefer backend-projected fields; fall back minimally.
// ===========================================================================

const num = (v) => (typeof v === "number" && Number.isFinite(v) ? v : v != null && v !== "" && Number.isFinite(Number(v)) ? Number(v) : null);

export function sealOf(lemma) {
  if (!lemma) return "open";
  if (typeof lemma.seal === "string" && lemma.seal) return lemma.seal;
  // Minimal fallback for pre-projection snapshots.
  if (lemma.status === "contradiction" || lemma.record_state?.contradiction) return "contradiction";
  if (lemma.kind === "record") return lemma.record_state?.closed ? "frozen" : lemma.record_state?.best ? "record" : "open";
  if (lemma.audit?.status === "flagged") return "flagged";
  if (lemma.status === "checked") {
    if (lemma.checker?.statement_frozen) return "frozen";
    return lemma.audit?.status === "faithful" ? "audited" : "provisional";
  }
  if (["refuted", "dead", "in_work"].includes(lemma.status)) return lemma.status;
  return "open";
}

export function freshnessOf(lemma) {
  const f = lemma?.freshness;
  return f === "stale_statement" || f === "stale_core" ? f : "fresh";
}

export function prStateOf(lemma) {
  const p = lemma?.pr_state;
  if (p === "none" || p === "open" || p === "passing" || p === "needs_fix") return p;
  return (lemma?.open_prs || []).length ? "open" : "none";
}

export function recordMetaOf(lemma) {
  if (!lemma || lemma.kind !== "record") return null;
  const cfg = lemma.record || {};
  const rs = lemma.record_state || {};
  const rm = lemma.record_meta && typeof lemma.record_meta === "object" ? lemma.record_meta : null;
  const direction = (rm?.direction || cfg.direction || rs.direction) === "max" ? "max" : "min";
  const literatureBound = direction === "max" ? cfg.literature_upper_bound : cfg.literature_lower_bound;
  const base = {
    direction,
    op: direction === "max" ? "≥" : "≤",
    unit: cfg.unit || "",
    start_target: num(cfg.start_target),
    best_score: num(rs.best?.score),
    best_seat: rs.best?.seat || null,
    best_at: rs.best?.at || null,
    next_target: num(rs.next_target ?? cfg.start_target),
    proven_bound: num(rs.refuted?.inclusive_bound),
    literature_best: num(cfg.literature_best),
    literature_bound: num(literatureBound),
    bound_floor: num(cfg.bound_floor),
    score_max: num(cfg.score_max),
    gap: null,
    closed: Boolean(rs.closed),
    contradiction: Boolean(rs.contradiction),
    allow_bound: cfg.allow_bound !== false,
    artifact_ext: cfg.artifact_ext || ".lean",
    file_stem: cfg.file_stem || null,
    claims_dir: cfg.claims_dir || null,
    theorem_template: cfg.theorem_template || null,
  };
  const merged = rm ? { ...base, ...rm, direction, op: rm.op || base.op } : base;
  merged.history = Array.isArray(rm?.history) ? rm.history : Array.isArray(rs.history) ? rs.history : [];
  merged.refuted_score = num(rs.refuted?.score) ?? refutedScoreFromBound(merged);
  if (merged.gap == null) merged.gap = computeGap(merged);
  return merged;
}

function refutedScoreFromBound(rm) {
  if (rm.proven_bound == null) return null;
  return rm.direction === "max" ? rm.proven_bound + 1 : rm.proven_bound - 1;
}

export function computeGap(rm) {
  if (!rm) return null;
  if (rm.closed) return 0;
  const cur = num(rm.best_score) ?? num(rm.start_target);
  const ref = num(rm.proven_bound) ?? num(rm.literature_bound) ?? num(rm.bound_floor);
  if (cur == null || ref == null) return null;
  return Math.max(0, rm.direction === "max" ? ref - cur : cur - ref);
}

export function actionsOf(lemma) {
  if (!lemma) return { can_attempt: false, can_bound: false, can_refute: false, can_audit: false, reason: "missing" };
  const a = lemma.actions;
  if (a && typeof a === "object" && typeof a.can_attempt === "boolean") {
    return { can_bound: false, can_refute: false, can_audit: false, reason: null, ...a };
  }
  if (lemma.kind === "record") {
    const rm = recordMetaOf(lemma);
    const live = !rm.closed && !rm.contradiction;
    return {
      can_attempt: live,
      can_bound: live && rm.allow_bound,
      can_refute: false,
      can_audit: false,
      reason: rm.contradiction ? "contradiction" : rm.closed ? "closed" : null,
    };
  }
  const open = lemma.status === "conjecture" || lemma.status === "in_work";
  const seal = sealOf(lemma);
  return {
    can_attempt: open,
    can_bound: false,
    can_refute: open,
    can_audit: seal === "provisional",
    reason: open ? null : `status:${lemma.status || "unknown"}`,
  };
}

export const isAttemptable = (lemma) => actionsOf(lemma).can_attempt === true;

/**
 * Shape-first two-hue status grammar. Returns { key, glyph, label, tone } where tone is
 * one of "muted" | "ink" | "accent" | "alarm" | "struck". Only "accent" and "alarm" carry hue.
 */
export function statusOf(lemma) {
  const seal = sealOf(lemma);
  if (seal === "contradiction") return { key: "contradiction", glyph: "⛔", label: "Contradiction", tone: "alarm" };
  if (seal === "flagged") return { key: "flagged", glyph: "⚠", label: "Flagged", tone: "alarm" };
  if (lemma?.kind === "record") {
    const rm = recordMetaOf(lemma);
    if (rm.closed) return { key: "frozen", glyph: "◆", label: "Optimal", tone: "accent" };
    if (rm.best_score != null) return { key: "record", glyph: "♛", label: `Record ${rm.best_score} · next ${rm.op} ${rm.next_target}`, tone: "accent" };
    return { key: "hunt", glyph: "♛", label: `Open hunt · ${rm.op} ${rm.next_target ?? rm.start_target}`, tone: "ink" };
  }
  switch (seal) {
    case "frozen":
      return { key: "frozen", glyph: "◆", label: "Frozen", tone: "accent" };
    case "audited":
      return { key: "audited", glyph: "◆", label: "Audited", tone: "accent" };
    case "provisional":
      return { key: "provisional", glyph: "◇", label: "Provisional", tone: "ink" };
    case "refuted":
      return { key: "refuted", glyph: "✕", label: "Refuted", tone: "ink" };
    case "dead":
      return { key: "dead", glyph: "—", label: "Barrier", tone: "struck" };
    case "in_work":
      return { key: "in_work", glyph: "◐", label: "In work", tone: "ink" };
    default:
      return { key: "open", glyph: "○", label: "Open", tone: "muted" };
  }
}

// ---------------------------------------------------------------------------
// Records board rows
// ---------------------------------------------------------------------------

export function recordRowFromLemma(lemma, mission = {}) {
  const rm = recordMetaOf(lemma);
  if (!rm) return null;
  return {
    mission: mission.slug || lemma.mission || "",
    mission_title: mission.title || lemma.mission_title || "",
    id: lemma.id,
    title: lemma.title || lemma.id,
    statement_file: lemma.statement_file || null,
    statement_def: lemma.statement_def || null,
    direction: rm.direction,
    op: rm.op,
    unit: rm.unit,
    start_target: rm.start_target,
    best_score: rm.best_score,
    best_seat: rm.best_seat,
    best_at: rm.best_at,
    next_target: rm.next_target,
    proven_bound: rm.proven_bound,
    literature_best: rm.literature_best,
    literature_bound: rm.literature_bound,
    bound_floor: rm.bound_floor,
    gap: rm.gap,
    closed: rm.closed,
    contradiction: rm.contradiction,
    allow_bound: rm.allow_bound,
    artifact_ext: rm.artifact_ext,
    open_prs: lemma.open_prs || [],
    history: rm.history || [],
  };
}

export function normalizeRecordRow(r) {
  if (!r || typeof r !== "object" || !r.id) return null;
  const direction = r.direction === "max" ? "max" : "min";
  const row = {
    mission: String(r.mission || ""),
    mission_title: String(r.mission_title || r.mission || ""),
    id: String(r.id),
    title: String(r.title || r.id),
    statement_file: r.statement_file || null,
    statement_def: r.statement_def || null,
    direction,
    op: r.op || (direction === "max" ? "≥" : "≤"),
    unit: r.unit || "",
    start_target: num(r.start_target),
    best_score: num(r.best_score),
    best_seat: r.best_seat || null,
    best_at: r.best_at || null,
    next_target: num(r.next_target ?? r.start_target),
    proven_bound: num(r.proven_bound),
    literature_best: num(r.literature_best),
    literature_bound: num(r.literature_bound),
    bound_floor: num(r.bound_floor),
    gap: num(r.gap),
    closed: Boolean(r.closed),
    contradiction: Boolean(r.contradiction),
    allow_bound: r.allow_bound !== false,
    artifact_ext: r.artifact_ext || ".lean",
    open_prs: Array.isArray(r.open_prs) ? r.open_prs : [],
    history: Array.isArray(r.history) ? r.history : [],
  };
  if (row.gap == null) row.gap = computeGap(row);
  return row;
}

/** Validate a /api/records or records.json payload. Returns null when unusable. */
export function normalizeRecordsPayload(raw) {
  if (!raw || typeof raw !== "object" || !Array.isArray(raw.records)) return null;
  const records = raw.records.map(normalizeRecordRow).filter(Boolean);
  return {
    generated_at: raw.generated_at || null,
    totals: raw.totals && typeof raw.totals === "object" ? raw.totals : null,
    latest_verified: raw.latest_verified && raw.latest_verified.id ? raw.latest_verified : null,
    records,
    synthesized: false,
  };
}

function lemmaVerifiedAt(l) {
  return l?.checker?.checked_at || l?.audit?.at || l?.updated_at || "";
}

export function latestVerifiedFromSnapshots(snapshots = []) {
  let best = null;
  for (const snap of snapshots) {
    if (!snap?.lemmas) continue;
    for (const l of snap.lemmas) {
      if (l.kind === "record" || l.status !== "checked") continue;
      const seal = sealOf(l);
      if (seal !== "frozen" && seal !== "audited") continue;
      const at = lemmaVerifiedAt(l);
      if (!best || at > best.at) {
        best = {
          mission: snap.mission?.slug || "",
          mission_title: snap.mission?.title || "",
          id: l.id,
          title: l.title,
          statement: l.verified_signature || l.registered_statement || l.statement || "",
          seal,
          judge_label: l.checker?.lean_version || snap.mission?.judge?.label || "",
          by_seat: l.checker?.by_seat || null,
          at,
          file: l.lean_file || null,
        };
      }
    }
  }
  return best;
}

export function synthesizeRecordsPayload(snapshots = [], catalog = []) {
  const records = [];
  for (const snap of snapshots) {
    if (!snap?.lemmas) continue;
    for (const l of snap.lemmas) {
      if (l.kind !== "record") continue;
      const row = recordRowFromLemma(l, snap.mission || {});
      if (row) records.push(row);
    }
  }
  const sum = (k) => catalog.reduce((acc, m) => acc + (Number(m?.counts?.[k]) || 0), 0);
  return {
    generated_at: null,
    totals: catalog.length
      ? {
          missions: catalog.length,
          checked_total: sum("checked"),
          trusted_proofs: sum("trusted"),
          refuted: sum("refuted"),
          barriers: sum("dead"),
          records_active: records.filter((r) => !r.closed && !r.contradiction).length,
          records_closed: records.filter((r) => r.closed).length,
        }
      : null,
    latest_verified: latestVerifiedFromSnapshots(snapshots),
    records,
    synthesized: true,
  };
}

/** Replace a mission's rows with rows derived from a fresher snapshot (keeps order stable by id). */
export function mergeSnapshotIntoRecords(payload, snap) {
  if (!payload || !snap?.mission?.slug) return payload;
  const slug = snap.mission.slug;
  const fresh = (snap.lemmas || []).filter((l) => l.kind === "record").map((l) => recordRowFromLemma(l, snap.mission));
  if (!fresh.length) return payload;
  const freshById = new Map(fresh.map((r) => [r.id, r]));
  const kept = payload.records.map((r) => (r.mission === slug && freshById.has(r.id) ? freshById.get(r.id) : r));
  for (const r of fresh) if (!kept.some((k) => k.mission === slug && k.id === r.id)) kept.push(r);
  return { ...payload, records: kept };
}

export function filterRecords(rows, { mission = "all", direction = "all" } = {}) {
  return rows.filter((r) => (mission === "all" || r.mission === mission) && (direction === "all" || r.direction === direction));
}

function lastRatchetAt(r) {
  let at = r.best_at || "";
  for (const h of r.history || []) if (h?.state === "accepted" && (h.at || "") > at) at = h.at || "";
  return at;
}

export function sortRecords(rows, sort = "gap") {
  const out = [...rows];
  const gapKey = (r) => (r.closed || r.contradiction ? Infinity : r.gap == null ? 1e12 : r.gap);
  const byMission = (a, b) => a.mission.localeCompare(b.mission) || a.id.localeCompare(b.id);
  if (sort === "recent") {
    out.sort((a, b) => lastRatchetAt(b).localeCompare(lastRatchetAt(a)) || gapKey(a) - gapKey(b) || byMission(a, b));
  } else if (sort === "mission") {
    out.sort(byMission);
  } else {
    out.sort((a, b) => gapKey(a) - gapKey(b) || (b.best_score != null) - (a.best_score != null) || byMission(a, b));
  }
  return out;
}

export function pickHotRecords(rows, n = 5) {
  return sortRecords(rows.filter((r) => !r.closed && !r.contradiction), "gap").slice(0, n);
}

/** Geometry for the bound-interval bar, as percentages of the track. */
export function boundIntervalGeometry(r) {
  const cur = num(r.best_score) ?? num(r.start_target);
  const proven = num(r.proven_bound);
  const bound = proven ?? num(r.literature_bound) ?? num(r.bound_floor);
  const lit = num(r.literature_best);
  const vals = [cur, bound, lit, num(r.start_target)].filter((v) => v != null);
  if (!vals.length) return null;
  let lo = Math.min(...vals);
  let hi = Math.max(...vals);
  const pad = Math.max(1, (hi - lo) * 0.14);
  lo -= pad;
  hi += pad;
  const pct = (v) => (v == null ? null : Math.round(((v - lo) / (hi - lo)) * 1000) / 10);
  const a = cur != null && bound != null ? Math.min(pct(cur), pct(bound)) : null;
  const b = cur != null && bound != null ? Math.max(pct(cur), pct(bound)) : null;
  return {
    lo,
    hi,
    current: cur,
    currentPct: pct(cur),
    bound,
    boundPct: pct(bound),
    boundProven: proven != null,
    literature: lit,
    literaturePct: lit != null && lit !== cur ? pct(lit) : null,
    gapLeftPct: a,
    gapWidthPct: a != null ? Math.max(0, b - a) : null,
  };
}

/** Points for a step-chart sparkline of accepted ratchets: [{t, score}] ascending by time. */
export function ratchetSeries(r) {
  const pts = (r.history || [])
    .filter((h) => h && (h.state === "accepted" || h.state == null) && (h.kind ?? "record") === "record" && num(h.score) != null)
    .map((h, i) => ({ t: h.at || h.git_ts || String(i).padStart(6, "0"), score: num(h.score) }))
    .sort((a, b) => String(a.t).localeCompare(String(b.t)));
  if (!pts.length && r.best_score != null) pts.push({ t: r.best_at || "", score: r.best_score });
  return pts;
}

export function toRoman(n) {
  const map = [
    [1000, "M"], [900, "CM"], [500, "D"], [400, "CD"], [100, "C"], [90, "XC"],
    [50, "L"], [40, "XL"], [10, "X"], [9, "IX"], [5, "V"], [4, "IV"], [1, "I"],
  ];
  let x = Math.max(0, Math.floor(Number(n) || 0));
  let out = "";
  for (const [v, s] of map) while (x >= v) { out += s; x -= v; }
  return out;
}

/** Pure continuous-queue loop instructions appended to the Attempt prompt when queueMode != "single". */
export function buildLoopSuffix({ slug, lemmaId, handle, queueMode, repo = "steph4n-gh/proof-foundry", missionCount = null }) {
  if (queueMode !== "mission" && queueMode !== "all") return "";
  const nextScope = queueMode === "all" ? "all" : slug;
  const scopeLabel = queueMode === "all" ? (missionCount ? `all ${missionCount} missions` : "all missions") : `mission ${slug}`;
  return [
    ``,
    `Continuous queue mode (${scopeLabel} — keep going task after task):`,
    `Track every claim ID you submit or skip this session (starting with "${lemmaId}"). Do NOT rely on a shell variable like $DONE across commands (each shell call may start fresh) — pass the literal comma-separated list to \`--exclude\` (or append one ID per line to \`$(git rev-parse --git-path fleet-exclude)\` and pass \`--exclude-file\`).`,
    `Fork note: if you are working in a fork, add \`upstream\` (\`git remote add upstream https://github.com/${repo}.git\`), fetch/branch off \`upstream/main\`, push branches to \`origin\`, and open PRs with \`gh pr create --repo ${repo}\`.`,
    `After opening the PR above, repeat:`,
    `A. Clean any state/event edits left by local verification and confirm a clean tree before switching branches:`,
    `   git restore --worktree --staged -- missions/*/state.json missions/*/events.ndjson && git status --porcelain`,
    `B. Refresh and check out latest main so \`fleet next\` sees newly merged submissions, then ask the queue for the next unclaimed problem (passing all session IDs literally):`,
    `   git fetch upstream main 2>/dev/null || git fetch origin main`,
    `   git checkout --detach upstream/main 2>/dev/null || git checkout --detach origin/main`,
    `   node hub/fleet.mjs next --mission ${nextScope} --exclude "${lemmaId}"  # append each completed/skipped ID`,
    `C. If \`claim\` is null, summarize every PR you opened and stop.`,
    `D. Otherwise create a fresh branch (\`donor/<next-id>-${handle}\`) directly off \`upstream/main\` (or \`origin/main\`): \`git checkout -B donor/<next-id>-${handle} upstream/main 2>/dev/null || git checkout -B donor/<next-id>-${handle} origin/main\`. Follow the returned \`instructions\`, verify locally with \`node hub/fleet.mjs ... --seat donor-${handle} --export\`, revert state/event files, commit ONLY the new artifact + submission JSON, push, open a clean PR against \`${repo}\`, add the ID to your \`--exclude\` list, and repeat.`,
    `E. If a problem hits a genuine mathematical roadblock after serious effort, do NOT cheat or leave dirty files — discard scratch changes, add its ID to your \`--exclude\` list, and move straight to the next problem.`,
  ].join("\n");
}
