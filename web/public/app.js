/* PROOF FOUNDRY v3 — "Proceedings" frontend.
 *
 * All UI state (transport, route, overlay) lives in the explicit state machine in
 * ./ui_machine.js. This module only:
 *   1. performs side effects (fetch, EventSource, history, clipboard, localStorage),
 *   2. holds fetched *data* (catalog, snapshots, records), and
 *   3. renders DOM from machine state + data.
 * Status, freshness, PR state, actions and record metadata come from the backend
 * projection (lemma.seal / freshness / pr_state / actions / record_meta) via the
 * adapters in ui_machine.js.
 */
import {
  DEFAULT_MISSION,
  NO_OVERLAY,
  createUIMachine,
  initialUIState,
  parseRouteFromLocation,
  serializeRouteToLocation,
  acceptsSnapshot,
  isCurrentMissionRequest,
  sealOf,
  statusOf,
  freshnessOf,
  prStateOf,
  actionsOf,
  isAttemptable,
  recordMetaOf,
  recordRowFromLemma,
  normalizeRecordsPayload,
  synthesizeRecordsPayload,
  mergeSnapshotIntoRecords,
  latestVerifiedFromSnapshots,
  filterRecords,
  sortRecords,
  pickHotRecords,
  boundIntervalGeometry,
  ratchetSeries,
  toRoman,
} from "./ui_machine.js";

// ---------------------------------------------------------------- helpers
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => Array.from(document.querySelectorAll(sel));
const DEFAULT_REPO = "steph4n-gh/proof-foundry";

function esc(s) {
  return String(s ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}
function int(v) {
  const n = Number(v);
  return Number.isFinite(n) ? Math.round(n) : 0;
}
function relTime(iso) {
  if (!iso) return "";
  const t = new Date(iso).getTime();
  if (!Number.isFinite(t)) return "";
  const diff = Math.max(0, Math.floor((Date.now() - t) / 1000));
  if (diff < 10) return "just now";
  if (diff < 60) return `${diff}s ago`;
  if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
  if (diff < 86400) return `${Math.floor(diff / 3600)}h ago`;
  return `${Math.floor(diff / 86400)}d ago`;
}
function longDate(iso) {
  const d = iso ? new Date(iso) : new Date();
  if (!Number.isFinite(d.getTime())) return "";
  return d.toLocaleDateString("en-US", { year: "numeric", month: "long", day: "numeric" });
}
function storageGet(key, fallback = "") {
  try {
    return window.localStorage.getItem(key) ?? fallback;
  } catch {
    return fallback;
  }
}
function storageSet(key, value) {
  try {
    window.localStorage.setItem(key, value);
  } catch {
    /* private mode */
  }
}
function showToast(msg) {
  const t = $("#toast");
  t.textContent = msg;
  t.hidden = false;
  clearTimeout(showToast._tm);
  showToast._tm = setTimeout(() => (t.hidden = true), 2600);
}
function isTyping() {
  const el = document.activeElement;
  if (!el) return false;
  return el.tagName === "INPUT" || el.tagName === "TEXTAREA" || el.tagName === "SELECT" || el.isContentEditable;
}
async function fetchJSON(url) {
  const res = await fetch(url, { headers: { Accept: "application/json" } });
  if (!res.ok) throw new Error(`HTTP ${res.status}`);
  const type = res.headers.get("content-type") || "";
  if (!type.includes("json")) throw new Error("not JSON");
  return res.json();
}
function cleanRecordTitle(t) {
  return String(t || "")
    .replace(/^King of the Hill(?:\s*\([^)]*\))?:\s*/i, "")
    .replace(/\s*\((?=[^)]*=)[^)]*\)\s*$/, "");
}
function shortLean(label) {
  const m = String(label || "").match(/Lean\D{0,12}(4\.\d+)/i);
  return m ? `Lean ${m[1]}` : label || "Judge";
}

// ------------------------------------------------------------------ theme
function applyTheme(theme) {
  const t = theme === "dark" ? "dark" : "light";
  document.documentElement.setAttribute("data-theme", t);
  $("#theme-paper").setAttribute("aria-pressed", String(t === "light"));
  $("#theme-night").setAttribute("aria-pressed", String(t === "dark"));
  if (isMapVisible()) drawMap();
}
$$("[data-theme-set]").forEach((b) =>
  b.addEventListener("click", () => {
    storageSet("pf-theme-v3", b.dataset.themeSet);
    applyTheme(b.dataset.themeSet);
  })
);

// ------------------------------------------------------- machine + data
const machine = createUIMachine(
  initialUIState({ route: parseRouteFromLocation(window.location, { defaultMission: DEFAULT_MISSION }) })
);
const dispatch = (ev) => machine.dispatch(ev);
const ui = () => machine.getState();

let CATALOG = []; // /api/missions summaries
let STATE = null; // committed snapshot of transport.activeMission
let RECORDS = null; // normalized records payload (all missions)
const SNAP_CACHE = new Map(); // slug -> snapshot (read-only data for cross-mission lookups)
let SSE = null; // { es, slug }
let PENDING_PUSH = false;
let LAST_FAILED_MISSION = null;
let FOCUS_RETURN = null;

// View-local presentation filters (not application state; never affect correctness)
const REC_FILTER = { mission: "all", direction: "all", sort: "gap" };
const BOUNTY = { mode: "open", expanded: new Set() };
let SEARCH_RESULTS = [];

const missionMeta = (slug) => CATALOG.find((m) => m.slug === slug) || null;
const activeSlug = () => ui().transport.activeMission;
const repoOf = (snap) => snap?.mission?.github_repo || DEFAULT_REPO;
const isStatic = () => ui().transport.mode === "static";

function lemmaFor(mission, id) {
  const snap = mission ? SNAP_CACHE.get(mission) : STATE;
  return (snap || STATE)?.lemmas?.find((l) => l.id === id) || null;
}

// ======================================================= status grammar
const STATUS_TITLES = {
  open: "Open problem — available to attempt",
  in_work: "Claimed by an active seat",
  provisional: "Kernel-checked; awaiting an independent cross-model audit",
  frozen: "Kernel type-matched against a frozen statement",
  audited: "Kernel-checked and confirmed faithful by an independent model",
  record: "Live record — beat it to take the hill",
  hunt: "Open record hunt — the launch target is unclaimed",
  refuted: "Judge-verified counterexample (a valid mathematical result)",
  dead: "Approach ruled dead against a known barrier",
  flagged: "Cross-model audit flagged a statement/title gap — excluded from objectives",
  contradiction: "Opposing verified proof and refutation — halted for review",
};

function statusHTML(lemma) {
  const s = statusOf(lemma);
  return `<span class="st tone-${s.tone}" title="${esc(STATUS_TITLES[s.key] || s.label)}"><span class="st-glyph" aria-hidden="true">${s.glyph}</span><span class="st-label">${esc(s.label)}</span></span>`;
}

function flagsHTML(lemma) {
  const out = [];
  const fresh = freshnessOf(lemma);
  if (fresh === "stale_statement") out.push(`<span class="pr-note" title="The frozen statement changed after this check; re-verification required">↻ stale statement</span>`);
  else if (fresh === "stale_core") out.push(`<span class="pr-note" title="Core definitions changed since this check (advisory)">↻ stale core</span>`);
  const pr = prStateOf(lemma);
  const first = (lemma?.open_prs || [])[0];
  if (pr === "needs_fix") {
    out.push(
      first
        ? `<a class="flag-line" href="${esc(first.url)}" target="_blank" rel="noopener noreferrer" data-stop>PR ${int(first.number) ? `#${int(first.number)} ` : ""}needs fix</a>`
        : `<span class="flag-line">PR needs fix</span>`
    );
  } else if (pr !== "none") {
    const label = pr === "passing" ? "passing" : "open";
    out.push(
      first
        ? `<a class="pr-note" href="${esc(first.url)}" target="_blank" rel="noopener noreferrer" data-stop title="${esc(first.title || "")}">PR #${int(first.number)} · ${label}</a>`
        : `<span class="pr-note">PR ${label}</span>`
    );
  }
  return out.join(" ");
}

function programTitle(snap, progId) {
  return snap?.programs?.find((p) => p.id === progId)?.title || progId || "";
}

// ================================================== records presentation
function recordFigureHTML(r) {
  const unit = esc(r.unit || "");
  if (r.contradiction) return `<span class="rec-figure"><span class="st tone-alarm"><span class="st-glyph">⛔</span><span class="st-label">Halted</span></span></span>`;
  if (r.closed && r.best_score != null) return `<span class="rec-figure">${int(r.best_score)}<span class="unit">${unit} · optimal, closed</span></span>`;
  if (r.best_score != null) {
    return `<span class="rec-figure">${int(r.best_score)}<span class="slash">/</span><span class="target">${esc(r.op)}${int(r.next_target)}</span><span class="unit">${unit}${r.best_seat ? ` · ${esc(r.best_seat)}` : ""}</span></span>`;
  }
  const t = r.next_target ?? r.start_target;
  return `<span class="rec-figure"><span class="target">${esc(r.op)}</span>${t == null ? "—" : int(t)}<span class="unit">${unit} · launch target, unclaimed</span></span>`;
}

function boundBarHTML(r) {
  const g = boundIntervalGeometry(r);
  if (!g) return `<span class="muted small">No bounds registered</span>`;
  const isMax = r.direction === "max";
  const boundWord = isMax ? "UB" : "LB";
  const parts = [`<span class="bib-track"></span>`];
  if (g.gapLeftPct != null && g.gapWidthPct > 0 && !r.closed) {
    parts.push(`<span class="bib-gap" style="left:${g.gapLeftPct}%;width:${g.gapWidthPct}%"></span>`);
  }
  if (g.literaturePct != null) {
    parts.push(`<span class="bib-lit" style="left:${g.literaturePct}%;top:calc(50% + 4px)" title="Best known in the literature: ${int(g.literature)}">▴</span>`);
  }
  if (g.boundPct != null) {
    parts.push(
      `<span class="bib-tick is-bound ${g.boundProven ? "" : "is-literature-bound"}" style="left:${g.boundPct}%" title="${g.boundProven ? "Proven in the ledger" : "Literature bound (not yet proven here)"}"><span class="bib-lab">${g.boundProven ? "" : "lit. "}${boundWord} ${int(g.bound)}</span></span>`
    );
  }
  if (g.currentPct != null) {
    parts.push(
      `<span class="bib-tick is-best" style="left:${g.currentPct}%" title="${r.best_score != null ? "Best verified" : "Launch target"}"><span class="bib-lab">${r.best_score != null ? "" : "launch "}${int(g.current)}</span></span>`
    );
  }
  const aria = `${r.best_score != null ? `Best ${r.best_score}` : `Launch target ${r.start_target}`}, ${g.boundProven ? "proven" : "literature"} ${isMax ? "upper" : "lower"} bound ${g.bound ?? "unknown"}${r.gap != null ? `, gap ${r.gap}` : ""}`;
  const caption = r.closed
    ? "closed — optimum proven"
    : [r.gap != null ? `gap ${int(r.gap)}${r.unit ? ` ${esc(r.unit)}` : ""}` : null, r.literature_best != null ? `lit. best ${int(r.literature_best)}` : null].filter(Boolean).join(" · ");
  return `<div class="bib" role="img" aria-label="${esc(aria)}">${parts.join("")}</div><div class="bib-caption">${caption}</div>`;
}

function sparkHTML(r) {
  const w = 112;
  const h = 26;
  const pts = ratchetSeries(r);
  if (!pts.length) {
    return `<svg class="spark" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" aria-hidden="true"><path class="spark-base" d="M0 ${h / 2} H${w}"/></svg><div class="spark-note">unclaimed baseline</div>`;
  }
  const scores = [r.start_target, ...pts.map((p) => p.score)].filter((v) => v != null);
  const lo = Math.min(...scores);
  const hi = Math.max(...scores);
  const y = (v) => (hi === lo ? h / 2 : 3 + ((hi - v) / (hi - lo)) * (h - 6));
  const steps = [r.start_target ?? pts[0].score, ...pts.map((p) => p.score)];
  const dx = w / Math.max(1, steps.length - 1);
  let d = `M0 ${y(steps[0]).toFixed(1)}`;
  for (let i = 1; i < steps.length; i++) d += ` H${(i * dx).toFixed(1)} V${y(steps[i]).toFixed(1)}`;
  const last = steps[steps.length - 1];
  return `<svg class="spark" width="${w}" height="${h}" viewBox="0 0 ${w} ${h}" aria-hidden="true"><path class="spark-base" d="M0 ${y(steps[0]).toFixed(1)} H${w}"/><path class="spark-line" d="${d}"/><circle class="spark-dot" cx="${w}" cy="${y(last).toFixed(1)}" r="2.2"/></svg><div class="spark-note">${pts.length} ratchet${pts.length === 1 ? "" : "s"}${pts[pts.length - 1].t && relTime(pts[pts.length - 1].t) ? ` · ${relTime(pts[pts.length - 1].t)}` : ""}</div>`;
}

function attemptButtonHTML(id, mission, label = "Attempt →") {
  return `<button class="attempt-link" type="button" data-attempt="${esc(id)}" data-mission="${esc(mission || "")}">${esc(label)}</button>`;
}

function recordRowHTML(r) {
  const live = !r.closed && !r.contradiction;
  const dirLabel = r.direction === "max" ? "maximize" : "minimize";
  return `
    <li class="rec-row" data-open-claim="${esc(r.id)}" data-mission="${esc(r.mission)}" tabindex="0" role="button" aria-label="Open dossier for ${esc(r.id)}">
      <span class="rec-id">${esc(r.id)}</span>
      <div><div class="rec-title">${esc(cleanRecordTitle(r.title))}</div><div class="rec-mission">${esc(r.mission_title || r.mission)} · ${dirLabel}</div></div>
      ${recordFigureHTML(r)}
      <div class="rec-bar">${boundBarHTML(r)}</div>
      <span class="rec-go">${live ? attemptButtonHTML(r.id, r.mission) : ""}</span>
    </li>`;
}

// ============================================================ render hub
function renderCurrent() {
  const r = ui().route;
  renderChrome();
  switch (r.view) {
    case "missions":
      renderMissions();
      break;
    case "records":
      renderRecords();
      break;
    case "control":
      renderControl();
      break;
    case "bounties":
      renderBounties();
      break;
    case "ledger":
      renderLedger(r.ledgerTab);
      break;
  }
}

function renderChrome() {
  const live = (RECORDS?.records || []).filter((r) => !r.closed && !r.contradiction).length;
  $("#nav-records-count").textContent = RECORDS ? String(live) : "";
  $("#records-more-link").textContent = RECORDS ? `View all ${RECORDS.records.length} records →` : "View all records →";
  const judge = STATE?.mission?.judge?.label;
  $("#footer-judge").textContent = judge ? `Judge · ${judge}` : "Judge · isolated mechanical Judge";
  $("#footer-gh").href = `https://github.com/${repoOf(STATE)}`;
  $("#footer-proofs").href = isStatic() ? "./PROOFS.md" : "/PROOFS.md";
  syncMissionSelects();
}

function syncMissionSelects() {
  const slug = activeSlug();
  for (const sel of $$(".mission-switch")) {
    if (sel.options.length !== CATALOG.length) {
      sel.innerHTML = CATALOG.map((m) => `<option value="${esc(m.slug)}">${esc(m.title)}</option>`).join("");
    }
    if (slug && sel.value !== slug) sel.value = slug;
  }
  const recSel = $("#rec-mission");
  if (recSel.options.length !== CATALOG.length + 1) {
    recSel.innerHTML = `<option value="all">All missions</option>` + CATALOG.map((m) => `<option value="${esc(m.slug)}">${esc(m.title)}</option>`).join("");
    recSel.value = REC_FILTER.mission;
  }
}

// =========================================================== I. Missions
function figureSentenceHTML() {
  const t = RECORDS?.totals || {};
  const sum = (k) => CATALOG.reduce((a, m) => a + int(m.counts?.[k]), 0);
  const checked = t.checked_total ?? sum("checked");
  const refuted = t.refuted ?? sum("refuted");
  const liveRecs = RECORDS ? RECORDS.records.filter((r) => !r.closed && !r.contradiction).length : t.records_active ?? sum("records_active");
  const missions = t.missions ?? CATALOG.length;
  const sep = `<span class="sep" aria-hidden="true">·</span>`;
  return `<strong>${int(checked)}</strong> checked${sep}<strong>${int(refuted)}</strong> refuted${sep}<strong class="accent">${int(liveRecs)}</strong> live records${sep}<strong>${int(missions)}</strong> missions`;
}

function featuredTheorem() {
  if (RECORDS?.latest_verified) return RECORDS.latest_verified;
  return latestVerifiedFromSnapshots([...SNAP_CACHE.values()]);
}

function renderMissions() {
  $("#dateline").textContent = longDate(RECORDS?.generated_at || STATE?.snapshot_at);
  $("#figure-sentence").innerHTML = CATALOG.length ? figureSentenceHTML() : "&nbsp;";

  const f = featuredTheorem();
  const feat = $("#featured");
  if (f) {
    feat.dataset.openClaim = f.id;
    feat.dataset.mission = f.mission || "";
    $("#featured-title").classList.toggle("is-long", String(f.title || "").length > 90);
    $("#featured-title").innerHTML = `<span class="featured-label">Theorem ${esc(f.id)}.</span>${esc(f.title)}`;
    $("#featured-stmt").textContent = f.statement || "";
    $("#featured-stmt").hidden = !f.statement;
    const sealWord = f.seal === "audited" ? "Audited" : "Verified";
    const bits = [
      `<span class="verified">◆ ${sealWord}</span>`,
      esc(shortLean(f.judge_label)),
      "zero sorry",
      f.by_seat ? `<span class="mono small">${esc(f.by_seat)}</span>` : null,
      f.mission_title ? esc(f.mission_title) : null,
      f.at ? esc(relTime(f.at)) : null,
    ].filter(Boolean);
    $("#featured-attr").innerHTML = bits.join(`<span class="sep" aria-hidden="true">·</span>`);
  } else {
    delete feat.dataset.openClaim;
    $("#featured-title").textContent = CATALOG.length ? "The ledger is open." : "Loading the ledger…";
    $("#featured-stmt").hidden = true;
    $("#featured-attr").textContent = "";
  }

  // §1 hottest record hunts
  const prev = $("#records-preview");
  if (!RECORDS) prev.innerHTML = `<li class="empty">Loading record hunts…</li>`;
  else {
    const hot = pickHotRecords(RECORDS.records, 5);
    prev.innerHTML = hot.length ? hot.map(recordRowHTML).join("") : `<li class="empty">No live record hunts right now.</li>`;
  }

  // §2 table of contents
  $("#missions-count").textContent = CATALOG.length ? `${CATALOG.length} missions` : "";
  $("#missions-toc").innerHTML = CATALOG.length
    ? CATALOG.map((m, i) => {
        const c = m.counts || {};
        const open = Math.max(0, int(c.conjecture) - int(c.records_active));
        const recs = int(c.records_active) + int(c.records_closed);
        return `
        <li class="toc-row ${m.slug === activeSlug() ? "is-active" : ""}" data-open-mission="${esc(m.slug)}" tabindex="0" role="link" aria-label="Open mission ${esc(m.title)}">
          <span class="toc-num">${toRoman(i + 1)}.</span>
          <div>
            <div class="toc-title">${esc(m.title)}</div>
            <p class="toc-question">${esc(m.question || m.tagline || "")}</p>
            <div class="toc-judge">${esc(m.judge_label || (m.judge_type === "command" ? "Command Judge" : "Lean 4 kernel"))}</div>
          </div>
          ${rungStripHTML(m)}
          <div class="toc-counts tabular"><strong>${int(c.trusted)}</strong> trusted<br><strong>${open}</strong> open · <strong>${recs}</strong> records</div>
          <span class="toc-arrow" aria-hidden="true">→</span>
        </li>`;
      }).join("")
    : `<li class="empty">Loading missions…</li>`;
}

function objectivesDetailFor(m) {
  if (Array.isArray(m.objectives_detail) && m.objectives_detail.length) return m.objectives_detail;
  const snap = SNAP_CACHE.get(m.slug);
  const objs = snap?.mission?.objectives;
  if (Array.isArray(objs) && objs.length) {
    return objs.map((o) => ({
      id: o.id,
      title: o.title,
      tier: o.tier,
      conquered: Boolean(o.conquered),
      rungs: (o.items || []).map((it) => ({ id: it.id, conquered: Boolean(it.done), seal: it.seal })),
    }));
  }
  return null;
}

function rungStripHTML(m) {
  const det = objectivesDetailFor(m);
  if (det) {
    const done = det.filter((o) => o.conquered).length;
    const groups = det
      .map((o) => {
        const rungs = (o.rungs || []).map((r) => `<span class="${r.conquered ? "on" : "off"}">${r.conquered ? "◆" : "○"}</span>`).join("");
        const n = (o.rungs || []).filter((r) => r.conquered).length;
        return `<span class="obj" title="${esc(o.title)} — ${n}/${(o.rungs || []).length} rungs">${rungs || `<span class="${o.conquered ? "on" : "off"}">${o.conquered ? "◆" : "○"}</span>`}</span>`;
      })
      .join("");
    return `<div class="rung-strip" aria-label="${done} of ${det.length} objectives conquered">${groups}<span class="rung-strip-label">${done}/${det.length}</span></div>`;
  }
  const total = int(m.objectives?.total);
  const won = int(m.objectives?.conquered);
  const marks = Array.from({ length: total }, (_, i) => `<span class="${i < won ? "on" : "off"}">${i < won ? "◆" : "○"}</span>`).join("");
  return `<div class="rung-strip" aria-label="${won} of ${total} objectives conquered"><span class="obj">${marks}</span><span class="rung-strip-label">${won}/${total}</span></div>`;
}

function pickNextProblem(snap = STATE) {
  if (!snap?.lemmas) return null;
  const byId = Object.fromEntries(snap.lemmas.map((l) => [l.id, l]));
  const depsOk = (l) => (l.deps || []).every((d) => !byId[d] || byId[d].status === "checked" || byId[d].status === "refuted");
  const score = (l) =>
    (l.kind !== "record" && l.statement_file ? 8 : 0) +
    ((l.open_prs || []).length === 0 ? 4 : 0) +
    (depsOk(l) ? 2 : 0) +
    (l.kind === "record" ? 1 : 0) -
    (l.rung || 0) * 0.01;
  return snap.lemmas.filter((l) => isAttemptable(l) && l.status !== "in_work").sort((a, b) => score(b) - score(a))[0] || null;
}

function takeOpenProblem() {
  const pick = pickNextProblem();
  if (pick) openAttempt(activeSlug(), pick.id);
  else navigate("bounties");
}

// ============================================================ II. Records
function renderRecords() {
  $$("#rec-direction [data-dir]").forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.dir === REC_FILTER.direction)));
  $("#rec-sort").value = REC_FILTER.sort;
  const body = $("#records-tbody");
  if (!RECORDS) {
    body.innerHTML = `<tr><td colspan="6" class="empty">Loading record hunts…</td></tr>`;
    $("#rec-count").textContent = "";
    return;
  }
  const rows = sortRecords(filterRecords(RECORDS.records, REC_FILTER), REC_FILTER.sort);
  $("#rec-count").textContent = `${rows.length} of ${RECORDS.records.length} hunts${RECORDS.synthesized ? " · assembled from mission snapshots" : ""}`;
  body.innerHTML = rows.length
    ? rows
        .map((r) => {
          const live = !r.closed && !r.contradiction;
          return `
          <tr data-open-claim="${esc(r.id)}" data-mission="${esc(r.mission)}" tabindex="0" aria-label="Open dossier for ${esc(r.id)}">
            <td class="rec-id">${esc(r.id)}</td>
            <td><div class="rec-title">${esc(cleanRecordTitle(r.title))}</div><div class="rec-mission">${esc(r.mission_title || r.mission)} · ${r.direction === "max" ? "maximize" : "minimize"}${r.unit ? ` ${esc(r.unit)}` : ""}${r.open_prs?.length ? ` · ${r.open_prs.length} open PR${r.open_prs.length > 1 ? "s" : ""}` : ""}</div></td>
            <td>${recordFigureHTML(r)}</td>
            <td class="col-bar">${boundBarHTML(r)}</td>
            <td class="col-hist">${sparkHTML(r)}</td>
            <td>${live ? attemptButtonHTML(r.id, r.mission) : `<span class="muted small">${r.closed ? "closed" : "halted"}</span>`}</td>
          </tr>`;
        })
        .join("")
    : `<tr><td colspan="6" class="empty">No record hunts match these filters.</td></tr>`;
}

// ===================================================== III. Mission control
function renderControl() {
  if (!STATE) return;
  const m = STATE.mission;
  const c = STATE.counts || {};
  const meta = missionMeta(m.slug);
  $("#control-slug").textContent = m.slug;
  $("#control-eyebrow").textContent = [m.brand && m.brand !== m.title ? m.brand : m.title, m.tagline].filter(Boolean).join(" · ");
  $("#control-question").textContent = m.question || m.title;
  $("#control-desc").textContent = m.description || "";
  $("#control-judge").innerHTML = [
    ["Judge", m.judge?.label || meta?.judge_label || "Mechanical Judge"],
    ["Verdict", STATE.meta?.verdict || "—"],
    ["PR sync", STATE.pr_sync?.ok ? `synced ${relTime(STATE.pr_sync.fetched_at)}` : "offline snapshot"],
    ["Snapshot", relTime(STATE.snapshot_at) || "—"],
  ]
    .map(([k, v]) => `<dt>${esc(k)}</dt><dd>${esc(v)}</dd>`)
    .join("");

  const objs = m.objectives || [];
  const won = objs.filter((o) => o.conquered).length;
  const records = STATE.lemmas.filter((l) => l.kind === "record");
  const openProblems = STATE.lemmas.filter((l) => l.kind !== "record" && isAttemptable(l));
  const sep = `<span class="sep" aria-hidden="true">·</span>`;
  $("#control-figures").innerHTML = [
    `<strong>${int(c.trusted)}</strong> trusted`,
    `<strong>${openProblems.length}</strong> open`,
    `<strong class="accent">${records.length}</strong> records`,
    `<strong>${int(c.refuted)}</strong> refuted`,
    `<strong>${won}/${objs.length}</strong> objectives`,
  ].join(sep);
  $("#control-attempt-btn").disabled = !pickNextProblem();

  // §1 ladders
  $("#ladders-count").textContent = objs.length ? `${won} of ${objs.length} conquered` : "";
  $("#ladders").innerHTML = objs.length
    ? objs
        .map((o) => {
          const items = o.items || [];
          const rungs = items
            .map((it) => {
              const goal =
                it.expect === "refutation"
                  ? "refute"
                  : it.expect && typeof it.expect === "object" && it.expect.record_at_most != null
                  ? `goal ≤ ${int(it.expect.record_at_most)}`
                  : it.expect && typeof it.expect === "object" && it.expect.record_at_least != null
                  ? `goal ≥ ${int(it.expect.record_at_least)}`
                  : "";
              const lemma = STATE.lemmas.find((l) => l.id === it.id) || it;
              return `
                <li class="rung">
                  <span class="rung-mark ${it.done ? "on" : "off"}" aria-hidden="true">${it.done ? "◆" : "○"}</span>
                  <button class="rung-btn" type="button" data-open-claim="${esc(it.id)}" aria-label="${esc(it.id)} — ${it.done ? "conquered" : "open"}">
                    <span><span class="rung-id">${esc(it.id)}</span><span class="rung-title">${esc(it.title)}</span>${goal ? `<span class="rung-goal">${esc(goal)}</span>` : ""}</span>
                    ${statusHTML(lemma)}
                  </button>
                </li>`;
            })
            .join("");
          return `
            <article class="ladder">
              <div class="ladder-head">
                <div>
                  <div class="ladder-tier">${esc(o.tier || "Objective")}${o.conquered ? ` · <span class="won">◆ conquered</span>` : ""}</div>
                  <h3 class="ladder-title">${esc(o.title)}</h3>
                </div>
                <span class="ladder-ratio tabular">${int(o.completed)} / ${int(o.total)}</span>
              </div>
              ${o.finish_line ? `<p class="ladder-finish">${esc(o.finish_line)}</p>` : ""}
              <ol class="rungs">${rungs}</ol>
            </article>`;
        })
        .join("")
    : `<p class="empty">No objectives are configured for this mission yet.</p>`;

  // §2 mission records
  const recRows = records.map((l) => recordRowFromLemma(l, m)).filter(Boolean);
  $("#control-records-section").hidden = recRows.length === 0;
  $("#control-records").innerHTML = sortRecords(recRows, "gap").map(recordRowHTML).join("");

  // §3 open problems
  const sorted = [...openProblems].sort(
    (a, b) => (b.statement_file ? 1 : 0) - (a.statement_file ? 1 : 0) || (a.status === "in_work") - (b.status === "in_work") || (a.rung || 99) - (b.rung || 99)
  );
  $("#control-open").innerHTML = sorted.length
    ? sorted.slice(0, 10).map((l) => claimRowHTML(l, { mission: m.slug, expandable: false })).join("") +
      (sorted.length > 10 ? `<li class="claim-row"><div class="claim-line" data-nav="bounties" role="link" tabindex="0"><span></span><span></span><span class="link-btn">${sorted.length - 10} more open problems →</span></div></li>` : "")
    : `<li class="empty">Every registered problem in this mission is settled. Try another mission.</li>`;

  // §4 strategy + receipts
  const note = STATE.meta?.strategy_note;
  $("#strategy-meta").textContent = note ? [note.seat, relTime(note.at)].filter(Boolean).join(" · ") : "";
  $("#strategy-text").textContent = note?.text || "No strategy note has been published for this mission yet.";
  $("#strategy-mentions").innerHTML = (note?.mentions || [])
    .map((id) => `<button class="chip-link" type="button" data-open-claim="${esc(id)}">${esc(id)}</button>`)
    .join("");
  const receipts = (STATE.events || []).filter((e) => ["checker_accepted", "claim_refuted", "lemma_audited", "approach_dead", "checker_rejected"].includes(e.type)).slice(0, 8);
  $("#receipts-count").textContent = receipts.length ? `${receipts.length} latest` : "";
  $("#receipts-list").innerHTML = receipts.length ? receipts.map(eventItemHTML).join("") : `<li class="empty">No Judge receipts yet.</li>`;
}

function claimTargetHTML(l) {
  if (l.kind === "record") {
    const rm = recordMetaOf(l);
    const bound = rm.proven_bound ?? rm.literature_bound;
    return [bound != null ? `${rm.proven_bound != null ? "" : "lit. "}${rm.direction === "max" ? "UB" : "LB"} ${int(bound)}` : null, rm.gap != null ? `gap ${int(rm.gap)}` : null]
      .filter(Boolean)
      .join(" · ");
  }
  return l.rung ? `rung ${int(l.rung)}` : "";
}

function claimRowHTML(l, { mission, expandable = true, expanded = false, reason = null } = {}) {
  const snap = SNAP_CACHE.get(mission) || STATE;
  const attempt = isAttemptable(l) ? attemptButtonHTML(l.id, mission, l.kind === "record" ? "Beat it →" : "Attempt →") : "";
  const subBits = [
    programTitle(snap, l.program) ? esc(programTitle(snap, l.program)) : null,
    l.kind === "record" ? "record hunt" : l.statement_file ? "frozen statement" : "free-form statement",
    (l.deps || []).length ? `needs ${(l.deps || []).map(esc).join(", ")}` : null,
    reason ? esc(reason) : null,
    flagsHTML(l) || null,
  ].filter(Boolean);
  const lineAttrs = expandable
    ? `data-toggle-claim="${esc(l.id)}" role="button" tabindex="0" aria-expanded="${expanded}"`
    : `data-open-claim="${esc(l.id)}" data-mission="${esc(mission || "")}" role="button" tabindex="0"`;
  const stmt = l.registered_statement || l.statement || l.theorem_name || "";
  return `
    <li class="claim-row ${expanded ? "is-open" : ""}">
      <div class="claim-line" ${lineAttrs}>
        <span class="claim-id">${expandable ? `<span class="caret" aria-hidden="true">▸</span>` : ""}${esc(l.id)}</span>
        <span class="claim-status">${statusHTML(l)}</span>
        <div><div class="claim-title">${esc(l.title)}</div><div class="claim-sub">${subBits.join(`<span aria-hidden="true">·</span>`)}</div></div>
        <span class="claim-target">${claimTargetHTML(l)}</span>
        <span class="claim-go">${attempt}</span>
      </div>
      ${
        expanded
          ? `<div class="claim-expand">
              ${l.statement_file ? `<p class="small muted mono">${esc(l.statement_file)}</p>` : ""}
              <pre class="lean-block">${esc(stmt)}</pre>
              ${l.paper_notes ? `<p class="notes">${esc(l.paper_notes)}</p>` : ""}
              <div class="actions">
                <button class="link-btn" type="button" data-open-claim="${esc(l.id)}" data-mission="${esc(mission || "")}">Open dossier</button>
                ${attempt}
              </div>
            </div>`
          : ""
      }
    </li>`;
}

// ============================================================ IV. Bounties
function renderBounties() {
  if (!STATE) return;
  $$("#bounty-mode [data-bmode]").forEach((b) => b.setAttribute("aria-selected", String(b.dataset.bmode === BOUNTY.mode)));
  $("#bounties-title").textContent = BOUNTY.mode === "open" ? "Open problems" : "Full claim ledger";
  $("#bounties-eyebrow").textContent = `${STATE.mission.title} · ${BOUNTY.mode === "open" ? "problem queue" : "every claim and receipt"}`;

  const progSel = $("#bounty-program");
  const progs = STATE.programs || [];
  const want = progSel.value || "all";
  const sig = progs.map((p) => p.id).join("|");
  if (progSel.dataset.sig !== sig) {
    progSel.innerHTML = `<option value="all">All programs</option>` + progs.map((p) => `<option value="${esc(p.id)}">${esc(p.title)}</option>`).join("");
    progSel.dataset.sig = sig;
    progSel.value = progs.some((p) => p.id === want) ? want : "all";
  }

  const q = ($("#bounty-search").value || "").trim().toLowerCase();
  const prog = progSel.value;
  const sealFilter = $("#bounty-seal").value;
  const rows = STATE.lemmas.filter((l) => {
    if (BOUNTY.mode === "open" && !isAttemptable(l)) return false;
    if (prog !== "all" && l.program !== prog) return false;
    if (sealFilter === "record") {
      if (!(l.kind === "record" && isAttemptable(l))) return false;
    } else if (sealFilter !== "all" && sealOf(l) !== sealFilter) return false;
    if (q && !`${l.id} ${l.title} ${l.statement || ""} ${l.theorem_name || ""} ${l.paper_notes || ""}`.toLowerCase().includes(q)) return false;
    return true;
  });
  const sorted =
    BOUNTY.mode === "open"
      ? rows.sort(
          (a, b) =>
            (b.kind !== "record" && b.statement_file ? 1 : 0) - (a.kind !== "record" && a.statement_file ? 1 : 0) ||
            (a.kind === "record") - (b.kind === "record") ||
            (a.rung || 99) - (b.rung || 99)
        )
      : rows;
  $("#bounty-count").textContent = `${sorted.length} ${BOUNTY.mode === "open" ? "open" : "claims"}`;
  $("#bounty-list").innerHTML = sorted.length
    ? sorted.map((l) => claimRowHTML(l, { mission: STATE.mission.slug, expandable: true, expanded: BOUNTY.expanded.has(l.id) })).join("")
    : `<li class="empty">${BOUNTY.mode === "open" ? "No open problems match. Switch to the full ledger to see settled claims." : "No claims match these filters."}</li>`;
}

// ============================================================== V. Ledger
function renderLedger(tab) {
  $$("#ledger-tabs [data-tab]").forEach((b) => b.setAttribute("aria-selected", String(b.dataset.tab === tab)));
  for (const t of ["map", "leaderboard", "refutations", "fleet", "audit"]) $(`#tab-${t}`).hidden = t !== tab;
  if (!STATE) return;
  $("#ledger-mission-name").textContent = STATE.mission.title;
  if (tab === "map") {
    renderMap();
    renderDAG();
  } else if (tab === "leaderboard") renderLeaderboard();
  else if (tab === "refutations") renderRefutations();
  else if (tab === "fleet") renderFleet();
  else if (tab === "audit") renderAudit();
}

// --- proof map (canvas reads every colour from CSS tokens)
const MAP = { nodes: [], cam: { x: 0, y: 0, z: 1 }, drag: null, bound: false };
function isMapVisible() {
  const r = ui().route;
  return r.view === "ledger" && r.ledgerTab === "map" && ui().overlay.kind === "none";
}
function tokens() {
  const cs = getComputedStyle(document.documentElement);
  const t = (n) => cs.getPropertyValue(n).trim();
  return { bg: t("--bg"), surface: t("--surface"), ink: t("--ink"), muted: t("--muted"), rule: t("--rule"), ruleStrong: t("--rule-strong"), accent: t("--accent"), alarm: t("--alarm") };
}
function renderMap() {
  const progs = STATE.programs?.length ? STATE.programs : [{ id: null, title: "Claims" }];
  const lemmas = STATE.lemmas || [];
  MAP.nodes = [];
  const ringR = progs.length <= 1 ? 0 : 190;
  progs.forEach((p, pi) => {
    const ang = (Math.PI * 2 * pi) / Math.max(1, progs.length) - Math.PI / 2;
    const cx = Math.cos(ang) * ringR;
    const cy = Math.sin(ang) * ringR;
    const group = lemmas.filter((l) => (p.id == null ? true : l.program === p.id));
    group.forEach((l, li) => {
      const a2 = (Math.PI * 2 * li) / Math.max(1, group.length);
      const r2 = group.length <= 1 ? 0 : 54 + (li % 2) * 30;
      MAP.nodes.push({ lemma: l, x: cx + Math.cos(a2) * r2, y: cy + Math.sin(a2) * r2, r: 9 });
    });
  });
  const orphan = lemmas.filter((l) => !MAP.nodes.some((n) => n.lemma === l));
  orphan.forEach((l, i) => MAP.nodes.push({ lemma: l, x: -260 + i * 34, y: 300, r: 9 }));
  if (!MAP.bound) bindMap();
  $("#map-legend").innerHTML = [
    ["◆", "accent", "Frozen / audited"],
    ["♛", "accent", "Live record"],
    ["◇", "ink", "Provisional"],
    ["◐", "ink", "In work"],
    ["○", "muted", "Open"],
    ["✕", "ink", "Refuted"],
    ["—", "struck", "Barrier"],
    ["⚠", "alarm", "Flagged / contradiction"],
  ]
    .map(([g, tone, label]) => `<li><span class="st tone-${tone === "alarm" ? "accent" : tone}" style="${tone === "alarm" ? "color:var(--alarm)" : ""}"><span class="st-glyph">${g}</span><span class="st-label">${label}</span></span></li>`)
    .join("");
  requestAnimationFrame(drawMap);
}

function drawNodeShape(ctx, n, tk) {
  const s = statusOf(n.lemma);
  const col = { accent: tk.accent, alarm: tk.alarm, ink: tk.ink, muted: tk.muted, struck: tk.muted }[s.tone] || tk.ink;
  const r = n.r;
  ctx.lineWidth = 1.4;
  ctx.strokeStyle = col;
  ctx.fillStyle = col;
  ctx.beginPath();
  switch (s.key) {
    case "frozen":
    case "audited":
      ctx.moveTo(n.x, n.y - r);
      ctx.lineTo(n.x + r, n.y);
      ctx.lineTo(n.x, n.y + r);
      ctx.lineTo(n.x - r, n.y);
      ctx.closePath();
      ctx.fill();
      break;
    case "provisional":
      ctx.fillStyle = tk.surface;
      ctx.moveTo(n.x, n.y - r);
      ctx.lineTo(n.x + r, n.y);
      ctx.lineTo(n.x, n.y + r);
      ctx.lineTo(n.x - r, n.y);
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
      break;
    case "in_work":
      ctx.fillStyle = tk.surface;
      ctx.arc(n.x, n.y, r - 1, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
      ctx.beginPath();
      ctx.fillStyle = col;
      ctx.arc(n.x, n.y, r - 1, Math.PI / 2, (Math.PI * 3) / 2);
      ctx.fill();
      break;
    case "refuted":
      ctx.moveTo(n.x - r * 0.7, n.y - r * 0.7);
      ctx.lineTo(n.x + r * 0.7, n.y + r * 0.7);
      ctx.moveTo(n.x + r * 0.7, n.y - r * 0.7);
      ctx.lineTo(n.x - r * 0.7, n.y + r * 0.7);
      ctx.lineWidth = 2;
      ctx.stroke();
      break;
    case "dead":
      ctx.moveTo(n.x - r, n.y);
      ctx.lineTo(n.x + r, n.y);
      ctx.lineWidth = 2;
      ctx.stroke();
      break;
    case "flagged":
    case "contradiction":
      ctx.fillStyle = tk.surface;
      ctx.rect(n.x - r, n.y - r, r * 2, r * 2);
      ctx.fill();
      ctx.stroke();
      ctx.fillStyle = col;
      ctx.font = `600 ${r + 2}px ${getComputedStyle(document.body).fontFamily}`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText("!", n.x, n.y + 0.5);
      break;
    case "record":
    case "hunt":
      ctx.font = `${r * 2 + 2}px serif`;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText("♛", n.x, n.y);
      break;
    default:
      ctx.fillStyle = tk.surface;
      ctx.arc(n.x, n.y, r - 1, 0, Math.PI * 2);
      ctx.fill();
      ctx.stroke();
  }
}

function drawMap() {
  const canvas = $("#map-canvas");
  if (!canvas || !STATE) return;
  const rect = canvas.getBoundingClientRect();
  if (!rect.width || !rect.height) return;
  const tk = tokens();
  const dpr = window.devicePixelRatio || 1;
  canvas.width = Math.round(rect.width * dpr);
  canvas.height = Math.round(rect.height * dpr);
  const ctx = canvas.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.fillStyle = tk.surface;
  ctx.fillRect(0, 0, rect.width, rect.height);
  ctx.save();
  ctx.translate(rect.width / 2 + MAP.cam.x, rect.height / 2 + MAP.cam.y);
  ctx.scale(MAP.cam.z, MAP.cam.z);
  const byId = Object.fromEntries(MAP.nodes.map((n) => [n.lemma.id, n]));
  ctx.strokeStyle = tk.ruleStrong;
  ctx.lineWidth = 1;
  for (const n of MAP.nodes) {
    for (const depId of n.lemma.deps || []) {
      const d = byId[depId];
      if (!d) continue;
      ctx.beginPath();
      ctx.moveTo(d.x, d.y);
      ctx.lineTo(n.x, n.y);
      ctx.stroke();
    }
  }
  const mono = getComputedStyle(document.documentElement).getPropertyValue("--font-mono") || "monospace";
  for (const n of MAP.nodes) {
    drawNodeShape(ctx, n, tk);
    ctx.fillStyle = tk.muted;
    ctx.font = `500 10px ${mono}`;
    ctx.textAlign = "center";
    ctx.textBaseline = "alphabetic";
    ctx.fillText(n.lemma.id, n.x, n.y + n.r + 13);
  }
  ctx.restore();
}

function screenToWorld(canvas, sx, sy) {
  const rect = canvas.getBoundingClientRect();
  return { x: (sx - rect.width / 2 - MAP.cam.x) / MAP.cam.z, y: (sy - rect.height / 2 - MAP.cam.y) / MAP.cam.z };
}
function hitNode(canvas, sx, sy) {
  const w = screenToWorld(canvas, sx, sy);
  return MAP.nodes.find((n) => Math.hypot(n.x - w.x, n.y - w.y) <= n.r + 6) || null;
}
function bindMap() {
  MAP.bound = true;
  const canvas = $("#map-canvas");
  const tip = $("#map-tip");
  canvas.addEventListener("pointerdown", (e) => {
    MAP.drag = { sx: e.clientX, sy: e.clientY, cx: MAP.cam.x, cy: MAP.cam.y, moved: false };
    canvas.setPointerCapture?.(e.pointerId);
  });
  canvas.addEventListener("pointermove", (e) => {
    const rect = canvas.getBoundingClientRect();
    if (MAP.drag) {
      const dx = e.clientX - MAP.drag.sx;
      const dy = e.clientY - MAP.drag.sy;
      if (Math.hypot(dx, dy) > 3) MAP.drag.moved = true;
      MAP.cam.x = MAP.drag.cx + dx;
      MAP.cam.y = MAP.drag.cy + dy;
      drawMap();
      tip.hidden = true;
      return;
    }
    const hit = hitNode(canvas, e.clientX - rect.left, e.clientY - rect.top);
    if (hit) {
      tip.innerHTML = `<strong class="mono small">${esc(hit.lemma.id)}</strong> ${statusHTML(hit.lemma)}<div class="small muted" style="margin-top:4px">${esc(hit.lemma.title)}</div>`;
      tip.style.left = `${Math.min(rect.width - 290, Math.max(8, e.clientX - rect.left + 14))}px`;
      tip.style.top = `${Math.min(rect.height - 90, Math.max(8, e.clientY - rect.top + 14))}px`;
      tip.hidden = false;
    } else tip.hidden = true;
  });
  canvas.addEventListener("pointerup", (e) => {
    if (!MAP.drag) return;
    const moved = MAP.drag.moved;
    MAP.drag = null;
    if (moved) return;
    const rect = canvas.getBoundingClientRect();
    const hit = hitNode(canvas, e.clientX - rect.left, e.clientY - rect.top);
    if (hit) openDossier(hit.lemma.id, activeSlug());
  });
  canvas.addEventListener("pointerleave", () => (tip.hidden = true));
  canvas.addEventListener(
    "wheel",
    (e) => {
      e.preventDefault();
      MAP.cam.z = Math.max(0.4, Math.min(2.6, MAP.cam.z * (e.deltaY < 0 ? 1.12 : 0.89)));
      drawMap();
    },
    { passive: false }
  );
  $("#map-zoom-in").addEventListener("click", () => {
    MAP.cam.z = Math.min(2.6, MAP.cam.z * 1.2);
    drawMap();
  });
  $("#map-zoom-out").addEventListener("click", () => {
    MAP.cam.z = Math.max(0.4, MAP.cam.z * 0.82);
    drawMap();
  });
  $("#map-reset").addEventListener("click", () => {
    MAP.cam = { x: 0, y: 0, z: 1 };
    drawMap();
  });
  window.addEventListener("resize", () => isMapVisible() && drawMap());
}

function renderDAG() {
  const lemmas = STATE.lemmas || [];
  const byId = Object.fromEntries(lemmas.map((l) => [l.id, l]));
  const memo = new Map();
  const depth = (id, seen = new Set()) => {
    if (memo.has(id)) return memo.get(id);
    if (seen.has(id)) return 0;
    seen.add(id);
    const l = byId[id];
    const d = !l || !(l.deps || []).length ? 0 : 1 + Math.max(...l.deps.map((x) => depth(x, seen)));
    memo.set(id, d);
    return d;
  };
  const cols = {};
  lemmas.forEach((l) => (cols[depth(l.id)] = cols[depth(l.id)] || []).push(l));
  const keys = Object.keys(cols).map(Number).sort((a, b) => a - b);
  const colW = 214;
  const rowH = 52;
  const pad = 16;
  const maxRows = Math.max(1, ...keys.map((k) => cols[k].length));
  const width = Math.max(600, keys.length * colW + pad * 2);
  const height = maxRows * rowH + pad * 2;
  const pos = {};
  keys.forEach((k, ci) => cols[k].forEach((l, ri) => (pos[l.id] = { x: pad + ci * colW, y: pad + ri * rowH })));
  const edges = [];
  for (const l of lemmas) {
    const to = pos[l.id];
    for (const d of l.deps || []) {
      const from = pos[d];
      if (!from || !to) continue;
      edges.push(`<path class="dag-edge" d="M ${from.x + 170} ${from.y + 18} C ${from.x + 192} ${from.y + 18}, ${to.x - 22} ${to.y + 18}, ${to.x} ${to.y + 18}"/>`);
    }
  }
  const nodes = lemmas.map((l) => {
    const p = pos[l.id];
    const s = statusOf(l);
    return `<g class="dag-node tone-${s.tone}" transform="translate(${p.x},${p.y})" data-open-claim="${esc(l.id)}" tabindex="0" role="button" aria-label="${esc(l.id)}">
      <rect width="170" height="36" rx="1"/>
      <text class="dag-glyph tone-${s.tone}" x="9" y="16">${s.glyph}</text>
      <text class="dag-id" x="25" y="15">${esc(l.id)}</text>
      <text class="dag-title" x="25" y="28">${esc((l.title || "").slice(0, 27))}</text>
    </g>`;
  });
  $("#dag-wrap").innerHTML = `<svg viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="Dependency DAG">${edges.join("")}${nodes.join("")}</svg>`;
}

// --- leaderboard
function renderLeaderboard() {
  const stats = new Map();
  const seatById = (id) => STATE.seats?.find((s) => s.id === id);
  const ensure = (id) => {
    if (!stats.has(id)) {
      const s = seatById(id);
      stats.set(id, { id, name: s?.name || id, model: s?.model || "Community contributor", trusted: 0, recordPts: 0, recordWins: 0, refuted: 0, dead: 0 });
    }
    return stats.get(id);
  };
  for (const s of STATE.seats || []) ensure(s.id);
  for (const l of STATE.lemmas || []) {
    if (l.kind === "record") {
      const rs = l.record_state;
      if (rs && !rs.contradiction) {
        for (const [seat, pts] of Object.entries(rs.points_by_seat || {})) ensure(seat).recordPts += int(pts);
        for (const h of rs.history || []) if (h.state === "accepted" && h.seat) ensure(h.seat).recordWins++;
      }
      continue;
    }
    const seal = sealOf(l);
    if ((seal === "audited" || seal === "frozen") && l.checker?.by_seat) ensure(l.checker.by_seat).trusted++;
    if (seal === "refuted" && l.refutation?.by_seat) ensure(l.refutation.by_seat).refuted++;
    if (seal === "dead" && l.epitaph?.by_seat) ensure(l.epitaph.by_seat).dead++;
  }
  const rows = [...stats.values()]
    .map((r) => ({ ...r, score: r.trusted * 10 + r.recordPts * 5 + r.refuted * 10 + r.dead * 4 }))
    .sort((a, b) => b.score - a.score || b.trusted - a.trusted || b.recordPts - a.recordPts);
  const byModel = new Map();
  for (const r of rows) byModel.set(r.model, (byModel.get(r.model) || 0) + r.trusted + r.refuted + r.recordWins);
  const list = [...byModel.entries()].filter(([, n]) => n > 0).sort((a, b) => b[1] - a[1]);
  const max = Math.max(1, ...list.map(([, n]) => n));
  $("#lb-models").innerHTML = list.length
    ? list
        .map(
          ([model, n]) =>
            `<div class="bar-row"><div class="bar-top"><span>${esc(model)}</span><span class="mono small tabular">${n}</span></div><div class="bar-track"><div class="bar-fill" style="width:${Math.round((n / max) * 100)}%"></div></div></div>`
        )
        .join("")
    : `<p class="empty">No trusted proofs or refutations yet.</p>`;
  const slug = STATE.mission.slug;
  $("#lb-howto").textContent = [
    `git clone https://github.com/${repoOf(STATE)}.git`,
    `node hub/fleet.mjs next --mission ${slug}`,
    `node hub/fleet.mjs verify --mission ${slug} --lemma <ID> --seat donor-<handle> --file <path> --theorem <name> --export`,
    `# King of the Hill records:`,
    `node hub/fleet.mjs record --mission ${slug} --lemma <ID> --score <N> --seat donor-<handle> --export`,
    `# Commit only your artifact + missions/${slug}/submissions/<ID>.*.json and open a PR.`,
  ].join("\n");
  $("#lb-tbody").innerHTML = rows
    .map(
      (r, i) => `
      <tr>
        <td class="mono tabular">${i + 1}</td>
        <td>${esc(r.name)}<div class="mono small muted">${esc(r.id)}</div></td>
        <td>${esc(r.model)}</td>
        <td class="num">${r.trusted}</td>
        <td class="num">${r.recordPts}</td>
        <td class="num">${r.refuted}</td>
        <td class="num">${r.dead}</td>
        <td class="num"><strong>${r.score}</strong></td>
      </tr>`
    )
    .join("");
}

// --- refutations & barriers
function renderRefutations() {
  const fallen = (STATE.lemmas || []).filter((l) => ["refuted", "dead", "flagged", "contradiction"].includes(sealOf(l)));
  const order = { contradiction: 0, flagged: 1, refuted: 2, dead: 3 };
  fallen.sort((a, b) => order[sealOf(a)] - order[sealOf(b)]);
  $("#refutations-list").innerHTML = fallen.length
    ? fallen
        .map((l) => {
          const s = sealOf(l);
          const reason = s === "refuted" ? l.refutation?.summary : s === "flagged" ? l.audit?.notes : s === "dead" ? l.epitaph?.reason : "Opposing verified proof and refutation — halted for review.";
          return claimRowHTML(l, { mission: STATE.mission.slug, expandable: false, reason }).replace('class="claim-row', 'class="claim-row refutation-row');
        })
        .join("")
    : `<li class="empty">No refutations, barriers or flagged claims in this mission yet.</li>`;
}

// --- fleet
function renderFleet() {
  const seats = STATE.seats || [];
  const runs = STATE.checker_runs || [];
  const msgs = STATE.messages || [];
  $("#fleet-stats").textContent = `${seats.length} seats`;
  $("#fleet-pass-rate").textContent = runs.length ? `${runs.filter((r) => r.ok).length}/${runs.length} passed` : "";
  $("#fleet-msg-count").textContent = msgs.length ? `${msgs.length}` : "";
  const w = 460;
  const h = 300;
  const cx = w / 2;
  const cy = h / 2;
  const R = 108;
  const pos = {};
  seats.forEach((s, i) => {
    const a = (Math.PI * 2 * i) / Math.max(1, seats.length) - Math.PI / 2;
    pos[s.id] = { x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) };
  });
  const edges = msgs
    .slice(0, 12)
    .map((m) => {
      const a = pos[m.from];
      const b = pos[m.to];
      if (!a || !b) return "";
      const ch = m.kind === "challenge" || m.kind === "refute";
      return `<line class="ring-edge ${ch ? "is-challenge" : ""}" x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}"/>`;
    })
    .join("");
  const nodes = seats
    .map((s) => {
      const p = pos[s.id];
      const active = s.status === "working" || s.status === "checking";
      return `<g transform="translate(${p.x.toFixed(1)},${p.y.toFixed(1)})"><circle class="ring-seat ${active ? "is-active" : ""}" r="18"/><text class="ring-badge" text-anchor="middle" dy="4">${esc(s.badge || s.id.slice(0, 2).toUpperCase())}</text><text class="ring-name" text-anchor="middle" dy="32">${esc((s.name || s.id).slice(0, 18))}</text></g>`;
    })
    .join("");
  $("#fleet-ring").innerHTML = seats.length
    ? `<svg viewBox="0 0 ${w} ${h}" width="${w}" height="${h}" role="img" aria-label="Seat ring"><circle class="ring-orbit" cx="${cx}" cy="${cy}" r="${R}"/><circle class="ring-judge" cx="${cx}" cy="${cy}" r="27"/><text class="ring-judge-label" x="${cx}" y="${cy + 4}" text-anchor="middle">JUDGE</text>${edges}${nodes}</svg>`
    : `<p class="empty">No seats registered.</p>`;
  $("#fleet-seats").innerHTML = seats
    .map(
      (s) => `<li><div><strong>${esc(s.name)}</strong> <span class="mono small muted">${esc(s.model || s.provider || "")}</span><div class="small muted">${esc(s.current_whisper || s.status || "")}</div></div><span class="mono small tabular muted">◆ ${int(s.counts?.checked)} · ✕ ${int(s.counts?.refuted)} · — ${int(s.counts?.blocked)}</span></li>`
    )
    .join("");
  $("#fleet-runs").innerHTML = runs.length
    ? runs
        .slice(0, 14)
        .map(
          (r) => `<li class="event-item" data-open-claim="${esc(r.lemma_id)}"><div><span class="event-type ${r.ok ? "accent" : ""}">${r.ok ? "ok" : "fail"}</span><strong class="mono small">${esc(r.lemma_id)}</strong><div class="event-detail">${esc(r.seat)} · ${int(r.duration_ms)}ms</div></div><span class="event-time">${esc(relTime(r.at))}</span></li>`
        )
        .join("")
    : `<li class="empty">No local Judge runs in this snapshot.</li>`;
  $("#fleet-messages").innerHTML = msgs.length
    ? msgs
        .slice(0, 14)
        .map(
          (m) => `<li class="event-item"><div><strong class="mono small">${esc(m.from)} → ${esc(m.to)}</strong><div class="event-detail">${esc(m.text)}</div></div><span class="event-time">${esc(relTime(m.at))}</span></li>`
        )
        .join("")
    : `<li class="empty">No seat dispatches yet.</li>`;
}

// --- audit log
const EVENT_LABELS = {
  checker_accepted: ["Checked", "accent"],
  claim_refuted: ["Refuted", ""],
  lemma_audited: ["Audited", "accent"],
  approach_dead: ["Barrier", ""],
  checker_rejected: ["Rejected", ""],
  attempt_started: ["Claimed", ""],
  seat_message: ["Dispatch", ""],
  strategy_update: ["Strategy", ""],
  lemma_stated: ["Stated", ""],
};
function eventItemHTML(e) {
  let [label, tone] = EVENT_LABELS[e.type] || [String(e.type || "event").replace(/_/g, " "), ""];
  if (e.type === "lemma_audited" && String(e.detail || "").startsWith("flagged")) {
    label = "Flagged";
    tone = "alarm";
  }
  return `
    <li class="event-item" ${e.lemma_id ? `data-open-claim="${esc(e.lemma_id)}" tabindex="0" role="button"` : ""}>
      <div>
        <span class="event-type ${tone}">${esc(label)}</span>${e.lemma_id ? `<strong class="mono small">${esc(e.lemma_id)}</strong>` : ""} <span class="mono small muted">${esc(e.seat || "")}</span>
        <div class="event-detail">${esc(e.title || e.detail || "")}</div>
      </div>
      <span class="event-time">${esc(relTime(e.at))}</span>
    </li>`;
}
function renderAudit() {
  const f = $("#audit-filter").value;
  const evs = (STATE.events || []).filter((e) => f === "all" || e.type === f);
  $("#audit-count").textContent = `${evs.length} events`;
  $("#audit-list").innerHTML = evs.length ? evs.map(eventItemHTML).join("") : `<li class="empty">No matching audit events.</li>`;
}

// ====================================================== transport effects
function snapshotUrl(slug) {
  return isStatic() ? `./data/${encodeURIComponent(slug)}/state.json` : `/api/state?mission=${encodeURIComponent(slug)}`;
}
async function getSnapshot(slug) {
  if (SNAP_CACHE.has(slug)) return SNAP_CACHE.get(slug);
  const snap = await fetchJSON(snapshotUrl(slug));
  if (!snap?.ready) throw new Error("snapshot not ready");
  SNAP_CACHE.set(slug, snap);
  return snap;
}

async function boot() {
  dispatch({ type: "RETRY" });
  const preferStatic = location.hostname.endsWith(".github.io") || location.protocol === "file:";
  const sources = preferStatic
    ? [{ url: "./data/missions.json", isStatic: true }, { url: "/api/missions", isStatic: false }]
    : [{ url: "/api/missions", isStatic: false }, { url: "./data/missions.json", isStatic: true }];
  let lastErr = null;
  let mode = null;
  for (const src of sources) {
    try {
      const data = await fetchJSON(src.url);
      if (!Array.isArray(data.missions)) throw new Error("malformed catalog");
      CATALOG = data.missions;
      mode = src.isStatic || data.static ? "static" : "live";
      break;
    } catch (err) {
      lastErr = err;
    }
  }
  if (!mode) {
    dispatch({ type: "CATALOG_FAILED", error: `Could not load the Proof Foundry catalog (${lastErr?.message || "network error"}).` });
    return;
  }
  dispatch({ type: "CATALOG_LOADED", mode });
  renderCurrent();
  const r = ui().route;
  const slug = CATALOG.some((m) => m.slug === r.mission) ? r.mission : CATALOG.find((m) => m.slug === DEFAULT_MISSION)?.slug || CATALOG[0]?.slug;
  loadRecords();
  if (slug) requestMission(slug, { intent: { view: r.view, ledgerTab: r.ledgerTab, claim: r.claim }, push: false });
}

async function loadRecords() {
  const urls = isStatic() ? ["./data/records.json"] : ["/api/records", "./data/records.json"];
  let payload = null;
  for (const url of urls) {
    try {
      payload = normalizeRecordsPayload(await fetchJSON(url));
      if (payload?.records.length) break;
      payload = null;
    } catch {
      /* fall through to the next source */
    }
  }
  if (!payload) {
    const snaps = await Promise.all(CATALOG.map((m) => getSnapshot(m.slug).catch(() => null)));
    payload = synthesizeRecordsPayload(snaps.filter(Boolean), CATALOG);
  }
  if (STATE) payload = mergeSnapshotIntoRecords(payload, STATE);
  RECORDS = payload;
  renderCurrent();
}

async function requestMission(slug, { intent = null, push = true } = {}) {
  dispatch({ type: "MISSION_REQUESTED", mission: slug, intent });
  const seq = ui().transport.reqSeq;
  try {
    const snap = await fetchJSON(snapshotUrl(slug));
    if (!snap?.ready) throw new Error("snapshot not ready");
    if (!isCurrentMissionRequest(ui(), seq)) return; // a newer switch superseded this one
    // Commit: only now is the previous mission's stream released.
    closeSSE();
    STATE = snap;
    SNAP_CACHE.set(slug, snap);
    if (RECORDS) RECORDS = mergeSnapshotIntoRecords(RECORDS, snap);
    LAST_FAILED_MISSION = null;
    PENDING_PUSH = push;
    dispatch({ type: "MISSION_LOADED", mission: slug, reqSeq: seq });
    PENDING_PUSH = false;
    if (ui().transport.mode === "live") openSSE(slug);
    const s = ui();
    if (s.route.claim && s.overlay.kind === "none") openDossier(s.route.claim, slug);
  } catch (err) {
    if (!isCurrentMissionRequest(ui(), seq)) return;
    LAST_FAILED_MISSION = slug;
    dispatch({ type: "MISSION_FAILED", mission: slug, reqSeq: seq, error: `Could not load mission “${slug}” (${err.message}).` });
    syncMissionSelects();
  }
}

function closeSSE() {
  if (SSE) {
    SSE.es.close();
    SSE = null;
  }
}

function openSSE(slug) {
  closeSSE();
  let es;
  try {
    es = new EventSource(`/api/stream?mission=${encodeURIComponent(slug)}`);
  } catch {
    dispatch({ type: "SSE_ERROR", mission: slug });
    return;
  }
  SSE = { es, slug };
  es.onopen = () => SSE?.es === es && dispatch({ type: "SSE_OPEN", mission: slug });
  es.addEventListener("snapshot", (ev) => {
    if (SSE?.es !== es || !acceptsSnapshot(ui(), slug)) return;
    let snap;
    try {
      snap = JSON.parse(ev.data);
    } catch {
      return;
    }
    if (!snap?.ready) return;
    STATE = snap;
    SNAP_CACHE.set(slug, snap);
    if (RECORDS) RECORDS = mergeSnapshotIntoRecords(RECORDS, snap);
    dispatch({ type: "SSE_SNAPSHOT", mission: slug });
    renderCurrent();
    refreshAttemptIfOpen();
  });
  es.onerror = () => SSE?.es === es && dispatch({ type: "SSE_ERROR", mission: slug });
}

function navigate(view, { ledgerTab, mission } = {}) {
  if (mission && mission !== activeSlug()) {
    requestMission(mission, { intent: { view, ledgerTab, claim: null }, push: true });
    return;
  }
  dispatch({ type: "ROUTE_NAVIGATE", route: { view, ledgerTab, claim: null }, push: true });
}

// ====================================================== machine listeners
function renderTransport(t) {
  const dot = $("#conn-dot");
  dot.className = "live-dot";
  let label = "Connecting…";
  if (t.status === "live_connected") {
    dot.classList.add("is-live");
    label = `Live · streaming ${t.activeMission}`;
  } else if (t.status === "live_reconnecting") {
    dot.classList.add("is-warn");
    label = "Reconnecting to the live stream…";
  } else if (t.status === "static_ready") {
    dot.classList.add("is-static");
    label = `Static snapshot · ${relTime(STATE?.snapshot_at) || "published build"}`;
  } else if (t.status === "error") {
    dot.classList.add("is-warn");
    label = "Offline";
  }
  dot.title = label;
  dot.setAttribute("aria-label", label);
  $("#footer-sync").textContent = label;
  $("#status-banner").hidden = !t.error;
  $("#status-msg").textContent = t.error || "";
  $("#status-retry").hidden = !(t.status === "error" || LAST_FAILED_MISSION);
}

function renderRoute(r, prevRoute) {
  for (const v of ["missions", "records", "control", "bounties", "ledger"]) $(`#view-${v}`).hidden = v !== r.view;
  $$(".nav [data-nav]").forEach((a) => {
    const on = a.dataset.nav === r.view || (r.view === "control" && a.dataset.nav === "missions");
    a.classList.toggle("is-active", on);
    if (on) a.setAttribute("aria-current", "page");
    else a.removeAttribute("aria-current");
  });
  const titles = { missions: "Proof Foundry · A Public Ledger of Machine-Checked Mathematics", records: "World Records · Proof Foundry", control: `${STATE?.mission?.title || "Mission"} · Proof Foundry`, bounties: "Open Problems · Proof Foundry", ledger: "Ledger · Proof Foundry" };
  document.title = titles[r.view] || titles.missions;
  if (!prevRoute || prevRoute.view !== r.view || prevRoute.mission !== r.mission || prevRoute.ledgerTab !== r.ledgerTab) {
    if (prevRoute && (prevRoute.view !== r.view || prevRoute.mission !== r.mission)) window.scrollTo({ top: 0 });
  }
}

function writeURL(route, push) {
  const next = serializeRouteToLocation(route, { pathname: location.pathname });
  const cur = `${location.pathname}${location.search}${location.hash}`;
  if (next === cur) return;
  if (push) history.pushState(null, "", next);
  else history.replaceState(null, "", next);
}

machine.subscribe((s, prev, ev) => {
  if (s.transport !== prev.transport) renderTransport(s.transport);
  const routeChanged = s.route !== prev.route;
  if (routeChanged) {
    renderRoute(s.route, prev.route);
    writeURL(s.route, ev.push === true || (ev.type === "MISSION_LOADED" && PENDING_PUSH));
  } else if (ev.type === "MISSION_LOADED") {
    writeURL(s.route, false); // canonicalise legacy aliases (#graveyard → #ledger/refutations)
  }
  const viewChanged = routeChanged && (s.route.view !== prev.route.view || s.route.mission !== prev.route.mission || s.route.ledgerTab !== prev.route.ledgerTab);
  if (viewChanged || ev.type === "MISSION_LOADED" || ev.type === "CATALOG_LOADED") renderCurrent();
  if (s.overlay !== prev.overlay) renderOverlay(s.overlay, prev.overlay);
});

// ================================================================ overlays
function renderOverlay(o, p) {
  if (o.kind !== p.kind) {
    if (p.kind === "none") FOCUS_RETURN = document.activeElement;
    $("#scrim").hidden = o.kind === "none";
    $("#dossier").hidden = o.kind !== "dossier";
    $("#attempt-modal").hidden = o.kind !== "attempt";
    $("#search-modal").hidden = o.kind !== "search";
    $("#shell").inert = o.kind !== "none";
    document.body.style.overflow = o.kind === "none" ? "" : "hidden";
    if (o.kind === "none") {
      if (FOCUS_RETURN && document.contains(FOCUS_RETURN) && typeof FOCUS_RETURN.focus === "function") FOCUS_RETURN.focus();
      FOCUS_RETURN = null;
      if (isMapVisible()) requestAnimationFrame(drawMap);
    }
  }
  if (o.kind === "dossier") renderDossier(o, p);
  else if (o.kind === "attempt") renderAttempt(o, p);
  else if (o.kind === "search") renderSearch(o, p);
}

function overlayRoot(kind) {
  return kind === "dossier" ? $("#dossier") : kind === "attempt" ? $("#attempt-modal") : kind === "search" ? $("#search-modal") : null;
}

// --------------------------------------------------------------- dossier
async function openDossier(claimId, mission = activeSlug()) {
  if (!claimId) return;
  dispatch({ type: "OPEN_DOSSIER", claimId, mission });
  const o = ui().overlay;
  if (o.kind !== "dossier") return;
  const { reqSeq } = o;
  const url = isStatic()
    ? `./data/${encodeURIComponent(mission)}/lemmas/${encodeURIComponent(claimId)}.json`
    : `/api/lemma/${encodeURIComponent(claimId)}?mission=${encodeURIComponent(mission)}`;
  try {
    const data = await fetchJSON(url);
    if (!data?.lemma) throw new Error("claim not found");
    dispatch({ type: "DOSSIER_LOADED", reqSeq, data });
  } catch (err) {
    dispatch({ type: "DOSSIER_FAILED", reqSeq, error: err.message });
  }
}

function kv(rows) {
  return `<dl class="d-kv">${rows
    .filter(Boolean)
    .map(([k, v, mono]) => `<dt>${esc(k)}</dt><dd class="${mono ? "mono" : ""}">${v}</dd>`)
    .join("")}</dl>`;
}

function receiptHTML(chk, label) {
  if (!chk) return "";
  return `<section class="d-section"><h4>Judge receipt${label ? ` · ${esc(label)}` : ""}</h4>${kv([
    ["Engine", esc(chk.lean_version || chk.judge || "Lean 4")],
    ["Checked", esc(chk.checked_at ? `${longDate(chk.checked_at)} · ${relTime(chk.checked_at)}` : chk.at ? relTime(chk.at) : "—")],
    ["Seat", esc(chk.by_seat || chk.seat || "—"), true],
    ["Duration", `${int(chk.duration_ms)} ms`, true],
    ["Axioms", esc((chk.axioms || []).join(", ") || "none beyond the kernel"), true],
    ["Artifact SHA-256", esc(chk.file_hash || "—"), true],
    chk.statement_hash ? ["Statement SHA-256", esc(chk.statement_hash), true] : null,
    chk.core_hash ? ["Core SHA-256", esc(chk.core_hash), true] : null,
  ])}</section>`;
}

function renderDossier(o, p) {
  const fresh = p.kind !== "dossier" || p.claimId !== o.claimId || p.mission !== o.mission;
  $("#dossier-id").textContent = o.claimId;
  const body = $("#dossier-body");
  if (o.status === "loading") {
    $("#dossier-status").innerHTML = `<span class="st tone-muted"><span class="st-label">Loading…</span></span>`;
    body.innerHTML = `<p class="empty">Fetching the verification receipt and source…</p>`;
  } else if (o.status === "error") {
    $("#dossier-status").innerHTML = "";
    body.innerHTML = `<div class="audit-box is-alarm"><strong>Could not load the dossier for ${esc(o.claimId)}</strong> <span class="small">(${esc(o.error)})</span></div><div class="d-actions"><button class="btn btn-sm" type="button" data-dossier-retry>Retry</button></div>`;
  } else {
    const d = o.data;
    const l = d.lemma;
    $("#dossier-status").innerHTML = `${statusHTML(l)} ${flagsHTML(l)}`;
    body.innerHTML = dossierBodyHTML(d, o.mission);
  }
  if (fresh) $("#dossier-close").focus();
}

function dossierBodyHTML(d, mission) {
  const l = d.lemma;
  const isRec = l.kind === "record";
  const rm = recordMetaOf(l);
  const snap = SNAP_CACHE.get(mission) || STATE;
  const meta = missionMeta(mission);
  const acts = actionsOf(l);
  const fresh = freshnessOf(l);

  const freshHTML =
    fresh === "stale_statement"
      ? `<div class="audit-box"><strong>↻ Stale statement.</strong> The frozen statement file changed after this result was checked. The receipt is preserved, but it must be re-verified against the current statement.</div>`
      : fresh === "stale_core"
      ? `<div class="audit-box"><strong>↻ Stale core.</strong> Shared core definitions changed after this check. The statement hash still matches, so this is advisory.</div>`
      : "";

  const audit = l.audit
    ? `<div class="audit-box ${l.audit.status === "faithful" ? "is-faithful" : l.audit.status === "flagged" ? "is-flagged" : ""}"><strong>Cross-model audit · ${esc(l.audit.status)}</strong> <span class="small muted">${esc(l.audit.by_model || l.audit.by_seat || "")}${l.audit.at ? ` · ${esc(relTime(l.audit.at))}` : ""}</span><div style="margin-top:6px">${esc(l.audit.notes || "")}</div></div>`
    : !isRec && sealOf(l) === "provisional"
    ? `<div class="audit-box"><strong>Provisional.</strong> Passed the mechanical Judge; awaiting an independent cross-model faithfulness audit before it counts toward objectives.</div>`
    : "";

  const attemptLabel = isRec ? (rm.best_score != null ? `Beat ${rm.best_score} (${rm.op} ${rm.next_target}) →` : `Claim the launch target ${rm.op} ${rm.next_target} →`) : "Attempt this problem →";
  const actions = acts.can_attempt
    ? `<div class="d-actions"><button class="btn btn-primary" type="button" data-attempt="${esc(l.id)}" data-mission="${esc(mission)}">${esc(attemptLabel)}</button>${acts.reason ? `<span class="small muted">${esc(acts.reason)}</span>` : ""}</div>`
    : acts.reason && !/^status:/.test(String(acts.reason))
    ? `<div class="d-actions"><span class="small muted">Closed to attempts: ${esc(acts.reason)}</span></div>`
    : "";

  let record = "";
  if (isRec) {
    const unit = esc(rm.unit || "");
    const boundWord = rm.direction === "max" ? "upper" : "lower";
    const hist = [...(rm.history || [])].reverse();
    record = `
      <section class="d-section"><h4>♛ King of the Hill · ${rm.direction === "max" ? "maximize" : "minimize"}</h4>
        ${boundBarHTML(recordRowFromLemma(l, snap?.mission || {}))}
        ${kv([
          ["Record holder", rm.best_score != null ? `<strong class="tone-accent">${int(rm.best_score)}</strong> ${unit} · <span class="mono">${esc(rm.best_seat || "")}</span>` : `Unclaimed · launch ${esc(rm.op)} ${int(rm.start_target)} ${unit}`],
          ["Next target", rm.contradiction ? "Halted (contradiction)" : rm.closed ? "Closed — optimum proven" : `${esc(rm.op)} ${int(rm.next_target)} ${unit}`, true],
          [`Proven ${boundWord} bound`, rm.proven_bound != null ? `${rm.direction === "max" ? "≤" : "≥"} ${int(rm.proven_bound)} ${unit}` : rm.allow_bound ? "None proven here yet" : "Not applicable (command Judge)"],
          ["Literature", [rm.literature_best != null ? `best known ${int(rm.literature_best)}` : null, rm.literature_bound != null ? `${rm.direction === "max" ? "UB" : "LB"} ${int(rm.literature_bound)}` : null].filter(Boolean).join(" · ") || "—"],
          ["Open gap", rm.gap != null ? `${int(rm.gap)} ${unit}` : "—", true],
        ])}
      </section>
      <section class="d-section"><h4>Ratchet history · ${hist.length}</h4>
        ${
          hist.length
            ? `<ul class="hist">${hist
                .map(
                  (h) =>
                    `<li><span><strong class="mono">${h.kind === "record_bound" ? "¬ Record" : "Record"} ${int(h.score)}</strong> · <span class="mono small">${esc(h.seat || "")}</span>${h.at ? ` <span class="small muted">${esc(relTime(h.at))}</span>` : ""}</span><span class="small ${h.state === "accepted" ? "tone-accent" : h.state === "contradiction" ? "tone-alarm" : "muted"}">${esc(String(h.state || "").replace(/_/g, " "))}${h.points > 0 ? ` · +${int(h.points)} pts` : ""}</span></li>`
                )
                .join("")}</ul>`
            : `<p class="empty">No verified entries yet — the launch target ${esc(rm.op)} ${int(rm.start_target)} ${unit} is open.</p>`
        }
      </section>`;
  }

  const receipts = isRec
    ? `${receiptHTML(l.record_state?.best, "current record")}${receiptHTML(l.record_state?.refuted, "proven bound")}`
    : receiptHTML(l.checker || l.refutation, l.refutation && !l.checker ? "counterexample" : "");

  const statementBlock = `<section class="d-section"><h4>Formal statement${l.statement_file ? ` · <span class="mono">${esc(l.statement_file)}</span>` : ""}</h4><pre class="lean-block">${esc(l.verified_signature || l.registered_statement || l.statement || "")}</pre></section>`;
  const frozenSrc = d.statementSource ? `<section class="d-section"><h4>Statement source</h4><pre class="source-pre">${esc(d.statementSource)}</pre></section>` : "";
  const srcCode = isRec ? d.leanSource : l.status === "refuted" ? d.refutationSource : d.leanSource;
  const srcPath = isRec ? l.record_state?.best?.file : l.status === "refuted" ? l.refutation?.counterexample_file : l.lean_file;
  const proofSrc = srcCode ? `<section class="d-section"><h4>${isRec ? "Current record artifact" : l.status === "refuted" ? "Counterexample source" : "Proof source"} · <span class="mono">${esc(srcPath || "")}</span></h4><pre class="source-pre">${esc(srcCode)}</pre></section>` : "";
  const boundSrc = isRec && d.refutationSource ? `<section class="d-section"><h4>Proven bound artifact · <span class="mono">${esc(l.record_state?.refuted?.file || "")}</span></h4><pre class="source-pre">${esc(d.refutationSource)}</pre></section>` : "";
  const deps =
    (l.deps || []).length || (d.dependents || []).length
      ? `<section class="d-section"><h4>Dependencies</h4><div class="chip-row">${(l.deps || [])
          .map((id) => `<button class="chip-link" type="button" data-open-claim="${esc(id)}" data-mission="${esc(mission)}">← ${esc(id)}</button>`)
          .join("")}${(d.dependents || []).map((x) => `<button class="chip-link" type="button" data-open-claim="${esc(x.id)}" data-mission="${esc(mission)}">${esc(x.id)} →</button>`).join("")}</div></section>`
      : "";

  return `
    <p class="eyebrow">${esc(meta?.title || snap?.mission?.title || mission)}${programTitle(snap, l.program) ? ` · ${esc(programTitle(snap, l.program))}` : ""}</p>
    <h2 class="d-title">${esc(isRec ? cleanRecordTitle(l.title) : l.title)}</h2>
    <div class="d-meta">${l.theorem_name ? `<span class="mono">${esc(l.theorem_name)}</span>` : ""}${l.rung ? `<span>rung ${int(l.rung)}</span>` : ""}</div>
    ${l.paper_notes ? `<p class="d-notes">${esc(l.paper_notes)}</p>` : ""}
    ${freshHTML}
    ${audit}
    ${actions}
    ${record}
    ${statementBlock}
    ${receipts}
    ${frozenSrc}
    ${proofSrc}
    ${boundSrc}
    ${deps}`;
}

// --------------------------------------------------------------- attempt
async function openAttempt(mission, claimId) {
  mission = mission || activeSlug();
  let lemma = lemmaFor(mission, claimId);
  if (!lemma) {
    try {
      const snap = await getSnapshot(mission);
      lemma = snap.lemmas.find((l) => l.id === claimId) || null;
    } catch (err) {
      showToast(`Could not load ${claimId} (${err.message})`);
      return;
    }
  }
  if (!lemma || !isAttemptable(lemma)) {
    showToast(`${claimId} is not open for attempts right now.`);
    return;
  }
  dispatch({
    type: "OPEN_ATTEMPT",
    claimId,
    mission,
    harness: storageGet("pf-harness", "claude"),
    handle: storageGet("pf-handle", ""),
    recKind: "record",
    recScore: lemma.kind === "record" ? defaultRecordScore(lemma, "record") : null,
  });
}

function defaultRecordScore(lemma, kind) {
  const rm = recordMetaOf(lemma);
  if (!rm) return null;
  const isMax = rm.direction === "max";
  if (kind === "record_bound") {
    if (isMax) {
      if (rm.refuted_score != null) return Math.max(0, rm.refuted_score - 1);
      const floor = int(rm.bound_floor ?? rm.score_max ?? 1000);
      const lit = rm.literature_bound != null ? int(rm.literature_bound) + 1 : floor;
      return Math.min(floor, lit);
    }
    if (rm.refuted_score != null) return rm.refuted_score + 1;
    const floor = int(rm.bound_floor ?? 0);
    const lit = rm.literature_bound != null ? Math.max(0, int(rm.literature_bound) - 1) : floor;
    return Math.max(floor, lit);
  }
  return int(rm.next_target ?? rm.start_target ?? 0);
}

function validateRecordScore(lemma, kind, raw) {
  const rm = recordMetaOf(lemma);
  const isMax = rm.direction === "max";
  const str = String(raw ?? "").trim();
  if (!/^(0|[1-9][0-9]*)$/.test(str)) return { ok: false, reason: "Enter a non-negative integer score." };
  const score = Number(str);
  const scoreMax = int(rm.score_max ?? 100000);
  if (!Number.isSafeInteger(score) || score > scoreMax) return { ok: false, reason: `Score must be between 0 and ${scoreMax}.` };
  const best = rm.best_score;
  const ref = rm.refuted_score;
  if (kind === "record_bound") {
    if (!rm.allow_bound) return { ok: false, reason: "Bound proofs are not supported on command-Judge hunts." };
    const floor = int(rm.bound_floor ?? 0);
    if (isMax) {
      if (ref != null && score >= ref) return { ok: false, reason: `Must beat ¬ Record ${ref} (enter < ${ref}).` };
      if (ref == null && score > floor) return { ok: false, reason: `Must be at most ${floor} (proves ≤ ${Math.max(0, floor - 1)}).` };
      if (best != null && score <= best) return { ok: false, reason: `Conflicts with the verified record ${best} (enter > ${best}).` };
      return { ok: true, score };
    }
    if (ref != null && score <= ref) return { ok: false, reason: `Must beat ¬ Record ${ref} (enter > ${ref}).` };
    if (ref == null && score < floor) return { ok: false, reason: `Must be at least ${floor} (proves ≥ ${floor + 1}).` };
    if (best != null && score >= best) return { ok: false, reason: `Conflicts with the verified record ${best} (enter < ${best}).` };
    return { ok: true, score };
  }
  const start = int(rm.start_target ?? 0);
  if (isMax) {
    if (best != null && score <= best) return { ok: false, reason: `Must beat the record ${best} (enter ≥ ${best + 1}).` };
    if (best == null && score < start) return { ok: false, reason: `Must meet the launch floor ${start} (enter ≥ ${start}).` };
    if (rm.proven_bound != null && score > rm.proven_bound) return { ok: false, reason: `Conflicts with the proven upper bound ≤ ${rm.proven_bound}.` };
    return { ok: true, score };
  }
  if (best != null && score >= best) return { ok: false, reason: `Must beat the record ${best} (enter ≤ ${best - 1}).` };
  if (best == null && score > start) return { ok: false, reason: `Must meet the launch ceiling ${start} (enter ≤ ${start}).` };
  if (rm.proven_bound != null && score < rm.proven_bound) return { ok: false, reason: `Conflicts with the proven lower bound ≥ ${rm.proven_bound}.` };
  return { ok: true, score };
}

function recordTargets(slug, lemma, kind, score) {
  const rm = recordMetaOf(lemma);
  const tag = kind === "record_bound" ? `not_s${score}` : `s${score}`;
  const stem = rm.file_stem || lemma.id.replace(/-/g, "_");
  const claimsDir = rm.claims_dir || `missions/${slug}/lean/Claims`;
  const ext = rm.artifact_ext || ".lean";
  return {
    tag,
    artifactFile: `${claimsDir}/${stem}_${tag}${ext}`,
    submissionFile: `missions/${slug}/submissions/${lemma.id}.${kind}.s${score}.json`,
    theoremName: (rm.theorem_template || `${stem}_{tag}.record`).replace(/\{tag\}/g, tag),
  };
}

function buildPrompt(lemma, o) {
  const snap = SNAP_CACHE.get(o.mission) || STATE;
  const slug = o.mission || snap?.mission?.slug;
  const repo = repoOf(snap);
  const handle = (o.handle || "my-handle").toLowerCase().replace(/[^a-z0-9-_]/g, "") || "my-handle";
  const seat = `donor-${handle}`;
  const preamble =
    {
      claude: "You are helping me contribute spare Claude Code tokens to Proof Foundry.",
      codex: "You are helping me contribute spare Codex tokens to Proof Foundry.",
      gemini: "You are helping me contribute spare Gemini CLI tokens to Proof Foundry.",
      t3: "Run this end-to-end in an isolated worktree to contribute to Proof Foundry.",
    }[o.harness] || "Contribute my spare AI tokens to Proof Foundry.";

  if (lemma.kind === "record") {
    const rm = recordMetaOf(lemma);
    const isMax = rm.direction === "max";
    const isCmd = rm.artifact_ext && rm.artifact_ext !== ".lean";
    const kind = !isCmd && rm.allow_bound && o.recKind === "record_bound" ? "record_bound" : "record";
    const check = validateRecordScore(lemma, kind, o.recScore);
    if (!check.ok) return `# Invalid target score: ${check.reason}\n# Fix the score above to generate a valid Judge & PR-gate prompt.`;
    const score = check.score;
    const t = recordTargets(slug, lemma, kind, score);
    const branch = `donor/${lemma.id.toLowerCase()}-${t.tag}-${handle}`;
    if (isCmd) {
      return [
        preamble,
        `Repository: https://github.com/${repo}`,
        `Mission: ${slug} · King-of-the-Hill hunt: ${lemma.id} (target ${rm.op} ${score} ${rm.unit})`,
        `Goal: ${lemma.title}`,
        ``,
        `Instructions:`,
        `1. Clone/pull \`https://github.com/${repo}\`, create branch \`${branch}\`, and read \`CONTRIBUTING_AGENTS.md\`.`,
        `2. Read the FROZEN spec in \`${lemma.statement_file}\` and the trusted verifier harness (do NOT edit specs/ or judge/).`,
        `3. Write a NEW score-stamped pure-data module at \`${t.artifactFile}\` exporting only the required float64 \`coeffs\` array, achieving worst-case error ${rm.op} ${score} ${rm.unit}. No imports, no Math calls, no code paths — data only. Never edit older score files.`,
        `4. Verify locally & export the hashless record submission JSON:`,
        `   node hub/fleet.mjs record --mission ${slug} --lemma ${lemma.id} --score ${score} --seat ${seat} --export`,
        `5. Commit ONLY \`${t.artifactFile}\` + \`${t.submissionFile}\` (never touch state.json or older files), push, and open a PR referencing ${lemma.id}.`,
        `Note: this hunt uses an empirical command Judge, so impossibility-bound submissions (¬ Record) are not accepted.`,
      ].join("\n");
    }
    const typeStr = kind === "record_bound" ? `¬ ${lemma.statement_def} ${score}` : `${lemma.statement_def} ${score}`;
    const ns = t.theoremName.split(".").slice(0, -1).join(".");
    const shortThm = t.theoremName.split(".").pop();
    const boundHeader = isMax ? `upper bound ≤ ${Math.max(0, score - 1)}` : `lower bound ≥ ${score + 1}`;
    return [
      preamble,
      `Repository: https://github.com/${repo}`,
      `Mission: ${slug} · King-of-the-Hill hunt: ${lemma.id} (${kind === "record_bound" ? boundHeader : `record ${rm.op} ${score}`})`,
      `Goal: ${lemma.title}`,
      ``,
      `Instructions:`,
      `1. Clone/pull \`https://github.com/${repo}\`, create branch \`${branch}\`, and read \`CONTRIBUTING_AGENTS.md\`.`,
      `2. Read the FROZEN record statement in \`${lemma.statement_file}\` (do NOT modify Core or Statements files).`,
      `3. Write a NEW score-stamped Lean 4 file at \`${t.artifactFile}\` (no sorry, no admit, no native_decide, no custom axioms) inside \`namespace ${ns}\` proving literally:`,
      `   \`theorem ${shortThm} : ${typeStr} := ...\``,
      `   (Use the canonical numeral literal \`${score}\`${kind === "record_bound" ? " and literally `¬`, not `→ False`" : ""} — never edit older score files.)`,
      `4. Verify locally & export the hashless record submission JSON:`,
      `   node hub/fleet.mjs ${kind === "record_bound" ? "record-bound" : "record"} --mission ${slug} --lemma ${lemma.id} --score ${score} --seat ${seat} --file ${t.artifactFile} --export`,
      `5. Commit ONLY \`${t.artifactFile}\` + \`${t.submissionFile}\` (never touch state.json or older files), push, and open a PR referencing ${lemma.id}.`,
    ].join("\n");
  }

  const branch = `donor/${lemma.id.toLowerCase()}-${handle}`;
  const thm = String(lemma.theorem_name || "").split(".").pop();
  const frozenStep = lemma.statement_file
    ? `2. Read the FROZEN formal statement in \`${lemma.statement_file}\`.\n   Your proof MUST import that module and state your theorem literally as:\n   \`theorem ${thm} : ${lemma.statement_def} := ...\`\n   (Or \`: ¬ ${lemma.statement_def}\` if you find a genuine counterexample.)`
    : `2. Read \`${snap?.mission?.judge?.core_file || "CONTRIBUTING_AGENTS.md"}\` and state your theorem matching:\n   \`${lemma.theorem_name} : ${lemma.registered_statement || lemma.statement}\`.`;
  return [
    preamble,
    `Repository: https://github.com/${repo}`,
    `Mission: ${slug} · Claim: ${lemma.id}`,
    `Goal: ${lemma.title}`,
    ``,
    `Instructions:`,
    `1. Clone/pull \`https://github.com/${repo}\`, create branch \`${branch}\`, and read \`CONTRIBUTING_AGENTS.md\`.`,
    frozenStep,
    `3. Write your isolated artifact in \`${lemma.lean_file}\` (no sorry, no admit, no native_decide, no custom axioms).`,
    `4. Run the local mechanical Judge & export a conflict-free submission JSON:`,
    `   node hub/fleet.mjs verify --mission ${slug} --lemma ${lemma.id} --seat ${seat} --file ${lemma.lean_file} --theorem ${lemma.theorem_name} --export`,
    `   (If the claim is false, use \`refute --summary "..."\` with a Judge-verified counterexample.)`,
    `5. Revert any edits to state.json/events.ndjson, commit ONLY \`${lemma.lean_file}\` + \`missions/${slug}/submissions/${lemma.id}.*.json\`, push, and open a PR referencing ${lemma.id}.`,
  ].join("\n");
}

function renderAttempt(o, p) {
  const lemma = lemmaFor(o.mission, o.claimId);
  if (!lemma) {
    dispatch({ type: "CLOSE_OVERLAY" });
    return;
  }
  const isNew = p.kind !== "attempt" || p.claimId !== o.claimId || p.mission !== o.mission;
  const snap = SNAP_CACHE.get(o.mission) || STATE;
  const isRec = lemma.kind === "record";
  const rm = recordMetaOf(lemma);
  if (isNew) {
    $("#attempt-meta").textContent = [missionMeta(o.mission)?.title || o.mission, lemma.id, isRec ? "♛ King of the Hill" : lemma.statement_file ? "◆ Frozen statement" : "Free-form statement"].join(" · ");
    $("#attempt-title").textContent = isRec ? cleanRecordTitle(lemma.title) : lemma.title;
    $("#attempt-gh").href = `https://github.com/${repoOf(snap)}/pulls`;
    const prs = lemma.open_prs || [];
    const warn = $("#attempt-pr-warn");
    warn.hidden = !prs.length;
    if (prs.length) {
      const links = prs.map((pr) => `<a href="${esc(pr.url)}" target="_blank" rel="noopener noreferrer">#${int(pr.number)}</a>`).join(", ");
      warn.innerHTML = isRec
        ? `<strong>Active competition.</strong> PR ${links} also targets <code>${esc(lemma.id)}</code>. Any strictly better score or bound still counts.`
        : `<strong>Heads up.</strong> PR ${links} already targets <code>${esc(lemma.id)}</code>; consider another problem to avoid duplicate work.`;
    }
    setTimeout(() => $("#attempt-copy").focus(), 0);
  }
  $$("#attempt-harness [data-harness]").forEach((b) => b.setAttribute("aria-selected", String(b.dataset.harness === o.harness)));
  const handleEl = $("#attempt-handle");
  if (document.activeElement !== handleEl && handleEl.value !== o.handle) handleEl.value = o.handle;

  const recBox = $("#attempt-record");
  recBox.hidden = !isRec;
  const copy = $("#attempt-copy");
  copy.disabled = false;
  if (isRec) {
    const isCmd = rm.artifact_ext && rm.artifact_ext !== ".lean";
    const allowBound = rm.allow_bound && !isCmd;
    const kind = allowBound ? o.recKind : "record";
    $$("#attempt-reckind [data-reckind]").forEach((b) => {
      if (b.dataset.reckind === "record") b.textContent = `Improve record (${rm.op} s)`;
      else {
        b.textContent = rm.direction === "max" ? "Prove upper bound (¬ Record b)" : "Prove lower bound (¬ Record b)";
        b.hidden = !allowBound;
      }
      b.setAttribute("aria-selected", String(b.dataset.reckind === kind));
    });
    const scoreEl = $("#attempt-score");
    const want = o.recScore == null ? "" : String(o.recScore);
    if (document.activeElement !== scoreEl && scoreEl.value !== want) scoreEl.value = want;
    $("#attempt-score-label").textContent =
      kind === "record_bound" ? (rm.direction === "max" ? "Refute b (proves ≤ b−1)" : "Refute b (proves ≥ b+1)") : `Target${rm.unit ? ` (${rm.unit})` : ""}`;
    const check = validateRecordScore(lemma, kind, o.recScore);
    const hint = $("#attempt-hint");
    hint.classList.toggle("is-bad", !check.ok);
    hint.textContent = check.ok ? "✓ valid target" : check.reason;
    copy.disabled = !check.ok;
  }
  $("#attempt-prompt").value = buildPrompt(lemma, o);
}

function refreshAttemptIfOpen() {
  const o = ui().overlay;
  if (o.kind === "attempt") renderAttempt(o, o);
}

// ---------------------------------------------------------------- search
function searchCorpus() {
  const items = [];
  const views = [
    ["missions", null, "Missions — front page"],
    ["records", null, "World records board"],
    ["bounties", null, "Open problems & claim ledger"],
    ["control", null, "Mission control"],
    ["ledger", "map", "Ledger · proof map & DAG"],
    ["ledger", "leaderboard", "Ledger · leaderboard"],
    ["ledger", "refutations", "Ledger · refutations & barriers"],
    ["ledger", "fleet", "Ledger · fleet"],
    ["ledger", "audit", "Ledger · audit log"],
  ];
  for (const [view, tab, title] of views) items.push({ group: "Views", glyph: "§", title, sub: tab ? `ledger/${tab}` : view, run: () => navigate(view, { ledgerTab: tab || undefined }) });
  CATALOG.forEach((m, i) => items.push({ group: "Missions", glyph: toRoman(i + 1), title: m.title, sub: m.slug, hay: `${m.question || ""} ${m.tagline || ""}`, run: () => navigate("control", { mission: m.slug }) }));
  for (const r of RECORDS?.records || []) {
    items.push({ group: "Records", glyph: "♛", title: `${r.id} · ${cleanRecordTitle(r.title)}`, sub: r.mission, hay: r.mission_title, run: () => openDossier(r.id, r.mission) });
  }
  for (const l of STATE?.lemmas || []) {
    if (l.kind === "record") continue;
    const s = statusOf(l);
    items.push({ group: `Claims · ${STATE.mission.title}`, glyph: s.glyph, title: `${l.id} · ${l.title}`, sub: s.label.toLowerCase(), hay: `${l.theorem_name || ""} ${l.statement || ""}`, run: () => openDossier(l.id, STATE.mission.slug) });
  }
  return items;
}

function computeSearchResults(query) {
  const all = searchCorpus();
  const terms = query.trim().toLowerCase().split(/\s+/).filter(Boolean);
  if (!terms.length) {
    const pick = (g, n) => all.filter((i) => i.group === g).slice(0, n);
    return [...pick("Views", 5), ...pick("Missions", 6), ...all.filter((i) => i.group === "Records").slice(0, 5)];
  }
  return all.filter((i) => {
    const hay = `${i.title} ${i.sub} ${i.hay || ""} ${i.group}`.toLowerCase();
    return terms.every((t) => hay.includes(t));
  }).slice(0, 40);
}

function openSearch(query = "") {
  dispatch({ type: "OPEN_SEARCH", query });
}

function renderSearch(o, p) {
  const input = $("#search-input");
  if (p.kind !== "search" || p.query !== o.query) SEARCH_RESULTS = computeSearchResults(o.query);
  if (p.kind !== "search") {
    input.value = o.query;
    setTimeout(() => input.focus(), 0);
  }
  let lastGroup = null;
  const html = [];
  SEARCH_RESULTS.forEach((it, idx) => {
    if (it.group !== lastGroup) {
      html.push(`<li class="palette-group" role="presentation">${esc(it.group)}</li>`);
      lastGroup = it.group;
    }
    const sel = idx === o.activeIndex;
    html.push(
      `<li role="presentation"><button type="button" class="palette-item" role="option" id="search-opt-${idx}" aria-selected="${sel}" data-search-idx="${idx}"><span class="muted">${esc(it.glyph)}</span><span class="ttl">${esc(it.title)}</span><span class="sub">${esc(it.sub)}</span></button></li>`
    );
  });
  $("#search-list").innerHTML = html.length ? html.join("") : `<li class="empty" style="padding:14px 16px">No matches.</li>`;
  input.setAttribute("aria-activedescendant", SEARCH_RESULTS.length ? `search-opt-${o.activeIndex}` : "");
  document.getElementById(`search-opt-${o.activeIndex}`)?.scrollIntoView({ block: "nearest" });
}

function runSearchResult(idx) {
  const it = SEARCH_RESULTS[idx];
  dispatch({ type: "CLOSE_OVERLAY" });
  if (it) it.run();
}

// ================================================================= events
document.addEventListener("click", (e) => {
  if (e.target.closest("[data-stop]")) return;
  const attempt = e.target.closest("[data-attempt]");
  if (attempt) {
    e.preventDefault();
    openAttempt(attempt.dataset.mission || activeSlug(), attempt.dataset.attempt);
    return;
  }
  const searchItem = e.target.closest("[data-search-idx]");
  if (searchItem) {
    runSearchResult(Number(searchItem.dataset.searchIdx));
    return;
  }
  if (e.target.closest("[data-dossier-retry]")) {
    const o = ui().overlay;
    if (o.kind === "dossier") openDossier(o.claimId, o.mission);
    return;
  }
  const toggle = e.target.closest("[data-toggle-claim]");
  if (toggle) {
    const id = toggle.dataset.toggleClaim;
    if (BOUNTY.expanded.has(id)) BOUNTY.expanded.delete(id);
    else BOUNTY.expanded.add(id);
    renderBounties();
    document.querySelector(`[data-toggle-claim="${CSS.escape(id)}"]`)?.focus();
    return;
  }
  const claim = e.target.closest("[data-open-claim]");
  if (claim) {
    e.preventDefault();
    openDossier(claim.dataset.openClaim, claim.dataset.mission || activeSlug());
    return;
  }
  const mission = e.target.closest("[data-open-mission]");
  if (mission) {
    navigate("control", { mission: mission.dataset.openMission });
    return;
  }
  const nav = e.target.closest("[data-nav]");
  if (nav) {
    e.preventDefault();
    navigate(nav.dataset.nav, { ledgerTab: nav.dataset.tab, mission: nav.dataset.mission });
  }
});

$("#search-btn").addEventListener("click", () => openSearch());
$("#scrim").addEventListener("click", () => dispatch({ type: "CLOSE_OVERLAY" }));
$("#dossier-close").addEventListener("click", () => dispatch({ type: "CLOSE_OVERLAY" }));
$("#attempt-close").addEventListener("click", () => dispatch({ type: "CLOSE_OVERLAY" }));
$("#take-problem-btn").addEventListener("click", takeOpenProblem);
$("#control-attempt-btn").addEventListener("click", takeOpenProblem);
$("#status-dismiss").addEventListener("click", () => dispatch({ type: "DISMISS_ERROR" }));
$("#status-retry").addEventListener("click", () => {
  if (ui().transport.status === "error" && !activeSlug()) boot();
  else if (LAST_FAILED_MISSION) requestMission(LAST_FAILED_MISSION, { intent: { view: ui().route.view }, push: true });
});

$("#search-input").addEventListener("input", (e) => dispatch({ type: "SEARCH_QUERY", query: e.target.value }));

$("#attempt-harness").addEventListener("click", (e) => {
  const b = e.target.closest("[data-harness]");
  if (!b) return;
  storageSet("pf-harness", b.dataset.harness);
  dispatch({ type: "ATTEMPT_UPDATE", patch: { harness: b.dataset.harness } });
});
$("#attempt-reckind").addEventListener("click", (e) => {
  const b = e.target.closest("[data-reckind]");
  const o = ui().overlay;
  if (!b || o.kind !== "attempt") return;
  const lemma = lemmaFor(o.mission, o.claimId);
  dispatch({ type: "ATTEMPT_UPDATE", patch: { recKind: b.dataset.reckind, recScore: defaultRecordScore(lemma, b.dataset.reckind) } });
});
$("#attempt-score").addEventListener("input", (e) => dispatch({ type: "ATTEMPT_UPDATE", patch: { recScore: e.target.value } }));
$("#attempt-handle").addEventListener("input", (e) => {
  storageSet("pf-handle", e.target.value);
  dispatch({ type: "ATTEMPT_UPDATE", patch: { handle: e.target.value } });
});
$("#attempt-copy").addEventListener("click", async () => {
  const text = $("#attempt-prompt").value;
  try {
    await navigator.clipboard.writeText(text);
    showToast(`Copied the ${ui().overlay.claimId || ""} prompt`);
  } catch {
    $("#attempt-prompt").select();
    showToast("Prompt selected — press ⌘C / Ctrl+C to copy");
  }
});
$("#attempt-select").addEventListener("click", () => {
  $("#attempt-prompt").focus();
  $("#attempt-prompt").select();
});

// filters
$("#rec-mission").addEventListener("change", (e) => {
  REC_FILTER.mission = e.target.value;
  renderRecords();
});
$("#rec-sort").addEventListener("change", (e) => {
  REC_FILTER.sort = e.target.value;
  renderRecords();
});
$("#rec-direction").addEventListener("click", (e) => {
  const b = e.target.closest("[data-dir]");
  if (!b) return;
  REC_FILTER.direction = b.dataset.dir;
  renderRecords();
});
$("#bounty-mode").addEventListener("click", (e) => {
  const b = e.target.closest("[data-bmode]");
  if (!b) return;
  BOUNTY.mode = b.dataset.bmode;
  renderBounties();
});
for (const id of ["#bounty-search", "#bounty-program", "#bounty-seal"]) $(id).addEventListener("input", renderBounties);
$("#audit-filter").addEventListener("change", renderAudit);
$("#ledger-tabs").addEventListener("click", (e) => {
  const b = e.target.closest("[data-tab]");
  if (b) navigate("ledger", { ledgerTab: b.dataset.tab });
});
for (const sel of $$(".mission-switch")) {
  sel.addEventListener("change", (e) => {
    if (e.target.value !== activeSlug()) requestMission(e.target.value, { intent: { view: ui().route.view, claim: null }, push: true });
  });
}

const FOCUSABLE = 'a[href], button:not([disabled]):not([hidden]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])';
document.addEventListener("keydown", (e) => {
  const s = ui();
  if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "k") {
    e.preventDefault();
    if (s.overlay.kind === "search") dispatch({ type: "CLOSE_OVERLAY" });
    else openSearch();
    return;
  }
  if (e.key === "Escape") {
    if (s.overlay.kind !== "none") {
      e.preventDefault();
      dispatch({ type: "ESCAPE" });
    }
    return;
  }
  if (s.overlay.kind === "search") {
    if (e.key === "ArrowDown" || e.key === "ArrowUp") {
      e.preventDefault();
      dispatch({ type: "SEARCH_MOVE", delta: e.key === "ArrowDown" ? 1 : -1, count: SEARCH_RESULTS.length });
      return;
    }
    if (e.key === "Enter") {
      e.preventDefault();
      runSearchResult(s.overlay.activeIndex);
      return;
    }
  }
  if (s.overlay.kind !== "none" && e.key === "Tab") {
    const root = overlayRoot(s.overlay.kind);
    const els = Array.from(root.querySelectorAll(FOCUSABLE)).filter((el) => el.offsetParent !== null);
    if (!els.length) return;
    const first = els[0];
    const last = els[els.length - 1];
    if (e.shiftKey && (document.activeElement === first || !root.contains(document.activeElement))) {
      e.preventDefault();
      last.focus();
    } else if (!e.shiftKey && (document.activeElement === last || !root.contains(document.activeElement))) {
      e.preventDefault();
      first.focus();
    }
    return;
  }
  if (s.overlay.kind !== "none" || isTyping()) return;
  if (e.key === "/") {
    e.preventDefault();
    openSearch();
    return;
  }
  if (e.key === "Enter" || e.key === " ") {
    const el = document.activeElement;
    if (el && el.tagName !== "BUTTON" && el.tagName !== "A" && el.matches("[data-open-claim], [data-open-mission], [data-toggle-claim], [data-nav]")) {
      e.preventDefault();
      el.click();
    }
  }
});

window.addEventListener("popstate", () => {
  const parsed = parseRouteFromLocation(location, { defaultMission: activeSlug() || DEFAULT_MISSION });
  const s = ui();
  if (parsed.mission && parsed.mission !== s.transport.activeMission && CATALOG.some((m) => m.slug === parsed.mission)) {
    if (s.overlay.kind !== "none") dispatch({ type: "CLOSE_OVERLAY" });
    requestMission(parsed.mission, { intent: { view: parsed.view, ledgerTab: parsed.ledgerTab, claim: parsed.claim }, push: false });
    return;
  }
  dispatch({ type: "ROUTE_SYNC", route: parsed });
  const o = ui().overlay;
  if (parsed.claim && !(o.kind === "dossier" && o.claimId === parsed.claim)) openDossier(parsed.claim, activeSlug());
});

// ------------------------------------------------------------------- go
applyTheme(storageGet("pf-theme-v3", "light"));
renderTransport(ui().transport);
renderRoute(ui().route, null);
renderOverlay(ui().overlay, NO_OVERLAY);
renderCurrent();
boot();
