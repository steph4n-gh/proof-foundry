/* PROOF FOUNDRY v2 — Observatory Lab Frontend
 * Covers: All-Missions Hub, 3-Tier Trust Seals, Interactive Donate Modal, ⌘K Command Palette,
 * Race-Safe Mission & Dossier Sequence Guards, Deep-Link URL Sync, Live SSE + Static Pages fallback.
 */
(function () {
  const $ = (sel) => document.querySelector(sel);
  const $$ = (sel) => Array.from(document.querySelectorAll(sel));

  const VALID_VIEWS = ["missions", "control", "bounties", "live", "map", "leaderboard", "graveyard", "feed"];
  const LAB_VIEWS = ["control", "live", "map", "leaderboard", "graveyard", "feed"];

  let STATE = null;
  let MISSIONS = [];
  let STATIC_MODE = false;
  let SSE = null;
  let MISSION_REQ_SEQ = 0;
  let DOSSIER_REQ_SEQ = 0;
  let CURRENT_MISSION = new URLSearchParams(location.search).get("mission") || "erdos-combinatorics";
  let CURRENT_VIEW = (location.hash || "").replace("#", "") || (new URLSearchParams(location.search).get("mission") ? "control" : "missions");
  if (!VALID_VIEWS.includes(CURRENT_VIEW)) CURRENT_VIEW = "missions";
  let BOUNTY_MODE = "open";
  const FOCUS_STACK = [];
  let PENDING_CLAIM_ID = null;

  // Donate modal state
  let DONATE_LEMMA = null;
  let DONATE_HARNESS = localStorage.getItem("pf-harness") || "claude";
  let DONATE_HANDLE = localStorage.getItem("pf-handle") || "";
  let DONATE_REC_KIND = "record";
  let DONATE_REC_SCORE = null;

  // Command palette state
  let CMD_ITEMS = [];
  let CMD_IDX = 0;

  // Theme: localStorage -> prefers-color-scheme fallback
  const prefersLight = window.matchMedia && window.matchMedia("(prefers-color-scheme: light)").matches;
  const savedTheme = localStorage.getItem("pf-theme") || (prefersLight ? "light" : "dark");
  document.documentElement.setAttribute("data-theme", savedTheme);
  $("#theme-toggle").addEventListener("click", () => {
    const next = document.documentElement.getAttribute("data-theme") === "dark" ? "light" : "dark";
    document.documentElement.setAttribute("data-theme", next);
    localStorage.setItem("pf-theme", next);
    if (STATE && CURRENT_VIEW === "map") drawProofMap();
  });

  function esc(s) {
    return String(s ?? "")
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#39;");
  }
  function safeInt(v) {
    const n = Number(v);
    return Number.isFinite(n) ? Math.round(n) : 0;
  }
  function relTime(iso) {
    if (!iso) return "";
    const diff = Math.max(0, Math.floor((Date.now() - new Date(iso).getTime()) / 1000));
    if (diff < 10) return "just now";
    if (diff < 60) return `${diff}s ago`;
    if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
    if (diff < 86400) return `${Math.floor(diff / 3600)}h ago`;
    return `${Math.floor(diff / 86400)}d ago`;
  }
  function showToast(msg) {
    const t = $("#toast");
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(t._tm);
    t._tm = setTimeout(() => (t.hidden = true), 2400);
  }
  function isInputFocused() {
    const el = document.activeElement;
    if (!el) return false;
    const tag = el.tagName;
    return tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT" || el.isContentEditable;
  }

  function sealOf(lemma) {
    if (!lemma) return "open";
    if (lemma.seal) return lemma.seal;
    if (lemma.status === "contradiction" || lemma.record_state?.contradiction) return "contradiction";
    if (lemma.kind === "record") {
      if (lemma.record_state?.closed) return "frozen";
      if (lemma.record_state?.best) return "record";
      return "open";
    }
    if (lemma.audit?.status === "flagged") return "flagged";
    if (lemma.status === "checked") {
      if (lemma.checker?.statement_frozen) return "frozen";
      if (lemma.audit?.status === "faithful") return "audited";
      return "provisional";
    }
    if (lemma.status === "refuted") return "refuted";
    if (lemma.status === "dead") return "dead";
    if (lemma.status === "in_work") return "in_work";
    return "open";
  }

  const SEAL_META = {
    frozen: { label: "◆ Frozen", title: "Kernel type-matched against frozen statement" },
    record: { label: "♛ Record", title: "Active King-of-the-Hill record hunt — open to beat!" },
    audited: { label: "✓ Audited", title: "Kernel-verified + independent cross-model audit passed" },
    provisional: { label: "◇ Provisional", title: "Kernel-verified; awaiting independent cross-model audit" },
    flagged: { label: "⚠ Flagged", title: "Cross-model audit flagged statement/title gap (excluded from objectives)" },
    refuted: { label: "✕ Refuted", title: "Judge-verified counterexample" },
    dead: { label: "☠ Barrier", title: "Ruled dead against known mathematical barrier" },
    contradiction: { label: "⛔ Contradiction", title: "Opposing verified proof & refutation detected" },
    in_work: { label: "● In Work", title: "Currently claimed by an active seat" },
    open: { label: "○ Open Bounty", title: "Available for token donation" },
  };

  function sealHTML(lemmaOrSeal) {
    if (lemmaOrSeal && typeof lemmaOrSeal === "object" && lemmaOrSeal.kind === "record") {
      const rs = lemmaOrSeal.record_state || {};
      const cfg = lemmaOrSeal.record || {};
      if (rs.contradiction) {
        return `<span class="seal seal-contradiction" title="${esc(SEAL_META.contradiction.title)}">⛔ Contradiction</span>`;
      }
      if (rs.closed && rs.best) {
        return `<span class="seal seal-frozen" title="Exact optimal proven and closed">◆ Optimal (${safeInt(rs.best.score)})</span>`;
      }
      if (rs.best) {
        return `<span class="seal seal-record" title="Current record held by ${esc(rs.best.seat || "donor")} — beat with ≤ ${safeInt(rs.next_target)}">♛ Record ${safeInt(rs.best.score)} · ≤${safeInt(rs.next_target)}</span>`;
      }
      return `<span class="seal seal-record" title="Open King-of-the-Hill hunt — launch ceiling ≤ ${safeInt(cfg.start_target)}">♛ Hunt · ≤${safeInt(cfg.start_target)}</span>`;
    }
    const key = typeof lemmaOrSeal === "string" ? lemmaOrSeal : sealOf(lemmaOrSeal);
    const m = SEAL_META[key] || SEAL_META.open;
    return `<span class="seal seal-${esc(key)}" title="${esc(m.title)}">${esc(m.label)}</span>`;
  }

  function prBadgesHTML(lemma) {
    const prs = lemma?.open_prs || [];
    if (!prs.length) return "";
    return prs
      .map(
        (p) =>
          `<a class="pr-pill" href="${esc(p.url)}" target="_blank" rel="noopener noreferrer" title="Active PR: ${esc(p.title)}" onclick="event.stopPropagation()">◷ PR #${safeInt(p.number)}</a>`
      )
      .join(" ");
  }

  function progMonogram(progId) {
    const p = STATE?.programs?.find((x) => x.id === progId);
    const code = (p?.key || progId || "GEN").slice(0, 3).toUpperCase();
    return `<span class="prog-tag" title="${esc(p?.title || progId)}">${esc(code)}</span>`;
  }

  function seatById(id) {
    return STATE?.seats?.find((s) => s.id === id);
  }

  function isClaimDonateable(lemma) {
    if (!lemma) return false;
    if (lemma.kind === "record") {
      return !lemma.record_state?.closed && !lemma.record_state?.contradiction;
    }
    return lemma.status === "conjecture" || lemma.status === "in_work";
  }

  function computeRecordTargetsUI(slug, lemma, kind, score) {
    const rec = lemma?.record || {};
    const tag = kind === "record_bound" ? `not_s${score}` : `s${score}`;
    const stem = rec.file_stem || lemma.id.replace(/-/g, "_");
    const claimsDir = rec.claims_dir || `missions/${slug}/lean/Claims`;
    const artifactFile = `${claimsDir}/${stem}_${tag}.lean`;
    const submissionFile = `missions/${slug}/submissions/${lemma.id}.${kind}.s${score}.json`;
    const tpl = rec.theorem_template || `${stem}_{tag}.record`;
    const theoremName = tpl.replace(/\{tag\}/g, tag);
    return { tag, artifactFile, submissionFile, theoremName };
  }

  // URL Sync
  function syncURL({ view = CURRENT_VIEW, mission = CURRENT_MISSION, claim = null, push = false } = {}) {
    const params = new URLSearchParams();
    if (mission) params.set("mission", mission);
    if (claim) params.set("claim", claim);
    const nextUrl = `${location.pathname}?${params.toString()}#${view}`;
    if (push) history.pushState({ view, mission, claim }, "", nextUrl);
    else history.replaceState({ view, mission, claim }, "", nextUrl);
  }

  // Dropdown Lab menu
  const labBtn = $("#lab-drop-btn");
  const labMenu = $("#lab-menu");
  function closeLabMenu() {
    labMenu.hidden = true;
    labBtn.setAttribute("aria-expanded", "false");
  }
  labBtn.addEventListener("click", (e) => {
    e.stopPropagation();
    const open = labMenu.hidden;
    labMenu.hidden = !open;
    labBtn.setAttribute("aria-expanded", open ? "true" : "false");
  });
  document.addEventListener("click", (e) => {
    if (!labMenu.hidden && !$("#lab-dropdown").contains(e.target)) closeLabMenu();
  });

  function setView(view, { push = false, preserveClaim = false } = {}) {
    if (!VALID_VIEWS.includes(view)) view = "missions";
    CURRENT_VIEW = view;
    closeLabMenu();
    $$(".view").forEach((el) => (el.hidden = el.id !== `view-${view}`));
    $$(".nav > a").forEach((a) => a.classList.toggle("active", a.dataset.nav === view));
    const isLab = LAB_VIEWS.includes(view);
    labBtn.classList.toggle("active", isLab);
    const labNames = {
      control: "Lab · Control",
      live: "Lab · Fleet",
      map: "Lab · Map",
      leaderboard: "Lab · Board",
      graveyard: "Lab · Graveyard",
      feed: "Lab · Audit",
    };
    $("#lab-drop-label").textContent = isLab ? labNames[view] : "Lab";
    $$("#lab-menu button").forEach((b) => b.classList.toggle("active", b.dataset.nav === view));
    const claimForUrl = preserveClaim ? (PENDING_CLAIM_ID || currentOpenClaimId()) : currentOpenClaimId();
    syncURL({ view, mission: CURRENT_MISSION, claim: claimForUrl, push });
    renderCurrentView();
  }

  function currentOpenClaimId() {
    return $("#lemma-drawer").classList.contains("open") ? $("#drawer-id").textContent || null : null;
  }

  // Delegate nav clicks everywhere
  document.addEventListener("click", (e) => {
    const navEl = e.target.closest("[data-nav]");
    if (!navEl) return;
    e.preventDefault();
    const v = navEl.dataset.nav;
    const m = navEl.dataset.mission;
    if (m && m !== CURRENT_MISSION) {
      switchMission(m, { targetView: v });
    } else {
      setView(v, { push: true });
      window.scrollTo({ top: 0, behavior: "smooth" });
    }
  });

  window.addEventListener("popstate", () => {
    const params = new URLSearchParams(location.search);
    const m = params.get("mission") || CURRENT_MISSION;
    const v = (location.hash || "").replace("#", "") || "missions";
    const c = params.get("claim");
    if (m !== CURRENT_MISSION) {
      switchMission(m, { targetView: v, openClaim: c, fromHistory: true });
    } else {
      PENDING_CLAIM_ID = c || null;
      setView(v, { push: false, preserveClaim: Boolean(c) });
      if (c) openDossier(c, { syncUrl: false });
      else if ($("#lemma-drawer").classList.contains("open")) closeDossier({ syncUrl: false });
    }
  });

  // Boot & mission loading (race-safe; zero 404 console noise on github.io!)
  async function boot() {
    $("#boot-error").hidden = true;
    const preferStatic = location.hostname.endsWith(".github.io") || location.protocol === "file:";
    const sources = preferStatic
      ? [
          { url: "./data/missions.json", isStatic: true },
          { url: "/api/missions", isStatic: false },
        ]
      : [
          { url: "/api/missions", isStatic: false },
          { url: "./data/missions.json", isStatic: true },
        ];

    let loaded = false;
    let lastErr = null;
    for (const src of sources) {
      try {
        const res = await fetch(src.url);
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        const data = await res.json();
        MISSIONS = data.missions || [];
        STATIC_MODE = src.isStatic || Boolean(data.static);
        loaded = true;
        break;
      } catch (err) {
        lastErr = err;
      }
    }
    if (!loaded) {
      $("#boot-error-msg").textContent = `Unable to load Proof Foundry catalog (${lastErr?.message || "network error"}).`;
      $("#boot-error").hidden = false;
      return;
    }

    if (!MISSIONS.some((m) => m.slug === CURRENT_MISSION) && MISSIONS.length) {
      CURRENT_MISSION = MISSIONS[0].slug;
    }
    populateMissionSelect();
    renderMissionsHub();

    const initialClaim = new URLSearchParams(location.search).get("claim");
    await switchMission(CURRENT_MISSION, { targetView: CURRENT_VIEW, openClaim: initialClaim, fromHistory: true });
  }

  $("#boot-retry-btn").addEventListener("click", boot);

  function populateMissionSelect() {
    const sel = $("#mission-select");
    sel.innerHTML = MISSIONS.map(
      (m) => `<option value="${esc(m.slug)}" ${m.slug === CURRENT_MISSION ? "selected" : ""}>${esc(m.title)}</option>`
    ).join("");
  }

  $("#mission-select").addEventListener("change", (e) => {
    const nextView = CURRENT_VIEW === "missions" ? "control" : CURRENT_VIEW;
    switchMission(e.target.value, { targetView: nextView });
  });

  async function switchMission(slug, { targetView = CURRENT_VIEW, openClaim = null, fromHistory = false } = {}) {
    const prevMission = CURRENT_MISSION;
    const seq = ++MISSION_REQ_SEQ;
    // Cancel any in-flight dossier fetch from the previous mission & close open drawer unless deep-linking into new mission
    DOSSIER_REQ_SEQ++;
    if (!openClaim && $("#lemma-drawer").classList.contains("open")) {
      closeDossier({ syncUrl: false });
    }
    if (SSE) {
      SSE.close();
      SSE = null;
    }

    try {
      const url = STATIC_MODE ? `./data/${encodeURIComponent(slug)}/state.json` : `/api/state?mission=${encodeURIComponent(slug)}`;
      const res = await fetch(url);
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const snap = await res.json();
      if (seq !== MISSION_REQ_SEQ) return; // Stale mission switch discarded!

      // Commit mission slug ONLY after fetch succeeds!
      CURRENT_MISSION = slug;
      if ($("#mission-select").value !== slug) $("#mission-select").value = slug;
      PENDING_CLAIM_ID = openClaim || null;

      applySnapshot(snap);
      $("#boot-error").hidden = true;
      if (!STATIC_MODE) connectSSE(slug, seq);
      setView(targetView, { push: !fromHistory, preserveClaim: Boolean(openClaim) });
      if (openClaim) openDossier(openClaim, { syncUrl: !fromHistory });
    } catch (err) {
      if (seq !== MISSION_REQ_SEQ) return;
      // Restore selector to still-active mission on failure!
      if ($("#mission-select").value !== prevMission) $("#mission-select").value = prevMission;
      $("#boot-error-msg").textContent = `Could not load mission "${slug}": ${err.message}`;
      $("#boot-error").hidden = false;
    }
  }

  function connectSSE(slug, seq) {
    try {
      SSE = new EventSource(`/api/stream?mission=${encodeURIComponent(slug)}`);
      SSE.addEventListener("snapshot", (ev) => {
        if (seq !== MISSION_REQ_SEQ) return;
        try {
          applySnapshot(JSON.parse(ev.data));
        } catch {}
      });
      SSE.onerror = () => {
        if (seq !== MISSION_REQ_SEQ) return;
        $("#sse-label").textContent = "Reconnecting…";
      };
    } catch {}
  }

  function applySnapshot(snap) {
    if (!snap || !snap.ready) return;
    STATE = snap;

    // Update topbar & sync pill
    const repo = snap.mission?.github_repo || "steph4n-gh/proof-foundry";
    $("#gh-repo-link").href = `https://github.com/${repo}`;
    $("#hub-proofs-link").href = STATIC_MODE ? "./PROOFS.md" : "/PROOFS.md";
    const openCount = snap.lemmas.filter((l) => isClaimDonateable(l) && l.status !== "in_work").length;
    $("#nav-bounty-count").textContent = String(openCount);

    const pillDot = $("#sse-pill .pulse-dot");
    if (STATIC_MODE) {
      pillDot.classList.add("static");
      $("#sse-label").textContent = relTime(snap.snapshot_at) || "synced";
    } else {
      pillDot.classList.remove("static");
      $("#sse-label").textContent = "Live";
    }
    $("#footer-judge").textContent = `Judge: ${snap.mission?.judge?.label || "Isolated Mechanical Judge"}`;

    // Just-in ribbon (explicit label for EVERY event type — never mislabel approach_dead as VERIFIED!)
    if (snap.just_in) {
      const e = snap.just_in;
      const tag = $("#just-in-tag");
      tag.className = "ribbon-tag";
      if (e.type === "claim_refuted") {
        tag.classList.add("refuted");
        tag.textContent = "REFUTED";
      } else if (e.type === "approach_dead") {
        tag.classList.add("dead");
        tag.textContent = "BARRIER / DEAD";
      } else if (e.type === "lemma_audited" && String(e.detail || "").startsWith("flagged")) {
        tag.classList.add("flagged");
        tag.textContent = "AUDIT FLAGGED";
      } else if (e.type === "lemma_audited") {
        tag.textContent = "AUDITED ✓";
      } else {
        tag.textContent = "VERIFIED ✓";
      }
      $("#just-in-text").textContent = `${e.lemma_id || ""} · ${e.title || e.detail || ""} (${relTime(e.at)})`;
      $("#just-in-open").onclick = () => e.lemma_id && openDossier(e.lemma_id, { triggerEl: $("#just-in-open") });
      $("#just-in").hidden = false;
    } else {
      $("#just-in").hidden = true;
    }

    // Populate program filter dropdown; reset to "all" if previous mission's program isn't in the new mission!
    const progSel = $("#board-program");
    const curProg = progSel.value || "all";
    const validProgIds = new Set((snap.programs || []).map((p) => p.id));
    progSel.innerHTML =
      `<option value="all">All programs</option>` +
      (snap.programs || []).map((p) => `<option value="${esc(p.id)}">${esc(p.title)}</option>`).join("");
    progSel.value = validProgIds.has(curProg) ? curProg : "all";

    renderCurrentView();
  }

  function renderCurrentView() {
    if (CURRENT_VIEW === "missions") {
      renderMissionsHub();
      return;
    }
    if (!STATE) return;
    if (CURRENT_VIEW === "control") renderControl();
    else if (CURRENT_VIEW === "bounties") renderBounties();
    else if (CURRENT_VIEW === "live") renderLive();
    else if (CURRENT_VIEW === "map") {
      renderProofMap();
      renderRelDAG();
    } else if (CURRENT_VIEW === "leaderboard") renderLeaderboard();
    else if (CURRENT_VIEW === "graveyard") renderGraveyard();
    else if (CURRENT_VIEW === "feed") renderAuditLog();
  }

  // =========================================================================
  // 0. ALL-MISSIONS HUB
  // =========================================================================
  function renderMissionsHub() {
    let totTrusted = 0, totChecked = 0, totObjDone = 0, totObj = 0, totOpen = 0, totFallen = 0;
    for (const m of MISSIONS) {
      totTrusted += safeInt(m.counts?.trusted);
      totChecked += safeInt(m.counts?.checked);
      totObjDone += safeInt(m.objectives?.conquered);
      totObj += safeInt(m.objectives?.total);
      totOpen += safeInt(m.counts?.conjecture);
      totFallen += safeInt(m.counts?.refuted) + safeInt(m.counts?.dead);
    }
    $("#gm-trusted").textContent = String(totTrusted);
    $("#gm-checked-sub").textContent = `${totChecked} kernel-checked across ${MISSIONS.length} missions`;
    $("#gm-objectives").textContent = `${totObjDone} / ${totObj}`;
    $("#gm-open").textContent = String(totOpen);
    $("#gm-fallen").textContent = String(totFallen);
    if (STATE?.pr_sync) {
      $("#hub-sync-chip").textContent = STATE.pr_sync.ok
        ? `GitHub PRs synced ${relTime(STATE.pr_sync.fetched_at)}`
        : "Offline snapshot";
    }

    $("#missions-hub-grid").innerHTML = MISSIONS.map((m) => {
      const isCur = m.slug === CURRENT_MISSION;
      return `
        <article class="mission-hub-card ${isCur ? "active-mission" : ""}">
          <div class="mhc-top">
            <div>
              <span class="mono small muted">${esc(m.slug)}</span>
              <h3 class="mhc-title">${esc(m.title)}</h3>
            </div>
            <span class="judge-chip">${esc(m.judge_type === "command" ? "Command Judge" : "Lean 4.36")}</span>
          </div>
          <p class="mhc-q">${esc(m.question)}</p>
          <div class="mhc-stats">
            <div class="mhc-stat"><strong class="tabular">${safeInt(m.objectives?.conquered)}/${safeInt(m.objectives?.total)}</strong><span>Objectives</span></div>
            <div class="mhc-stat"><strong class="tabular">${safeInt(m.counts?.trusted)}</strong><span>Trusted Proofs</span></div>
            <div class="mhc-stat"><strong class="tabular">${safeInt(m.counts?.conjecture)}</strong><span>Open Bounties</span></div>
          </div>
          <div class="mhc-actions">
            <button class="btn btn-primary btn-sm" type="button" data-nav="control" data-mission="${esc(m.slug)}">Mission Control &rarr;</button>
            <button class="btn btn-ghost btn-sm" type="button" data-nav="bounties" data-mission="${esc(m.slug)}">Bounties (${safeInt(m.counts?.conjecture)})</button>
          </div>
        </article>`;
    }).join("");
  }

  function pickTopOpenBounty() {
    if (!STATE) return null;
    const byId = Object.fromEntries(STATE.lemmas.map((l) => [l.id, l]));
    const open = STATE.lemmas
      .filter((l) => isClaimDonateable(l) && l.status !== "in_work")
      .sort((a, b) => {
        const aNoPr = a.kind === "record" || (a.open_prs?.length || 0) === 0 ? 1 : 0;
        const bNoPr = b.kind === "record" || (b.open_prs?.length || 0) === 0 ? 1 : 0;
        if (bNoPr !== aNoPr) return bNoPr - aNoPr;
        const aFroz = a.statement_file ? 1 : 0;
        const bFroz = b.statement_file ? 1 : 0;
        if (bFroz !== aFroz) return bFroz - aFroz;
        const aDepsOk = (a.deps || []).every((d) => !byId[d] || byId[d].status === "checked" || byId[d].status === "refuted" || byId[d].record_state?.best) ? 1 : 0;
        const bDepsOk = (b.deps || []).every((d) => !byId[d] || byId[d].status === "checked" || byId[d].status === "refuted" || byId[d].record_state?.best) ? 1 : 0;
        if (bDepsOk !== aDepsOk) return bDepsOk - aDepsOk;
        return (a.rung || 99) - (b.rung || 99);
      });
    return open[0] || null;
  }

  $("#hub-donate-cta").addEventListener("click", () => {
    const pick = pickTopOpenBounty();
    if (pick) openDonateModal(pick, $("#hub-donate-cta"));
    else setView("bounties", { push: true });
  });
  $("#control-donate-next").addEventListener("click", () => {
    const pick = pickTopOpenBounty();
    if (pick) openDonateModal(pick, $("#control-donate-next"));
    else setView("bounties", { push: true });
  });

  // =========================================================================
  // 1. MISSION CONTROL
  // =========================================================================
  function renderControl() {
    const m = STATE.mission;
    const c = STATE.counts;
    $("#control-mission-slug").textContent = m.slug;
    $("#control-pr-sync").textContent = STATE.pr_sync?.ok
      ? `GitHub PRs synced ${relTime(STATE.pr_sync.fetched_at)}`
      : "Local state (offline PR sync)";
    $("#hero-judge-chip").textContent = m.judge?.label || "Mechanical Judge";
    $("#hero-verdict-chip").textContent = STATE.meta?.verdict || "";
    $("#hero-question").textContent = m.question;
    $("#hero-description").textContent = m.description;

    const objs = m.objectives || [];
    const conquered = objs.filter((o) => o.conquered).length;
    const openPrCount = STATE.lemmas.reduce((acc, l) => acc + (l.open_prs?.length || 0), 0);

    $("#m-objectives").textContent = `${conquered} / ${objs.length}`;
    $("#m-objectives-sub").textContent = c.flagged > 0 ? `${c.flagged} flagged excluded` : "trusted non-flagged rungs";
    $("#m-checked").textContent = String(c.trusted ?? c.checked);
    $("#m-audited-sub").textContent = `${c.frozen_matched || 0} frozen · ${c.audited_faithful || 0} audited · ${c.checked} total`;
    $("#m-open").textContent = String(c.conjecture || 0);
    $("#m-active-sub").textContent = !STATE.pr_sync?.ok
      ? "PR sync offline"
      : openPrCount > 0
      ? `${openPrCount} active GitHub PR${openPrCount > 1 ? "s" : ""}`
      : "0 open PRs · ready";
    $("#m-fallen").textContent = String((c.refuted || 0) + (c.dead || 0));
    $("#m-fallen-sub").textContent = `${c.refuted || 0} refuted · ${c.dead || 0} barriers`;

    // Tug of war
    if (m.tug_of_war?.enabled) {
      const l = c.aims_left_checked || 0;
      const r = c.aims_right_checked || 0;
      const tot = Math.max(1, l + r);
      $("#tug-left-text").textContent = `${m.tug_of_war.left_label}: ${l}`;
      $("#tug-right-text").textContent = `${m.tug_of_war.right_label}: ${r}`;
      $("#tug-l").style.width = `${(l / tot) * 100}%`;
      $("#tug-r").style.width = `${(r / tot) * 100}%`;
      $("#tug-inline").hidden = false;
    } else {
      $("#tug-inline").hidden = true;
    }

    // Objectives
    $("#objectives-grid").innerHTML = objs.length
      ? objs
          .map((o) => {
            const rungs = (o.items || [])
              .map((it) => {
                const expTag =
                  it.expect === "refutation"
                    ? `<span class="prog-tag" title="Refutation required">REFUTE</span>`
                    : it.expect && typeof it.expect === "object" && it.expect.record_at_most != null
                    ? `<span class="prog-tag" title="Milestone target score">GOAL ≤${safeInt(it.expect.record_at_most)}</span>`
                    : "";
                const prTag = (it.open_prs || []).length
                  ? `<span class="pr-pill">◷ PR #${safeInt(it.open_prs[0].number)}</span>`
                  : "";
                return `
                  <button class="rung-btn" type="button" data-open-claim="${esc(it.id)}">
                    <span class="rung-main">
                      <span class="rung-id">${esc(it.id)}</span>
                      <span class="rung-title">${esc(it.title)}</span>
                    </span>
                    <span class="rung-meta">
                      ${expTag}${prTag}${sealHTML(it)}
                    </span>
                  </button>`;
              })
              .join("");
            return `
              <article class="obj-card ${o.conquered ? "conquered" : ""}">
                <div class="obj-top">
                  <div>
                    <div class="obj-tier">${esc(o.tier || "Objective")}${o.conquered ? " · CONQUERED ✓" : ""}</div>
                    <h3 class="obj-title">${esc(o.title)}</h3>
                  </div>
                  <span class="obj-ratio tabular">${safeInt(o.completed)} / ${safeInt(o.total)}</span>
                </div>
                <div class="obj-bar"><div class="obj-bar-fill" style="width:${safeInt(o.pct)}%"></div></div>
                <p class="obj-desc">${esc(o.finish_line || "")}</p>
                <div class="obj-rungs">${rungs}</div>
              </article>`;
          })
          .join("")
      : `<div class="empty-state">No objectives configured for this mission yet.</div>`;

    // Top Open Bounties (prioritize active King-of-the-Hill hunts & frozen targets)
    const openBounties = STATE.lemmas
      .filter((l) => isClaimDonateable(l) && l.status !== "in_work")
      .sort(
        (a, b) =>
          (b.kind === "record" ? 1 : 0) - (a.kind === "record" ? 1 : 0) ||
          (b.statement_file ? 1 : 0) - (a.statement_file ? 1 : 0) ||
          (a.rung || 99) - (b.rung || 99)
      )
      .slice(0, 6);
    $("#control-bounties").innerHTML = openBounties.length
      ? openBounties.map(renderBountyCard).join("")
      : `<div class="empty-state">All registered bounties in this mission are complete! Switch missions or propose a new claim.</div>`;

    // Strategy Desk
    const note = STATE.meta?.strategy_note;
    if (note) {
      $("#strategy-meta").textContent = `${note.seat || "Strategy"} · ${relTime(note.at)}`;
      $("#strategy-text").textContent = note.text || "";
      $("#mentioned-list").innerHTML = (note.mentions || [])
        .map((id) => `<button class="chip-btn" type="button" data-open-claim="${esc(id)}">${esc(id)}</button>`)
        .join("");
    } else {
      $("#strategy-meta").textContent = "";
      $("#strategy-text").textContent = "No strategy dispatch published yet.";
      $("#mentioned-list").innerHTML = "";
    }

    // Live Whispers
    const whispers = (STATE.whispers || []).slice(0, 8);
    $("#whispers-count").textContent = `${whispers.length} recent`;
    $("#whispers-list").innerHTML = whispers.length
      ? whispers
          .map(
            (w) => `
            <li class="whisper-item">
              <div><strong class="mono small">${esc(w.seat)}</strong> <span class="muted">${esc(w.text)}</span></div>
              <span class="mono small muted">${relTime(w.at)}</span>
            </li>`
          )
          .join("")
      : `<li class="empty-state">No whispers yet.</li>`;

    // Recent Events
    $("#overview-events").innerHTML = (STATE.events || []).slice(0, 8).map(renderEventItem).join("") || `<li class="empty-state">No events logged yet.</li>`;
  }

  function renderBountyCard(l) {
    const isRec = l.kind === "record";
    const rs = l.record_state || {};
    const cfg = l.record || {};
    const frozenChip = isRec
      ? `<span class="seal seal-frozen" title="Auto-ratcheting King-of-the-Hill frozen statement">♛ King of the Hill</span>`
      : l.statement_file
      ? `<span class="seal seal-frozen" title="Frozen formal statement: ${esc(l.statement_file)}">◆ Frozen Target</span>`
      : "";
    const deps = (l.deps || []).length
      ? `<span class="mono small muted">deps: ${(l.deps || []).map(esc).join(", ")}</span>`
      : `<span class="mono small muted">standalone</span>`;
    let donateLabel = "Donate Tokens";
    if (isRec) {
      const nextT = rs.next_target ?? cfg.start_target;
      donateLabel = rs.best ? `Beat Record (≤ ${safeInt(nextT)})` : `Start Hunt (≤ ${safeInt(nextT)})`;
    }
    const donateBtn = isClaimDonateable(l)
      ? `<button class="btn btn-primary btn-sm" type="button" data-donate-claim="${esc(l.id)}">${esc(donateLabel)}</button>`
      : "";
    const recBanner = isRec
      ? `<div class="rec-banner">
           <span>${rs.best ? `Best: <strong>${safeInt(rs.best.score)}</strong> ${esc(cfg.unit || "")} (${esc(rs.best.seat)})` : `Unclaimed · Ceiling ≤ <strong>${safeInt(cfg.start_target)}</strong> ${esc(cfg.unit || "")}`}</span>
           <span>${rs.closed ? `Exact Optimal ✓` : `Target: <strong>≤ ${safeInt(rs.next_target ?? cfg.start_target)}</strong>`}</span>
           <span>${rs.refuted ? `Proven LB: <strong>≥ ${safeInt(rs.refuted.inclusive_bound)}</strong>` : cfg.literature_lower_bound ? `Lit. LB: ${safeInt(cfg.literature_lower_bound)}` : ""}</span>
         </div>`
      : "";
    return `
      <article class="bounty-card">
        <div class="bounty-top">
          <div class="bounty-id-group">
            <strong class="mono">${esc(l.id)}</strong>
            ${progMonogram(l.program)}
            ${frozenChip}
          </div>
          <div class="bounty-id-group">
            ${prBadgesHTML(l)}
            ${sealHTML(l)}
          </div>
        </div>
        <p class="bounty-title">${esc(l.title)}</p>
        ${recBanner}
        <pre class="bounty-stmt">${esc(l.registered_statement || l.statement || l.theorem_name)}</pre>
        <div class="bounty-foot">
          ${deps}
          <div class="bounty-actions">
            <button class="btn btn-ghost btn-sm" type="button" data-open-claim="${esc(l.id)}">Dossier</button>
            ${donateBtn}
          </div>
        </div>
      </article>`;
  }

  // =========================================================================
  // 2. BOUNTIES & CLAIM LEDGER
  // =========================================================================
  $$("[data-bmode]").forEach((btn) => {
    btn.addEventListener("click", () => {
      BOUNTY_MODE = btn.dataset.bmode;
      $$("[data-bmode]").forEach((b) => {
        const active = b.dataset.bmode === BOUNTY_MODE;
        b.classList.toggle("active", active);
        b.setAttribute("aria-selected", active ? "true" : "false");
      });
      renderBounties();
    });
  });
  ["#board-search", "#board-program", "#board-status"].forEach((id) => {
    $(id).addEventListener("input", renderBounties);
    $(id).addEventListener("change", renderBounties);
  });

  function renderBounties() {
    const q = ($("#board-search").value || "").trim().toLowerCase();
    const prog = $("#board-program").value;
    const sealFilter = $("#board-status").value;

    const filtered = (STATE.lemmas || []).filter((l) => {
      const s = sealOf(l);
      if (BOUNTY_MODE === "open" && !isClaimDonateable(l)) return false;
      if (prog !== "all" && l.program !== prog) return false;
      if (sealFilter === "record") {
        if (s !== "record" && !(l.kind === "record" && !l.record_state?.closed && !l.record_state?.contradiction)) return false;
      } else if (sealFilter !== "all" && s !== sealFilter) {
        return false;
      }
      if (q) {
        const hay = `${l.id} ${l.title} ${l.statement} ${l.theorem_name} ${l.paper_notes || ""}`.toLowerCase();
        if (!hay.includes(q)) return false;
      }
      return true;
    });

    if (BOUNTY_MODE === "open") {
      $("#bounties-open-grid").hidden = false;
      $("#bounties-table-wrap").hidden = true;
      const sorted = [...filtered].sort(
        (a, b) =>
          (b.kind === "record" ? 1 : 0) - (a.kind === "record" ? 1 : 0) ||
          (b.statement_file ? 1 : 0) - (a.statement_file ? 1 : 0) ||
          (a.rung || 99) - (b.rung || 99)
      );
      $("#bounties-open-grid").innerHTML = sorted.length
        ? sorted.map(renderBountyCard).join("")
        : `<div class="empty-state">No open bounties match your filter. Switch to <strong>Full Claim Table</strong> to view all completed &amp; audited proofs.</div>`;
    } else {
      $("#bounties-open-grid").hidden = true;
      $("#bounties-table-wrap").hidden = false;
      $("#board-tbody").innerHTML = filtered.length
        ? filtered
            .map((l) => {
              const actor =
                l.kind === "record"
                  ? l.record_state?.best?.seat || "—"
                  : l.checker?.by_seat || l.refutation?.by_seat || l.epitaph?.by_seat || l.claimed_by || "—";
              const dur =
                l.kind === "record"
                  ? l.record_state?.best?.duration_ms
                  : l.checker?.duration_ms || l.refutation?.duration_ms;
              return `
                <tr data-open-claim="${esc(l.id)}">
                  <td class="mono"><button class="table-id-btn" type="button" data-open-claim="${esc(l.id)}">${esc(l.id)}</button></td>
                  <td>${sealHTML(l)} ${prBadgesHTML(l)}</td>
                  <td>${progMonogram(l.program)}</td>
                  <td><div>${esc(l.title)}</div><div class="mono small muted">${esc((l.statement || "").slice(0, 110))}</div></td>
                  <td class="mono small">${esc(actor)}</td>
                  <td class="mono small tabular">${dur ? `${safeInt(dur)}ms` : "—"}</td>
                </tr>`;
            })
            .join("")
        : `<tr><td colspan="6" class="empty-state">No claims match your filter.</td></tr>`;
    }
  }

  // =========================================================================
  // 3. LIVE FLEET
  // =========================================================================
  function renderLive() {
    const seats = STATE.seats || [];
    const runs = STATE.checker_runs || [];
    const passed = runs.filter((r) => r.ok).length;
    $("#live-header-stats").textContent = `${seats.length} seats · ${runs.length} recent Judge runs`;
    $("#checker-pass-rate").textContent = `${passed}/${runs.length} passed`;
    $("#live-msg-count").textContent = `${(STATE.messages || []).length} dispatches`;

    // SVG communication ring
    const w = 520, h = 290, cx = 260, cy = 145, R = 102;
    const coords = {};
    seats.forEach((s, i) => {
      const ang = (Math.PI * 2 * i) / Math.max(1, seats.length) - Math.PI / 2;
      coords[s.id] = { x: cx + R * Math.cos(ang), y: cy + R * Math.sin(ang) };
    });
    const edges = (STATE.messages || []).slice(0, 12).map((m) => {
      const a = coords[m.from];
      const b = coords[m.to];
      if (!a || !b) return "";
      const isChallenge = m.kind === "challenge" || m.kind === "refute";
      return `<line x1="${a.x.toFixed(1)}" y1="${a.y.toFixed(1)}" x2="${b.x.toFixed(1)}" y2="${b.y.toFixed(1)}" stroke="${isChallenge ? "var(--coral)" : "var(--emerald)"}" stroke-width="1.6" stroke-dasharray="${isChallenge ? "4 3" : "none"}" opacity="0.7"/>`;
    });
    const nodes = seats.map((s) => {
      const p = coords[s.id];
      const active = s.status === "working" || s.status === "checking";
      return `
        <g transform="translate(${p.x.toFixed(1)},${p.y.toFixed(1)})">
          <circle r="19" fill="var(--bg)" stroke="${active ? "var(--sky)" : "var(--border-strong)"}" stroke-width="${active ? 2.2 : 1.3}"/>
          <text text-anchor="middle" dy="4" fill="var(--ink)" font-size="11" font-family="var(--font-mono)" font-weight="600">${esc(s.badge || s.id.slice(0, 2).toUpperCase())}</text>
          <text text-anchor="middle" dy="33" fill="var(--muted)" font-size="10" font-family="var(--font-mono)">${esc(s.name.slice(0, 16))}</text>
        </g>`;
    });
    $("#live-seat-graph").innerHTML = `
      <svg viewBox="0 0 ${w} ${h}" width="${w}" height="${h}" role="img" aria-label="Seat communication ring">
        <circle cx="${cx}" cy="${cy}" r="${R}" fill="none" stroke="var(--border)" stroke-dasharray="3 5"/>
        <circle cx="${cx}" cy="${cy}" r="28" fill="var(--sky-dim)" stroke="var(--sky)" stroke-width="1.4"/>
        <text x="${cx}" y="${cy + 4}" text-anchor="middle" fill="var(--sky)" font-size="10.5" font-family="var(--font-mono)" font-weight="700">JUDGE</text>
        ${edges.join("")}${nodes.join("")}
      </svg>`;

    $("#live-seat-cards").innerHTML = seats
      .map(
        (s) => `
        <div class="seat-card">
          <div class="seat-head">
            <strong class="small">${esc(s.name)}</strong>
            <span class="seat-badge">${esc(s.badge || "TD")}</span>
          </div>
          <div class="mono small muted">${esc(s.model || s.provider || "")}</div>
          <div class="small muted">${esc(s.current_whisper || s.status)}</div>
          <div class="mono small tabular">✓ ${safeInt(s.counts?.checked)} · ✕ ${safeInt(s.counts?.refuted)} · ☠ ${safeInt(s.counts?.blocked)}</div>
        </div>`
      )
      .join("");

    $("#live-checker-runs").innerHTML = runs.length
      ? runs
          .slice(0, 14)
          .map(
            (r) => `
            <li class="ticker-item" data-open-claim="${esc(r.lemma_id)}" style="cursor:pointer">
              <div>
                <strong class="mono">${esc(r.lemma_id)}</strong>
                <span class="seal ${r.ok ? "seal-audited" : "seal-refuted"}">${r.ok ? "OK" : "FAIL"}</span>
                <div class="small muted">${esc(r.seat)} · ${safeInt(r.duration_ms)}ms</div>
              </div>
              <span class="mono small muted">${relTime(r.at)}</span>
            </li>`
          )
          .join("")
      : `<li class="empty-state">No local Judge runs recorded in this snapshot.</li>`;

    $("#live-messages").innerHTML = (STATE.messages || []).length
      ? STATE.messages
          .slice(0, 14)
          .map(
            (m) => `
            <li class="ticker-item">
              <div>
                <strong class="mono small">${esc(m.from)} &rarr; ${esc(m.to)}</strong>
                <div class="small muted">${esc(m.text)}</div>
              </div>
              <span class="mono small muted">${relTime(m.at)}</span>
            </li>`
          )
          .join("")
      : `<li class="empty-state">No inter-seat dispatches yet.</li>`;
  }

  // =========================================================================
  // 4. CONSTELLATION MAP & REL DAG
  // =========================================================================
  let MAP_NODES = [];
  let MAP_CAM = { x: 0, y: 0, z: 1 };
  let MAP_DRAG = null;
  let MAP_BOUND = false;

  function sealColor(seal) {
    const dark = document.documentElement.getAttribute("data-theme") !== "light";
    if (seal === "frozen") return dark ? "#22d3ee" : "#0891b2";
    if (seal === "record") return dark ? "#c084fc" : "#7e22ce";
    if (seal === "audited") return dark ? "#10b981" : "#059669";
    if (seal === "provisional") return dark ? "#94a3b8" : "#64748b";
    if (seal === "flagged" || seal === "in_work") return dark ? "#f59e0b" : "#d97706";
    if (seal === "refuted" || seal === "contradiction") return dark ? "#f43f5e" : "#e11d48";
    if (seal === "dead") return dark ? "#64748b" : "#94a3b8";
    return dark ? "#38bdf8" : "#0284c7";
  }

  function renderProofMap() {
    const progs = STATE.programs || [];
    const lemmas = STATE.lemmas || [];
    MAP_NODES = [];
    const ringR = progs.length <= 1 ? 0 : 180;
    progs.forEach((p, pi) => {
      const ang = (Math.PI * 2 * pi) / Math.max(1, progs.length) - Math.PI / 2;
      const cx = Math.cos(ang) * ringR;
      const cy = Math.sin(ang) * ringR;
      const group = lemmas.filter((l) => l.program === p.id);
      group.forEach((l, li) => {
        const a2 = (Math.PI * 2 * li) / Math.max(1, group.length);
        const r2 = group.length <= 1 ? 0 : 52 + (li % 2) * 28;
        MAP_NODES.push({ lemma: l, prog: p, x: cx + Math.cos(a2) * r2, y: cy + Math.sin(a2) * r2, r: l.status === "checked" ? 11 : 9 });
      });
    });
    if (!MAP_BOUND) bindMapEvents();
    drawProofMap();
  }

  function drawProofMap() {
    const canvas = $("#proof-map-canvas");
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    if (!rect.width || !rect.height) return;
    const dpr = window.devicePixelRatio || 1;
    canvas.width = rect.width * dpr;
    canvas.height = rect.height * dpr;
    const ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, rect.width, rect.height);

    ctx.save();
    ctx.translate(rect.width / 2 + MAP_CAM.x, rect.height / 2 + MAP_CAM.y);
    ctx.scale(MAP_CAM.z, MAP_CAM.z);

    const byId = Object.fromEntries(MAP_NODES.map((n) => [n.lemma.id, n]));
    // Dependency edges
    ctx.strokeStyle = document.documentElement.getAttribute("data-theme") === "light" ? "rgba(15,23,42,0.16)" : "rgba(182,197,224,0.2)";
    ctx.lineWidth = 1.2;
    for (const n of MAP_NODES) {
      for (const depId of n.lemma.deps || []) {
        const d = byId[depId];
        if (!d) continue;
        ctx.beginPath();
        ctx.moveTo(d.x, d.y);
        ctx.lineTo(n.x, n.y);
        ctx.stroke();
      }
    }

    // Nodes
    const ink = document.documentElement.getAttribute("data-theme") === "light" ? "#0f172a" : "#ecf2ff";
    for (const n of MAP_NODES) {
      const col = sealColor(sealOf(n.lemma));
      ctx.beginPath();
      ctx.arc(n.x, n.y, n.r, 0, Math.PI * 2);
      ctx.fillStyle = col;
      ctx.fill();
      ctx.strokeStyle = ink;
      ctx.lineWidth = n.lemma.statement_file ? 2 : 0.8;
      ctx.stroke();

      ctx.fillStyle = ink;
      ctx.font = "600 10.5px JetBrains Mono, monospace";
      ctx.textAlign = "center";
      ctx.fillText(n.lemma.id, n.x, n.y + n.r + 13);
    }
    ctx.restore();
  }

  function screenToWorld(canvas, sx, sy) {
    const rect = canvas.getBoundingClientRect();
    return {
      x: (sx - rect.width / 2 - MAP_CAM.x) / MAP_CAM.z,
      y: (sy - rect.height / 2 - MAP_CAM.y) / MAP_CAM.z,
    };
  }

  function hitTestNode(canvas, sx, sy) {
    const w = screenToWorld(canvas, sx, sy);
    return MAP_NODES.find((n) => Math.hypot(n.x - w.x, n.y - w.y) <= n.r + 6) || null;
  }

  function bindMapEvents() {
    MAP_BOUND = true;
    const canvas = $("#proof-map-canvas");
    const tip = $("#map-hover-card");
    canvas.addEventListener("mousedown", (e) => {
      MAP_DRAG = { sx: e.clientX, sy: e.clientY, cx: MAP_CAM.x, cy: MAP_CAM.y, moved: false };
    });
    window.addEventListener("mousemove", (e) => {
      if (MAP_DRAG) {
        const dx = e.clientX - MAP_DRAG.sx;
        const dy = e.clientY - MAP_DRAG.sy;
        if (Math.hypot(dx, dy) > 3) MAP_DRAG.moved = true;
        MAP_CAM.x = MAP_DRAG.cx + dx;
        MAP_CAM.y = MAP_DRAG.cy + dy;
        drawProofMap();
        return;
      }
      if (CURRENT_VIEW !== "map") return;
      const rect = canvas.getBoundingClientRect();
      const hit = hitTestNode(canvas, e.clientX - rect.left, e.clientY - rect.top);
      if (hit) {
        tip.innerHTML = `<strong>${esc(hit.lemma.id)}</strong> ${sealHTML(hit.lemma)}<div class="small muted" style="margin-top:4px">${esc(hit.lemma.title)}</div>`;
        tip.style.left = `${Math.min(rect.width - 260, Math.max(10, e.clientX - rect.left + 14))}px`;
        tip.style.top = `${Math.min(rect.height - 90, Math.max(10, e.clientY - rect.top + 14))}px`;
        tip.hidden = false;
      } else {
        tip.hidden = true;
      }
    });
    window.addEventListener("mouseup", (e) => {
      if (!MAP_DRAG) return;
      const wasMoved = MAP_DRAG.moved;
      MAP_DRAG = null;
      if (!wasMoved && CURRENT_VIEW === "map") {
        const rect = canvas.getBoundingClientRect();
        const hit = hitTestNode(canvas, e.clientX - rect.left, e.clientY - rect.top);
        if (hit) openDossier(hit.lemma.id);
      }
    });
    canvas.addEventListener(
      "wheel",
      (e) => {
        e.preventDefault();
        const f = e.deltaY < 0 ? 1.12 : 0.89;
        MAP_CAM.z = Math.max(0.4, Math.min(2.6, MAP_CAM.z * f));
        drawProofMap();
      },
      { passive: false }
    );
    $("#map-zoom-in").addEventListener("click", () => {
      MAP_CAM.z = Math.min(2.6, MAP_CAM.z * 1.2);
      drawProofMap();
    });
    $("#map-zoom-out").addEventListener("click", () => {
      MAP_CAM.z = Math.max(0.4, MAP_CAM.z * 0.82);
      drawProofMap();
    });
    $("#map-reset").addEventListener("click", () => {
      MAP_CAM = { x: 0, y: 0, z: 1 };
      drawProofMap();
    });
    window.addEventListener("resize", () => CURRENT_VIEW === "map" && drawProofMap());

    // Map search jump
    const inp = $("#map-search");
    const pop = $("#map-search-results");
    inp.addEventListener("input", () => {
      const q = inp.value.trim().toLowerCase();
      if (!q) {
        pop.hidden = true;
        return;
      }
      const matches = MAP_NODES.filter((n) => `${n.lemma.id} ${n.lemma.title}`.toLowerCase().includes(q)).slice(0, 8);
      pop.innerHTML = matches.length
        ? matches.map((n) => `<button type="button" data-jump-id="${esc(n.lemma.id)}"><strong class="mono">${esc(n.lemma.id)}</strong><span class="muted">${esc(n.lemma.title.slice(0, 40))}</span></button>`).join("")
        : `<div class="small muted" style="padding:8px 10px">No matches</div>`;
      pop.hidden = false;
    });
    pop.addEventListener("click", (e) => {
      const btn = e.target.closest("[data-jump-id]");
      if (!btn) return;
      const node = MAP_NODES.find((n) => n.lemma.id === btn.dataset.jumpId);
      if (node) {
        MAP_CAM = { x: -node.x * 1.25, y: -node.y * 1.25, z: 1.25 };
        drawProofMap();
        openDossier(node.lemma.id);
      }
      pop.hidden = true;
    });
  }

  function renderRelDAG() {
    const lemmas = STATE.lemmas || [];
    const byId = Object.fromEntries(lemmas.map((l) => [l.id, l]));
    const depthOf = (id, seen = new Set()) => {
      if (seen.has(id)) return 0;
      seen.add(id);
      const l = byId[id];
      if (!l || !(l.deps || []).length) return 0;
      return 1 + Math.max(...l.deps.map((d) => depthOf(d, seen)));
    };
    const cols = {};
    lemmas.forEach((l) => {
      const d = depthOf(l.id);
      (cols[d] = cols[d] || []).push(l);
    });
    const colKeys = Object.keys(cols).map(Number).sort((a, b) => a - b);
    const colW = 210, rowH = 54, padX = 20, padY = 24;
    const maxRows = Math.max(1, ...colKeys.map((k) => cols[k].length));
    const width = Math.max(600, colKeys.length * colW + padX * 2);
    const height = maxRows * rowH + padY * 2;
    const pos = {};
    colKeys.forEach((ck, ci) => {
      cols[ck].forEach((l, ri) => {
        pos[l.id] = { x: padX + ci * colW, y: padY + ri * rowH };
      });
    });

    const lines = [];
    for (const l of lemmas) {
      const to = pos[l.id];
      for (const depId of l.deps || []) {
        const from = pos[depId];
        if (!from || !to) continue;
        lines.push(`<path d="M ${from.x + 156} ${from.y + 18} C ${from.x + 184} ${from.y + 18}, ${to.x - 28} ${to.y + 18}, ${to.x} ${to.y + 18}" fill="none" stroke="var(--border-strong)" stroke-width="1.3"/>`);
      }
    }
    const boxes = lemmas.map((l) => {
      const p = pos[l.id];
      const col = sealColor(sealOf(l));
      return `
        <g transform="translate(${p.x},${p.y})" style="cursor:pointer" data-open-claim="${esc(l.id)}">
          <rect width="156" height="36" rx="7" fill="var(--bg)" stroke="${col}" stroke-width="1.4"/>
          <text x="10" y="15" fill="var(--ink)" font-size="11" font-family="var(--font-mono)" font-weight="600">${esc(l.id)}</text>
          <text x="10" y="29" fill="var(--muted)" font-size="9.5" font-family="var(--font-body)">${esc((l.title || "").slice(0, 22))}</text>
        </g>`;
    });
    $("#rel-graph-wrap").innerHTML = `<svg viewBox="0 0 ${width} ${height}" width="${width}" height="${height}">${lines.join("")}${boxes.join("")}</svg>`;
  }

  // =========================================================================
  // 5. LEADERBOARD
  // =========================================================================
  function renderLeaderboard() {
    // Credit ONLY trusted non-flagged proofs + King-of-the-Hill delta record points + verified refutations + barrier rulings
    const seatStats = new Map();
    const ensure = (id) => {
      if (!seatStats.has(id)) {
        const s = seatById(id);
        seatStats.set(id, { id, name: s?.name || id, model: s?.model || "Community Donor", trusted: 0, recordPts: 0, recordWins: 0, refuted: 0, dead: 0 });
      }
      return seatStats.get(id);
    };
    for (const s of STATE.seats || []) ensure(s.id);
    for (const l of STATE.lemmas || []) {
      if (l.kind === "record") {
        const rs = l.record_state;
        if (rs && !rs.contradiction) {
          for (const [seatId, pts] of Object.entries(rs.points_by_seat || {})) {
            ensure(seatId).recordPts += safeInt(pts);
          }
          for (const h of rs.history || []) {
            if (h.state === "accepted" && h.seat) ensure(h.seat).recordWins++;
          }
        }
        continue;
      }
      const seal = sealOf(l);
      if ((seal === "audited" || seal === "frozen") && l.checker?.by_seat) ensure(l.checker.by_seat).trusted++;
      if (seal === "refuted" && l.refutation?.by_seat) ensure(l.refutation.by_seat).refuted++;
      if (seal === "dead" && l.epitaph?.by_seat) ensure(l.epitaph.by_seat).dead++;
    }
    const rows = [...seatStats.values()]
      .map((r) => ({ ...r, score: r.trusted * 10 + r.recordPts * 5 + r.refuted * 10 + r.dead * 4 }))
      .sort((a, b) => b.score - a.score || b.trusted - a.trusted || b.recordPts - a.recordPts);

    // Group by model family
    const byModel = new Map();
    for (const r of rows) {
      const cur = byModel.get(r.model) || 0;
      byModel.set(r.model, cur + r.trusted + r.refuted + r.recordWins);
    }
    const mList = [...byModel.entries()].filter(([, n]) => n > 0).sort((a, b) => b[1] - a[1]);
    const maxM = Math.max(1, ...mList.map(([, n]) => n));
    $("#leaderboard-models").innerHTML = mList.length
      ? mList
          .map(
            ([model, n]) => `
            <div class="mbar-row">
              <div class="mbar-top"><strong>${esc(model)}</strong><span class="mono tabular">${n} verified</span></div>
              <div class="mbar-track"><div class="mbar-fill" style="width:${Math.round((n / maxM) * 100)}%"></div></div>
            </div>`
          )
          .join("")
      : `<div class="empty-state">No trusted proofs or refutations yet.</div>`;

    const slug = STATE.mission?.slug || CURRENT_MISSION;
    $("#leaderboard-howto").textContent = [
      `git clone https://github.com/${STATE.mission?.github_repo || "steph4n-gh/proof-foundry"}.git`,
      `node hub/fleet.mjs next --mission ${slug}`,
      `node hub/fleet.mjs verify --mission ${slug} --lemma <ID> --seat donor-<handle> --file <path> --theorem <name> --export`,
      `# Or for King of the Hill records:`,
      `node hub/fleet.mjs record --mission ${slug} --lemma <ID> --score <N> --seat donor-<handle> --export`,
      `# Commit ONLY your artifact + missions/${slug}/submissions/<ID>.*.json and open a PR!`,
    ].join("\n");

    $("#leaderboard-tbody").innerHTML = rows
      .map(
        (r, idx) => `
        <tr>
          <td class="mono tabular">#${idx + 1}</td>
          <td><strong>${esc(r.name)}</strong><div class="mono small muted">${esc(r.id)}</div></td>
          <td>${esc(r.model)}</td>
          <td class="mono tabular">${r.trusted}</td>
          <td class="mono tabular">${r.recordPts}</td>
          <td class="mono tabular">${r.refuted}</td>
          <td class="mono tabular">${r.dead}</td>
          <td class="mono tabular"><strong>${r.score}</strong></td>
        </tr>`
      )
      .join("");
  }

  // =========================================================================
  // 6. GRAVEYARD & 7. AUDIT LOG
  // =========================================================================
  function renderGraveyard() {
    const fallen = (STATE.lemmas || []).filter((l) => {
      const s = sealOf(l);
      return s === "refuted" || s === "dead" || s === "flagged" || s === "contradiction";
    });
    $("#graveyard-grid").innerHTML = fallen.length
      ? fallen
          .map((l) => {
            const s = sealOf(l);
            const reason =
              s === "refuted"
                ? l.refutation?.summary
                : s === "flagged"
                ? l.audit?.notes
                : l.epitaph?.reason || "Ruled dead.";
            return `
              <article class="grave-card is-${esc(s)}">
                <div class="bounty-top">
                  <strong class="mono">${esc(l.id)}</strong>
                  ${sealHTML(l)}
                </div>
                <p class="bounty-title">${esc(l.title)}</p>
                <p class="small muted" style="margin:0">${esc(reason || "")}</p>
                <div style="margin-top:auto">
                  <button class="btn btn-ghost btn-sm" type="button" data-open-claim="${esc(l.id)}">Inspect Counterexample / Audit &rarr;</button>
                </div>
              </article>`;
          })
          .join("")
      : `<div class="empty-state">No refuted conjectures, flagged claims, or barriers recorded in this mission yet.</div>`;
  }

  function renderEventItem(e) {
    return `
      <li class="event-item" ${e.lemma_id ? `data-open-claim="${esc(e.lemma_id)}"` : ""}>
        <div class="event-main">
          <div class="event-top">
            <span class="prog-tag">${esc(e.type)}</span>
            ${e.lemma_id ? `<strong class="mono">${esc(e.lemma_id)}</strong>` : ""}
            <span class="mono small muted">${esc(e.seat || "")}</span>
          </div>
          <div class="small muted">${esc(e.title || e.detail || "")}</div>
        </div>
        <span class="mono small muted">${relTime(e.at)}</span>
      </li>`;
  }

  $("#feed-filter").addEventListener("change", renderAuditLog);
  function renderAuditLog() {
    const f = $("#feed-filter").value;
    const evs = (STATE.events || []).filter((e) => f === "all" || e.type === f);
    $("#full-feed-list").innerHTML = evs.length ? evs.map(renderEventItem).join("") : `<li class="empty-state">No matching audit events.</li>`;
  }

  function pushFocus(triggerEl) {
    const el = triggerEl || (document.activeElement && document.activeElement !== document.body ? document.activeElement : null);
    FOCUS_STACK.push(el);
  }
  function popFocus() {
    const el = FOCUS_STACK.pop();
    if (el && document.contains(el) && typeof el.focus === "function") el.focus();
  }

  // =========================================================================
  // VERIFICATION RECEIPT DOSSIER (Race-safe + Inert A11y + Focus Stack + Retry)
  // =========================================================================
  async function openDossier(id, { syncUrl = true, triggerEl = null } = {}) {
    if (!id) return;
    const drawer = $("#lemma-drawer");
    if (!drawer.classList.contains("open")) pushFocus(triggerEl);

    const seq = ++DOSSIER_REQ_SEQ;
    PENDING_CLAIM_ID = id;
    $("#drawer-backdrop").hidden = false;
    drawer.inert = false;
    drawer.classList.add("open");
    drawer.setAttribute("aria-hidden", "false");
    $("#drawer-id").textContent = id;
    $("#drawer-badge").innerHTML = `<span class="seal seal-provisional">Loading…</span>`;
    $("#drawer-body").innerHTML = `<div class="empty-state">Fetching verification receipt &amp; source…</div>`;
    $("#drawer-close").focus();
    if (syncUrl) syncURL({ view: CURRENT_VIEW, mission: CURRENT_MISSION, claim: id, push: false });

    try {
      const url = STATIC_MODE
        ? `./data/${encodeURIComponent(CURRENT_MISSION)}/lemmas/${encodeURIComponent(id)}.json`
        : `/api/lemma/${encodeURIComponent(id)}?mission=${encodeURIComponent(CURRENT_MISSION)}`;
      const res = await fetch(url);
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const d = await res.json();
      if (seq !== DOSSIER_REQ_SEQ) return; // Discard stale response (even after closeDossier or mission switch!)
      renderDossierContent(d);
    } catch (err) {
      if (seq !== DOSSIER_REQ_SEQ) return;
      $("#drawer-badge").innerHTML = `<span class="seal seal-refuted">Error</span>`;
      $("#drawer-body").innerHTML = `
        <div class="empty-state">
          <p>Could not load dossier for <strong>${esc(id)}</strong> (${esc(err.message)}).</p>
          <button class="btn btn-ghost btn-sm" type="button" id="dossier-retry-btn">Retry</button>
        </div>`;
      $("#dossier-retry-btn").addEventListener("click", () => openDossier(id, { syncUrl }));
    }
  }

  function renderDossierContent(d) {
    const l = d.lemma;
    const isRec = l.kind === "record";
    const rs = l.record_state || {};
    const cfg = l.record || {};
    $("#drawer-id").textContent = l.id;
    $("#drawer-badge").innerHTML = `${sealHTML(l)} ${prBadgesHTML(l)}`;

    const auditHTML = l.audit
      ? `<div class="audit-box ${esc(l.audit.status)}">
           <strong>Cross-Model Audit (${esc(l.audit.status.toUpperCase())})</strong>
           <span class="mono small"> · ${esc(l.audit.by_model || l.audit.by_seat)} · ${relTime(l.audit.at)}</span>
           <div style="margin-top:5px">${esc(l.audit.notes || "")}</div>
         </div>`
      : !isRec && l.status === "checked" && !l.checker?.statement_frozen
      ? `<div class="audit-box"><strong>Provisional:</strong> Passed the mechanical Judge; awaiting independent cross-model faithfulness audit before counting toward Objectives.</div>`
      : "";

    let recordHTML = "";
    if (isRec) {
      const unit = cfg.unit || "";
      const bestVal = rs.best ? `${safeInt(rs.best.score)} ${unit} (${rs.best.seat})` : `Unclaimed (ceiling ≤ ${safeInt(cfg.start_target)} ${unit})`;
      const nextVal = rs.contradiction ? "Halted (Contradiction)" : rs.closed ? "Exact Optimal Closed ✓" : `≤ ${safeInt(rs.next_target ?? cfg.start_target)} ${unit}`;
      const lbVal = rs.refuted ? `≥ ${safeInt(rs.refuted.inclusive_bound)} ${unit} (¬ Record ${safeInt(rs.refuted.score)} by ${rs.refuted.seat})` : "None proven in Lean yet";
      const litVal = cfg.literature_best != null
        ? `Best known: ${safeInt(cfg.literature_best)}${cfg.literature_lower_bound != null ? ` · LB: ${safeInt(cfg.literature_lower_bound)}` : ""} ${unit}`
        : "—";
      const histItems = [...(rs.history || [])].reverse();
      const histHTML = histItems.length
        ? `<ul class="rec-history">
            ${histItems
              .map((h) => {
                const badgeCls =
                  h.state === "accepted"
                    ? "seal-audited"
                    : h.state === "contradiction"
                    ? "seal-contradiction"
                    : "seal-provisional";
                const label = h.kind === "record_bound" ? `¬ Record ${safeInt(h.score)}` : `Record ${safeInt(h.score)}`;
                return `<li class="rec-hist-item">
                  <span><strong class="mono">${esc(label)}</strong> · <span class="mono small">${esc(h.seat)}</span></span>
                  <span><span class="mono small tabular">${h.points > 0 ? `+${safeInt(h.points)} pts` : "0 pts"}</span> <span class="seal ${badgeCls}">${esc(h.state)}</span></span>
                </li>`;
              })
              .join("")}
          </ul>`
        : `<div class="empty-state" style="padding:14px">No Lean-verified record entries yet — claim the launch ceiling ≤ ${safeInt(cfg.start_target)} ${esc(unit)}!</div>`;
      recordHTML = `
        <div class="d-section">
          <h4>♛ King of the Hill Scoreboard</h4>
          <div class="d-kv">
            <div class="d-kv-item"><span>Current Record Holder</span><strong>${esc(bestVal)}</strong></div>
            <div class="d-kv-item"><span>Next Auto-Ratchet Target</span><strong class="mono">${esc(nextVal)}</strong></div>
            <div class="d-kv-item"><span>Proven Lower Bound</span><strong>${esc(lbVal)}</strong></div>
            <div class="d-kv-item"><span>Literature Reference</span><strong class="mono">${esc(litVal)}</strong></div>
          </div>
        </div>
        <div class="d-section">
          <h4>Record Progression History (${histItems.length})</h4>
          ${histHTML}
        </div>`;
    }

    function renderReceiptBlock(chkObj, label) {
      if (!chkObj) return "";
      return `<div class="d-section">
           <h4>Cryptographic Judge Receipt${label ? ` (${esc(label)})` : ""}</h4>
           <div class="d-kv">
             <div class="d-kv-item"><span>Engine / Judge</span><strong>${esc(chkObj.lean_version || chkObj.judge || "Lean 4")}</strong></div>
             <div class="d-kv-item"><span>Duration / Axioms</span><strong class="mono tabular">${safeInt(chkObj.duration_ms)}ms · ${esc((chkObj.axioms || []).join(", ") || "none")}</strong></div>
             <div class="d-kv-item"><span>Artifact SHA-256</span><strong class="mono">${esc((chkObj.file_hash || "—").slice(0, 18))}…</strong></div>
             <div class="d-kv-item"><span>Core / Statement Hash</span><strong class="mono">${esc((chkObj.statement_hash || chkObj.core_hash || "—").slice(0, 18))}…</strong></div>
           </div>
         </div>`;
    }

    const receiptHTML = isRec
      ? `${renderReceiptBlock(rs.best, "Current Record")}${renderReceiptBlock(rs.refuted, "Proven Lower Bound")}`
      : renderReceiptBlock(l.checker || l.refutation, "");

    const frozenHTML = d.statementSource
      ? `<div class="d-section">
           <h4>Frozen Formal Statement (${esc(l.statement_file)})</h4>
           <pre class="source-pre">${esc(d.statementSource)}</pre>
         </div>`
      : "";

    const srcCode = isRec ? d.leanSource : l.status === "refuted" ? d.refutationSource : d.leanSource;
    const srcPath = isRec ? rs.best?.file : l.status === "refuted" ? l.refutation?.counterexample_file : l.lean_file;
    const sourceHTML = srcCode
      ? `<div class="d-section">
           <h4>${isRec ? "Current Best Record Artifact" : "Verified Artifact"} (${esc(srcPath || "")})</h4>
           <pre class="source-pre">${esc(srcCode)}</pre>
         </div>`
      : "";

    const boundCode = isRec ? (d.boundSource || d.refutationSource) : null;
    const boundSourceHTML =
      isRec && boundCode
        ? `<div class="d-section">
             <h4>Best Proven Lower Bound Artifact (${esc(rs.refuted?.file || "")})</h4>
             <pre class="source-pre">${esc(boundCode)}</pre>
           </div>`
        : "";

    const depsHTML =
      (l.deps || []).length || (d.dependents || []).length
        ? `<div class="d-section">
             <h4>Dependency Graph</h4>
             <div class="mentioned-strip">
               ${(l.deps || []).map((id) => `<button class="chip-btn" type="button" data-open-claim="${esc(id)}">&larr; ${esc(id)}</button>`).join("")}
               ${(d.dependents || []).map((o) => `<button class="chip-btn" type="button" data-open-claim="${esc(o.id)}">${esc(o.id)} &rarr;</button>`).join("")}
             </div>
           </div>`
        : "";

    const donateBtnLabel = isRec
      ? rs.best
        ? `Beat ${l.id} Record (Target ≤ ${safeInt(rs.next_target)})`
        : `Start ${l.id} Hunt (Target ≤ ${safeInt(cfg.start_target)})`
      : `Donate Spare Tokens to ${l.id}`;
    const actionHTML = isClaimDonateable(l)
      ? `<div class="d-section">
           <button class="btn btn-primary" type="button" data-donate-claim="${esc(l.id)}">${esc(donateBtnLabel)}</button>
         </div>`
      : "";

    $("#drawer-body").innerHTML = `
      <div>
        <div class="bounty-id-group" style="margin-bottom:8px">${progMonogram(l.program)} <span class="mono small muted">${esc(l.theorem_name || "")}</span></div>
        <h3 style="margin:0 0 8px;font-family:var(--font-display)">${esc(l.title)}</h3>
        ${l.paper_notes ? `<p class="small muted" style="margin:0">${esc(l.paper_notes)}</p>` : ""}
      </div>
      ${auditHTML}
      ${actionHTML}
      ${recordHTML}
      <div class="d-section">
        <h4>Formal Target / Kernel Signature</h4>
        <pre class="bounty-stmt">${esc(l.verified_signature || l.registered_statement || l.statement || "")}</pre>
      </div>
      ${receiptHTML}
      ${frozenHTML}
      ${sourceHTML}
      ${boundSourceHTML}
      ${depsHTML}
    `;
  }

  function closeDossier({ syncUrl = true } = {}) {
    DOSSIER_REQ_SEQ++; // Cancel any in-flight dossier fetch!
    PENDING_CLAIM_ID = null;
    const drawer = $("#lemma-drawer");
    const wasOpen = drawer.classList.contains("open");
    drawer.classList.remove("open");
    drawer.setAttribute("aria-hidden", "true");
    drawer.inert = true;
    $("#drawer-backdrop").hidden = true;
    if (syncUrl) syncURL({ view: CURRENT_VIEW, mission: CURRENT_MISSION, claim: null, push: false });
    if (wasOpen) popFocus();
  }
  $("#drawer-close").addEventListener("click", () => closeDossier());
  $("#drawer-backdrop").addEventListener("click", () => closeDossier());

  // =========================================================================
  // INTERACTIVE DONATE TOKENS MODAL
  // =========================================================================
  function defaultRecordScore(lemma, kind) {
    const rs = lemma?.record_state || {};
    const cfg = lemma?.record || {};
    if (kind === "record_bound") {
      if (rs.refuted) return safeInt(rs.refuted.score) + 1;
      const floor = safeInt(cfg.bound_floor ?? 0);
      const lit = cfg.literature_lower_bound != null ? Math.max(0, safeInt(cfg.literature_lower_bound) - 1) : floor;
      return Math.max(floor, lit);
    }
    return safeInt(rs.next_target ?? cfg.start_target ?? 0);
  }

  function validateDonateRecordScore(lemma, kind, rawVal) {
    const rs = lemma?.record_state || {};
    const cfg = lemma?.record || {};
    const str = String(rawVal ?? "").trim();
    if (!/^(0|[1-9][0-9]*)$/.test(str)) {
      return { ok: false, reason: "Enter a non-negative integer score." };
    }
    const score = Number(str);
    const scoreMax = safeInt(cfg.score_max ?? 100000);
    if (!Number.isSafeInteger(score) || score > scoreMax) {
      return { ok: false, reason: `Score must be between 0 and ${scoreMax}.` };
    }
    if (kind === "record_bound") {
      const floor = safeInt(cfg.bound_floor ?? 0);
      if (rs.refuted && score <= rs.refuted.score) {
        return { ok: false, reason: `Bound must beat current ¬ Record ${rs.refuted.score} (enter > ${rs.refuted.score}).` };
      }
      if (!rs.refuted && score < floor) {
        return { ok: false, reason: `Bound must be at least ${floor} (proves ≥ ${floor + 1}).` };
      }
      if (rs.best && score >= rs.best.score) {
        return { ok: false, reason: `Bound ${score} conflicts with current verified record ${rs.best.score} (enter < ${rs.best.score}).` };
      }
      return { ok: true, score };
    }
    const ceiling = safeInt(cfg.start_target ?? 0);
    if (rs.best && score >= rs.best.score) {
      return { ok: false, reason: `Score must beat current record ${rs.best.score} (enter ≤ ${rs.best.score - 1}).` };
    }
    if (!rs.best && score > ceiling) {
      return { ok: false, reason: `Score must meet or beat launch ceiling ${ceiling} (enter ≤ ${ceiling}).` };
    }
    if (rs.refuted && score <= rs.refuted.score) {
      return { ok: false, reason: `Score ${score} conflicts with proven lower bound ≥ ${rs.refuted.inclusive_bound}.` };
    }
    return { ok: true, score };
  }

  function buildDonatePrompt(lemma, harness, handle) {
    const slug = STATE?.mission?.slug || CURRENT_MISSION;
    const repo = STATE?.mission?.github_repo || "steph4n-gh/proof-foundry";
    const cleanHandle = (handle || "my-handle").toLowerCase().replace(/[^a-z0-9-_]/g, "") || "my-handle";
    const seat = `donor-${cleanHandle}`;
    const preamble = {
      claude: "You are helping me donate spare Claude Code tokens to Proof Foundry.",
      codex: "You are helping me donate spare Codex tokens to Proof Foundry.",
      gemini: "You are helping me donate spare Gemini CLI tokens to Proof Foundry.",
      t3: "Run this end-to-end in an isolated worktree to donate tokens to Proof Foundry.",
    }[harness] || "Donate my spare AI tokens to Proof Foundry.";

    if (lemma.kind === "record") {
      const kind = DONATE_REC_KIND === "record_bound" ? "record_bound" : "record";
      const check = validateDonateRecordScore(lemma, kind, DONATE_REC_SCORE);
      if (!check.ok) {
        return `# Invalid target score: ${check.reason}\n# Fix the score above to generate a valid Lean 4 & PR Gate prompt.`;
      }
      const score = check.score;
      const t = computeRecordTargetsUI(slug, lemma, kind, score);
      const cliCmd = kind === "record_bound" ? "record-bound" : "record";
      const typeStr = kind === "record_bound" ? `¬ ${lemma.statement_def} ${score}` : `${lemma.statement_def} ${score}`;
      const branch = `donor/${lemma.id.toLowerCase()}-${t.tag}-${cleanHandle}`;
      const ns = t.theoremName.split(".").slice(0, -1).join(".");
      const shortThm = t.theoremName.split(".").pop();
      return [
        preamble,
        `Repository: https://github.com/${repo}`,
        `Mission: ${slug} · King-of-the-Hill Hunt: ${lemma.id} (${kind === "record_bound" ? `Lower Bound ≥ ${score + 1}` : `Record ≤ ${score}`})`,
        `Goal: ${lemma.title}`,
        ``,
        `Instructions:`,
        `1. Clone/pull \`https://github.com/${repo}\`, create branch \`${branch}\`, and read \`CONTRIBUTING_AGENTS.md\`.`,
        `2. Read the FROZEN record statement in \`${lemma.statement_file}\` (do NOT modify Core or Statements files).`,
        `3. Write a NEW score-stamped Lean 4 file at \`${t.artifactFile}\` (no sorry, no admit, no native_decide, no custom axioms) inside \`namespace ${ns}\` proving literally:`,
        `   \`theorem ${shortThm} : ${typeStr} := ...\``,
        `   (Use canonical numeral literal \`${score}\`${kind === "record_bound" ? " and literally `¬`, not `→ False`" : ""} — never edit older score files!)`,
        `4. Verify locally & export the hashless record submission JSON:`,
        `   node hub/fleet.mjs ${cliCmd} --mission ${slug} --lemma ${lemma.id} --score ${score} --seat ${seat} --file ${t.artifactFile} --export`,
        `5. Commit ONLY \`${t.artifactFile}\` + \`${t.submissionFile}\` (never touch state.json or older files), push, and open a PR referencing ${lemma.id}.`,
      ].join("\n");
    }

    const branch = `donor/${lemma.id.toLowerCase()}-${cleanHandle}`;
    const frozenStep = lemma.statement_file
      ? `2. Read the FROZEN formal statement in \`${lemma.statement_file}\`.\n   Your proof MUST import that module and state your theorem literally as:\n   \`theorem ${lemma.theorem_name.split(".").pop()} : ${lemma.statement_def} := ...\`\n   (Or \`: ¬ ${lemma.statement_def}\` if you find a genuine counterexample!).`
      : `2. Read \`${STATE?.mission?.judge?.core_file || "CONTRIBUTING_AGENTS.md"}\` and state your theorem matching:\n   \`${lemma.theorem_name} : ${lemma.registered_statement || lemma.statement}\`.`;

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
      `   (If false, use \`refute --summary "..."\` with a Judge-verified counterexample!)`,
      `5. Revert any edits to state.json/events.ndjson, commit ONLY \`${lemma.lean_file}\` + \`missions/${slug}/submissions/${lemma.id}.*.json\`, push, and open a PR referencing ${lemma.id}.`,
    ].join("\n");
  }

  function refreshDonatePrompt() {
    if (!DONATE_LEMMA) return;
    const copyBtn = $("#donate-copy-btn");
    if (DONATE_LEMMA.kind === "record") {
      const cfg = DONATE_LEMMA.record || {};
      const rs = DONATE_LEMMA.record_state || {};
      const check = validateDonateRecordScore(DONATE_LEMMA, DONATE_REC_KIND, DONATE_REC_SCORE);
      $("#donate-rec-score-label").textContent =
        DONATE_REC_KIND === "record_bound" ? "Refute score b (proves ≥ b+1):" : `Target score (${cfg.unit || "cost"}):`;
      const hintEl = $("#donate-rec-hint");
      if (!check.ok) {
        hintEl.textContent = `⚠ ${check.reason}`;
        hintEl.style.color = "var(--coral)";
        copyBtn.disabled = true;
      } else {
        hintEl.style.color = "";
        hintEl.textContent =
          DONATE_REC_KIND === "record_bound"
            ? rs.refuted
              ? `valid (> ${safeInt(rs.refuted.score)})`
              : `valid (≥ ${safeInt(cfg.bound_floor ?? 0)})`
            : rs.best
            ? `valid (< ${safeInt(rs.best.score)})`
            : `valid (≤ ${safeInt(cfg.start_target)})`;
        copyBtn.disabled = false;
      }
    } else {
      copyBtn.disabled = false;
    }
    $("#donate-prompt-text").value = buildDonatePrompt(DONATE_LEMMA, DONATE_HARNESS, DONATE_HANDLE);
  }

  function openDonateModal(lemma, triggerEl = null) {
    if (!lemma || !isClaimDonateable(lemma)) return;
    pushFocus(triggerEl);
    DONATE_LEMMA = lemma;
    const isRec = lemma.kind === "record";
    $("#donate-claim-meta").textContent = `${CURRENT_MISSION} · ${lemma.id}${isRec ? " · ♛ King of the Hill" : lemma.statement_file ? " · ◆ Frozen Statement" : ""}`;
    $("#donate-title").textContent = lemma.title.slice(0, 90);
    $("#donate-handle").value = DONATE_HANDLE;
    const repo = STATE?.mission?.github_repo || "steph4n-gh/proof-foundry";
    $("#donate-open-gh").href = `https://github.com/${repo}/pulls`;

    // Record hunt controls
    const recBox = $("#donate-record-controls");
    if (isRec) {
      DONATE_REC_KIND = "record";
      DONATE_REC_SCORE = defaultRecordScore(lemma, "record");
      $("#donate-rec-score").value = String(DONATE_REC_SCORE);
      $$("#donate-rec-mode button").forEach((b) => {
        const act = b.dataset.reckind === DONATE_REC_KIND;
        b.classList.toggle("active", act);
        b.setAttribute("aria-selected", act ? "true" : "false");
      });
      recBox.hidden = false;
    } else {
      recBox.hidden = true;
    }

    // PR collision warning
    const prs = lemma.open_prs || [];
    const warn = $("#donate-pr-warn");
    if (prs.length) {
      warn.innerHTML = isRec
        ? `<strong>Active competition:</strong> PR ${prs.map((p) => `<a href="${esc(p.url)}" target="_blank" rel="noopener noreferrer" style="text-decoration:underline">#${safeInt(p.number)}</a>`).join(", ")} also targets <code>${esc(lemma.id)}</code> — you can still submit any strictly better score or lower bound!`
        : `<strong>Heads up:</strong> Active PR ${prs.map((p) => `<a href="${esc(p.url)}" target="_blank" rel="noopener noreferrer" style="text-decoration:underline">#${safeInt(p.number)}</a>`).join(", ")} already targets <code>${esc(lemma.id)}</code>. You may want to pick a different bounty to avoid duplicate work.`;
      warn.hidden = false;
    } else {
      warn.hidden = true;
    }

    $$("#donate-harness-tabs button").forEach((b) => {
      const act = b.dataset.harness === DONATE_HARNESS;
      b.classList.toggle("active", act);
      b.setAttribute("aria-selected", act ? "true" : "false");
    });

    refreshDonatePrompt();
    $("#donate-backdrop").hidden = false;
    $("#donate-modal").hidden = false;
    $("#donate-copy-btn").focus();
  }

  function closeDonateModal() {
    $("#donate-backdrop").hidden = true;
    $("#donate-modal").hidden = true;
    DONATE_LEMMA = null;
    popFocus();
  }

  $("#donate-close").addEventListener("click", closeDonateModal);
  $("#donate-backdrop").addEventListener("click", closeDonateModal);
  $("#donate-harness-tabs").addEventListener("click", (e) => {
    const b = e.target.closest("[data-harness]");
    if (!b) return;
    DONATE_HARNESS = b.dataset.harness;
    localStorage.setItem("pf-harness", DONATE_HARNESS);
    $$("#donate-harness-tabs button").forEach((x) => {
      const act = x === b;
      x.classList.toggle("active", act);
      x.setAttribute("aria-selected", act ? "true" : "false");
    });
    refreshDonatePrompt();
  });
  $("#donate-rec-mode").addEventListener("click", (e) => {
    const b = e.target.closest("[data-reckind]");
    if (!b || !DONATE_LEMMA) return;
    DONATE_REC_KIND = b.dataset.reckind;
    DONATE_REC_SCORE = defaultRecordScore(DONATE_LEMMA, DONATE_REC_KIND);
    $("#donate-rec-score").value = String(DONATE_REC_SCORE);
    $$("#donate-rec-mode button").forEach((x) => {
      const act = x === b;
      x.classList.toggle("active", act);
      x.setAttribute("aria-selected", act ? "true" : "false");
    });
    refreshDonatePrompt();
  });
  $("#donate-rec-score").addEventListener("input", (e) => {
    DONATE_REC_SCORE = e.target.value;
    refreshDonatePrompt();
  });
  $("#donate-handle").addEventListener("input", (e) => {
    DONATE_HANDLE = e.target.value;
    localStorage.setItem("pf-handle", DONATE_HANDLE);
    refreshDonatePrompt();
  });
  $("#donate-copy-btn").addEventListener("click", async () => {
    const text = $("#donate-prompt-text").value;
    try {
      await navigator.clipboard.writeText(text);
      showToast(`Copied ${DONATE_LEMMA?.id || ""} prompt ✓`);
    } catch {
      $("#donate-prompt-text").select();
      showToast("Prompt selected — press ⌘C / Ctrl+C to copy");
    }
  });
  $("#donate-select-btn").addEventListener("click", () => {
    $("#donate-prompt-text").focus();
    $("#donate-prompt-text").select();
  });

  // =========================================================================
  // COMMAND PALETTE (⌘K / Ctrl+K)
  // =========================================================================
  function openCmdPalette() {
    pushFocus(document.activeElement);
    $("#cmd-backdrop").hidden = false;
    $("#cmd-modal").hidden = false;
    $("#cmd-input").value = "";
    renderCmdList("");
    $("#cmd-input").focus();
  }
  function closeCmdPalette() {
    $("#cmd-backdrop").hidden = true;
    $("#cmd-modal").hidden = true;
    popFocus();
  }
  function renderCmdList(query) {
    const q = query.trim().toLowerCase();
    const items = [];
    // Views
    const viewLabels = [
      ["missions", "All Missions Hub"],
      ["control", "Mission Control"],
      ["bounties", "Bounties & Claim Ledger"],
      ["live", "Live Fleet"],
      ["map", "Constellation Proof Map & DAG"],
      ["leaderboard", "Donor Leaderboard"],
      ["graveyard", "The Graveyard"],
      ["feed", "Structured Audit Log"],
    ];
    for (const [v, label] of viewLabels) {
      items.push({ kind: "View", title: label, sub: `#${v}`, run: () => setView(v, { push: true }) });
    }
    for (const m of MISSIONS) {
      items.push({ kind: "Mission", title: m.title, sub: m.slug, run: () => switchMission(m.slug, { targetView: "control" }) });
    }
    for (const l of STATE?.lemmas || []) {
      items.push({ kind: "Claim", title: `${l.id} · ${l.title}`, sub: sealOf(l), run: () => openDossier(l.id) });
    }
    CMD_ITEMS = q ? items.filter((it) => `${it.kind} ${it.title} ${it.sub}`.toLowerCase().includes(q)).slice(0, 14) : items.slice(0, 12);
    CMD_IDX = 0;
    paintCmdItems();
  }
  function paintCmdItems() {
    $("#cmd-list").innerHTML = CMD_ITEMS.length
      ? CMD_ITEMS.map(
          (it, idx) =>
            `<li><button type="button" class="${idx === CMD_IDX ? "active" : ""}" data-cmd-idx="${idx}"><span><span class="prog-tag" style="margin-right:8px">${esc(it.kind)}</span>${esc(it.title.slice(0, 64))}</span><span class="mono small muted">${esc(it.sub)}</span></button></li>`
        ).join("")
      : `<li class="empty-state">No matches</li>`;
  }

  $("#cmd-open-btn").addEventListener("click", openCmdPalette);
  $("#cmd-backdrop").addEventListener("click", closeCmdPalette);
  $("#cmd-input").addEventListener("input", (e) => renderCmdList(e.target.value));
  $("#cmd-list").addEventListener("click", (e) => {
    const b = e.target.closest("[data-cmd-idx]");
    if (!b) return;
    const it = CMD_ITEMS[Number(b.dataset.cmdIdx)];
    closeCmdPalette();
    if (it) it.run();
  });

  // Global delegated clicks for claim dossiers & donate buttons
  document.addEventListener("click", (e) => {
    const don = e.target.closest("[data-donate-claim]");
    if (don) {
      e.stopPropagation();
      const l = STATE?.lemmas?.find((x) => x.id === don.dataset.donateClaim);
      if (l) openDonateModal(l, don);
      return;
    }
    const open = e.target.closest("[data-open-claim]");
    if (open) {
      openDossier(open.dataset.openClaim, { triggerEl: open });
    }
  });

  // Global keyboard shortcuts (strictly guarding text inputs!)
  document.addEventListener("keydown", (e) => {
    if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "k") {
      e.preventDefault();
      if ($("#cmd-modal").hidden) openCmdPalette();
      else closeCmdPalette();
      return;
    }
    if (e.key === "Escape") {
      if (!$("#cmd-modal").hidden) closeCmdPalette();
      else if (!$("#donate-modal").hidden) closeDonateModal();
      else if ($("#lemma-drawer").classList.contains("open")) closeDossier();
      else closeLabMenu();
      return;
    }
    if (!$("#cmd-modal").hidden) {
      if (e.key === "ArrowDown") {
        e.preventDefault();
        CMD_IDX = (CMD_IDX + 1) % Math.max(1, CMD_ITEMS.length);
        paintCmdItems();
      } else if (e.key === "ArrowUp") {
        e.preventDefault();
        CMD_IDX = (CMD_IDX - 1 + Math.max(1, CMD_ITEMS.length)) % Math.max(1, CMD_ITEMS.length);
        paintCmdItems();
      } else if (e.key === "Enter" && CMD_ITEMS[CMD_IDX]) {
        e.preventDefault();
        const it = CMD_ITEMS[CMD_IDX];
        closeCmdPalette();
        it.run();
      }
      return;
    }
    if (e.key === "/" && !isInputFocused()) {
      e.preventDefault();
      if (CURRENT_VIEW === "map") $("#map-search").focus();
      else if (CURRENT_VIEW === "bounties") $("#board-search").focus();
      else openCmdPalette();
    }
  });

  boot();
})();
