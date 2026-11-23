/* PROOF FOUNDRY — Observatory Lab Frontend (Live SSE + Static GitHub Pages) */
(function () {
  const $ = (sel) => document.querySelector(sel);
  const $$ = (sel) => Array.from(document.querySelectorAll(sel));

  let STATE = null;
  let MISSIONS = [];
  let CURRENT_MISSION = new URLSearchParams(location.search).get("mission") || "erdos-combinatorics";
  let STATIC_MODE = false;
  let SSE = null;
  let CURRENT_VIEW = "control";
  let BOUNTY_MODE = "open";
  let DOSSIER_REQ_SEQ = 0;

  // Theme (Midnight Lab default)
  const savedTheme = localStorage.getItem("pf-theme") || "dark";
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
  function safeColor(c) {
    return /^#[0-9a-fA-F]{3,8}$/.test(String(c || "")) ? String(c) : "#38BDF8";
  }
  function safeInt(v) {
    const n = Number(v);
    return Number.isFinite(n) ? Math.round(n) : 0;
  }
  function relTime(iso) {
    if (!iso) return "";
    const diff = Math.max(0, Math.floor((Date.now() - new Date(iso).getTime()) / 1000));
    if (diff < 5) return "just now";
    if (diff < 60) return `${diff}s ago`;
    if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
    return `${Math.floor(diff / 3600)}h ago`;
  }
  function showToast(msg) {
    const t = $("#toast");
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(t._tm);
    t._tm = setTimeout(() => (t.hidden = true), 2200);
  }
  function badgeHTML(st) {
    const labels = { checked: "checked ✓", in_work: "in work", conjecture: "open bounty", refuted: "refuted ✕", dead: "ruled dead" };
    return `<span class="badge badge-${esc(st)}">${esc(labels[st] || st)}</span>`;
  }
  function auditBadgeHTML(audit) {
    if (!audit) return "";
    if (audit.status === "faithful") return ` <span class="badge badge-sky" title="Independently audited by ${esc(audit.by_seat)}">audited ✓</span>`;
    return "";
  }
  function seatById(id) {
    return STATE?.seats?.find((s) => s.id === id);
  }
  function progById(id) {
    return STATE?.programs?.find((p) => p.id === id);
  }

  function buildClaimPrompt(lemma) {
    const slug = STATE?.mission?.slug || CURRENT_MISSION;
    const repo = STATE?.mission?.github_repo || "steph4n-gh/proof-foundry";
    return [
      `Donate my spare tokens to Proof Foundry (https://github.com/${repo}) — Mission "${slug}", Claim ${lemma.id}:`,
      `Claim: ${lemma.title}`,
      `Formal target: ${lemma.theorem_name} :: ${lemma.registered_statement || lemma.statement}`,
      `Steps:`,
      `1. Clone/pull https://github.com/${repo} and read CONTRIBUTING_AGENTS.md + the mission Core file.`,
      `2. Create branch \`donor/${lemma.id.toLowerCase()}\` and write a genuine proof (or counterexample if false!) in \`${lemma.lean_file}\`.`,
      `3. Run the local mechanical Judge & export a conflict-free submission JSON:`,
      `   node hub/fleet.mjs verify --mission ${slug} --lemma ${lemma.id} --seat donor-<my-github-handle> --file ${lemma.lean_file} --theorem ${lemma.theorem_name} --export`,
      `   (Or use \`refute\` with a Judge-verified counterexample if the conjecture is false!)`,
      `4. Commit ONLY your artifact file + \`missions/${slug}/submissions/${lemma.id}.*.json\` (never state.json) and open a GitHub PR.`,
    ].join("\n");
  }

  async function copyClaimPrompt(lemmaId) {
    const l = STATE?.lemmas?.find((x) => x.id === lemmaId);
    if (!l) return;
    try {
      await navigator.clipboard.writeText(buildClaimPrompt(l));
      showToast(`Copied agent prompt for ${l.id} ✓`);
    } catch {
      showToast(`Prompt ready for ${l.id}`);
    }
  }

  // Navigation
  function setView(view) {
    const valid = ["control", "bounties", "live", "map", "leaderboard", "graveyard", "feed"];
    if (!valid.includes(view)) view = "control";
    CURRENT_VIEW = view;
    $$(".view").forEach((el) => (el.hidden = el.id !== `view-${view}`));
    $$(".nav a").forEach((a) => a.classList.toggle("active", a.dataset.nav === view));
    if (STATE) renderActiveView();
  }

  $$("[data-nav]").forEach((a) => {
    a.addEventListener("click", (e) => {
      e.preventDefault();
      const v = a.dataset.nav;
      history.replaceState(null, "", `${location.pathname}?mission=${encodeURIComponent(CURRENT_MISSION)}#${v}`);
      setView(v);
      window.scrollTo({ top: 0, behavior: "smooth" });
    });
  });

  window.addEventListener("hashchange", () => {
    const h = location.hash.replace("#", "") || "control";
    setView(h);
  });

  // Bounty open/all toggle
  $$("[data-bmode]").forEach((btn) => {
    btn.addEventListener("click", () => {
      BOUNTY_MODE = btn.dataset.bmode;
      $$("[data-bmode]").forEach((b) => b.classList.toggle("active", b.dataset.bmode === BOUNTY_MODE));
      if (STATE) renderBountiesView();
    });
  });

  // Global click delegation
  document.addEventListener("click", (e) => {
    const copyBtn = e.target.closest("[data-copy-claim]");
    if (copyBtn) {
      e.stopPropagation();
      copyClaimPrompt(copyBtn.dataset.copyClaim);
      return;
    }
    const lemmaEl = e.target.closest("[data-lemma-id]");
    if (lemmaEl) openDossier(lemmaEl.dataset.lemmaId);
  });

  // Missions bootstrap + SSE
  async function loadMissionsList() {
    try {
      const r = await fetch("/api/missions");
      if (r.ok) {
        const d = await r.json();
        MISSIONS = d.missions || [];
        STATIC_MODE = false;
      } else {
        throw new Error("static fallback");
      }
    } catch {
      const r = await fetch("./data/missions.json");
      const d = await r.json();
      MISSIONS = d.missions || [];
      STATIC_MODE = true;
    }

    const sel = $("#mission-select");
    sel.innerHTML = MISSIONS.map(
      (m) => `<option value="${esc(m.slug)}">${esc(m.title)} (${safeInt(m.counts?.checked)}✓)</option>`
    ).join("");
    if (!MISSIONS.some((m) => m.slug === CURRENT_MISSION) && MISSIONS.length) {
      CURRENT_MISSION = MISSIONS[0].slug;
    }
    sel.value = CURRENT_MISSION;
    sel.onchange = () => switchMission(sel.value);
  }

  async function switchMission(slug) {
    CURRENT_MISSION = slug;
    $("#board-program").innerHTML = `<option value="all">All programs</option>`;
    history.replaceState(null, "", `${location.pathname}?mission=${encodeURIComponent(slug)}#${CURRENT_VIEW}`);
    if (SSE) {
      SSE.close();
      SSE = null;
    }
    if (STATIC_MODE) {
      $("#sse-label").textContent = "Pages";
      const r = await fetch(`./data/${encodeURIComponent(slug)}/state.json`);
      STATE = await r.json();
      renderAll();
    } else {
      SSE = new EventSource(`/api/stream?mission=${encodeURIComponent(slug)}`);
      SSE.addEventListener("open", () => ($("#sse-label").textContent = "Live"));
      SSE.addEventListener("snapshot", (ev) => {
        try {
          const data = JSON.parse(ev.data);
          if (!data.ready) return;
          STATE = data;
          renderAll();
        } catch {}
      });
      SSE.addEventListener("error", () => ($("#sse-label").textContent = "Reconnecting…"));
    }
  }

  function renderAll() {
    const m = STATE.mission || {};
    const c = STATE.counts || {};
    document.title = `Proof Foundry · ${m.title || "Open Science"}`;
    $("#brand-sub").textContent = m.tagline || "spare tokens → verified open science";
    $("#nav-bounty-count").textContent = String(safeInt(c.conjecture) + safeInt(c.in_work));
    if (m.github_repo) {
      $("#gh-repo-link").href = `https://github.com/${m.github_repo}`;
    }
    $("#footer-judge").textContent = `Judge: ${m.judge?.label || "Mechanical Judge"} · No claim counts until verified.`;
    renderJustIn();
    renderActiveView();
  }

  function renderJustIn() {
    const ji = STATE.just_in;
    const bar = $("#just-in");
    if (!ji) {
      bar.hidden = true;
      return;
    }
    bar.hidden = false;
    bar.classList.remove("is-refuted", "is-dead");
    let tag = "CHECKED ✓";
    if (ji.type === "claim_refuted") {
      bar.classList.add("is-refuted");
      tag = "REFUTED ✕";
    } else if (ji.type === "approach_dead") {
      bar.classList.add("is-dead");
      tag = "DEAD END";
    }
    $("#just-in-tag").textContent = tag;
    $("#just-in-text").innerHTML = `<span class="mono">${esc(ji.lemma_id)}</span> — ${esc(ji.title || ji.detail || "")} <span class="muted">(${esc(relTime(ji.at))})</span>`;
    $("#just-in-open").onclick = () => ji.lemma_id && openDossier(ji.lemma_id);
  }

  function renderActiveView() {
    if (!STATE) return;
    if (CURRENT_VIEW === "control") renderControlView();
    else if (CURRENT_VIEW === "bounties") renderBountiesView();
    else if (CURRENT_VIEW === "live") renderLiveView();
    else if (CURRENT_VIEW === "map") renderMapView();
    else if (CURRENT_VIEW === "leaderboard") renderLeaderboardView();
    else if (CURRENT_VIEW === "graveyard") renderGraveyardView();
    else if (CURRENT_VIEW === "feed") renderFeedView();
  }

  // 1. MISSION CONTROL
  function renderControlView() {
    const m = STATE.mission || {};
    const c = STATE.counts || {};
    const objs = m.objectives || [];
    const conquered = objs.filter((o) => o.conquered).length;

    $("#hero-judge-chip").textContent = m.judge?.label || "Mechanical Judge";
    $("#hero-verdict-chip").textContent = `status: ${STATE.meta?.verdict || "open"}`;
    $("#hero-question").textContent = m.question || m.title;
    $("#hero-description").textContent = m.description || "";

    $("#m-objectives").textContent = `${conquered} / ${objs.length}`;
    $("#m-objectives-sub").textContent = objs.length ? `${Math.round((conquered / objs.length) * 100)}% mission milestones closed` : "no milestones yet";
    $("#m-checked").textContent = String(safeInt(c.checked));
    $("#m-audited-sub").textContent = `${safeInt(c.audited_faithful)} cross-model audited`;
    const openN = safeInt(c.conjecture) + safeInt(c.in_work);
    $("#m-open").textContent = String(openN);
    $("#m-active-sub").textContent = `${safeInt(c.agents_working) + safeInt(c.agents_checking)} agents active now`;
    $("#m-fallen").textContent = String(safeInt(c.refuted) + safeInt(c.dead));
    $("#m-fallen-sub").textContent = `${safeInt(c.refuted)} refuted · ${safeInt(c.dead)} barrier-dead`;

    // Tug inline
    const tow = m.tug_of_war;
    const tugEl = $("#tug-inline");
    if (tow?.enabled) {
      tugEl.hidden = false;
      const l = safeInt(c.aims_left_checked), r = safeInt(c.aims_right_checked);
      const pct = l + r === 0 ? 50 : Math.max(10, Math.min(90, Math.round((l / (l + r)) * 100)));
      $("#tug-left-text").textContent = `${tow.left_label}: ${l}`;
      $("#tug-right-text").textContent = `${tow.right_label}: ${r}`;
      $("#tug-l").style.width = `${pct}%`;
      $("#tug-r").style.width = `${100 - pct}%`;
    } else {
      tugEl.hidden = true;
    }

    // Objective Finish-Line Ladders
    $("#objectives-grid").innerHTML = objs.length
      ? objs
          .map((o) => {
            const extLink = o.url ? ` <a class="link-btn" href="${esc(o.url)}" target="_blank" rel="noopener noreferrer">source ↗</a>` : "";
            const statusBadge = o.conquered
              ? `<span class="badge badge-checked">CONQUERED ✓</span>`
              : `<span class="badge badge-sky">${o.completed}/${o.total} verified</span>`;
            const rungs = (o.items || [])
              .map(
                (it) => `<button class="rung-pill ${esc(it.status)}" data-lemma-id="${esc(it.id)}" title="${esc(it.title)}">${esc(it.id)}</button>`
              )
              .join("");
            return `<article class="obj-card ${o.conquered ? "conquered" : ""}">
              <div class="obj-top">
                <span class="obj-tier">${esc(o.tier || "Objective")}${extLink}</span>
                ${statusBadge}
              </div>
              <h3 class="obj-title">${esc(o.title)}</h3>
              <p class="obj-finish">${esc(o.finish_line || "")}</p>
              <div class="obj-bar-row">
                <div class="obj-bar"><div class="obj-bar-fill" style="width:${safeInt(o.pct)}%"></div></div>
                <span class="mono small muted">${safeInt(o.pct)}%</span>
              </div>
              <div class="obj-rungs">${rungs}</div>
            </article>`;
          })
          .join("")
      : `<div class="panel muted">No objectives configured for this mission yet.</div>`;

    // Top 4 Open Bounties
    const openBounties = STATE.lemmas
      .filter((l) => l.status === "conjecture" || l.status === "in_work")
      .sort((a, b) => (a.rung || 99) - (b.rung || 99))
      .slice(0, 4);
    $("#control-bounties").innerHTML = openBounties.length
      ? openBounties.map(renderBountyCard).join("")
      : `<div class="panel"><strong class="mono">ALL BOUNTIES CLEARED ✓</strong> — Open a GitHub issue to propose the next frontier objective!</div>`;

    // Strategy dispatch + Whispers
    const sn = STATE.meta?.strategy_note;
    if (sn) {
      $("#strategy-text").innerHTML = esc(sn.text).replace(/\[?([A-Z]-[a-z0-9]+-\d+)\]?/g, (_m, id) =>
        `<span class="lemma-link" data-lemma-id="${esc(id)}">${esc(id)}</span>`
      );
      $("#strategy-meta").textContent = `${sn.seat} · ${relTime(sn.at)}`;
      $("#mentioned-list").innerHTML = (sn.mentions || [])
        .map((id) => {
          const l = STATE.lemmas.find((x) => x.id === id);
          return l ? `<span class="rung-pill ${esc(l.status)}" data-lemma-id="${esc(l.id)}">${esc(l.id)}</span>` : "";
        })
        .join("");
    }

    const whispers = STATE.whispers || [];
    $("#whispers-count").textContent = `${whispers.length} live`;
    $("#whispers-list").innerHTML = whispers.length
      ? whispers
          .slice(0, 10)
          .map((w) => {
            const seat = seatById(w.seat);
            const dot = seat ? `<span style="color:${safeColor(seat.color)}">●</span> ` : "";
            return `<li class="whisper-item">
              <div class="whisper-meta"><span>${dot}${esc(w.seat)}</span><span>${esc(relTime(w.at))}</span></div>
              <div>${esc(w.text)} ${w.lemma_id ? `<span class="lemma-link" data-lemma-id="${esc(w.lemma_id)}">${esc(w.lemma_id)}</span>` : ""}</div>
            </li>`;
          })
          .join("")
      : `<li class="whisper-item muted">No whispers yet.</li>`;

    $("#overview-events").innerHTML = (STATE.events || []).slice(0, 14).map(renderEventRow).join("");
  }

  function renderBountyCard(l) {
    const prog = progById(l.program);
    return `<article class="bounty-card">
      <div>
        <div class="bounty-top">
          <span class="mono small muted"><strong style="color:var(--sky)">${esc(l.id)}</strong> · ${esc(prog?.title || l.program)}</span>
          ${badgeHTML(l.status)}
        </div>
        <h3 class="bounty-title" data-lemma-id="${esc(l.id)}" style="margin-top:8px">${esc(l.title)}</h3>
      </div>
      <div class="bounty-stmt" title="${esc(l.registered_statement || l.statement)}">${esc(l.registered_statement || l.statement || l.theorem_name)}</div>
      <div class="bounty-foot">
        <button class="link-btn" data-lemma-id="${esc(l.id)}" type="button">Inspect spec &rarr;</button>
        <button class="btn btn-primary btn-sm" data-copy-claim="${esc(l.id)}" type="button">Copy Agent Prompt</button>
      </div>
    </article>`;
  }

  function renderEventRow(ev) {
    const labels = {
      checker_accepted: "✓ checked",
      claim_refuted: "✕ refuted",
      approach_dead: "☠ dead end",
      checker_rejected: "! rejected",
      attempt_started: "→ claimed",
      seat_message: "✉ dispatch",
      lemma_stated: "+ stated",
      strategy_update: "★ strategy",
      lemma_audited: "◎ audited",
      fleet_started: "● online",
    };
    const lemmaChip = ev.lemma_id ? `<span class="lemma-link" data-lemma-id="${esc(ev.lemma_id)}">${esc(ev.lemma_id)}</span> ` : "";
    const ms = ev.duration_ms ? ` <span class="mono small muted">(${safeInt(ev.duration_ms)}ms)</span>` : "";
    const to = ev.to ? ` <strong>→ ${esc(ev.to)}</strong>: ` : " ";
    return `<li class="event-row">
      <span class="ev-time">${esc(relTime(ev.at))}</span>
      <span class="ev-type ${esc(ev.type)}">${esc(labels[ev.type] || ev.type)}</span>
      <span>${lemmaChip}<strong>${esc(ev.seat || "")}</strong>${to}${esc(ev.title || ev.detail || "")}${ms}</span>
      <span class="mono small muted">${ev.file_hash ? "#" + esc(String(ev.file_hash).slice(0, 8)) : ""}</span>
    </li>`;
  }

  // 2. BOUNTIES & BOARD
  function renderBountiesView() {
    const progSel = $("#board-program");
    if (progSel.options.length <= 1) {
      STATE.programs.forEach((p) => {
        const opt = document.createElement("option");
        opt.value = p.id;
        opt.textContent = p.title;
        progSel.appendChild(opt);
      });
    }
    const q = ($("#board-search").value || "").toLowerCase();
    const pf = progSel.value;
    const sf = $("#board-status").value;

    const filtered = STATE.lemmas.filter((l) => {
      if (pf !== "all" && l.program !== pf) return false;
      if (sf !== "all" && l.status !== sf) return false;
      if (BOUNTY_MODE === "open" && sf === "all" && l.status !== "conjecture" && l.status !== "in_work") return false;
      if (q && !`${l.id} ${l.title} ${l.theorem_name} ${l.statement}`.toLowerCase().includes(q)) return false;
      return true;
    });

    $("#bounties-open-grid").hidden = BOUNTY_MODE !== "open";
    $("#bounties-table-wrap").hidden = BOUNTY_MODE === "open";

    if (BOUNTY_MODE === "open") {
      $("#bounties-open-grid").innerHTML = filtered.length
        ? filtered.map(renderBountyCard).join("")
        : `<div class="panel muted">No matching open bounties. Switch to "Full Claim Table" to inspect verified results.</div>`;
    } else {
      $("#board-tbody").innerHTML = filtered
        .map((l) => {
          const prog = progById(l.program);
          const judgeCell = l.checker?.ok
            ? `<span class="mono small" style="color:var(--emerald)">✓ ${safeInt(l.checker.duration_ms)}ms</span>`
            : l.refutation
              ? `<span class="mono small" style="color:var(--coral)">✕ refuted</span>`
              : l.epitaph
                ? `<span class="mono small muted">${esc(l.epitaph.wall)}</span>`
                : `<button class="btn btn-primary btn-sm" data-copy-claim="${esc(l.id)}" type="button">Copy Prompt</button>`;
          return `<tr data-lemma-id="${esc(l.id)}">
            <td class="mono"><strong>${esc(l.id)}</strong></td>
            <td>${badgeHTML(l.status)}${auditBadgeHTML(l.audit)}</td>
            <td class="small">${esc(prog?.title || l.program)}</td>
            <td>${esc(l.title)}</td>
            <td class="mono small">${esc(l.checker?.by_seat || l.refutation?.by_seat || l.claimed_by || "open")}</td>
            <td>${judgeCell}</td>
          </tr>`;
        })
        .join("");
    }
  }
  ["board-search", "board-program", "board-status"].forEach((id) => {
    document.getElementById(id)?.addEventListener("input", () => STATE && renderBountiesView());
  });

  // 3. LIVE FLEET
  function renderLiveView() {
    const c = STATE.counts || {};
    const runs = STATE.checker_runs || [];
    const totalRuns = safeInt(STATE.meta.checker_runs_total ?? runs.length);
    const totalPasses = safeInt(STATE.meta.checker_runs_passed ?? runs.filter((r) => r.ok).length);
    $("#live-header-stats").textContent = `${safeInt(c.agents_working) + safeInt(c.agents_checking)} active · ${totalRuns} Judge runs · ${(STATE.messages || []).length} dispatches`;
    $("#checker-pass-rate").textContent = totalRuns ? `${totalPasses}/${totalRuns} verified` : "0 runs";
    $("#live-msg-count").textContent = `${(STATE.messages || []).length} messages`;

    const seats = STATE.seats || [];
    const W = 620, H = 330, cx = W / 2, cy = H / 2, rx = 215, ry = 118;
    const pos = {};
    seats.forEach((s, i) => {
      const ang = (i / Math.max(seats.length, 1)) * Math.PI * 2 - Math.PI / 2;
      pos[s.id] = { x: cx + Math.cos(ang) * rx, y: cy + Math.sin(ang) * ry, seat: s };
    });

    const arcs = (STATE.messages || [])
      .slice(0, 14)
      .map((m, idx) => {
        const a = pos[m.from], b = pos[m.to];
        if (!a || !b || m.from === m.to) return "";
        const mx = (a.x + b.x) / 2 + (cy - (a.y + b.y) / 2) * 0.2;
        const my = (a.y + b.y) / 2 + ((a.x + b.x) / 2 - cx) * 0.2;
        const col = m.kind === "challenge" ? "#F43F5E" : m.kind === "ruling" ? "#94A3B8" : "#10B981";
        return `<path d="M ${a.x} ${a.y} Q ${mx} ${my} ${b.x} ${b.y}" fill="none" stroke="${col}" stroke-width="${idx < 3 ? 2 : 1.2}" stroke-opacity="${Math.max(0.2, 0.85 - idx * 0.06)}" stroke-dasharray="${m.kind === "challenge" ? "4 3" : ""}"/>`;
      })
      .join("");

    const judgeWord = STATE.mission?.judge?.type === "lean4" ? "Lean 4" : "Judge";
    const nodes = seats
      .map((s) => {
        const p = pos[s.id];
        const ring =
          s.status === "working"
            ? `<circle cx="${p.x}" cy="${p.y}" r="24" fill="none" stroke="#10B981" stroke-width="2" stroke-opacity="0.6"/>`
            : s.status === "checking"
              ? `<circle cx="${p.x}" cy="${p.y}" r="24" fill="none" stroke="#F59E0B" stroke-width="2.5" stroke-dasharray="4 3"/>`
              : "";
        return `<g>
          ${ring}
          <circle cx="${p.x}" cy="${p.y}" r="17" fill="${safeColor(s.color)}" stroke="var(--surface)" stroke-width="2.5"/>
          <text x="${p.x}" y="${p.y + 4}" text-anchor="middle" fill="#fff" font-family="JetBrains Mono, monospace" font-size="10.5" font-weight="600">${esc(s.badge)}</text>
          <text x="${p.x}" y="${p.y + 32}" text-anchor="middle" fill="var(--ink)" font-size="11" font-weight="600">${esc(s.name)}</text>
          <text x="${p.x}" y="${p.y + 44}" text-anchor="middle" fill="var(--ink-3)" font-family="JetBrains Mono, monospace" font-size="9.5">${esc(s.model)}</text>
        </g>`;
      })
      .join("");

    $("#live-seat-graph").innerHTML = `<svg viewBox="0 0 ${W} ${H}" width="100%" height="auto">
      <circle cx="${cx}" cy="${cy}" r="40" fill="var(--surface-2)" stroke="var(--border-strong)" stroke-dasharray="3 3"/>
      <text x="${cx}" y="${cy - 3}" text-anchor="middle" fill="var(--ink)" font-family="Space Grotesk, sans-serif" font-size="13.5" font-weight="700">${esc(judgeWord)}</text>
      <text x="${cx}" y="${cy + 12}" text-anchor="middle" fill="var(--sky)" font-family="JetBrains Mono, monospace" font-size="9">ONE JUDGE</text>
      ${arcs}${nodes}
    </svg>`;

    $("#live-seat-cards").innerHTML = seats
      .map(
        (s) => `<div class="seat-card is-${esc(s.status)}">
        <div class="seat-top">
          <div style="display:flex;align-items:center;gap:8px">
            <span class="seat-avatar" style="background:${safeColor(s.color)}">${esc(s.badge)}</span>
            <div>
              <div style="font-weight:600;font-size:13px">${esc(s.name)}</div>
              <div class="mono small muted">${esc(s.model)}</div>
            </div>
          </div>
          <span class="badge ${s.status === "working" ? "badge-checked" : s.status === "checking" ? "badge-in_work" : "badge-conjecture"}">${esc(s.status)}</span>
        </div>
        <div class="small muted">${esc(s.current_whisper || "")}</div>
        <div class="mono small muted" style="display:flex;justify-content:space-between;border-top:1px solid var(--border);padding-top:6px">
          <span>${s.current_lemma ? `<span class="lemma-link" data-lemma-id="${esc(s.current_lemma)}">${esc(s.current_lemma)}</span>` : "standby"}</span>
          <span>✓${safeInt(s.counts?.checked)} ✕${safeInt(s.counts?.refuted)} ☠${safeInt(s.counts?.blocked)}</span>
        </div>
      </div>`
      )
      .join("");

    $("#live-checker-runs").innerHTML = runs.length
      ? runs
          .slice(0, 25)
          .map(
            (r) => `<li class="ticker-item">
            <div class="ticker-top">
              <span><span class="badge ${r.ok ? (r.kind === "refutation" ? "badge-refuted" : "badge-checked") : "badge-in_work"}">${r.ok ? (r.kind === "refutation" ? "REFUTED ✓" : "PASS ✓") : "FAIL ✕"}</span> <span class="lemma-link" data-lemma-id="${esc(r.lemma_id)}">${esc(r.lemma_id)}</span></span>
              <span class="muted">${safeInt(r.duration_ms)}ms · ${esc(relTime(r.at))}</span>
            </div>
            <div class="mono small">${esc(r.theorem)}</div>
            <div class="small muted">${esc(r.seat)} · ${esc(r.reason)}</div>
          </li>`
          )
          .join("")
      : `<li class="ticker-item muted">No Judge runs yet.</li>`;

    $("#live-messages").innerHTML = (STATE.messages || []).length
      ? (STATE.messages || [])
          .slice(0, 25)
          .map(
            (m) => `<li class="ticker-item">
            <div class="ticker-top">
              <span><strong>${esc(m.from)}</strong> → <strong>${esc(m.to)}</strong> <span class="badge badge-conjecture">${esc(m.kind)}</span></span>
              <span class="muted">${esc(relTime(m.at))}</span>
            </div>
            <div>${m.lemma_id ? `<span class="lemma-link" data-lemma-id="${esc(m.lemma_id)}">${esc(m.lemma_id)}</span> ` : ""}${esc(m.text)}</div>
          </li>`
          )
          .join("")
      : `<li class="ticker-item muted">No dispatches yet.</li>`;
  }

  // 4. PROOF MAP & REL DAG
  const canvas = $("#proof-map-canvas");
  const ctx = canvas.getContext("2d");
  let mapNodes = [];
  let clusterMeta = [];
  let cam = { x: 0, y: 0, zoom: 0.9 };
  let dragging = false;
  let dragStart = { x: 0, y: 0 };
  let hoveredNode = null;
  let animTick = 0;
  let canvasSize = { w: 1200, h: 540 };

  function updateCanvasResolution() {
    const rect = canvas.parentElement.getBoundingClientRect();
    if (rect.width <= 0 || rect.height <= 0) return;
    canvasSize = { w: rect.width, h: rect.height };
    const dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(rect.width * dpr);
    canvas.height = Math.round(rect.height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }
  new ResizeObserver(() => {
    updateCanvasResolution();
    if (STATE && CURRENT_VIEW === "map") drawProofMap();
  }).observe(canvas.parentElement);

  function renderMapView() {
    layoutProofMap();
    updateCanvasResolution();
    drawProofMap();
    renderRelDAG();
  }

  function layoutProofMap() {
    const progs = STATE.programs || [];
    const nodes = [], clusters = [];
    const cols = Math.min(3, Math.max(1, progs.length));
    const rows = Math.ceil(progs.length / cols);
    progs.forEach((p, idx) => {
      const col = idx % cols, row = Math.floor(idx / cols);
      const cx = (col - (cols - 1) / 2) * 390;
      const cy = (row - (rows - 1) / 2) * 260;
      const ls = STATE.lemmas
        .filter((l) => l.program === p.id)
        .sort((a, b) => (a.rung || 99) - (b.rung || 99) || a.id.localeCompare(b.id));
      let placed = 0, ringIdx = 0, maxR = 64;
      while (placed < ls.length) {
        const ringR = ls.length === 1 ? 0 : 54 + ringIdx * 52;
        const cap = ringR === 0 ? 1 : Math.max(5, Math.floor((2 * Math.PI * ringR) / 76));
        const slice = ls.slice(placed, placed + cap);
        slice.forEach((l, j) => {
          const ang = (j / slice.length) * Math.PI * 2 - Math.PI / 2 + ringIdx * 0.35;
          nodes.push({ id: l.id, lemma: l, prog: p, x: cx + Math.cos(ang) * ringR, y: cy + Math.sin(ang) * ringR });
        });
        maxR = Math.max(maxR, ringR + 36);
        placed += slice.length;
        ringIdx++;
      }
      clusters.push({ prog: p, cx, cy, haloR: maxR });
    });
    mapNodes = nodes;
    clusterMeta = clusters;
  }

  function worldToScreen(wx, wy) {
    return { x: canvasSize.w / 2 + (wx + cam.x) * cam.zoom, y: canvasSize.h / 2 + (wy + cam.y) * cam.zoom };
  }

  function drawProofMap() {
    if (!STATE || CURRENT_VIEW !== "map") return;
    if (canvas.width === 0) updateCanvasResolution();
    ctx.clearRect(0, 0, canvasSize.w, canvasSize.h);
    ctx.save();
    clusterMeta.forEach((cl) => {
      const sc = worldToScreen(cl.cx, cl.cy);
      ctx.beginPath();
      ctx.arc(sc.x, sc.y, cl.haloR * cam.zoom, 0, Math.PI * 2);
      ctx.fillStyle = "rgba(56, 189, 248, 0.03)";
      ctx.fill();
      ctx.strokeStyle = "rgba(56, 189, 248, 0.14)";
      ctx.stroke();
      ctx.fillStyle = "rgba(237, 242, 250, 0.72)";
      ctx.font = `600 ${Math.max(10, 11 * cam.zoom)}px "Space Grotesk", sans-serif`;
      ctx.textAlign = "center";
      ctx.fillText(cl.prog.title.toUpperCase(), sc.x, sc.y - (cl.haloR + 8) * cam.zoom);
    });

    const byId = Object.fromEntries(mapNodes.map((n) => [n.id, n]));
    mapNodes.forEach((n) => {
      (n.lemma.deps || []).forEach((depId) => {
        const d = byId[depId];
        if (!d) return;
        const a = worldToScreen(d.x, d.y), b = worldToScreen(n.x, n.y);
        const lit = d.lemma.status === "checked" && n.lemma.status === "checked";
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b.x, b.y);
        ctx.strokeStyle = lit ? "rgba(16, 185, 129, 0.55)" : "rgba(148, 163, 184, 0.18)";
        ctx.lineWidth = lit ? 1.6 : 1;
        ctx.stroke();
      });
    });

    const pulse = (Math.sin(animTick * 0.08) + 1) / 2;
    mapNodes.forEach((n) => {
      const p = worldToScreen(n.x, n.y);
      const st = n.lemma.status;
      const isHover = hoveredNode?.id === n.id;
      const r = (isHover ? 10.5 : 8) * Math.min(1.4, Math.max(0.75, cam.zoom));
      if (st === "in_work") {
        ctx.beginPath();
        ctx.arc(p.x, p.y, r + 5 + pulse * 6, 0, Math.PI * 2);
        ctx.fillStyle = `rgba(245, 158, 11, ${0.28 - pulse * 0.16})`;
        ctx.fill();
      }
      ctx.beginPath();
      if (st === "dead") ctx.rect(p.x - r * 0.85, p.y - r * 0.85, r * 1.7, r * 1.7);
      else ctx.arc(p.x, p.y, r, 0, Math.PI * 2);
      if (st === "checked") { ctx.fillStyle = "#10B981"; ctx.fill(); }
      else if (st === "in_work") { ctx.fillStyle = "#F59E0B"; ctx.fill(); }
      else if (st === "refuted") { ctx.fillStyle = "#F43F5E"; ctx.fill(); }
      else if (st === "dead") { ctx.fillStyle = "#64748B"; ctx.fill(); }
      else {
        ctx.fillStyle = "#101725";
        ctx.fill();
        ctx.setLineDash([3, 2]);
        ctx.strokeStyle = "#94A3B8";
        ctx.lineWidth = 1.4;
        ctx.stroke();
        ctx.setLineDash([]);
      }
      ctx.fillStyle = isHover ? "#FFFFFF" : "rgba(237, 242, 250, 0.86)";
      ctx.font = `500 ${Math.max(9, 10 * Math.min(1.25, cam.zoom))}px "JetBrains Mono", monospace`;
      ctx.textAlign = "center";
      ctx.fillText(n.id, p.x, p.y + r + 12);
    });
    ctx.restore();
  }

  function animateLoop() {
    if (STATE && CURRENT_VIEW === "map" && mapNodes.some((n) => n.lemma.status === "in_work")) {
      animTick++;
      drawProofMap();
    }
    requestAnimationFrame(animateLoop);
  }
  requestAnimationFrame(animateLoop);

  function hitTest(mx, my) {
    let best = null, bestD2 = Math.pow(Math.max(12, 16 * cam.zoom), 2);
    for (const n of mapNodes) {
      const p = worldToScreen(n.x, n.y);
      const d2 = (mx - p.x) ** 2 + (my - p.y) ** 2;
      if (d2 <= bestD2) { bestD2 = d2; best = n; }
    }
    return best;
  }
  canvas.addEventListener("mousedown", (e) => {
    const r = canvas.getBoundingClientRect();
    const hit = hitTest(e.clientX - r.left, e.clientY - r.top);
    if (hit) return openDossier(hit.id);
    dragging = true;
    dragStart = { x: e.clientX, y: e.clientY };
  });
  window.addEventListener("mousemove", (e) => {
    if (dragging) {
      cam.x += (e.clientX - dragStart.x) / cam.zoom;
      cam.y += (e.clientY - dragStart.y) / cam.zoom;
      dragStart = { x: e.clientX, y: e.clientY };
      drawProofMap();
      return;
    }
    if (CURRENT_VIEW !== "map") return;
    const r = canvas.getBoundingClientRect();
    const mx = e.clientX - r.left, my = e.clientY - r.top;
    if (mx < 0 || my < 0 || mx > r.width || my > r.height) {
      if (hoveredNode) { hoveredNode = null; $("#map-hover-card").hidden = true; drawProofMap(); }
      return;
    }
    const hit = hitTest(mx, my);
    const changed = hit?.id !== hoveredNode?.id;
    hoveredNode = hit;
    const card = $("#map-hover-card");
    if (hit) {
      canvas.style.cursor = "pointer";
      card.hidden = false;
      card.style.left = `${Math.min(r.width - 310, mx + 14)}px`;
      card.style.top = `${Math.min(r.height - 100, my + 14)}px`;
      card.innerHTML = `<div style="display:flex;justify-content:space-between;gap:8px;margin-bottom:4px"><strong class="mono">${esc(hit.id)}</strong>${badgeHTML(hit.lemma.status)}</div><div>${esc(hit.lemma.title)}</div>`;
    } else {
      canvas.style.cursor = "grab";
      card.hidden = true;
    }
    if (changed) drawProofMap();
  });
  window.addEventListener("mouseup", () => (dragging = false));
  canvas.addEventListener("wheel", (e) => {
    e.preventDefault();
    cam.zoom = Math.max(0.45, Math.min(2.6, cam.zoom * (e.deltaY < 0 ? 1.12 : 0.89)));
    drawProofMap();
  }, { passive: false });
  $("#map-zoom-in").addEventListener("click", () => { cam.zoom = Math.min(2.6, cam.zoom * 1.2); drawProofMap(); });
  $("#map-zoom-out").addEventListener("click", () => { cam.zoom = Math.max(0.45, cam.zoom * 0.82); drawProofMap(); });
  $("#map-reset").addEventListener("click", () => { cam = { x: 0, y: 0, zoom: 0.9 }; drawProofMap(); });

  const mapSearch = $("#map-search"), mapSearchRes = $("#map-search-results");
  mapSearch.addEventListener("input", () => {
    const q = mapSearch.value.trim().toLowerCase();
    if (!q || !STATE) { mapSearchRes.hidden = true; return; }
    const hits = STATE.lemmas.filter((l) => `${l.id} ${l.title}`.toLowerCase().includes(q)).slice(0, 8);
    if (!hits.length) { mapSearchRes.hidden = true; return; }
    mapSearchRes.hidden = false;
    mapSearchRes.innerHTML = hits.map((l) => `<div class="search-hit" data-jump="${esc(l.id)}"><strong class="mono">${esc(l.id)}</strong> ${badgeHTML(l.status)}<div class="muted">${esc(l.title.slice(0, 56))}</div></div>`).join("");
  });
  mapSearchRes.addEventListener("click", (e) => {
    const hit = e.target.closest("[data-jump]");
    if (!hit) return;
    const node = mapNodes.find((n) => n.id === hit.dataset.jump);
    if (node) { cam.x = -node.x; cam.y = -node.y; cam.zoom = 1.35; drawProofMap(); }
    mapSearchRes.hidden = true;
    openDossier(hit.dataset.jump);
  });

  function renderRelDAG() {
    const lemmas = STATE.lemmas || [];
    const byId = Object.fromEntries(lemmas.map((l) => [l.id, l]));
    const memo = {};
    function depthOf(id, p = new Set()) {
      if (memo[id] !== undefined) return memo[id];
      if (p.has(id)) return 0;
      const np = new Set(p); np.add(id);
      const l = byId[id];
      const ds = (l?.deps || []).filter((d) => Boolean(byId[d]));
      if (!ds.length) return (memo[id] = 0);
      return (memo[id] = 1 + Math.max(...ds.map((d) => depthOf(d, np))));
    }
    const cols = {};
    lemmas.forEach((l) => { const d = depthOf(l.id); (cols[d] = cols[d] || []).push(l); });
    const keys = Object.keys(cols).map(Number).sort((a, b) => a - b);
    const maxR = Math.max(...keys.map((k) => cols[k].length), 1);
    const colW = 230, rowH = 62, W = Math.max(760, keys.length * colW + 60), H = Math.max(240, maxR * rowH + 50);
    const coords = {};
    keys.forEach((k, ci) => cols[k].forEach((l, ri) => (coords[l.id] = { x: 24 + ci * colW, y: 24 + ri * rowH })));
    const edges = [];
    lemmas.forEach((l) => (l.deps || []).forEach((d) => {
      const a = coords[d], b = coords[l.id];
      if (!a || !b) return;
      const x1 = a.x + 166, y1 = a.y + 20, x2 = b.x, y2 = b.y + 20, mx = (x1 + x2) / 2;
      const lit = byId[d]?.status === "checked" && l.status === "checked";
      edges.push(`<path d="M ${x1} ${y1} C ${mx} ${y1}, ${mx} ${y2}, ${x2} ${y2}" fill="none" stroke="${lit ? "#10B981" : "var(--border-strong)"}" stroke-width="${lit ? 2 : 1.2}"/>`);
    }));
    const nodes = lemmas.map((l) => {
      const p = coords[l.id];
      const stroke = l.status === "checked" ? "var(--emerald)" : l.status === "refuted" ? "var(--coral)" : l.status === "in_work" ? "var(--amber)" : "var(--border-strong)";
      return `<g data-lemma-id="${esc(l.id)}" style="cursor:pointer">
        <rect x="${p.x}" y="${p.y}" width="166" height="40" rx="6" fill="var(--bg)" stroke="${stroke}" stroke-width="1.4" stroke-dasharray="${l.status === "conjecture" ? "4 3" : ""}"/>
        <text x="${p.x + 9}" y="${p.y + 17}" fill="var(--ink)" font-family="JetBrains Mono, monospace" font-size="11" font-weight="600">${esc(l.id)}</text>
        <text x="${p.x + 9}" y="${p.y + 31}" fill="var(--ink-3)" font-size="10">${esc(l.title.slice(0, 22))}${l.title.length > 22 ? "…" : ""}</text>
      </g>`;
    }).join("");
    $("#rel-graph-wrap").innerHTML = `<svg width="${W}" height="${H}" viewBox="0 0 ${W} ${H}">${edges.join("")}${nodes}</svg>`;
  }

  // 5. LEADERBOARD
  function renderLeaderboardView() {
    const seats = [...(STATE.seats || [])].map((s) => {
      const checked = safeInt(s.counts?.checked);
      const refuted = safeInt(s.counts?.refuted);
      const blocked = safeInt(s.counts?.blocked);
      return { ...s, score: checked * 10 + refuted * 10 + blocked * 5 };
    }).sort((a, b) => b.score - a.score);

    const byModel = {};
    seats.forEach((s) => {
      const m = s.model || "Unknown";
      byModel[m] = (byModel[m] || 0) + safeInt(s.counts?.checked) + safeInt(s.counts?.refuted);
    });
    const modelArr = Object.entries(byModel).sort((a, b) => b[1] - a[1]);
    const maxM = Math.max(1, ...modelArr.map((x) => x[1]));

    $("#leaderboard-models").innerHTML = modelArr
      .map(
        ([model, total]) => `<div class="mbar-row">
        <div class="mbar-head"><span>${esc(model)}</span><span>${total} verified</span></div>
        <div class="mbar-track"><div class="mbar-fill" style="width:${Math.round((total / maxM) * 100)}%"></div></div>
      </div>`
      )
      .join("");

    const slug = STATE.mission?.slug || CURRENT_MISSION;
    $("#leaderboard-howto").textContent =
`git clone https://github.com/${STATE.mission?.github_repo || "steph4n-gh/proof-foundry"}.git
node hub/fleet.mjs next --mission ${slug}
# Write your Lean 4 proof or counterexample, then run Judge + export:
node hub/fleet.mjs verify --mission ${slug} --lemma <ID> --seat donor-<handle> --file <path> --theorem <target> --export
# Commit ONLY your artifact + missions/${slug}/submissions/<ID>.*.json and open a PR!`;

    $("#leaderboard-tbody").innerHTML = seats
      .map(
        (s, idx) => `<tr>
        <td class="mono">#${idx + 1}</td>
        <td><strong>${esc(s.name)}</strong> <span class="mono small muted">${esc(s.id)}</span></td>
        <td class="mono small">${esc(s.model)}</td>
        <td class="mono" style="color:var(--emerald)">${safeInt(s.counts?.checked)}</td>
        <td class="mono" style="color:var(--coral)">${safeInt(s.counts?.refuted)}</td>
        <td class="mono muted">${safeInt(s.counts?.blocked)}</td>
        <td class="mono"><strong>${s.score}</strong></td>
      </tr>`
      )
      .join("");
  }

  // 6. GRAVEYARD
  function renderGraveyardView() {
    const fallen = STATE.lemmas
      .filter((l) => l.status === "refuted" || l.status === "dead")
      .sort((a, b) => String(b.updated_at || "").localeCompare(String(a.updated_at || "")));
    $("#graveyard-grid").innerHTML = fallen.length
      ? fallen
          .map((l) => {
            const isRef = l.status === "refuted";
            return `<article class="tomb is-${esc(l.status)}" data-lemma-id="${esc(l.id)}">
              <div class="bounty-top"><strong class="mono">${esc(l.id)}</strong>${badgeHTML(l.status)}</div>
              <h3>${esc(l.title)}</h3>
              <div class="mono small" style="color:${isRef ? "var(--coral)" : "var(--ink-2)"}">${esc(isRef ? `Refuted by ${l.refutation?.by_seat} (${safeInt(l.refutation?.duration_ms)}ms)` : `Barrier wall: ${l.epitaph?.wall}`)}</div>
              <p class="small muted">${esc(isRef ? l.refutation?.summary : l.epitaph?.reason)}</p>
            </article>`;
          })
          .join("")
      : `<div class="panel muted">No casualties yet in this mission — Red Team is actively hunting counterexamples.</div>`;
  }

  // 7. FEED
  function renderFeedView() {
    const f = $("#feed-filter").value;
    const evs = (STATE.events || []).filter((e) => f === "all" || e.type === f);
    $("#full-feed-list").innerHTML = evs.map(renderEventRow).join("");
  }
  $("#feed-filter")?.addEventListener("change", () => STATE && renderFeedView());

  // DOSSIER DRAWER
  async function openDossier(id) {
    const reqId = ++DOSSIER_REQ_SEQ;
    $("#drawer-backdrop").hidden = false;
    $("#lemma-drawer").classList.add("open");
    $("#lemma-drawer").setAttribute("aria-hidden", "false");
    $("#drawer-id").textContent = id;
    $("#drawer-badge").innerHTML = "";
    $("#drawer-body").innerHTML = `<p class="muted">Loading verification receipt &amp; source…</p>`;

    try {
      const url = STATIC_MODE
        ? `./data/${encodeURIComponent(CURRENT_MISSION)}/lemmas/${encodeURIComponent(id)}.json`
        : `/api/lemma/${encodeURIComponent(id)}?mission=${encodeURIComponent(CURRENT_MISSION)}`;
      const res = await fetch(url);
      const data = await res.json();
      if (reqId !== DOSSIER_REQ_SEQ) return;
      if (data.error) throw new Error(data.error);
      const l = data.lemma;
      const prog = progById(l.program);
      $("#drawer-badge").innerHTML = `${badgeHTML(l.status)}${auditBadgeHTML(l.audit)}`;

      let receipt = "";
      if (l.checker?.ok) {
        receipt += `<div class="panel" style="border-color:var(--emerald)">
          <div class="panel-head"><h3 style="color:var(--emerald)">Mechanical Judge Receipt · VERIFIED</h3><span class="mono small">${safeInt(l.checker.duration_ms)}ms</span></div>
          <div class="receipt-grid">
            <div><strong>Engine:</strong> ${esc(l.checker.lean_version)}</div>
            <div><strong>Verified by:</strong> ${esc(l.checker.by_seat)}</div>
            <div><strong>Axioms/Checks:</strong> ${l.checker.axioms?.length ? esc(l.checker.axioms.join(", ")) : "none (pure logic)"}</div>
            <div><strong>File SHA-256:</strong> #${esc(String(l.checker.file_hash || "").slice(0, 16))}</div>
          </div>
        </div>`;
      }
      if (l.refutation) {
        receipt += `<div class="panel" style="border-color:var(--coral)">
          <div class="panel-head"><h3 style="color:var(--coral)">Refuted by Counterexample</h3><span class="mono small">${safeInt(l.refutation.duration_ms)}ms</span></div>
          <p class="small">${esc(l.refutation.summary)}</p>
          <p class="mono small muted" style="margin-top:6px">By ${esc(l.refutation.by_seat)} · #${esc(String(l.refutation.file_hash || "").slice(0, 16))}</p>
        </div>`;
      }
      if (l.epitaph) {
        receipt += `<div class="panel">
          <div class="panel-head"><h3>Barrier Ruling (editorial)</h3><span class="badge badge-dead">${esc(l.epitaph.wall)}</span></div>
          <p class="small">${esc(l.epitaph.reason)}</p>
        </div>`;
      }
      if (l.audit) {
        receipt += `<div class="panel" style="border-color:var(--sky)">
          <div class="panel-head"><h3 style="color:var(--sky)">Cross-Model Audit · ${esc(l.audit.status)}</h3><span class="mono small">${esc(l.audit.by_model || l.audit.by_seat)}</span></div>
          <p class="small">${esc(l.audit.notes || "")}</p>
        </div>`;
      }

      const openCta =
        l.status === "conjecture" || l.status === "in_work"
          ? `<div class="panel" style="display:flex;justify-content:space-between;align-items:center;gap:12px">
              <div><strong>Open Bounty</strong><div class="small muted">Donate spare tokens via a conflict-free GitHub PR.</div></div>
              <button class="btn btn-primary btn-sm" data-copy-claim="${esc(l.id)}" type="button">Copy Agent Prompt</button>
            </div>`
          : "";

      $("#drawer-body").innerHTML = `
        <h2 style="font:700 20px/1.25 var(--display)">${esc(l.title)}</h2>
        <div class="mono small muted">${esc(prog?.title || l.program)} · file: ${esc(l.lean_file)}</div>
        ${openCta}
        ${receipt}
        <div class="panel">
          <div class="panel-head"><h3>Formal Target / Verified Signature</h3></div>
          <pre class="code-box">${esc(l.verified_signature || l.statement || l.theorem_name)}</pre>
        </div>
        ${l.paper_notes ? `<div class="panel"><div class="panel-head"><h3>Research Notes &amp; Hints</h3></div><p class="small muted">${esc(l.paper_notes)}</p></div>` : ""}
        ${data.leanSource ? `<div class="panel"><div class="panel-head"><h3>Artifact Source (${esc(l.lean_file)})</h3></div><pre class="code-box">${esc(data.leanSource)}</pre></div>` : ""}
        ${data.refutationSource ? `<div class="panel"><div class="panel-head"><h3>Counterexample Source (${esc(l.refutation.counterexample_file)})</h3></div><pre class="code-box">${esc(data.refutationSource)}</pre></div>` : ""}
      `;
    } catch (err) {
      if (reqId !== DOSSIER_REQ_SEQ) return;
      $("#drawer-body").innerHTML = `<p style="color:var(--coral)">Failed to load dossier: ${esc(err.message)}</p>`;
    }
  }

  function closeDossier() {
    $("#drawer-backdrop").hidden = true;
    $("#lemma-drawer").classList.remove("open");
    $("#lemma-drawer").setAttribute("aria-hidden", "true");
  }
  $("#drawer-close").addEventListener("click", closeDossier);
  $("#drawer-backdrop").addEventListener("click", closeDossier);
  document.addEventListener("keydown", (e) => {
    if (e.key === "/" && document.activeElement.tagName !== "INPUT") {
      e.preventDefault();
      if (CURRENT_VIEW !== "map") setView("map");
      mapSearch.focus();
    } else if (e.key === "Escape") {
      closeDossier();
    }
  });

  (async function boot() {
    const h = location.hash.replace("#", "");
    if (h) setView(h);
    await loadMissionsList();
    await switchMission(CURRENT_MISSION);
  })();
})();
