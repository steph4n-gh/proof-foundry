#!/usr/bin/env node
/**
 * hub/test_design_and_ui.mjs — Proceedings design-system guardrails + UI state machine tests.
 *
 *   1. Anti-slop contract on web/public/{style.css,index.html,app.js,ui_machine.js}
 *      (banned palettes/fonts/effects, tokens-only colour, radius & shadow rules, contrast).
 *   2. DOM wiring: every #id app.js references exists; data-nav/data-tab values are valid;
 *      every JS file parses; every import app.js takes from ui_machine.js is exported.
 *   3. web/public/ui_machine.js unit tests: routes & legacy aliases, strict single overlay,
 *      Esc, failed mission switch keeps the healthy stream, out-of-order reqSeq ignored,
 *      snapshot adapters against the real six-mission data.
 *
 * Zero dependencies. Run: node hub/test_design_and_ui.mjs
 */
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const PUB = path.join(ROOT, "web", "public");
const read = (f) => fs.readFileSync(path.join(PUB, f), "utf8");

let failed = 0;
let passed = 0;
function assert(cond, label, detail = "") {
  if (cond) {
    passed++;
    console.log(`PASS  ${label}`);
  } else {
    failed++;
    console.error(`FAIL  ${label}${detail ? ` -> ${detail}` : ""}`);
  }
}
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);

const CSS = read("style.css");
const HTML = read("index.html");
const APP = read("app.js");
const MACHINE_SRC = read("ui_machine.js");
const FILES = { "style.css": CSS, "index.html": HTML, "app.js": APP, "ui_machine.js": MACHINE_SRC };

// ===========================================================================
// 1. Anti-slop contract
// ===========================================================================
console.log("\n— Anti-slop design contract —");

const BANNED_HEXES = ["#38bdf8", "#22d3ee", "#10b981", "#c084fc", "#f43f5e", "#080d18"];
const BANNED_PATTERNS = [
  [/radial-gradient/i, "radial-gradient"],
  [/backdrop-filter/i, "backdrop-filter"],
  [/border-radius\s*:\s*9{2,}px/i, "border-radius: 99px pills"],
  [/\bInter\b/, "Inter font"],
  [/Space[\s+]Grotesk/i, "Space Grotesk font"],
  [/JetBrains/i, "JetBrains Mono (use IBM Plex Mono)"],
  [/conic-gradient/i, "conic-gradient"],
];
for (const [name, src] of Object.entries(FILES)) {
  const lower = src.toLowerCase();
  for (const hex of BANNED_HEXES) assert(!lower.includes(hex), `${name}: banned Tailwind hex ${hex} absent`);
  for (const [re, label] of BANNED_PATTERNS) assert(!re.test(src), `${name}: banned ${label} absent`, String(src.match(re)?.[0] || ""));
}

const stripComments = (s) => s.replace(/\/\*[\s\S]*?\*\//g, "");
const HEX_RE = /(^|[^&\w])#(?:[0-9a-fA-F]{8}|[0-9a-fA-F]{6}|[0-9a-fA-F]{3,4})\b/g;
const COLOR_FN_RE = /\b(?:rgba?|hsla?|hwb|lab|lch|oklab|oklch)\s*\(/gi;

// Extract token blocks (top-level `:root {…}` containing --bg and `[data-theme="dark"] {…}`).
function extractBlocks(css) {
  const rules = [];
  let depth = 0;
  let start = 0;
  let selStart = 0;
  for (let i = 0; i < css.length; i++) {
    const ch = css[i];
    if (ch === "{") {
      if (depth === 0) {
        start = i;
      }
      depth++;
    } else if (ch === "}") {
      depth--;
      if (depth === 0) {
        rules.push({ selector: css.slice(selStart, start).trim(), body: css.slice(start + 1, i), from: selStart, to: i + 1 });
        selStart = i + 1;
      }
    }
  }
  return rules;
}
const cssNoComments = stripComments(CSS);
const topRules = extractBlocks(cssNoComments);
const tokenRules = topRules.filter((r) => (r.selector === ":root" || r.selector === '[data-theme="dark"]') && /--bg\s*:/.test(r.body));
assert(tokenRules.length === 2, "style.css: exactly two colour token blocks (:root light + [data-theme=dark])", tokenRules.map((r) => r.selector).join(", "));

function tokensOf(body) {
  const out = {};
  for (const m of body.matchAll(/(--[\w-]+)\s*:\s*([^;]+);/g)) out[m[1]] = m[2].trim();
  return out;
}
const light = tokensOf(tokenRules.find((r) => r.selector === ":root")?.body || "");
const dark = tokensOf(tokenRules.find((r) => r.selector === '[data-theme="dark"]')?.body || "");
const SPEC_LIGHT = { "--bg": "#F5F2EA", "--surface": "#FBF9F4", "--ink": "#1A1916", "--muted": "#6E6A60", "--rule": "#D9D3C5", "--rule-strong": "#B8B09E", "--accent": "#8E2A1A", "--alarm": "#B4521A" };
const SPEC_DARK = { "--bg": "#0F0F0D", "--surface": "#181815", "--ink": "#E9E5D9", "--muted": "#8B8778", "--rule": "#2B2A25", "--rule-strong": "#3E3C35", "--accent": "#E0785F", "--alarm": "#FFC53D" };
for (const [k, v] of Object.entries(SPEC_LIGHT)) assert((light[k] || "").toUpperCase() === v, `light token ${k} = ${v}`, light[k]);
for (const [k, v] of Object.entries(SPEC_DARK)) assert((dark[k] || "").toUpperCase() === v, `dark token ${k} = ${v}`, dark[k]);
assert(eq(Object.keys(light).sort(), Object.keys(dark).sort()), "light and dark token blocks define the same token names", `${Object.keys(light)} vs ${Object.keys(dark)}`);

// Warm palette: no navy (blue channel never dominates) in either theme.
const rgb = (hex) => [1, 3, 5].map((i) => parseInt(hex.slice(i, i + 2), 16));
for (const [theme, toks] of [["light", light], ["dark", dark]]) {
  for (const [k, v] of Object.entries(toks)) {
    if (!/^#[0-9a-f]{6}$/i.test(v)) continue;
    const [r, , b] = rgb(v);
    assert(b <= r + 6, `${theme} ${k} ${v} is warm/neutral (no navy blue)`, `r=${r} b=${b}`);
  }
}

// WCAG contrast of the semantic roles.
const lum = (hex) => {
  const c = rgb(hex).map((v) => v / 255).map((v) => (v <= 0.03928 ? v / 12.92 : ((v + 0.055) / 1.055) ** 2.4));
  return 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
};
const contrast = (a, b) => {
  const x = lum(a);
  const y = lum(b);
  return (Math.max(x, y) + 0.05) / (Math.min(x, y) + 0.05);
};
for (const [theme, t] of [["light", light], ["dark", dark]]) {
  assert(contrast(t["--ink"], t["--bg"]) >= 7, `${theme}: ink on bg ≥ 7:1 (AAA)`, contrast(t["--ink"], t["--bg"]).toFixed(2));
  for (const role of ["--muted", "--accent", "--alarm"]) {
    for (const base of ["--bg", "--surface"]) {
      const c = contrast(t[role], t[base]);
      assert(c >= 4.5, `${theme}: ${role} on ${base} ≥ 4.5:1 (AA)`, c.toFixed(2));
    }
  }
  assert(contrast(t["--accent-ink"], t["--accent"]) >= 4.5, `${theme}: primary button label on accent ≥ 4.5:1`, contrast(t["--accent-ink"], t["--accent"]).toFixed(2));
}

// Raw colour literals only inside the token blocks.
let cssOutside = cssNoComments;
for (const r of [...tokenRules].sort((a, b) => b.from - a.from)) cssOutside = cssOutside.slice(0, r.from) + cssOutside.slice(r.to);
const strayCssHex = [...cssOutside.matchAll(HEX_RE)].map((m) => m[0].trim());
assert(strayCssHex.length === 0, "style.css: zero raw #hex outside the token blocks", strayCssHex.join(" "));
const strayCssFn = [...cssOutside.matchAll(COLOR_FN_RE)].map((m) => m[0]);
assert(strayCssFn.length === 0, "style.css: zero rgb()/hsl()/oklch() literals outside the token blocks", strayCssFn.join(" "));
const namedColors = [...cssOutside.matchAll(/(?:color|background|border(?:-\w+)?|fill|stroke|outline)\s*:\s*[^;]*\b(white|black|red|blue|green|gray|grey|navy|purple|orange|yellow|pink|cyan|teal)\b/gi)].map((m) => m[0]);
assert(namedColors.length === 0, "style.css: zero named CSS colours outside tokens", namedColors.join(" | "));

for (const name of ["index.html", "app.js", "ui_machine.js"]) {
  const src = name.endsWith(".html") ? FILES[name] : stripComments(FILES[name]);
  const hexes = [...src.matchAll(HEX_RE)].map((m) => m[0].trim());
  assert(hexes.length === 0, `${name}: zero raw #hex colour literals`, hexes.join(" "));
  const fns = [...src.matchAll(COLOR_FN_RE)].map((m) => m[0]);
  assert(fns.length === 0, `${name}: zero rgb()/hsl() colour literals`, fns.join(" "));
}

// Geometry: 0–2px radius everywhere; 50% only for the live dot.
const radii = [...cssNoComments.matchAll(/([^{}]*)\{([^{}]*)\}/g)].flatMap((m) =>
  [...m[2].matchAll(/border-radius\s*:\s*([^;]+);/g)].map((r) => ({ selector: m[1].trim(), value: r[1].trim() }))
);
assert(radii.length > 0, "style.css: border-radius declarations found for inspection");
for (const { selector, value } of radii) {
  const ok = /^(0|0px|1px|2px|1\.5px|var\(--radius\))$/.test(value) || (value === "50%" && /live-dot/.test(selector));
  assert(ok, `radius ${value} on ${selector.split("\n").pop()} is 0–2px (50% only for the live dot)`);
}
assert(/--radius\s*:\s*(0|1px|2px)\s*;/.test(cssNoComments), "style.css: --radius token is ≤ 2px");
assert(!/\brx="(?:[3-9]|\d{2,})/.test(APP), "app.js: SVG rects use rx ≤ 2");

// Shadows only on the dossier drawer and modal dialogs.
const shadowRules = [...cssNoComments.matchAll(/([^{}]*)\{([^{}]*)\}/g)].filter((m) => /(^|[;\s{])box-shadow\s*:/.test(m[2]));
for (const m of shadowRules) {
  const sel = m[1].trim();
  assert(/\.(drawer|modal)\b/.test(sel) && !/,/.test(sel.replace(/\.modal[\w.-]*|\.drawer[\w.-]*/g, "")), `box-shadow only on drawer/modal (found on "${sel}")`);
}
assert(shadowRules.length >= 2, "style.css: drawer and modal carry the only shadows", String(shadowRules.length));
assert(!/text-shadow\s*:/.test(cssNoComments), "style.css: no text-shadow glow");
assert(!/filter\s*:\s*drop-shadow/.test(cssNoComments), "style.css: no drop-shadow glow");

// No generic SaaS cards / KPI grids.
assert(!/\.[\w-]*(card|kpi)\b/i.test(cssNoComments), "style.css: no card/KPI component selectors");
assert(!/class="[^"]*\b[\w-]*(card|kpi)\b/i.test(HTML + APP), "index.html/app.js: no card/KPI classes in markup");

// Fonts: exactly Newsreader + Source Sans 3 + IBM Plex Mono from Google Fonts.
const fontHref = HTML.match(/href="(https:\/\/fonts\.googleapis\.com\/css2\?[^"]+)"/)?.[1] || "";
const families = [...fontHref.matchAll(/family=([^:&]+)/g)].map((m) => decodeURIComponent(m[1].replace(/\+/g, " "))).sort();
assert(eq(families, ["IBM Plex Mono", "Newsreader", "Source Sans 3"]), "index.html: Google Fonts = Newsreader, Source Sans 3, IBM Plex Mono only", families.join(", "));
assert(/--font-display\s*:\s*"Newsreader"/.test(CSS) && /--font-body\s*:\s*"Source Sans 3"/.test(CSS) && /--font-mono\s*:\s*"IBM Plex Mono"/.test(CSS), "style.css: font tokens map display/body/mono to the three families");
assert(/1\.5px solid var\(--ink\)/.test(CSS), "style.css: bold 1.5px masthead rule present");

// CSP: no inline scripts; app.js loaded as a module.
const scripts = [...HTML.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/g)];
assert(scripts.every((m) => /\bsrc=/.test(m[1]) && !m[2].trim()), "index.html: every <script> is external (CSP script-src 'self')");
assert(/<script type="module" src="\.\/app\.js"><\/script>/.test(HTML), "index.html: app.js is loaded as an ES module");
assert(!/\son[a-z]+=\s*"/i.test(HTML) && !/\son[a-z]+=\\?"/i.test(APP.replace(/\bon(open|error)\b/g, "")), "index.html/app.js: no inline on* event-handler attributes");

// Canvas reads every semantic token from CSS (no hard-coded palette in JS).
assert(/getComputedStyle\(document\.documentElement\)/.test(APP), "app.js: canvas reads tokens via getComputedStyle(document.documentElement)");
for (const t of ["--bg", "--surface", "--ink", "--muted", "--rule", "--accent", "--alarm"]) assert(APP.includes(`"${t}"`), `app.js: canvas token reader includes ${t}`);

// Status grammar glyphs + the "never double-chip a record" rule.
for (const g of ["○", "◐", "◇", "◆", "♛", "✕", "—", "⚠", "⛔"]) assert(MACHINE_SRC.includes(`"${g}"`), `ui_machine.js: status grammar defines glyph ${g}`);
assert(!/King of the Hill<\/span>[\s\S]{0,80}seal-record/.test(APP) && !APP.includes("frozenChip"), "app.js: no duplicated King-of-the-Hill chips on record rows");
assert(!/function\s+sealOf\s*\(/.test(APP), "app.js: no duplicated sealOf() (backend seal via ui_machine adapters)");

// ===========================================================================
// 2. DOM wiring & parsing
// ===========================================================================
console.log("\n— DOM wiring & parse checks —");

for (const f of ["app.js", "ui_machine.js"]) {
  const r = spawnSync(process.execPath, ["--check", path.join(PUB, f)], { encoding: "utf8" });
  assert(r.status === 0, `node --check web/public/${f}`, r.stderr);
}

const htmlIds = new Set([...HTML.matchAll(/\sid="([^"]+)"/g)].map((m) => m[1]));
const dupIds = [...HTML.matchAll(/\sid="([^"]+)"/g)].map((m) => m[1]).filter((id, i, a) => a.indexOf(id) !== i);
assert(dupIds.length === 0, "index.html: no duplicate ids", dupIds.join(", "));
const dynamicIds = new Set([...APP.matchAll(/\sid="([a-z][\w-]*)"/g)].map((m) => m[1]));
const dynamicIdPrefixes = [...APP.matchAll(/\sid="([a-z][\w-]*)\$\{/g)].map((m) => m[1]);

const staticRefs = new Set();
for (const m of APP.matchAll(/\$\$?\(\s*"#([A-Za-z][\w-]*)/g)) staticRefs.add(m[1]);
for (const m of APP.matchAll(/\$\$?\(\s*'#([A-Za-z][\w-]*)/g)) staticRefs.add(m[1]);
for (const m of APP.matchAll(/for \(const id of \[([^\]]+)\]\)/g)) for (const s of m[1].matchAll(/"#([\w-]+)"/g)) staticRefs.add(s[1]);
for (const m of APP.matchAll(/getElementById\(\s*"([\w-]+)"\s*\)/g)) staticRefs.add(m[1]);
assert(staticRefs.size > 60, `app.js: collected ${staticRefs.size} static #id references`);
const missing = [...staticRefs].filter((id) => !htmlIds.has(id) && !dynamicIds.has(id));
assert(missing.length === 0, "every $(\"#id\") in app.js exists in index.html or app.js markup", missing.join(", "));

const templRefs = [...APP.matchAll(/\$\(\s*`#([\w-]*)\$\{/g)].map((m) => m[1]);
for (const prefix of templRefs) assert([...htmlIds].some((id) => id.startsWith(prefix)), `templated selector #${prefix}\${…} matches index.html ids`);
for (const prefix of [...APP.matchAll(/getElementById\(`([\w-]+)\$\{/g)].map((m) => m[1])) {
  assert(dynamicIdPrefixes.includes(prefix), `templated getElementById ${prefix}\${…} matches generated markup`);
}
for (const v of ["missions", "records", "control", "bounties", "ledger"]) assert(htmlIds.has(`view-${v}`), `index.html: #view-${v} section exists`);
for (const t of ["map", "leaderboard", "refutations", "fleet", "audit"]) assert(htmlIds.has(`tab-${t}`), `index.html: #tab-${t} panel exists`);

const mod = await import(pathToFileURL(path.join(PUB, "ui_machine.js")).href);
const importBlock = APP.match(/import\s*\{([\s\S]*?)\}\s*from\s*"\.\/ui_machine\.js"/)?.[1] || "";
const importedNames = importBlock.split(",").map((s) => s.trim()).filter(Boolean);
assert(importedNames.length > 10, `app.js imports ${importedNames.length} names from ui_machine.js`);
for (const n of importedNames) assert(n in mod, `ui_machine.js exports ${n}`);

for (const m of (HTML + APP).matchAll(/data-nav="([\w-]+)"/g)) assert(mod.VIEWS.includes(m[1]), `data-nav="${m[1]}" is a valid view`);
for (const m of HTML.matchAll(/data-tab="([\w-]+)"/g)) assert(mod.LEDGER_TABS.includes(m[1]), `data-tab="${m[1]}" is a valid ledger tab`);
for (const m of HTML.matchAll(/data-harness="([\w-]+)"/g)) assert(mod.HARNESSES.includes(m[1]), `data-harness="${m[1]}" is a known harness`);
assert(!/\b(window|document|fetch|EventSource|localStorage)\b\s*[.(]/.test(stripComments(MACHINE_SRC).replace(/"[^"]*"/g, "")), "ui_machine.js: pure (no window/document/fetch/EventSource/localStorage)");
assert(!/^\s*import\b/m.test(MACHINE_SRC), "ui_machine.js: zero imports (zero dependencies)");

// ===========================================================================
// 3. ui_machine.js unit tests
// ===========================================================================
console.log("\n— UI state machine —");
const {
  initialUIState,
  reduceUI,
  createUIMachine,
  parseRouteFromLocation: parse,
  serializeRouteToLocation: serialize,
  acceptsSnapshot,
  isCurrentMissionRequest,
  VIEWS,
  LEDGER_TABS,
} = mod;

// --- routes
const P = (hash, search = "") => parse({ hash, search }, { defaultMission: "erdos-combinatorics" });
for (const v of VIEWS) assert(P(`#${v}`).view === v, `route #${v} → view ${v}`);
for (const t of LEDGER_TABS) assert(eq(P(`#ledger/${t}`), { view: "ledger", ledgerTab: t, mission: "erdos-combinatorics", claim: null }), `route #ledger/${t} → ledger/${t}`);
const ALIASES = { live: "fleet", map: "map", leaderboard: "leaderboard", graveyard: "refutations", feed: "audit" };
for (const [h, tab] of Object.entries(ALIASES)) {
  const r = P(`#${h}`, "?mission=p-vs-np");
  assert(r.view === "ledger" && r.ledgerTab === tab && r.mission === "p-vs-np", `legacy alias #${h} → ledger/${tab}`, JSON.stringify(r));
}
assert(P("", "?mission=sorting-networks").view === "control", "no hash + ?mission → control (v2 deep links)");
assert(P("", "").view === "missions", "no hash, no mission → missions");
assert(P("#does-not-exist").view === "missions", "unknown hash → missions");
assert(P("#ledger/bogus").ledgerTab === "map", "unknown ledger tab → map");
assert(P("#LEDGER/Audit").ledgerTab === "audit", "hash parsing is case-insensitive");
assert(P("#/records").view === "records", "#/records (slash form) accepted");
assert(P("#records", "?mission=../../etc").mission === "erdos-combinatorics", "malicious mission slug rejected → default");
assert(P("#bounties", "?claim=<script>alert(1)</script>").claim === null, "malicious claim id rejected");
assert(P("#control", "?mission=p-vs-np&claim=L-rec-005").claim === "L-rec-005", "claim param parsed");
for (const view of VIEWS) {
  for (const tab of view === "ledger" ? LEDGER_TABS : ["map"]) {
    for (const claim of [null, "E-ram-001"]) {
      const route = { view, ledgerTab: tab, mission: "fast-matrix-mul", claim };
      const url = serialize(route, { pathname: "/" });
      const [pathAndSearch, hash] = url.split("#");
      const back = parse({ hash: `#${hash}`, search: pathAndSearch.slice(1) }, { defaultMission: "x" });
      assert(eq(back, route), `serialize ⇄ parse round-trip ${url}`, JSON.stringify(back));
    }
  }
}
assert(serialize({ view: "ledger", ledgerTab: "audit", mission: "p-vs-np" }, { pathname: "/pf/" }) === "/pf/?mission=p-vs-np#ledger/audit", "serialize keeps pathname (GitHub Pages subpath)");

// --- overlays: strictly one at a time
const base = () => {
  let s = initialUIState({ route: { view: "control", mission: "erdos-combinatorics" } });
  s = reduceUI(s, { type: "CATALOG_LOADED", mode: "live" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics" });
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: s.transport.reqSeq });
  return reduceUI(s, { type: "SSE_OPEN", mission: "erdos-combinatorics" });
};
const OPENERS = {
  dossier: { type: "OPEN_DOSSIER", claimId: "E-ram-001", mission: "erdos-combinatorics" },
  attempt: { type: "OPEN_ATTEMPT", claimId: "E-rec-r55", mission: "erdos-combinatorics", harness: "codex", handle: "ada", recKind: "record", recScore: 43 },
  search: { type: "OPEN_SEARCH", query: "ramsey" },
};
for (const [a, evA] of Object.entries(OPENERS)) {
  for (const [b, evB] of Object.entries(OPENERS)) {
    const s = reduceUI(reduceUI(base(), evA), evB);
    assert(s.overlay.kind === b, `open ${a} then ${b} → only ${b} is open`, s.overlay.kind);
  }
}
{
  let s = reduceUI(base(), OPENERS.dossier);
  assert(s.route.claim === "E-ram-001", "dossier mirrors claim into route");
  s = reduceUI(s, OPENERS.search);
  assert(s.overlay.kind === "search" && s.route.claim === null, "opening search closes the dossier and clears route.claim");
  s = reduceUI(s, OPENERS.attempt);
  assert(s.overlay.kind === "attempt" && s.overlay.claimId === "E-rec-r55" && s.overlay.harness === "codex", "opening attempt closes search");
  s = reduceUI(s, { type: "ESCAPE" });
  assert(s.overlay.kind === "none", "Esc closes the topmost (only) overlay");
  const same = reduceUI(s, { type: "ESCAPE" });
  assert(same === s, "Esc with nothing open is a no-op (same state reference)");
  s = reduceUI(s, OPENERS.dossier);
  s = reduceUI(s, { type: "ESCAPE" });
  assert(s.overlay.kind === "none" && s.route.claim === null, "Esc on dossier clears route.claim");
}
{
  let s = reduceUI(base(), OPENERS.attempt);
  s = reduceUI(s, { type: "ATTEMPT_UPDATE", patch: { harness: "gemini", handle: "x".repeat(80), recKind: "record_bound", recScore: "40" } });
  assert(s.overlay.harness === "gemini" && s.overlay.handle.length === 39 && s.overlay.recKind === "record_bound" && s.overlay.recScore === "40", "ATTEMPT_UPDATE patches harness/handle (clamped)/recKind/recScore");
  const before = s;
  s = reduceUI(s, { type: "ATTEMPT_UPDATE", patch: { harness: "netscape" } });
  assert(s === before, "ATTEMPT_UPDATE with unknown harness is ignored");
  assert(reduceUI(reduceUI(base(), OPENERS.search), { type: "ATTEMPT_UPDATE", patch: { handle: "z" } }).overlay.kind === "search", "ATTEMPT_UPDATE ignored when attempt is not open");
  assert(reduceUI(base(), { type: "OPEN_DOSSIER", claimId: "<img onerror>" }).overlay.kind === "none", "OPEN_DOSSIER with invalid id is rejected");
}
{
  let s = reduceUI(base(), OPENERS.search);
  s = reduceUI(s, { type: "SEARCH_MOVE", delta: -1, count: 5 });
  assert(s.overlay.activeIndex === 4, "SEARCH_MOVE wraps upward");
  s = reduceUI(s, { type: "SEARCH_MOVE", delta: 1, count: 5 });
  assert(s.overlay.activeIndex === 0, "SEARCH_MOVE wraps downward");
  s = reduceUI(reduceUI(s, { type: "SEARCH_MOVE", delta: 3, count: 5 }), { type: "SEARCH_QUERY", query: "golomb" });
  assert(s.overlay.query === "golomb" && s.overlay.activeIndex === 0, "SEARCH_QUERY resets the active index");
}

// --- dossier reqSeq: out-of-order responses ignored
{
  let s = reduceUI(base(), OPENERS.dossier);
  const seqA = s.overlay.reqSeq;
  s = reduceUI(s, { type: "OPEN_DOSSIER", claimId: "E-ram-002", mission: "erdos-combinatorics" });
  const seqB = s.overlay.reqSeq;
  assert(seqB === seqA + 1, "dossier reqSeq increments monotonically");
  const stale = reduceUI(s, { type: "DOSSIER_LOADED", reqSeq: seqA, data: { lemma: { id: "E-ram-001" } } });
  assert(stale === s && s.overlay.status === "loading", "stale DOSSIER_LOADED (older reqSeq) is ignored");
  s = reduceUI(s, { type: "DOSSIER_LOADED", reqSeq: seqB, data: { lemma: { id: "E-ram-002" } } });
  assert(s.overlay.status === "ready" && s.overlay.data.lemma.id === "E-ram-002", "current DOSSIER_LOADED commits");
  s = reduceUI(s, { type: "CLOSE_OVERLAY" });
  s = reduceUI(s, OPENERS.dossier);
  assert(s.overlay.reqSeq === seqB + 1, "reopening after close never reuses a sequence number");
  assert(reduceUI(s, { type: "DOSSIER_FAILED", reqSeq: seqB, error: "late" }) === s, "late DOSSIER_FAILED from a closed dossier is ignored");
  const closed = reduceUI(s, { type: "CLOSE_OVERLAY" });
  assert(reduceUI(closed, { type: "DOSSIER_LOADED", reqSeq: s.overlay.reqSeq, data: {} }) === closed, "DOSSIER_LOADED after close is ignored (drawer stays closed)");
  const err = reduceUI(s, { type: "DOSSIER_FAILED", reqSeq: s.overlay.reqSeq, error: "HTTP 404" });
  assert(err.overlay.status === "error" && err.overlay.error === "HTTP 404", "current DOSSIER_FAILED moves the dossier to error");
}

// --- transport
{
  let s = initialUIState();
  assert(s.transport.status === "boot" && s.overlay.kind === "none", "initial: transport boot, no overlay");
  s = reduceUI(s, { type: "CATALOG_LOADED", mode: "live" });
  assert(s.transport.status === "live_connecting" && s.transport.mode === "live", "catalog (live) → live_connecting");
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "erdos-combinatorics", intent: { view: "records" } });
  const s1 = s.transport.reqSeq;
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "erdos-combinatorics", reqSeq: s1 });
  assert(s.transport.activeMission === "erdos-combinatorics" && s.route.mission === "erdos-combinatorics" && s.route.view === "records", "MISSION_LOADED commits mission and applies intent view");
  s = reduceUI(s, { type: "SSE_OPEN", mission: "erdos-combinatorics" });
  assert(s.transport.status === "live_connected", "SSE_OPEN → live_connected");
  s = reduceUI(s, { type: "SSE_ERROR", mission: "erdos-combinatorics" });
  assert(s.transport.status === "live_reconnecting", "SSE_ERROR → live_reconnecting");
  s = reduceUI(s, { type: "SSE_SNAPSHOT", mission: "erdos-combinatorics" });
  assert(s.transport.status === "live_connected", "SSE_SNAPSHOT after reconnect → live_connected");

  // Failed switch keeps the healthy stream of the committed mission.
  const healthy = s;
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "control" } });
  assert(s.transport.status === "live_connected" && s.transport.activeMission === "erdos-combinatorics" && s.transport.pendingMission === "p-vs-np", "switch in flight: still live_connected on the old mission");
  const s2 = s.transport.reqSeq;
  s = reduceUI(s, { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: s2, error: "HTTP 500" });
  assert(s.transport.status === "live_connected", "failed switch: status stays live_connected (stream not killed)");
  assert(s.transport.activeMission === "erdos-combinatorics" && s.route.mission === "erdos-combinatorics" && s.route.view === healthy.route.view, "failed switch: active mission, route mission and view unchanged");
  assert(s.transport.error === "HTTP 500" && s.transport.pendingMission === null, "failed switch: error surfaced, pending cleared");
  assert(acceptsSnapshot(s, "erdos-combinatorics") && !acceptsSnapshot(s, "p-vs-np"), "failed switch: old mission's SSE snapshots still accepted");
  s = reduceUI(s, { type: "SSE_SNAPSHOT", mission: "erdos-combinatorics" });
  assert(s.transport.status === "live_connected", "old stream keeps flowing after the failed switch");
  s = reduceUI(s, { type: "DISMISS_ERROR" });
  assert(s.transport.error === null, "DISMISS_ERROR clears the banner");

  // Out-of-order mission responses.
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np" });
  const sB = s.transport.reqSeq;
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "sorting-networks", intent: { view: "ledger", ledgerTab: "fleet" } });
  const sC = s.transport.reqSeq;
  assert(isCurrentMissionRequest(s, sC) && !isCurrentMissionRequest(s, sB), "isCurrentMissionRequest tracks only the latest request");
  const ignored = reduceUI(s, { type: "MISSION_LOADED", mission: "p-vs-np", reqSeq: sB });
  assert(ignored === s, "late MISSION_LOADED for a superseded request is ignored");
  assert(reduceUI(s, { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: sB, error: "late" }) === s, "late MISSION_FAILED for a superseded request is ignored");
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "sorting-networks", reqSeq: sC });
  assert(s.transport.activeMission === "sorting-networks" && s.route.view === "ledger" && s.route.ledgerTab === "fleet" && s.transport.status === "live_connecting", "latest MISSION_LOADED commits with its intent; new stream connecting");
  assert(reduceUI(s, { type: "SSE_SNAPSHOT", mission: "erdos-combinatorics" }) === s, "SSE events from the previous mission's stream are ignored");
  assert(!acceptsSnapshot(s, "erdos-combinatorics") && acceptsSnapshot(s, "sorting-networks"), "acceptsSnapshot follows the committed mission");
}
{
  let s = reduceUI(initialUIState(), { type: "CATALOG_LOADED", mode: "live" });
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np" });
  s = reduceUI(s, { type: "MISSION_FAILED", mission: "p-vs-np", reqSeq: s.transport.reqSeq, error: "boom" });
  assert(s.transport.status === "error", "first mission load failing (nothing committed) → error");
  s = reduceUI(s, { type: "RETRY" });
  assert(s.transport.status === "boot" && s.transport.error === null, "RETRY from error → boot");
  let f = reduceUI(initialUIState(), { type: "CATALOG_FAILED", error: "offline" });
  assert(f.transport.status === "error" && f.transport.error === "offline", "CATALOG_FAILED → error");
}
{
  let s = reduceUI(initialUIState(), { type: "CATALOG_LOADED", mode: "static" });
  assert(s.transport.status === "static_loading", "catalog (static) → static_loading");
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "fast-matrix-mul" });
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "fast-matrix-mul", reqSeq: s.transport.reqSeq });
  assert(s.transport.status === "static_ready", "static mission load → static_ready");
  assert(reduceUI(s, { type: "SSE_OPEN", mission: "fast-matrix-mul" }) === s && !acceptsSnapshot(s, "fast-matrix-mul"), "static mode ignores SSE entirely");
}
{
  // A committed switch closes a dossier bound to the old mission; intent deep-links a claim.
  let s = reduceUI(base(), OPENERS.dossier);
  s = reduceUI(s, { type: "MISSION_REQUESTED", mission: "p-vs-np", intent: { view: "control", claim: "L-rec-005" } });
  assert(s.overlay.kind === "dossier", "dossier stays open while a switch is in flight");
  s = reduceUI(s, { type: "MISSION_LOADED", mission: "p-vs-np", reqSeq: s.transport.reqSeq });
  assert(s.overlay.kind === "none" && s.route.claim === "L-rec-005" && s.route.mission === "p-vs-np", "committed switch closes old-mission dossier and carries the deep-linked claim");
  s = reduceUI(s, { type: "ROUTE_SYNC", route: { view: "bounties", mission: "erdos-combinatorics", claim: null } });
  assert(s.route.view === "bounties" && s.route.mission === "p-vs-np", "ROUTE_SYNC never moves the mission (only MISSION_LOADED does)");
  s = reduceUI(s, { type: "ROUTE_NAVIGATE", route: { view: "ledger", ledgerTab: "refutations" } });
  assert(s.route.view === "ledger" && s.route.ledgerTab === "refutations", "ROUTE_NAVIGATE moves view/tab");
  const nav2 = reduceUI(s, { type: "ROUTE_NAVIGATE", route: { view: "ledger", ledgerTab: "refutations" } });
  assert(nav2 === s, "navigating to the current route is a no-op");
  s = reduceUI(s, { type: "OPEN_DOSSIER", claimId: "L-001", mission: "p-vs-np" });
  s = reduceUI(s, { type: "ROUTE_SYNC", route: { view: "ledger", ledgerTab: "refutations", claim: null } });
  assert(s.overlay.kind === "none", "history back to a claim-less URL closes the dossier");
  s = reduceUI(s, { type: "OPEN_DOSSIER", claimId: "E-rec-r55", mission: "erdos-combinatorics" });
  assert(s.overlay.kind === "dossier" && s.route.claim === null, "cross-mission dossier opens without writing a foreign claim into the URL");
}
{
  const m = createUIMachine(initialUIState());
  const seen = [];
  m.subscribe(() => {
    throw new Error("listener crash");
  });
  m.subscribe((next, prev, ev) => seen.push([ev.type, prev.overlay.kind, next.overlay.kind]));
  const origErr = console.error;
  console.error = () => {};
  m.dispatch({ type: "OPEN_SEARCH" });
  m.dispatch({ type: "ESCAPE" });
  m.dispatch({ type: "ESCAPE" }); // no-op: no notification
  m.dispatch({ type: "NOT_A_REAL_EVENT" });
  console.error = origErr;
  assert(eq(seen, [["OPEN_SEARCH", "none", "search"], ["ESCAPE", "search", "none"]]), "createUIMachine notifies only on change and survives a throwing listener", JSON.stringify(seen));
}

// --- adapters against the real six missions
console.log("\n— Snapshot adapters (real mission data) —");
{
  const { sealOf, statusOf, actionsOf, recordMetaOf, freshnessOf, prStateOf, normalizeRecordsPayload, synthesizeRecordsPayload, sortRecords, pickHotRecords, boundIntervalGeometry, ratchetSeries, computeGap, mergeSnapshotIntoRecords, toRoman } = mod;

  assert(sealOf({ status: "checked", seal: "flagged", audit: { status: "faithful" } }) === "flagged", "sealOf trusts backend lemma.seal over local derivation");
  assert(sealOf({ status: "checked", checker: { statement_frozen: true } }) === "frozen", "sealOf minimal fallback for older snapshots");
  assert(actionsOf({ status: "checked", actions: { can_attempt: true, can_bound: false, can_refute: false, can_audit: false, reason: null } }).can_attempt === true, "actionsOf trusts backend lemma.actions");
  assert(actionsOf({ status: "refuted" }).can_attempt === false && actionsOf({ status: "conjecture" }).can_attempt === true, "actionsOf fallback: open vs settled");
  assert(freshnessOf({ freshness: "stale_core" }) === "stale_core" && freshnessOf({}) === "fresh", "freshnessOf reads lemma.freshness");
  assert(prStateOf({ pr_state: "needs_fix" }) === "needs_fix" && prStateOf({ open_prs: [{ number: 3 }] }) === "open" && prStateOf({}) === "none", "prStateOf reads lemma.pr_state with safe fallback");
  const projected = recordMetaOf({ kind: "record", record: { direction: "min", start_target: 50 }, record_state: {}, record_meta: { direction: "min", op: "≤", best_score: 45, next_target: 44, gap: 2, closed: false, contradiction: false, allow_bound: true } });
  assert(projected.best_score === 45 && projected.gap === 2 && projected.next_target === 44, "recordMetaOf prefers backend record_meta");
  const minFb = recordMetaOf({ kind: "record", record: { direction: "min", start_target: 46, literature_lower_bound: 43, bound_floor: 42 }, record_state: { best: { score: 45, seat: "s" }, next_target: 44 } });
  assert(minFb.gap === 2 && minFb.op === "≤", "fallback gap (min) = best − lower bound", JSON.stringify(minFb.gap));
  const maxFb = recordMetaOf({ kind: "record", record: { direction: "max", start_target: 36, literature_upper_bound: 47 }, record_state: { refuted: { score: 47, inclusive_bound: 46 } } });
  assert(maxFb.gap === 10 && maxFb.op === "≥" && maxFb.proven_bound === 46 && maxFb.refuted_score === 47, "fallback gap (max) = proven upper bound − launch", JSON.stringify([maxFb.gap, maxFb.proven_bound]));
  assert(computeGap({ closed: true, direction: "min", best_score: 9, proven_bound: 9 }) === 0, "closed hunt has zero gap");

  const S = (lemma) => statusOf(lemma);
  assert(S({ status: "refuted" }).tone === "ink" && S({ status: "refuted" }).glyph === "✕", "refuted renders ✕ in plain ink (not alarm)");
  assert(S({ status: "dead" }).tone === "struck" && S({ status: "dead" }).glyph === "—", "barrier renders — muted, struck");
  assert(S({ status: "checked", seal: "flagged" }).tone === "alarm" && S({ seal: "contradiction" }).glyph === "⛔", "flagged/contradiction carry the alarm hue");
  assert(S({ status: "checked", seal: "frozen" }).tone === "accent" && S({ status: "checked", seal: "audited" }).glyph === "◆", "frozen/audited render ◆ accent");
  assert(S({ status: "checked", seal: "provisional" }).glyph === "◇" && S({ status: "in_work", seal: "in_work" }).glyph === "◐" && S({ status: "conjecture" }).glyph === "○", "provisional ◇ · in work ◐ · open ○");
  const recLive = S({ kind: "record", seal: "record", record: { direction: "min" }, record_state: { best: { score: 45 }, next_target: 44 } });
  assert(recLive.glyph === "♛" && recLive.tone === "accent" && /45/.test(recLive.label) && /44/.test(recLive.label), "live record: single ♛ accent chip with score and next target", recLive.label);
  assert(toRoman(6) === "VI" && toRoman(4) === "IV" && toRoman(9) === "IX", "Roman numerals for the ToC");
  assert(normalizeRecordsPayload(null) === null && normalizeRecordsPayload({ records: "nope" }) === null, "normalizeRecordsPayload rejects malformed payloads (e.g. index.html fallbacks)");

  let snaps = [];
  let catalog = [];
  try {
    const missions = await import(pathToFileURL(path.join(ROOT, "hub", "missions.mjs")).href);
    const site = await import(pathToFileURL(path.join(ROOT, "hub", "build_site.mjs")).href);
    catalog = missions.loadAllMissionsSummary();
    snaps = missions.listMissionSlugs().map((slug) => site.buildMissionSnapshot(missions.loadMission(slug), null));
  } catch (err) {
    assert(false, "load real mission snapshots", err.message);
  }
  assert(snaps.length === 6 && catalog.length === 6, "six missions load", `${snaps.length}/${catalog.length}`);
  const expectedRecords = snaps.reduce((a, s) => a + s.lemmas.filter((l) => l.kind === "record").length, 0);
  const synth = synthesizeRecordsPayload(snaps, catalog);
  assert(synth.records.length === expectedRecords && expectedRecords >= 18, `synthesized records board has all ${expectedRecords} King-of-the-Hill hunts`, String(synth.records.length));
  assert(new Set(synth.records.map((r) => r.mission)).size === 6, "records span all six missions");
  assert(synth.latest_verified && synth.latest_verified.id && synth.latest_verified.statement, "synthesized latest_verified theorem for the masthead", JSON.stringify(synth.latest_verified?.id));
  assert(synth.totals.missions === 6 && synth.totals.checked_total > 0, "synthesized totals for the figure sentence", JSON.stringify(synth.totals));
  for (const r of synth.records) {
    const g = boundIntervalGeometry(r);
    const inside = (v) => v == null || (v >= 0 && v <= 100);
    assert(g && inside(g.currentPct) && inside(g.boundPct) && inside(g.literaturePct) && inside(g.gapLeftPct) && (g.gapWidthPct == null || g.gapLeftPct + g.gapWidthPct <= 100.01), `${r.id}: bound-interval bar geometry within the track`, JSON.stringify(g));
    assert(r.gap == null || r.gap >= 0, `${r.id}: gap is non-negative`);
    assert(Array.isArray(ratchetSeries(r)), `${r.id}: ratchet series renders (baseline when unclaimed)`);
  }
  const sorted = sortRecords(synth.records, "gap").filter((r) => r.gap != null);
  assert(sorted.every((r, i) => i === 0 || sorted[i - 1].gap <= r.gap), "sortRecords('gap') orders by smallest open gap");
  assert(pickHotRecords(synth.records, 5).length === Math.min(5, expectedRecords), "pickHotRecords returns the 5 hottest hunts");
  const byMission = sortRecords(synth.records, "mission");
  assert(byMission.every((r, i) => i === 0 || byMission[i - 1].mission <= r.mission), "sortRecords('mission') groups by mission");
  const normalized = normalizeRecordsPayload({ records: synth.records, totals: synth.totals, latest_verified: synth.latest_verified });
  assert(normalized && normalized.records.length === expectedRecords && !normalized.synthesized, "records.json-shaped payload normalizes losslessly");
  const merged = mergeSnapshotIntoRecords(normalized, snaps[0]);
  assert(merged.records.length === expectedRecords, "merging a fresh mission snapshot keeps every row exactly once");
  for (const snap of snaps) {
    for (const l of snap.lemmas) {
      const st = statusOf(l);
      if (!st.glyph || !st.label) {
        assert(false, `${l.id}: status grammar resolves`);
      }
    }
  }
  assert(true, `status grammar resolves for all ${snaps.reduce((a, s) => a + s.lemmas.length, 0)} claims`);
}

console.log(`\n${passed} passed, ${failed} failed`);
if (failed > 0) {
  console.error(`\n${failed} design/UI test(s) failed!`);
  process.exit(1);
}
console.log("ALL PROCEEDINGS DESIGN-CONTRACT & UI STATE-MACHINE TESTS PASSED!");
