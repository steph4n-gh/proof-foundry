# Proof Foundry Design System — "Proceedings"

Proof Foundry is a **public ledger of machine-checked mathematics**. The interface should read like
a permanent scientific record — *Annals of Mathematics*, Distill, the Stacks Project — that happens
to update live. It is **not** a SaaS dashboard.

- **Paper** (default, light): warm rag paper, archival ink, oxblood accent.
- **Night** (`[data-theme="dark"]`): "Bench Instrument" — warm graphite, terracotta signal, amber alarm. Never navy.

Everything in this document is enforced by `hub/test_design_and_ui.mjs`. If a rule here and the
test disagree, fix the test *and* this document in the same change.

---

## 1. Colour tokens

Raw colour literals (`#hex`, `rgb()`, `hsl()`, named colours) may appear **only** inside the two token
blocks at the top of `web/public/style.css`. Every other rule, all of `index.html`, `app.js` and
`ui_machine.js` reference tokens (`var(--accent)`), and canvas code reads them with
`getComputedStyle(document.documentElement)`.

| Token | Paper | Night | Role |
|---|---|---|---|
| `--bg` | `#F5F2EA` | `#0F0F0D` | Page (rag paper / graphite) |
| `--surface` | `#FBF9F4` | `#181815` | Elevated sheet: Lean blocks, drawer, modal |
| `--ink` | `#1A1916` | `#E9E5D9` | Text, rules that matter, refutations |
| `--muted` | `#6E6A60` | `#8B8778` | Marginalia, secondary text, open problems |
| `--rule` | `#D9D3C5` | `#2B2A25` | 1px hairline between rows/sections |
| `--rule-strong` | `#B8B09E` | `#3E3C35` | Section-head rules, inputs, bar tracks |
| `--accent` | `#8E2A1A` oxblood | `#E0785F` terracotta | **Only** verified results, live records, the one primary action per view |
| `--alarm` | `#B4521A` burnt orange | `#FFC53D` amber | **Only** flagged, contradiction, PR needs fix |

Surface tints (also token-only): `--accent-ink` (label on an accent button), `--hover`,
`--accent-tint`, `--alarm-tint`, `--scrim`, `--shadow`.

Contrast (tested): ink on bg ≥ 7:1; muted, accent and alarm on bg and surface ≥ 4.5:1, in both themes.

**Two hues, no more.** If you want a third colour to tell states apart, use a **shape** (§3) instead.

## 2. Typography

| Role | Family | Use |
|---|---|---|
| Display | **Newsreader** (optical size; *italic* for theorem labels & mission questions) | Theorem titles, view titles, section heads, large tabular figures |
| Body / UI | **Source Sans 3** | Prose, controls, tables |
| Code | **IBM Plex Mono** | Lean statements, IDs, hashes, bounds, seats |

- Figures use `font-variant-numeric: tabular-nums lining-nums`.
- Eyebrows are 11–12px, uppercase, `letter-spacing: .12–.14em`, muted.
- Section heads are numbered `§1`, `§2`… in muted italic Newsreader; missions are numbered with Roman numerals `I.`–`VI.`.

## 3. Shape-first status grammar

Shape carries meaning; colour only confirms it. Rendered by `statusOf()` in `web/public/ui_machine.js`
— never re-implement it in a view.

| State | Glyph | Tone | Notes |
|---|---|---|---|
| open | ○ | muted | |
| in_work | ◐ | ink | |
| provisional | ◇ | ink | kernel-checked, awaiting audit |
| frozen / audited | ◆ | **accent** | label says *Frozen* or *Audited* |
| record (live) | ♛ | **accent** | one chip: "Record 45 · next ≤ 44". **Never** add a second King-of-the-Hill chip |
| open hunt (unclaimed) | ♛ | ink | "Open hunt · ≤ 46" |
| closed record | ◆ | accent | "Optimal" |
| refuted | ✕ | **ink** | A counterexample is a valid result, not an error. Never alarm |
| dead / barrier | — | muted, struck | |
| flagged | ⚠ | **alarm**, 1px outline box | excluded from objectives |
| contradiction | ⛔ | **alarm**, 1px outline box | halted |

Secondary flags come from backend projection fields: `freshness` (`↻ stale statement` / `↻ stale core`,
muted) and `pr_state` (`PR #n · open|passing` muted; `needs fix` alarm).

## 4. Geometry & layout

- **Radius 0–2px everywhere** (`--radius: 2px`). The only circle is the 7px live dot (`50%`).
- **Hairlines, not boxes.** Separate rows and sections with `1px var(--rule)`; section heads sit on
  `1px var(--rule-strong)`; mastheads and view heads close with a bold **1.5px ink** rule.
- **Shadows only** on the dossier drawer and modal dialogs (`--shadow`). Nothing else floats.
- No cards, no cards inside cards, no KPI tile grids. Counts are one **figure sentence**:
  "34 checked · 4 refuted · 18 live records · 6 missions".
- One primary (accent-filled) button per view. Everything else is an underlined text action
  (`Attempt →`) or a hairline button.
- Content width `--wrap: 1160px`, gutter 28px (20px under 860px). No horizontal page scroll at 390px.
- Motion: ≤ 220ms fades/slides on overlays only; disabled under `prefers-reduced-motion`.

## 5. Information architecture

Topbar: live dot + **PROOF FOUNDRY** wordmark · `Missions · Records (n) · Bounties · Ledger` · ⌘K search · Paper/Night.
GitHub, PROOFS.md and Judge status live in the footer.

1. **Missions** — masthead (latest kernel-checked theorem, Lean block with 2px accent rule,
   attribution), figure sentence + *Take an open problem →*; §1 five hottest record hunts;
   §2 numbered table of contents with rung strips; §3 three-column colophon.
2. **Records** — every King-of-the-Hill hunt: ID · problem & mission · best/target figure ·
   **bound-interval bar** (proven/literature bound tick ↔ best/launch tick, hatched open gap,
   literature-best marker ▴) · ratchet sparkline · *Attempt →*.
3. **Mission control** — breadcrumb + switcher, italic question, marginalia Judge metadata,
   §1 **true vertical rung ladders** (1px spine, ◆/○ rungs), §2 records, §3 open problems,
   §4 strategy note | recent receipts.
4. **Bounties** — Open problems / Full ledger; dense rows that expand to the frozen Lean statement.
5. **Ledger** — sub-tabs: Proof map & DAG, Leaderboard, Refutations & barriers, Fleet, Audit log.

Overlays (exactly one at a time): Verification **dossier** drawer, **Attempt** modal, ⌘K **search**.

## 6. State machine contract

`web/public/ui_machine.js` is a pure, zero-dependency ES module shared by the browser and Node tests.

- `transport`: `boot → live_connecting → live_connected ⇄ live_reconnecting`, or
  `boot → static_loading → static_ready`; `error` only while nothing is committed.
  A failed mission switch keeps the previous mission's healthy stream; stale `reqSeq` responses are dropped.
- `route`: `{ view, ledgerTab, mission, claim }` ⇄ `?mission=…&claim=…#view[/tab]`.
  Legacy hashes `#live #map #leaderboard #graveyard #feed` resolve to Ledger tabs and are canonicalised.
- `overlay`: `none | dossier | attempt | search` — opening any overlay replaces the open one; Esc closes it.

Views consume the backend projection (`lemma.seal`, `freshness`, `pr_state`, `actions`, `record_meta`)
through the adapters (`sealOf`, `freshnessOf`, `prStateOf`, `actionsOf`, `recordMetaOf`), which fall back
minimally only for older snapshots. Do not add new seal/record logic to `app.js`.

## 7. Banned

`Inter`, `Space Grotesk`, JetBrains Mono · Tailwind palette literals (`#38bdf8 #22d3ee #10b981 #c084fc
#f43f5e #080d18`) · navy backgrounds · `radial-gradient`, `conic-gradient`, glows, `text-shadow`,
`drop-shadow` · `backdrop-filter` · `border-radius: 99px` pills or any radius > 2px · card/KPI
components · double record chips · inline `<script>` (CSP is `script-src 'self'`) · raw colours outside
the token blocks · alarm colour on refutations.

## 8. Checklist for any UI change

1. Colours via tokens only; new token? add it to **both** blocks.
2. New status? extend `statusOf()` and §3 above.
3. New `$("#id")`? the id must exist in `index.html` (tested).
4. New overlay or async fetch? model it in `ui_machine.js` with a sequence guard and a test.
5. Check 390px width and both themes.
6. `node hub/test_design_and_ui.mjs`.
