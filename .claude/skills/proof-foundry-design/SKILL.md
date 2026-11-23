---
name: proof-foundry-design
description: Proof Foundry's "Proceedings" design system and frontend state-machine rules. Use before changing anything in web/public/ (index.html, style.css, app.js, ui_machine.js), adding a view, status, colour, overlay or chart to the dashboard, or reviewing a UI change in this repo.
---

# Proof Foundry — Proceedings design skill

The full spec is `docs/DESIGN.md`. Read it before editing `web/public/*`. This skill is the short version
plus the workflow.

## The look in one paragraph

A public ledger of machine-checked mathematics, set like a journal: warm rag paper (`--bg #F5F2EA`),
archival ink, **one** oxblood accent (`--accent`) for verified results, live records and the single
primary action per view, and **one** alarm colour (`--alarm`) for flagged, contradiction and needs-fix.
The Night theme is warm graphite with a terracotta accent and an amber alarm, never navy.
Newsreader for display (italic theorem labels and mission questions), Source Sans 3 for UI, IBM Plex Mono
for Lean, IDs and hashes. Hairline rules, 0–2px corners, no cards, no glows.

## Hard rules (enforced by `node hub/test_design_and_ui.mjs`)

- Colour literals live **only** in the `:root` and `[data-theme="dark"]` token blocks of `style.css`.
  Everywhere else, including canvas code, use `var(--token)` or `getComputedStyle(document.documentElement)`.
- Radius ≤ 2px (`var(--radius)`); `50%` is allowed only on `.live-dot`.
- `box-shadow` only on `.drawer` / `.modal*`.
- Banned: Inter, Space Grotesk, JetBrains Mono, Tailwind sky/cyan/emerald/purple/rose hexes, `#080d18`,
  radial/conic gradients, `backdrop-filter`, pill radii, `text-shadow`, card/KPI classes, inline scripts.
- Fonts: exactly Newsreader, Source Sans 3 and IBM Plex Mono from Google Fonts.
- Every `$("#id")` in `app.js` must exist in `index.html`.

## Status grammar — always via `statusOf(lemma)`

○ open (muted) · ◐ in work · ◇ provisional · ◆ frozen/audited (accent) · ♛ live record (accent, one chip
with score and next target) · ✕ refuted (**plain ink**, since a counterexample is a result) · — barrier
(muted, struck) · ⚠ flagged / ⛔ contradiction (alarm, 1px outline box). Never render a second
King-of-the-Hill chip next to a record's status.

## State: `web/public/ui_machine.js`

A pure ES module with three orthogonal machines: `transport` (boot / live_* / static_* / error),
`route` (`{view, ledgerTab, mission, claim}` ⇄ URL) and `overlay` (`none | dossier | attempt | search`,
strictly one at a time). `app.js` only performs effects and renders. When you add async work, give it
a sequence number in the machine so stale responses are dropped, and add a test to
`hub/test_design_and_ui.mjs`. Read the backend projection fields (`seal`, `freshness`, `pr_state`,
`actions`, `record_meta`) through the adapters. Never re-derive seals in `app.js`.

## Workflow

1. Read `docs/DESIGN.md` §1–§4 and the relevant view in `app.js`.
2. Make the change with tokens, glyphs and hairlines. Reuse `statusHTML`, `recordRowHTML`,
   `claimRowHTML`, `boundBarHTML` and `sparkHTML` before writing new markup.
3. Run `node hub/test_design_and_ui.mjs`, then `node --check web/public/app.js`.
4. Look at it: `PORT=4321 node web/server.mjs`, then check Paper and Night at 1440px and at 390px
   (no horizontal scroll), and open and close each overlay with the mouse and with Esc.
5. If you changed a rule, update `docs/DESIGN.md` and the test in the same commit.
