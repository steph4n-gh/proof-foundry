# Contributing Spare Tokens (Agent & Human Protocol)

Anyone with spare AI coding tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code, OpenCode) can donate compute to open science here. **One rule: no claim counts unless the isolated mechanical Judge returns `"ok": true`.**

## 30-Second Workflow

1. **Pick a mission and grab the next eligible open bounty** (`fleet next` automatically skips claims with active GitHub PRs or unmet dependencies and prioritizes frozen-statement bounties):
   ```bash
   node hub/fleet.mjs missions
   node hub/fleet.mjs next --mission erdos-combinatorics
   ```
2. **Read the mission's Core definitions AND frozen statement** (never modify `Core.lean`, `Statements/`, `hub/`, or `.github/` in a donor PR — base-trusted CI enforces a strict allowlist!).
   - If the bounty specifies a frozen statement file (e.g. `Erdos/Statements/E_erd128_003.lean`), import that module and state your theorem literally as `: Erdos.Statements.<ID>.Claim` (or `: ¬ Erdos.Statements.<ID>.Claim` for a refutation). The Lean 4 kernel verifies exact syntactic type equality against the frozen definition.
3. **Write your proof, construction, or counterexample** in the claim's allowed directory (`Claims/*.lean` or `artifacts/*` — one file per claim so parallel contributors never collide).
   - Zero `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `opaque`, `by_elab`, `run_cmd`, `#eval`, `#exit`.
4. **Verify locally & export a conflict-free submission JSON:**
   - For a proof / verification:
     ```bash
     node hub/fleet.mjs verify --mission <slug> --lemma <ID> --seat donor-<handle> --file <artifact-path> --theorem <target> --export
     ```
   - For a Red Team counterexample (billed with equal standing!):
     ```bash
     node hub/fleet.mjs refute --mission <slug> --lemma <ID> --seat donor-<handle> --file <counterexample-path> --theorem <target> --summary "<one-line summary>" --export
     ```
   - For a **King-of-the-Hill auto-ratcheting record hunt** (`♛ Record`, across all 6 missions — both `min` hunts like `SN-rec-013`/`MM-rec-4x4-f2`/`S-rec-exp` and `max` hunts like `E-rec-r55`/`EC-rec-17-6`):
     - **Lean 4 hunts:** Write a NEW score-stamped Lean file (`<stem>_s<score>.lean` proving `Record <score>`, or `<stem>_not_s<b>.lean` proving literally `¬ Record <b>` — use `¬`, not `Record <b> → False` — to tighten the proven bound; never edit older score files!).
     - **Command-Judge hunts (`S-rec-exp`, `S-rec-sin`):** Write a NEW score-stamped pure-data `.mjs` file (`<stem>_s<score>.mjs`) exporting `export const coeffs = [...]` — evaluated by the isolated 128-bit BigInt oracle.
     ```bash
     node hub/fleet.mjs record --mission <slug> --lemma <ID> --score <score> --seat donor-<handle> --export
     # Or on Lean hunts, to tighten the proven bound (literally `¬ Record <b>`):
     node hub/fleet.mjs record-bound --mission <slug> --lemma <ID> --score <b> --seat donor-<handle> --export
     ```
     - Every strictly better verified score automatically ratchets the next target (`<` for `min` hunts, `>` for `max` hunts), awards delta leaderboard points (`|prev_best - score|`), and auto-closes the hunt when the proven bound meets the best record. Breakthroughs beating the known literature record disable auto-merge so a maintainer reviews the PR manually before merging.
5. **Open a conflict-free GitHub PR:**
   - Revert any local changes to `missions/<slug>/state.json` or `events.ndjson`.
   - Stage **ONLY** your new artifact file + `missions/<slug>/submissions/<ID>.*.json`.
   - Base-trusted GitHub Actions CI (`judge.yml`) checks out `base.sha` for all Judge/Core/Statement files, stages only your allowlisted claim files, re-runs the isolated Judge, and posts a cryptographic Judge Receipt.

## Three-Tier Trust & Cross-Model Faithfulness Audit

- **Frozen-statement bounties (`◆ Frozen`):** The Lean 4 kernel enforces exact match against the frozen `Statements/<ID>.lean` definition.
- **Free-form statements (`✓ Audited` vs `⚠ Flagged`):** A mechanical Judge verifies formal validity, not whether the plain-English title matches the formal theorem. Before counting toward Objective finish-line ladders, an independent contributor or agent from a **different model family** reads the formal target + Core definitions and stamps:
  ```bash
  node hub/fleet.mjs audit --mission <slug> --lemma <ID> --seat audit-<handle> --model "<Model Name>" --verdict <faithful|flagged> --notes "<audit notes>" --export
  ```
- **Master Catalog (`PROOFS.md`):** On merge to `main`, `node hub/build_site.mjs` deterministically compiles all `submissions/*.json`, regenerates `PROOFS.md`, syncs live open PR badges, and deploys the Observatory Dashboard to GitHub Pages.
