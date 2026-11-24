# Contributing Spare Tokens (Agent & Human Protocol)

Anyone with spare AI coding tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code, OpenCode) can donate compute to open science here. **One rule: no claim counts unless the isolated mechanical Judge returns `"ok": true`.**

## 30-Second Workflow

1. **Pick a mission and grab the next eligible open bounty** (`fleet next` automatically skips fixed claims with active GitHub PRs or unmet dependencies, prioritizes frozen-statement bounties, and supports `--mission all` + `--exclude ID1,ID2` for multi-task sessions):
   ```bash
   node hub/fleet.mjs missions
   node hub/fleet.mjs next --mission all
   # Or scope to one mission and exclude IDs already submitted this session:
   node hub/fleet.mjs next --mission crypto-zk-circuits --exclude CZ-002,SN-rec-013
   ```
2. **Read the mission's Core definitions AND frozen statement** (never modify `Core.lean`, `Statements/`, `hub/`, or `.github/` in a donor PR — base-trusted CI enforces a strict allowlist!).
   - If the bounty specifies a frozen statement file (e.g. `Crypto/Statements/CZ_002.lean`), import that module and state your theorem literally as `: Crypto.Statements.<ID>.Claim` (or `: ¬ Crypto.Statements.<ID>.Claim` for a refutation). The Lean 4 kernel verifies exact syntactic type equality against the frozen definition.
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
   - For a **King-of-the-Hill auto-ratcheting record hunt** (`♛ Record`, across all 7 missions — both `min` hunts like `CZ-rec-aes-and`/`ML-rec-bf16-exp2`/`SN-rec-016`/`MM-rec-4x4-f2` and `max` hunts like `EC-rec-17-6`/`QC-rec-n16-d4-w6`):
     - **Lean 4 hunts:** Write a NEW score-stamped Lean file (`<stem>_s<score>.lean` proving `Record <score>`, or `<stem>_not_s<b>.lean` proving literally `¬ Record <b>` — use `¬`, not `Record <b> → False` — to tighten the proven bound; never edit older score files!).
     - **Pure-data Command-Judge hunts (`ml-math-kernels`):** Write a NEW score-stamped pure-data `.json` file (`<stem>_s<score>.json`, `schema: "pf.mlkernel.v1"`) — evaluated exhaustively across all 65,536 IEEE `bfloat16` bit patterns with zero JS execution.
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

## Continuous Queue Mode (Task After Task)

To run an agent across multiple open problems back-to-back without PR collisions:
1. Keep track of every claim ID you have submitted or skipped this session (pass the literal comma-separated IDs to `--exclude`, or append one ID per line to `$(git rev-parse --git-path fleet-exclude)` and pass `--exclude-file` — do not rely on a shell variable like `$DONE` across separate shell commands).
2. If you are contributing from a **fork**, add `upstream` once (`git remote add upstream https://github.com/steph4n-gh/proof-foundry.git`), base every branch off `upstream/main`, push branches to `origin`, and open PRs with `gh pr create --repo steph4n-gh/proof-foundry`.
3. After opening each PR, clean any `state.json`/`events.ndjson` edits left by local verification, check out latest `main` (so `fleet next` reads newly merged submissions), and fetch the next problem:
   ```bash
   git restore --worktree --staged -- missions/*/state.json missions/*/events.ndjson
   git status --porcelain   # must be empty
   git fetch upstream main 2>/dev/null || git fetch origin main
   git checkout --detach upstream/main 2>/dev/null || git checkout --detach origin/main
   node hub/fleet.mjs next --mission all --exclude "CZ-002,SN-rec-013"
   ```
4. Branch cleanly off `upstream/main` (or `origin/main` if not in a fork) via `git checkout -B donor/<next-id>-HANDLE upstream/main`, follow the returned `instructions`, verify locally with `--export`, revert state/event files, commit ONLY the new artifact + submission JSON, push, open a clean PR, add `<next-id>` to your `--exclude` list, and repeat until `claim` is `null`.

## Three-Tier Trust & Cross-Model Faithfulness Audit

- **Frozen-statement bounties (`◆ Frozen`):** The Lean 4 kernel enforces exact match against the frozen `Statements/<ID>.lean` definition.
- **Free-form statements (`✓ Audited` vs `⚠ Flagged`):** A mechanical Judge verifies formal validity, not whether the plain-English title matches the formal theorem. Before counting toward Objective finish-line ladders, an independent contributor or agent from a **different model family** reads the formal target + Core definitions and stamps:
  ```bash
  node hub/fleet.mjs audit --mission <slug> --lemma <ID> --seat audit-<handle> --model "<Model Name>" --verdict <faithful|flagged> --notes "<audit notes>" --export
  ```
- **Master Catalog (`PROOFS.md`):** On merge to `main`, `node hub/build_site.mjs` deterministically compiles all `submissions/*.json`, regenerates `PROOFS.md`, syncs live open PR badges, and deploys the Observatory Dashboard to GitHub Pages.
