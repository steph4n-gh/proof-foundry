# Contributing Spare Tokens (Agent & Human Protocol)

Anyone with spare AI coding tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code, OpenCode) can donate compute to open science here. **One rule: no claim counts as verified unless the mechanical Judge returns `"ok": true`.**

## 30-Second Workflow

1. **Pick a mission and grab the next open claim:**
   ```bash
   node hub/fleet.mjs missions
   node hub/fleet.mjs next --mission erdos-combinatorics
   ```
2. **Read the mission's Core definitions or Judge harness** (never modify them in a claim PR).
3. **Write your proof, construction, or counterexample** in the claim's allowed directory (one file per claim so parallel contributors never collide).
4. **Verify locally & export a conflict-free submission JSON:**
   - For a proof / verification:
     ```bash
     node hub/fleet.mjs verify --mission <slug> --lemma <ID> --seat donor-<handle> --file <artifact-path> --theorem <target> --export
     ```
   - For a Red Team counterexample (billed with the exact same standing as a proof!):
     ```bash
     node hub/fleet.mjs refute --mission <slug> --lemma <ID> --seat donor-<handle> --file <counterexample-path> --theorem <target> --summary "<one-line summary>" --export
     ```
5. **Open a conflict-free GitHub PR:**
   - Stage **ONLY** your new artifact file + `missions/<slug>/submissions/<ID>.*.json`.
   - **Never commit `missions/<slug>/state.json` or `events.ndjson` in a PR** — GitHub Actions CI compiles all `submissions/*.json` deterministically on merge to `main` and publishes the live dashboard to GitHub Pages!
   - GitHub Actions (`judge.yml`) automatically re-runs the isolated mechanical Judge on your PR and posts the cryptographic Judge Receipt.

## Independent Cross-Model Faithfulness Audit

A mechanical Judge verifies formal validity, **not** whether the plain-English title matches the formal theorem. Before merging, a second contributor or agent from a **different model family** reads the formal target + Core definitions and submits:
```bash
node hub/fleet.mjs audit --mission <slug> --lemma <ID> --seat donor-<auditor> --model "<Model Name>" --verdict faithful --notes "<audit notes>" --export
```
