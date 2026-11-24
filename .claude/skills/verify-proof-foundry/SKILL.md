---
name: verify-proof-foundry
description: Formally verify Proof Foundry's core state machine, King-of-the-Hill scoring, Lean Judge security gate, PR-gate concurrency, 128-bit math oracle, and frontend UI state machine. Use before merging any change to hub/state_machine.mjs, hub/missions.mjs, hub/pr_gate.mjs, hub/judges/lean4.mjs, missions/verified-science-kernels/judge/verify.mjs, web/public/ui_machine.js, or .github/workflows/judge.yml.
---

# Verify Proof Foundry (Formal Verification Skill)

This skill guards the six software boundaries in Proof Foundry where a bug corrupts scientific truth, breaks King-of-the-Hill fairness, lets an unverified submission merge, or wedges the frontend — and where ordinary unit tests miss rare orderings or edge cases.

## Sync Commit & Coverage Record

- **Last confirmed sync commit:** `e560de7`
- Move this commit forward **only** after confirming every covered check describes the code at the new commit and passes cleanly.

| Covered Code | Plain-English Promise & Harm if Broken | Verification Artifact | How to Check |
| :--- | :--- | :--- | :--- |
| `hub/state_machine.mjs` (`transitionClaim`, `transitionRecord`, `replayRecordSubmissions`, `assignSeatClaim`, `releaseSeatClaim`, `computeTrustSeal`, `isRungConquered`), `hub/missions.mjs` (`recordPointsBySeat`) | Records ratchet strictly monotonically; total KotH points equal the single-jump delta (no 1-step point farming); contradictions are sticky & order-independent; exact closure locks permanently; seats and claims stay 1-to-1; contradicted/flagged claims never count as conquered. | `formal/lean/PFFormal/StateMachine.lean`, `formal/lean/PFFormal/AxiomCheck.lean`, `formal/verify_state_machine_equiv.mjs` | `node formal/verify_state_machine_equiv.mjs` |
| `hub/judges/lean4.mjs` (native `Init` AST gate + Pass 2 `.olean` env/import/dependency audit) | No submitted Lean proof can smuggle forbidden imports (`Lean.*`), `sorry`, `axiom`, `opaque`, `unsafe` helpers, `native_decide`, or metaprograms past the judge before or during compilation. | `hub/test_judge.mjs` (99 checks + all 43 tracked Lean proofs) | `node hub/test_judge.mjs` |
| `hub/pr_gate.mjs` (`classifyEntries`, `validateRecordImprovement`, `evaluateAutoMergeDataOnly`, `verifyPrEntries`), `.github/workflows/judge.yml`, `.github/workflows/auto-merge.yml` | No unjudged commit, stale bounty, duplicate/beaten score, contradiction crossing, non-100644/path escape, or frozen-statement edit can auto-merge under moving PR heads or competing PRs. | `formal/pr_gate_merge.tla`, `formal/pr_gate_koth.tla`, `formal/claim_seat_lifecycle.tla` | `npm run verify:formal -- --tlc-only --require-tlc` (inspect with `/statechart`) |
| `missions/verified-science-kernels/judge/verify.mjs` (`dyadic*`, `fixed128Exp`, `fixed128Sin`, `ceilScore`) | Dyadic `TwoSum`/`Dot2`/`orient2d` arithmetic is exact; 128-bit Taylor oracle error is strictly `< 10⁻³⁶` (more than `10²²×` smaller than score ticks); ceiling score rounding is exact. | `formal/oracle/PFOracle/MathOracle.lean`, `formal/oracle/PFOracle/AxiomCheck.lean`, `formal/verify_math_oracle.mjs` | `node formal/verify_math_oracle.mjs` |
| `web/public/ui_machine.js` (`reduceUI`, `parseRouteFromLocation`, `serializeRouteToLocation`, `sealOf`, `recordMetaOf`, `actionsOf`, `computeGap`, `statusOf`) | Only one overlay exists at a time; failed mission switches never tear down an active stream; stale async responses are pure no-ops; `route.mission` moves only on commit; cross-mission overlays clear on commit; URL routes round-trip losslessly. | `formal/ui_machine.tla`, `formal/verify_ui_machine.mjs` | `node formal/verify_ui_machine.mjs` and `/statechart` on `formal/ui_machine.tla` |

## Quick Check: Did Your Change Touch Verified Code?

Run from the repository root:

```sh
git diff --name-only <sync-commit>..HEAD -- \
  hub/state_machine.mjs hub/missions.mjs hub/pr_gate.mjs \
  hub/judges/lean4.mjs missions/verified-science-kernels/judge/verify.mjs \
  web/public/ui_machine.js .github/workflows/judge.yml .github/workflows/auto-merge.yml \
  formal/
```

If that list is non-empty, run the full formal gate:

```sh
npm run verify:formal -- --require-tlc && npm test
```

## Reading Results & Telling Bugs from Model Drift

1. **Lean 4 proofs (`formal/lean/` and `formal/oracle/`):**
   - If `lake build` fails in `StateMachine.lean` or `MathOracle.lean`, a proved invariant no longer holds on the model (or `AxiomCheck.lean` caught a `sorry` / non-standard axiom). Never add `sorry` or weaken an invariant without explicit maintainer sign-off.
   - If `lake build` passes but `verify_state_machine_equiv.mjs` or `verify_math_oracle.mjs` reports a mismatch, **the running JS diverged from the formally proved Lean spec**:
     - If the JS change was an accidental regression → fix the JS bug.
     - If the JS change was an intentional behavioral change → update the Lean model AND re-prove every theorem (without weakening safety properties) so Lean and JS agree again.
2. **TLA+ protocol models (`formal/*.tla`):**
   - Use the `/statechart` skill on the relevant `formal/<model>.tla` file to read every invariant violation as its shortest step-by-step counterexample in plain words, or to regenerate the Mermaid statechart when all rules hold.
   - Verify whether each action in the `.tla` model still matches the real indivisibility and guards in `hub/pr_gate.mjs`, `.github/workflows/*.yml`, `hub/state_machine.mjs`, or `web/public/ui_machine.js`. If code removed or reordered a guard, that counterexample is a **real bug**; if a workflow intentionally changed shape, update the `.tla` model first and confirm TLC passes with `0 states left on queue` and `0` errors.
   - Confirm each changed property can still fail by toggling its guard constant to `FALSE` in a scratch `.cfg` (e.g., `PinJudgeInputs`, `CheckFrozenStatement`, `CheckMissionSeq`, `PreserveHealthyStream`) and observing TLC produce a short counterexample.
3. **UI executable verifier (`formal/verify_ui_machine.mjs`) & Judge suite (`hub/test_judge.mjs`):**
   - Any failure in `verify_ui_machine.mjs` prints the exact seed/step and violated invariant name (`SingleOverlayKind`, `HealthyStreamSurvivesFailedSwitch`, `StaleMissionResponseIgnored`, `DossierRouteClaimSync`, etc.). Fix `web/public/ui_machine.js` before touching the oracle.
   - Any failure in `hub/test_judge.mjs` means either a security gate regressed or a tracked mission proof broke under the native `Init` parser / `.olean` audit.

## Honest Scope & Assumptions (TCB)

- **Proved universally (unbounded):** Lean 4 theorems over `PFFormal.StateMachine` and `PFOracle.MathOracle`.
- **Proved exhaustively within finite bounds:** TLC models (`pr_gate_merge`: 1 PR, 2 heads, 1 base advance; `claim_seat_lifecycle`: 2 seats, 2 claims; `pr_gate_koth`: 2 competing PRs on 1 hunt; `ui_machine`: 2 missions, 2 claims, seq budget 2).
- **Verified empirically against the real JS:** `verify_state_machine_equiv.mjs` (2,673 traces / 17,900 steps), `verify_math_oracle.mjs` (8,194 grid points + 173 edge cases), `verify_ui_machine.mjs` (11,099 trace steps + 23,296 URL round-trips + 20,253 adapter states).
- **Outside the proof boundary (TCB):** Lean 4.36.0 kernel, Node.js/V8 (`--permission`), Linux/macOS, Git, GitHub branch-protection internals (`strict_required_status_checks_policy: true`), and browsers.

## Updating the Sync Commit

Once every check passes (`npm run verify:formal -- --require-tlc && npm test`) and you have verified that each model/proof still accurately describes the current code, update **Last confirmed sync commit** at the top of this file to the new commit SHA (or run `/maintain-formal-verification-skill` after changes that skipped rechecking).
