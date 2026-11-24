---
name: verify-proof-foundry
description: Formally verify Proof Foundry's core state machine, King-of-the-Hill scoring, Lean Judge security gate, PR-gate concurrency, BF16/FMA/C++20 ML math oracle, and frontend UI state machine. Use before merging any change to hub/state_machine.mjs, hub/missions.mjs, hub/pr_gate.mjs, hub/judges/lean4.mjs, hub/judges/command.mjs, missions/ml-math-kernels/judge/verify.mjs, hub/export_dropin.mjs, web/public/ui_machine.js, or .github/workflows/judge.yml.
---

# Verify Proof Foundry (Formal Verification Skill)

This skill guards the six software boundaries in Proof Foundry where a bug corrupts scientific truth, breaks King-of-the-Hill fairness, lets an unverified submission merge, or wedges the frontend — and where ordinary unit tests miss rare orderings or edge cases.

## Sync Commit & Coverage Record

- **Last confirmed sync commit:** `8a048ab`
- Move this commit forward **only** after confirming every covered check describes the code at the new commit and passes cleanly.

| Covered Code | Plain-English Promise & Harm if Broken | Verification Artifact | How to Check |
| :--- | :--- | :--- | :--- |
| `hub/state_machine.mjs` (`transitionClaim`, `transitionRecord`, `replayRecordSubmissions`, `assignSeatClaim`, `releaseSeatClaim`, `computeTrustSeal`, `isRungConquered`), `hub/missions.mjs` (`recordPointsBySeat`) | Records ratchet strictly monotonically; total KotH points equal the single-jump delta (no 1-step point farming); stale `core_hash` / `statement_hash` receipts receive 0 points, `stale` seal, and never conquer objectives; contradictions are sticky & order-independent (including direct replay calls); exact closure locks permanently; seats and claims stay 1-to-1; contradicted/flagged/stale claims never count as conquered. | `formal/lean/PFFormal/StateMachine.lean`, `formal/lean/PFFormal/AxiomCheck.lean`, `formal/verify_state_machine_equiv.mjs` | `node formal/verify_state_machine_equiv.mjs` |
| `hub/judges/lean4.mjs` (native `Init` AST gate + Pass 2 `.olean` env/import/dependency audit) | No submitted Lean proof can smuggle forbidden imports (`Lean.*`), `sorry`, `axiom`, `opaque`, `unsafe` helpers, `native_decide`, or metaprograms past the judge before or during compilation. | `hub/test_judge.mjs` (113 checks + 51 tracked Lean proofs across 6 Lean missions) | `node hub/test_judge.mjs` |
| `hub/pr_gate.mjs` (`classifyEntries`, `validateRecordImprovement`, `evaluateAutoMergeDataOnly`, `verifyPrEntries`), `.github/workflows/judge.yml`, `.github/workflows/auto-merge.yml` | No unjudged commit, stale bounty, duplicate/beaten score, contradiction crossing, non-100644/path escape, mismatched receipt metadata, or frozen-statement edit (outside whole-mission maintainer retirement) can auto-merge under moving PR heads or competing PRs. | `formal/pr_gate_merge.tla`, `formal/pr_gate_koth.tla`, `formal/claim_seat_lifecycle.tla` | `npm run verify:formal -- --tlc-only --require-tlc` (inspect with `/statechart`) |
| `missions/ml-math-kernels/judge/verify.mjs` (`bf16ToF32`, `f32ToBf16RNE`, `f64ToBf16RNE`, `bf16LatticeIndex`, `fmafExact`, `erfcExact64`), `hub/export_dropin.mjs` (UB-free 32-bit C++/CUDA emitters), `hub/judges/command.mjs` (`allowed_extensions` pre-spawn gate) | Exact dyadic algebra, universal IEEE-754 RNE optimality/tie-to-even/monotonicity, BF16 lattice order-isomorphism & ULP metric axioms, direct real-value RNE & overflow proofs (`f32→bf16`, zero-double-rounding `f64→bf16`, single-rounding `fmaf`), and universal $2^{64}$ UB-free C++ `ishr_s`/`ishl`/`ishr_u` & 32-bit wrapping equivalence match the JS judge across all 65,536 BF16 inputs and 2,377 adversarial cases. | `formal/oracle/PFOracle/BF16Oracle.lean`, `formal/oracle/PFOracle/BF16Rounding.lean`, `formal/oracle/PFOracle/AxiomCheck.lean`, `formal/verify_ml_oracle.mjs` | `node formal/verify_ml_oracle.mjs` |
| `web/public/ui_machine.js` (`reduceUI`, `parseRouteFromLocation`, `serializeRouteToLocation`, `sealOf`, `recordMetaOf`, `actionsOf`, `computeGap`, `statusOf`) | Only one overlay exists at a time; failed mission switches never tear down an active stream; stale async responses are pure no-ops; `route.mission` moves only on commit; cross-mission overlays clear on commit; URL routes round-trip losslessly. | `formal/ui_machine.tla`, `formal/verify_ui_machine.mjs` | `node formal/verify_ui_machine.mjs` and `/statechart` on `formal/ui_machine.tla` |

## Quick Check: Did Your Change Touch Verified Code?

Run from the repository root:

```sh
git diff --name-only <sync-commit>..HEAD -- \
  hub/state_machine.mjs hub/missions.mjs hub/pr_gate.mjs \
  hub/judges/lean4.mjs hub/judges/command.mjs missions/ml-math-kernels/judge/verify.mjs hub/export_dropin.mjs \
  web/public/ui_machine.js .github/workflows/judge.yml .github/workflows/auto-merge.yml \
  formal/
```

If that list is non-empty, run the full formal gate:

```sh
npm run verify:formal -- --require-tlc && npm test
```

## Reading Results & Telling Bugs from Model Drift

1. **Lean 4 proofs (`formal/lean/` and `formal/oracle/`):**
   - If `lake build` fails in `StateMachine.lean` or `BF16Oracle.lean`, a proved invariant no longer holds on the model (or `AxiomCheck.lean` caught a `sorry` / `bv_decide` / non-standard axiom). Never add `sorry`, `bv_decide`, or weaken an invariant without explicit maintainer sign-off.
   - If `lake build` passes but `verify_state_machine_equiv.mjs` or `verify_ml_oracle.mjs` reports a mismatch, **the running JS diverged from the formally proved Lean spec**:
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

- **Proved universally (unbounded):** Lean 4 theorems over `PFFormal.StateMachine` (331 swept theorems) and `PFOracle.BF16Oracle` + `PFOracle.BF16Rounding` (34 pure-kernel theorems, zero `bv_decide`).
- **Proved exhaustively within finite bounds:** TLC models (`pr_gate_merge`: 1 PR, 2 heads, 1 base advance; `claim_seat_lifecycle`: 2 seats, 2 claims; `pr_gate_koth`: 2 competing PRs on 1 hunt; `ui_machine`: 2 missions, 2 claims, seq budget 2).
- **Verified empirically against the real JS & C++20:** `verify_state_machine_equiv.mjs` (2,818 traces / 20,233 steps, 10 mutants), `verify_ml_oracle.mjs` (65,536/65,536 BF16 sweep + 2,377 adversarial cases + 3 CLI kernels + 5 mutants), `missions/ml-math-kernels/judge/test_verify.mjs` (9 tests including C++20 `-fsanitize=undefined` across 6 kernels × 65,536 inputs), `verify_ui_machine.mjs` (11,099 trace steps + 23,296 URL round-trips + 20,231 adapter states).
- **Outside the proof boundary (TCB):** Lean 4.36.0 kernel, Node.js/V8, C++20/CUDA compilers, Linux/macOS, Git, GitHub branch-protection internals (`strict_required_status_checks_policy: true`), float64 transcendental reference targets (`Math.sqrt`/`Math.pow`/`Math.exp`/`erfExact64`/`erfcExact64`), and browsers.

## Updating the Sync Commit

Once every check passes (`npm run verify:formal -- --require-tlc && npm test`) and you have verified that each model/proof still accurately describes the current code, update **Last confirmed sync commit** at the top of this file to the new commit SHA (or run `/maintain-formal-verification-skill` after changes that skipped rechecking).
