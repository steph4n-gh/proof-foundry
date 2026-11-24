# Proof Foundry Formal Verification Suite

Proof Foundry formally verifies its own critical software core across four complementary layers — combining **universally quantified Lean 4.36.0 proofs**, **exhaustive TLA+ / TLC protocol model checking**, **Lean-native AST & compiled `.olean` security auditing**, and **differential equivalence / trace verification** against the running Node.js & browser code.

Run the entire suite in one command:

```sh
npm run verify:formal
```

In CI (`.github/workflows/judge.yml`), `npm run verify:formal -- --require-tlc` runs on every maintainer PR and push to `main` inside the required `gate` check, using Lean 4.36.0, Java 21, and SHA-256-verified `tla2tools.jar` v1.7.4 (`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`).

---

## Summary Matrix

| Layer | Covered Product Code | Formal Artifact | Verification Engine | Scope & Result |
| :--- | :--- | :--- | :--- | :--- |
| **1. Core State Machine & KotH** | [hub/state_machine.mjs](../hub/state_machine.mjs), [hub/missions.mjs](../hub/missions.mjs) | [PFFormal/StateMachine.lean](./lean/PFFormal/StateMachine.lean), [AxiomCheck.lean](./lean/PFFormal/AxiomCheck.lean), [verify_state_machine_equiv.mjs](./verify_state_machine_equiv.mjs) | Lean 4.36.0 + `pf_state_check` differential oracle | **30 named / 327 swept theorems** (`∀` scores, `∀` histories, arbitrary seat sets, zero `sorry`, standard axioms only) + **2,673 traces / 17,900 steps** exact JS equivalence + **8/8 mutants caught** |
| **2a. Lean Judge Security Gate** | [hub/judges/lean4.mjs](../hub/judges/lean4.mjs) | Native `Init` pre-compile AST parser + Pass 2 `.olean` import/constant/dependency-closure audit + [hub/test_judge.mjs](../hub/test_judge.mjs) | Lean 4.36.0 parser & kernel environment | **99 judge tests** + **43/43 tracked Lean proofs** audited; zero elaboration before AST pass; blocks forbidden imports, unused axioms, `opaque`/`unsafe` helpers, and `ctorIdx._impl` spoofs |
| **2b. PR Gate & KotH Concurrency** | [hub/pr_gate.mjs](../hub/pr_gate.mjs), [.github/workflows/judge.yml](../.github/workflows/judge.yml), [.github/workflows/auto-merge.yml](../.github/workflows/auto-merge.yml) | [pr_gate_merge.tla](./pr_gate_merge.tla), [pr_gate_koth.tla](./pr_gate_koth.tla), [claim_seat_lifecycle.tla](./claim_seat_lifecycle.tla) | TLA+ / TLC 2.19 (BFS, deadlock check) | `pr_gate_merge`: **248 gen / 112 distinct** (depth 7, 0 errors, 3 counterexamples)<br>`claim_seat_lifecycle`: **174 gen / 36 distinct** (depth 5, 0 errors)<br>`pr_gate_koth` (2-PR race): **9,462 gen / 2,597 distinct** (depth 11, 0 errors, 6 counterexamples) |
| **3. 128-Bit BigInt Math Oracle** | [missions/verified-science-kernels/judge/verify.mjs](../missions/verified-science-kernels/judge/verify.mjs) | [PFOracle/MathOracle.lean](./oracle/PFOracle/MathOracle.lean), [AxiomCheck.lean](./oracle/PFOracle/AxiomCheck.lean), [verify_math_oracle.mjs](./verify_math_oracle.mjs) | Lean 4.36.0 + `pf_oracle_check` differential oracle | **28 theorems** (zero `sorry`, standard axioms only): exact dyadic `TwoSum`/`Dot2`/`orient2d`, finite Taylor partial-sum enclosures `< 69/2¹²⁸` (`exp`) and `< 41/2¹²⁸` (`sin`) (`< 10⁻³⁶`), exact ceiling score + **8,194/8,194 bit-for-bit grid matches** + `S-rec-exp = 405` certified (`> 6.7 × 10²²×` margin) |
| **4. Frontend UI State Machine** | [web/public/ui_machine.js](../web/public/ui_machine.js) | [ui_machine.tla](./ui_machine.tla), [verify_ui_machine.mjs](./verify_ui_machine.mjs) | TLA+ / TLC 2.19 + JS trace/URL/adapter verifier | `ui_machine.tla`: **379,157 gen / 24,856 distinct** (depth 14, 0 errors, 4 counterexamples) + **11,099 fuzzer steps**, **23,296 URL round-trips**, **20,253 adapter states**, **8/8 mutants caught** |

---

## Real Software Bugs Found & Fixed by This Suite

Formal verification was not rubber-stamping — building these proofs uncovered real defects in the codebase that unit tests had missed, all of which are now fixed and locked behind regression checks:

1. **Points ledger prototype-property corruption (`hub/state_machine.mjs`, `hub/missions.mjs`)** — Found by Track 1 (Lean state machine differential audit): `(rs.points_by_seat[entry.seat] || 0) + points` read inherited `Object.prototype` keys on seat IDs like `"constructor"`, turning numeric totals into concatenated strings (`"function Object() { [native code] }22"`). Fixed with `Object.hasOwn` and null-prototype accumulation.
2. **Fail-open catch & loose score type guard (`hub/pr_gate.mjs`)** — Found by Track 2 (PR gate audit): `classifyEntries` swallowed state-derivation exceptions when checking frozen-statement edits, and `evaluateAutoMergeDataOnly` accepted string score `"7"`. Hardened to fail closed on unreadable base state and require strict integer `typeof sub.score === "number"`.
3. **Three UI async/edge-case state-machine bugs (`web/public/ui_machine.js`)** — Found by Track 4 (UI TLA+ / trace verification):
   - Closing `search` or `attempt` via `ESCAPE` left a deep-linked `route.claim` stuck in the URL.
   - Switching missions via `MISSION_LOADED` without an explicit `intent.claim` leaked the previous mission's `route.claim` onto the new mission.
   - Unprojected legacy `contradiction` records checked only `record_state.contradiction` in `recordMetaOf` instead of matching `sealOf` (`status === "contradiction" || record_state.contradiction`), and `CATALOG_FAILED` did not preserve an already-committed healthy `activeMission`.
4. **Command-Judge sandboxing (`missions/verified-science-kernels/judge/verify.mjs`)** — Functional kernel runs now execute in a double-isolated child process under Node `--permission` (with **zero** filesystem, child-process, worker, addon, or WASI permissions) + `--max-old-space-size=256` + an isolated V8 `vm` context (`Object.create(null)`, `codeGeneration: { strings: false, wasm: false }`, pre-captured `Reflect.apply` / `Object.hasOwn` intrinsics, syntax-aware `tokenizeJsCode` rejecting `import` and regex literals while preserving string/template literals verbatim) + a per-run 128-bit random stdout nonce; `S-rec-exp`/`S-rec-sin` coefficient artifacts and `ml-math-kernels` BF16 DAGs are parsed statically as pure data with **zero JS execution**.

---

## Pillar Details

### 1. Lean 4 Core State Machine & King-of-the-Hill Proofs (`formal/lean/`)

Proved in [formal/lean/PFFormal/StateMachine.lean](./lean/PFFormal/StateMachine.lean) for **all** natural-number scores, **all** replay histories, and **arbitrary** seat/claim counts:
- **Monotonicity:** `koth_monotone_best`, `koth_monotone_best_replay`, `koth_monotone_refuted`, `koth_monotone_refuted_replay`.
- **Anti-farming telescoping totals:** `koth_anti_farming_ledger`, `koth_anti_farming_record_points`, `koth_anti_farming_bound_points`, `koth_anti_farming_record_points_replay` — stepping 1 unit at a time yields the exact same total points as a single jump (`(best - startTarget) * step + 1`).
- **Sticky & order-independent contradiction:** `koth_contradiction_sticky`, `koth_contradiction_reachable`, `koth_contradiction_order_independent`, `claim_contradiction_sticky`, `claim_order_independent_contradiction`.
- **Exact optimal closure:** `koth_closed_exact_optimal`, `koth_closed_denies`.
- **Barriers, arbitrary seat↔claim bijection, trust seals & conquest:** `barrier_never_overwrites_verdict`, `seat_claim_bijection_preserved`, `trust_seal_and_conquered_sound`, `conquered_false_of_bad_seal`, `conquered_replay_default`.

[formal/lean/PFFormal/AxiomCheck.lean](./lean/PFFormal/AxiomCheck.lean) mechanically sweeps all 331 theorems in `PF` during `lake build` and fails compilation if any theorem uses `sorryAx` or non-standard axioms.

### 2. Judge Security Boundary & PR-Gate TLA+ Models

- **Three-layer Lean Judge ([hub/judges/lean4.mjs](../hub/judges/lean4.mjs)):**
  1. Fast JS lexical pre-filter (blocks guillemets, raw strings, unclosed comments/strings, forbidden tokens).
  2. **Lean 4.36 native `Init` pre-compile AST gate** (parses exact private source bytes with Lean's own parser before Pass 1; zero elaboration, zero user code execution; checks imports, commands, attributes, and `set_option` allowlist).
  3. **Pass 2 compiled `.olean` environment audit** (verifies true direct module imports, every declared constant in `claimMod`, and full transitive local kernel dependencies of the target theorem; the sole `unsafe` exemption requires compiler-synthesized `<Ind>.ctorIdx._impl` owned by a same-module `.inductInfo`, matching the tag-intrinsic body and compiler `implemented_by` link, and unreachable from the target theorem).
- **TLA+ / TLC protocol models:**
  - [pr_gate_merge.tla](./pr_gate_merge.tla) (`248` generated / `112` distinct, depth `7`, 0 errors) — single donor PR under moving head & advancing `main`; 3 counterexamples (`PinJudgeInputs`, `RequireCurrentBase`, `RequireAuthorizedHead`).
  - [claim_seat_lifecycle.tla](./claim_seat_lifecycle.tla) (`174` generated / `36` distinct, depth `5`, 0 errors) — seat bijection, sticky & order-independent contradiction, editorial barriers.
  - [pr_gate_koth.tla](./pr_gate_koth.tla) (`9,462` generated / `2,597` distinct, depth `11`, 0 errors) — two competing donor PRs racing on a KotH hunt, crossing bounds, frozen-statement mutations, and non-100644/path escapes; 6 reproduced counterexamples.

### 3. Lean 4 128-Bit Math Oracle Proofs (`formal/oracle/`)

Proved in [formal/oracle/PFOracle/MathOracle.lean](./oracle/PFOracle/MathOracle.lean) (`28` audited theorems, zero `sorry`, standard axioms only):
- Exact dyadic rational algebra (`dyadicAdd_sound`, `dyadicSub_sound`, `dyadicMul_sound`, `dyadicEq_iff`, `dyadicSign_sound`, `exactDot_sound`, `orient2d_sign_exact`).
- Truncating BigInt division (`Int.tdiv`) error bound `< 1` ULP (`tdiv_error`).
- `fixed128Exp` (34 terms, `|xFix| ≤ 2¹²⁷`): rounding `< 68/2¹²⁸`, rational remainder tail `< 1/2¹²⁸`, finite partial-sum enclosure `< 69/2¹²⁸ < 10⁻³⁶` for every `34 + n` Taylor partial sum.
- `fixed128Sin` (20 terms, `|xFix| ≤ ⌊4·2¹²⁸/5⌋`): rounding `< 40/2¹²⁸`, rational remainder tail `< 1/2¹²⁸`, finite partial-sum enclosure `< 41/2¹²⁸ < 10⁻³⁶` for every `20 + n` Taylor partial sum.
- Exact integer ceiling score (`ceilScore_spec`, `ceilScore_eq_ceil`, `ceilScore_decision_robustness`).
- Differential harness ([verify_math_oracle.mjs](./verify_math_oracle.mjs)) verifies **bit-for-bit agreement on all 8,194 grid points** (`S-rec-exp` + `S-rec-sin`) plus `173` adversarial cases and certifies winning record `S-rec-exp = 405` (`6.7 × 10²²×` margin above the formal error bound).

### 4. Frontend UI State Machine (`formal/ui_machine.*` & `formal/verify_ui_machine.mjs`)

- [ui_machine.tla](./ui_machine.tla) (`379,157` generated / `24,856` distinct states, depth `14`, 0 errors, 0 deadlocks) verifies `SingleOverlayKind`, `HealthyStreamSurvivesFailedSwitch`, `RouteMissionTracksActiveMission`, `NoCrossMissionOverlayAfterCommit`, `StaleMissionResponseIgnored`, `StaleDossierResponseIgnored`, `DossierRouteClaimSync`, and reproduces 4 mutation counterexamples (`CheckMissionSeq`, `CheckDossierSeq`, `PreserveHealthyStream`, `ClearCrossMissionOverlay`).
- [verify_ui_machine.mjs](./verify_ui_machine.mjs) runs `11,099` randomized/adversarial transitions, `23,296` Cartesian URL route round-trips + `90` legacy hash aliases, `20,253` snapshot adapter checks, and `8` negative mutation self-checks directly against [web/public/ui_machine.js](../web/public/ui_machine.js).

---

## Trusted Computing Base (What Stays Outside the Proofs)

Formal verification proves Proof Foundry's logic **up to** the following platform boundary (explicitly assumed, not proved):
- **Lean 4.36.0 kernel & compiler**, **TLC 2.19**, and **JVM**.
- **Node.js / V8** (including `--permission`, isolated `vm.createContext`, and `--max-old-space-size=256`), **OS kernel**, **Git**, and **browser DOM/EventSource** implementations.
- **Analytic series limits (Math Oracle):** `PFOracle/MathOracle.lean` proves exact enclosures against every finite rational Taylor partial sum (`34 + n` for `exp`, `20 + n` for `sin`); the real-analysis convergence of those Taylor series to transcendental $\exp(x)$ and $\sin(x)$ on $[-\tfrac{1}{2}, \tfrac{1}{2}]$ and $[-\tfrac{4}{5}, \tfrac{4}{5}]$ is an explicit external mathematical assumption (not formalized via Mathlib real analysis).
- **GitHub hosted branch rules & merge enforcement:** `pr_gate_merge.tla` and `pr_gate_koth.tla` assume protected `main` without privileged bypass, `strict_required_status_checks_policy: true` on `gate`, and head-SHA-pinned merges (the hosted deferred auto-merge behavior for write-capable contributors remains an external GitHub platform assumption).
- **Differential equivalence scope:** `verify_state_machine_equiv.mjs` and `verify_math_oracle.mjs` prove properties universally on the Lean executable specifications and verify exact equivalence to the JS implementations across large deterministic/adversarial suites rather than compiling JS via a verified compiler.

---

## Reproduce Locally

```sh
# Full formal verification suite (Lean builds + differential checks + all 4 TLC models)
npm run verify:formal

# Require TLC even locally (same command CI enforces)
TLA2TOOLS=/path/to/tla2tools.jar JAVA=/path/to/java npm run verify:formal -- --require-tlc

# Individual layers
node formal/verify_state_machine_equiv.mjs
node formal/verify_math_oracle.mjs
node formal/verify_ui_machine.mjs
npm test
```

To inspect TLA+ counterexamples or redraw statecharts interactively, use the `/statechart` skill on any `formal/*.tla` model, or see [.claude/skills/verify-proof-foundry/SKILL.md](../.claude/skills/verify-proof-foundry/SKILL.md) for the project-local maintenance workflow.
