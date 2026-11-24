# Proof Foundry Formal Verification Suite

Proof Foundry formally verifies its own critical software core across four complementary layers — combining **universally quantified Lean 4.36.0 proofs**, **exhaustive TLA+ / TLC protocol model checking**, **Lean-native AST & compiled `.olean` security auditing**, and **differential equivalence / trace verification** against the running Node.js, C++20 UBSan, & browser code.

Run the entire suite in one command:

```sh
npm run verify:formal
```

In CI (`.github/workflows/judge.yml`), `npm run verify:formal -- --require-tlc` runs on every maintainer PR and push to `main` inside the required `gate` check, using Lean 4.36.0, Java 21, and SHA-256-verified `tla2tools.jar` v1.7.4 (`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`).

---

## Summary Matrix

| Layer | Covered Product Code | Formal Artifact | Verification Engine | Scope & Result |
| :--- | :--- | :--- | :--- | :--- |
| **1. Core State Machine & KotH** | [hub/state_machine.mjs](../hub/state_machine.mjs), [hub/missions.mjs](../hub/missions.mjs) | [PFFormal/StateMachine.lean](./lean/PFFormal/StateMachine.lean), [AxiomCheck.lean](./lean/PFFormal/AxiomCheck.lean), [verify_state_machine_equiv.mjs](./verify_state_machine_equiv.mjs) | Lean 4.36.0 + `pf_state_check` differential oracle | **30 named / 331 swept theorems** (`∀` scores, `∀` histories, arbitrary seat sets, zero `sorry`, standard axioms only) + **2,818 traces / 20,233 steps** exact JS equivalence + **10/10 mutants caught** |
| **2a. Lean Judge Security Gate** | [hub/judges/lean4.mjs](../hub/judges/lean4.mjs) | Native `Init` pre-compile AST parser + Pass 2 `.olean` import/constant/dependency-closure audit + [hub/test_judge.mjs](../hub/test_judge.mjs) | Lean 4.36.0 parser & kernel environment | **113 judge tests** + **51/51 tracked Lean proofs** across 6 Lean missions audited; zero elaboration before AST pass; blocks forbidden imports, unused axioms, `opaque`/`unsafe` helpers, and `ctorIdx._impl` spoofs |
| **2b. PR Gate & KotH Concurrency** | [hub/pr_gate.mjs](../hub/pr_gate.mjs), [.github/workflows/judge.yml](../.github/workflows/judge.yml), [.github/workflows/auto-merge.yml](../.github/workflows/auto-merge.yml) | [pr_gate_merge.tla](./pr_gate_merge.tla), [pr_gate_koth.tla](./pr_gate_koth.tla), [claim_seat_lifecycle.tla](./claim_seat_lifecycle.tla) | TLA+ / TLC 2.19 (BFS, deadlock check) | `pr_gate_merge`: **248 gen / 112 distinct** (depth 7, 0 errors, 3 counterexamples)<br>`claim_seat_lifecycle`: **174 gen / 36 distinct** (depth 5, 0 errors)<br>`pr_gate_koth` (2-PR race): **9,462 gen / 2,597 distinct** (depth 11, 0 errors, 6 counterexamples) |
| **3. BF16 / Dyadic FMA / C++20 ML Oracle** | [missions/ml-math-kernels/judge/verify.mjs](../missions/ml-math-kernels/judge/verify.mjs), [hub/export_dropin.mjs](../hub/export_dropin.mjs) | [PFOracle/BF16Oracle.lean](./oracle/PFOracle/BF16Oracle.lean), [PFOracle/BF16Rounding.lean](./oracle/PFOracle/BF16Rounding.lean), [AxiomCheck.lean](./oracle/PFOracle/AxiomCheck.lean), [verify_ml_oracle.mjs](./verify_ml_oracle.mjs) | Lean 4.36.0 + `pf_oracle_check` differential oracle + C++20 UBSan | **34 pure-kernel theorems** (zero `sorry`, zero `bv_decide`, standard axioms only): exact dyadic algebra, universal RNE optimality/tie-to-even/monotonicity, BF16 lattice metric & order-isomorphism, direct real-value IEEE-754 RNE & overflow proofs (`f32→bf16`, zero-double-rounding `f64→bf16`, single-rounding `fmaf`), universal $2^{64}$ UB-free C++ `ishr_s`/`ishl`/`ishr_u` & 32-bit wrapping equivalence + **65,536/65,536 BF16 sweep** + **2,377 adversarial checks** + **5/5 mutants caught** |
| **4. Frontend UI State Machine** | [web/public/ui_machine.js](../web/public/ui_machine.js) | [ui_machine.tla](./ui_machine.tla), [verify_ui_machine.mjs](./verify_ui_machine.mjs) | TLA+ / TLC 2.19 + JS trace/URL/adapter verifier | `ui_machine.tla`: **379,157 gen / 24,856 distinct** (depth 14, 0 errors, 4 counterexamples) + **11,099 fuzzer steps**, **23,296 URL round-trips**, **20,231 adapter states**, **8/8 mutants caught** |

---

## Real Software Bugs Found & Fixed by This Suite

Formal verification was not rubber-stamping — building these proofs uncovered real defects in the codebase that unit tests had missed, all of which are now fixed and locked behind regression checks:

1. **Points ledger prototype-property corruption (`hub/state_machine.mjs`, `hub/missions.mjs`)** — Found by Track 1 (Lean state machine differential audit): `(rs.points_by_seat[entry.seat] || 0) + points` read inherited `Object.prototype` keys on seat IDs like `"constructor"`, turning numeric totals into concatenated strings (`"function Object() { [native code] }22"`). Fixed with `Object.hasOwn` and null-prototype accumulation.
2. **Fail-open catch & loose score type guard (`hub/pr_gate.mjs`)** — Found by Track 2 (PR gate audit): `classifyEntries` swallowed state-derivation exceptions when checking frozen-statement edits, and `evaluateAutoMergeDataOnly` accepted string score `"7"`. Hardened to fail closed on unreadable base state and require strict integer `typeof sub.score === "number"`.
3. **Three UI async/edge-case state-machine bugs (`web/public/ui_machine.js`)** — Found by Track 4 (UI TLA+ / trace verification):
   - Closing `search` or `attempt` via `ESCAPE` left a deep-linked `route.claim` stuck in the URL.
   - Switching missions via `MISSION_LOADED` without an explicit `intent.claim` leaked the previous mission's `route.claim` onto the new mission.
   - Unprojected legacy `contradiction` records checked only `record_state.contradiction` in `recordMetaOf` instead of matching `sealOf` (`status === "contradiction" || record_state.contradiction`), and `CATALOG_FAILED` did not preserve an already-committed healthy `activeMission`.
4. **Pure-data ML Judge & UB-free C++20/CUDA emitters (`missions/ml-math-kernels/judge/verify.mjs`, `hub/export_dropin.mjs`, `hub/judges/command.mjs`)** — Following the Sharp 7 consolidation (retiring all untrusted donor JS execution), `ml-math-kernels` is the sole non-Lean mission and parses declarative JSON (`pf.mlkernel.v1`, 32 KiB cap, symlink rejection, **zero JS execution**, with `allowed_extensions` enforced in `hub/judges/command.mjs` before spawning the harness). Drop-in C++/CUDA code generation uses formally proved UB-free `uint32_t` modular arithmetic and bounded shifts (`cppIshrS_equiv_sshiftRight`, `cppIshrS_no_ub_shift_bounds`, `cppIshl_no_ub_shift_bounds`, `cppIshrU_no_ub_shift_bounds`), range-guarded `ftoi_trunc`/`ftoi_round`, and signed-zero `min`/`max` parity — eliminating signed-overflow UB in `isub` triggered on `-0` input (`INT32_MIN` shifted to `-1073741824` subtracted from `1597463174`) and nonfinite/out-of-range float-to-int UB, matching the JS interpreter across 7 kernels × 65,536 BF16 inputs under C++20 `-fsanitize=undefined` (C++20 guarantees two's-complement unsigned→signed narrowing, whereas C++17 leaves it implementation-defined). Negative-tail cancellation in `bf16_gelu` was also eliminated via `erfcExact64`.

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

### 3. Lean 4 BF16 / Dyadic FMA / UB-Free C++20 ML Oracle Proofs (`formal/oracle/`)

Proved in [formal/oracle/PFOracle/BF16Oracle.lean](./oracle/PFOracle/BF16Oracle.lean) and [formal/oracle/PFOracle/BF16Rounding.lean](./oracle/PFOracle/BF16Rounding.lean) (`34` pure-kernel theorems, zero `sorry`, zero `bv_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only):
- **Exact dyadic rational algebra:** `dyadicAdd_sound`, `dyadicSub_sound`, `dyadicMul_sound`, `dyadicEq_iff`, `dyadicSign_sound`.
- **Universal IEEE-754 Round-to-Nearest-Ties-to-Even (`roundShiftEven`):** error `≤ 1/2` ULP (`roundShiftEven_err_le_half`), global nearest-integer optimality (`roundShiftEven_nearest`), exact halfway tie-to-even (`roundShiftEven_tie_even`), and monotonicity (`roundShiftEven_mono`).
- **Bit-exact BF16 conversion, NaN canonicalization & direct real-value RNE proofs:** `bf16ToF32_roundtrip`, `bf16ToF32_nan_canonical`, `f32BitsToBf16RNE_eq_roundShiftEven`, `f32BitsToBf16RNE_value_spec`, `f64BitsToBf16RNE_nan_canonical`, `f64BitsToBf16RNE_inf`, and `f64BitsToBf16RNE_value_spec` (proving exact zero-double-rounding RNE & overflow directly on `f32BitsToBf16RNE` and `f64BitsToBf16RNE` against rational values).
- **BF16 lattice order-isomorphism & ULP metric:** `bf16LatticeIndex_zero`, `bf16LatticeIndex_strict_mono`, `bf16LatticeIndex_eq_iff`, `bf16UlpDist_zero_pm`, `bf16UlpDist_zero_iff`, `bf16UlpDist_symm`, `bf16UlpDist_triangle`.
- **Single-rounding float32 FMA (`fmafExact`):** `bf16ToF32_dyadic_exact`, `fmafDyadicSum_sound`, `dyadicToF32BitsRNE_value_spec`, `fmafFiniteBits_value_spec` — proving `a * b + c` is computed with zero intermediate rounding and satisfies exact IEEE-754 binary32 RNE / overflow directly on `fmafFiniteBits`.
- **Universal $2^{64}$ UB-free C++20 / CUDA emitter equivalence:** `cppIshrS_equiv_sshiftRight`, `cppIshrS_no_ub_shift_bounds`, `cppIshl_no_ub_shift_bounds`, `cppIshrU_no_ub_shift_bounds`, `cppIadd_two_complement_mod`, `cppIsub_two_complement_mod`, `cppImul_two_complement_mod` — proving the emitted unsigned wrapping arithmetic and bounded shifts match 32-bit two's-complement / JS semantics with zero shift-count or signed-overflow UB for every `(a, b) : BitVec 32 × BitVec 32`.
- **Differential & CLI harness ([verify_ml_oracle.mjs](./verify_ml_oracle.mjs)):** cross-checks all **65,536/65,536** BF16 bit patterns (`65,282` finite/±Inf bit-exact + `254` NaN canonicalization), **2,377** adversarial differential cases (`542` `f32→bf16` + `1,064` `f64→bf16` including double-rounding traps & non-bf16 PRNG values + `273` full-24-bit `fmafExact` + `498` `cpp32` ops), certifies all **3** committed pure-data ML kernels (`rsqrt(17)`, `exp2(18)`, `silu(31)`), and catches **5/5** injected judge mutants.

### 4. Frontend UI State Machine (`formal/ui_machine.*` & `formal/verify_ui_machine.mjs`)

- [ui_machine.tla](./ui_machine.tla) (`379,157` generated / `24,856` distinct states, depth `14`, 0 errors, 0 deadlocks) verifies `SingleOverlayKind`, `HealthyStreamSurvivesFailedSwitch`, `RouteMissionTracksActiveMission`, `NoCrossMissionOverlayAfterCommit`, `StaleMissionResponseIgnored`, `StaleDossierResponseIgnored`, `DossierRouteClaimSync`, and reproduces 4 mutation counterexamples (`CheckMissionSeq`, `CheckDossierSeq`, `PreserveHealthyStream`, `ClearCrossMissionOverlay`).
- [verify_ui_machine.mjs](./verify_ui_machine.mjs) runs `11,099` randomized/adversarial transitions, `23,296` Cartesian URL route round-trips + `90` legacy hash aliases, `20,231` snapshot adapter checks, and `8` negative mutation self-checks directly against [web/public/ui_machine.js](../web/public/ui_machine.js).

---

## Trusted Computing Base (What Stays Outside the Proofs)

Formal verification proves Proof Foundry's logic **up to** the following platform boundary (explicitly assumed, not proved):
- **Lean 4.36.0 kernel & compiler**, **TLC 2.19**, and **JVM**.
- **Node.js / V8**, **OS kernel**, **Git**, **C++20 / CUDA compilers**, and **browser DOM/EventSource** implementations.
- **Transcendental float64 reference functions (`ml-math-kernels`):** `PFOracle/BF16Oracle.lean` and `PFOracle/BF16Rounding.lean` prove bit-exact BF16 RNE rounding, ULP metric axioms, direct real-value `f32→bf16`, `f64→bf16`, and single-rounding `fmaf` RNE/overflow semantics, and UB-free 32-bit integer emitter semantics; the float64 reference targets (`Math.sqrt`, `Math.pow`, `Math.exp`, `erfExact64`, `erfcExact64`) used to compute reference `bf16` truth tables stay in the JS/V8 libm TCB (with `< 1e-12` relative error across BF16's full subnormal/normal range vs `bf16`'s `~7.8e-3` ULP spacing, >10⁹× margin).
- **GitHub hosted branch rules & merge enforcement:** `pr_gate_merge.tla` and `pr_gate_koth.tla` assume protected `main` without privileged bypass, `strict_required_status_checks_policy: true` on `gate`, and head-SHA-pinned merges (the hosted deferred auto-merge behavior for write-capable contributors remains an external GitHub platform assumption).
- **Differential equivalence scope:** `verify_state_machine_equiv.mjs` and `verify_ml_oracle.mjs` prove properties universally on the Lean executable specifications and verify exact equivalence to the JS implementations across exhaustive/adversarial suites rather than compiling JS via a verified compiler.

---

## Reproduce Locally

```sh
# Full formal verification suite (Lean builds + differential checks + all 4 TLC models)
npm run verify:formal

# Require TLC even locally (same command CI enforces)
TLA2TOOLS=/path/to/tla2tools.jar JAVA=/path/to/java npm run verify:formal -- --require-tlc

# Individual layers
node formal/verify_state_machine_equiv.mjs
node formal/verify_ml_oracle.mjs
node formal/verify_ui_machine.mjs
npm test
```

To inspect TLA+ counterexamples or redraw statecharts interactively, use the `/statechart` skill on any `formal/*.tla` model, or see [.claude/skills/verify-proof-foundry/SKILL.md](../.claude/skills/verify-proof-foundry/SKILL.md) for the project-local maintenance workflow.
