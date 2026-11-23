# Proof Foundry — Master Verified Catalog

> Auto-generated from conflict-free mission records. **33 Judge-verified proofs** (32 cross-model audited / frozen-matched) and **4 Judge-verified refutations** across 3 open-science missions.

**Trust Seal Legend:** `◆ Frozen` (kernel type-matched against frozen statement) · `✓ Audited` (independent cross-model faithfulness audit passed) · `◇ Provisional` (kernel verified, audit pending) · `⚠ Flagged` (audit found statement/title gap — does NOT count toward Objective completion) · `✕ Refuted` (Judge-verified counterexample).

## Erdős & Extremal Combinatorics (`erdos-combinatorics`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `E-ram-001` | ✓ Audited | The 5-cycle C5 contains neither a triangle nor a 3-independent set, proving R(3,3) > 5 | [E_ram_001.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_001.lean) | `none` | `36697e8874` |
| `E-ram-002` | ✓ Audited | Ramsey's Theorem R(3,3) ≤ 6: every simple graph on 6 vertices contains either a triangle or a 3-independent set | [E_ram_002.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_002.lean) | `propext` | `cf46d9f005` |
| `E-ram-003` | ✓ Audited | Circulant witness on 8 vertices proving R(3,4) > 8 (no 3-independent set and no K4) | [E_ram_003.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_003.lean) | `none` | `70beb304f0` |
| `E-tur-001` | ✓ Audited | Mantel's Theorem (1907): every triangle-free simple graph on n vertices has at most n² / 4 edges | [E_tur_001.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_tur_001.lean) | `propext, Quot.sound` | `c27432fc64` |
| `E-sch-001` | ✓ Audited | Exact Schur Number S(2) = 4: {1..4} admits a 2-color sum-free coloring, while every 2-coloring of {1..5} has a monochromatic x + y = z | [E_sch_001.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_001.lean) | `propext` | `786e23d8f5` |
| `E-sch-002` | ✓ Audited | Schur Lower Bound S(3) ≥ 13: explicit 3-color sum-free coloring of {1..13} verified in Lean 4 | [E_sch_002.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_002.lean) | `propext` | `742d0ea6a6` |
| `E-erd128-001` | ✓ Audited | Erdős #128 Bipartite Base Case: every bipartite graph on n vertices satisfies HasSparseHalf (an independent half of size ≥ n/2 has 0 ≤ n²/50 edges) | [E_erd128_001.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_001.lean) | `propext, Classical.choice, Quot.sound` | `4c9595134a` |
| `E-erd128-002` | ⚠ Flagged | Erdős #128 Tightness Witness: the 5-cycle C5 is triangle-free and satisfies HasSparseHalf with an independent set of size 2 = 5/2 | [E_erd128_002.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_002.lean) | `propext, Classical.choice, Quot.sound` | `6b985eb330` |
| `E-sch-003` | ✕ Refuted | CONJECTURE (Red Team Target): Every 3-coloring of {1..13} contains a monochromatic Schur triple x + y = z (i.e. S(3) ≤ 12) | [E_sch_003_refute.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_003_refute.lean) | `propext` | `b605bc16eb` |
| `E-erd156-001` | ✓ Audited | Erdős #156 Blocking Lemma: if A is a maximal Sidon subset of {1..N}, every x ∈ {1..N} \ A satisfies either x + a = b + c or 2x = a + b for some a, b, c ∈ A | [E_erd156_001.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_001.lean) | `propext, Quot.sound` | `071bd9aba9` |
| `E-erd156-002` | ✓ Audited | Erdős #156 Small-N Synthesis: construct and Lean-verify a maximal Sidon subset A ⊆ {1..30} of size at most 6 | [E_erd156_002.lean](./missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_002.lean) | `propext, Classical.choice, Quot.sound` | `4c090bd724` |

## P vs NP · Circuit & Proof Complexity (`p-vs-np`)
*Judge: Lean 4.36.0 kernel · zero sorry*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `L-lib-000` | ✓ Audited | Bit-flipping an input coordinate twice returns the original Boolean vector | [L_lib_000.lean](./lean/PnP/Lemmas/L_lib_000.lean) | `propext, Quot.sound` | `0f522adda1` |
| `L-lib-001` | ✓ Audited | Every monotone circuit computes a monotone Boolean function | [L_lib_001.lean](./lean/PnP/Lemmas/L_lib_001.lean) | `propext` | `d87422c5a7` |
| `L-lib-002` | ✓ Audited | A circuit that does not reference input wire i is invariant to flipping bit i | [L_lib_002.lean](./lean/PnP/Lemmas/L_lib_002.lean) | `propext` | `311fd21935` |
| `L-lib-003` | ✓ Audited | Polynomial bounds are closed under addition and multiplication | [L_lib_003.lean](./lean/PnP/Lemmas/L_lib_003.lean) | `propext, Quot.sound` | `5acf3da10b` |
| `L-clb-001` | ✓ Audited | Two-input XOR is not monotone, so no monotone circuit of any size computes it | [L_clb_001.lean](./lean/PnP/Lemmas/L_clb_001.lean) | `propext, Quot.sound` | `30acc6c5be` |
| `L-clb-002` | ✓ Audited | Every circuit computing a function that depends on input i must contain input leaf i | [L_clb_002.lean](./lean/PnP/Lemmas/L_clb_002.lean) | `propext` | `3565d82884` |
| `L-clb-003` | ✓ Audited | Any formula circuit using k distinct inputs needs at least k - 1 binary gates (hence n-bit parity needs ≥ n - 1 binary gates) | [L_clb_003.lean](./lean/PnP/Lemmas/L_clb_003.lean) | `propext, Classical.choice, Quot.sound` | `623811acef` |
| `L-clb-004` | ✓ Audited | Depth-size tradeoff: a formula circuit of depth d can reference at most 2^d input leaves | [L_clb_004.lean](./lean/PnP/Lemmas/L_clb_004.lean) | `propext, Classical.choice, Quot.sound` | `4704eba967` |
| `L-pcx-001` | ✓ Audited | Soundness of Resolution: every clause derivable by Resolution is implied by the CNF, so deriving the empty clause proves UNSAT | [L_pcx_001.lean](./lean/PnP/Lemmas/L_pcx_001.lean) | `propext, Quot.sound` | `4ad0f14cc4` |
| `L-pcx-002` | ✓ Audited | PHP(3, 2) — placing 3 pigeons into 2 holes — is unsatisfiable | [L_pcx_002.lean](./lean/PnP/Lemmas/L_pcx_002.lean) | `propext, Quot.sound` | `05db04ac93` |
| `L-pcx-003` | ✓ Audited | Any tree-like Resolution refutation (ResProof) of a CNF whose clauses all have list length ≥ 2 requires at least 3 proof nodes (tight: [[x,x],[¬x,¬x]] has size 3) | [L_pcx_003.lean](./lean/PnP/Lemmas/L_pcx_003.lean) | `propext, Quot.sound` | `ab517d937b` |
| `L-meta-001` | ✓ Audited | 3-bit Majority (MAJ3) is computable by a 4-gate monotone circuit and needs at least 2 binary gates | [L_meta_001.lean](./lean/PnP/Lemmas/L_meta_001.lean) | `propext, Classical.choice, Quot.sound` | `9c65f00941` |
| `L-meta-002` | ✓ Audited | No single-gate DAGCircuit over {NOT, AND, OR, XOR, CONST} computes 3-bit Majority | [L_meta_002.lean](./lean/PnP/Lemmas/L_meta_002.lean) | `propext, Quot.sound` | `825a84f689` |
| `L-alg-001` | ✓ Audited | Every Horn CNF in which every clause contains at least one negative literal is satisfied by the all-false assignment (excluding empty/positive-only clauses) | [L_alg_001.lean](./lean/PnP/Lemmas/L_alg_001.lean) | `propext, Quot.sound` | `eb738e0d90` |
| `L-alg-002` | ✕ Refuted | CONJECTURE (Red Team target): Every 3-CNF where every clause has at least 2 literals and each variable appears at most 3 times is satisfiable | [L_alg_002_refute.lean](./lean/PnP/Lemmas/L_alg_002_refute.lean) | `propext, Classical.choice, Quot.sound` | `fe302b01dd` |
| `L-alg-003` | ✕ Refuted | CONJECTURE (Red Team target): Every symmetric Boolean function on 3 variables is computed by a monotone circuit | [L_alg_003_refute.lean](./lean/PnP/Lemmas/L_alg_003_refute.lean) | `propext, Classical.choice, Quot.sound` | `0642b93cc9` |
| `L-lib-004` | ✓ Audited | B2 DAG Restriction: fixing an input wire preserves B2Circuit size whenever c.size > 0, outputWire ≠ n, or b = false (companion proof shows the 0-gate outputWire = n, b = true case requires 1 gate) | [L_lib_004.lean](./lean/PnP/Lemmas/L_lib_004.lean) | `propext, Classical.choice, Quot.sound` | `10382a6312` |
| `L-clb-005` | ✓ Audited | Shared-wire DAG Lower Bound: any B2Circuit computing a function that depends on all n inputs requires at least n - 1 gates | [L_clb_005.lean](./lean/PnP/Lemmas/L_clb_005.lean) | `propext, Classical.choice, Quot.sound` | `417fad10a9` |
| `L-clb-006` | ✓ Audited | Exact Ring Upper Bound: for every n ≥ 5, cyclic-adjacent-ones on an n-ring has a U2/B2 DAG circuit with at most n + (n + 1) / 2 - 1 gates | [L_clb_006.lean](./lean/PnP/Lemmas/L_clb_006.lean) | `propext, Classical.choice, Quot.sound` | `04c954ac4a` |
| `L-meta-003` | ✓ Audited | Exact B2 Circuit Complexity of MAJ3: 3-bit Majority requires at least 4 gates in the full binary basis B2 (matching the 4-gate upper bound gate for gate!) | [L_meta_003.lean](./lean/PnP/Lemmas/L_meta_003.lean) | `propext, Classical.choice, Quot.sound` | `ff984a1c14` |
| `L-meta-004` | ✕ Refuted | CONJECTURE (Red Team Synthesis Target): Every shared-wire B2 circuit computing 5-bit Majority (MAJ5) requires at least 11 gates | [L_meta_004_refute.lean](./lean/PnP/Lemmas/L_meta_004_refute.lean) | `propext, Quot.sound` | `47a7f9bcce` |
| `L-alg-004` | ✓ Audited | Synthesized Shared-Wire B2 Circuit for MOD3=0 on 4 bits: construct and verify a compact shared-wire B2Circuit 4 computing mod3Eq0 4 in ≤ 7 gates | [L_alg_004.lean](./lean/PnP/Lemmas/L_alg_004.lean) | `propext, Quot.sound` | `cfa12c7528` |
| `L-pcx-004` | ✓ Audited | Universal Pigeonhole Principle: for EVERY n : Nat, the CNF encoding PHP(n + 1, n) is unsatisfiable | [L_pcx_004.lean](./lean/PnP/Lemmas/L_pcx_004.lean) | `propext, Classical.choice, Quot.sound` | `269a64c739` |
| `L-pcx-005` | ✓ Audited | Qualitative Resolution Restriction: restricting a variable v := b maps any Resolution refutability (ResDerivable φ []) to a Resolution refutability of restrictCNF v b φ | [L_pcx_005.lean](./lean/PnP/Lemmas/L_pcx_005.lean) | `propext, Classical.choice, Quot.sound` | `c1d587f86a` |
| `L-bar-003` | ✓ Audited | Abstract Oracle-Barrier Conditional: if oracle-indexed propositions P_O, NP_O agree on some oracle A and disagree on some oracle B, neither ∀ O, P_O O ≠ NP_O O nor ∀ O, P_O O = NP_O O holds | [L_bar_003.lean](./lean/PnP/Lemmas/L_bar_003.lean) | `none` | `1537cd2f65` |

## Verified Scientific & Numerical Kernels (`verified-science-kernels`)
*Judge: Deterministic IEEE-754 Stress Judge*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `S-num-001` | ✓ Audited | Neumaier-compensated summation preserves exact sums across 1e16 and 1e100 catastrophic cancellation | [S_num_001.mjs](./missions/verified-science-kernels/artifacts/S_num_001.mjs) | `catastrophic_1e16_cancel, neumaier_1e100_cancel` | `b4b66491cb` |

