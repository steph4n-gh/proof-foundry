# Proof Foundry — Master Verified Catalog

> Auto-generated from conflict-free mission records. **34 Judge-verified proofs** (33 cross-model audited / frozen-matched), **4 Judge-verified refutations**, and **18 King-of-the-Hill auto-ratcheting record hunts** across 6 open-science missions.

**Trust Seal Legend:** `◆ Frozen` (kernel type-matched against frozen statement) · `♛ Record` (active King-of-the-Hill holder — open to beat!) · `✓ Audited` (cross-model faithfulness audit passed) · `◇ Provisional` (kernel verified, audit pending) · `⚠ Flagged` (audit found statement/title gap) · `✕ Refuted` (Judge-verified counterexample).

## King of the Hill — Live Auto-Ratcheting Record Hunts

| Mission | ID | Target | Current Best | Next Target | Proven Bound | Holder | Status |
|---|---|---|---|---|---|---|---|
| `erdos-combinatorics` | `E-rec-200` | King of the Hill (Erdős #156): Smallest Maximal Sidon Subset of {1..200} (Greedy = 14, Search ≤ 11) | *(unclaimed, ceiling 14)* | `≤ 14` | *(lit. ≥ 6)* | — | ○ Open Hunt |
| `erdos-combinatorics` | `E-rec-r55` | King of the Hill (MAXIMIZE · Open Prize): Largest K5- & I5-Free Graph for Ramsey R(5,5) (Record = 42, UB = 47) | *(unclaimed, floor 36)* | `≥ 36` | *(lit. ≤ 47)* | — | ○ Open Hunt |
| `erdos-combinatorics` | `E-rec-gol11` | King of the Hill: Shortest 11-Mark Golomb Ruler (Greedy = 97, Exact Optimum = 72) | *(unclaimed, ceiling 88)* | `≤ 88` | *(lit. ≥ 72)* | — | ○ Open Hunt |
| `error-correcting-codes` | `EC-rec-17-6` | King of the Hill: Binary Code A(17,6) (World Record = 258, Upper Bound = 340) | *(unclaimed, floor 256)* | `≥ 256` | *(lit. ≤ 340)* | — | ○ Open Hunt |
| `error-correcting-codes` | `EC-rec-17-6-7` | King of the Hill: Constant-Weight Code A(17,6,7) (World Record = 166, Upper Bound = 206) | *(unclaimed, floor 166)* | `≥ 166` | *(lit. ≤ 206)* | — | ○ Open Hunt |
| `error-correcting-codes` | `EC-rec-20-8-10` | King of the Hill: Constant-Weight Code A(20,8,10) (World Record = 176, Upper Bound = 206) | *(unclaimed, floor 176)* | `≥ 176` | *(lit. ≤ 206)* | — | ○ Open Hunt |
| `fast-matrix-mul` | `MM-rec-3x3x4` | 3×3 by 3×4 over the integers | *(unclaimed, ceiling 29)* | `≤ 29` | *(lit. ≥ 25)* | — | ○ Open Hunt |
| `fast-matrix-mul` | `MM-rec-4x4-f2` | 4×4 by 4×4 over GF(2) | *(unclaimed, ceiling 49)* | `≤ 49` | *(lit. ≥ 34)* | — | ○ Open Hunt |
| `fast-matrix-mul` | `MM-rec-3x4x5` | 3×4 by 4×5 over the integers | *(unclaimed, ceiling 47)* | `≤ 47` | *(lit. ≥ 34)* | — | ○ Open Hunt |
| `p-vs-np` | `L-rec-005` | King of the Hill: Lean 4 Certification of Exact Well-Formed B2 Circuit Size for MOD3=0 on 5 Bits (Known Optimum = 10) | *(unclaimed, ceiling 12)* | `≤ 12` | *(lit. ≥ 10)* | — | ○ Open Hunt |
| `p-vs-np` | `L-rec-maj5` | King of the Hill: Exact Well-Formed B2 Circuit Size for 5-Bit Majority MAJ5 (Known Optimum = 10) | *(unclaimed, ceiling 12)* | `≤ 12` | *(lit. ≥ 10)* | — | ○ Open Hunt |
| `p-vs-np` | `L-rec-php4` | King of the Hill: Shortest Tree-Like Resolution Proof of Pigeonhole Principle PHP(4,3) | *(unclaimed, ceiling 105)* | `≤ 105` | *(lit. ≥ 31)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-013` | King of the Hill: 13-Wire Sorting Network Size (World Record = 45, Proven Lower Bound = 43) | *(unclaimed, ceiling 46)* | `≤ 46` | *(lit. ≥ 43)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-014` | King of the Hill: 14-Wire Sorting Network Size (World Record = 51, Proven Lower Bound = 47) | *(unclaimed, ceiling 52)* | `≤ 52` | *(lit. ≥ 47)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-015` | King of the Hill: 15-Wire Sorting Network Size (World Record = 56, Proven Lower Bound = 51) | *(unclaimed, ceiling 58)* | `≤ 58` | *(lit. ≥ 51)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-d17` | King of the Hill: 17-Wire Parallel Depth (OPEN WORLD RECORD: Current = 10, Proven LB = 9) | *(unclaimed, ceiling 11)* | `≤ 11` | *(lit. ≥ 9)* | — | ○ Open Hunt |
| `verified-science-kernels` | `S-rec-exp` | King of the Hill: Minimax Degree-7 Float64 Polynomial for exp(x) on [-ln2/2, ln2/2] (128-bit BigInt Oracle) | *(unclaimed, ceiling 500)* | `≤ 500` | *(lit. ≥ 380)* | — | ○ Open Hunt |
| `verified-science-kernels` | `S-rec-sin` | King of the Hill: Minimax Degree-7 Odd Float64 Polynomial for sin(x) on [-π/4, π/4] (128-bit BigInt Oracle) | *(unclaimed, ceiling 1500)* | `≤ 1500` | *(lit. ≥ 1100)* | — | ○ Open Hunt |

## Erdős & Extremal Combinatorics (`erdos-combinatorics`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `E-ram-001` | ✓ Audited | The 5-cycle C5 contains neither a triangle nor a 3-independent set, proving R(3,3) > 5 | [E_ram_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_001.lean) | `none` | `36697e8874` |
| `E-ram-002` | ✓ Audited | Ramsey's Theorem R(3,3) ≤ 6: every simple graph on 6 vertices contains either a triangle or a 3-independent set | [E_ram_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_002.lean) | `propext` | `cf46d9f005` |
| `E-ram-003` | ✓ Audited | Circulant witness on 8 vertices proving R(3,4) > 8 (no 3-independent set and no K4) | [E_ram_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_003.lean) | `none` | `70beb304f0` |
| `E-tur-001` | ✓ Audited | Mantel's Theorem (1907): every triangle-free simple graph on n vertices has at most n² / 4 edges | [E_tur_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_tur_001.lean) | `propext, Quot.sound` | `c27432fc64` |
| `E-sch-001` | ✓ Audited | Exact Schur Number S(2) = 4: {1..4} admits a 2-color sum-free coloring, while every 2-coloring of {1..5} has a monochromatic x + y = z | [E_sch_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_001.lean) | `propext` | `786e23d8f5` |
| `E-sch-002` | ✓ Audited | Schur Lower Bound S(3) ≥ 13: explicit 3-color sum-free coloring of {1..13} verified in Lean 4 | [E_sch_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_002.lean) | `propext` | `742d0ea6a6` |
| `E-erd128-001` | ✓ Audited | Erdős #128 Bipartite Base Case: every bipartite graph on n vertices satisfies HasSparseHalf (an independent half of size ≥ n/2 has 0 ≤ n²/50 edges) | [E_erd128_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_001.lean) | `propext, Classical.choice, Quot.sound` | `4c9595134a` |
| `E-erd128-002` | ⚠ Flagged | Erdős #128 Tightness Witness: the 5-cycle C5 is triangle-free and satisfies HasSparseHalf with an independent set of size 2 = 5/2 | [E_erd128_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_002.lean) | `propext, Classical.choice, Quot.sound` | `6b985eb330` |
| `E-sch-003` | ✕ Refuted | CONJECTURE (Red Team Target): Every 3-coloring of {1..13} contains a monochromatic Schur triple x + y = z (i.e. S(3) ≤ 12) | [E_sch_003_refute.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_003_refute.lean) | `propext` | `b605bc16eb` |
| `E-erd156-001` | ✓ Audited | Erdős #156 Blocking Lemma: if A is a maximal Sidon subset of {1..N}, every x ∈ {1..N} \ A satisfies either x + a = b + c or 2x = a + b for some a, b, c ∈ A | [E_erd156_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_001.lean) | `propext, Quot.sound` | `071bd9aba9` |
| `E-erd156-002` | ✓ Audited | Erdős #156 Small-N Synthesis: construct and Lean-verify a maximal Sidon subset A ⊆ {1..30} of size at most 6 | [E_erd156_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_002.lean) | `propext, Classical.choice, Quot.sound` | `4c090bd724` |
| `E-erd128-003` | ◆ Frozen | Erdős #128 Exact n=10 Sharpness: exhibit a triangle-free 10-vertex graph (e.g. C5[2] or Petersen) achieving 50·e(S) ≥ 100 on every ≥5-vertex half and exact equality 50·e(S) = 100 | [E_erd128_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_003.lean) | `propext, Quot.sound` | `c74fe84b59` |

## Error-Correcting Codes (Sloane & Grassl Open World Tables) (`error-correcting-codes`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*

_No closed proofs yet (see King of the Hill hunts above or open bounties on the dashboard)._

## Fast Matrix Multiplication · Strassen / AlphaTensor Frontier (`fast-matrix-mul`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*

_No closed proofs yet (see King of the Hill hunts above or open bounties on the dashboard)._

## P vs NP · Circuit & Proof Complexity (`p-vs-np`)
*Judge: Lean 4.36.0 kernel · zero sorry*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `L-lib-000` | ✓ Audited | Bit-flipping an input coordinate twice returns the original Boolean vector | [L_lib_000.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_lib_000.lean) | `propext, Quot.sound` | `0f522adda1` |
| `L-lib-001` | ✓ Audited | Every monotone circuit computes a monotone Boolean function | [L_lib_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_lib_001.lean) | `propext` | `d87422c5a7` |
| `L-lib-002` | ✓ Audited | A circuit that does not reference input wire i is invariant to flipping bit i | [L_lib_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_lib_002.lean) | `propext` | `311fd21935` |
| `L-lib-003` | ✓ Audited | Polynomial bounds are closed under addition and multiplication | [L_lib_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_lib_003.lean) | `propext, Quot.sound` | `5acf3da10b` |
| `L-clb-001` | ✓ Audited | Two-input XOR is not monotone, so no monotone circuit of any size computes it | [L_clb_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_001.lean) | `propext, Quot.sound` | `30acc6c5be` |
| `L-clb-002` | ✓ Audited | Every circuit computing a function that depends on input i must contain input leaf i | [L_clb_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_002.lean) | `propext` | `3565d82884` |
| `L-clb-003` | ✓ Audited | Any formula circuit using k distinct inputs needs at least k - 1 binary gates (hence n-bit parity needs ≥ n - 1 binary gates) | [L_clb_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_003.lean) | `propext, Classical.choice, Quot.sound` | `623811acef` |
| `L-clb-004` | ✓ Audited | Depth-size tradeoff: a formula circuit of depth d can reference at most 2^d input leaves | [L_clb_004.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_004.lean) | `propext, Classical.choice, Quot.sound` | `4704eba967` |
| `L-pcx-001` | ✓ Audited | Soundness of Resolution: every clause derivable by Resolution is implied by the CNF, so deriving the empty clause proves UNSAT | [L_pcx_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_pcx_001.lean) | `propext, Quot.sound` | `4ad0f14cc4` |
| `L-pcx-002` | ✓ Audited | PHP(3, 2) — placing 3 pigeons into 2 holes — is unsatisfiable | [L_pcx_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_pcx_002.lean) | `propext, Quot.sound` | `05db04ac93` |
| `L-pcx-003` | ✓ Audited | Any tree-like Resolution refutation (ResProof) of a CNF whose clauses all have list length ≥ 2 requires at least 3 proof nodes (tight: [[x,x],[¬x,¬x]] has size 3) | [L_pcx_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_pcx_003.lean) | `propext, Quot.sound` | `ab517d937b` |
| `L-meta-001` | ✓ Audited | 3-bit Majority (MAJ3) is computable by a 4-gate monotone circuit and needs at least 2 binary gates | [L_meta_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_meta_001.lean) | `propext, Classical.choice, Quot.sound` | `9c65f00941` |
| `L-meta-002` | ✓ Audited | No single-gate DAGCircuit over {NOT, AND, OR, XOR, CONST} computes 3-bit Majority | [L_meta_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_meta_002.lean) | `propext, Quot.sound` | `825a84f689` |
| `L-alg-001` | ✓ Audited | Every Horn CNF in which every clause contains at least one negative literal is satisfied by the all-false assignment (excluding empty/positive-only clauses) | [L_alg_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_alg_001.lean) | `propext, Quot.sound` | `eb738e0d90` |
| `L-alg-002` | ✕ Refuted | CONJECTURE (Red Team target): Every 3-CNF where every clause has at least 2 literals and each variable appears at most 3 times is satisfiable | [L_alg_002_refute.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_alg_002_refute.lean) | `propext, Classical.choice, Quot.sound` | `fe302b01dd` |
| `L-alg-003` | ✕ Refuted | CONJECTURE (Red Team target): Every symmetric Boolean function on 3 variables is computed by a monotone circuit | [L_alg_003_refute.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_alg_003_refute.lean) | `propext, Classical.choice, Quot.sound` | `0642b93cc9` |
| `L-lib-004` | ✓ Audited | B2 DAG Restriction: fixing an input wire preserves B2Circuit size whenever c.size > 0, outputWire ≠ n, or b = false (companion proof shows the 0-gate outputWire = n, b = true case requires 1 gate) | [L_lib_004.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_lib_004.lean) | `propext, Classical.choice, Quot.sound` | `10382a6312` |
| `L-clb-005` | ✓ Audited | Shared-wire DAG Lower Bound: any B2Circuit computing a function that depends on all n inputs requires at least n - 1 gates | [L_clb_005.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_005.lean) | `propext, Classical.choice, Quot.sound` | `417fad10a9` |
| `L-clb-006` | ✓ Audited | Exact Ring Upper Bound: for every n ≥ 5, cyclic-adjacent-ones on an n-ring has a U2/B2 DAG circuit with at most n + (n + 1) / 2 - 1 gates | [L_clb_006.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_clb_006.lean) | `propext, Classical.choice, Quot.sound` | `04c954ac4a` |
| `L-meta-003` | ✓ Audited | Exact B2 Circuit Complexity of MAJ3: 3-bit Majority requires at least 4 gates in the full binary basis B2 (matching the 4-gate upper bound gate for gate!) | [L_meta_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_meta_003.lean) | `propext, Classical.choice, Quot.sound` | `ff984a1c14` |
| `L-meta-004` | ✕ Refuted | CONJECTURE (Red Team Synthesis Target): Every shared-wire B2 circuit computing 5-bit Majority (MAJ5) requires at least 11 gates | [L_meta_004_refute.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_meta_004_refute.lean) | `propext, Quot.sound` | `47a7f9bcce` |
| `L-alg-004` | ✓ Audited | Synthesized Shared-Wire B2 Circuit for MOD3=0 on 4 bits: construct and verify a compact shared-wire B2Circuit 4 computing mod3Eq0 4 in ≤ 7 gates | [L_alg_004.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_alg_004.lean) | `propext, Quot.sound` | `cfa12c7528` |
| `L-pcx-004` | ✓ Audited | Universal Pigeonhole Principle: for EVERY n : Nat, the CNF encoding PHP(n + 1, n) is unsatisfiable | [L_pcx_004.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_pcx_004.lean) | `propext, Classical.choice, Quot.sound` | `269a64c739` |
| `L-pcx-005` | ✓ Audited | Qualitative Resolution Restriction: restricting a variable v := b maps any Resolution refutability (ResDerivable φ []) to a Resolution refutability of restrictCNF v b φ | [L_pcx_005.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_pcx_005.lean) | `propext, Classical.choice, Quot.sound` | `c1d587f86a` |
| `L-bar-003` | ✓ Audited | Abstract Oracle-Barrier Conditional: if oracle-indexed propositions P_O, NP_O agree on some oracle A and disagree on some oracle B, neither ∀ O, P_O O ≠ NP_O O nor ∀ O, P_O O = NP_O O holds | [L_bar_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_bar_003.lean) | `none` | `1537cd2f65` |

## Optimal Sorting Networks (Knuth Open Frontier) (`sorting-networks`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*

_No closed proofs yet (see King of the Hill hunts above or open bounties on the dashboard)._

## Verified Scientific & Numerical Kernels (`verified-science-kernels`)
*Judge: Deterministic IEEE-754 Stress Judge*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `S-num-001` | ✓ Audited | Neumaier-compensated summation preserves exact sums across 1e16 and 1e100 catastrophic cancellation | [S_num_001.mjs](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/verified-science-kernels/artifacts/S_num_001.mjs) | `catastrophic_1e16_cancel, neumaier_1e100_cancel` | `b4b66491cb` |

