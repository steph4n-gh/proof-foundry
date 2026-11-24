# Proof Foundry — Master Verified Catalog

> Auto-generated from conflict-free mission records. **33 Judge-verified proofs** (33 cross-model audited / frozen-matched), **4 Judge-verified refutations**, and **32 King-of-the-Hill auto-ratcheting record hunts** across 7 open-science missions.

**Trust Seal Legend:** `◆ Frozen` (kernel type-matched against frozen statement) · `♛ Record` (active King-of-the-Hill holder — open to beat!) · `✓ Audited` (cross-model faithfulness audit passed) · `◇ Provisional` (kernel verified, audit pending) · `⚠ Flagged` (audit found statement/title gap) · `✕ Refuted` (Judge-verified counterexample).

## Where Verified Proofs Ship (Direct Real-World Impact)

> Full real-world impact breakdown & drop-in integration examples: [docs/REAL_WORLD_IMPACT.md](./docs/REAL_WORLD_IMPACT.md).

| Mission | Impact Tier | Ships Directly To | What One Step Buys |
|---|---|---|---|
| `crypto-zk-circuits` | **Direct production impact** | TFHE / OpenFHE, MP-SPDZ, NIST SP 800-232 Ascon, masked AES silicon, ZK circuits | Removing 1 AND gate from the AES S-box saves 160 Beaver triples per AES-128 encryption across every MPC protocol and cuts masked ASIC S-box area by ~3%. |
| `error-correcting-codes` | **Direct production impact** | DNA multiplexing barcodes (Illumina/Twist), NVMe/NAND flash ECC, optical/deep-space short-block FEC, Brouwer's tables | Adding +1 verified codeword to A(17,6), A(17,6,7), or A(20,8,10) permanently expands multiplexing capacity at identical error-correction strength (2–3 bit errors corrected) and updates Brouwer's decades-old world tables. |
| `fast-matrix-mul` | **Direct production impact** | BLIS / OpenBLAS, CUTLASS / Triton GEMM, GF(2) crypto & erasure coding, NumPy/SciPy | Cutting 1 scalar multiplication in a 3×3×3 or 4×4×4 base kernel compounds exponentially across recursive block levels (r^L vs 27^L); shaving additions with {-1,0,1} coefficients directly lowers the crossover matrix size where fast GEMM beats schoolbook in real BLAS libraries. |
| `ml-math-kernels` | **Direct production impact** | FlashAttention, Triton, PyTorch Inductor, vLLM, TensorRT-LLM, llama.cpp | Each branchless FMA/ALU op shaved off an exhaustively verified ≤1-ULP bf16 kernel directly lowers register pressure and instruction count across trillions of daily inference tokens with a 100% mathematical guarantee of zero NaN/edge-case regressions. |
| `sorting-networks` | **Direct production impact** | LLVM libc++ std::sort, Google Highway (vqsort), DuckDB, NVIDIA CUB / Thrust GPU warp sort, FPGA pipelines | Removing 1 comparator or 1 parallel layer from a 16-wire network speeds up every AVX-512 (16×32-bit) and CUDA half-warp base sort in databases, search engines, and standard libraries — permanently, with zero branch mispredictions. |
| `quantum-codes` | **Applied research frontier** | Neutral-atom arrays (QuEra/Atom), trapped ions (Quantinuum), superconducting qLDPC (IBM Gross/Bivariate Bicycle) | Increasing logical qubits k by +1 at fixed physical count n, distance d, and check weight w ≤ 6 directly raises hardware encoding rate k/n with zero extra physical qubits. |
| `p-vs-np` | **Foundational / theoretical** | EDA logic synthesis (ABC / Yosys), SAT proof compression (DRAT/LRAT), circuit-complexity benchmarks | Shrinking an exact B2 circuit for MAJ7 or MOD3_6 by 1 gate improves exact peephole rewriting libraries used by logic synthesizers (ABC/Mockturtle) and pins down open entries in Knuth/Kulikov's exact circuit tables. |

## King of the Hill — Live Auto-Ratcheting Record Hunts

| Mission | ID | Target | Current Best | Next Target | Proven Bound | Holder | Status |
|---|---|---|---|---|---|---|---|
| `crypto-zk-circuits` | `CZ-rec-ascon-gates` | King of the Hill: NIST Ascon 5-Bit S-Box Total B2 Gates (at ≤ 5 ANDs, Depth ≤ 1) | **16** gates | `≤ 15` | *(lit. ≥ 13)* | `donor-foundry-seed` | ♛ Active Hunt |
| `crypto-zk-circuits` | `CZ-rec-present-gates` | King of the Hill: ISO PRESENT 4-Bit S-Box Total B2 Gates (at ≤ 4 ANDs) | *(unclaimed, ceiling 16)* | `≤ 16` | *(lit. ≥ 10)* | — | ○ Open Hunt |
| `crypto-zk-circuits` | `CZ-rec-skinny4-gates` | King of the Hill: SKINNY 4-Bit S-Box Total B2 Gates | *(unclaimed, ceiling 12)* | `≤ 12` | *(lit. ≥ 6)* | — | ○ Open Hunt |
| `crypto-zk-circuits` | `CZ-rec-aes-and` | King of the Hill: FIPS-197 AES 8-Bit S-Box Multiplicative Complexity (Boyar–Peralta Record = 32 ANDs) | *(unclaimed, ceiling 34)* | `≤ 34` | *(lit. ≥ 12)* | — | ○ Open Hunt |
| `crypto-zk-circuits` | `CZ-rec-aes-total` | King of the Hill: FIPS-197 AES 8-Bit S-Box Total B2 Gates at AND-Depth ≤ 4 (Record = 113 Gates) | *(unclaimed, ceiling 120)* | `≤ 120` | *(lit. ≥ 64)* | — | ○ Open Hunt |
| `error-correcting-codes` | `EC-rec-17-6` | King of the Hill: Binary Code A(17,6) (World Record = 258, Upper Bound = 340) | **256** codewords | `≥ 257` | *(lit. ≤ 340)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `error-correcting-codes` | `EC-rec-17-6-7` | King of the Hill: Constant-Weight Code A(17,6,7) (World Record = 166, Upper Bound = 206) | **166** codewords | `≥ 167` | *(lit. ≤ 206)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `error-correcting-codes` | `EC-rec-20-8-10` | King of the Hill: Constant-Weight Code A(20,8,10) (World Record = 176, Upper Bound = 206) | **176** codewords | `≥ 177` | *(lit. ≤ 206)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `fast-matrix-mul` | `MM-rec-3x3x4` | 3×3 by 3×4 over the integers | **29** products | `≤ 28` | *(lit. ≥ 25)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `fast-matrix-mul` | `MM-rec-4x4-f2` | 4×4 by 4×4 over GF(2) | **47** products | `≤ 46` | *(lit. ≥ 34)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `fast-matrix-mul` | `MM-rec-3x4x5` | 3×4 by 4×5 over the integers | **47** products | `≤ 46` | *(lit. ≥ 34)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `fast-matrix-mul` | `MM-rec-3x3x3` | King of the Hill: 3×3 by 3×3 over the integers (Laderman 1976 Record = 23, LB = 19) | *(unclaimed, ceiling 23)* | `≤ 23` | *(lit. ≥ 19)* | — | ○ Open Hunt |
| `fast-matrix-mul` | `MM-rec-3x3x3-hw` | King of the Hill: Hardware-Friendly 3×3×3 Scheme (Rank ≤ 23, {-1,0,1} Coeffs, Minimum Additions) | *(unclaimed, ceiling 105)* | `≤ 105` | *(lit. ≥ 30)* | — | ○ Open Hunt |
| `ml-math-kernels` | `ML-rec-bf16-rsqrt` | King of the Hill: Exhaustive BF16 rsqrt(x) = 1/sqrt(x) at ≤ 1 ULP (65,536/65,536 Inputs) | **17** ALU/FMA ops | `≤ 16` | *(lit. ≥ 6)* | `donor-foundry-seed` | ♛ Active Hunt |
| `ml-math-kernels` | `ML-rec-bf16-exp2` | King of the Hill: Exhaustive BF16 exp2(x) = 2^x at ≤ 1 ULP (65,536/65,536 Inputs) | **18** ALU/FMA ops | `≤ 17` | *(lit. ≥ 7)* | `donor-foundry-seed` | ♛ Active Hunt |
| `ml-math-kernels` | `ML-rec-bf16-silu` | King of the Hill: Exhaustive BF16 SiLU(x) = x / (1 + e^-x) at ≤ 1 ULP (65,536/65,536 Inputs) | **31** ALU/FMA ops | `≤ 30` | *(lit. ≥ 9)* | `donor-foundry-seed` | ♛ Active Hunt |
| `ml-math-kernels` | `ML-rec-bf16-gelu` | King of the Hill: Exhaustive BF16 Exact GELU(x) = 0.5·x·(1 + erf(x/√2)) at ≤ 1 ULP (65,536/65,536 Inputs) | *(unclaimed, ceiling 32)* | `≤ 32` | *(lit. ≥ 9)* | — | ○ Open Hunt |
| `p-vs-np` | `L-rec-005` | King of the Hill: Lean 4 Certification of Exact Well-Formed B2 Circuit Size for MOD3=0 on 5 Bits (Known Optimum = 10) | **10** B2 gates | `≤ 9` | *(lit. ≥ 10)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `p-vs-np` | `L-rec-maj5` | King of the Hill: Exact Well-Formed B2 Circuit Size for 5-Bit Majority MAJ5 (Known Optimum = 10) | **10** B2 gates | `≤ 9` | *(lit. ≥ 10)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `p-vs-np` | `L-rec-php4` | King of the Hill: Shortest Tree-Like Resolution Proof of Pigeonhole Principle PHP(4,3) | **85** proof nodes | `≤ 84` | *(lit. ≥ 31)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `p-vs-np` | `L-rec-mod3-6` | King of the Hill: Exact Well-Formed B2 Circuit Size for MOD3=0 on 6 Bits (Open Frontier: Best Known = 13, LB = 11) | *(unclaimed, ceiling 16)* | `≤ 16` | *(lit. ≥ 11)* | — | ○ Open Hunt |
| `p-vs-np` | `L-rec-maj7` | King of the Hill: Exact Well-Formed B2 Circuit Size for 7-Bit Majority MAJ7 (Open Frontier: Best Known = 16, LB = 12) | *(unclaimed, ceiling 20)* | `≤ 20` | *(lit. ≥ 12)* | — | ○ Open Hunt |
| `quantum-codes` | `QC-rec-n15-d3-w4` | King of the Hill: Ultra-Low-Weight [[15, k, 3]] CSS Code (Check Weight ≤ 4) | *(unclaimed, floor 1)* | `≥ 1` | *(lit. ≤ 7)* | — | ○ Open Hunt |
| `quantum-codes` | `QC-rec-n16-d4-w6` | King of the Hill: Distance-4 qLDPC [[16, k, 4]] CSS Code (Check Weight ≤ 6) | **2** logical qubits | `≥ 3` | *(lit. ≤ 6)* | `donor-foundry-seed` | ♛ Active Hunt |
| `quantum-codes` | `QC-rec-n18-d4-w6` | King of the Hill: Distance-4 qLDPC [[18, k, 4]] CSS Code (Check Weight ≤ 6) | *(unclaimed, floor 2)* | `≥ 2` | *(lit. ≤ 8)* | — | ○ Open Hunt |
| `quantum-codes` | `QC-rec-n20-d4-w6` | King of the Hill: Distance-4 qLDPC [[20, k, 4]] CSS Code (Check Weight ≤ 6) | *(unclaimed, floor 2)* | `≥ 2` | *(lit. ≤ 10)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-013` | King of the Hill: 13-Wire Sorting Network Size (Exact Optimum S(13) = 45 · Tomar 2026 Lean 4 LB = 45) | **45** comparators | `≤ 44` | *(lit. ≥ 45)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `sorting-networks` | `SN-rec-014` | King of the Hill: 14-Wire Sorting Network Size (World Record = 51, Tomar 2026 LB = 50) | **51** comparators | `≤ 50` | *(lit. ≥ 50)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `sorting-networks` | `SN-rec-015` | King of the Hill: 15-Wire Sorting Network Size (World Record = 56, Proven LB = 54) | **56** comparators | `≤ 55` | *(lit. ≥ 54)* | `donor-steph4n-gh` | ♛ Active Hunt |
| `sorting-networks` | `SN-rec-d17` | King of the Hill: 17-Wire Parallel Depth (OPEN WORLD RECORD: Current = 10, Proven LB = 9) | *(unclaimed, ceiling 11)* | `≤ 11` | *(lit. ≥ 9)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-016` | King of the Hill: 16-Wire AVX-512 / GPU Half-Warp Sorting Network Size (Green 1969 Record = 60, Tomar 2026 LB = 59) | *(unclaimed, ceiling 62)* | `≤ 62` | *(lit. ≥ 59)* | — | ○ Open Hunt |
| `sorting-networks` | `SN-rec-d16` | King of the Hill: 16-Wire AVX-512 / FPGA Parallel Depth (Exact Optimum = 9 Layers, Beats Batcher's 10) | *(unclaimed, ceiling 10)* | `≤ 10` | *(lit. ≥ 9)* | — | ○ Open Hunt |

## Cryptographic & ZK/FHE Circuit Minimization (`crypto-zk-circuits`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*
*Direct production impact · Ships to: TFHE / OpenFHE, MP-SPDZ, NIST SP 800-232 Ascon, masked AES silicon, ZK circuits*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `CZ-001` | ◆ Frozen | NIST SP 800-232 Ascon 5-bit S-box: 5 non-linear (AND) gates at multiplicative depth 1 | [CZ_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/crypto-zk-circuits/lean/Crypto/Claims/CZ_001.lean) | `propext, Classical.choice, Quot.sound` | `bd354ffcce` |

## Error-Correcting Codes (Sloane & Grassl Open World Tables) (`error-correcting-codes`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*
*Direct production impact · Ships to: DNA multiplexing barcodes (Illumina/Twist), NVMe/NAND flash ECC, optical/deep-space short-block FEC, Brouwer's tables*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `EC-001` | ◆ Frozen | Hamming [7,4,3] code: 16 binary words of length 7 with minimum distance 3 (A(7,3) ≥ 16) | [EC_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/error-correcting-codes/lean/Codes/Claims/EC_001.lean) | `propext, Classical.choice, Quot.sound` | `4e97401235` |
| `EC-002` | ◆ Frozen | Hamming sphere-packing bound: every distance-3 binary code of length n has \|C\|·(n+1) ≤ 2^n | [EC_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/error-correcting-codes/lean/Codes/Claims/EC_002.lean) | `propext, Classical.choice, Quot.sound` | `738d58683c` |

## Fast Matrix Multiplication · Strassen / AlphaTensor Frontier (`fast-matrix-mul`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*
*Direct production impact · Ships to: BLIS / OpenBLAS, CUTLASS / Triton GEMM, GF(2) crypto & erasure coding, NumPy/SciPy*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `MM-001` | ◆ Frozen | Strassen’s seven products over the integers | [MM_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/fast-matrix-mul/lean/MatMul/Claims/MM_001.lean) | `propext, Classical.choice, Quot.sound` | `ff929acec6` |
| `MM-002` | ◆ Frozen | Strassen’s seven products over GF(2) | [MM_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/fast-matrix-mul/lean/MatMul/Claims/MM_002.lean) | `propext` | `7ce82683fe` |
| `MM-003` | ◆ Frozen | Compose integer schemes by tensor product | [MM_003.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/fast-matrix-mul/lean/MatMul/Claims/MM_003.lean) | `propext, Classical.choice, Quot.sound` | `7f85272424` |

## Exhaustively Verified BF16 GPU & ML Math Kernels (`ml-math-kernels`)
*Judge: Exhaustive 65,536-Input BF16 Pure-Data Judge (zero JS exec)*
*Direct production impact · Ships to: FlashAttention, Triton, PyTorch Inductor, vLLM, TensorRT-LLM, llama.cpp*

_No closed proofs yet (see King of the Hill hunts above or open bounties on the dashboard)._

## P vs NP · Circuit & Proof Complexity (`p-vs-np`)
*Judge: Lean 4.36.0 kernel · zero sorry*
*Foundational / theoretical · Ships to: EDA logic synthesis (ABC / Yosys), SAT proof compression (DRAT/LRAT), circuit-complexity benchmarks*

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
| `L-meta-005` | ◆ Frozen | Exact U2 complexity of XOR2: without XOR/XNOR gates, 2-bit parity needs exactly 3 gates | [L_meta_005.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_meta_005.lean) | `propext, Quot.sound` | `9b2b28c80c` |
| `L-syn-001` | ◆ Frozen | Shared-Wire B2 Circuit for MOD3=0 on 4 Bits: synthesize an ≤ 8-gate B2 DAG circuit computing mod3Eq0 4 | [L_syn_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_syn_001.lean) | `propext, Quot.sound` | `0c5296687c` |
| `L-syn-002` | ✕ Refuted | FRONTIER CONTEST (Exact MAJ5): Does 5-bit Majority require ≥ 10 gates in full B2 (or can someone beat our 10-gate circuit)? Prove OR refute! | [L_syn_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/lean/PnP/Lemmas/L_syn_002.lean) | `propext, Quot.sound` | `1380483be0` |

## Quantum LDPC & CSS Stabilizer Codes (`quantum-codes`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*
*Applied research frontier · Ships to: Neutral-atom arrays (QuEra/Atom), trapped ions (Quantinuum), superconducting qLDPC (IBM Gross/Bivariate Bicycle)*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `QC-001` | ◆ Frozen | Steane [[7, 1, 3]] CSS code with weight-4 stabilizers | [QC_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/quantum-codes/lean/Quantum/Claims/QC_001.lean) | `propext, Classical.choice, Quot.sound` | `998523f4e4` |

## Optimal Sorting Networks (Knuth Open Frontier) (`sorting-networks`)
*Judge: Lean 4.36.0 kernel · frozen statements · zero sorry*
*Direct production impact · Ships to: LLVM libc++ std::sort, Google Highway (vqsort), DuckDB, NVIDIA CUB / Thrust GPU warp sort, FPGA pipelines*

| ID | Seal | Plain Statement | Artifact | Axioms / Checks | SHA-256 |
|---|---|---|---|---|---|
| `SN-001` | ◆ Frozen | Knuth's Zero-One Principle: any comparator network that sorts all 0/1 inputs sorts all natural-number inputs | [SN_001.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/sorting-networks/lean/SortNet/Claims/SN_001.lean) | `propext, Quot.sound` | `2a05a3bbc5` |
| `SN-002` | ◆ Frozen | Optimal 4-wire (5 steps, depth 3) & 5-wire (9 steps, depth 5) sorting networks | [SN_002.lean](https://github.com/steph4n-gh/proof-foundry/blob/main/missions/sorting-networks/lean/SortNet/Claims/SN_002.lean) | `propext, Quot.sound` | `3eccb4d250` |

