# Real-World Impact & Production Use Cases

Every verified artifact in Proof Foundry is checked by an isolated **mechanical Judge** (the Lean 4.36.0 kernel with zero `sorry` and standard axioms only, or a pure-data exhaustive command verifier with zero untrusted code execution).

Not every open math problem has the same distance to production systems. We label every mission honestly across three impact tiers — and for direct-impact missions, the dashboard dossier and `hub/export_dropin.mjs` auto-generate **copyable drop-in code** (CUDA `__device__`, bit-sliced C99, branchless SIMD C, NumPy/Stim parity matrices) straight from the verified proof artifact.

---

## Portfolio Impact Map (9 Missions · 37 Live King-of-the-Hill Hunts)

| Mission | Honest Tier | Ships Directly To | What One Verified Step Buys |
|---|---|---|---|
| `crypto-zk-circuits` | **Direct production impact** | TFHE-rs, OpenFHE, MP-SPDZ, NIST SP 800-232 Ascon, masked AES ASICs | −1 AES AND gate saves 160 Beaver triples per AES-128 block in MPC and ~3% masked S-box silicon area |
| `ml-math-kernels` | **Direct production impact** | FlashAttention, Triton, PyTorch Inductor, vLLM, TensorRT-LLM, llama.cpp | −1 branchless FMA/ALU op cuts register pressure & GPU SFU stalls across trillions of tokens with 65,536/65,536 exhaustive ≤1 ULP guarantee |
| `sorting-networks` | **Direct production impact** | LLVM `libc++ std::sort`, Google Highway (`vqsort`), DuckDB, NVIDIA CUB/Thrust, FPGAs | −1 comparator or −1 parallel layer permanently speeds up 16-lane AVX-512 & GPU warp register sorting with zero branch mispredictions |
| `fast-matrix-mul` | **Direct production impact** | BLIS, OpenBLAS, CUTLASS GEMM, M4RI GF(2) engines, PQC / erasure coding | −1 product compounds exponentially ($r^L$ vs $27^L$); fewer additions with $\{-1,0,1\}$ coeffs lowers the real BLAS crossover size |
| `verified-science-kernels` | **Direct production impact** | CORE-MATH, LLVM `libc`, SLEEF, CGAL, PostGIS, SciPy / CFD solvers | Tighter float64-lattice minimax coeffs cut worst-case `exp`/`sin` ULP error at zero extra FLOPs; exact `orient2d` stops meshing crashes |
| `error-correcting-codes` | **Direct production impact** | DNA multiplexing barcodes, NAND/NVMe short-block ECC, optical FEC, Brouwer's tables | +1 codeword permanently expands error-tolerant multiplexing capacity at fixed block length and constant GC/DC weight |
| `quantum-codes` | **Applied research frontier** | IBM Bivariate Bicycle (w ≤ 6), QuEra/Atom neutral-atom arrays, Quantinuum ions, Stim | +1 logical qubit $k$ at fixed physical $n$, distance $d$, and check weight $w \le 6$ raises hardware QEC rate with zero extra physical qubits |
| `erdos-combinatorics` | **Applied research frontier** | VLA/VLBI radio interferometry, phased-array radar, optical DWDM spacing, Erdős Registry | Shorter Golomb rulers / Sidon sets eliminate baseline & four-wave-mixing collisions in smaller physical/spectral apertures |
| `p-vs-np` | **Foundational / theoretical** | EPFL Mockturtle, Berkeley ABC, SAT proof compression, Kulikov/Knuth tables | Honest: P vs NP itself is long-horizon foundational theory, while exact small-$n$ `MAJ7` / `MOD3_6` B2 circuits feed EDA peephole synthesis |

---

## Direct Production Examples (From Real Verified Artifacts)

### 1. Cryptographic & ZK/FHE S-Boxes (`crypto-zk-circuits`)

**The bottleneck:** In Fully Homomorphic Encryption (TFHE/BGV), Multi-Party Computation (MP-SPDZ / Garbled Circuits), and side-channel-masked hardware (smartcards, HSMs, TPMs), linear XOR gates are nearly free — while every non-linear AND gate costs bootstrapping latency, interactive Beaver triples, or quadratic masking randomness.

**Verified proof → drop-in bit-sliced C99:**
`CZ-001` and `CZ-rec-ascon-gates` (`s16`) prove in Lean 4.36.0 that 16 binary gates (only **5 non-linear AND gates** at **multiplicative depth 1**) compute the exact NIST SP 800-232 Ascon 5-bit S-box across all 32 inputs. Exporting that verified `MultiCircuit 5 5` yields a branchless 64-way bit-sliced C function executing 64 S-boxes simultaneously per 64-bit register:

```c
/* Auto-generated from Lean-verified CZ-rec-ascon-gates (16 B2 gates, 5 ANDs, depth 1) */
#include <stdint.h>
static inline void pf_cz_rec_ascon_gates_bitslice64(uint64_t out[5], const uint64_t w_in[5]) {
  const uint64_t w0 = w_in[0], w1 = w_in[1], w2 = w_in[2], w3 = w_in[3], w4 = w_in[4];
  const uint64_t w5 = (w4 ^ w0);
  const uint64_t w6 = (w0 ^ w1);
  const uint64_t w7 = (w2 ^ w3);
  const uint64_t w8 = (~w5 & w3);   /* AND #1 */
  const uint64_t w9 = (~w3 & w7);   /* AND #2 */
  const uint64_t w10 = (~w7 & w1);  /* AND #3 */
  const uint64_t w11 = (~w1 & w6);  /* AND #4 */
  const uint64_t w12 = (~w6 & w5);  /* AND #5 */
  const uint64_t w13 = (w5 ^ w9);
  const uint64_t w14 = (w3 ^ w10);
  const uint64_t w15 = ~(w7 ^ w11);
  const uint64_t w16 = (w1 ^ w12);
  const uint64_t w17 = (w6 ^ w8);
  const uint64_t w18 = (w14 ^ w13);
  const uint64_t w19 = (w13 ^ w17);
  const uint64_t w20 = ~(w16 ^ w15);
  out[0] = w17; out[1] = w20; out[2] = w15; out[3] = w18; out[4] = w19;
}
```

**Headline open targets:**
- `CZ-rec-aes-and` — Boyar–Peralta's famous **32-AND** FIPS-197 AES S-box frontier (31 ANDs is a landmark result for every MPC/FHE AES implementation).
- `CZ-rec-aes-total` — FIPS-197 AES S-box total B2 gates at **AND-depth ≤ 4** (record = 113 gates; directly sizes masked hardware AES and depth-capped FHE).

---

### 2. Exhaustively Verified BF16 GPU & ML Math Kernels (`ml-math-kernels`)

**The bottleneck:** On H100/B200/MI300 GPUs, Special Function Units (`exp2`, `rsqrt`, `tanh`) have 4–8× lower throughput than FMA/ALU pipes. Online softmax (`exp2`), RMSNorm (`rsqrt`), and SwiGLU/GELU FFNs regularly stall on SFU contention — yet hand-tuned polynomial approximations notoriously break on subnormals, `±0`, `±Inf`, or `NaN` propagation.

**Why BF16 is uniquely exact:** IEEE `bfloat16` has exactly **65,536** possible bit patterns. Our pure-data JSON Judge (`schema: "pf.mlkernel.v1"`, zero donor JS execution) checks **100% of all 65,536 inputs** with exact single-rounding dyadic `fmaf` in ~100ms — zero sampling blind spots.

**Verified artifact → drop-in CUDA `__device__` kernel:**
`ML-rec-bf16-exp2` (`s18`: **18 branchless ALU/FMA ops**, 65,518/65,536 exact 0-ULP matches, max 1 ULP across all 65,536 inputs including subnormals, overflow → `+Inf`, underflow → `+0`, and `NaN` → `NaN`):

```cuda
// Auto-generated from Proof Foundry verified pure-data kernel (18 ops, 65,536/65,536 bf16 inputs checked)
__device__ __forceinline__ float pf_bf16_exp2(float r0) {
  const float r10 = fminf(r0, 128.0f);
  const float r11 = fmaxf(r10, -135.0f);
  const int32_t r12 = __float2int_rn(r11);
  const float r13 = (float)r12;
  const float r14 = r11 - r13;
  const float r15 = fmaf(0.0555041097f, r14, 0.240226507f);
  const float r16 = fmaf(r15, r14, 0.693147182f);
  const float r17 = fmaf(r16, r14, 1.0f);
  const int32_t r18 = r12 >> 1;
  const int32_t r19 = r12 - r18;
  const float r24 = __int_as_float((r18 + 127) << 23);
  const float r25 = __int_as_float((r19 + 127) << 23);
  const float r27 = (r17 * r24) * r25;
  return (r0 == r0) ? r27 : r0;
}
```

Already verified out of the box: `ML-rec-bf16-rsqrt` (17 ops), `ML-rec-bf16-exp2` (18 ops), and `ML-rec-bf16-silu` (31 ops) — with `ML-rec-bf16-gelu` and further op-count reductions open to beat!

---

### 3. Branchless AVX-512 & GPU Warp Sorting Networks (`sorting-networks`)

**The bottleneck:** Modern libraries (`libc++ std::sort`, Google Highway `vqsort`, DuckDB, NVIDIA CUB `WarpSort`) finish small register tiles using branchless min/max comparator networks. Every comparator is two vector instructions; every parallel layer adds a full register-dependency latency cycle.

**Headline production targets:**
- `SN-rec-016` — **16 wires = 1 full AVX-512 register (`16×int32/float32`) or GPU half-warp**. Green's 1969 record is 60 comparators (LB 53); every verified `Net 16` exports directly as branchless C/SIMD `PF_CSWAP(v[i], v[j])` code.
- `SN-rec-d16` — **16-wire parallel depth** (optimal depth **9** beats Batcher bitonic's 10 by 10% pipeline latency).
- `SN-rec-013`, `SN-rec-014`, `SN-rec-015`, `SN-rec-d17` — Active Knuth / Bundala–Závodný world-record frontiers.

---

### 4. Hardware-Friendly Fast Matrix Multiplication (`fast-matrix-mul`)

**The bottleneck:** Pure bilinear rank ignores addition overhead and coefficient growth, which cause naïve Strassen/Laderman variants to lose to schoolbook GEMM on small/medium FP16/BF16 matrices.

**Headline targets:**
- `MM-rec-3x3x3-hw` — Minimizes direct addition count for rank ≤ 23 `3×3×3` schemes restricted to **unit coefficients `{-1, 0, 1}`** (keeping FP16/BF16 numerical stability tight and lowering the real BLAS/CUTLASS crossover size).
- `MM-rec-3x3x3` — Laderman's 50-year open integer frontier (record 23, LB 19).
- `MM-rec-4x4-f2`, `MM-rec-3x3x4`, `MM-rec-3x4x5` — AlphaTensor & Smirnov frontiers for GF(2) coding/crypto engines and rectangular block GEMM.

---

### 5. Numerical & Geometric Reliability (`verified-science-kernels`)

**The bottleneck:** Silent IEEE-754 rounding errors crash Delaunay triangulators/CAD engines on near-collinear geometry, erase small terms under catastrophic cancellation, and degrade `libm` elementary functions.

**Direct outputs:**
- `S-rec-exp`, `S-rec-sin` — Float64-lattice minimax polynomial coefficients verified against an exact **128-bit BigInt** oracle (drop straight into `libm`/SIMD Horner FMA loops).
- `S-num-001`..`S-num-004` — Verified Neumaier summation, outward-rounded interval arithmetic, error-free `TwoSum`/`Dot2`, and Shewchuk exact `orient2d`.

---

### 6. Short-Block & Constant-Weight Codes (`error-correcting-codes`)

**The bottleneck:** Multiplexed DNA sequencing (Illumina/Twist), DNA storage, and DC-balanced optical links need maximal sets of short binary words with fixed Hamming weight (constant GC-content / zero DC bias) and guaranteed Hamming distance $d \ge 6$ or $8$ (correcting 2–3 bit errors).

**Direct outputs:** Lean-certified codes for Brouwer's open tables `A(17,6)` (256 verified, record 258, UB 340), `A(17,6,7)` (166 verified = record, UB 206), and `A(20,8,10)` (176 verified = record, UB 206).

---

### 7. Low-Weight Quantum LDPC Codes (`quantum-codes`) — *Applied Research Frontier*

**The bottleneck:** Surface codes need hundreds of physical qubits per logical qubit. Low-weight qLDPC CSS codes (`check weight ≤ 6`, matching IBM Bivariate Bicycle and neutral-atom/trapped-ion hardware) slash physical qubit overhead by 5–10×.

**Verified proof → NumPy / Stim parity matrices:**
`QC-rec-n16-d4-w6` (`s2`) certifies the rotated 4×4 toric CSS code `[[16, 2, 4]]` with all weight-4 stabilizers (`H_X H_Z^T = 0`, exact symplectic logical pairs, exact quantum distance 4 modulo stabilizers) — and every dossier exports `H_X, H_Z, L_X, L_Z` as ready-to-load NumPy arrays for Stim & BP+OSD simulation. Open hunts push logical qubit count $k$ upward on `[[15,k,3]]` ($w \le 4$) and `[[16/18/20, k, 4]]` ($w \le 6$).

---

### 8. Extremal Combinatorics (`erdos-combinatorics`) — *Applied Research Frontier*

- `E-rec-gol11` (verified optimal length 72) & `E-rec-200` (verified 10-element maximal Sidon set) give collision-free sensor/antenna placements for radio interferometry (VLBI/phased-array radar) and DWDM fiber-optic channel plans eliminating four-wave mixing.
- `E-rec-r55` (verified 42-vertex $K_5/I_5$-free graph), Erdős #128, #156, Schur $S(3)/S(4)$, and van der Waerden bounds advance formal extremal mathematics.

---

### 9. P vs NP & Exact Circuit Synthesis (`p-vs-np`) — *Foundational / Theoretical*

We keep `p-vs-np` both as the original flagship foundational frontier (formalizing Relativization/Natural Proofs/Algebrization barriers, universal `PHP(n+1, n)`, and Resolution soundness) **and** as an active exact small-$n$ Boolean circuit synthesis arena (`L-rec-mod3-6`, `L-rec-maj7`, `L-rec-005`, `L-rec-maj5`, `L-rec-php4`) whose minimal shared-wire B2 DAG circuits directly benchmark EDA logic synthesizers (EPFL Mockturtle, Berkeley ABC) and SAT proof compression.
