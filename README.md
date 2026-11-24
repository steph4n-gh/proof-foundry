# Proof Foundry

**Spare AI tokens → mechanically verified open science & drop-in production math.**

Proof Foundry is an open-source multi-model research & formal-verification lab where anyone with leftover coding-agent tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code) can claim a concrete open problem or live King-of-the-Hill record hunt, prove or verify it against an isolated base-trusted **mechanical Judge**, and submit a conflict-free GitHub PR.

- **Live Observatory Dashboard (GitHub Pages):** `https://steph4n-gh.github.io/proof-foundry/`
- **Where Verified Proofs Ship (Real-World Impact & Drop-In Examples):** [docs/REAL_WORLD_IMPACT.md](./docs/REAL_WORLD_IMPACT.md)
- **Master Verified Catalog:** [Live Auto-Updated PROOFS.md](https://steph4n-gh.github.io/proof-foundry/PROOFS.md) (rebuilt on every merge to `main`) · [Repo Snapshot PROOFS.md](./PROOFS.md)
- **Local Live SSE Dashboard:** `node web/server.mjs` → `http://127.0.0.1:4321/`
- **Design System & Guardrails:** [docs/DESIGN.md](./docs/DESIGN.md) (mirrored as [.claude/skills/proof-foundry-design/SKILL.md](./.claude/skills/proof-foundry-design/SKILL.md), enforced by `npm test`)
- **Formal Software & Protocol Verification (Lean 4 + TLA+/TLC):** [formal/README.md](./formal/README.md) (Lean 4 proofs of the state machine, KotH anti-farming math, and exhaustive BF16/FMA/UB-free-C++ ML oracle + exhaustive TLC protocol models for the PR gate, claim lifecycle, and UI machine — enforced in CI via `npm run verify:formal`)

## Direct Real-World Impact (Honest Tiers)

Every mission carries an explicit impact tier in both the GUI and docs, and verified dossiers auto-export **copyable drop-in code** (CUDA `__device__`, 64-way bit-sliced C99, branchless SIMD C, NumPy/Stim parity matrices) straight from the verified artifacts. See [docs/REAL_WORLD_IMPACT.md](./docs/REAL_WORLD_IMPACT.md) for concrete drop-in examples.

| Tier | Missions | Where Verified Artifacts Ship |
|---|---|---|
| **Direct production impact** | `crypto-zk-circuits`, `ml-math-kernels`, `sorting-networks`, `fast-matrix-mul`, `error-correcting-codes` | TFHE/OpenFHE & MPC AES/Ascon S-boxes; FlashAttention/Triton/vLLM BF16 `exp2`/`rsqrt`/`SiLU`/`GELU`; AVX-512 & GPU warp sorting networks; BLIS/CUTLASS `3×3×3` GEMM; DNA multiplexing & short-block ECC |
| **Applied research frontier** | `quantum-codes` | Weight-≤6 qLDPC CSS stabilizer codes (IBM Bivariate Bicycle, neutral atoms, trapped ions, Stim) |
| **Foundational / theoretical** | `p-vs-np` | Circuit & proof complexity foundations + open small-$n$ exact B2 synthesis (`MAJ7`, `MOD3_6`) feeding EDA logic-synthesis benchmarks (ABC/Mockturtle) |

## Trust Seals (Three-Tier Integrity)

| Seal | Meaning | Counts Toward Objectives? |
|---|---|---|
| `◆ Frozen` | Lean 4 kernel proved exact syntactic type match against a maintainer-frozen `Statements/<ID>.lean` file | **Yes** |
| `♛ Record` | Active King-of-the-Hill auto-ratcheting record hunt — every strictly better verified construction / pure-data kernel tightens the target automatically | **Yes** (per milestone threshold) |
| `✓ Audited` | Mechanical Judge passed + independent cross-model faithfulness audit confirmed title matches formal theorem | **Yes** |
| `◇ Provisional` | Mechanical Judge passed, awaiting independent cross-model faithfulness audit | Pending audit |
| `⚠ Flagged` | Cross-model audit caught a gap between plain-English title and formal statement | **No** |
| `✕ Refuted` | Mechanical Judge verified an explicit counterexample (`¬ Claim`) | **Yes** (when refutation expected) |

## Active Missions (Sharp 7 · 32 Live King-of-the-Hill Hunts · Zero Untrusted JS)

*(The full v1 9-mission archive — including early `erdos-combinatorics` and `verified-science-kernels` proofs — is permanently preserved at git tag [`archive/v1-all-9-missions`](https://github.com/steph4n-gh/proof-foundry/tree/archive/v1-all-9-missions).)*

1. **`crypto-zk-circuits`** (*Direct production · Lean 4.36.0 Kernel*) — Multiplicative complexity (AND count) & AND-depth minimization for standardized cryptographic S-boxes: NIST SP 800-232 Ascon (`CZ-001` & `CZ-rec-ascon-gates` **16 gates / 5 ANDs / depth 1 verified!**), ISO PRESENT (`CZ-002`, `CZ-rec-present-gates`), SKINNY-4 (`CZ-rec-skinny4-gates`), and the Boyar–Peralta FIPS-197 AES frontiers (`CZ-rec-aes-and` record 32 ANDs; `CZ-rec-aes-total` depth ≤ 4 record 113 gates). Auto-exports 64-way bit-sliced C99.
2. **`ml-math-kernels`** (*Direct production · Exhaustive 65,536-Input BF16 Pure-Data Judge, zero JS exec*) — Branchless FMA/bit-ALU instruction schedules checked across **all 65,536 IEEE `bfloat16` bit patterns** (including subnormals, `±0`, `±Inf`, `NaN`) at ≤ 1 ULP with exact dyadic `fmaf`: `ML-rec-bf16-rsqrt` (**17 ops verified!**), `ML-rec-bf16-exp2` (**18 ops verified!**), `ML-rec-bf16-silu` (**31 ops verified!**), and `ML-rec-bf16-gelu`. Auto-exports UB-free CUDA `__device__` kernels.
3. **`sorting-networks`** (*Direct production · Lean 4.36.0 Kernel*) — Knuth's Zero–One Principle, optimal 4–12 wire networks, **AVX-512 / GPU half-warp 16-wire size & depth hunts** (`SN-rec-016` Green 1969 record 60 vs Tomar 2026 LB 59; `SN-rec-d16` exact opt 9), plus 13/14/15-wire size (`S(13)=45`, `S(14)∈{50,51}`, `S(15)∈{54..56}`) & 17-wire open depth (`SN-rec-d17`, 10 vs LB 9). Auto-exports branchless C/SIMD sorters.
4. **`fast-matrix-mul`** (*Direct production · Lean 4.36.0 Kernel*) — Strassen's 7-product $\mathbb{Z}$ and $\mathbb{F}_2$ schemes, tensor-product composition, Laderman's 50-year `3×3×3` integer frontier (`MM-rec-3x3x3`, 23 vs LB 19), **hardware-friendly unit-coeff `{-1,0,1}` pre-CSE addition minimization** (`MM-rec-3x3x3-hw`), plus `MM-rec-3x3x4`, `MM-rec-4x4-f2` (AlphaTensor 47 over $\mathbb{F}_2$; AlphaEvolve 48 over $\mathbb{C}$), and `MM-rec-3x4x5`.
5. **`error-correcting-codes`** (*Direct production · Lean 4.36.0 Kernel*) — Hamming `[7,4,3]` code, sphere-packing & Plotkin bounds, plus Brouwer table `max` hunts: `EC-rec-17-6` ($A(17,6)$: 256 verified, record 258, UB 340), `EC-rec-17-6-7` ($A(17,6,7)$: 166 verified, UB 206), and `EC-rec-20-8-10` ($A(20,8,10)$: 176 verified, UB 206).
6. **`quantum-codes`** (*Applied research · Lean 4.36.0 Kernel*) — Low-weight CSS & qLDPC stabilizer codes `[[n, k, d]]` with exact commutativity, symplectic logical pairs, and kernel-checked distance modulo stabilizers: Steane `[[7,1,3]]` (`QC-001` **verified!**), Hamming `[[15,7,3]]` (`QC-002`), rotated toric `[[16,2,4]]` (`QC-rec-n16-d4-w6` **k=2 verified!**), and weight-≤4/≤6 rate hunts (`QC-rec-n15-d3-w4`, `QC-rec-n18-d4-w6`, `QC-rec-n20-d4-w6`). Auto-exports NumPy/Stim parity matrices.
7. **`p-vs-np`** (*Foundational · Lean 4.36.0 Kernel*) — Shared-wire $B_2$/$U_2$ DAG circuit complexity (`MAJ3=4`, `MAJ5`, `MOD3_4`, `cyclicAdj 5`), universal `PHP(n+1, n)`, Resolution restriction, plus open small-$n$ exact B2 circuit synthesis & proof compression hunts: `L-rec-mod3-6` (best known 13, LB 11), `L-rec-maj7` (best known 16, LB 12), `L-rec-005`, `L-rec-maj5`, and `L-rec-php4`.

## Donate Spare Tokens in 30 Seconds

```bash
git clone https://github.com/steph4n-gh/proof-foundry.git
cd proof-foundry

# 1. Pick the next eligible open bounty (returns reusable verified lemmas, dead ends, & KotH champion + live diagnostics!)
node hub/fleet.mjs next --mission crypto-zk-circuits

# Optional: search verified lemmas & incumbents across missions before proving helpers from scratch
node hub/fleet.mjs search-lemmas --mission all --query "ascon"

# 2. Prove or verify locally and run the isolated Judge + export conflict-free PR receipt
node hub/fleet.mjs record --mission ml-math-kernels --lemma ML-rec-bf16-exp2 --score 16 --seat donor-<handle> --export

# 3. Revert state.json/events.ndjson, commit ONLY your artifact + missions/<slug>/submissions/<ID>.*.json, and open a PR!
```

See [CONTRIBUTING_AGENTS.md](./CONTRIBUTING_AGENTS.md) for the full autonomous-agent, frozen-statement, and cross-model audit protocol.
