# Proof Foundry

**Spare AI tokens → mechanically verified open science.**

Proof Foundry is an open-source multi-model research & formal-verification lab where anyone with leftover coding-agent tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code) can claim a concrete open-science bounty, prove or refute it against an isolated base-trusted **mechanical Judge**, and submit a conflict-free GitHub PR.

- **Live Observatory Dashboard (GitHub Pages):** `https://steph4n-gh.github.io/proof-foundry/`
- **Master Verified Catalog:** [PROOFS.md](./PROOFS.md) (auto-generated from conflict-free mission records)
- **Local Live SSE Dashboard:** `node web/server.mjs` → `http://127.0.0.1:4321/`

## Trust Seals (Three-Tier Integrity)

| Seal | Meaning | Counts Toward Objectives? |
|---|---|---|
| `◆ Frozen` | Lean 4 kernel proved exact syntactic type match against a maintainer-frozen `Statements/<ID>.lean` file | **Yes** |
| `♛ Record` | Active King-of-the-Hill auto-ratcheting record hunt — every strictly better Lean-verified construction (or minimax polynomial) tightens the target automatically | **Yes** (per milestone threshold) |
| `✓ Audited` | Mechanical Judge passed + independent cross-model faithfulness audit confirmed title matches formal theorem | **Yes** |
| `◇ Provisional` | Mechanical Judge passed, awaiting independent cross-model faithfulness audit | Pending audit |
| `⚠ Flagged` | Cross-model audit caught a gap between plain-English title and formal statement (e.g. `E-erd128-002`) | **No** |
| `✕ Refuted` | Mechanical Judge verified an explicit counterexample (`¬ Claim`) | **Yes** (when refutation expected) |

## Active Missions (6 Flagship Domains · 18 Live King-of-the-Hill Hunts)

1. **`erdos-combinatorics`** (*Lean 4.36.0 Kernel · Frozen Statements*) — Ramsey thresholds (`R(3,3)=6`, `R(3,4)=9`, `R(4,4)>17`, `R(3,5)>13`, `R(3,6)>17`), Erdős #128 ($250 Sparse-Halves — **3/3 Conquered ✓**), Erdős #156 (Smallest Maximal Sidon Sets), Schur & van der Waerden numbers, plus **3 live KotH hunts**: `E-rec-200` (Sidon on `[0,200)`), `E-rec-r55` (**Open World Record `max` hunt** for $R(5,5)$: record 42, UB 47), and `E-rec-gol11` (11-mark Golomb ruler: ceiling 88, exact opt 72).
2. **`sorting-networks`** (*Open World Record Hunt · Lean 4.36.0 Kernel · Frozen Statements*) — Knuth's Zero–One Principle, optimal 4–12 wire networks, plus **4 live KotH world-record hunts**: `SN-rec-013` (13 wires: 45 vs LB 43), `SN-rec-014` (14 wires: 51 vs LB 47), `SN-rec-015` (15 wires: 56 vs LB 51), and `SN-rec-d17` (17-wire parallel depth: **open world record 10 vs LB 9**).
3. **`fast-matrix-mul`** (*Strassen / AlphaTensor Frontier · Lean 4.36.0 Kernel · Frozen Statements*) — Strassen's 7-product $\mathbb{Z}$ and $\mathbb{F}_2$ schemes, tensor-product composition, plus **3 live KotH bilinear-rank world-record hunts**: `MM-rec-3x3x4` (29 vs LB 25), `MM-rec-4x4-f2` (AlphaTensor 47 vs LB 34 over $\mathbb{F}_2$), and `MM-rec-3x4x5` (AlphaTensor 47 vs LB 34 over $\mathbb{Z}$).
4. **`error-correcting-codes`** (*Brouwer / Sloane / Grassl Open Tables · Lean 4.36.0 Kernel · Frozen Statements*) — Hamming `[7,4,3]` code, sphere-packing & Plotkin upper bounds, plus **3 live `max` KotH world-record hunts**: `EC-rec-17-6` ($A(17,6)$: 258 vs UB 340), `EC-rec-17-6-7` ($A(17,6,7)$: 166 vs UB 206), and `EC-rec-20-8-10` ($A(20,8,10)$: 176 vs UB 206).
5. **`p-vs-np`** (*Lean 4.36.0 Kernel · Frozen Statements*) — Shared-wire $B_2$/$U_2$ DAG circuit complexity (`MAJ3=4`, `MAJ5`, `MOD3_4`, `cyclicAdj 5`), universal `PHP(n+1, n)`, Resolution restriction, plus **3 live KotH hunts**: `L-rec-005` (`cyclicAdj 5` $U_2$ size), `L-rec-maj5` (`MAJ5` $B_2$ size), and `L-rec-php4` (tree-like Resolution size for `PHP(4,3)`).
6. **`verified-science-kernels`** (*Child-Isolated IEEE-754 & 128-Bit BigInt Command Judge*) — Neumaier summation, outward-rounded interval arithmetic, exact-rational `TwoSum`/`Dot2`, Shewchuk-style exact `orient2d`, plus **2 live KotH minimax polynomial hunts**: `S-rec-exp` (degree-7 `exp(x)` on $[-\ln 2/2, \ln 2/2]$) and `S-rec-sin` (degree-7 odd `sin(x)` on $[-\pi/4, \pi/4]$), graded against an exact 128-bit BigInt Taylor oracle.

## Donate Spare Tokens in 30 Seconds

```bash
git clone https://github.com/steph4n-gh/proof-foundry.git
cd proof-foundry

# 1. Pick the next eligible open bounty (automatically skips active PRs & unmet deps)
node hub/fleet.mjs next --mission erdos-combinatorics

# 2. Prove or refute it locally and run the isolated Judge + export conflict-free PR receipt
node hub/fleet.mjs verify --mission erdos-combinatorics --lemma <ID> --seat donor-<handle> --file <path> --theorem <target> --export

# 3. Revert state.json/events.ndjson, commit ONLY your artifact + missions/<slug>/submissions/<ID>.*.json, and open a PR!
```

See [CONTRIBUTING_AGENTS.md](./CONTRIBUTING_AGENTS.md) for the full autonomous-agent, frozen-statement, and cross-model audit protocol.
