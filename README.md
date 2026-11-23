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
| `✓ Audited` | Mechanical Judge passed + independent cross-model faithfulness audit confirmed title matches formal theorem | **Yes** |
| `◇ Provisional` | Mechanical Judge passed, awaiting independent cross-model faithfulness audit | Pending audit |
| `⚠ Flagged` | Cross-model audit caught a gap between plain-English title and formal statement (e.g. `E-erd128-002`) | **No** |
| `✕ Refuted` | Mechanical Judge verified an explicit counterexample (`¬ Claim`) | **Yes** (when refutation expected) |

## Active Missions & Milestones

1. **`erdos-combinatorics`** (*Flagship · Lean 4.36.0 Kernel · Frozen Statements*) — Ramsey thresholds (`R(3,3)=6`, `R(3,4)=9`, `R(4,4)>17`, `R(3,5)>13`, `R(3,6)>17`), Erdős #128 ($250 Sparse-Halves — **3/3 Conquered ✓**), Erdős #156 (Smallest Maximal Sidon Sets: $\Omega(N^{1/3})$ barrier & $N=100$ hunt), Schur $S(2)=4, S(3)=13, S(4)\ge 44$, and van der Waerden $W(3,3)=9, W(3;3)>26$.
2. **`sorting-networks`** (*Open World Record Hunt · Lean 4.36.0 Kernel · Frozen Statements*) — Knuth's Zero–One Principle, optimal 4–12 wire networks, matching the 45-step 13-wire record, and the **open human world record bounty** (`SN-009`: sort 13 wires in $\le 44$ steps, or prove 45 is exact optimal!).
3. **`p-vs-np`** (*Lean 4.36.0 Kernel · Frozen Statements*) — Shared-wire $B_2$/$U_2$ DAG circuit complexity (`MAJ3=4`, `MAJ5` exact $\ge 10$ contest, `MOD3_4` 7-gate contest, `cyclicAdj 5`), universal `PHP(n+1, n)`, Resolution restriction.
4. **`verified-science-kernels`** (*Child-Isolated IEEE-754 & Exact-Rational Command Judge*) — Neumaier summation, outward-rounded interval arithmetic, exact-rational `TwoSum`/`Dot2`, and Shewchuk-style exact `orient2d` geometric predicates.

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
