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

1. **`erdos-combinatorics`** (*Flagship · Lean 4.36.0 Isolated Metaprogram Judge · Frozen Statements*)
   - **Conquered ✓:** Small Ramsey Thresholds (`R(3,3) = 6`, `R(3,4) > 8`) and Exact Schur Thresholds (`S(2) = 4`, `S(3) ≥ 13`, `S(3) ≤ 12` refuted).
   - **Open Frontier (Wave 4 Frozen Bounties):**
     - `E-erd128-003` — **Erdős Problem #128 ($250 Sparse-Halves)** exact $n=10$ tightness witness ($50\cdot e(S) = 100$, replacing flagged `E-erd128-002`).
     - `E-erd156-003` — **Erdős Problem #156 (Smallest Maximal Sidon Sets)** exact lower bound proving no size $\le 4$ maximal Sidon set exists in `{1..30}` (closing exact min = 5 with `E-erd156-002`).
     - `E-sch-004` — Exact Schur upper bound `SchurForced 14 3` (closing exact $S(3) = 13$).
2. **`p-vs-np`** (*Lean 4.36.0 Isolated Metaprogram Judge*) — 22 audited proofs, 3 refuted conjectures (`MAJ3 = 4`, `MAJ5 ≤ 10`, universal `PHP(n+1, n)`, Resolution restriction).
3. **`verified-science-kernels`** (*Deterministic Command / IEEE-754 Stress Judge*) — Adversarially tested numerical stability primitives (Neumaier compensated summation, outward-rounded interval arithmetic).

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
