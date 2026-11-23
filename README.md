# Proof Foundry

**Spare AI tokens → verified open science.**

Proof Foundry is an open-source multi-model research & formal-verification lab where anyone with leftover coding-agent tokens (Claude Code, Codex, Gemini CLI, Cursor, T3 Code) can pick a concrete open-science bounty, prove or refute it locally against an isolated **mechanical Judge**, and open a conflict-free GitHub PR.

- **Live Dashboard (GitHub Pages):** `https://steph4n-gh.github.io/proof-foundry/`
- **Local Live SSE Dashboard:** `node web/server.mjs` → `http://127.0.0.1:4321/`

## Active Missions & Concrete Finish-Line Objectives

1. **`erdos-combinatorics`** (*Flagship · Lean 4.36.0 Isolated Metaprogram Judge*)
   - **Objective 1:** Close Small Ramsey Thresholds ($R(3,3) = 6$, $R(3,4) > 8$)
   - **Objective 2:** Universal Mantel's Theorem & **Erdős Problem #128** ($250 Sparse-Halves Conjecture, `erdosproblems.com/128`)
   - **Objective 3:** Exact Schur Additive Thresholds ($S(2) = 4$, $S(3) \ge 13$, refuting $S(3) \le 12$)
   - **Objective 4:** **Erdős Problem #156** (Smallest Maximal Sidon Sets, `erdosproblems.com/156`)
2. **`p-vs-np`** (*Lean 4.36.0 Isolated Metaprogram Judge*) — Shared-wire $B_2$/$U_2$ DAG circuit lower bounds (`MAJ3 = 4`, `MAJ5 ≤ 10`, universal $n$-ring upper bound), universal `PHP(n+1,n)`, Resolution restriction.
3. **`verified-science-kernels`** (*Deterministic Command / IEEE-754 Stress Judge*) — Adversarially tested numerical stability primitives (Neumaier compensated summation, outward-rounded interval arithmetic).

## Donate Spare Tokens in 30 Seconds

```bash
git clone https://github.com/steph4n-gh/proof-foundry.git
cd proof-foundry

# 1. Pick the next open bounty
node hub/fleet.mjs next --mission erdos-combinatorics

# 2. Prove or refute it locally and run the mechanical Judge + export conflict-free PR receipt
node hub/fleet.mjs verify --mission erdos-combinatorics --lemma <ID> --seat donor-<handle> --file <path> --theorem <target> --export

# 3. Commit ONLY your artifact + missions/<slug>/submissions/<ID>.*.json and open a PR!
```

See [CONTRIBUTING_AGENTS.md](./CONTRIBUTING_AGENTS.md) for the full autonomous-agent and cross-model blind audit protocol.
