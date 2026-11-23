#!/usr/bin/env node
/**
 * hub/launch_wave3.mjs — Launches Wave 3 across 4 isolated git-worktree multi-model seats,
 * attacking all 4 Objectives of `erdos-combinatorics` and opening REAL conflict-free GitHub PRs
 * on steph4n-gh/proof-foundry (verified automatically by GitHub Actions Lean 4 CI!).
 */
import { spawnSync } from "node:child_process";

const NODE_BIN = process.env.T3_ACP_MCP_NODE;
const ENTRY = process.env.T3_ACP_MCP_ENTRYPOINT;
const MAIN_REPO = "/Volumes/Storage/pnpenis2";

function callT3(tool, argsObj) {
  const cmdArgs = [];
  if (ENTRY) cmdArgs.push(ENTRY);
  cmdArgs.push("acp-mcp-call", tool, JSON.stringify(argsObj));
  const res = spawnSync(NODE_BIN, cmdArgs, {
    encoding: "utf8",
    env: { ...process.env, ELECTRON_RUN_AS_NODE: "1" },
    timeout: 30000,
  });
  return {
    status: res.status,
    stdout: (res.stdout || "").trim(),
    stderr: (res.stderr || "").trim(),
  };
}

const COMMON_WAVE3 = `
You are a live multi-model seat in **Proof Foundry** (\`steph4n-gh/proof-foundry\`), Wave 3 — Mission: \`erdos-combinatorics\`.
You are running in your OWN isolated git worktree cloned from \`main\`.

READ FIRST:
- \`CONTRIBUTING_AGENTS.md\`
- \`missions/erdos-combinatorics/lean/Erdos/Core.lean\`

STRICT RULES:
1. NEVER edit \`Core.lean\`, \`hub/\`, \`.github/\`, \`state.json\`, or \`events.ndjson\` in your PR commit!
   (GitHub Actions \`judge.yml\` enforces this and REJECTS any PR touching restricted files or \`state.json\`!)
2. Put every Lean 4 proof in its own dedicated file under \`missions/erdos-combinatorics/lean/Erdos/Claims/\` importing ONLY \`Erdos.Core\`.
   Use Lean 4.36.0 pure stdlib (NO Mathlib). Zero \`sorry\`, zero \`admit\`, zero \`native_decide\`, zero custom \`axiom\`, zero \`#eval\`/\`#print\`.
3. Build \`Erdos\` once in your worktree if needed: \`(cd missions/erdos-combinatorics/lean && lake build Erdos)\`.
4. Verify EVERY proof locally using the isolated Judge WITH \`--export\`:
   \`node hub/fleet.mjs verify --mission erdos-combinatorics --lemma <ID> --seat <seat> --file <rel-path> --theorem <Exact.Theorem.Name> --export\`
   (Or \`refute ... --export\` for Red Team refutations!)
   Iterate until the Judge returns \`"ok": true\`!
5. ALSO mirror your live progress & final verified file into the user's live local dashboard repo at \`${MAIN_REPO}\`:
   - Copy your verified \`.lean\` file(s) into \`${MAIN_REPO}/missions/erdos-combinatorics/lean/Erdos/Claims/\`
   - Run \`node ${MAIN_REPO}/hub/fleet.mjs verify --mission erdos-combinatorics ...\` (or \`refute ...\`) so the live local SSE dashboard at http://127.0.0.1:4321/ lights up in real time!
6. OPEN A REAL CONFLICT-FREE GITHUB PR on \`steph4n-gh/proof-foundry\`:
   - In your worktree, make sure you are on a clean feature branch (e.g. \`git checkout -b wave3/<branch>\`).
   - Run \`git checkout -- missions/erdos-combinatorics/state.json missions/erdos-combinatorics/events.ndjson\` so monolithic state files stay UNTOUCHED!
   - Stage ONLY your new \`missions/erdos-combinatorics/lean/Erdos/Claims/*.lean\` file(s) and your exported \`missions/erdos-combinatorics/submissions/*.json\` file(s).
   - Verify with \`node hub/fleet.mjs verify-pr --files "$(git diff --cached --name-only | paste -sd, -)"\` BEFORE pushing!
   - Commit, \`git push -u origin <branch>\`, and run \`gh pr create --repo steph4n-gh/proof-foundry --base main --title "..." --body "..."\`.
7. In your final response, include the exact PR URL, head SHA, and verified theorems/axioms/times. Do NOT spawn subagents.
`.trim();

const WAVE_3 = [
  {
    clientRequestId: "wave3-obj1-ramsey",
    title: "Wave 3 · Objective 1 · Small Ramsey R(3,3)=6 & R(3,4)>8 (Claude Opus 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-opus-5-5",
      options: { effort: "xhigh" },
    },
    task: `${COMMON_WAVE3}

YOUR SEAT: \`seat-ramsey-1\` (Claude Opus 5.5)
BRANCH: \`wave3/obj1-ramsey-thresholds\`
OBJECTIVE 1 — CONQUER SMALL RAMSEY THRESHOLDS:
1. \`E-ram-002\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_002.lean\`, theorem \`Erdos.Claims.E_ram_002.ramsey33_le_six\`:
   \`theorem ramsey33_le_six : Ramsey33At 6\`
   (Prove that every \`SimpleGraph 6\` has \`HasTriangle G ∨ HasIndep3 G\`. Hint: fix vertex \`0 : Fin 6\`, inspect its 5 adjacencies \`G.adj 0 1, ..., G.adj 0 5\`; by case analysis either ≥3 are \`true\` — among those 3 any edge gives a triangle with 0, else they form an \`Indep3\` — or ≥3 are \`false\` — among those 3 any non-edge gives an \`Indep3\` with 0, else they form a triangle! Super clean & fast in Lean 4!)
2. \`E-ram-003\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_003.lean\`, theorem \`Erdos.Claims.E_ram_003.ramsey34_gt_eight\`:
   \`theorem ramsey34_gt_eight : ¬ Ramsey34At 8\`
   (Construct an explicit 8-vertex \`SimpleGraph 8\` with NO \`HasIndep3\` and NO \`HasK4\` — e.g. the complement of the circulant \`C8(1,4)\` on \`Z/8Z\`: adj u v = true iff \`(u - v) % 8 ∈ {2, 3, 5, 6}\`? DOUBLE CHECK! Wait: in complement of \`C8(1,4)\`, non-edges are diffs \`{1, 4, 7}\` which is triangle-free (since 1+1≠4, 1+4≠7, 1+7=0, 4+4=0) -> so \`G\` has NO 3-independent set! And does \`G\` have a K4? Check diffs \`{2, 3, 5, 6}\` — 0,2,5? (5-2=3, 5-0=5, 2-0=2 -> K3, can you add a 4th? 3 is adj to 0(3), not 2(1); 6 is adj to 0(6), not 5(1)! NO K4!! Verify by \`decide\` in Lean 4!)`,
  },
  {
    clientRequestId: "wave3-obj2-erdos128-mantel",
    title: "Wave 3 · Objective 2 · Mantel's Theorem & Erdős #128 (GPT-6.2 Sol)",
    role: "implementation",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-sol",
      options: { reasoningEffort: "xhigh" },
    },
    task: `${COMMON_WAVE3}

YOUR SEAT: \`donor-gpt-mantel\` (GPT-6.2 Sol)
BRANCH: \`wave3/obj2-mantel-erdos128\`
OBJECTIVE 2 — CONQUER MANTEL'S THEOREM & ERDŐS PROBLEM #128 BASE CASES:
1. \`E-tur-001\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_tur_001.lean\`, theorem \`Erdos.Claims.E_tur_001.mantel_theorem\`:
   \`theorem mantel_theorem (n : Nat) (G : SimpleGraph n) (htf : ¬ HasTriangle G) : 4 * edgeCount G ≤ n * n\`
   (Real universal Mantel's Theorem for ALL \`n : Nat\`! Classic 2-vertex induction or sum-of-degrees proof:
   - Option A (super clean!): Double-count \`∑_{u < v, adj u v} (deg u + deg v)\`! Because G is triangle-free, every edge \`(u, v)\` has disjoint neighborhoods, so \`deg u + deg v ≤ n\` for EVERY edge! Summing over all \`e = edgeCount G\` edges gives \`∑_u (deg u)^2 ≤ n * e\`. Meanwhile by Cauchy–Schwarz \`(∑_u deg u)^2 ≤ n * ∑_u (deg u)^2\` and \`∑_u deg u = 2 * e\`, so \`4 * e^2 ≤ n^2 * e\`, hence \`4 * e ≤ n^2\`!
   - Option B: Strong induction on \`n\` deleting endpoints of an edge \`(u, v)\`: remaining \`n - 2\` vertices have \`e' ≤ (n-2)^2/4\`, and \`deg u + deg v ≤ n\` adds at most \`n - 1\` edges, giving \`4 * (e' + n - 1) ≤ (n-2)^2 + 4n - 4 = n^2\`! Both are gorgeous!)
2. \`E-erd128-001\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_001.lean\`, theorem \`Erdos.Claims.E_erd128_001.bipartite_has_sparse_half\`:
   \`theorem bipartite_has_sparse_half (n : Nat) (G : SimpleGraph n) (hb : IsBipartite G) : HasSparseHalf G\`
   (Given 2-coloring \`col\`, let \`S0 = fun v => !col v\` and \`S1 = col\`. Show \`subsetSize S0 + subsetSize S1 = n\`, so one of them has \`subsetSize S ≥ n / 2\`, and \`inducedEdgeCount G S = 0\`, so \`50 * 0 ≤ n * n\`!)
3. \`E-erd128-002\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_002.lean\`, theorem \`Erdos.Claims.E_erd128_002.c5_erdos128_witness\`:
   \`theorem c5_erdos128_witness : ∃ G : SimpleGraph 5, ¬ HasTriangle G ∧ HasSparseHalf G\`
   (Exhibit \`C5\` and independent set \`{0, 2}\` of size \`2 = 5 / 2\` with 0 internal edges!)`,
  },
  {
    clientRequestId: "wave3-obj3-schur",
    title: "Wave 3 · Objective 3 · Exact Schur S(2)=4, S(3)≥13 & Refute S(3)≤12 (Claude Sonnet 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-sonnet-5-5",
      options: { effort: "high" },
    },
    task: `${COMMON_WAVE3}

YOUR SEAT: \`seat-redteam-1\` (Claude Sonnet 5.5)
BRANCH: \`wave3/obj3-schur-thresholds\`
OBJECTIVE 3 — CONQUER EXACT SCHUR NUMBERS S(2)=4 & S(3)≥13 + REFUTE S(3)≤12:
1. \`E-sch-001\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_001.lean\`, theorem \`Erdos.Claims.E_sch_001.schur_two_exact\`:
   \`theorem schur_two_exact : (∃ col : Fin 4 → Fin 2, IsSumFreeColoring 4 2 col) ∧ SchurForced 5 2\`
   (Witness \`{1,4}\` color 0, \`{2,3}\` color 1 for \`n=4\`; for \`n=5\`, case split on \`col 0, col 1, col 2, col 3, col 4 : Fin 2\` — only 32 cases, closes fast in Lean 4!)
2. \`E-sch-002\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_002.lean\`, theorem \`Erdos.Claims.E_sch_002.schur_three_ge_13\`:
   \`theorem schur_three_ge_13 : ∃ col : Fin 13 → Fin 3, IsSumFreeColoring 13 3 col\`
   (Classic 3-coloring of {1..13}: color 0 = {1,4,10,13}, color 1 = {2,3,11,12}, color 2 = {5,6,7,8,9} — remember \`Fin 13\` is 0-indexed so \`i\` represents \`i+1\`! Verify \`IsSumFreeColoring 13 3 col\` by \`decide\`!)
3. **REFUTE \`E-sch-003\`** (\`SchurForced 13 3\` is FALSE!) -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_003_refute.lean\`, theorem \`Erdos.Claims.E_sch_003_refute.counterexample\`:
   \`theorem counterexample : ¬ SchurForced 13 3\`
   Submit via \`refute\` (NOT \`verify\`!):
   \`node hub/fleet.mjs refute --mission erdos-combinatorics --lemma E-sch-003 --seat seat-redteam-1 --file missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_003_refute.lean --theorem Erdos.Claims.E_sch_003_refute.counterexample --summary "Explicit 3-color sum-free partition {1,4,10,13} | {2,3,11,12} | {5,6,7,8,9} refutes S(3) ≤ 12" --export\`
   (And mirror to \`${MAIN_REPO}\` too!)`,
  },
  {
    clientRequestId: "wave3-obj4-erdos156-sidon",
    title: "Wave 3 · Objective 4 · Erdős Problem #156 Maximal Sidon Sets (Gemini 4 Neon)",
    role: "implementation",
    target: {
      providerInstanceId: "antigravity",
      model: "gemini-4-neon",
      options: { thought_level: "xhigh" },
    },
    task: `${COMMON_WAVE3}

YOUR SEAT: \`donor-gemini-sidon\` (Gemini 4 Neon)
BRANCH: \`wave3/obj4-erdos156-sidon\`
OBJECTIVE 4 — CONQUER ERDŐS PROBLEM #156 FOUNDATIONS & SMALL-N SYNTHESIS:
1. \`E-erd156-001\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_001.lean\`, theorem \`Erdos.Claims.E_erd156_001.maximal_sidon_blocking\`:
   \`theorem maximal_sidon_blocking (N : Nat) (A : List Nat) (x : Nat) (hmax : IsMaximalSidon N A) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hnot : x ∉ A) : (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x + a = b + c) ∨ (∃ a ∈ A, ∃ b ∈ A, x + x = a + b)\`
   (Proof idea: \`hmax\` gives \`¬ IsSidon (x :: A)\`. By classical contradiction, there exist \`u, v, w, z ∈ x :: A\` with \`u ≤ v\`, \`w ≤ z\`, \`u + v = w + z\`, and \`¬(u = w ∧ v = z)\`. Since \`A\` itself \`IsSidon\`, at least one of \`u, v, w, z\` must equal \`x\`. Case split cleanly on which ones equal \`x\` — using \`x ∉ A\` and \`omega\`, every case produces either \`x + a = b + c\` or \`x + x = a + b\` with \`a, b, c ∈ A\`!)
2. \`E-erd156-002\` -> \`missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_002.lean\`, theorem \`Erdos.Claims.E_erd156_002.small_maximal_sidon_30\`:
   \`theorem small_maximal_sidon_30 : ∃ A : List Nat, A.length ≤ 6 ∧ IsMaximalSidon 30 A\`
   (Write a tiny 15-line Python search script in \`/tmp\` to find a real maximal Sidon subset \`A ⊆ {1..30}\` with \`|A| ≤ 6\`! Test that EVERY \`x ∈ {1..30} \\ A\` creates a duplicate pairwise sum with \`A\`! Then encode that exact \`A\` in Lean 4 and prove \`A.Nodup ∧ SubsetOfRange 30 A ∧ IsSidon A ∧ ∀ x, 1 ≤ x → x ≤ 30 → x ∉ A → ¬ IsSidon (x :: A)\` cleanly without \`native_decide\`!)`,
  },
];

console.log("Dispatching Wave 3 (4 isolated git-worktree multi-model PR seats)...");
for (const s of WAVE_3) {
  const res = callT3("delegate_task", {
    clientRequestId: s.clientRequestId,
    title: s.title,
    role: s.role,
    mode: "async",
    isolation: "worktree",
    target: s.target,
    task: s.task,
  });
  console.log(`\n[${s.clientRequestId}] status=${res.status}`);
  console.log(res.stdout || res.stderr);
}
