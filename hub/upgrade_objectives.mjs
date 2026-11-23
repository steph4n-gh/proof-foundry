#!/usr/bin/env node
/**
 * hub/upgrade_objectives.mjs — Adds concrete winnable Objective Finish-Line Ladders,
 * real open Erdős #128 & #156 frontier bounties, and GitHub repo metadata across all 3 missions.
 */
import fs from "node:fs";
import path from "node:path";

const ROOT = path.resolve(import.meta.dirname, "..");
const REPO = "steph4n-gh/proof-foundry";
const now = new Date().toISOString();

function readJson(p) {
  return JSON.parse(fs.readFileSync(p, "utf8"));
}
function writeJson(p, obj) {
  fs.writeFileSync(p, JSON.stringify(obj, null, 2) + "\n", "utf8");
}

// ============================================================================
// 1. ERDŐS & EXTREMAL COMBINATORICS (Flagship Mission)
// ============================================================================
const erdosMissionPath = path.join(ROOT, "missions/erdos-combinatorics/mission.json");
const erdosStatePath = path.join(ROOT, "missions/erdos-combinatorics/state.json");
const erdosMission = readJson(erdosMissionPath);
erdosMission.brand = "PROOF FOUNDRY · ERDŐS";
erdosMission.github_repo = REPO;
erdosMission.objectives = [
  {
    id: "OBJ-ramsey",
    title: "Close Small Ramsey Thresholds: R(3,3) = 6 & R(3,4) > 8",
    tier: "Milestone 1",
    finish_line: "Prove both sides of R(3,3) = 6 and exhibit a Lean-verified 8-vertex avoidance graph for R(3,4) > 8.",
    required_claims: ["E-ram-001", "E-ram-002", "E-ram-003"],
  },
  {
    id: "OBJ-erdos-128",
    title: "Erdős Problem #128 ($250 Sparse-Halves) & Mantel's Theorem",
    tier: "Open Erdős Frontier",
    url: "https://www.erdosproblems.com/128",
    finish_line: "Prove universal Mantel (4e ≤ n²), prove all bipartite graphs satisfy Erdős #128, and verify C5 tightness.",
    required_claims: ["E-tur-001", "E-erd128-001", "E-erd128-002"],
  },
  {
    id: "OBJ-schur",
    title: "Exact Schur Additive Thresholds: S(2) = 4 & S(3) ≥ 13",
    tier: "Milestone 2",
    finish_line: "Pin down exact S(2) = 4, verify a 13-element 3-color sum-free witness for S(3) ≥ 13, and refute S(3) ≤ 12.",
    accept_refutation: true,
    required_claims: ["E-sch-001", "E-sch-002", "E-sch-003"],
  },
  {
    id: "OBJ-erdos-156",
    title: "Erdős Problem #156: Smallest Maximal Sidon Sets",
    tier: "Open Erdős Frontier",
    url: "https://www.erdosproblems.com/156",
    finish_line: "Prove the formal Sidon blocking lemma and synthesize a compact Lean-verified maximal Sidon subset of {1..30} of size ≤ 6.",
    required_claims: ["E-erd156-001", "E-erd156-002"],
  },
];
writeJson(erdosMissionPath, erdosMission);

const erdosState = readJson(erdosStatePath);
if (!erdosState.programs.some((p) => p.id === "erdos_open")) {
  erdosState.programs.push({
    id: "erdos_open",
    key: "erd",
    title: "Open Erdős Frontier (#128 & #156)",
    aims_at: "upper_forced",
    color: "#38BDF8",
    goal: "Formalize and attack real open problems from erdosproblems.com: #128 (Sparse Halves, $250 prize) and #156 (Smallest Maximal Sidon Sets).",
    target_summary: "Machine-checked theorems, tightness witnesses, and computational counterexample hunts on live open Erdős problems.",
  });
}

const newErdosClaims = [
  {
    id: "E-erd128-001",
    program: "erdos_open",
    title: "Erdős #128 Bipartite Base Case: every bipartite graph on n vertices satisfies HasSparseHalf (an independent half of size ≥ n/2 has 0 ≤ n²/50 edges)",
    statement: "∀ (n : Nat) (G : SimpleGraph n), IsBipartite G → HasSparseHalf G",
    registered_statement: "∀ (n : Nat) (G : SimpleGraph n), IsBipartite G → HasSparseHalf G",
    verified_signature: null,
    theorem_name: "Erdos.Claims.E_erd128_001.bipartite_has_sparse_half",
    lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_001.lean",
    status: "conjecture",
    aims_at: "upper_forced",
    deps: ["E-tur-001"],
    rung: 1,
    proposed_by: "seat-strat-1",
    claimed_by: null,
    paper_notes: "In any 2-coloring of G, the larger color class S has size ≥ n/2 and 0 internal edges, giving 50 * 0 ≤ n².",
    created_at: now,
    updated_at: now,
    checker: null,
    refutation: null,
    epitaph: null,
    audit: null,
  },
  {
    id: "E-erd128-002",
    program: "erdos_open",
    title: "Erdős #128 Tightness Witness: the 5-cycle C5 is triangle-free and satisfies HasSparseHalf with an independent set of size 2 = 5/2",
    statement: "∃ G : SimpleGraph 5, ¬ HasTriangle G ∧ HasSparseHalf G",
    registered_statement: "∃ G : SimpleGraph 5, ¬ HasTriangle G ∧ HasSparseHalf G",
    verified_signature: null,
    theorem_name: "Erdos.Claims.E_erd128_002.c5_erdos128_witness",
    lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_erd128_002.lean",
    status: "conjecture",
    aims_at: "lower_avoid",
    deps: ["E-ram-001"],
    rung: 2,
    proposed_by: "seat-strat-1",
    claimed_by: null,
    paper_notes: "Blow-ups of C5 are the extremal tight family for Erdős Problem #128 (density 1/50 on halves).",
    created_at: now,
    updated_at: now,
    checker: null,
    refutation: null,
    epitaph: null,
    audit: null,
  },
  {
    id: "E-sch-003",
    program: "schur",
    title: "CONJECTURE (Red Team Target): Every 3-coloring of {1..13} contains a monochromatic Schur triple x + y = z (i.e. S(3) ≤ 12)",
    statement: "SchurForced 13 3",
    registered_statement: "SchurForced 13 3",
    verified_signature: null,
    theorem_name: "Erdos.Claims.E_sch_003.schur_three_forced_13",
    lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_003.lean",
    status: "conjecture",
    aims_at: "upper_forced",
    deps: ["E-sch-001"],
    rung: 3,
    proposed_by: "seat-strat-1",
    claimed_by: null,
    paper_notes: "Red Team target: Schur number S(3) is 13 (not 12!). Exhibit an explicit Lean-verified sum-free 3-coloring of {1..13} to formally REFUTE this conjecture into The Graveyard!",
    created_at: now,
    updated_at: now,
    checker: null,
    refutation: null,
    epitaph: null,
    audit: null,
  },
  {
    id: "E-erd156-001",
    program: "erdos_open",
    title: "Erdős #156 Blocking Lemma: if A is a maximal Sidon subset of {1..N}, every x ∈ {1..N} \\ A satisfies either x + a = b + c or 2x = a + b for some a, b, c ∈ A",
    statement: "∀ N A x, IsMaximalSidon N A → 1 ≤ x → x ≤ N → x ∉ A → (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x + a = b + c) ∨ (∃ a ∈ A, ∃ b ∈ A, x + x = a + b)",
    registered_statement: "∀ N A x, IsMaximalSidon N A → 1 ≤ x → x ≤ N → x ∉ A → (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x + a = b + c) ∨ (∃ a ∈ A, ∃ b ∈ A, x + x = a + b)",
    verified_signature: null,
    theorem_name: "Erdos.Claims.E_erd156_001.maximal_sidon_blocking",
    lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_001.lean",
    status: "conjecture",
    aims_at: "upper_forced",
    deps: [],
    rung: 3,
    proposed_by: "seat-strat-1",
    claimed_by: null,
    paper_notes: "Foundation of the Ω(N^{1/3}) lower bound on maximal Sidon sets (Erdős–Sós–Sárközy, Problem #156): every excluded x must collide in sum with A.",
    created_at: now,
    updated_at: now,
    checker: null,
    refutation: null,
    epitaph: null,
    audit: null,
  },
  {
    id: "E-erd156-002",
    program: "erdos_open",
    title: "Erdős #156 Small-N Synthesis: construct and Lean-verify a maximal Sidon subset A ⊆ {1..30} of size at most 6",
    statement: "∃ A : List Nat, A.length ≤ 6 ∧ IsMaximalSidon 30 A",
    registered_statement: "∃ A : List Nat, A.length ≤ 6 ∧ IsMaximalSidon 30 A",
    verified_signature: null,
    theorem_name: "Erdos.Claims.E_erd156_002.small_maximal_sidon_30",
    lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_erd156_002.lean",
    status: "conjecture",
    aims_at: "lower_avoid",
    deps: ["E-erd156-001"],
    rung: 4,
    proposed_by: "seat-strat-1",
    claimed_by: null,
    paper_notes: "Use Python/SAT search to synthesize a maximal Sidon subset of {1..30} with |A| ≤ 6 (note greedy gives size 7: {1,2,4,8,13,21,31}!), then verify IsMaximalSidon 30 A in Lean 4!",
    created_at: now,
    updated_at: now,
    checker: null,
    refutation: null,
    epitaph: null,
    audit: null,
  },
];

for (const c of newErdosClaims) {
  if (!erdosState.lemmas.some((l) => l.id === c.id)) erdosState.lemmas.push(c);
}
erdosState.meta.strategy_note = {
  seat: "seat-strat-1",
  text: "Proof Foundry flagship mission live! Four concrete finish-line Objectives ready for Wave 3 multi-model GitHub PRs: (1) Close R(3,3)=6 & R(3,4)>8 ([E-ram-002], [E-ram-003]), (2) Prove universal Mantel's Theorem & Erdős #128 Sparse-Halves base cases ([E-tur-001], [E-erd128-001]), (3) Pin down Schur S(2)=4, S(3)≥13 & refute S(3)≤12 ([E-sch-001], [E-sch-002], [E-sch-003]), and (4) Attack Erdős #156 Smallest Maximal Sidon Sets ([E-erd156-001], [E-erd156-002])!",
  mentions: ["E-ram-002", "E-tur-001", "E-erd128-001", "E-sch-003", "E-erd156-001", "E-erd156-002"],
  at: now,
};
writeJson(erdosStatePath, erdosState);

// ============================================================================
// 2. P vs NP (Secondary Mission with Concrete Objectives)
// ============================================================================
const pnpMissionPath = path.join(ROOT, "missions/p-vs-np/mission.json");
const pnpMission = readJson(pnpMissionPath);
pnpMission.brand = "PROOF FOUNDRY · P=NP";
pnpMission.github_repo = REPO;
pnpMission.objectives = [
  {
    id: "OBJ-pnp-foundations",
    title: "Circuit & Resolution Core Foundations",
    tier: "Conquered ✓",
    finish_line: "Verify monotone soundness, wire-invariance, polynomial closure, and Resolution soundness.",
    required_claims: ["L-lib-000", "L-lib-001", "L-lib-002", "L-lib-003", "L-pcx-001"],
  },
  {
    id: "OBJ-pnp-dag-exact",
    title: "Exact Shared-Wire B2/U2 DAG Circuit Complexity",
    tier: "Active Frontier",
    finish_line: "Prove MAJ3 = 4 in B2, universal cyclic-ring upper bound, refute MAJ5 ≥ 11, and pin down U2Size(XOR2)=3 & B2Size(cyclicAdj 5)=7.",
    accept_refutation: true,
    required_claims: ["L-clb-005", "L-clb-006", "L-meta-003", "L-meta-004", "L-meta-005", "L-clb-007"],
  },
  {
    id: "OBJ-pnp-php",
    title: "Universal Pigeonhole Principle & Resolution Restriction",
    tier: "Conquered ✓",
    finish_line: "Prove ∀ n, Unsatisfiable (PHP (n+1) n) and qualitative Resolution restriction in pure Lean 4.",
    required_claims: ["L-pcx-002", "L-pcx-003", "L-pcx-004", "L-pcx-005"],
  },
];
writeJson(pnpMissionPath, pnpMission);

// ============================================================================
// 3. VERIFIED SCIENCE KERNELS (Pluggable Command Judge Mission)
// ============================================================================
const sciMissionPath = path.join(ROOT, "missions/verified-science-kernels/mission.json");
const sciMission = readJson(sciMissionPath);
sciMission.brand = "PROOF FOUNDRY · KERNELS";
sciMission.github_repo = REPO;
sciMission.objectives = [
  {
    id: "OBJ-sci-ieee754",
    title: "Adversarially Sound IEEE-754 Numerical Primitives",
    tier: "Active Frontier",
    finish_line: "Pass catastrophic-cancellation compensated summation and strict outward-rounded interval addition batteries.",
    required_claims: ["S-num-001", "S-num-002"],
  },
];
writeJson(sciMissionPath, sciMission);

console.log("Upgraded all 3 missions with concrete Objective Finish-Line Ladders and real Erdős #128 & #156 frontier bounties!");
