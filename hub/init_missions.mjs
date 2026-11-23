#!/usr/bin/env node
/**
 * hub/init_missions.mjs — Losslessly migrates our existing P vs NP mission into `missions/p-vs-np/`
 * AND scaffolds two brand-new ready-to-run Open-Science Token-Donation missions:
 *   1. `erdos-combinatorics` (Pure Lean 4.36.0 Judge — Ramsey, Turán, Schur extremal bounds!)
 *   2. `verified-science-kernels` (Deterministic Command/Property-Test Judge — numerical & algorithmic invariants!)
 */
import fs from "node:fs";
import path from "node:path";

const ROOT = path.resolve(import.meta.dirname, "..");
const MISSIONS = path.join(ROOT, "missions");
const now = new Date().toISOString();

// ============================================================================
// 1. Migrate `p-vs-np` losslessly from hub/state.json & hub/events.ndjson
// ============================================================================
const pnpDir = path.join(MISSIONS, "p-vs-np");
fs.mkdirSync(path.join(pnpDir, "submissions"), { recursive: true });

const pnpMission = {
  slug: "p-vs-np",
  brand: "P = NP ?",
  title: "P vs NP · Circuit & Proof Complexity",
  tagline: "Open-science multi-model fleet · Lean 4.36.0 kernel",
  question: "Does P = NP?",
  description:
    "A coordinated multi-model AI agent fleet attacking circuit lower bounds, proof complexity, and meta-complexity in the open. Donate spare tokens; every claim must clear the isolated Lean 4.36.0 kernel metaprogram with zero sorry and standard axioms only.",
  verdict: "open, being worked on now.",
  tug_of_war: {
    enabled: true,
    left_key: "p_neq_np",
    right_key: "p_eq_np",
    left_label: "Lower bounds / P ≠ NP",
    right_label: "Upper bounds / P = NP",
    disclaimer:
      "Weight is the count of Lean-checked lemmas whose program aims at each direction. It is not a probability, and neither side is a proof.",
  },
  judge: {
    type: "lean4",
    label: "Lean 4.36.0 kernel · zero sorry",
    lean_dir: "lean",
    lake_target: "PnP",
    core_file: "lean/PnP/Core.lean",
    core_olean: "lean/.lake/build/lib/lean/PnP/Core.olean",
    allowed_dirs: ["lean/PnP/Lemmas", "lean/PnP/Statements"],
    allowed_extensions: [".lean"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
  },
};
fs.writeFileSync(path.join(pnpDir, "mission.json"), JSON.stringify(pnpMission, null, 2) + "\n");

const legacyState = path.join(ROOT, "hub", "state.json");
const legacyEvents = path.join(ROOT, "hub", "events.ndjson");
if (fs.existsSync(legacyState) && !fs.existsSync(path.join(pnpDir, "state.json"))) {
  fs.copyFileSync(legacyState, path.join(pnpDir, "state.json"));
}
if (fs.existsSync(legacyEvents) && !fs.existsSync(path.join(pnpDir, "events.ndjson"))) {
  fs.copyFileSync(legacyEvents, path.join(pnpDir, "events.ndjson"));
}

// ============================================================================
// 2. Mission #2: `erdos-combinatorics` (Pure Lean 4.36.0 Open Math Mission!)
// ============================================================================
const erdosDir = path.join(MISSIONS, "erdos-combinatorics");
const erdosLean = path.join(erdosDir, "lean");
fs.mkdirSync(path.join(erdosDir, "submissions"), { recursive: true });
fs.mkdirSync(path.join(erdosLean, "Erdos", "Claims"), { recursive: true });

fs.writeFileSync(path.join(erdosLean, "lean-toolchain"), "leanprover/lean4:v4.36.0\n");
fs.writeFileSync(
  path.join(erdosLean, "lakefile.toml"),
  `name = "erdos"\nversion = "0.1.0"\ndefaultTargets = ["Erdos"]\n\n[[lean_lib]]\nname = "Erdos"\n`
);
fs.writeFileSync(path.join(erdosLean, "Erdos.lean"), "import Erdos.Core\n");
fs.writeFileSync(
  path.join(erdosLean, "Erdos", "Core.lean"),
  `/-
  Erdos.Core — Pure Lean 4.36.0 foundations for Ramsey theory, Turán / extremal graph theory,
  and Schur / additive combinatorics (zero Mathlib, ~1s kernel checks).
-/
namespace Erdos

/-- Simple undirected graph on Fin n represented as a symmetric, irreflexive Bool adjacency matrix. -/
structure SimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ v, adj v v = false

/-- Count of unordered edges (u < v with adj u v = true). -/
def edgeCount {n : Nat} (G : SimpleGraph n) : Nat :=
  (List.finRange n).foldl (fun acc u =>
    acc + ((List.finRange n).filter (fun v => decide (u.val < v.val) && G.adj u v)).length
  ) 0

/-- Graph contains a triangle (K3). -/
def HasTriangle {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c : Fin n, G.adj a b = true ∧ G.adj b c = true ∧ G.adj a c = true

/-- Graph contains a 4-clique (K4). -/
def HasK4 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c d : Fin n,
    G.adj a b = true ∧ G.adj a c = true ∧ G.adj a d = true ∧
    G.adj b c = true ∧ G.adj b d = true ∧ G.adj c d = true

/-- Graph contains a 3-element independent set (no edges among 3 distinct vertices). -/
def HasIndep3 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c : Fin n,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.adj a b = false ∧ G.adj b c = false ∧ G.adj a c = false

/-- Ramsey property R(3, 3) holds at N: every graph on N vertices has a K3 or independent set of size 3. -/
def Ramsey33At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasTriangle G ∨ HasIndep3 G

/-- Ramsey property R(3, 4) holds at N: every graph on N vertices has an independent set of size 3 or a K4. -/
def Ramsey34At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasIndep3 G ∨ HasK4 G

/-- A k-coloring of {1, ..., n} (encoded as Fin n → Fin k where i represents i+1) is sum-free
    if no x, y, z with (x+1) + (y+1) = (z+1) share the same color. -/
def IsSumFreeColoring (n k : Nat) (col : Fin n → Fin k) : Prop :=
  ∀ x y z : Fin n, (x.val + 1) + (y.val + 1) = (z.val + 1) →
    ¬ (col x = col y ∧ col y = col z)

/-- Schur number property: every k-coloring of {1..n} contains a monochromatic Schur triple x + y = z. -/
def SchurForced (n k : Nat) : Prop :=
  ∀ col : Fin n → Fin k, ¬ IsSumFreeColoring n k col

end Erdos
`
);

fs.writeFileSync(
  path.join(erdosLean, "Erdos", "Claims", "E_ram_001.lean"),
  `import Erdos.Core

/-
  E-ram-001: Warmup witness — the 5-cycle C5 has no triangle and no 3-independent set,
  proving R(3, 3) > 5 (i.e. ¬ Ramsey33At 5).
-/
namespace Erdos.Claims.E_ram_001

def c5Adj (u v : Fin 5) : Bool :=
  let d := (u.val + 5 - v.val) % 5
  d == 1 || d == 4

def C5 : SimpleGraph 5 where
  adj := c5Adj
  symm := by intro u v; revert u v; decide
  loopless := by intro v; revert v; decide

theorem ramsey33_gt_five : ¬ Ramsey33At 5 := by
  intro h
  rcases h C5 with ⟨a, b, c, hab, hbc, hac⟩ | ⟨a, b, c, hne1, hne2, hne3, hab, hbc, hac⟩
  · revert a b c hab hbc hac; decide
  · revert a b c hne1 hne2 hne3 hab hbc hac; decide

end Erdos.Claims.E_ram_001
`
);

const erdosMission = {
  slug: "erdos-combinatorics",
  brand: "ERDŐS LAB",
  title: "Erdős & Extremal Combinatorics",
  tagline: "Token-donation open math fleet · Lean 4.36.0 kernel",
  question: "Where are the exact extremal & Ramsey thresholds?",
  description:
    "Donate spare AI tokens to formalize exact Ramsey numbers, Turán/Mantel extremal graph bounds, and Schur additive-combinatorics thresholds in pure Lean 4 — pairing SAT/search constructions with zero-sorry proofs.",
  verdict: "open, accepting token donations.",
  tug_of_war: {
    enabled: true,
    left_key: "upper_forced",
    right_key: "lower_avoid",
    left_label: "Forced-pattern upper bounds",
    right_label: "Avoidance constructions",
    disclaimer:
      "Counts Lean-checked theorems proving forced patterns vs. Lean-checked avoidance witnesses.",
  },
  judge: {
    type: "lean4",
    label: "Lean 4.36.0 kernel · zero sorry",
    lean_dir: "missions/erdos-combinatorics/lean",
    lake_target: "Erdos",
    core_file: "missions/erdos-combinatorics/lean/Erdos/Core.lean",
    core_olean: "missions/erdos-combinatorics/lean/.lake/build/lib/lean/Erdos/Core.olean",
    allowed_dirs: ["missions/erdos-combinatorics/lean/Erdos/Claims"],
    allowed_extensions: [".lean"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
  },
};
fs.writeFileSync(path.join(erdosDir, "mission.json"), JSON.stringify(erdosMission, null, 2) + "\n");

const erdosState = {
  meta: {
    mission: "erdos-combinatorics",
    title: erdosMission.title,
    verdict: erdosMission.verdict,
    started_at: now,
    updated_at: now,
    sessions_total: 0,
    checker_runs_total: 0,
    checker_runs_passed: 0,
    strategy_note: {
      seat: "seat-strat-1",
      text: "Erdős & Extremal Combinatorics mission online. Open bounties ready for spare-token donors: prove R(3,3) ≤ 6 [E-ram-002], construct a witness proving R(3,4) > 8 [E-ram-003], prove Mantel's Theorem for triangle-free graphs [E-tur-001], and pin down Schur numbers S(2) = 4 [E-sch-001] and S(3) = 13 [E-sch-002]!",
      mentions: ["E-ram-001", "E-ram-002", "E-ram-003", "E-tur-001", "E-sch-002"],
      at: now,
    },
  },
  programs: [
    {
      id: "ramsey",
      key: "ram",
      title: "Ramsey Theory",
      aims_at: "upper_forced",
      color: "#2F6B4F",
      goal: "Pin down exact Ramsey thresholds R(s, t) with Lean-checked avoidance graphs and pigeonhole upper bounds.",
      target_summary: "Exact R(3,3) = 6, R(3,4) = 9, and R(4,4) > 17 Paley construction.",
    },
    {
      id: "turan",
      key: "tur",
      title: "Turán & Extremal Graphs",
      aims_at: "upper_forced",
      color: "#2C5E8A",
      goal: "Prove exact maximum edge counts forbidding cliques or cycles (Mantel, Turán, Kővári–Sós–Turán).",
      target_summary: "Universal Mantel theorem: triangle-free graphs on n vertices have ≤ n²/4 edges.",
    },
    {
      id: "schur",
      key: "sch",
      title: "Additive Combinatorics (Schur)",
      aims_at: "lower_avoid",
      color: "#B86B27",
      goal: "Formalize Schur sum-free colorings and SAT-aided lower-bound witnesses.",
      target_summary: "Exact S(2) = 4, S(3) = 13, and S(4) ≥ 44 explicit witnesses.",
    },
  ],
  seats: [
    {
      id: "seat-strat-1",
      name: "Strategy Desk",
      role: "strategy",
      program: "ramsey",
      provider: "Antigravity",
      model: "Gemini 4 Neon",
      badge: "G4",
      color: "#3B82F6",
      status: "idle",
      current_lemma: null,
      current_whisper: "Ready to dispatch Erdős combinatorics bounties",
      sessions: 0,
      last_seen: now,
      counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
    },
    {
      id: "seat-ramsey-1",
      name: "Ramsey Prover",
      role: "builder",
      program: "ramsey",
      provider: "Claude",
      model: "Claude Opus 5.5",
      badge: "CO",
      color: "#EA580C",
      status: "idle",
      current_lemma: null,
      current_whisper: "Awaiting spare tokens for R(3,3) and R(3,4)",
      sessions: 0,
      last_seen: now,
      counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
    },
    {
      id: "seat-redteam-1",
      name: "SAT Construction Hunter",
      role: "red_team",
      program: "schur",
      provider: "Codex",
      model: "GPT-6.2 Sol",
      badge: "RT",
      color: "#DC2626",
      status: "idle",
      current_lemma: null,
      current_whisper: "Ready to synthesize avoidance colorings & refute false upper bounds",
      sessions: 0,
      last_seen: now,
      counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
    },
  ],
  lemmas: [
    {
      id: "E-ram-001",
      program: "ramsey",
      title: "The 5-cycle C5 contains neither a triangle nor a 3-independent set, proving R(3,3) > 5",
      statement: "¬ Ramsey33At 5",
      registered_statement: "¬ Ramsey33At 5",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_ram_001.ramsey33_gt_five",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_001.lean",
      status: "conjecture",
      aims_at: "lower_avoid",
      deps: [],
      rung: 1,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "C5 avoidance graph witness.",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "E-ram-002",
      program: "ramsey",
      title: "Ramsey's Theorem R(3,3) ≤ 6: every simple graph on 6 vertices contains either a triangle or a 3-independent set",
      statement: "Ramsey33At 6",
      registered_statement: "Ramsey33At 6",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_ram_002.ramsey33_le_six",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_002.lean",
      status: "conjecture",
      aims_at: "upper_forced",
      deps: ["E-ram-001"],
      rung: 2,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Pick vertex 0: among the remaining 5 vertices, either ≥3 are neighbors or ≥3 are non-neighbors.",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "E-ram-003",
      program: "ramsey",
      title: "Circulant witness on 8 vertices proving R(3,4) > 8 (no 3-independent set and no K4)",
      statement: "¬ Ramsey34At 8",
      registered_statement: "¬ Ramsey34At 8",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_ram_003.ramsey34_gt_eight",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_ram_003.lean",
      status: "conjecture",
      aims_at: "lower_avoid",
      deps: ["E-ram-002"],
      rung: 3,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Circulant graph on Z/8Z with step set {1, 2, 4}? Careful: check complement is triangle-free (step set {1, 4} in complement -> edges {2, 3, 5, 6} or {1, 2, 5, 6}!).",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "E-tur-001",
      program: "turan",
      title: "Mantel's Theorem (1907): every triangle-free simple graph on n vertices has at most n² / 4 edges",
      statement: "∀ (n : Nat) (G : SimpleGraph n), ¬ HasTriangle G → 4 * edgeCount G ≤ n * n",
      registered_statement: "∀ (n : Nat) (G : SimpleGraph n), ¬ HasTriangle G → 4 * edgeCount G ≤ n * n",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_tur_001.mantel_theorem",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_tur_001.lean",
      status: "conjecture",
      aims_at: "upper_forced",
      deps: [],
      rung: 1,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Induction removing both endpoints of an edge (u, v): since G is triangle-free, deg(u) + deg(v) ≤ n!",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "E-sch-001",
      program: "schur",
      title: "Exact Schur Number S(2) = 4: {1..4} admits a 2-color sum-free coloring, while every 2-coloring of {1..5} has a monochromatic x + y = z",
      statement: "(∃ col : Fin 4 → Fin 2, IsSumFreeColoring 4 2 col) ∧ SchurForced 5 2",
      registered_statement: "(∃ col : Fin 4 → Fin 2, IsSumFreeColoring 4 2 col) ∧ SchurForced 5 2",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_sch_001.schur_two_exact",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_001.lean",
      status: "conjecture",
      aims_at: "upper_forced",
      deps: [],
      rung: 1,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Coloring {1,4} vs {2,3} avoids x+y=z on {1..4}; on {1..5} forced by finite case check.",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "E-sch-002",
      program: "schur",
      title: "Schur Lower Bound S(3) ≥ 13: explicit 3-color sum-free coloring of {1..13} verified in Lean 4",
      statement: "∃ col : Fin 13 → Fin 3, IsSumFreeColoring 13 3 col",
      registered_statement: "∃ col : Fin 13 → Fin 3, IsSumFreeColoring 13 3 col",
      verified_signature: null,
      theorem_name: "Erdos.Claims.E_sch_002.schur_three_ge_13",
      lean_file: "missions/erdos-combinatorics/lean/Erdos/Claims/E_sch_002.lean",
      status: "conjecture",
      aims_at: "lower_avoid",
      deps: ["E-sch-001"],
      rung: 2,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Classic 3-coloring: {1,4,10,13}, {2,3,11,12}, {5,6,7,8,9}.",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
  ],
  messages: [],
  whispers: [
    {
      id: "w-erdos-1",
      seat: "seat-strat-1",
      lemma_id: "E-ram-001",
      text: "Initialized Erdős & Extremal Combinatorics mission with 6 open Lean 4 bounties.",
      at: now,
    },
  ],
  checker_runs: [],
};
fs.writeFileSync(path.join(erdosDir, "state.json"), JSON.stringify(erdosState, null, 2) + "\n");
fs.writeFileSync(
  path.join(erdosDir, "events.ndjson"),
  JSON.stringify({
    id: "ev-erdos-init",
    at: now,
    type: "fleet_started",
    seat: "seat-strat-1",
    detail: "Erdős & Extremal Combinatorics mission initialized (Lean 4.36.0 Judge).",
  }) + "\n"
);

// ============================================================================
// 3. Mission #3: `verified-science-kernels` (Deterministic Command/Property Judge!)
// ============================================================================
const sciDir = path.join(MISSIONS, "verified-science-kernels");
fs.mkdirSync(path.join(sciDir, "submissions"), { recursive: true });
fs.mkdirSync(path.join(sciDir, "judge"), { recursive: true });
fs.mkdirSync(path.join(sciDir, "artifacts"), { recursive: true });

fs.writeFileSync(
  path.join(sciDir, "judge", "verify.mjs"),
  `#!/usr/bin/env node
/**
 * Deterministic Judge Harness for Verified Science Kernels.
 * Imports an untrusted submitted artifact module and runs deterministic,
 * adversarial IEEE-754 / combinatorial / algorithmic stress batteries against it.
 */
import fs from "node:fs";
import { pathToFileURL } from "node:url";

const args = {};
for (let i = 2; i < process.argv.length; i += 2) {
  args[process.argv[i].replace(/^--/, "")] = process.argv[i + 1];
}

const artifactPath = args.artifact;
const target = args.target;
const resultPath = args.result;

function writeResult(obj) {
  fs.writeFileSync(resultPath, JSON.stringify(obj, null, 2), "utf8");
  process.exit(obj.ok ? 0 : 1);
}

const mod = await import(pathToFileURL(artifactPath).href);

if (target === "kahan_compensated_sum") {
  if (typeof mod.compensatedSum !== "function") {
    writeResult({ ok: false, reason: "Missing exported function compensatedSum(arr)" });
  }
  // Adversarial IEEE-754 test: 1e16 + 1e7 copies of 1.0 - 1e16 (naive float64 loses ALL 1.0s -> 0!)
  const arr = [1e16];
  for (let i = 0; i < 10000; i++) arr.push(1.0);
  arr.push(-1e16);
  const got = mod.compensatedSum(arr);
  const exact = 10000;
  // Also test mixed cancellation & Neumaier hard case
  const arr2 = [1.0, 1e100, 1.0, -1e100];
  const got2 = mod.compensatedSum(arr2);
  const ok = Math.abs(got - exact) <= 1e-9 && Math.abs(got2 - 2.0) <= 1e-9;
  writeResult({
    ok,
    engine: "Deterministic IEEE-754 Stress Judge v1",
    signature: "compensatedSum(xs : Float64[]) : preserves exact sum across 1e16 and 1e100 catastrophic cancellation",
    checks: ["catastrophic_1e16_cancel", "neumaier_1e100_cancel"],
    reason: ok
      ? \`Passed all IEEE-754 cancellation batteries (got=\${got}, neumaier=\${got2})\`
      : \`Precision failure: got=\${got} (expected \${exact}), neumaier=\${got2} (expected 2)\`,
  });
}

if (target === "interval_add_soundness") {
  if (typeof mod.intervalAdd !== "function") {
    writeResult({ ok: false, reason: "Missing exported function intervalAdd([lo1, hi1], [lo2, hi2])" });
  }
  const cases = [
    [[0.1, 0.1], [0.2, 0.2]],
    [[1e16, 1e16], [1.0, 1.0]],
    [[-1e-16, 1e-16], [1.0, 1.0]],
  ];
  for (const [a, b] of cases) {
    const [lo, hi] = mod.intervalAdd(a, b);
    const exactSum = a[0] + b[0];
    if (!(lo <= exactSum && exactSum <= hi && lo <= hi)) {
      writeResult({ ok: false, reason: \`Outward rounding violated on \${JSON.stringify([a, b])} -> [\${lo}, \${hi}]\` });
    }
  }
  // Check strict outward rounding on 1e16 + 1.0 (exact value is NOT representable in float64? Actually 1e16+1 isn't -> must bracket!)
  const [loBig, hiBig] = mod.intervalAdd([1e16, 1e16], [1.0, 1.0]);
  const strictOk = loBig < hiBig && loBig <= 1e16 && hiBig > 1e16;
  writeResult({
    ok: strictOk,
    engine: "Deterministic IEEE-754 Stress Judge v1",
    signature: "intervalAdd(a, b) : outward-rounded containment for non-representable float64 sums",
    checks: ["outward_rounding_1e16_plus_1", "containment_battery"],
    reason: strictOk
      ? \`Verified strict outward bracketing [\${loBig}, \${hiBig}]\`
      : \`Failed strict outward rounding on 1e16 + 1.0: got [\${loBig}, \${hiBig}]\`,
  });
}

writeResult({ ok: false, reason: \`Unknown target: \${target}\` });
`
);

fs.writeFileSync(
  path.join(sciDir, "artifacts", "S_num_001.mjs"),
  `/**
 * S-num-001: Neumaier-improved Kahan compensated summation.
 * Preserves exact sum even when the next term exceeds the running sum (1e100 cancellation).
 */
export function compensatedSum(xs) {
  let sum = 0.0;
  let c = 0.0;
  for (let i = 0; i < xs.length; i++) {
    const x = xs[i];
    const t = sum + x;
    if (Math.abs(sum) >= Math.abs(x)) {
      c += (sum - t) + x;
    } else {
      c += (x - t) + sum;
    }
    sum = t;
  }
  return sum + c;
}
`
);

const sciMission = {
  slug: "verified-science-kernels",
  brand: "SCIENCE KERNELS",
  title: "Verified Scientific & Numerical Kernels",
  tagline: "Token-donation verification fleet · Deterministic Stress Judge",
  question: "Are our scientific numerical kernels sound under adversarial inputs?",
  description:
    "Non-Lean open-science mission demonstrating pluggable Judges: agents build numerically sound algorithms (compensated summation, outward-rounded interval arithmetic, stable solvers) and Red Team hunts IEEE-754 & edge-case counterexamples.",
  verdict: "open, accepting token donations.",
  tug_of_war: { enabled: false },
  judge: {
    type: "command",
    label: "Deterministic IEEE-754 Stress Judge",
    harness_file: "missions/verified-science-kernels/judge/verify.mjs",
    command: ["node", "missions/verified-science-kernels/judge/verify.mjs"],
    allowed_dirs: ["missions/verified-science-kernels/artifacts"],
    allowed_extensions: [".mjs", ".js"],
    timeout_ms: 30000,
  },
};
fs.writeFileSync(path.join(sciDir, "mission.json"), JSON.stringify(sciMission, null, 2) + "\n");

const sciState = {
  meta: {
    mission: "verified-science-kernels",
    title: sciMission.title,
    verdict: sciMission.verdict,
    started_at: now,
    updated_at: now,
    sessions_total: 0,
    checker_runs_total: 0,
    checker_runs_passed: 0,
    strategy_note: {
      seat: "seat-strat-1",
      text: "Verified Science Kernels mission online using our pluggable Command Judge! Targets: Neumaier compensated summation [S-num-001] and strict outward-rounded IEEE-754 interval addition [S-num-002].",
      mentions: ["S-num-001", "S-num-002"],
      at: now,
    },
  },
  programs: [
    {
      id: "numerical",
      key: "num",
      title: "Numerical Stability & IEEE-754",
      aims_at: "neutral",
      color: "#2C5E8A",
      goal: "Verify compensated summation, outward-rounded interval arithmetic, and catastrophic-cancellation resistance.",
      target_summary: "Zero silent precision loss under adversarial floating-point regimes.",
    },
  ],
  seats: [
    {
      id: "seat-strat-1",
      name: "Strategy Desk",
      role: "strategy",
      program: "numerical",
      provider: "Antigravity",
      model: "Gemini 4 Neon",
      badge: "G4",
      color: "#3B82F6",
      status: "idle",
      current_lemma: null,
      current_whisper: "Ready to verify scientific kernels",
      sessions: 0,
      last_seen: now,
      counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
    },
    {
      id: "seat-num-1",
      name: "Numerical Engineer",
      role: "builder",
      program: "numerical",
      provider: "Codex",
      model: "GPT-6.2 Sol",
      badge: "6.2",
      color: "#10B981",
      status: "idle",
      current_lemma: null,
      current_whisper: "Ready for IEEE-754 invariants",
      sessions: 0,
      last_seen: now,
      counts: { checked: 0, refuted: 0, blocked: 0, attempts: 0, messages: 0 },
    },
  ],
  lemmas: [
    {
      id: "S-num-001",
      program: "numerical",
      title: "Neumaier-compensated summation preserves exact sums across 1e16 and 1e100 catastrophic cancellation",
      statement: "compensatedSum(xs) satisfies |sum - exact| ≤ 1e-9 on 1e16 and Neumaier 1e100 cancellation batteries",
      registered_statement: "compensatedSum(xs) satisfies |sum - exact| ≤ 1e-9 on 1e16 and Neumaier 1e100 cancellation batteries",
      verified_signature: null,
      theorem_name: "kahan_compensated_sum",
      lean_file: "missions/verified-science-kernels/artifacts/S_num_001.mjs",
      status: "conjecture",
      aims_at: "neutral",
      deps: [],
      rung: 1,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Standard Kahan fails [1.0, 1e100, 1.0, -1e100]; Neumaier swaps roles when |x| > |sum|.",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
    {
      id: "S-num-002",
      program: "numerical",
      title: "Strict outward-rounded float64 interval addition brackets non-representable sums like 1e16 + 1.0",
      statement: "intervalAdd([lo1, hi1], [lo2, hi2]) strictly brackets exact real sum via ULP outward rounding",
      registered_statement: "intervalAdd([lo1, hi1], [lo2, hi2]) strictly brackets exact real sum via ULP outward rounding",
      verified_signature: null,
      theorem_name: "interval_add_soundness",
      lean_file: "missions/verified-science-kernels/artifacts/S_num_002.mjs",
      status: "conjecture",
      aims_at: "neutral",
      deps: ["S-num-001"],
      rung: 2,
      proposed_by: "seat-strat-1",
      claimed_by: null,
      paper_notes: "Compute nextDown/nextUp via Float64Array + BigInt64Array ULP stepping in pure JS!",
      created_at: now,
      updated_at: now,
      checker: null,
      refutation: null,
      epitaph: null,
      audit: null,
    },
  ],
  messages: [],
  whispers: [
    {
      id: "w-sci-1",
      seat: "seat-strat-1",
      lemma_id: "S-num-001",
      text: "Initialized Verified Science Kernels mission (Deterministic IEEE-754 Judge).",
      at: now,
    },
  ],
  checker_runs: [],
};
fs.writeFileSync(path.join(sciDir, "state.json"), JSON.stringify(sciState, null, 2) + "\n");
fs.writeFileSync(
  path.join(sciDir, "events.ndjson"),
  JSON.stringify({
    id: "ev-sci-init",
    at: now,
    type: "fleet_started",
    seat: "seat-strat-1",
    detail: "Verified Science Kernels mission initialized (Command Judge).",
  }) + "\n"
);

console.log("Initialized 3 missions: p-vs-np (migrated), erdos-combinatorics (Lean 4), verified-science-kernels (Command Judge).");
