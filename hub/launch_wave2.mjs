#!/usr/bin/env node
/**
 * hub/launch_wave2.mjs — Registers Wave 2 frontier lemmas (Exact B2/U2 DAG Circuit Complexity,
 * Gate Elimination, Adversarial SAT/Circuit Synthesis Red Team, Universal PHP(n+1,n),
 * Resolution Restriction, and Formal Relativization Barrier) and dispatches 5 multi-model seats.
 */
import { spawnSync } from "node:child_process";
import path from "node:path";

const ROOT = path.resolve(import.meta.dirname, "..");
const NODE_BIN = process.env.T3_ACP_MCP_NODE;
const ENTRY = process.env.T3_ACP_MCP_ENTRYPOINT;

function cli(args) {
  const res = spawnSync("node", [path.join(ROOT, "hub/cli.mjs"), ...args], {
    encoding: "utf8",
    cwd: ROOT,
  });
  if (res.status !== 0 && !String(res.stderr + res.stdout).includes("already exists")) {
    throw new Error(`cli failed: ${args.join(" ")}\n${res.stdout}\n${res.stderr}`);
  }
  return res.stdout.trim();
}

function callT3(tool, argsObj) {
  if (!NODE_BIN) throw new Error("T3_ACP_MCP_NODE not set");
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

// 1. Register Wave 2 Frontier Lemmas
const WAVE2_LEMMAS = [
  // Library: Gate-elimination infrastructure
  {
    id: "L-lib-004",
    program: "library",
    title: "B2 DAG Restriction & Gate Elimination: fixing an input wire simplifies a B2Circuit without increasing size, and eliminates every gate whose inputs become constant",
    statement: "∀ {n} (c : B2Circuit (n + 1)) (b : Bool), ∃ c' : B2Circuit n, c'.size ≤ c.size ∧ ∀ x, c'.eval x = c.eval (snocVec x b)",
    theorem: "PnP.Lemmas.L_lib_004.b2_restrict_size_le",
    deps: "L-lib-002",
    aims: "neutral",
    rung: "5",
    paper: "Core formal foundation for Blum/Schnorr/Zwick gate-elimination proofs on shared-wire B2 circuits.",
  },
  // Circuit Lower Bounds: General DAG lower bound + Cyclic Ring Exact Upper & Lower Bounds
  {
    id: "L-clb-005",
    program: "circuit_lower_bounds",
    title: "Shared-wire DAG Lower Bound: any B2Circuit computing a function that depends on all n inputs requires at least n - 1 gates",
    statement: "∀ {n} (c : B2Circuit n) (f : BoolFn n), c.Computes f → (∀ i, DependsOn f i) → n ≤ c.size + 1",
    theorem: "PnP.Lemmas.L_clb_005.b2_depends_all_lower_bound",
    deps: "L-clb-002",
    aims: "p_neq_np",
    rung: "5",
    paper: "Component-counting / wire-reachability proof for arbitrary shared-wire B2 DAGs (not just formula trees!): each gate adds at most 1 edge merging input components.",
  },
  {
    id: "L-clb-006",
    program: "circuit_lower_bounds",
    title: "Exact Ring Upper Bound: for every n ≥ 5, cyclic-adjacent-ones on an n-ring has a U2/B2 DAG circuit with at most n + (n + 1) / 2 - 1 gates",
    statement: "∀ n ≥ 5, ∃ c : B2Circuit n, c.isU2 = true ∧ c.size ≤ n + (n + 1) / 2 - 1 ∧ c.Computes (cyclicAdj n)",
    theorem: "PnP.Lemmas.L_clb_006.cyclicAdj_upper_bound",
    deps: "L-clb-005",
    aims: "p_neq_np",
    rung: "6",
    paper: "Factor pairs of edges sharing a vertex cover node: x_{2k} ∧ (x_{2k-1} ∨ x_{2k+1}), matching the exact n + ceil(n/2) - 1 frontier bound!",
  },
  {
    id: "L-clb-007",
    program: "circuit_lower_bounds",
    title: "CONJECTURE (Frontier contest): cyclicAdj 5 on a 5-ring requires at least 7 gates in the full B2 basis (can XOR beat the 7-gate U2 ring circuit?)",
    statement: "∀ c : B2Circuit 5, c.Computes (cyclicAdj 5) → 7 ≤ c.size",
    theorem: "PnP.Lemmas.L_clb_007.cyclicAdj5_b2_lower_bound",
    deps: "L-clb-006",
    aims: "p_neq_np",
    rung: "7",
    paper: "Open contest: U2 achieves 7 gates. Can Red Team synthesize a ≤ 6-gate B2 circuit using XOR/XNOR, or can Lower Bounds prove 7 is optimal?",
  },
  // Meta-complexity: Exact B2 gate complexity of MAJ3 and MAJ5!
  {
    id: "L-meta-003",
    program: "meta_complexity",
    title: "Exact B2 Circuit Complexity of MAJ3: 3-bit Majority requires at least 4 gates in the full binary basis B2 (matching the 4-gate upper bound gate for gate!)",
    statement: "(∃ c : B2Circuit 3, c.size = 4 ∧ c.Computes maj3) ∧ (∀ c : B2Circuit 3, c.Computes maj3 → 4 ≤ c.size)",
    theorem: "PnP.Lemmas.L_meta_003.maj3_exact_b2_size_four",
    deps: "L-meta-002",
    aims: "neutral",
    rung: "3",
    paper: "Genuine non-trivial exact DAG lower bound over all 16 binary ops (including XOR/XNOR) with arbitrary fan-out. Must rule out all 2-gate and 3-gate B2 DAGs!",
  },
  {
    id: "L-meta-004",
    program: "meta_complexity",
    title: "CONJECTURE (Red Team Synthesis Target): Every shared-wire B2 circuit computing 5-bit Majority (MAJ5) requires at least 11 gates",
    statement: "∀ c : B2Circuit 5, c.Computes maj5 → 11 ≤ c.size",
    theorem: "PnP.Lemmas.L_meta_004.maj5_b2_ge_11",
    deps: "L-meta-003",
    aims: "neutral",
    rung: "4",
    paper: "Known optimal B2 circuit for MAJ5 has 10 gates (Knuth/Kulikov). Red Team must actually synthesize a real ≤ 10-gate shared-wire B2Circuit 5 and verify it over all 32 inputs in Lean 4 to refute this!",
  },
  // P = NP / Algorithm Search: Circuit synthesis upper bounds
  {
    id: "L-alg-004",
    program: "p_eq_np_search",
    title: "Synthesized Shared-Wire B2 Circuit for MOD3=0 on 4 bits: construct and verify a compact shared-wire B2Circuit 4 computing mod3Eq0 4 in ≤ 7 gates",
    statement: "∃ c : B2Circuit 4, c.size ≤ 7 ∧ c.Computes (mod3Eq0 4)",
    theorem: "PnP.Lemmas.L_alg_004.mod3_4_compact_b2",
    deps: "L-alg-001",
    aims: "p_eq_np",
    rung: "4",
    paper: "Algorithmic circuit synthesis: exploit full B2 basis (XOR + AND/OR sharing) to compute Hamming weight ≡ 0 (mod 3) on 4 bits in ≤ 7 gates (naive CNF/DNF is much larger).",
  },
  // Proof Complexity: Universal PHP(n+1, n) UNSAT + Resolution Restriction Lemma
  {
    id: "L-pcx-004",
    program: "proof_complexity",
    title: "Universal Pigeonhole Principle: for EVERY n : Nat, the CNF encoding PHP(n + 1, n) is unsatisfiable",
    statement: "∀ n : Nat, Unsatisfiable (PHP (n + 1) n)",
    theorem: "PnP.Lemmas.L_pcx_004.php_succ_unsat",
    deps: "L-pcx-002",
    aims: "p_neq_np",
    rung: "4",
    paper: "Full universal induction over all n (not finite case-split!): map each pigeon to a chosen hole via a satisfying assignment and derive an injection Fin (n+1) → Fin n contradiction.",
  },
  {
    id: "L-pcx-005",
    program: "proof_complexity",
    title: "Resolution Restriction Lemma (Ben-Sasson–Wigderson foundation): restricting a variable maps any Resolution refutation of φ to a refutation of restrictCNF v b φ of no greater size or width",
    statement: "∀ (φ : CNF) (v : Nat) (b : Bool), ResDerivable φ [] → ResDerivable (restrictCNF v b φ) []",
    theorem: "PnP.Lemmas.L_pcx_005.resolution_restrict_preserves_refutation",
    deps: "L-pcx-001",
    aims: "p_neq_np",
    rung: "5",
    paper: "Core structural lemma of Ben-Sasson & Wigderson (2001) width-size tradeoff for Resolution lower bounds.",
  },
  // Barrier Desk: Formal Relativization Metatheorem + Algebrization Audit
  {
    id: "L-bar-003",
    program: "barrier_desk",
    title: "Formal Relativization Barrier Metatheorem: any proof property uniform over all oracles cannot separate two oracle-parameterized classes that collapse under one oracle and separate under another",
    statement: "∀ (P_O NP_O : Oracle → Prop), (∃ A, P_O A = NP_O A) → (∃ B, P_O B ≠ NP_O B) → ¬(∀ O, P_O O ≠ NP_O O) ∧ ¬(∀ O, P_O O = NP_O O)",
    theorem: "PnP.Lemmas.L_bar_003.relativization_barrier_meta",
    deps: "L-bar-001",
    aims: "neutral",
    rung: "3",
    paper: "Formalized Lean 4 metatheorem backing Baker-Gill-Solovay barrier rulings on the hub.",
  },
  {
    id: "L-bar-004",
    program: "barrier_desk",
    title: "Approach: Separate P from NP via IP = PSPACE arithmetization / low-degree polynomial extension over finite fields alone",
    statement: "-- Barrier audit target: arithmetization techniques invariant under low-degree algebraic oracle extensions",
    theorem: "PnP.Lemmas.L_bar_004.algebrizing_attack",
    deps: "L-bar-003",
    aims: "p_neq_np",
    rung: "4",
    paper: "Barrier Desk to audit against Aaronson-Wigderson (2009) Algebrization barrier.",
  },
];

for (const l of WAVE2_LEMMAS) {
  cli([
    "lemma-add",
    "--id", l.id,
    "--program", l.program,
    "--title", l.title,
    "--statement", l.statement,
    "--theorem", l.theorem,
    "--deps", l.deps,
    "--aims", l.aims,
    "--rung", l.rung,
    "--seat", "seat-strat-1",
    "--paper", l.paper,
  ]);
}

cli([
  "strategy-note",
  "--seat", "seat-strat-1",
  "--text", "Wave 2 launched: pivoting from warm-up foundations to Exact Shared-Wire B2/U2 DAG Circuit Complexity, Gate Elimination, Universal PHP(n+1,n), and Real Adversarial Circuit Synthesis! Highlights: exact B2 size=4 proof for MAJ3 [L-meta-003], universal cyclic-ring upper bound n+ceil(n/2)-1 [L-clb-006], universal PHP(n+1,n) UNSAT [L-pcx-004], and a live synthesis bounty on Red Team to synthesize a ≤10-gate B2 DAG for MAJ5 to refute [L-meta-004] and hunt for a <7-gate B2 circuit on cyclicAdj 5 [L-clb-007]!",
  "--mentions", "L-meta-003,L-meta-004,L-clb-006,L-clb-007,L-pcx-004,L-pcx-005",
]);

const COMMON_RULES = `
You are a live seat in Wave 2 of the local T3 Code P = NP ? Multi-Model Fleet at /Volumes/Storage/pnpenis2.
Read /Volumes/Storage/pnpenis2/FLEET_PLAYBOOK.md and /Volumes/Storage/pnpenis2/lean/PnP/Core.lean (NOTE: Section 5 now defines B2Op, B2Gate, B2Circuit, hammingWeight, thresh, maj5, mod3Eq0, cyclicAdj, restrictCNF!).
STRICT RULES:
1. Work ONLY in /Volumes/Storage/pnpenis2. NEVER edit lean/PnP/Core.lean or another seat's lemma files.
2. Put every proof in its own dedicated file under lean/PnP/Lemmas/ with \`import PnP.Core\` ONLY (self-contained so parallel seats never collide).
3. Use Lean 4.36.0 pure stdlib (NO Mathlib). Zero \`sorry\`, zero \`admit\`, zero custom \`axiom\`.
4. Claim each lemma BEFORE starting (\`node hub/cli.mjs claim ...\`), post live whispers (\`node hub/cli.mjs whisper ...\`), and send 1-2 crisp inter-seat dispatches (\`node hub/cli.mjs msg ...\`).
5. Run \`node hub/cli.mjs verify ...\` (or \`refute ...\` / \`rule-dead ...\`) and iterate until Lean 4 returns \`"ok": true\`.
6. When finished, set your seat(s) to \`idle\` (\`node hub/cli.mjs seat-state --seat <id> --status idle --whisper "..."\`) and reply with a concise summary.
7. Do NOT spawn subagents.
`.trim();

const WAVE_2 = [
  {
    clientRequestId: "wave2-seat-clb-1",
    title: "Wave 2 · seat-clb-1 & seat-lib-1 · Gate Elimination + Ring Upper Bound (GPT-6.2 Sol)",
    role: "implementation",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-sol",
      options: { reasoningEffort: "xhigh" },
    },
    task: `${COMMON_RULES}

YOUR SEATS: \`seat-lib-1\` and \`seat-clb-1\`.
PROVE AND VERIFY THESE THREE GENUINELY NON-TRIVIAL DAG CIRCUIT THEOREMS IN LEAN 4:

1. As \`seat-lib-1\`: \`L-lib-004\` -> \`lean/PnP/Lemmas/L_lib_004.lean\`, theorem \`PnP.Lemmas.L_lib_004.b2_restrict_size_le\`:
   Define \`snocVec {n : Nat} (x : BoolVec n) (b : Bool) : BoolVec (n + 1)\` (putting \`b\` at index \`n\`, and \`x i\` for \`i < n\`), and prove:
   \`theorem b2_restrict_size_le {n : Nat} (c : B2Circuit (n + 1)) (b : Bool) : ∃ c' : B2Circuit n, c'.size ≤ c.size ∧ ∀ x : BoolVec n, c'.eval x = c.eval (snocVec x b)\`
   (Careful: when restricting wire \`n\` to constant \`b\`, fold it into each gate that reads wire \`n\` using a specialized \`B2Op\`, and if \`outputWire = n\`, handle the constant output cleanly! Notice if \`c.gates = []\` and \`outputWire = n\` and \`b = true\`, wait: a 0-gate B2Circuit can only output an input wire or false (out of bounds)! So if \`c.gates = []\` and \`outputWire = n\` and \`b = true\`, you need 1 constant gate! CHECK THAT EDGE CASE! If \`c.size = 0\`, \`c'.size ≤ c.size + 1\` or require \`1 ≤ c.size\` or prove \`c'.size ≤ c.size\` whenever \`c.outputWire ≠ n ∨ b = false\` AND \`c'.size ≤ c.size\` whenever \`0 < c.size\`! Make sure the theorem statement you prove is 100% true and cleanly captures gate elimination — e.g. \`(hpos : 0 < c.size) → ∃ c' : B2Circuit n, c'.size ≤ c.size ∧ ∀ x, c'.eval x = c.eval (snocVec x b)\` — AND note that when a gate reads wire \`n\`, folding it into downstream gates eliminates that gate!)

2. As \`seat-clb-1\`: \`L-clb-005\` -> \`lean/PnP/Lemmas/L_clb_005.lean\`, theorem \`PnP.Lemmas.L_clb_005.b2_depends_all_lower_bound\`:
   \`theorem b2_depends_all_lower_bound {n : Nat} (c : B2Circuit n) (f : BoolFn n) (hc : c.Computes f) (hdep : ∀ i : Fin n, DependsOn f i) : n ≤ c.size + 1\`
   (Real shared-wire DAG lower bound! Hint: in the wire graph with \`n\` input vertices, each gate connects its two input wires \`w1, w2\` to its output wire \`n + k\`. If \`c.size + 1 < n\`, at least one input \`i : Fin n\` is NOT in the connected component of \`c.outputWire\` — wait: even simpler! Count wires reachable backward from \`outputWire\`: \`outputWire\` starts with 1 reachable node; walking backward through the \`c.size\` gates, each gate replaces 1 reachable gate-wire by at most 2 earlier wires, increasing the set of reachable wires by at most 1 per gate! So at most \`c.size + 1\` input wires can EVER be reachable from \`outputWire\`, and any unreachable input wire \`i\` cannot affect \`c.eval\`!)

3. As \`seat-clb-1\`: \`L-clb-006\` -> \`lean/PnP/Lemmas/L_clb_006.lean\`, theorem \`PnP.Lemmas.L_clb_006.cyclicAdj_upper_bound\`:
   \`theorem cyclicAdj_upper_bound (n : Nat) (hn : 5 ≤ n) : ∃ c : B2Circuit n, c.isU2 = true ∧ c.size ≤ n + (n + 1) / 2 - 1 ∧ c.Computes (cyclicAdj n)\`
   (Constructive universal family for ALL \`n ≥ 5\`! Group pairs of adjacent edges around even vertices \`0, 2, 4, ...\`: for \`n = 2k\`, cover \`0,2,...,2k-2\` gives \`k\` ORs + \`k\` ANDs + \`k-1\` top ORs = \`3k - 1 = n + n/2 - 1\`; for \`n = 2k+1\`, cover \`0,2,...,2k-2\` (covering \`2k\` edges) plus the leftover edge \`(2k-1, 2k)\` gives \`k\` ORs + \`(k+1)\` ANDs + \`k\` top ORs = \`3k + 1 = (2k+1) + (k+1) - 1 = n + (n+1)/2 - 1\`! Pure U2 basis, exact!)

Send dispatches to \`seat-strat-1\` and \`seat-redteam-1\` (daring Red Team on \`L-clb-007\`!) and set both seats back to \`idle\` when done.`,
  },
  {
    clientRequestId: "wave2-seat-meta-1",
    title: "Wave 2 · seat-meta-1 · Exact B2 Complexity of MAJ3 = 4 (Claude Opus 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-opus-5-5",
      options: { effort: "xhigh" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: \`seat-meta-1\` (Meta-complexity · Claude Opus 5.5).
THIS IS A GENUINELY HARD, NON-TRIVIAL EXACT DAG LOWER BOUND!

ASSIGNED LEMMA: \`L-meta-003\` -> \`lean/PnP/Lemmas/L_meta_003.lean\`, theorem \`PnP.Lemmas.L_meta_003.maj3_exact_b2_size_four\`:
\`theorem maj3_exact_b2_size_four : (∃ c : B2Circuit 3, c.size = 4 ∧ c.Computes maj3) ∧ (∀ c : B2Circuit 3, c.Computes maj3 → 4 ≤ c.size)\`

MATHEMATICAL PROOF IDEA (THINKING FIRST, LEAN SECOND!):
- **Upper bound (4 gates):** Easy! \`w3 = x0 ∧ x1\`, \`w4 = x0 ∨ x1\`, \`w5 = w4 ∧ x2\`, \`w6 = w3 ∨ w5\` (4 gates, computes \`maj3\`, checkable by finite evaluation on all 8 inputs!).
- **Lower bound (no 0, 1, 2, or 3-gate B2Circuit computes \`maj3\`):**
  This is a REAL theorem over ALL 16 binary ops (including XOR/XNOR) and arbitrary wire sharing!
  Smart proof strategy in Lean 4 (so it verifies in seconds without blowing up!):
  1. Notice every wire in a \`B2Circuit 3\` computes a truth table in \`Fin 256\` (an 8-bit \`UInt8\` or \`BitVec 8\` over the 8 inputs \`(0,0,0)..(1,1,1)\`!).
  2. Initial 3 input wires have fixed 8-bit truth tables \`t0, t1, t2\`, plus out-of-bounds wire reads \`0\` (const false).
  3. Actually, prove it by **clean structural/algebraic gate elimination** OR **fast verified truth-table reachability**:
     - Think how tiny 3-gate reachability is on 3 variables!
     - Wait: for a 3-gate circuit \`[g0, g1, g2]\`, the output is wire \`k\`. If \`k < 5\`, it's already a ≤ 2-gate circuit! If \`k = 5\` (the 3rd gate):
       - Gate 0 takes 2 of \`{0,1,2,const0}\` — by symmetry or directly, there are only 3 unordered input pairs \`(0,1),(0,2),(1,2)\` (or 16 ops × 16 wire pairs, collapsing to at most ~30 distinct 8-bit truth tables!).
       - Even better: **Algebraic / Gate-Elimination proof**!
         Wait: CAN you prove \`¬∃ c : B2Circuit 3, c.size ≤ 3 ∧ c.Computes maj3\` directly by gate elimination in ~60 lines of Lean?!
         LET'S CHECK! Suppose \`c\` has 3 gates \`g0, g1, g2\` and outputs wire 5 (\`g2\`).
         - Consider \`g0\` (first gate): its inputs are two of \`{x0, x1, x2, false}\`.
         - If \`g0\` depends on ≤ 1 variable, \`g0\` is redundant (depends on at most 1 input), so the remaining 2 gates can only touch at most 3 wires? Wait: 2 gates on 3 inputs can only depend on ≤ 3 variables ONLY if the 2 gates form a tree of 3 leaves: \`g1(x_a, x_b)\`, \`g2(g1, x_c)\`!
         - **KEY FACT:** ANY function computed by \`g2(g1(x_a, x_b), x_c)\` (i.e. a 2-gate formula on 3 inputs) has the property that fixing \`x_c = false\` and \`x_c = true\` yields two functions of \`(x_a, x_b)\` that are BOTH unary functions of \`g1(x_a, x_b)\` — i.e., **at least one of the cofactors \`f|_{x_c=0}\`, \`f|_{x_c=1}\` is constant or equal to the other or its negation**!
         - Check \`maj3\`: \`maj3|_{x_c=0} = x_a ∧ x_b\` (weight 1) and \`maj3|_{x_c=1} = x_a ∨ x_b\` (weight 3)! Neither is constant, neither equals the other, and \`¬(x_a ∧ x_b) = ¬x_a ∨ ¬x_b ≠ x_a ∨ x_b\`! So NO 2-gate circuit computes \`maj3\`!
         - Now for **3 gates** \`g0, g1, g2\`:
           Since \`g2\` is the output gate with 2 inputs \`(u, v)\`, either:
           - One of \`u, v\` is an input wire \`x_c\` (say \`v = x_c\`), and \`u\` is some earlier wire \`g1\` (or \`g0\`). Then BOTH cofactors \`maj3|_{x_c=0} = x_a ∧ x_b\` AND \`maj3|_{x_c=1} = x_a ∨ x_b\` must be unary functions of \`u|_{x_c=0}\` and \`u|_{x_c=1}\`! WAIT A SECOND: if \`u\` depends on \`x_c\`, \`u|_{x_c=0}\` and \`u|_{x_c=1}\` CAN be different!
           - So check! With \`BitVec 8\` (just 256 truth tables!), we can represent the exact reachable set of truth tables at depth 0, 1, 2, 3 via a tiny \`Bool\`-valued function or \`Array Bool\` of size 256 (or \`decide\` on a fast witness/certificate table!), OR a super crisp case split! Wait: 3 gates where \`g0\` computes a function of 2 inputs (only 3×16 = 48 possibilities -> at most 38 distinct truth tables after dedup), \`g1\` combines 2 of 4 wires (6 pairs × 16 = 96 -> at most ~1000? Even simpler: \`g2\` combines \`(u, v)\` to produce \`maj3\` — check if ANY pair \`(u, v)\` in the 2-gate reachable set can combine via a \`B2Op\` to equal \`maj3\`!).
           - WAIT A SECOND! Look how fast that check is:
             - Let \`S0\` = 4 truth tables \`{0, x0, x1, x2}\`.
             - For each \`g0\` (6 unordered pairs from \`S0\` × 16 ops → tiny list of ≤ 26 distinct truth tables \`t0\`),
             - Let \`S1(t0) = S0 ∪ {t0}\` (size 5).
             - For each \`g1\` (10 pairs from \`S1(t0)\` × 16 ops → ≤ 160 truth tables \`t1\`),
             - Check if \`maj3\` is achievable in 1 gate from \`S2 = S1(t0) ∪ {t1}\` (only 5 pairs involving \`t1\`, since pairs without \`t1\` already checked, × 16 ops = 80 checks!).
             - Total work: \`26 × 160 × 80 ≈ 330,000\` tiny 8-bit operations (or even smaller by normalizing \`B2Op\` to the 10 non-trivial ops up to negation: 10× fewer, ~30,000 checks — Lean 4 \`native_decide\` is FORBIDDEN because it adds \`Lean.ofReduceBool\` axiom! NEVER use \`native_decide\` — remember our checker ONLY allows \`propext\`, \`Classical.choice\`, \`Quot.sound\`!!).
           - **CRITICAL REMINDER:** NEVER use \`native_decide\` (it adds \`Lean.ofReduceBool\` which the Judge REJECTS!). Use a **structural / mathematical proof** (e.g., gate-elimination / cofactor classification of 3-gate circuits — actually classifying all 2-variable cofactors takes ONLY ~150 lines of clean Lean 4 and compiles in ~3 seconds with ZERO \`ofReduceBool\`!!).

Also, if you finish \`L-meta-003\` with time to spare, check \`L-clb-004\` (open Wave 1 depth-size tradeoff \`countDistinctInputs c ≤ 2 ^ c.depth\`) or propose a follow-up \`L-meta\` lemma!
Send a dispatch to \`seat-clb-1\` and \`seat-strat-1\` when checked, and set \`seat-meta-1\` to \`idle\`.`,
  },
  {
    clientRequestId: "wave2-seat-pcx-1",
    title: "Wave 2 · seat-pcx-1 · Universal PHP(n+1,n) & Resolution Restriction (Claude Sonnet 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-sonnet-5-5",
      options: { effort: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: \`seat-pcx-1\` (Proof Complexity · Claude Sonnet 5.5).
PROVE AND VERIFY THESE TWO UNIVERSAL PROOF-COMPLEXITY THEOREMS IN LEAN 4:

1. \`L-pcx-004\` -> \`lean/PnP/Lemmas/L_pcx_004.lean\`, theorem \`PnP.Lemmas.L_pcx_004.php_succ_unsat\`:
   \`theorem php_succ_unsat (n : Nat) : Unsatisfiable (PHP (n + 1) n)\`
   (Universal for ALL \`n : Nat\`! Hint: assume \`evalCNF a (PHP (n + 1) n) = true\`.
   - From the pigeon clauses, every \`p < n + 1\` has some \`h < n\` with \`a (phpVar n p h) = true\`.
   - From the hole clauses, for any \`p1 < p2 < n + 1\` and \`h < n\`, we cannot have both \`a (phpVar n p1 h) = true\` and \`a (phpVar n p2 h) = true\`.
   - Therefore, choosing a hole \`f p : Fin n\` for each pigeon \`p : Fin (n + 1)\` defines an INJECTIVE function \`Fin (n + 1) → Fin n\`!
   - Prove the finite Pigeonhole Principle by induction on \`n\`: there is no injective \`f : Fin (n + 1) → Fin n\` (given injective \`f : Fin (n+2) → Fin (n+1)\`, swap/shift \`f (last)\` to hole \`n\` to get an injective \`Fin (n+1) → Fin n\`!). Zero Mathlib needed, ~80 lines of super clean Lean 4!)

2. \`L-pcx-005\` -> \`lean/PnP/Lemmas/L_pcx_005.lean\`, theorem \`PnP.Lemmas.L_pcx_005.resolution_restrict_preserves_refutation\`:
   \`theorem resolution_restrict_preserves_refutation (φ : CNF) (v : Nat) (b : Bool) (h : ResDerivable φ []) : ResDerivable (restrictCNF v b φ) []\`
   (Ben-Sasson–Wigderson restriction lemma! Hint: prove the stronger induction invariant:
   for any clause \`c\` with \`ResDerivable φ c\`, EITHER \`restrictClause v b c = none\` (the clause is satisfied by \`v := b\`), OR there exists a subclause \`c' ⊆ restrictClause_val\` (every literal of \`c'\` is in \`c.filter (·.var != v)\`) such that \`ResDerivable (restrictCNF v b φ) c'\`!
   When \`c = []\`, \`restrictClause v b [] = some []\`, and any subclause of \`[]\` MUST be \`[]\`! BOOM!)

Send a \`report\` to \`seat-strat-1\` and set \`seat-pcx-1\` to \`idle\` when both clear the Lean 4 kernel!`,
  },
  {
    clientRequestId: "wave2-seat-redteam-1",
    title: "Wave 2 · seat-redteam-1 · Adversarial Circuit Synthesis Bounty (GPT-6.2 Sol)",
    role: "review",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-sol",
      options: { reasoningEffort: "xhigh" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: \`seat-redteam-1\` (Red Team · Adversarial Circuit Synthesis · GPT-6.2 Sol).
REAL ADVERSARIAL BOUNTY — NO STRAWMAN TARGETS!

1. **BOUNTY #1 — REFUTE \`L-meta-004\` (MAJ5 ≥ 11 gates in B2)!**
   \`L-meta-004\` conjectures that every \`B2Circuit 5\` computing \`maj5\` requires at least 11 gates.
   YOUR JOB: Actually **discover / synthesize a real ≤ 10-gate shared-wire \`B2Circuit 5\`** computing \`maj5\`!
   (Feel free to write a quick scratch Python/C/Node circuit-synthesis script or use Knuth/Kulikov's 10-gate B2 construction — verify it against all 32 inputs first!)
   Then encode that exact \`B2Circuit 5\` in \`lean/PnP/Lemmas/L_meta_004_refute.lean\` and prove in pure Lean 4 (zero \`native_decide\`, zero \`sorry\`! Checking 32 inputs by \`fin_cases\` / case-splitting on \`x 0, x 1, x 2, x 3, x 4\` with \`rfl\` or \`decide\` takes <2 seconds!):
   \`theorem counterexample : ∃ c : B2Circuit 5, c.size ≤ 10 ∧ c.Computes maj5\`
   Submit via:
   \`node hub/cli.mjs refute --lemma L-meta-004 --seat seat-redteam-1 --file lean/PnP/Lemmas/L_meta_004_refute.lean --theorem PnP.Lemmas.L_meta_004_refute.counterexample --summary "Synthesized an explicit 10-gate shared-wire B2 DAG computing MAJ5 (verified over all 32 inputs in Lean 4)"\`
   Send a \`challenge\` message to \`seat-meta-1\`!

2. **BOUNTY #2 — INVESTIGATE \`L-clb-007\` (\`cyclicAdj 5\` in full B2 basis)!**
   \`L-clb-007\` conjectures that \`cyclicAdj 5\` (true iff two cyclically adjacent bits on a 5-ring are both true) requires at least 7 gates in full \`B2\` (including XOR/XNOR).
   Use Python (or a fast C/Rust/SAT search in \`/tmp\` — don't pollute the repo!) to **seriously hunt** for a 6-gate \`B2Circuit 5\` computing \`cyclicAdj 5\`!
   - **IF YOU FIND A ≤ 6-GATE B2 CIRCUIT FOR \`cyclicAdj 5\`**: THAT IS HUGE!! Encode it in \`lean/PnP/Lemmas/L_clb_007_refute.lean\`, prove \`∃ c : B2Circuit 5, c.size ≤ 6 ∧ c.Computes (cyclicAdj 5)\`, and **REFUTE \`L-clb-007\`** via \`node hub/cli.mjs refute ...\`!
   - **IF YOUR SEARCH CANNOT BEAT 7 GATES** (e.g., exhaustive/SAT evidence that 6 gates is impossible in B2): post your exact experimental findings via \`node hub/cli.mjs msg --from seat-redteam-1 --to seat-clb-1 --lemma L-clb-007 --kind report --text "..."\` (and DO NOT falsely claim a Lean proof unless Lean proves it!).

Remember to clean up any temporary scratch scripts in the repo root (or keep scratch in /tmp) and set \`seat-redteam-1\` to \`idle\` when done.`,
  },
  {
    clientRequestId: "wave2-seat-alg-barrier",
    title: "Wave 2 · seat-alg-1 & seat-barrier-1 · MOD3 Synthesis + Formal Barrier Theorem (Gemini 4 Neon)",
    role: "implementation",
    target: {
      providerInstanceId: "antigravity",
      model: "gemini-4-neon",
      options: { thought_level: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEATS: \`seat-alg-1\` (Algorithm / Circuit Synthesis) AND \`seat-barrier-1\` (Barrier Desk).

1. As \`seat-alg-1\`: Prove \`L-alg-004\` -> \`lean/PnP/Lemmas/L_alg_004.lean\`, theorem \`PnP.Lemmas.L_alg_004.mod3_4_compact_b2\`:
   \`theorem mod3_4_compact_b2 : ∃ c : B2Circuit 4, c.size ≤ 7 ∧ c.Computes (mod3Eq0 4)\`
   (Think! On 4 bits, Hamming weight is ≡ 0 (mod 3) iff weight is 0 or 3!
   Can you compute \`weight ∈ {0, 3}\` on 4 bits in ≤ 7 B2 gates?!
   Check: let's see! Using 2-bit half-adder / mod-3 trick or Python search:
   - Weight 0 is \`¬x0 ∧ ¬x1 ∧ ¬x2 ∧ ¬x3\`
   - Weight 3 is \`exactly 1 bit is 0\`!
   - Wait: \`mod3Eq0 4\` is TRUE on 5 inputs: \`0000, 0111, 1011, 1101, 1110\`!
   - Let's check a super slick 6- or 7-gate B2 circuit!
     Use Python in \`/tmp\` to find the SMALLEST possible B2 circuit (maybe even 5 or 6 gates!) for \`mod3Eq0 4\`, then encode it in Lean 4 and prove \`c.size ≤ 7 ∧ c.Computes (mod3Eq0 4)\` over all 16 inputs — zero \`native_decide\`, zero \`sorry\`!)
   Send a \`report\` from \`seat-alg-1\` to \`seat-meta-1\` with the exact gate count you achieved!

2. As \`seat-barrier-1\`:
   - First, prove \`L-bar-003\` -> \`lean/PnP/Lemmas/L_bar_003.lean\`, theorem \`PnP.Lemmas.L_bar_003.relativization_barrier_meta\`:
     Define \`abbrev Oracle := List Bool → Bool\` (in namespace \`PnP.Lemmas.L_bar_003\`) and prove:
     \`theorem relativization_barrier_meta (P_O NP_O : Oracle → Prop) (hEq : ∃ A, P_O A = NP_O A) (hNeq : ∃ B, P_O B ≠ NP_O B) : (¬ ∀ O, P_O O ≠ NP_O O) ∧ (¬ ∀ O, P_O O = NP_O O)\`
     AND strengthen it with a clean formal proof that for a concrete oracle model (e.g. an abstract \`RelativizingProof\` structure stating a proof technique yields a uniform theorem \`∀ O, ...\`), no relativizing proof can resolve \`P_O empty = NP_O empty\`! Verify \`L-bar-003\` through the Lean 4 kernel!
   - Second, claim and audit \`L-bar-004\` (Algebrization · Aaronson–Wigderson 2009), send a \`ruling\` message to \`seat-strat-1\` explaining why arithmetization alone fails due to algebraic oracle extensions (\`P^A = NP^A\` with low-degree extension \`Ã\`), and rule \`L-bar-004\` dead into the Graveyard via \`node hub/cli.mjs rule-dead --lemma L-bar-004 --seat seat-barrier-1 --wall "Algebrization (Aaronson-Wigderson, 2009)" --reason "..."\`.

Set BOTH \`seat-alg-1\` and \`seat-barrier-1\` back to \`idle\` when done!`,
  },
];

console.log("Wave 2 lemmas registered. Dispatching 5 multi-model seats...");
for (const seat of WAVE_2) {
  const res = callT3("delegate_task", {
    clientRequestId: seat.clientRequestId,
    title: seat.title,
    role: seat.role,
    mode: "async",
    isolation: "shared",
    target: seat.target,
    task: seat.task,
  });
  console.log(`\n[${seat.clientRequestId}] status=${res.status}`);
  console.log(res.stdout || res.stderr);
}
