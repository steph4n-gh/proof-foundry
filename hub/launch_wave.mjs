#!/usr/bin/env node
/**
 * hub/launch_wave.mjs — Opens the live dashboard in T3 Code Preview and dispatches
 * Wave 1 across our multi-model fleet (Claude Sonnet 5.5, Claude Opus 5.5, GPT-6.2 Sol, Gemini 4 Neon)
 * using T3 Code's ACP MCP bridge.
 */
import { spawnSync } from "node:child_process";

const NODE_BIN = process.env.T3_ACP_MCP_NODE;
const ENTRY = process.env.T3_ACP_MCP_ENTRYPOINT;

if (!NODE_BIN) {
  console.error("T3_ACP_MCP_NODE is not set in environment.");
  process.exit(1);
}

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

const COMMON_RULES = `
You are a live seat in the local T3 Code P = NP ? Multi-Model Fleet at /Volumes/Storage/pnpenis2.
Read /Volumes/Storage/pnpenis2/FLEET_PLAYBOOK.md and /Volumes/Storage/pnpenis2/lean/PnP/Core.lean first.
STRICT RULES:
1. Work ONLY in /Volumes/Storage/pnpenis2. NEVER edit lean/PnP/Core.lean or another seat's lemma files.
2. Put every proof in its own dedicated file under lean/PnP/Lemmas/ with \`import PnP.Core\` ONLY (self-contained so parallel seats never collide).
3. Use Lean 4.36.0 pure stdlib (NO Mathlib). Zero \`sorry\`, zero \`admit\`, zero custom \`axiom\`.
4. Always claim each lemma BEFORE starting work (\`node hub/cli.mjs claim ...\`), post short live whispers (\`node hub/cli.mjs whisper ...\`) so the live dashboard lights up, and send at least 1-2 crisp inter-seat messages (\`node hub/cli.mjs msg ...\`).
5. Run \`node hub/cli.mjs verify ...\` (or \`refute ...\` / \`rule-dead ...\`) and iterate until Lean 4 returns \`"ok": true\`.
6. When all assigned targets are verified, set your seat back to idle (\`node hub/cli.mjs seat-state --seat <id> --status idle --whisper "..."\`) and reply with a concise summary of verified theorems, durations, and axioms.
7. Do NOT spawn subagents. Do the work yourself cleanly and quickly.
`.trim();

const WAVE_1 = [
  {
    clientRequestId: "wave1-seat-lib-1",
    title: "seat-lib-1 · Library Foundations (Claude Sonnet 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-sonnet-5-5",
      options: { effort: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: seat-lib-1 (Library Builder · Claude Sonnet 5.5)
ASSIGNED LEMMAS (prove and verify ALL THREE in Lean 4):
1. L-lib-001 -> file \`lean/PnP/Lemmas/L_lib_001.lean\`, theorem \`PnP.Lemmas.L_lib_001.monotone_circuit_is_monotone\`:
   \`theorem monotone_circuit_is_monotone {n : Nat} (c : Circuit n) (hm : c.isMonotone = true) : Monotone c.eval\`
2. L-lib-002 -> file \`lean/PnP/Lemmas/L_lib_002.lean\`, theorem \`PnP.Lemmas.L_lib_002.unused_input_invariant\`:
   \`theorem unused_input_invariant {n : Nat} (c : Circuit n) (i : Fin n) (hu : c.usesInput i = false) (x : BoolVec n) : c.eval (flipBit x i) = c.eval x\`
3. L-lib-003 -> file \`lean/PnP/Lemmas/L_lib_003.lean\`, theorem \`PnP.Lemmas.L_lib_003.polyBounded_add_mul\`:
   \`theorem polyBounded_add_mul {f g : Nat → Nat} (hf : PolyBounded f) (hg : PolyBounded g) : PolyBounded (fun n => f n + g n) ∧ PolyBounded (fun n => f n * g n)\`

After verifying L-lib-001 and L-lib-002, send a \`handoff\` message to \`seat-clb-1\` via \`node hub/cli.mjs msg --from seat-lib-1 --to seat-clb-1 --kind handoff --lemma L-lib-001 --text "..."\`.`,
  },
  {
    clientRequestId: "wave1-seat-clb-1",
    title: "seat-clb-1 · Circuit Lower Bounds (GPT-6.2 Sol)",
    role: "implementation",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-sol",
      options: { reasoningEffort: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: seat-clb-1 (Circuit Lower Bounds · GPT-6.2 Sol)
ASSIGNED LEMMAS (prove and verify ALL THREE in Lean 4 — keep each file self-contained importing only \`PnP.Core\`):
1. L-clb-001 -> file \`lean/PnP/Lemmas/L_clb_001.lean\`, theorem \`PnP.Lemmas.L_clb_001.xor2_no_monotone_circuit\`:
   \`theorem xor2_no_monotone_circuit (c : Circuit 2) (hm : c.isMonotone = true) : ¬ c.Computes xor2\`
2. L-clb-002 -> file \`lean/PnP/Lemmas/L_clb_002.lean\`, theorem \`PnP.Lemmas.L_clb_002.depends_implies_usesInput\`:
   \`theorem depends_implies_usesInput {n : Nat} (c : Circuit n) (f : BoolFn n) (i : Fin n) (hc : c.Computes f) (hd : DependsOn f i) : c.usesInput i = true\`
3. L-clb-003 -> file \`lean/PnP/Lemmas/L_clb_003.lean\`, theorem \`PnP.Lemmas.L_clb_003.parity_binary_gate_lower_bound\`:
   \`theorem parity_binary_gate_lower_bound {n : Nat} (c : Circuit n) (hc : c.Computes (parityFn n)) : n ≤ c.binaryGateCount + 1\`
   (Hint: prove that the count of distinct Fin n inputs with \`c.usesInput i = true\` is ≤ \`c.binaryGateCount + 1\` by structural induction on \`c\`, and prove \`parityFn n\` depends on every \`i : Fin n\`!)

Send a \`report\` message to \`seat-strat-1\` and a \`handoff\` message to \`seat-meta-1\` once checked!`,
  },
  {
    clientRequestId: "wave1-seat-pcx-1",
    title: "seat-pcx-1 · Proof Complexity (Claude Opus 5.5)",
    role: "implementation",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-opus-5-5",
      options: { effort: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEAT: seat-pcx-1 (Proof Complexity · Claude Opus 5.5)
ASSIGNED LEMMAS (prove and verify ALL THREE in Lean 4 — self-contained importing only \`PnP.Core\`):
1. L-pcx-001 -> file \`lean/PnP/Lemmas/L_pcx_001.lean\`, theorem \`PnP.Lemmas.L_pcx_001.resolution_sound\`:
   \`theorem resolution_sound (φ : CNF) (h : ResDerivable φ []) : Unsatisfiable φ\`
2. L-pcx-002 -> file \`lean/PnP/Lemmas/L_pcx_002.lean\`, theorem \`PnP.Lemmas.L_pcx_002.php_3_2_unsat\`:
   \`theorem php_3_2_unsat : Unsatisfiable (PHP 3 2)\`
3. L-pcx-003 -> file \`lean/PnP/Lemmas/L_pcx_003.lean\`, theorem \`PnP.Lemmas.L_pcx_003.resolution_min_size_ge_three\`:
   \`theorem resolution_min_size_ge_three (φ : CNF) (p : ResProof φ []) (hlen : ∀ c ∈ φ, 2 ≤ c.length) : 3 ≤ p.size\`
   (Note: if you can prove even \`5 ≤ p.size\`, feel free to prove both and expose \`resolution_min_size_ge_three\`!)

Send a \`report\` message to \`seat-strat-1\` and a \`challenge\`/\`report\` to \`seat-alg-1\` once PHP(3,2) UNSAT and Resolution soundness clear the kernel!`,
  },
  {
    clientRequestId: "wave1-seat-alg-meta",
    title: "seat-alg-1 & seat-meta-1 · P=NP Search + Meta-Complexity (Gemini 4 Neon)",
    role: "implementation",
    target: {
      providerInstanceId: "antigravity",
      model: "gemini-4-neon",
      options: { thought_level: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEATS: \`seat-alg-1\` (P = NP Search) AND \`seat-meta-1\` (Meta-complexity) — both Gemini 4 Neon.
ASSIGNED LEMMAS (prove and verify ALL THREE in Lean 4 — self-contained importing only \`PnP.Core\`):
1. As \`seat-alg-1\`: L-alg-001 -> file \`lean/PnP/Lemmas/L_alg_001.lean\`, theorem \`PnP.Lemmas.L_alg_001.horn_no_positive_unit_sat\`:
   \`theorem horn_no_positive_unit_sat (φ : CNF) (hHorn : IsHornCNF φ = true) (hNeg : ∀ c ∈ φ, c.any (fun l => !l.pos) = true) : Satisfiable φ\`
   (Aiming at P = NP: witness assignment \`fun _ => false\`!)
2. As \`seat-meta-1\`: L-meta-001 -> file \`lean/PnP/Lemmas/L_meta_001.lean\`, theorem \`PnP.Lemmas.L_meta_001.maj3_circuit_bounds\`:
   \`theorem maj3_circuit_bounds : (∃ c : Circuit 3, c.isMonotone = true ∧ c.gateCount ≤ 4 ∧ c.Computes maj3) ∧ (∀ c : Circuit 3, c.Computes maj3 → 2 ≤ c.binaryGateCount)\`
3. As \`seat-meta-1\`: L-meta-002 -> file \`lean/PnP/Lemmas/L_meta_002.lean\`, theorem \`PnP.Lemmas.L_meta_002.maj3_no_one_gate_dag\`:
   \`theorem maj3_no_one_gate_dag (c : DAGCircuit 3) (hs : c.size ≤ 1) : ¬ c.Computes maj3\`

Send a \`handoff\` from \`seat-alg-1\` to \`seat-redteam-1\` daring them to attack L-alg-002 and L-alg-003, and a \`report\` from \`seat-meta-1\` to \`seat-clb-1\` when MAJ3 bounds clear the kernel! Remember to set BOTH \`seat-alg-1\` and \`seat-meta-1\` to \`idle\` when done.`,
  },
  {
    clientRequestId: "wave1-seat-redteam-barrier",
    title: "seat-redteam-1 & seat-barrier-1 · Red Team + Barrier Desk (GPT-6.2 Sol)",
    role: "review",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-sol",
      options: { reasoningEffort: "high" },
    },
    task: `${COMMON_RULES}

YOUR SEATS: \`seat-redteam-1\` (Red Team) AND \`seat-barrier-1\` (Barrier Desk).
YOUR MISSION — HUNT COUNTEREXAMPLES & ENFORCE COMPLEXITY BARRIERS!

PART A — RED TEAM (\`seat-redteam-1\`): Formally REFUTE BOTH false conjectures with Lean 4 kernel-verified counterexamples!
1. Refute \`L-alg-002\`:
   Claim was: "Every 3-CNF where every clause has 2..3 literals and each variable appears at most 3 times is satisfiable."
   Construct an explicit counterexample CNF \`cex_cnf : CNF\` (e.g., 4 variables 0,1,2,3 with 5 binary clauses: \`(0 ∨ 1), (¬0 ∨ 1), (¬1 ∨ 2), (3 ∨ ¬2), (¬3 ∨ ¬2)\` — check: every clause has length 2, variable occurrences are v0=2, v1=3, v2=3, v3=2, ALL ≤ 3, yet it is UNSATISFIABLE!).
   Write \`lean/PnP/Lemmas/L_alg_002_refute.lean\` proving:
   \`theorem counterexample : (∀ c ∈ cex_cnf, 2 ≤ c.length ∧ c.length ≤ 3) ∧ (∀ v, varOcc cex_cnf v ≤ 3) ∧ Unsatisfiable cex_cnf\`
   Verify & record refutation using:
   \`node hub/cli.mjs refute --lemma L-alg-002 --seat seat-redteam-1 --file lean/PnP/Lemmas/L_alg_002_refute.lean --theorem PnP.Lemmas.L_alg_002_refute.counterexample --summary "..."\`
   Send a crisp \`challenge\` message from \`seat-redteam-1\` to \`seat-alg-1\`!

2. Refute \`L-alg-003\`:
   Claim was: "Every symmetric Boolean function on 3 variables is computed by a monotone circuit."
   Counterexample: \`parityFn 3\` IS symmetric under all permutations of \`Fin 3\`, yet is NOT monotone (e.g. (true,false,false) ≤ (true,true,false) flips parity from true to false), so NO monotone \`Circuit 3\` computes it!
   Write \`lean/PnP/Lemmas/L_alg_003_refute.lean\` proving \`parityFn 3\` is permutation-invariant on \`Fin 3\` AND \`∀ c : Circuit 3, c.isMonotone = true → ¬ c.Computes (parityFn 3)\`, exposed as \`PnP.Lemmas.L_alg_003_refute.counterexample\`.
   Submit with \`node hub/cli.mjs refute --lemma L-alg-003 --seat seat-redteam-1 --file lean/PnP/Lemmas/L_alg_003_refute.lean --theorem PnP.Lemmas.L_alg_003_refute.counterexample --summary "..."\`!

PART B — BARRIER DESK (\`seat-barrier-1\`):
1. Audit \`L-bar-001\` (pure step-counting black-box diagonalization): claim it, analyze why it relativizes (Baker-Gill-Solovay 1975: any proof invariant under arbitrary oracle access fails because ∃ A, P^A = NP^A and ∃ B, P^B ≠ NP^B), send a \`ruling\` message to \`seat-strat-1\`, and rule it dead with:
   \`node hub/cli.mjs rule-dead --lemma L-bar-001 --seat seat-barrier-1 --wall "Relativization (Baker-Gill-Solovay, 1975)" --reason "..."\`
2. Audit \`L-bar-002\` (dense constructive truth-table property against P/poly): claim it, analyze why it hits Razborov-Rudich (1997) Natural Proofs (largeness + poly-time constructivity contradicts sub-exponentially hard PRFs / one-way functions), send a \`ruling\` message to \`seat-clb-1\`, and rule it dead with:
   \`node hub/cli.mjs rule-dead --lemma L-bar-002 --seat seat-barrier-1 --wall "Natural Proofs (Razborov-Rudich, 1997)" --reason "..."\`

Remember to set BOTH \`seat-redteam-1\` and \`seat-barrier-1\` to \`idle\` when done.`,
  },
];

console.log("1. Opening T3 Code live preview tab on port 4321...");
const prev = callT3("preview_open", {
  open: true,
  target: { kind: "environment-port", port: 4321 },
});
console.log("preview_open:", prev.status, prev.stdout || prev.stderr);

console.log("\n2. Dispatching Wave 1 across 5 multi-model seats...");
const results = [];
for (const seat of WAVE_1) {
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
  results.push({ id: seat.clientRequestId, status: res.status, out: res.stdout || res.stderr });
}
