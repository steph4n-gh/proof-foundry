#!/usr/bin/env node
/**
 * hub/launch_audit.mjs — Cross-model adversarial audit panel (GPT-6.2 Astra + Claude Opus 5.5)
 * independently verifying our Lean 4 checker, Core.lean definitions, every checked lemma's
 * semantic faithfulness, and the hub/dashboard architecture.
 */
import { spawnSync } from "node:child_process";

const NODE_BIN = process.env.T3_ACP_MCP_NODE;
const ENTRY = process.env.T3_ACP_MCP_ENTRYPOINT;

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

const AUDITORS = [
  {
    clientRequestId: "audit-astra-checker-math",
    title: "Audit Desk · Checker + Core.lean + Proof Faithfulness (GPT-6.2 Astra)",
    role: "review",
    target: {
      providerInstanceId: "codex_06d6149f-22b4-4f80-9623-d16e67f6876c",
      model: "gpt-6.2-astra",
      options: { reasoningEffort: "xhigh" },
    },
    task: `You are an independent, ruthless Adversarial Auditor (GPT-6.2 Astra) inspecting /Volumes/Storage/pnpenis2.
DO NOT EDIT ANY FILES. Read-only audit only. Do NOT spawn subagents.

Audit these 3 areas thoroughly and prove every finding with exact file paths, line numbers, and concrete failure modes:
1. **The Judge (\`hub/checker.mjs\`)**:
   - Can a malicious or buggy Lean file bypass the static ban or the \`#print axioms\` parser (e.g., nested block comments, printing fake \`depends on axioms: []\` via \`#eval IO.println\`, declaring a local theorem with the same name as a different statement, shadowing \`PnP.Core\` definitions, or passing a weak/vacuous theorem to \`verify\` that doesn't match the conjecture in \`hub/state.json\`)?
   - Check \`hub/cli.mjs\` \`verify\` and \`refute\` flows too.
2. **Core Definitions (\`lean/PnP/Core.lean\`)**:
   - Check EVERY definition (\`Monotone\`, \`DependsOn\`, \`Circuit\`, \`DAGCircuit\`, \`B2Op\`, \`B2Circuit\`, \`PHP\`, \`IsResolvent\`, \`ResDerivable\`, \`ResProof\`, \`PolyBounded\`, \`PolyTimeReducible\`, \`cyclicAdj\`, \`mod3Eq0\`, \`restrictCNF\`) for mathematical bugs, edge cases, or vacuous definitions!
   - Example things to scrutinize: \`PolyTimeReducible\` (does it actually enforce poly-time computability of \`f\`?), \`B2Circuit\` out-of-bounds wire semantics, \`PHP 0 0\` or \`PHP (n+1) n\`, \`IsResolvent\` duplicate-literal behavior, \`cyclicAdj\` for small \`n\`.
3. **Semantic Faithfulness of Checked Lemmas (\`lean/PnP/Lemmas/*.lean\` vs \`hub/state.json\`)**:
   - Inspect EVERY existing \`.lean\` file in \`lean/PnP/Lemmas/\` right now and compare its actual Lean theorem signature against the plain-English title in \`hub/state.json\`.
   - Flag ANY mismatch, weakening, hidden extra hypothesis, or vacuous proof!

Return a concise, prioritized report: CRITICAL vulnerabilities/math bugs first, then MEDIUM, then VERIFIED-CLEAN items.`,
  },
  {
    clientRequestId: "audit-opus-system-rigor",
    title: "Audit Desk · Hub Integrity + Dashboard + Mathematical Strategy (Claude Opus 5.5)",
    role: "review",
    target: {
      providerInstanceId: "claudeAgent",
      model: "claude-opus-5-5",
      options: { effort: "xhigh" },
    },
    task: `You are an independent Adversarial Systems & Math Auditor (Claude Opus 5.5) inspecting /Volumes/Storage/pnpenis2.
DO NOT EDIT ANY FILES. Read-only audit only. Do NOT spawn subagents.

Audit these 3 areas thoroughly with exact file/line citations:
1. **Hub & Checker Architecture (\`hub/cli.mjs\`, \`hub/checker.mjs\`, \`hub/state.json\`)**:
   - Check lock safety, atomicity, and whether \`verify\`/\`refute\` can silently mutate or weaken a conjecture's formal statement without detection.
   - Compare against \`pequalnp.com\`'s gold standard ("checked statement must match recorded statement, plus an independent non-author seat audits plain-English faithfulness"). What concrete mechanism should we add so our Judge is genuinely airtight?
2. **Live Dashboard & SSE Server (\`web/server.mjs\`, \`web/public/app.js\`, \`web/public/style.css\`)**:
   - Check for real bugs: XSS, SSE reconnect/memory leaks, Proof Map node overlap as lemma count grows past 25-30, Rel Graph layout bugs, missing error handling, or misleading UI metrics.
3. **Mathematical Rigor & Next-Wave Critique**:
   - Read \`lean/PnP/Core.lean\` and \`hub/state.json\`. Give a blunt, senior complexity-theorist critique of what is strong vs. weak in our formalization right now (e.g., \`PolyTimeReducible\` / \`PolyDecider\`, \`B2Circuit\`, \`ResProof\`), and name the top 3 upgrades that would make this codebase genuinely elite.

Return a sharp, concrete, prioritized report with zero fluff.`,
  },
];

for (const a of AUDITORS) {
  const res = callT3("delegate_task", {
    clientRequestId: a.clientRequestId,
    title: a.title,
    role: a.role,
    mode: "async",
    isolation: "shared",
    target: a.target,
    task: a.task,
  });
  console.log(`\n[${a.clientRequestId}] status=${res.status}`);
  console.log(res.stdout || res.stderr);
}
