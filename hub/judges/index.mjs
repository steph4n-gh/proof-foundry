#!/usr/bin/env node
/**
 * hub/judges/index.mjs — Unified pluggable Judge router across all missions.
 */
import { checkLeanProof } from "./lean4.mjs";
import { checkCommandArtifact } from "./command.mjs";

export function runJudge(
  mission,
  {
    file,
    target,
    kind = "proof",
    statementFile = null,
    statementDef = null,
    expectedScore = null,
    allowTempForTests = false,
  }
) {
  const judgeConfig = mission?.judge || { type: "lean4" };
  if (judgeConfig.type === "lean4") {
    return checkLeanProof(file, target, {
      judgeConfig,
      kind,
      statementFile,
      statementDef,
      expectedScore,
      allowTempForTests,
    });
  }
  if (judgeConfig.type === "command") {
    return checkCommandArtifact(file, target, { judgeConfig, kind, allowTempForTests });
  }
  return {
    ok: false,
    judge: String(judgeConfig.type || "unknown"),
    reason: `Unsupported judge type: ${judgeConfig.type}`,
    file,
    theorem: target,
    axioms: [],
    duration_ms: 0,
    lean_version: "unknown",
    file_hash: null,
    core_hash: null,
    output: "",
  };
}
