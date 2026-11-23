#!/usr/bin/env node
/**
 * hub/test_judge.mjs — Adversarial security & frozen-statement regression test for Lean 4 Judge v2.
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { checkLeanProof } from "./judges/lean4.mjs";
import { loadMission } from "./missions.mjs";

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "pnp-attack-"));
let failed = 0;

function assert(cond, label, detail) {
  if (cond) {
    console.log(`PASS  ${label}`);
  } else {
    console.error(`FAIL  ${label} -> ${detail}`);
    failed++;
  }
}

try {
  // Attack A: #eval spoofing + #exit (no theorem exists)
  const fileA = path.join(tmp, "AttackA.lean");
  fs.writeFileSync(fileA, `#eval IO.println "'X.t' depends on axioms: [propext]"\n#exit\n`);
  const resA = checkLeanProof(fileA, "X.t", { allowTempForTests: true });
  assert(!resA.ok, "Attack A (#eval spoof + #exit) rejected", JSON.stringify(resA));

  // Attack B: inline `axiom cheat : False`
  const fileB = path.join(tmp, "AttackB.lean");
  fs.writeFileSync(fileB, `namespace X\ndef a := 1 axiom cheat : False\ntheorem t : 1 = 2 := cheat.elim\nend X\n`);
  const resB = checkLeanProof(fileB, "X.t", { allowTempForTests: true });
  assert(!resB.ok, "Attack B (inline axiom cheat : False) rejected", JSON.stringify(resB));

  // Attack C: foreign theorem Nat.add_comm rejected by module binding
  const fileC = path.resolve("lean/PnP/Lemmas/.test_attack_c.lean");
  fs.writeFileSync(fileC, `import PnP.Core\nnamespace Fake\nend Fake\n`);
  try {
    const resC = checkLeanProof(fileC, "Nat.add_comm");
    assert(
      !resC.ok && resC.reason.includes("NOT declared in submitted file"),
      "Attack C (foreign theorem Nat.add_comm) rejected by module binding",
      JSON.stringify(resC)
    );
  } finally {
    try { fs.unlinkSync(fileC); } catch {}
  }

  // Attack D: string-escaped comment delimiter hiding `sorry`
  const fileD = path.join(tmp, "AttackD.lean");
  fs.writeFileSync(fileD, `def s := "/-"\ntheorem fake : False := by sorry\ndef e := "-/"\n`);
  const resD = checkLeanProof(fileD, "fake", { allowTempForTests: true });
  assert(!resD.ok, "Attack D (string-escaped comment hiding sorry) rejected", JSON.stringify(resD));

  // Attack E: canonical path gate outside allowed_dirs
  const fileE = path.join(tmp, "AttackE.lean");
  fs.writeFileSync(fileE, `import PnP.Core\n`);
  const resE = checkLeanProof(fileE, "Nat.add_comm");
  assert(
    !resE.ok && resE.reason.includes("path gate"),
    "Attack E (outside allowed_dirs) rejected by canonical path gate",
    JSON.stringify(resE)
  );

  // Attack F (Opus 5.5 finding): char literal '"' desyncing string lexer to hide `sorry`
  const fileF = path.join(tmp, "AttackF.lean");
  fs.writeFileSync(
    fileF,
    `def q : Char := '"'\ntheorem fake : False := by sorry\ndef r : Char := '"'\n`
  );
  const resF = checkLeanProof(fileF, "fake", { allowTempForTests: true });
  assert(
    !resF.ok && resF.reason.includes("sorry"),
    "Attack F (char literal '\"' desync hiding sorry) rejected by Lean-aware lexer",
    JSON.stringify(resF)
  );

  // Attack G: meta-escape via `by_elab` / `skipKernelTC`
  const fileG = path.join(tmp, "AttackG.lean");
  fs.writeFileSync(fileG, `theorem fake : True := by_elab pure (Lean.mkConst \`True.intro)\n`);
  const resG = checkLeanProof(fileG, "fake", { allowTempForTests: true });
  assert(
    !resG.ok && resG.reason.includes("by_elab"),
    "Attack G (by_elab meta escape) rejected by static gate",
    JSON.stringify(resG)
  );

  // Legitimate proof check: L_lib_000.lean must PASS with full untruncated signature
  const resOk = checkLeanProof("lean/PnP/Lemmas/L_lib_000.lean", "PnP.Lemmas.L_lib_000.flipBit_involutive");
  assert(
    resOk.ok && resOk.signature.includes("flipBit (PnP.flipBit x i) i = x"),
    "Legitimate theorem L_lib_000 passes with FULL untruncated signature",
    JSON.stringify(resOk)
  );

  // Frozen-statement kernel type-matching tests on erdos-combinatorics
  const erdos = loadMission("erdos-combinatorics");
  const testStmtPath = path.resolve("missions/erdos-combinatorics/lean/Erdos/Statements/_TestFrozen.lean");
  const testClaimPass = path.resolve("missions/erdos-combinatorics/lean/Erdos/Claims/_TestFrozenPass.lean");
  const testClaimRefute = path.resolve("missions/erdos-combinatorics/lean/Erdos/Claims/_TestFrozenRefute.lean");
  const testClaimBait = path.resolve("missions/erdos-combinatorics/lean/Erdos/Claims/_TestFrozenBait.lean");
  const testClaimShadow = path.resolve("missions/erdos-combinatorics/lean/Erdos/Claims/_TestFrozenShadow.lean");

  fs.writeFileSync(
    testStmtPath,
    `import Erdos.Core\nnamespace Erdos.Statements._TestFrozen\ndef Claim : Prop := 2 + 2 = 4\ndef FalseClaim : Prop := 2 + 2 = 5\nend Erdos.Statements._TestFrozen\n`
  );
  fs.writeFileSync(
    testClaimPass,
    `import Erdos.Core\nimport Erdos.Statements._TestFrozen\nnamespace Erdos.Claims._TestFrozenPass\ntheorem ok : Erdos.Statements._TestFrozen.Claim := rfl\nend Erdos.Claims._TestFrozenPass\n`
  );
  fs.writeFileSync(
    testClaimRefute,
    `import Erdos.Core\nimport Erdos.Statements._TestFrozen\nnamespace Erdos.Claims._TestFrozenRefute\ntheorem ref : ¬ Erdos.Statements._TestFrozen.FalseClaim := by unfold Erdos.Statements._TestFrozen.FalseClaim; decide\nend Erdos.Claims._TestFrozenRefute\n`
  );
  fs.writeFileSync(
    testClaimBait,
    `import Erdos.Core\nnamespace Erdos.Claims._TestFrozenBait\ntheorem bait : True := trivial\nend Erdos.Claims._TestFrozenBait\n`
  );
  fs.writeFileSync(
    testClaimShadow,
    `import Erdos.Core\nnamespace Erdos.Statements._TestFrozen\ndef Claim : Prop := True\nend Erdos.Statements._TestFrozen\nnamespace Erdos.Claims._TestFrozenShadow\ntheorem shadowed : Erdos.Statements._TestFrozen.Claim := trivial\nend Erdos.Claims._TestFrozenShadow\n`
  );

  try {
    const resFrozenPass = checkLeanProof(testClaimPass, "Erdos.Claims._TestFrozenPass.ok", {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: "missions/erdos-combinatorics/lean/Erdos/Statements/_TestFrozen.lean",
      statementDef: "Erdos.Statements._TestFrozen.Claim",
    });
    assert(
      resFrozenPass.ok && resFrozenPass.statement_frozen === true,
      "Frozen statement PASS: exact match against Erdos.Statements._TestFrozen.Claim",
      JSON.stringify(resFrozenPass)
    );

    const resFrozenRefute = checkLeanProof(testClaimRefute, "Erdos.Claims._TestFrozenRefute.ref", {
      judgeConfig: erdos.judge,
      kind: "refutation",
      statementFile: "missions/erdos-combinatorics/lean/Erdos/Statements/_TestFrozen.lean",
      statementDef: "Erdos.Statements._TestFrozen.FalseClaim",
    });
    assert(
      resFrozenRefute.ok && resFrozenRefute.statement_frozen === true,
      "Frozen statement REFUTATION PASS: exact match against ¬ Erdos.Statements._TestFrozen.FalseClaim",
      JSON.stringify(resFrozenRefute)
    );

    const resFrozenBait = checkLeanProof(testClaimBait, "Erdos.Claims._TestFrozenBait.bait", {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: "missions/erdos-combinatorics/lean/Erdos/Statements/_TestFrozen.lean",
      statementDef: "Erdos.Statements._TestFrozen.Claim",
    });
    assert(
      !resFrozenBait.ok && resFrozenBait.reason.includes("frozen-statement gate"),
      "Frozen statement REJECT: bait-and-switch theorem (True) blocked by kernel",
      JSON.stringify(resFrozenBait)
    );

    const resFrozenShadow = checkLeanProof(testClaimShadow, "Erdos.Claims._TestFrozenShadow.shadowed", {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: "missions/erdos-combinatorics/lean/Erdos/Statements/_TestFrozen.lean",
      statementDef: "Erdos.Statements._TestFrozen.Claim",
    });
    assert(
      !resFrozenShadow.ok,
      "Frozen statement REJECT: shadowed `Claim := True` blocked by dual-import collision",
      JSON.stringify(resFrozenShadow)
    );
  } finally {
    for (const f of [testStmtPath, testClaimPass, testClaimRefute, testClaimBait, testClaimShadow]) {
      try { fs.unlinkSync(f); } catch {}
    }
  }
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}

if (failed > 0) {
  console.error(`\n${failed} test(s) failed!`);
  process.exit(1);
}
console.log("\nALL 12 ADVERSARIAL, REGRESSION & FROZEN-STATEMENT TESTS PASSED!");
