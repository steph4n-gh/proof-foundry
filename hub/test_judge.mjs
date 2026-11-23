#!/usr/bin/env node
/**
 * hub/test_judge.mjs — Adversarial security & frozen-statement regression suite for Lean 4 & Command Judges.
 * Every negative test asserts BOTH `!res.ok` AND the exact expected rejection reason!
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { auditLeanSyntax, checkLeanProof, compiledModulePolicy } from "./judges/lean4.mjs";
import { checkCommandArtifact } from "./judges/command.mjs";
import { computeRecordTargets, deriveMissionState, listMissionSlugs, loadMission } from "./missions.mjs";

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "pf-judge-test-"));
const salt = `${process.pid}_${Date.now()}`;
let failed = 0;
let passed = 0;

function assert(cond, label, detail) {
  if (cond) {
    passed++;
    console.log(`PASS  ${label}`);
  } else {
    console.error(`FAIL  ${label} -> ${detail}`);
    failed++;
  }
}

try {
  // Attack A: #eval spoofing + #exit
  const fileA = path.join(tmp, "AttackA.lean");
  fs.writeFileSync(fileA, `#eval IO.println "'X.t' depends on axioms: [propext]"\n#exit\n`);
  const resA = checkLeanProof(fileA, "X.t", { allowTempForTests: true });
  assert(!resA.ok && resA.reason.includes("#eval"), "Attack A (#eval spoof + #exit) rejected by static gate", JSON.stringify(resA));

  // Attack B: inline `axiom cheat : False`
  const fileB = path.join(tmp, "AttackB.lean");
  fs.writeFileSync(fileB, `namespace X\ndef a := 1 axiom cheat : False\ntheorem t : 1 = 2 := cheat.elim\nend X\n`);
  const resB = checkLeanProof(fileB, "X.t", { allowTempForTests: true });
  assert(!resB.ok && resB.reason.includes("axiom"), "Attack B (inline axiom cheat : False) rejected", JSON.stringify(resB));

  // Attack C: foreign theorem Nat.add_comm rejected by module binding
  const fileC = path.resolve(`lean/PnP/Lemmas/.test_attack_c_${salt}.lean`);
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
  assert(!resD.ok && resD.reason.includes("sorry"), "Attack D (string-escaped comment hiding sorry) rejected", JSON.stringify(resD));

  // Attack E: canonical path gate outside allowed_dirs
  const fileE = path.join(tmp, "AttackE.lean");
  fs.writeFileSync(fileE, `import PnP.Core\n`);
  const resE = checkLeanProof(fileE, "Nat.add_comm");
  assert(!resE.ok && resE.reason.includes("path gate"), "Attack E (outside allowed_dirs) rejected by canonical path gate", JSON.stringify(resE));

  // Attack F: char literal '"' desync hiding `sorry`
  const fileF = path.join(tmp, "AttackF.lean");
  fs.writeFileSync(fileF, `def q : Char := '"'\ntheorem fake : False := by sorry\ndef r : Char := '"'\n`);
  const resF = checkLeanProof(fileF, "fake", { allowTempForTests: true });
  assert(!resF.ok && resF.reason.includes("sorry"), "Attack F (char literal '\"' desync hiding sorry) rejected", JSON.stringify(resF));

  // Attack G: meta-escape via `by_elab`
  const fileG = path.join(tmp, "AttackG.lean");
  fs.writeFileSync(fileG, `theorem fake : True := by_elab pure (Lean.mkConst \`True.intro)\n`);
  const resG = checkLeanProof(fileG, "fake", { allowTempForTests: true });
  assert(!resG.ok && resG.reason.includes("by_elab"), "Attack G (by_elab meta escape) rejected", JSON.stringify(resG));

  // Attack H (Opus P0 #3): guillemet «q"» desync hiding `#eval`
  const fileH = path.join(tmp, "AttackH.lean");
  fs.writeFileSync(fileH, `def «q"» : Nat := 0\n#eval IO.println "HIDDEN_EVAL_RAN"\ndef «r"» : Nat := 0\ntheorem ok : True := trivial\n`);
  const resH = checkLeanProof(fileH, "ok", { allowTempForTests: true });
  assert(!resH.ok && resH.reason.includes("guillemet"), "Attack H (Opus P0 #3: guillemet «q\"» desync) rejected", JSON.stringify(resH));

  // Attack I (Opus P0 #3): raw string r#"..."# desync
  const fileI = path.join(tmp, "AttackI.lean");
  fs.writeFileSync(fileI, `def s := r#"hello"#\ntheorem ok : True := trivial\n`);
  const resI = checkLeanProof(fileI, "ok", { allowTempForTests: true });
  assert(!resI.ok && resI.reason.includes("raw string"), "Attack I (raw string r#\"…\"#) rejected", JSON.stringify(resI));

  // Attack J (Opus P0 #3): `import Lean` blocked by import allowlist
  const fileJ = path.join(tmp, "AttackJ.lean");
  fs.writeFileSync(fileJ, `import Lean\ntheorem ok : True := trivial\n`);
  const resJ = checkLeanProof(fileJ, "ok", { allowTempForTests: true });
  assert(!resJ.ok && resJ.reason.includes("Disallowed import"), "Attack J (`import Lean`) rejected by import allowlist", JSON.stringify(resJ));

  // Attack K (Opus P0 #3): `set_option debug.skipKernelTC true` blocked by set_option allowlist
  const fileK = path.join(tmp, "AttackK.lean");
  fs.writeFileSync(fileK, `set_option debug.skipKernelTC true\ntheorem ok : True := trivial\n`);
  const resK = checkLeanProof(fileK, "ok", { allowTempForTests: true });
  assert(!resK.ok && resK.reason.includes("Disallowed set_option"), "Attack K (`set_option debug.skipKernelTC`) rejected", JSON.stringify(resK));

  // Attack L (Opus P0 #3): `run_meta` blocked
  const fileL = path.join(tmp, "AttackL.lean");
  fs.writeFileSync(fileL, `run_meta pure ()\ntheorem ok : True := trivial\n`);
  const resL = checkLeanProof(fileL, "ok", { allowTempForTests: true });
  assert(!resL.ok && resL.reason.includes("run_meta"), "Attack L (`run_meta`) rejected", JSON.stringify(resL));

  // Attack M (Opus P0 #2): symlink inside allowed dir rejected directly
  const symlinkPath = path.resolve(`lean/PnP/Lemmas/.test_symlink_${salt}.lean`);
  fs.symlinkSync(path.resolve("lean/PnP/Lemmas/L_lib_000.lean"), symlinkPath);
  try {
    const resM = checkLeanProof(symlinkPath, "PnP.Lemmas.L_lib_000.flipBit_involutive");
    assert(!resM.ok && resM.reason.includes("symlink"), "Attack M (symlink inside allowed_dirs) rejected", JSON.stringify(resM));
  } finally {
    try { fs.unlinkSync(symlinkPath); } catch {}
  }

  // Attack N (Opus P0 #5): Command Judge child-process isolation blocks `--result` forgery
  const sci = loadMission("verified-science-kernels");
  const fakeArtifact = path.join(tmp, "ForgeResult.mjs");
  fs.writeFileSync(
    fakeArtifact,
    `import fs from "node:fs";
const idx = process.argv.indexOf("--result");
if (idx !== -1 && process.argv[idx + 1]) {
  fs.writeFileSync(process.argv[idx + 1], JSON.stringify({ ok: true, reason: "FORGED" }));
  process.exit(0);
}
export function compensatedSum() { return 0; }
`
  );
  const resN = checkCommandArtifact(fakeArtifact, "kahan_compensated_sum", { judgeConfig: sci.judge, allowTempForTests: true });
  assert(!resN.ok && resN.reason.includes("Precision failure"), "Attack N (Opus P0 #5: Command Judge --result forgery) defeated by child isolation", JSON.stringify(resN));

  // Positive control for Command Judge: legitimate S_num_001.mjs passes isolated child harness!
  const resSciOk = checkCommandArtifact("missions/verified-science-kernels/artifacts/S_num_001.mjs", "kahan_compensated_sum", { judgeConfig: sci.judge });
  assert(resSciOk.ok && resSciOk.lean_version.includes("isolated child"), "Positive control: S_num_001 passes isolated child Command Judge", JSON.stringify(resSciOk));

  // Positive control for Lean 4 Judge: L_lib_000.lean passes with full signature
  const resOk = checkLeanProof("lean/PnP/Lemmas/L_lib_000.lean", "PnP.Lemmas.L_lib_000.flipBit_involutive");
  assert(resOk.ok && resOk.signature.includes("flipBit (PnP.flipBit x i) i = x"), "Positive control: L_lib_000 passes with FULL untruncated signature", JSON.stringify(resOk));

  // Frozen-statement kernel type-matching tests (unique salted filenames)
  const erdos = loadMission("erdos-combinatorics");
  const modStem = `_TestFrozen_${salt}`;
  const testStmtPath = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Statements/${modStem}.lean`);
  const testClaimPass = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${modStem}_Pass.lean`);
  const testClaimRefute = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${modStem}_Refute.lean`);
  const testClaimBait = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${modStem}_Bait.lean`);
  const testClaimShadow = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${modStem}_Shadow.lean`);

  fs.writeFileSync(
    testStmtPath,
    `import Erdos.Core\nnamespace Erdos.Statements.${modStem}\ndef Claim : Prop := 2 + 2 = 4\ndef FalseClaim : Prop := 2 + 2 = 5\nend Erdos.Statements.${modStem}\n`
  );
  fs.writeFileSync(
    testClaimPass,
    `import Erdos.Core\nimport Erdos.Statements.${modStem}\nnamespace Erdos.Claims.${modStem}_Pass\ntheorem ok : Erdos.Statements.${modStem}.Claim := rfl\nend Erdos.Claims.${modStem}_Pass\n`
  );
  fs.writeFileSync(
    testClaimRefute,
    `import Erdos.Core\nimport Erdos.Statements.${modStem}\nnamespace Erdos.Claims.${modStem}_Refute\ntheorem ref : ¬ Erdos.Statements.${modStem}.FalseClaim := by unfold Erdos.Statements.${modStem}.FalseClaim; decide\nend Erdos.Claims.${modStem}_Refute\n`
  );
  fs.writeFileSync(
    testClaimBait,
    `import Erdos.Core\nnamespace Erdos.Claims.${modStem}_Bait\ntheorem bait : True := trivial\nend Erdos.Claims.${modStem}_Bait\n`
  );
  fs.writeFileSync(
    testClaimShadow,
    `import Erdos.Core\nnamespace Erdos.Statements.${modStem}\ndef Claim : Prop := True\nend Erdos.Statements.${modStem}\nnamespace Erdos.Claims.${modStem}_Shadow\ntheorem shadowed : Erdos.Statements.${modStem}.Claim := trivial\nend Erdos.Claims.${modStem}_Shadow\n`
  );

  try {
    const stmtRel = `missions/erdos-combinatorics/lean/Erdos/Statements/${modStem}.lean`;
    const resFrozenPass = checkLeanProof(testClaimPass, `Erdos.Claims.${modStem}_Pass.ok`, {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: stmtRel,
      statementDef: `Erdos.Statements.${modStem}.Claim`,
    });
    assert(resFrozenPass.ok && resFrozenPass.statement_frozen === true, "Frozen statement PASS: exact match", JSON.stringify(resFrozenPass));

    const resFrozenRefute = checkLeanProof(testClaimRefute, `Erdos.Claims.${modStem}_Refute.ref`, {
      judgeConfig: erdos.judge,
      kind: "refutation",
      statementFile: stmtRel,
      statementDef: `Erdos.Statements.${modStem}.FalseClaim`,
    });
    assert(resFrozenRefute.ok && resFrozenRefute.statement_frozen === true, "Frozen statement REFUTATION PASS: exact ¬ Claim match", JSON.stringify(resFrozenRefute));

    const resFrozenBait = checkLeanProof(testClaimBait, `Erdos.Claims.${modStem}_Bait.bait`, {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: stmtRel,
      statementDef: `Erdos.Statements.${modStem}.Claim`,
    });
    assert(!resFrozenBait.ok && resFrozenBait.reason.includes("frozen-statement gate"), "Frozen statement REJECT: bait theorem (True) blocked", JSON.stringify(resFrozenBait));

    const resFrozenShadow = checkLeanProof(testClaimShadow, `Erdos.Claims.${modStem}_Shadow.shadowed`, {
      judgeConfig: erdos.judge,
      kind: "proof",
      statementFile: stmtRel,
      statementDef: `Erdos.Statements.${modStem}.Claim`,
    });
    assert(!resFrozenShadow.ok && resFrozenShadow.reason.includes("duplicate/shadowed"), "Frozen statement REJECT: shadowed Claim := True blocked", JSON.stringify(resFrozenShadow));
  } finally {
    for (const f of [testStmtPath, testClaimPass, testClaimRefute, testClaimBait, testClaimShadow]) {
      try { fs.unlinkSync(f); } catch {}
    }
  }

  // King-of-the-Hill Record kernel checks (exact Expr mkNatLit equality, OfNat spoof defense!)
  const recStem = `_TestRec_${salt}`;
  const recStmtPath = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Statements/${recStem}.lean`);
  const recPass10 = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_s10.lean`);
  const recBound9 = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_not_s9.lean`);
  const recSpoofExplicit = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_spoof1.lean`);
  const recSpoofInst = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_spoof2.lean`);
  const recSucc = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_succ.lean`);
  const recWrongScore = path.resolve(`missions/erdos-combinatorics/lean/Erdos/Claims/${recStem}_s11.lean`);

  fs.writeFileSync(
    recStmtPath,
    `import Erdos.Core\nnamespace Erdos.Statements.${recStem}\ndef Record (score : Nat) : Prop := 10 ≤ score\ntheorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b := fun ha => Nat.le_trans ha h\nend Erdos.Statements.${recStem}\n`
  );
  fs.writeFileSync(
    recPass10,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_s10\ntheorem record : Erdos.Statements.${recStem}.Record 10 := Nat.le_refl 10\nend Erdos.Claims.${recStem}_s10\n`
  );
  fs.writeFileSync(
    recBound9,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_not_s9\ntheorem record : ¬ Erdos.Statements.${recStem}.Record 9 := by unfold Erdos.Statements.${recStem}.Record; decide\nend Erdos.Claims.${recStem}_not_s9\n`
  );
  // Opus P0 #1 attack: explicit forged OfNat instance printing like 10 while evaluating to 12!
  fs.writeFileSync(
    recSpoofExplicit,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_spoof1\ntheorem record : Erdos.Statements.${recStem}.Record (@OfNat.ofNat Nat 10 ⟨12⟩) := by unfold Erdos.Statements.${recStem}.Record; decide\nend Erdos.Claims.${recStem}_spoof1\n`
  );
  // Opus P0 #1 attack: local scoped OfNat Nat 10 := ⟨12⟩ so source literally reads `Record 10`!
  fs.writeFileSync(
    recSpoofInst,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_spoof2\nlocal instance (priority := high) : OfNat Nat 10 := ⟨12⟩\ntheorem record : Erdos.Statements.${recStem}.Record 10 := by unfold Erdos.Statements.${recStem}.Record; decide\nend Erdos.Claims.${recStem}_spoof2\n`
  );
  fs.writeFileSync(
    recSucc,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_succ\ntheorem record : Erdos.Statements.${recStem}.Record (Nat.succ 9) := Nat.le_refl 10\nend Erdos.Claims.${recStem}_succ\n`
  );
  fs.writeFileSync(
    recWrongScore,
    `import Erdos.Core\nimport Erdos.Statements.${recStem}\nnamespace Erdos.Claims.${recStem}_s11\ntheorem record : Erdos.Statements.${recStem}.Record 11 := by unfold Erdos.Statements.${recStem}.Record; decide\nend Erdos.Claims.${recStem}_s11\n`
  );

  try {
    const recStmtRel = `missions/erdos-combinatorics/lean/Erdos/Statements/${recStem}.lean`;
    const recDef = `Erdos.Statements.${recStem}.Record`;

    const rRecPass = checkLeanProof(recPass10, `Erdos.Claims.${recStem}_s10.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(rRecPass.ok && rRecPass.statement_frozen === true && rRecPass.score === 10, "KotH PASS: canonical Record 10 accepted", JSON.stringify(rRecPass));

    const rBoundPass = checkLeanProof(recBound9, `Erdos.Claims.${recStem}_not_s9.record`, {
      judgeConfig: erdos.judge,
      kind: "record_bound",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 9,
    });
    assert(rBoundPass.ok && rBoundPass.statement_frozen === true && rBoundPass.score === 9, "KotH PASS: canonical ¬ Record 9 accepted", JSON.stringify(rBoundPass));

    const rSpoof1 = checkLeanProof(recSpoofExplicit, `Erdos.Claims.${recStem}_spoof1.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(!rSpoof1.ok && rSpoof1.reason.includes("frozen-statement gate"), "KotH REJECT (Opus P0 #1): explicit @OfNat.ofNat Nat 10 ⟨12⟩ spoof blocked", JSON.stringify(rSpoof1));

    const rSpoof2 = checkLeanProof(recSpoofInst, `Erdos.Claims.${recStem}_spoof2.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(!rSpoof2.ok && rSpoof2.reason.includes("frozen-statement gate"), "KotH REJECT (Opus P0 #1): local fake OfNat Nat 10 instance spoof blocked", JSON.stringify(rSpoof2));

    const rSucc = checkLeanProof(recSucc, `Erdos.Claims.${recStem}_succ.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(!rSucc.ok && rSucc.reason.includes("frozen-statement gate"), "KotH REJECT: non-canonical Record (Nat.succ 9) blocked", JSON.stringify(rSucc));

    const rWrong = checkLeanProof(recWrongScore, `Erdos.Claims.${recStem}_s11.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(!rWrong.ok && rWrong.reason.includes("frozen-statement gate"), "KotH REJECT: wrong score Record 11 vs expected 10 blocked", JSON.stringify(rWrong));

    const rPol1 = checkLeanProof(recPass10, `Erdos.Claims.${recStem}_s10.record`, {
      judgeConfig: erdos.judge,
      kind: "record_bound",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 10,
    });
    assert(!rPol1.ok && rPol1.reason.includes("frozen-statement gate"), "KotH REJECT: wrong polarity (Record 10 for record_bound) blocked", JSON.stringify(rPol1));

    const rPol2 = checkLeanProof(recBound9, `Erdos.Claims.${recStem}_not_s9.record`, {
      judgeConfig: erdos.judge,
      kind: "record",
      statementFile: recStmtRel,
      statementDef: recDef,
      expectedScore: 9,
    });
    assert(!rPol2.ok && rPol2.reason.includes("frozen-statement gate"), "KotH REJECT: wrong polarity (¬ Record 9 for record) blocked", JSON.stringify(rPol2));

    for (const badScore of ["10; #eval 1", "-1", "01", "NaN"]) {
      const rInj = checkLeanProof(recPass10, `Erdos.Claims.${recStem}_s10.record`, {
        judgeConfig: erdos.judge,
        kind: "record",
        statementFile: recStmtRel,
        statementDef: recDef,
        expectedScore: badScore,
      });
      assert(!rInj.ok && rInj.reason.includes("Invalid canonical Nat score"), `KotH REJECT: invalid/injection score ${JSON.stringify(badScore)} blocked`, JSON.stringify(rInj));
    }
  } finally {
    for (const f of [recStmtPath, recPass10, recBound9, recSpoofExplicit, recSpoofInst, recSucc, recWrongScore]) {
      try { fs.unlinkSync(f); } catch {}
    }
  }

  const policyFile = path.join(tmp, "Policy.lean");
  fs.writeFileSync(policyFile, Buffer.from([0xff]));
  const invalidSource = checkLeanProof(policyFile, "target", { allowTempForTests: true });
  assert(!invalidSource.ok && invalidSource.reason === "Invalid UTF-8 source", "Invalid UTF-8 is not normalized into a different proof", JSON.stringify(invalidSource));
  for (const [source, expected] of [
    ['attribute [extern "c_fn"] sample', "extern"],
    ["attribute [implemented_by sample] other", "implemented_by"],
    ["@[init] def sample := 0", "init"],
    ["opaque sample : Nat := 0", "opaque"],
    ["unsafe def sample : Nat := 0", "unsafe"],
    ["unsafe def Sample.ctorIdx._impl : Nat := 0", "unsafe"],
    ["axiom sample : True", "axiom"],
    ["set_option /- comment -/\n  debug.skipKernelTC false", "disallowed set_option"],
    ["import /- comment -/\n Lean.Elab.Command", "disallowed import"],
    ['syntax "sample" : term', "syntax"],
    ["macro_rules | `(sample) => `(0)", "macro_rules"],
    ["def sample := by_elab pure default", "by_elab"],
    ["initialize sample : Nat ← pure 0", "initialize"],
    ["run_cmd pure ()", "run_cmd"],
    ["#eval 0", "#eval"],
    ["theorem sample :", "parse error"],
  ]) {
    fs.writeFileSync(policyFile, source + "\n");
    const res = auditLeanSyntax(policyFile);
    assert(!res.ok && res.reason.includes(expected), `Native syntax policy: ${expected}`, JSON.stringify(res));
  }
  fs.writeFileSync(policyFile, 'attribute [extern "unused"] sample\n');
  const precompile = checkLeanProof(policyFile, "target", { allowTempForTests: true });
  assert(!precompile.ok && precompile.reason.includes("Lean AST gate: forbidden extern"),
    "Native policy stops a standalone attribute before compilation", JSON.stringify(precompile));
  fs.writeFileSync(policyFile, "partial def unused : Nat → Nat | n => unused n\ntheorem target : True := trivial\n");
  const unused = checkLeanProof(policyFile, "target", { allowTempForTests: true });
  assert(!unused.ok && unused.reason.includes("compiled environment audit") && unused.reason.includes("unused"),
    "Compiled module audit rejects an unrelated partial helper", JSON.stringify(unused));

  const compiledFixtures = [
    ["ForeignImport", "import Lean.Elab.Command", "", "disallowed import Lean.Elab.Command"],
    ["UnusedAxiom", "", "axiom helper : True", "disallowed constant UnusedAxiom.helper"],
    ["UnusedOpaque", "", "opaque helper : Nat := 0", "disallowed constant UnusedOpaque.helper"],
    ["UnusedUnsafe", "", "unsafe def helper : Nat := 0", "disallowed constant UnusedUnsafe.helper"],
    ["Lookalike", "", "structure Box where value : Nat\nunsafe def Box.ctorIdx._impl := 0", "disallowed constant Lookalike.Box.ctorIdx._impl"],
  ];
  const elanLean = path.join(os.homedir(), ".elan", "bin", "lean");
  const lean = fs.existsSync(elanLean) ? elanLean : "lean";
  const leanOpts = { cwd: path.resolve("lean"), env: { ...process.env, LEAN_PATH: tmp }, timeout: 30000, encoding: "utf8" };
  for (const [mod, header, decl] of compiledFixtures) {
    const src = path.join(tmp, `${mod}.lean`);
    fs.writeFileSync(src, `${header}\nnamespace ${mod}\n${decl}\ntheorem target : True := trivial\nend ${mod}\n`);
    execFileSync(lean, ["-R", tmp, "-o", path.join(tmp, `${mod}.olean`), src], leanOpts);
  }
  const fixtureAudit = path.join(tmp, "FixtureAudit.lean");
  fs.writeFileSync(fixtureAudit, [
    "import Lean", ...compiledFixtures.map(([mod]) => `import ${mod}`), compiledModulePolicy,
    "open Lean in", "#eval show CoreM Unit from do", "  let env ← getEnv",
    ...compiledFixtures.map(([mod]) => `  IO.println (modulePolicyError env \`${mod} \`${mod}.target "PnP")`), "",
  ].join("\n"));
  const findings = execFileSync(lean, [fixtureAudit], leanOpts).trim().split("\n");
  for (const [, , , expected] of compiledFixtures) {
    assert(findings.includes(expected), `Independent compiled audit: ${expected}`, findings);
  }

  for (const slug of listMissionSlugs()) {
    const { judge } = loadMission(slug);
    if (judge.type !== "lean4") continue;
    for (const claim of deriveMissionState(slug).state.lemmas) {
      const cases = [];
      if (claim.kind === "record") {
        for (const record of claim.record_state.history.filter(entry => entry.state === "accepted")) {
          const { theoremName } = computeRecordTargets(slug, claim, record.kind, record.score);
          cases.push([record.file, theoremName, record.kind, record.score]);
        }
      } else if (claim.status === "checked") {
        cases.push([claim.lean_file, claim.theorem_name, "proof"]);
      } else if (claim.status === "refuted") {
        cases.push([claim.refutation.counterexample_file, claim.refutation.theorem_name, "refutation"]);
      }
      for (const [file, theorem, kind, score] of cases) {
        const res = checkLeanProof(file, theorem, {
          judgeConfig: judge, kind, expectedScore: score, statementFile: claim.statement_file, statementDef: claim.statement_def,
        });
        assert(res.ok && res.ast_audited && res.env_audited, `Mission proof: ${file}`, JSON.stringify(res));
      }
    }
  }
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}

if (failed > 0) {
  console.error(`\n${failed} Judge test(s) failed!`);
  process.exit(1);
}
console.log(`\nALL ${passed} JUDGE TESTS PASSED!`);
