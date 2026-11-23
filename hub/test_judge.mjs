#!/usr/bin/env node
/**
 * hub/test_judge.mjs — Adversarial security regression test for our hardened Lean 4 Judge.
 * Reproduces ALL 3 live exploits Claude Opus 5.5 found + Attack D (native_decide) + Path traversal,
 * proving every single attack is REJECTED while a legitimate Lean 4 theorem PASSES with full type.
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { checkLeanProof } from "./checker.mjs";

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

  // Attack B: inline `axiom cheat : False` + fake axiom print
  const fileB = path.join(tmp, "AttackB.lean");
  fs.writeFileSync(
    fileB,
    `namespace X\ndef a := 1 axiom cheat : False\ntheorem t : 1 = 2 := cheat.elim\nend X\n`
  );
  const resB = checkLeanProof(fileB, "X.t", { allowTempForTests: true });
  assert(!resB.ok, "Attack B (inline axiom cheat : False) rejected", JSON.stringify(resB));

  // Attack C: empty file inside lean/PnP/Lemmas/ claiming `Nat.add_comm` from Init
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

  // Attack D: string-hidden comment delimiter hiding `sorry`
  const fileD = path.join(tmp, "AttackD.lean");
  fs.writeFileSync(
    fileD,
    `def s := "/-"\ntheorem fake : False := by sorry\ndef e := "-/"\n`
  );
  const resD = checkLeanProof(fileD, "fake", { allowTempForTests: true });
  assert(!resD.ok, "Attack D (string-escaped comment hiding sorry) rejected", JSON.stringify(resD));

  // Attack E: Path traversal outside lean/PnP/Lemmas/ (without allowTempForTests)
  const fileE = path.join(tmp, "AttackE.lean");
  fs.writeFileSync(fileE, `import PnP.Core\n`);
  const resE = checkLeanProof(fileE, "Nat.add_comm");
  assert(
    !resE.ok && resE.reason.includes("path gate"),
    "Attack E (outside lean/PnP/Lemmas/) rejected by canonical path gate",
    JSON.stringify(resE)
  );

  // Legitimate proof check: L_lib_000.lean must PASS with FULL multi-line type!
  const resOk = checkLeanProof(
    "lean/PnP/Lemmas/L_lib_000.lean",
    "PnP.Lemmas.L_lib_000.flipBit_involutive"
  );
  assert(
    resOk.ok && resOk.signature.includes("flipBit (PnP.flipBit x i) i = x"),
    "Legitimate theorem L_lib_000 passes with FULL untruncated signature",
    JSON.stringify(resOk)
  );
} finally {
  fs.rmSync(tmp, { recursive: true, force: true });
}

if (failed > 0) {
  console.error(`\n${failed} test(s) failed!`);
  process.exit(1);
}
console.log("\nALL 6 ADVERSARIAL & REGRESSION TESTS PASSED!");
