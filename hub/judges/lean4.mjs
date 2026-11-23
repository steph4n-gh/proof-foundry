#!/usr/bin/env node
/**
 * hub/judges/lean4.mjs — Generalized, Airtight Lean 4 Kernel Metaprogram Judge.
 *
 * Works for ANY Lean 4 mission (configured via `mission.judge`):
 * - Canonical realpath containment inside mission's `allowed_dirs`
 * - Lean-aware comment/string lexer banning sorry, admit, axiom, unsafe, opaque,
 *   extern, implemented_by, native_decide, #eval, #exit, #print, run_cmd, elab, macro, syntax, initialize
 * - Isolated per-run `.olean` compilation + Judge-owned Lean metaprogram calling
 *   `Environment.find?`, `ConstantInfo.thmInfo`, `getModuleIdxFor?`, and `Lean.collectAxioms`
 * - Writes structured JSON to a Judge-owned file (zero stdout scraping)
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";

const ROOT = path.resolve(import.meta.dirname, "../..");

const DEFAULT_JUDGE_CONFIG = {
  lean_dir: "lean",
  lake_target: "PnP",
  core_file: "lean/PnP/Core.lean",
  core_olean: "lean/.lake/build/lib/lean/PnP/Core.olean",
  allowed_dirs: ["lean/PnP/Lemmas", "lean/PnP/Statements"],
  allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
};

const FORBIDDEN_TOKENS = [
  { name: "sorry", re: /\bsorry\b/ },
  { name: "admit", re: /\badmit\b/ },
  { name: "axiom", re: /\baxiom\b/ },
  { name: "unsafe", re: /\bunsafe\b/ },
  { name: "opaque", re: /\bopaque\b/ },
  { name: "implemented_by", re: /\bimplemented_by\b/ },
  { name: "extern", re: /@\[[^\]]*\bextern\b/ },
  { name: "native_decide", re: /\bnative_decide\b/ },
  { name: "#eval", re: /#eval\b/ },
  { name: "#exit", re: /#exit\b/ },
  { name: "#print", re: /#print\b/ },
  { name: "run_cmd", re: /\brun_cmd\b/ },
  { name: "elab", re: /\belab(_rules)?\b/ },
  { name: "macro", re: /\bmacro(_rules)?\b/ },
  { name: "syntax", re: /\bsyntax\b/ },
  { name: "initialize", re: /\binitialize\b/ },
];

export function stripLeanCommentsAndStrings(src) {
  let out = "";
  let i = 0;
  let blockDepth = 0;
  let inLine = false;
  let inString = false;

  while (i < src.length) {
    const ch = src[i];
    const next = src[i + 1];

    if (inLine) {
      if (ch === "\n") {
        inLine = false;
        out += "\n";
      }
      i++;
      continue;
    }
    if (blockDepth > 0) {
      if (ch === "/" && next === "-") {
        blockDepth++;
        i += 2;
      } else if (ch === "-" && next === "/") {
        blockDepth--;
        out += " ";
        i += 2;
      } else {
        if (ch === "\n") out += "\n";
        i++;
      }
      continue;
    }
    if (inString) {
      if (ch === "\\" && i + 1 < src.length) {
        i += 2;
      } else if (ch === '"') {
        inString = false;
        out += '""';
        i++;
      } else {
        i++;
      }
      continue;
    }
    if (ch === "/" && next === "-") {
      blockDepth = 1;
      out += " ";
      i += 2;
      continue;
    }
    if (ch === "-" && next === "-") {
      inLine = true;
      out += " ";
      i += 2;
      continue;
    }
    if (ch === '"') {
      inString = true;
      i++;
      continue;
    }
    out += ch;
    i++;
  }
  return { stripped: out, unclosedComment: blockDepth > 0, unclosedString: inString };
}

export function sha256File(filePath) {
  if (!filePath || !fs.existsSync(filePath)) return null;
  return crypto.createHash("sha256").update(fs.readFileSync(filePath)).digest("hex");
}

export function getLeanVersion(leanDir) {
  const res = spawnSync("lean", ["--version"], { encoding: "utf8", cwd: leanDir });
  if (res.status !== 0) return "lean-unknown";
  return (res.stdout || "").trim().split("\n")[0] || "lean-unknown";
}

function validateLeanIdentifier(name) {
  return /^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(String(name || ""));
}

export function checkLeanProof(relOrAbsFile, theoremName, opts = {}) {
  const cfg = { ...DEFAULT_JUDGE_CONFIG, ...(opts.judgeConfig || {}) };
  const leanDir = path.resolve(ROOT, cfg.lean_dir);
  const coreFile = cfg.core_file ? path.resolve(ROOT, cfg.core_file) : null;
  const coreOlean = cfg.core_olean ? path.resolve(ROOT, cfg.core_olean) : null;
  const allowedDirs = (cfg.allowed_dirs || []).map((d) => path.resolve(ROOT, d));
  const allowedAxioms = new Set(cfg.allowed_axioms || ["propext", "Classical.choice", "Quot.sound"]);

  const started = Date.now();
  const leanVersion = getLeanVersion(leanDir);
  const coreHash = sha256File(coreFile);

  if (!validateLeanIdentifier(theoremName)) {
    return {
      ok: false,
      judge: "lean4",
      reason: `Invalid Lean theorem identifier: ${theoremName}`,
      file: relOrAbsFile,
      theorem: theoremName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: null,
      core_hash: coreHash,
      output: "",
    };
  }

  const absFile = path.isAbsolute(relOrAbsFile)
    ? relOrAbsFile
    : path.resolve(ROOT, relOrAbsFile);
  if (!fs.existsSync(absFile)) {
    return {
      ok: false,
      judge: "lean4",
      reason: `File not found: ${relOrAbsFile}`,
      file: relOrAbsFile,
      theorem: theoremName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: null,
      core_hash: coreHash,
      output: "",
    };
  }

  const realFile = fs.realpathSync(absFile);
  const relFile = path.relative(ROOT, realFile);
  if (!realFile.endsWith(".lean")) {
    return {
      ok: false,
      judge: "lean4",
      reason: "Submitted file must have a .lean extension",
      file: relFile,
      theorem: theoremName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: null,
      core_hash: coreHash,
      output: "",
    };
  }

  if (!opts.allowTempForTests) {
    const insideAllowed = allowedDirs.some((dir) => {
      try {
        const realDir = fs.realpathSync(dir);
        return realFile.startsWith(realDir + path.sep);
      } catch {
        return false;
      }
    });
    if (!insideAllowed) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Rejected by path gate: file must reside inside ${cfg.allowed_dirs.join(" or ")}`,
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: null,
        core_hash: coreHash,
        output: "",
      };
    }
  }

  const rawSource = fs.readFileSync(realFile, "utf8");
  const fileHash = crypto.createHash("sha256").update(rawSource).digest("hex");

  const lex = stripLeanCommentsAndStrings(rawSource);
  if (lex.unclosedComment || lex.unclosedString) {
    return {
      ok: false,
      judge: "lean4",
      reason: "Rejected by static gate: unclosed comment or string literal",
      file: relFile,
      theorem: theoremName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: fileHash,
      core_hash: coreHash,
      output: "",
    };
  }
  for (const pat of FORBIDDEN_TOKENS) {
    if (pat.re.test(lex.stripped)) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Rejected by static gate: forbidden construct "${pat.name}" detected`,
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: `Forbidden token: ${pat.name}`,
      };
    }
  }

  // Build core library only if missing or stale
  let needBuild = true;
  if (coreOlean && coreFile && fs.existsSync(coreOlean) && fs.existsSync(coreFile)) {
    if (fs.statSync(coreOlean).mtimeMs >= fs.statSync(coreFile).mtimeMs) needBuild = false;
  } else if (!cfg.lake_target) {
    needBuild = false;
  }
  if (needBuild && cfg.lake_target) {
    const b = spawnSync("lake", ["build", cfg.lake_target], { encoding: "utf8", cwd: leanDir });
    if (b.status !== 0) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Core library \`lake build ${cfg.lake_target}\` failed`,
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: ((b.stdout || "") + "\n" + (b.stderr || "")).trim().slice(0, 4000),
      };
    }
  }

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "fleet-lean4-judge-"));
  const modStem = `Sub_${process.pid}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  const modName = `FleetJudgeTmp.${modStem}`;
  const oleanDir = path.join(tmpDir, "FleetJudgeTmp");
  fs.mkdirSync(oleanDir, { recursive: true });
  const oleanPath = path.join(oleanDir, `${modStem}.olean`);
  const auditLeanPath = path.join(tmpDir, "JudgeAudit.lean");
  const resultJsonPath = path.join(tmpDir, "result.json");

  try {
    const lpRes = spawnSync("lake", ["env", "printenv", "LEAN_PATH"], {
      encoding: "utf8",
      cwd: leanDir,
    });
    const baseLeanPath =
      lpRes.status === 0
        ? (lpRes.stdout || "").trim()
        : path.join(leanDir, ".lake", "build", "lib", "lean");
    const envWithPath = {
      ...process.env,
      LEAN_PATH: `${tmpDir}${path.delimiter}${baseLeanPath}`,
    };

    const pass1 = spawnSync("lake", ["env", "lean", "-o", oleanPath, realFile], {
      encoding: "utf8",
      cwd: leanDir,
      env: envWithPath,
      timeout: 90000,
    });
    if (pass1.status !== 0 || !fs.existsSync(oleanPath)) {
      return {
        ok: false,
        judge: "lean4",
        reason: "Lean 4 kernel typecheck failed",
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: ((pass1.stdout || "") + "\n" + (pass1.stderr || "")).trim().slice(0, 4000),
      };
    }

    const escapedResultPath = JSON.stringify(resultJsonPath);
    const auditProgram = `import Lean.Util.CollectAxioms
import Lean.Meta.Basic
import Lean.Data.Json
import ${modName}

open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let target : Name := \`${theoremName}
  let expectedMod : Name := \`${modName}
  match env.find? target with
  | none =>
      let j := Json.mkObj [("found", Json.bool false)]
      IO.FS.writeFile ${escapedResultPath} j.compress
  | some info =>
      let isThm := match info with | .thmInfo _ => true | _ => false
      let modNameStr := match env.getModuleIdxFor? target with
        | some idx => (env.header.moduleNames[idx]!).toString
        | none => ""
      let inSubmittedMod := modNameStr == expectedMod.toString
      let axioms ← Lean.collectAxioms target
      let fmt ← ppExpr info.type
      let j := Json.mkObj [
        ("found", Json.bool true),
        ("isTheorem", Json.bool isThm),
        ("inSubmittedMod", Json.bool inSubmittedMod),
        ("declaredModule", Json.str modNameStr),
        ("axioms", Json.arr (axioms.map (fun n => Json.str n.toString))),
        ("type", Json.str fmt.pretty)
      ]
      IO.FS.writeFile ${escapedResultPath} j.compress
`;
    fs.writeFileSync(auditLeanPath, auditProgram, "utf8");

    const pass2 = spawnSync("lake", ["env", "lean", auditLeanPath], {
      encoding: "utf8",
      cwd: leanDir,
      env: envWithPath,
      timeout: 90000,
    });
    if (pass2.status !== 0 || !fs.existsSync(resultJsonPath)) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Judge kernel audit failed for ${theoremName}`,
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: ((pass2.stdout || "") + "\n" + (pass2.stderr || "")).trim().slice(0, 4000),
      };
    }

    const audit = JSON.parse(fs.readFileSync(resultJsonPath, "utf8"));
    if (!audit.found) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Theorem \`${theoremName}\` not found in compiled environment`,
        file: relFile,
        theorem: theoremName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: "",
      };
    }
    if (!audit.inSubmittedMod) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Rejected: \`${theoremName}\` was NOT declared in submitted file (declared in \`${audit.declaredModule || "unknown"}\`)`,
        file: relFile,
        theorem: theoremName,
        axioms: audit.axioms || [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: "",
      };
    }
    if (!audit.isTheorem) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Rejected: \`${theoremName}\` is not a theorem (ConstantInfo.thmInfo required)`,
        file: relFile,
        theorem: theoremName,
        axioms: audit.axioms || [],
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: "",
      };
    }

    const axioms = Array.isArray(audit.axioms) ? audit.axioms : [];
    const disallowed = axioms.filter((a) => !allowedAxioms.has(a));
    if (disallowed.length > 0) {
      return {
        ok: false,
        judge: "lean4",
        reason: `Disallowed kernel axioms detected: ${disallowed.join(", ")}`,
        file: relFile,
        theorem: theoremName,
        axioms,
        duration_ms: Date.now() - started,
        lean_version: leanVersion,
        file_hash: fileHash,
        core_hash: coreHash,
        output: `Axioms: ${axioms.join(", ")}`,
      };
    }

    return {
      ok: true,
      judge: "lean4",
      reason: "Verified by isolated Lean 4 kernel metaprogram (zero sorry, standard axioms only, module-bound)",
      file: relFile,
      theorem: theoremName,
      signature: `${theoremName} :\n  ${audit.type}`,
      axioms,
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: fileHash,
      core_hash: coreHash,
      output: (pass1.stdout || "").trim().slice(0, 2000),
    };
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {}
  }
}
