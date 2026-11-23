#!/usr/bin/env node
/**
 * hub/judges/lean4.mjs — Hardened Isolated Lean 4 Kernel Metaprogram Judge (v3).
 *
 * Security & Verification Guarantees (hardened per Opus 5.5 + Astra 6.2 audits):
 * 1. Canonical realpath containment inside mission's `allowed_dirs`.
 * 2. Lean-aware lexer rejecting guillemets (`«`/`»`) and raw strings (`r"`/`r#`), handling nested
 *    `/- ... -/`, `-- ...`, `"..."` strings, and `'c'` char literals with zero desync.
 * 3. Strict import allowlist (`<lake_target>.*`, `Init`, `Std` — zero `import Lean*`), strict
 *    `set_option` allowlist (`maxHeartbeats`, `maxRecDepth`, `autoImplicit`), and expanded forbidden
 *    token gate (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`,
 *    `native_decide`, `#eval`, `#exit`, `#print`, `run_cmd`, `run_tac`, `run_meta`, `by_elab`,
 *    `elab`, `macro`, `syntax`, `declare_syntax_cat`, `simproc`, `dsimproc`, `initialize`,
 *    `builtin_initialize`, `@[init`, `@[tactic`, `@[delab`, `@[app_unexpander`, `skipKernelTC`,
 *    `modifyEnv`).
 * 4. Minimal sanitized environment (never passes `...process.env`) and resolved absolute `lean` path.
 * 5. Isolated per-run `.olean` compilation + Frozen-Statement Kernel Type-Matching importing BOTH
 *    trusted `stmtMod` and `claimMod` (dual-import blocks shadowing) with exact syntactic `Expr` match.
 * 6. Kernel `Lean.collectAxioms` written to a Judge-owned JSON file.
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

const ALLOWED_SET_OPTIONS = new Set(["maxHeartbeats", "maxRecDepth", "autoImplicit"]);

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
  { name: "run_tac", re: /\brun_tac\b/ },
  { name: "run_meta", re: /\brun_meta\b/ },
  { name: "by_elab", re: /\bby_elab\b/ },
  { name: "elab", re: /\b([a-z_]*elab(_rules)?)\b/ },
  { name: "tactic attribute", re: /@\[[^\]]*\btactic\b/ },
  { name: "init attribute", re: /@\[[^\]]*\binit\b/ },
  { name: "delab/unexpander attribute", re: /@\[[^\]]*\b(delab|app_unexpander)\b/ },
  { name: "macro", re: /\bmacro(_rules)?\b/ },
  { name: "syntax", re: /\bsyntax\b/ },
  { name: "declare_syntax_cat", re: /\bdeclare_syntax_cat\b/ },
  { name: "simproc", re: /\b(d?simproc(_decl)?)\b/ },
  { name: "initialize", re: /\b(builtin_)?initialize\b/ },
  { name: "skipKernelTC", re: /\bskipKernelTC\b/ },
  { name: "modifyEnv", re: /\bmodifyEnv\b/ },
];

function minimalEnv(extra = {}) {
  return {
    PATH: process.env.PATH || "/usr/local/bin:/usr/bin:/bin",
    HOME: process.env.HOME || os.homedir(),
    TMPDIR: process.env.TMPDIR || os.tmpdir(),
    LANG: process.env.LANG || "C.UTF-8",
    ...extra,
  };
}

let cachedLeanBin = null;
function resolveBinary(name) {
  const candidates = [
    path.join(os.homedir(), ".elan", "bin", name),
    `/usr/local/bin/${name}`,
    `/usr/bin/${name}`,
  ];
  for (const c of candidates) {
    if (fs.existsSync(c)) return c;
  }
  const which = spawnSync("which", [name], { encoding: "utf8", env: minimalEnv() });
  if (which.status === 0 && which.stdout.trim()) return which.stdout.trim().split("\n")[0];
  return name;
}

function getLeanBin() {
  if (!cachedLeanBin) cachedLeanBin = resolveBinary("lean");
  return cachedLeanBin;
}

/**
 * Strip nested block comments, line comments, string literals, and char literals.
 * Explicitly flags guillemet identifiers («…») and raw strings (r"…"/r#"…"#) as forbidden
 * so they can NEVER desync string/comment scanning.
 */
export function stripLeanCommentsAndStrings(src) {
  let out = "";
  let i = 0;
  let blockDepth = 0;
  let inLine = false;
  let inString = false;
  let forbiddenLexeme = null;

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
    // Reject guillemet identifiers «...» (can contain ", /-, -- and desync lexing!)
    if (ch === "«" || ch === "»") {
      forbiddenLexeme = "guillemet identifier («…»)";
      break;
    }
    // Reject Lean raw strings r"..." / r#"..."# (not preceded by identifier char)
    if (ch === "r" && (i === 0 || !/[A-Za-z0-9_']/.test(src[i - 1])) && (next === '"' || next === "#")) {
      let j = i + 1;
      while (src[j] === "#") j++;
      if (src[j] === '"') {
        forbiddenLexeme = "raw string literal (r\"…\" / r#\"…\"#)";
        break;
      }
    }
    // Char literal: e.g. 'a', '"', '\n', '\'' — only when NOT preceded by identifier char (prime suffix x')
    if (ch === "'" && (i === 0 || !/[A-Za-z0-9_']/.test(src[i - 1]))) {
      if (next === "\\" && i + 3 < src.length && src[i + 3] === "'") {
        out += "''";
        i += 4;
        continue;
      }
      if (next !== "'" && next !== "\n" && i + 2 < src.length && src[i + 2] === "'") {
        out += "''";
        i += 3;
        continue;
      }
    }
    if (ch === '"') {
      inString = true;
      i++;
      continue;
    }
    out += ch;
    i++;
  }
  return { stripped: out, unclosedComment: blockDepth > 0, unclosedString: inString, forbiddenLexeme };
}

export function sha256File(filePath) {
  if (!filePath || !fs.existsSync(filePath)) return null;
  return crypto.createHash("sha256").update(fs.readFileSync(filePath)).digest("hex");
}

export function getLeanVersion(leanDir) {
  const res = spawnSync(getLeanBin(), ["--version"], { encoding: "utf8", cwd: leanDir, env: minimalEnv() });
  if (res.status !== 0) return "lean-unknown";
  return (res.stdout || "").trim().split("\n")[0] || "lean-unknown";
}

function validateLeanIdentifier(name) {
  return /^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(String(name || ""));
}

function checkImportsAndOptions(stripped, lakeTarget) {
  // Enforce import allowlist: only `<lakeTarget>`, `<lakeTarget>.*`, `Init`, `Init.*`, `Std`, `Std.*`
  const importRe = /^\s*import\s+([^\s]+)/gm;
  let m;
  while ((m = importRe.exec(stripped)) !== null) {
    const mod = m[1];
    const allowedPrefixes = ["Init", "Std"];
    if (lakeTarget) allowedPrefixes.push(lakeTarget);
    const ok = allowedPrefixes.some((p) => mod === p || mod.startsWith(`${p}.`));
    if (!ok) {
      return `Disallowed import "${mod}" (only ${allowedPrefixes.join(", ")} modules allowed)`;
    }
  }
  // Enforce set_option allowlist (blocks debug.skipKernelTC, etc.)
  const optRe = /\bset_option\s+([A-Za-z0-9_.]+)/g;
  while ((m = optRe.exec(stripped)) !== null) {
    const opt = m[1];
    if (!ALLOWED_SET_OPTIONS.has(opt)) {
      return `Disallowed set_option "${opt}" (only ${[...ALLOWED_SET_OPTIONS].join(", ")} allowed)`;
    }
  }
  return null;
}

export function checkLeanProof(relOrAbsFile, theoremName, opts = {}) {
  const cfg = { ...DEFAULT_JUDGE_CONFIG, ...(opts.judgeConfig || {}) };
  const leanDir = path.resolve(ROOT, cfg.lean_dir);
  const coreFile = cfg.core_file ? path.resolve(ROOT, cfg.core_file) : null;
  const coreOlean = cfg.core_olean ? path.resolve(ROOT, cfg.core_olean) : null;
  const allowedDirs = (cfg.allowed_dirs || []).map((d) => path.resolve(ROOT, d));
  const allowedAxioms = new Set(cfg.allowed_axioms || ["propext", "Classical.choice", "Quot.sound"]);
  const kind = opts.kind === "refutation" ? "refutation" : "proof";
  const leanBin = getLeanBin();
  const lakeBin = resolveBinary("lake");

  const started = Date.now();
  const leanVersion = getLeanVersion(leanDir);
  const coreHash = sha256File(coreFile);

  const fail = (reason, extra = {}) => ({
    ok: false,
    judge: "lean4",
    reason,
    file: relOrAbsFile,
    theorem: theoremName,
    axioms: [],
    duration_ms: Date.now() - started,
    lean_version: leanVersion,
    file_hash: null,
    core_hash: coreHash,
    statement_frozen: false,
    statement_hash: null,
    output: "",
    ...extra,
  });

  if (!validateLeanIdentifier(theoremName)) {
    return fail(`Invalid Lean theorem identifier: ${theoremName}`);
  }

  const absFile = path.isAbsolute(relOrAbsFile) ? relOrAbsFile : path.resolve(ROOT, relOrAbsFile);
  if (!fs.existsSync(absFile)) return fail(`File not found: ${relOrAbsFile}`);

  // Reject symlinks directly even before realpath containment
  if (fs.lstatSync(absFile).isSymbolicLink()) {
    return fail(`Rejected by path gate: symlinks are forbidden (${relOrAbsFile})`);
  }

  const realFile = fs.realpathSync(absFile);
  const relFile = path.relative(ROOT, realFile);
  if (!realFile.endsWith(".lean")) return fail("Submitted file must have a .lean extension", { file: relFile });

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
      return fail(`Rejected by path gate: file must reside inside ${cfg.allowed_dirs.join(" or ")}`, { file: relFile });
    }
  }

  const rawSource = fs.readFileSync(realFile, "utf8");
  const fileHash = crypto.createHash("sha256").update(rawSource).digest("hex");

  const lex = stripLeanCommentsAndStrings(rawSource);
  if (lex.forbiddenLexeme) {
    return fail(`Rejected by static gate: forbidden ${lex.forbiddenLexeme}`, { file: relFile, file_hash: fileHash });
  }
  if (lex.unclosedComment || lex.unclosedString) {
    return fail("Rejected by static gate: unclosed comment or string literal", { file: relFile, file_hash: fileHash });
  }
  const impOptErr = checkImportsAndOptions(lex.stripped, cfg.lake_target);
  if (impOptErr) {
    return fail(`Rejected by static gate: ${impOptErr}`, { file: relFile, file_hash: fileHash });
  }
  for (const pat of FORBIDDEN_TOKENS) {
    if (pat.re.test(lex.stripped)) {
      return fail(`Rejected by static gate: forbidden construct "${pat.name}" detected`, {
        file: relFile,
        file_hash: fileHash,
        output: `Forbidden token: ${pat.name}`,
      });
    }
  }

  // Optional frozen statement binding
  let realStmtFile = null;
  let stmtHash = null;
  const stmtDef = opts.statementDef || null;
  if (opts.statementFile) {
    const absStmt = path.isAbsolute(opts.statementFile) ? opts.statementFile : path.resolve(ROOT, opts.statementFile);
    if (!fs.existsSync(absStmt)) {
      return fail(`Frozen statement file missing: ${opts.statementFile}`, { file: relFile, file_hash: fileHash });
    }
    if (!validateLeanIdentifier(stmtDef)) {
      return fail(`Invalid frozen statement identifier: ${stmtDef}`, { file: relFile, file_hash: fileHash });
    }
    realStmtFile = fs.realpathSync(absStmt);
    stmtHash = sha256File(realStmtFile);
  }

  // Ensure Core library is built
  let needBuild = true;
  if (coreOlean && coreFile && fs.existsSync(coreOlean) && fs.existsSync(coreFile)) {
    if (fs.statSync(coreOlean).mtimeMs >= fs.statSync(coreFile).mtimeMs) needBuild = false;
  } else if (!cfg.lake_target) {
    needBuild = false;
  }
  if (needBuild && cfg.lake_target) {
    const b = spawnSync(lakeBin, ["build", cfg.lake_target], { encoding: "utf8", cwd: leanDir, env: minimalEnv() });
    if (b.status !== 0) {
      return fail(`Core library \`lake build ${cfg.lake_target}\` failed`, {
        file: relFile,
        file_hash: fileHash,
        output: ((b.stdout || "") + "\n" + (b.stderr || "")).trim().slice(0, 4000),
      });
    }
  }

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "fleet-lean4-judge-"));
  const salt = `${process.pid}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  const claimMod = `FleetJudgeTmp.Sub_${salt}`;
  const oleanDir = path.join(tmpDir, "FleetJudgeTmp");
  fs.mkdirSync(oleanDir, { recursive: true });
  const claimOlean = path.join(oleanDir, `Sub_${salt}.olean`);
  const auditLeanPath = path.join(tmpDir, "JudgeAudit.lean");
  const resultJsonPath = path.join(tmpDir, "result.json");

  try {
    const lpRes = spawnSync(lakeBin, ["env", "printenv", "LEAN_PATH"], { encoding: "utf8", cwd: leanDir, env: minimalEnv() });
    const baseLeanPath =
      lpRes.status === 0 ? (lpRes.stdout || "").trim() : path.join(leanDir, ".lake", "build", "lib", "lean");
    const envWithPath = minimalEnv({
      LEAN_PATH: `${tmpDir}${path.delimiter}${baseLeanPath}`,
    });

    // Pass 0 (when frozen statement exists): mirror trusted base package .oleans into tmpDir
    // so Lean's top-level package search sees BOTH trusted Core.olean AND freshly compiled stmtOlean.
    let stmtMod = null;
    if (realStmtFile) {
      const relFromLean = path.relative(leanDir, realStmtFile);
      if (!relFromLean.startsWith("..") && relFromLean.endsWith(".lean")) {
        stmtMod = relFromLean.slice(0, -5).split(path.sep).join(".");
        const topPkg = stmtMod.split(".")[0];
        const lakeLibDir = path.join(leanDir, ".lake", "build", "lib", "lean");
        const srcPkgDir = path.join(lakeLibDir, topPkg);
        const dstPkgDir = path.join(tmpDir, topPkg);
        if (fs.existsSync(srcPkgDir)) {
          fs.cpSync(srcPkgDir, dstPkgDir, { recursive: true });
        }
        const srcPkgOlean = path.join(lakeLibDir, `${topPkg}.olean`);
        if (fs.existsSync(srcPkgOlean)) {
          fs.copyFileSync(srcPkgOlean, path.join(tmpDir, `${topPkg}.olean`));
        }
        const stmtOlean = path.join(tmpDir, relFromLean.slice(0, -5) + ".olean");
        fs.mkdirSync(path.dirname(stmtOlean), { recursive: true });
        const pass0 = spawnSync(leanBin, ["-o", stmtOlean, realStmtFile], {
          encoding: "utf8",
          cwd: leanDir,
          env: envWithPath,
          timeout: 90000,
        });
        if (pass0.status !== 0 || !fs.existsSync(stmtOlean)) {
          return fail(`Trusted frozen statement failed to compile: ${opts.statementFile}`, {
            file: relFile,
            file_hash: fileHash,
            statement_hash: stmtHash,
            output: ((pass0.stdout || "") + "\n" + (pass0.stderr || "")).trim().slice(0, 4000),
          });
        }
      } else {
        return fail(`Frozen statement must reside inside ${cfg.lean_dir}`, {
          file: relFile,
          file_hash: fileHash,
          statement_hash: stmtHash,
        });
      }
    }

    // Pass 1: Compile submitted Lean file cleanly into isolated .olean
    const pass1 = spawnSync(leanBin, ["-o", claimOlean, realFile], {
      encoding: "utf8",
      cwd: leanDir,
      env: envWithPath,
      timeout: 90000,
    });
    if (pass1.status !== 0 || !fs.existsSync(claimOlean)) {
      return fail("Lean 4 kernel typecheck failed", {
        file: relFile,
        file_hash: fileHash,
        statement_hash: stmtHash,
        output: ((pass1.stdout || "") + "\n" + (pass1.stderr || "")).trim().slice(0, 4000),
      });
    }

    // Pass 2: Isolated Judge metaprogram importing BOTH trusted stmtMod (if present) and claimMod
    const escapedResultPath = JSON.stringify(resultJsonPath);
    const stmtImport = stmtMod ? `import ${stmtMod}\n` : "";
    const stmtCheckBlock = stmtMod
      ? `
      let stmtTarget : Name := \`${stmtDef}
      let expectedStmtMod : Name := \`${stmtMod}
      let stmtMatch := match env.find? stmtTarget with
        | some (.defnInfo c) =>
            let stmtModOk := match env.getModuleIdxFor? stmtTarget with
              | some idx => (env.header.moduleNames[idx]!).toString == expectedStmtMod.toString
              | none => false
            let levelsOk := c.levelParams.isEmpty && info.levelParams.isEmpty
            let isProp := c.type == Expr.sort Level.zero
            let wantExpr := ${
              kind === "refutation"
                ? `Expr.app (Expr.const \`Not []) (Expr.const stmtTarget [])`
                : `Expr.const stmtTarget []`
            }
            let exactMatch := info.type == wantExpr
            let bodyMatch := info.type == (${
              kind === "refutation" ? `Expr.app (Expr.const \`Not []) c.value` : `c.value`
            })
            stmtModOk && levelsOk && isProp && (exactMatch || bodyMatch)
        | _ => false`
      : `      let stmtMatch := true`;

    const auditProgram = `import Lean.Util.CollectAxioms
import Lean.Meta.Basic
import Lean.Data.Json
${stmtImport}import ${claimMod}

open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let target : Name := \`${theoremName}
  let expectedMod : Name := \`${claimMod}
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
      let levelsEmpty := info.levelParams.isEmpty
${stmtCheckBlock}
      let axioms ← Lean.collectAxioms target
      let fmt ← ppExpr info.type
      let j := Json.mkObj [
        ("found", Json.bool true),
        ("isTheorem", Json.bool isThm),
        ("inSubmittedMod", Json.bool inSubmittedMod),
        ("levelsEmpty", Json.bool levelsEmpty),
        ("statementMatched", Json.bool stmtMatch),
        ("declaredModule", Json.str modNameStr),
        ("axioms", Json.arr (axioms.map (fun n => Json.str n.toString))),
        ("type", Json.str fmt.pretty)
      ]
      IO.FS.writeFile ${escapedResultPath} j.compress
`;
    fs.writeFileSync(auditLeanPath, auditProgram, "utf8");

    const pass2 = spawnSync(leanBin, [auditLeanPath], {
      encoding: "utf8",
      cwd: leanDir,
      env: envWithPath,
      timeout: 90000,
    });
    if (pass2.status !== 0 || !fs.existsSync(resultJsonPath)) {
      return fail(`Judge kernel audit failed for ${theoremName} (possible duplicate/shadowed declaration)`, {
        file: relFile,
        file_hash: fileHash,
        statement_hash: stmtHash,
        output: ((pass2.stdout || "") + "\n" + (pass2.stderr || "")).trim().slice(0, 4000),
      });
    }

    const audit = JSON.parse(fs.readFileSync(resultJsonPath, "utf8"));
    if (!audit.found) return fail(`Theorem \`${theoremName}\` not found in compiled environment`, { file: relFile, file_hash: fileHash });
    if (!audit.inSubmittedMod) {
      return fail(`Rejected: \`${theoremName}\` was NOT declared in submitted file (declared in \`${audit.declaredModule || "unknown"}\`)`, {
        file: relFile,
        file_hash: fileHash,
      });
    }
    if (!audit.isTheorem) {
      return fail(`Rejected: \`${theoremName}\` is not a theorem (ConstantInfo.thmInfo required)`, {
        file: relFile,
        file_hash: fileHash,
      });
    }
    if (stmtMod && !audit.statementMatched) {
      return fail(
        `Rejected by frozen-statement gate: \`${theoremName}\` does not syntactically match ${kind === "refutation" ? "¬ " : ""}\`${stmtDef}\` (no universe params, Prop required)`,
        { file: relFile, file_hash: fileHash, statement_hash: stmtHash }
      );
    }

    const axioms = Array.isArray(audit.axioms) ? audit.axioms : [];
    const disallowed = axioms.filter((a) => !allowedAxioms.has(a));
    if (disallowed.length > 0) {
      return fail(`Disallowed kernel axioms detected: ${disallowed.join(", ")}`, {
        file: relFile,
        file_hash: fileHash,
        axioms,
      });
    }

    return {
      ok: true,
      judge: "lean4",
      reason: stmtMod
        ? `Verified by Lean 4 kernel & exact frozen-statement match against ${stmtDef} (zero sorry, standard axioms only)`
        : "Verified by isolated Lean 4 kernel metaprogram (zero sorry, standard axioms only, module-bound)",
      file: relFile,
      theorem: theoremName,
      signature: `${theoremName} :\n  ${audit.type}`,
      axioms,
      duration_ms: Date.now() - started,
      lean_version: leanVersion,
      file_hash: fileHash,
      core_hash: coreHash,
      statement_frozen: Boolean(stmtMod),
      statement_hash: stmtHash,
      output: (pass1.stdout || "").trim().slice(0, 2000),
    };
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {}
  }
}
