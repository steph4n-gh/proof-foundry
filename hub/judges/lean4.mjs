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
 * 6. A parse-only Init environment checks the submitted snapshot before compilation. The compiled
 *    module's imports, declarations, target dependencies and kernel axioms are audited independently.
 *    Only Lean's generated constructor-index implementation may be unsafe, never a kernel dependency
 *    of the target. These checks enforce a language policy; they do not provide an OS sandbox.
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import crypto from "node:crypto";
import { isUtf8 } from "node:buffer";
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

export function validateCanonicalNatScore(raw) {
  const s = typeof raw === "number" && Number.isSafeInteger(raw) && raw >= 0 ? String(raw) : String(raw ?? "");
  return /^(0|[1-9][0-9]{0,8})$/.test(s) ? s : null;
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

const importPolicy = `
private def allowedImport (target : String) (mod : Lean.Name) : Bool :=
  (["Init", "Std", target].filter (!·.isEmpty)).any fun root => root.toName.isPrefixOf mod
`;

export const compiledModulePolicy = `${importPolicy}
open Lean in
private def generatedCtorIndex (env : Environment) (owner : ModuleIdx) (decl : ConstantInfo) : Bool := Id.run do
  let .defnInfo defn := decl | return false
  let .str (.str parent "ctorIdx") "_impl" := defn.name | return false
  let some (.inductInfo ind) := env.find? parent | return false
  let body := defn.value.getLambdaBody
  return env.getModuleIdxFor? parent == some owner && ind.numCtors > 1 &&
    Compiler.getImplementedBy? env (parent.str "ctorIdx") == some defn.name &&
    body.isAppOfArity \`\`getObjTagNat 2 && body.appArg! == .bvar 0

open Lean in
private partial def dependencyError (env : Environment) (owner : ModuleIdx) (target : Name) : String := Id.run do
  let mut work := [target]
  let mut seen : NameSet := {}
  while let name :: rest := work do
    work := rest
    if seen.contains name || env.getModuleIdxFor? name != some owner then continue
    seen := seen.insert name
    let some decl := env.checked.get.find? name | return s!"missing dependency {name}"
    if decl.isUnsafe || (decl matches .axiomInfo _ | .opaqueInfo _) then return s!"disallowed dependency {name}"
    for dep in decl.getUsedConstantsAsSet do work := dep :: work
    if let .recInfo recursor := decl then
      for rule in recursor.rules do work := rule.rhs.getUsedConstants.toList ++ work
  return ""

open Lean in
private def modulePolicyError (env : Environment) (mod target : Name) (root : String) : String := Id.run do
  let some idx := env.getModuleIdx? mod | return "missing submitted module"
  let data := env.header.moduleData[idx]!
  for imp in data.imports do
    unless allowedImport root imp.module do return s!"disallowed import {imp.module}"
  if data.constNames.size != data.constants.size then return "invalid constant table"
  for name in data.constNames, decl in data.constants do
    if decl.name != name then return "invalid constant name"
    if (decl matches .axiomInfo _ | .opaqueInfo _) || (decl.isUnsafe && !generatedCtorIndex env idx decl) then
      return s!"disallowed constant {name}"
  return dependencyError env idx target
`;

const syntaxAuditor = `import Lean.Elab.Import
open Lean Parser
${importPolicy}
private def forbidden := ["sorry", "admit", "axiom", "opaque", "unsafe", "native_decide",
  "#eval", "#exit", "#print", "run_cmd", "run_tac", "run_meta", "by_elab", "elab", "elab_rules",
  "macro", "macro_rules", "syntax", "syntax_cat", "declare_syntax_cat", "simproc", "dsimproc",
  "simproc_decl", "dsimproc_decl", "initialize", "builtin_initialize", "local_elab", "command_elab",
  "term_elab", "tactic_elab", "skipKernelTC", "modifyEnv"]

private def forbiddenAttrs := ["extern", "implemented_by", "tactic", "init", "delab", "app_unexpander"]

private partial def inspectSyntax (stx : Syntax) (inAttr := false) : Except String Unit := do
  let kind := stx.getKind
  let attr := inAttr || kind == \`\`Term.attrInstance
  let check (word : String) := do
    if forbidden.contains word || word.startsWith "#eval" || word.startsWith "#print" || (attr && forbiddenAttrs.contains word) then
      throw s!"forbidden {word}"
  match stx with
  | .missing => throw "missing syntax"
  | .atom _ word => check word
  | .ident _ _ id _ => for part in id.components do check part.toString
  | .node _ (.str _ name) args =>
    check name
    if args[0]?.any (·.getAtomVal == "set_option") then
      let opt := stx[1].getId.toString
      unless ([${[...ALLOWED_SET_OPTIONS].map(x => JSON.stringify(x)).join(', ')}] : List String).contains opt do
        throw s!"disallowed set_option {opt}"
    for child in args do inspectSyntax child attr
  | .node _ _ args => for child in args do inspectSyntax child attr

private def audit (file target : String) : IO (Except String Unit) := do
  let input := mkInputContext (← IO.FS.readFile file) file
  let (header, initial, errors) ← parseHeader input
  if errors.hasErrors then return .error "header parse error"
  for imp in Elab.HeaderSyntax.imports header do
    unless allowedImport target imp.module do return .error s!"disallowed import {imp.module}"
  let env ← importModules #[{ module := \`Init }] {} (loadExts := true)
  let mut cursor := initial
  repeat
    let (cmd, next, msgs) := parseCommand input { env, options := {} } cursor {}
    if msgs.hasErrors || next.recovering then
      return .error s!"command parse error at {input.fileMap.toPosition cursor.pos}"
    if cmd.isOfKind \`\`Command.eoi then return .ok ()
    if let .error reason := inspectSyntax cmd then return .error reason
    if isTerminalCommand cmd || next.pos <= cursor.pos then return .error "unexpected command terminator"
    cursor := next
  return .error "missing end of input"

unsafe def main (args : List String) : IO Unit := do
  let [source, target, result] := args | throw (IO.userError "invalid judge arguments")
  enableInitializersExecution
  let verdict ← audit source target
  let json := match verdict with
    | .ok () => Json.mkObj [("ok", toJson true)]
    | .error reason => Json.mkObj [("ok", toJson false), ("reason", toJson reason)]
  IO.FS.writeFile result json.compress
`;

function auditSnapshot(source, lakeTarget, leanDir, tmpDir) {
  const script = path.join(tmpDir, "JudgeSyntax.lean");
  const result = path.join(tmpDir, "syntax.json");
  fs.writeFileSync(script, syntaxAuditor);
  const run = spawnSync(getLeanBin(), ["--run", script, source, lakeTarget || "", result], {
    cwd: leanDir, env: minimalEnv(), encoding: "utf8", timeout: 30000,
  });
  if (run.status !== 0 || !fs.existsSync(result)) {
    return { ok: false, reason: "syntax auditor failed", output: `${run.stdout || ""}${run.stderr || run.error || ""}`.slice(0, 4000) };
  }
  return JSON.parse(fs.readFileSync(result, "utf8"));
}

export function auditLeanSyntax(source, judgeConfig = DEFAULT_JUDGE_CONFIG) {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "fleet-lean-syntax-"));
  try {
    return auditSnapshot(path.resolve(source), judgeConfig.lake_target, path.resolve(ROOT, judgeConfig.lean_dir), tmpDir);
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
}

export function checkLeanProof(relOrAbsFile, theoremName, opts = {}) {
  const cfg = { ...DEFAULT_JUDGE_CONFIG, ...(opts.judgeConfig || {}) };
  const leanDir = path.resolve(ROOT, cfg.lean_dir);
  const coreFile = cfg.core_file ? path.resolve(ROOT, cfg.core_file) : null;
  const coreOlean = cfg.core_olean ? path.resolve(ROOT, cfg.core_olean) : null;
  const allowedDirs = (cfg.allowed_dirs || []).map((d) => path.resolve(ROOT, d));
  const allowedAxioms = new Set(cfg.allowed_axioms || ["propext", "Classical.choice", "Quot.sound"]);
  const allowedKinds = new Set(["proof", "refutation", "record", "record_bound"]);
  const kind = allowedKinds.has(opts.kind) ? opts.kind : "proof";
  const isRecordKind = kind === "record" || kind === "record_bound";
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
    score: null,
    output: "",
    ...extra,
  });

  if (!validateLeanIdentifier(theoremName)) {
    return fail(`Invalid Lean theorem identifier: ${theoremName}`);
  }

  let scoreStr = null;
  if (isRecordKind) {
    scoreStr = validateCanonicalNatScore(opts.expectedScore);
    if (scoreStr === null) {
      return fail(`Invalid canonical Nat score for ${kind}: ${JSON.stringify(opts.expectedScore)}`);
    }
    if (!opts.statementFile || !opts.statementDef) {
      return fail(`Record kind "${kind}" requires a frozen statementFile and statementDef`);
    }
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

  const sourceBytes = fs.readFileSync(realFile);
  const fileHash = crypto.createHash("sha256").update(sourceBytes).digest("hex");
  if (!isUtf8(sourceBytes)) return fail("Invalid UTF-8 source", { file: relFile, file_hash: fileHash });

  const lex = stripLeanCommentsAndStrings(sourceBytes.toString("utf8"));
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

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "fleet-lean4-judge-"));
  const salt = `${process.pid}_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`;
  const claimMod = `FleetJudgeTmp.Sub_${salt}`;
  const oleanDir = path.join(tmpDir, "FleetJudgeTmp");
  const claimOlean = path.join(oleanDir, `Sub_${salt}.olean`);
  const snapshot = path.join(oleanDir, `Sub_${salt}.lean`);
  const auditLeanPath = path.join(tmpDir, "JudgeAudit.lean");
  const resultJsonPath = path.join(tmpDir, "result.json");

  try {
    fs.mkdirSync(oleanDir);
    fs.writeFileSync(snapshot, sourceBytes);
    const ast = auditSnapshot(snapshot, cfg.lake_target, leanDir, tmpDir);
    if (ast.ok !== true) return fail(`Rejected by Lean AST gate: ${ast.reason}`, { file: relFile, file_hash: fileHash, output: ast.output || "" });

    const coreBuilt = coreOlean && coreFile && fs.existsSync(coreOlean) && fs.existsSync(coreFile)
      && fs.statSync(coreOlean).mtimeMs >= fs.statSync(coreFile).mtimeMs;
    if (!coreBuilt && cfg.lake_target) {
      const b = spawnSync(lakeBin, ["build", cfg.lake_target], { encoding: "utf8", cwd: leanDir, env: minimalEnv() });
      if (b.status !== 0) {
        return fail(`Core library \`lake build ${cfg.lake_target}\` failed`, {
          file: relFile,
          file_hash: fileHash,
          output: ((b.stdout || "") + "\n" + (b.stderr || "")).trim().slice(0, 4000),
        });
      }
    }

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
    const pass1 = spawnSync(leanBin, ["-R", tmpDir, "-o", claimOlean, snapshot], {
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
    let stmtCheckBlock;
    if (stmtMod && isRecordKind) {
      // Exact canonical Nat-literal kernel Expr check (Opus 5.5 + Astra 6.2 verified in Lean 4.36.0):
      // mkNatLit n constructs @OfNat.ofNat.{0} Nat (.lit (.natVal n)) (instOfNatNat (.lit (.natVal n))),
      // blocking OfNat instance spoofing (OfNat 58 <61>), Nat.succ, bodyMatch, and isDefEq DoS.
      stmtCheckBlock = `
      let stmtTarget : Name := \`${stmtDef}
      let expectedStmtMod : Name := \`${stmtMod}
      let stmtMatch := match env.find? stmtTarget with
        | some (.defnInfo c) =>
            let stmtModOk := match env.getModuleIdxFor? stmtTarget with
              | some idx => (env.header.moduleNames[idx]!).toString == expectedStmtMod.toString
              | none => false
            let levelsOk := c.levelParams.isEmpty && info.levelParams.isEmpty
            let argOK := match c.type with
              | .forallE _ dom cod .default =>
                  dom.equal (mkConst \`\`Nat) && cod.equal (.sort .zero)
              | _ => false
            let pos := mkApp (mkConst stmtTarget) (mkNatLit ${scoreStr})
            let wantExpr := ${kind === "record_bound" ? `mkApp (mkConst \`\`Not) pos` : `pos`}
            stmtModOk && levelsOk && argOK && info.type.equal wantExpr
        | _ => false`;
    } else if (stmtMod) {
      stmtCheckBlock = `
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
        | _ => false`;
    } else {
      stmtCheckBlock = `      let stmtMatch := true`;
    }

    const auditProgram = `import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Meta.Basic
import Lean.Data.Json
${stmtImport}import ${claimMod}
${compiledModulePolicy}

open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let target : Name := \`${theoremName}
  let expectedMod : Name := \`${claimMod}
  let envError := modulePolicyError env expectedMod target ${JSON.stringify(cfg.lake_target || "")}
  unless envError.isEmpty do
    IO.FS.writeFile ${escapedResultPath} (Json.mkObj [("envError", toJson envError)]).compress
    return
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
      let axioms ← if stmtMatch && isThm && inSubmittedMod then Lean.collectAxioms target else pure #[]
      let typeStr ← if stmtMatch && isThm && inSubmittedMod then do
        let fmt ← ppExpr info.type
        pure fmt.pretty
      else
        pure ""
      let j := Json.mkObj [
        ("found", Json.bool true),
        ("envAudited", Json.bool true),
        ("isTheorem", Json.bool isThm),
        ("inSubmittedMod", Json.bool inSubmittedMod),
        ("levelsEmpty", Json.bool levelsEmpty),
        ("statementMatched", Json.bool stmtMatch),
        ("declaredModule", Json.str modNameStr),
        ("axioms", Json.arr (axioms.map (fun n => Json.str n.toString))),
        ("type", Json.str typeStr)${isRecordKind ? `,\n        ("score", Json.str ${JSON.stringify(scoreStr)})` : ""}
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
    if (audit.envError) return fail(`Rejected by compiled environment audit: ${audit.envError}`, { file: relFile, file_hash: fileHash });
    if (!audit.found) return fail(`Theorem \`${theoremName}\` not found in compiled environment`, { file: relFile, file_hash: fileHash });
    if (audit.envAudited !== true) return fail("Missing compiled environment audit", { file: relFile, file_hash: fileHash });
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
      const targetDesc = isRecordKind
        ? `${kind === "record_bound" ? "¬ " : ""}\`${stmtDef} ${scoreStr}\` (canonical Nat literal, Nat → Prop required)`
        : `${kind === "refutation" ? "¬ " : ""}\`${stmtDef}\` (no universe params, Prop required)`;
      return fail(
        `Rejected by frozen-statement gate: \`${theoremName}\` does not syntactically match ${targetDesc}`,
        { file: relFile, file_hash: fileHash, statement_hash: stmtHash, score: isRecordKind ? Number(scoreStr) : null }
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
      ast_audited: true,
      env_audited: true,
      reason: isRecordKind
        ? `Verified by Lean 4 kernel & exact canonical match against ${kind === "record_bound" ? "¬ " : ""}${stmtDef} ${scoreStr} (zero sorry, standard axioms only)`
        : stmtMod
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
      score: isRecordKind ? Number(audit.score ?? scoreStr) : null,
      output: (pass1.stdout || "").trim().slice(0, 2000),
    };
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {}
  }
}
