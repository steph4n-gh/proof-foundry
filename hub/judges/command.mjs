#!/usr/bin/env node
/**
 * hub/judges/command.mjs — Pluggable Deterministic Command / Test-Harness Judge.
 *
 * Enables non-Lean missions (algorithm verification, Z3/SMT, TLA+, Rust/Python property tests,
 * fuzzers, benchmark harnesses) to share the exact same fleet, Graveyard, Audit Desk, and GitHub CI.
 *
 * Contract:
 * - Mission configures `judge.harness` (a Judge-owned verifier script/binary) and `judge.allowed_dirs`.
 * - Judge verifies canonical path containment + hashes both submitted artifact and Judge harness.
 * - Executes `judge.command` (array of argv tokens, e.g. ["node", "missions/.../judge/verify.mjs"])
 *   passing `--artifact <realFile> --target <target> --result <resultJsonPath>` (zero shell injection!).
 * - Reads structured verdict JSON from Judge-owned `resultJsonPath` (never scrapes untrusted stdout!).
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import crypto from "node:crypto";
import { spawnSync } from "node:child_process";
import { validateCanonicalNatScore } from "./lean4.mjs";

const ROOT = path.resolve(import.meta.dirname, "../..");

function sha256File(p) {
  if (!p || !fs.existsSync(p)) return null;
  return crypto.createHash("sha256").update(fs.readFileSync(p)).digest("hex");
}

export function checkCommandArtifact(relOrAbsFile, targetName, opts = {}) {
  const cfg = opts.judgeConfig || {};
  const started = Date.now();
  const judgeLabel = cfg.label || "Command Judge";
  const allowedDirs = (cfg.allowed_dirs || []).map((d) => path.resolve(ROOT, d));
  const harnessFile = cfg.harness_file ? path.resolve(ROOT, cfg.harness_file) : null;
  const coreHash = sha256File(harnessFile);
  const kind = opts.kind || "proof";
  const isRecordKind = kind === "record" || kind === "record_bound";
  const specAbs = opts.statementFile ? path.resolve(ROOT, opts.statementFile) : null;
  const statementHash = specAbs ? sha256File(specAbs) : null;

  if (kind === "record_bound") {
    return {
      ok: false,
      judge: "command",
      reason: "Command Judge does not support impossibility bound proofs (record_bound)",
      file: relOrAbsFile,
      theorem: targetName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: judgeLabel,
      file_hash: null,
      core_hash: coreHash,
      statement_frozen: false,
      statement_hash: statementHash,
      score: null,
      output: "",
    };
  }

  let scoreStr = null;
  if (kind === "record") {
    scoreStr = validateCanonicalNatScore(opts.expectedScore);
    if (scoreStr === null) {
      return {
        ok: false,
        judge: "command",
        reason: `Invalid canonical Nat score for record: ${JSON.stringify(opts.expectedScore)}`,
        file: relOrAbsFile,
        theorem: targetName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: judgeLabel,
        file_hash: null,
        core_hash: coreHash,
        statement_frozen: false,
        statement_hash: statementHash,
        score: null,
        output: "",
      };
    }
    if (!specAbs || !statementHash) {
      return {
        ok: false,
        judge: "command",
        reason: `Missing frozen spec file for Command-Judge record hunt: ${opts.statementFile || "(none)"}`,
        file: relOrAbsFile,
        theorem: targetName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: judgeLabel,
        file_hash: null,
        core_hash: coreHash,
        statement_frozen: false,
        statement_hash: null,
        score: null,
        output: "",
      };
    }
  }

  const absFile = path.isAbsolute(relOrAbsFile)
    ? relOrAbsFile
    : path.resolve(ROOT, relOrAbsFile);
  if (!fs.existsSync(absFile)) {
    return {
      ok: false,
      judge: "command",
      reason: `Artifact not found: ${relOrAbsFile}`,
      file: relOrAbsFile,
      theorem: targetName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: judgeLabel,
      file_hash: null,
      core_hash: coreHash,
      output: "",
    };
  }

  if (fs.lstatSync(absFile).isSymbolicLink()) {
    return {
      ok: false,
      judge: "command",
      reason: `Rejected by path gate: symlinks are forbidden (${relOrAbsFile})`,
      file: relOrAbsFile,
      theorem: targetName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: judgeLabel,
      file_hash: null,
      core_hash: coreHash,
      output: "",
    };
  }

  const realFile = fs.realpathSync(absFile);
  const relFile = path.relative(ROOT, realFile);
  if (!opts.allowTempForTests && allowedDirs.length > 0) {
    const inside = allowedDirs.some((dir) => {
      try {
        const rd = fs.realpathSync(dir);
        return realFile.startsWith(rd + path.sep);
      } catch {
        return false;
      }
    });
    if (!inside) {
      return {
        ok: false,
        judge: "command",
        reason: `Rejected by path gate: artifact must reside inside ${cfg.allowed_dirs.join(" or ")}`,
        file: relFile,
        theorem: targetName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: judgeLabel,
        file_hash: null,
        core_hash: coreHash,
        output: "",
      };
    }
  }

  const fileHash = sha256File(realFile);
  const cmd = cfg.command;
  if (!Array.isArray(cmd) || cmd.length === 0) {
    return {
      ok: false,
      judge: "command",
      reason: "Mission judge.command is not configured",
      file: relFile,
      theorem: targetName,
      axioms: [],
      duration_ms: Date.now() - started,
      lean_version: judgeLabel,
      file_hash: fileHash,
      core_hash: coreHash,
      output: "",
    };
  }

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "fleet-cmd-judge-"));
  const resultJsonPath = path.join(tmpDir, "result.json");
  try {
    const [bin, ...baseArgs] = cmd;
    const args = [
      ...baseArgs,
      "--artifact", realFile,
      "--target", String(targetName || ""),
      "--result", resultJsonPath,
      "--kind", String(kind),
      ...(scoreStr !== null ? ["--score", scoreStr] : []),
      ...(specAbs ? ["--spec", specAbs] : []),
    ];
    const run = spawnSync(bin, args, {
      encoding: "utf8",
      cwd: ROOT,
      timeout: Number(cfg.timeout_ms || 60000),
      env: {
        PATH: process.env.PATH || "/usr/local/bin:/usr/bin:/bin",
        HOME: process.env.HOME || os.homedir(),
        TMPDIR: os.tmpdir(),
      },
    });

    if (!fs.existsSync(resultJsonPath)) {
      return {
        ok: false,
        judge: "command",
        reason: `Judge harness exited with status ${run.status}`,
        file: relFile,
        theorem: targetName,
        axioms: [],
        duration_ms: Date.now() - started,
        lean_version: judgeLabel,
        file_hash: fileHash,
        core_hash: coreHash,
        output: ((run.stdout || "") + "\n" + (run.stderr || "")).trim().slice(0, 4000),
      };
    }

    const parsed = JSON.parse(fs.readFileSync(resultJsonPath, "utf8"));
    let finalOk = run.status === 0 && Boolean(parsed.ok);
    let reason = parsed.reason || (finalOk ? `Verified by ${judgeLabel}` : `Rejected by ${judgeLabel} (exit=${run.status})`);
    if (isRecordKind && finalOk && Number(parsed.score) !== Number(scoreStr)) {
      finalOk = false;
      reason = `Harness score mismatch: got ${parsed.score}, expected ${scoreStr}`;
    }
    return {
      ok: finalOk,
      judge: "command",
      reason,
      file: relFile,
      theorem: targetName,
      signature: parsed.signature || `${targetName} (${judgeLabel})`,
      axioms: Array.isArray(parsed.checks) ? parsed.checks : [],
      duration_ms: Date.now() - started,
      lean_version: parsed.engine || judgeLabel,
      file_hash: fileHash,
      core_hash: coreHash,
      statement_frozen: Boolean(isRecordKind && statementHash),
      statement_hash: isRecordKind ? statementHash : null,
      score: isRecordKind ? Number(scoreStr) : null,
      output: String(parsed.summary || run.stdout || "").trim().slice(0, 2000),
    };
  } finally {
    try {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    } catch {}
  }
}
