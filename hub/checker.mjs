#!/usr/bin/env node
/**
 * hub/checker.mjs — Backwards-compatible wrapper over hub/judges/lean4.mjs.
 */
import { checkLeanProof, stripLeanCommentsAndStrings, getLeanVersion, sha256File } from "./judges/lean4.mjs";

export { checkLeanProof, stripLeanCommentsAndStrings, getLeanVersion, sha256File };

if (import.meta.url === `file://${process.argv[1]}`) {
  const [, , file, theorem] = process.argv;
  if (!file || !theorem) {
    console.error("Usage: node hub/checker.mjs <lean-file> <Theorem.Name>");
    process.exit(2);
  }
  const result = checkLeanProof(file, theorem);
  console.log(JSON.stringify(result, null, 2));
  process.exit(result.ok ? 0 : 1);
}
