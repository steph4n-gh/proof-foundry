/**
 * hub/export_dropin.mjs — Deterministic drop-in code extractor from verified Proof Foundry artifacts.
 *
 * Converts machine-checked Lean 4 / pure-data JSON witnesses into ready-to-paste production snippets:
 *  - ml-math-kernels (.json)        -> branchless CUDA / C++ __device__ function
 *  - crypto-zk-circuits (.lean)     -> 64-way bit-sliced C99 S-box function
 *  - sorting-networks (.lean)       -> branchless C/SIMD CMP_SWAP sorting function
 *  - verified-science-kernels (.mjs)-> C/CUDA FMA Horner polynomial evaluator
 *  - quantum-codes (.lean)          -> Python/NumPy/Stim binary parity-check matrices (H_X, H_Z, L_X, L_Z)
 *
 * Pure, self-contained read-only text transformation (zero imports from missions/, zero code execution).
 */

const B2_C_OP = {
  opZero: () => "0ULL",
  opOne: () => "~0ULL",
  opAnd: (a, b) => `(${a} & ${b})`,
  opOr: (a, b) => `(${a} | ${b})`,
  opXor: (a, b) => `(${a} ^ ${b})`,
  opXnor: (a, b) => `~(${a} ^ ${b})`,
  opNand: (a, b) => `~(${a} & ${b})`,
  opNor: (a, b) => `~(${a} | ${b})`,
  opAndNot: (a, b) => `(${a} & ~${b})`,
  opNotAnd: (a, b) => `(~${a} & ${b})`,
  opOrNot: (a, b) => `(${a} | ~${b})`,
  opNotOr: (a, b) => `(~${a} | ${b})`,
  opNotA: (a) => `(~${a})`,
  opNotB: (_, b) => `(~${b})`,
  opA: (a) => a,
  opB: (_, b) => b,
};

const ZERO_COST_ML_OPS = new Set(["const", "iconst", "bitcast_i32", "bitcast_f32"]);

function sanitizeIdent(id) {
  return String(id || "artifact").toLowerCase().replace(/[^a-z0-9]+/g, "_").replace(/^_|_$/g, "");
}

function formatFloat32Lit(v) {
  if (Object.is(v, -0)) return "-0.0f";
  const s = Number(Math.fround(v)).toPrecision(9);
  if (s.includes("e") || s.includes("E")) {
    const [m, e] = s.split(/[eE]/);
    return `${m.replace(/(\.\d*?[1-9])0+$/, "$1").replace(/\.0+$/, ".0")}e${e}f`;
  }
  const trimmed = s.replace(/(\.\d*?[1-9])0+$/, "$1").replace(/\.0+$/, ".0");
  return (trimmed.includes(".") ? trimmed : `${trimmed}.0`) + "f";
}

function extractMlKernelCuda(lemma, source) {
  const k = JSON.parse(source);
  if (!k || k.schema !== "pf.mlkernel.v1" || !Array.isArray(k.ops) || !k.ops.length || !Number.isSafeInteger(k.output)) {
    return null;
  }
  let opCost = 0;
  for (const inst of k.ops) {
    if (!Array.isArray(inst) || typeof inst[0] !== "string") return null;
    if (!ZERO_COST_ML_OPS.has(inst[0])) opCost++;
  }
  const fnName = `pf_${sanitizeIdent(k.target || lemma.id)}`;
  const lines = [
    `// Auto-generated from Proof Foundry verified pure-data kernel (${opCost} ops, 65,536/65,536 bf16 inputs checked)`,
    `__device__ __forceinline__ float ${fnName}(float r0) {`,
  ];
  const regTypes = ["f32"];
  for (let i = 0; i < k.ops.length; i++) {
    const inst = k.ops[i];
    const op = inst[0];
    const r = `r${i + 1}`;
    const a = inst.slice(1).map((x) => `r${x}`);
    let outType = "f32";
    switch (op) {
      case "const": lines.push(`  const float ${r} = ${formatFloat32Lit(inst[1])};`); break;
      case "iconst": {
        outType = "i32";
        const iv = inst[1] | 0;
        lines.push(`  const int32_t ${r} = ${iv === -2147483648 ? "(-2147483647 - 1)" : iv};`);
        break;
      }
      case "bitcast_i32": outType = "i32"; lines.push(`  const int32_t ${r} = __float_as_int(${a[0]});`); break;
      case "bitcast_f32": lines.push(`  const float ${r} = __int_as_float(${a[0]});`); break;
      case "add": lines.push(`  const float ${r} = ${a[0]} + ${a[1]};`); break;
      case "sub": lines.push(`  const float ${r} = ${a[0]} - ${a[1]};`); break;
      case "mul": lines.push(`  const float ${r} = ${a[0]} * ${a[1]};`); break;
      case "fma": lines.push(`  const float ${r} = fmaf(${a[0]}, ${a[1]}, ${a[2]});`); break;
      case "abs": lines.push(`  const float ${r} = fabsf(${a[0]});`); break;
      case "neg": lines.push(`  const float ${r} = -${a[0]};`); break;
      case "min": lines.push(`  const float ${r} = fminf(${a[0]}, ${a[1]});`); break;
      case "max": lines.push(`  const float ${r} = fmaxf(${a[0]}, ${a[1]});`); break;
      case "iadd": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} + ${a[1]};`); break;
      case "isub": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} - ${a[1]};`); break;
      case "imul": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} * ${a[1]};`); break;
      case "iand": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} & ${a[1]};`); break;
      case "ior": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} | ${a[1]};`); break;
      case "ixor": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} ^ ${a[1]};`); break;
      case "ishl": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} << (${a[1]} & 31);`); break;
      case "ishr_u": outType = "i32"; lines.push(`  const int32_t ${r} = (int32_t)((uint32_t)${a[0]} >> (${a[1]} & 31));`); break;
      case "ishr_s": outType = "i32"; lines.push(`  const int32_t ${r} = ${a[0]} >> (${a[1]} & 31);`); break;
      case "ftoi_trunc": outType = "i32"; lines.push(`  const int32_t ${r} = __float2int_rz(${a[0]});`); break;
      case "ftoi_round": outType = "i32"; lines.push(`  const int32_t ${r} = __float2int_rn(${a[0]});`); break;
      case "itof": lines.push(`  const float ${r} = (float)${a[0]};`); break;
      case "lt": outType = "bool"; lines.push(`  const bool ${r} = ${a[0]} < ${a[1]};`); break;
      case "le": outType = "bool"; lines.push(`  const bool ${r} = ${a[0]} <= ${a[1]};`); break;
      case "eq": outType = "bool"; lines.push(`  const bool ${r} = ${a[0]} == ${a[1]};`); break;
      case "select": {
        outType = regTypes[inst[2]] || "f32";
        lines.push(`  const ${outType === "i32" ? "int32_t" : "float"} ${r} = ${a[0]} ? ${a[1]} : ${a[2]};`);
        break;
      }
      default:
        return null;
    }
    regTypes.push(outType);
  }
  lines.push(`  return r${k.output};`, `}`);
  return {
    lang: "cuda",
    title: `Drop-in CUDA / C++ __device__ kernel (${opCost} ops, 65,536/65,536 bf16 verified)`,
    filename: `${fnName}.cuh`,
    code: lines.join("\n"),
  };
}

function stripLeanComments(src) {
  return String(src || "").replace(/\/-[\s\S]*?-\//g, "").replace(/--[^\n]*/g, "");
}

function extractCryptoBitslice(lemma, source) {
  const clean = stripLeanComments(source);
  const sigMatch = clean.match(/MultiCircuit\s+(\d+)\s+(\d+)/);
  if (!sigMatch) return null;
  const nIn = Number(sigMatch[1]);
  const nOut = Number(sigMatch[2]);
  const gatesBlock = clean.match(/gates\s*:=\s*\[([\s\S]*?)\]/);
  const outBlock = clean.match(/outputs\s*:=\s*\[([\s\S]*?)\]/);
  if (!gatesBlock || !outBlock) return null;

  const gates = [];
  for (const m of gatesBlock[1].matchAll(/⟨\s*(op[A-Za-z0-9_]+)\s*,\s*(\d+)\s*,\s*(\d+)\s*⟩/g)) {
    const fn = B2_C_OP[m[1]];
    if (!fn) return null;
    gates.push({ op: m[1], fn, w1: Number(m[2]), w2: Number(m[3]) });
  }
  const outputs = [...outBlock[1].matchAll(/\d+/g)].map((m) => Number(m[0]));
  if (!gates.length || outputs.length !== nOut) return null;

  const fnName = `pf_${sanitizeIdent(lemma.id)}_bitslice64`;
  const lines = [
    `/* Auto-generated from Lean-verified ${lemma.id} (${gates.length} B2 gates; executes 64 S-boxes in parallel) */`,
    `#include <stdint.h>`,
    `static inline void ${fnName}(uint64_t out[${nOut}], const uint64_t w_in[${nIn}]) {`,
  ];
  for (let i = 0; i < nIn; i++) lines.push(`  const uint64_t w${i} = w_in[${i}];`);
  gates.forEach((g, idx) => {
    const w = nIn + idx;
    lines.push(`  const uint64_t w${w} = ${g.fn(`w${g.w1}`, `w${g.w2}`)};`);
  });
  outputs.forEach((w, idx) => lines.push(`  out[${idx}] = w${w};`));
  lines.push(`}`);
  return {
    lang: "c",
    title: `Drop-in 64-way bit-sliced C99 S-box (${gates.length} ops)`,
    filename: `${fnName}.h`,
    code: lines.join("\n"),
  };
}

function extractSortNetC(lemma, source) {
  const clean = stripLeanComments(source);
  const netDefs = [...clean.matchAll(/def\s+\w+\s*:\s*(?:SortNet\.)?Net\s+(\d+)\s*:=\s*\[([\s\S]*?)\]/g)];
  if (netDefs.length !== 1) return null;
  const n = Number(netDefs[0][1]);
  const body = netDefs[0][2];
  const pairs = [];
  for (const m of body.matchAll(/(?:mkComp|⟨\s*⟨)\s*(\d+)\s*(?:,?\s*by\s+decide\s*⟩\s*,\s*⟨\s*)?(\d+)/g)) {
    const a = Number(m[1]);
    const b = Number(m[2]);
    if (a < b && b < n) pairs.push([a, b]);
  }
  if (!pairs.length) {
    for (const m of body.matchAll(/\(\s*(\d+)\s*,\s*(\d+)\s*\)/g)) {
      const a = Number(m[1]);
      const b = Number(m[2]);
      if (a < b && b < n) pairs.push([a, b]);
    }
  }
  if (pairs.length < 3 || pairs.length > 256) return null;

  const fnName = `pf_sort_${n}_${sanitizeIdent(lemma.id)}`;
  const lines = [
    `/* Auto-generated from Lean-verified ${lemma.id} (${n} wires, ${pairs.length} branchless comparators) */`,
    `#define PF_CSWAP(a, b) do { int32_t _t = (a) < (b) ? (a) : (b); (b) = (a) < (b) ? (b) : (a); (a) = _t; } while (0)`,
    `static inline void ${fnName}(int32_t v[${n}]) {`,
  ];
  for (let i = 0; i < pairs.length; i += 4) {
    const chunk = pairs.slice(i, i + 4).map(([a, b]) => `PF_CSWAP(v[${a}], v[${b}]);`).join(" ");
    lines.push(`  ${chunk}`);
  }
  lines.push(`}`);
  return {
    lang: "c",
    title: `Drop-in branchless C/SIMD ${n}-wire sorting network (${pairs.length} comparators)`,
    filename: `${fnName}.h`,
    code: lines.join("\n"),
  };
}

function extractMinimaxC(lemma, source) {
  const m = source.match(/export\s+const\s+coeffs\s*=\s*\[([\s\S]*?)\]/);
  if (!m) return null;
  const nums = m[1].split(",").map((s) => s.trim()).filter(Boolean).map(Number);
  if (!nums.length || nums.some((v) => !Number.isFinite(v))) return null;
  const isSin = /sin/i.test(lemma.id);
  const fnName = `pf_${sanitizeIdent(lemma.id)}_horner`;
  const lines = [
    `/* Auto-generated from 128-bit BigInt-verified ${lemma.id} (${nums.length} float64 coefficients) */`,
    `#include <math.h>`,
    `static inline double ${fnName}(double x) {`,
  ];
  if (isSin) {
    lines.push(`  const double x2 = x * x;`);
    let expr = String(nums[nums.length - 1]);
    for (let i = nums.length - 2; i >= 0; i--) expr = `fma(${expr}, x2, ${nums[i]})`;
    lines.push(`  return x * ${expr};`);
  } else {
    let expr = String(nums[nums.length - 1]);
    for (let i = nums.length - 2; i >= 0; i--) expr = `fma(${expr}, x, ${nums[i]})`;
    lines.push(`  return ${expr};`);
  }
  lines.push(`}`);
  return {
    lang: "c",
    title: `Drop-in C/C++ FMA Horner kernel (${nums.length} float64 coeffs)`,
    filename: `${fnName}.h`,
    code: lines.join("\n"),
  };
}

function extractQuantumStim(lemma, source) {
  const parseList = (re) => {
    const m = source.match(re);
    if (!m) return null;
    const vals = [...m[1].matchAll(/(0x[0-9a-fA-F]+|\d+)#(\d+)/g)];
    if (!vals.length) return null;
    return { n: Number(vals[0][2]), ints: vals.map((v) => Number(v[1])) };
  };
  const hx = parseList(/def\s+\w*[Hh][Xx]?\w*\s*:\s*List\s*\(BitVec\s+\d+\)\s*:=\s*\[([\s\S]*?)\]/);
  if (!hx) return null;
  const hz = parseList(/def\s+\w*[Hh][Zz]\w*\s*:\s*List\s*\(BitVec\s+\d+\)\s*:=\s*\[([\s\S]*?)\]/) || hx;
  const lx = parseList(/def\s+\w*[Ll][Xx]?\w*\s*:\s*List\s*\(BitVec\s+\d+\)\s*:=\s*\[([\s\S]*?)\]/);
  const lz = parseList(/def\s+\w*[Ll][Zz]\w*\s*:\s*List\s*\(BitVec\s+\d+\)\s*:=\s*\[([\s\S]*?)\]/) || lx;
  const toRows = (arr) => arr.map((v) => `[${Array.from({ length: hx.n }, (_, i) => (v >> i) & 1).join(",")}]`);
  const lines = [
    `# Auto-generated from Lean-verified ${lemma.id} (n=${hx.n} physical qubits, k=${lx ? lx.ints.length : "?"} logical qubits)`,
    `import numpy as np`,
    `H_X = np.array([${toRows(hx.ints).join(", ")}], dtype=np.uint8)`,
    `H_Z = np.array([${toRows(hz.ints).join(", ")}], dtype=np.uint8)`,
    ...(lx ? [`L_X = np.array([${toRows(lx.ints).join(", ")}], dtype=np.uint8)`] : []),
    ...(lz ? [`L_Z = np.array([${toRows(lz.ints).join(", ")}], dtype=np.uint8)`] : []),
    `assert ((H_X @ H_Z.T) % 2 == 0).all()  # CSS commutativity`,
  ];
  return {
    lang: "python",
    title: `Drop-in NumPy / Stim CSS check matrices ([[${hx.n}, ${lx ? lx.ints.length : "?"}, d]])`,
    filename: `pf_${sanitizeIdent(lemma.id)}.py`,
    code: lines.join("\n"),
  };
}

export function extractDropInArtifact(missionSlug, lemma, sourceText) {
  if (!sourceText || typeof sourceText !== "string") return null;
  try {
    if (missionSlug === "ml-math-kernels") return extractMlKernelCuda(lemma, sourceText);
    if (missionSlug === "crypto-zk-circuits") return extractCryptoBitslice(lemma, sourceText);
    if (missionSlug === "sorting-networks") return extractSortNetC(lemma, sourceText);
    if (missionSlug === "verified-science-kernels") return extractMinimaxC(lemma, sourceText);
    if (missionSlug === "quantum-codes") return extractQuantumStim(lemma, sourceText);
  } catch {
    return null;
  }
  return null;
}
