import Lean.Data.Json
import PFOracle.BF16Oracle

open Lean PFOracle

private def jsonNat (j : Json) : Except String Nat :=
  match j with
  | .str s =>
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"Invalid nat: {s}"
  | j => j.getNat?

private def natField (j : Json) (key : String) : Except String Nat :=
  j.getObjVal? key >>= jsonNat

private def evaluate (j : Json) : Except String Json := do
  match ← (← j.getObjVal? "op").getStr? with
  | "allBf16Sweep" =>
    -- Single fast call sweeping all 65,536 bf16 bit patterns:
    -- returns flat arrays [f32Bits, rne32, latticeIdx, isNaN]
    let mut f32Arr : Array Json := Array.mkEmpty 65536
    let mut r32Arr : Array Json := Array.mkEmpty 65536
    let mut latArr : Array Json := Array.mkEmpty 65536
    let mut nanArr : Array Json := Array.mkEmpty 65536
    for i in [:65536] do
      let b : BitVec 16 := BitVec.ofNat 16 i
      let f32 := bf16ToF32Bits b
      let r32 := f32BitsToBf16RNE f32
      let lat := bf16LatticeIndex b
      let nan := bf16IsNaN b
      f32Arr := f32Arr.push (toJson f32.toNat)
      r32Arr := r32Arr.push (toJson r32.toNat)
      latArr := latArr.push (toJson lat)
      nanArr := nanArr.push (toJson nan)
    return Json.mkObj [
      ("f32Bits", Json.arr f32Arr),
      ("rne32", Json.arr r32Arr),
      ("lattice", Json.arr latArr),
      ("isNaN", Json.arr nanArr)
    ]
  | "f32ToBf16RNE" =>
    let u := BitVec.ofNat 32 (← natField j "u")
    return toJson (f32BitsToBf16RNE u).toNat
  | "f64ToBf16RNE" =>
    let u := BitVec.ofNat 64 (← natField j "u")
    return toJson (f64BitsToBf16RNE u).toNat
  | "fmafFiniteBits" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    let c := BitVec.ofNat 32 (← natField j "c")
    return toJson (fmafFiniteBits a b c).toNat
  | "cppIshrS" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppIshrS a b).toNat
  | "cppIadd" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppIadd a b).toNat
  | "cppIsub" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppIsub a b).toNat
  | "cppImul" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppImul a b).toNat
  | "cppIshl" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppIshl a b).toNat
  | "cppIshrU" =>
    let a := BitVec.ofNat 32 (← natField j "a")
    let b := BitVec.ofNat 32 (← natField j "b")
    return toJson (cppIshrU a b).toNat
  | op => throw s!"Unknown operation: {op}"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match Json.parse line >>= evaluate with
    | .ok value => stdout.putStrLn value.compress
    | .error message => throw (IO.userError message)
