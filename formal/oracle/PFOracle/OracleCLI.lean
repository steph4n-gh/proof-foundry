import Lean.Data.Json
import PFOracle.MathOracle

open Lean PFOracle

private def jsonInt (j : Json) : Except String Int :=
  match j with
  | .str s =>
    match s.toInt? with
    | some n => .ok n
    | none => .error s!"Invalid integer: {s}"
  | j => j.getInt?

private def intField (j : Json) (key : String) : Except String Int :=
  j.getObjVal? key >>= jsonInt

private def natField (j : Json) (key : String) : Except String Nat := do
  let n ← intField j key
  if n < 0 then throw s!"Expected a nonnegative integer for {key}"
  return n.toNat

private def dyadic (j : Json) : Except String PFOracle.Dyadic := do
  return ⟨← intField j "m", ← intField j "e"⟩

private def dyadicField (j : Json) (key : String) : Except String PFOracle.Dyadic :=
  j.getObjVal? key >>= dyadic

private def dyadicJson (a : PFOracle.Dyadic) : Json :=
  Json.mkObj [("m", toString a.m), ("e", toString a.e)]

private def evaluate (j : Json) : Except String Json := do
  match ← (← j.getObjVal? "op").getStr? with
  | "fixed128Exp" => return toString (fixed128Exp (← intField j "x"))
  | "fixed128Sin" => return toString (fixed128Sin (← intField j "x"))
  | "dyadicToFixed128" => return toString (dyadicToFixed128 (← dyadicField j "a"))
  | "dyadicAdd" => return dyadicJson (dyadicAdd (← dyadicField j "a") (← dyadicField j "b"))
  | "dyadicSub" => return dyadicJson (dyadicSub (← dyadicField j "a") (← dyadicField j "b"))
  | "dyadicMul" => return dyadicJson (dyadicMul (← dyadicField j "a") (← dyadicField j "b"))
  | "dyadicEq" => return toJson (dyadicEq (← dyadicField j "a") (← dyadicField j "b"))
  | "dyadicSign" => return toJson (dyadicSign (← dyadicField j "a"))
  | "exactDot" =>
    let pairs ← (← j.getObjVal? "pairs").getArr?
    let pairs ← pairs.toList.mapM fun pair => do
      return (← dyadicField pair "a", ← dyadicField pair "b")
    return dyadicJson (exactDot pairs)
  | "orient2d" =>
    return toJson (orient2dSign (← dyadicField j "ax") (← dyadicField j "ay")
      (← dyadicField j "bx") (← dyadicField j "by") (← dyadicField j "cx") (← dyadicField j "cy"))
  | "measuredScore" => return toString (ceilScore (← natField j "diffFix") (← natField j "scale"))
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
