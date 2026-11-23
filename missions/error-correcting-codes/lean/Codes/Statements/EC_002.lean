import Codes.Core

namespace Codes.Statements.EC_002

/-- Frozen Statement: Hamming's sphere-packing bound for single-error-correcting codes —
    the radius-1 balls (each of size `n + 1`) around the codewords of a binary code with
    minimum distance 3 are disjoint, so `|C| · (n + 1) ≤ 2^n`. -/
def Claim : Prop :=
  ∀ (n : Nat) (C : List (BitVec n)), Codes.IsBinaryCode n 3 C → C.length * (n + 1) ≤ 2 ^ n

end Codes.Statements.EC_002
