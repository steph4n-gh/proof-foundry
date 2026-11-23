import Codes.Core

namespace Codes.Statements.EC_003

/-- Frozen Statement: the Plotkin bound — if `2d > n`, every binary code of length `n` and
    minimum distance `d` satisfies `|C| · (2d − n) ≤ 2d`, i.e. `A(n,d) ≤ 2d / (2d − n)`. -/
def Claim : Prop :=
  ∀ (n d : Nat) (C : List (BitVec n)), n < 2 * d → Codes.IsBinaryCode n d C →
    C.length * (2 * d - n) ≤ 2 * d

end Codes.Statements.EC_003
