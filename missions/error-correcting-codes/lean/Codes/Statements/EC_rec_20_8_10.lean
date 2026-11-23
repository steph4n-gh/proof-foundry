import Codes.Core

namespace Codes.Statements.EC_rec_20_8_10

/--
  King of the Hill Frozen Record Statement (Constant-Weight Code A(20,8,10): best known 176 (group code, BSSS 1990), upper bound 206 (Agrell–Vardy–Zeger 2000)):
  Downward-closed via `score ≤ C.length`, so `Record b` certifies A(20,8,10) ≥ b and
  `¬ Record b` certifies the upper bound A(20,8,10) ≤ b - 1.
-/
def Record (score : Nat) : Prop :=
  ∃ C : List (BitVec 20), score ≤ C.length ∧ Codes.IsConstantWeightCode 20 8 10 C

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨C, hlen, hc⟩ => ⟨C, Nat.le_trans h hlen, hc⟩

end Codes.Statements.EC_rec_20_8_10
