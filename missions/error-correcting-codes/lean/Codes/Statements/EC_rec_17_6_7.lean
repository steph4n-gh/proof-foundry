import Codes.Core

namespace Codes.Statements.EC_rec_17_6_7

/--
  King of the Hill Frozen Record Statement (Constant-Weight Code A(17,6,7): best known 166 (Golay-derived, BSSS 1990), upper bound 206 (Polak 2017)):
  Downward-closed via `score ≤ C.length`, so `Record b` certifies A(17,6,7) ≥ b and
  `¬ Record b` certifies the upper bound A(17,6,7) ≤ b - 1.
-/
def Record (score : Nat) : Prop :=
  ∃ C : List (BitVec 17), score ≤ C.length ∧ Codes.IsConstantWeightCode 17 6 7 C

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨C, hlen, hc⟩ => ⟨C, Nat.le_trans h hlen, hc⟩

end Codes.Statements.EC_rec_17_6_7
