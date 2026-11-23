import Codes.Core

namespace Codes.Statements.EC_rec_17_6

/--
  King of the Hill Frozen Record Statement (Binary Code A(17,6): best known 258 (Milshtein 2019), upper bound 340 (Brouwer table)):
  Downward-closed via `score ≤ C.length`, so `Record b` certifies A(17,6) ≥ b and
  `¬ Record b` certifies the upper bound A(17,6) ≤ b - 1.
-/
def Record (score : Nat) : Prop :=
  ∃ C : List (BitVec 17), score ≤ C.length ∧ Codes.IsBinaryCode 17 6 C

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨C, hlen, hc⟩ => ⟨C, Nat.le_trans h hlen, hc⟩

end Codes.Statements.EC_rec_17_6
