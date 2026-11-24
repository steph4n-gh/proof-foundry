import Crypto.Core

namespace Crypto.Statements.CZ_rec_present_gates

/--
  King of the Hill: Minimum total B2 gate count for the PRESENT 4-bit S-box
  while keeping multiplicative complexity ≤ 4 non-linear gates.
-/
def Record (score : Nat) : Prop :=
  ∃ c : Crypto.MultiCircuit 4 4,
    c.IsWellFormed ∧ c.nonLinearCount ≤ 4 ∧ c.totalGates ≤ score ∧ c.Computes Crypto.presentSBox

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hnl, hsz, hcomp⟩ => ⟨c, hwf, hnl, Nat.le_trans hsz h, hcomp⟩

end Crypto.Statements.CZ_rec_present_gates
