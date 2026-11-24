import Crypto.Core

namespace Crypto.Statements.CZ_rec_ascon_gates

/--
  King of the Hill: Minimum total B2 gate count for the NIST SP 800-232 Ascon 5-bit S-box
  while keeping multiplicative complexity ≤ 5 AND gates and AND-depth ≤ 1.
-/
def Record (score : Nat) : Prop :=
  ∃ c : Crypto.MultiCircuit 5 5,
    c.IsWellFormed ∧ c.nonLinearCount ≤ 5 ∧ c.andDepth ≤ 1 ∧
    c.totalGates ≤ score ∧ c.Computes Crypto.asconSBox

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hnl, hd, hsz, hcomp⟩ => ⟨c, hwf, hnl, hd, Nat.le_trans hsz h, hcomp⟩

end Crypto.Statements.CZ_rec_ascon_gates
