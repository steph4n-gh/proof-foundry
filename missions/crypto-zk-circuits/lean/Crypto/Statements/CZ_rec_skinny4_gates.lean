import Crypto.Core

namespace Crypto.Statements.CZ_rec_skinny4_gates

/--
  King of the Hill: Minimum total B2 gate count for the SKINNY 4-bit S-box.
  Directly lowers ASIC/FPGA area and bit-sliced software cycle count.
-/
def Record (score : Nat) : Prop :=
  ∃ c : Crypto.MultiCircuit 4 4,
    c.IsWellFormed ∧ c.totalGates ≤ score ∧ c.Computes Crypto.skinny4SBox

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hsz, hcomp⟩ => ⟨c, hwf, Nat.le_trans hsz h, hcomp⟩

end Crypto.Statements.CZ_rec_skinny4_gates
