import Crypto.Core

namespace Crypto.Statements.CZ_rec_aes_and

/--
  King of the Hill (Famous Boyar-Peralta Frontier): Minimum multiplicative complexity
  (non-linear / AND-gate count) for the FIPS-197 AES 8-bit S-box.
  Literature best = 32 AND gates (Boyar-Peralta); proving 31 or lower is a landmark result
  for MPC, FHE (TFHE/BGV), and masked hardware AES.
-/
def Record (score : Nat) : Prop :=
  ∃ c : Crypto.MultiCircuit 8 8,
    c.IsWellFormed ∧ c.nonLinearCount ≤ score ∧ c.Computes Crypto.aesSBox

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hnl, hcomp⟩ => ⟨c, hwf, Nat.le_trans hnl h, hcomp⟩

end Crypto.Statements.CZ_rec_aes_and
