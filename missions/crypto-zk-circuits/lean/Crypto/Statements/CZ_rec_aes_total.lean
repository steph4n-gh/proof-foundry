import Crypto.Core

namespace Crypto.Statements.CZ_rec_aes_total

/--
  King of the Hill (Boyar-Peralta / Maximov-Ekdahl Frontier): Minimum total B2 gate count
  for the FIPS-197 AES 8-bit S-box at multiplicative depth ≤ 4 (directly critical for
  low-latency FHE bootstrapping and hardware side-channel masking).
-/
def Record (score : Nat) : Prop :=
  ∃ c : Crypto.MultiCircuit 8 8,
    c.IsWellFormed ∧ c.andDepth ≤ 4 ∧ c.totalGates ≤ score ∧ c.Computes Crypto.aesSBox

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hd, hsz, hcomp⟩ => ⟨c, hwf, hd, Nat.le_trans hsz h, hcomp⟩

end Crypto.Statements.CZ_rec_aes_total
