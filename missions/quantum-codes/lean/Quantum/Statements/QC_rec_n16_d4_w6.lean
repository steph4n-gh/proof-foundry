import Quantum.Core

namespace Quantum.Statements.QC_rec_n16_d4_w6

/--
  King of the Hill (MAXIMIZE): Maximum logical qubits `k` for a 16-qubit distance-4
  low-weight qLDPC CSS code `[[16, k, 4]]` with stabilizer check weight ≤ 6.
  (Downward-closed via `∃ k, score ≤ k ∧ ...` so `¬ Record b` proves upper bound `k ≤ b - 1`.)
-/
def Record (score : Nat) : Prop :=
  ∃ (k : Nat) (hx hz lx lz : List (BitVec 16)),
    score ≤ k ∧ Quantum.IsCSSCode 16 k 4 6 hx hz lx lz

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨k, hx, hz, lx, lz, hk, hcss⟩ => ⟨k, hx, hz, lx, lz, Nat.le_trans h hk, hcss⟩

end Quantum.Statements.QC_rec_n16_d4_w6
