import Quantum.Core

namespace Quantum.Statements.QC_rec_n18_d4_w6

/--
  King of the Hill (MAXIMIZE): Maximum logical qubits `k` for an 18-qubit distance-4
  low-weight qLDPC CSS code `[[18, k, 4]]` with stabilizer check weight ≤ 6.
-/
def Record (score : Nat) : Prop :=
  ∃ (k : Nat) (hx hz lx lz : List (BitVec 18)),
    score ≤ k ∧ Quantum.IsCSSCode 18 k 4 6 hx hz lx lz

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨k, hx, hz, lx, lz, hk, hcss⟩ => ⟨k, hx, hz, lx, lz, Nat.le_trans h hk, hcss⟩

end Quantum.Statements.QC_rec_n18_d4_w6
