import Quantum.Core

namespace Quantum.Statements.QC_rec_n15_d3_w4

/--
  King of the Hill (MAXIMIZE): Maximum logical qubits `k` for a 15-qubit distance-3
  ultra-low-weight CSS code `[[15, k, 3]]` with stabilizer check weight ≤ 4 (surface-code
  hardware connectivity budget!).
-/
def Record (score : Nat) : Prop :=
  ∃ (k : Nat) (hx hz lx lz : List (BitVec 15)),
    score ≤ k ∧ Quantum.IsCSSCode 15 k 3 4 hx hz lx lz

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨k, hx, hz, lx, lz, hk, hcss⟩ => ⟨k, hx, hz, lx, lz, Nat.le_trans h hk, hcss⟩

end Quantum.Statements.QC_rec_n15_d3_w4
