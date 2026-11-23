import MatMul.Core

namespace MatMul.Statements.MM_rec_3x4x5

def Record (score : Nat) : Prop :=
  ∃ S : SchemeInt 3 4 5, S.length ≤ score ∧ IsMatMulSchemeInt S

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨S, size, valid⟩ => ⟨S, Nat.le_trans size h, valid⟩

end MatMul.Statements.MM_rec_3x4x5
