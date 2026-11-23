import MatMul.Core

namespace MatMul.Statements.MM_rec_3x3x4

def Record (score : Nat) : Prop :=
  ∃ S : SchemeInt 3 3 4, S.length ≤ score ∧ IsMatMulSchemeInt S

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨S, size, valid⟩ => ⟨S, Nat.le_trans size h, valid⟩

end MatMul.Statements.MM_rec_3x3x4
