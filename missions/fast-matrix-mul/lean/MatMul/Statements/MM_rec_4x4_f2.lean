import MatMul.Core

namespace MatMul.Statements.MM_rec_4x4_f2

def Record (score : Nat) : Prop :=
  ∃ S : SchemeF2 4 4 4, S.length ≤ score ∧ IsMatMulSchemeF2 S

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨S, size, valid⟩ => ⟨S, Nat.le_trans size h, valid⟩

end MatMul.Statements.MM_rec_4x4_f2
