import MatMul.Core

namespace MatMul.Statements.MM_rec_3x3x3

/--
  King of the Hill Frozen Record Statement (3×3 by 3×3 Matrix Multiplication over ℤ):
  One of the most famous open problems in algorithmic algebra since Laderman (1976):
  best known rank = 23 products, proven lower bound = 19 (Bläser).
  Certifying 22 products over ℤ would break a 50-year-old world record!
-/
def Record (score : Nat) : Prop :=
  ∃ S : SchemeInt 3 3 3, S.length ≤ score ∧ IsMatMulSchemeInt S

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨S, size, valid⟩ => ⟨S, Nat.le_trans size h, valid⟩

end MatMul.Statements.MM_rec_3x3x3
