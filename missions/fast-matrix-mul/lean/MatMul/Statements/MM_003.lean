import MatMul.Statements.MM_001

namespace MatMul.Statements.MM_003

/-- Tensoring two integer schemes multiplies their size bounds.
    Using the same rank-seven witness for both factors gives 4×4 in ≤49 products. -/
def Claim : Prop :=
  ∀ {m₁ n₁ p₁ m₂ n₂ p₂ r₁ r₂ : Nat},
    (∃ S : SchemeInt m₁ n₁ p₁, S.length ≤ r₁ ∧ IsMatMulSchemeInt S) →
    (∃ S : SchemeInt m₂ n₂ p₂, S.length ≤ r₂ ∧ IsMatMulSchemeInt S) →
    ∃ S : SchemeInt (m₁ * m₂) (n₁ * n₂) (p₁ * p₂), S.length ≤ r₁ * r₂ ∧ IsMatMulSchemeInt S

theorem four_by_four (compose : Claim) (strassen : MM_001.Claim) :
    ∃ S : SchemeInt 4 4 4, S.length ≤ 49 ∧ IsMatMulSchemeInt S :=
  compose (m₁ := 2) (n₁ := 2) (p₁ := 2) (r₁ := 7)
    (m₂ := 2) (n₂ := 2) (p₂ := 2) (r₂ := 7) strassen strassen

end MatMul.Statements.MM_003
