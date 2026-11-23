import MatMul.Core

namespace MatMul.Statements.MM_001

/-- Strassen's seven-product upper bound with integer coefficients. -/
def Claim : Prop :=
  ∃ S : SchemeInt 2 2 2, S.length ≤ 7 ∧ IsMatMulSchemeInt S

end MatMul.Statements.MM_001
