import MatMul.Core

namespace MatMul.Statements.MM_002

/-- Strassen's seven-product upper bound with coefficients in GF(2). -/
def Claim : Prop :=
  ∃ S : SchemeF2 2 2 2, S.length ≤ 7 ∧ IsMatMulSchemeF2 S

end MatMul.Statements.MM_002
