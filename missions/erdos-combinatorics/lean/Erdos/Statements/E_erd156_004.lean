import Erdos.Core

namespace Erdos.Statements.E_erd156_004

/-- Frozen Wave 5 Statement: Exact length-5 maximal Sidon subset of {1..30} (pins exact min = 5 with E-erd156-003). -/
def Claim : Prop :=
  ∃ A : List Nat, A.length = 5 ∧ Erdos.IsMaximalSidon 30 A

end Erdos.Statements.E_erd156_004
