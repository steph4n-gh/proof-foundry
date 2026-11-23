import Erdos.Core

namespace Erdos.Statements.E_erd156_006

/-- Frozen Wave 5 Statement: Synthesize a maximal Sidon subset of {1..100} of size ≤ 8 (beating greedy size 10). -/
def Claim : Prop :=
  ∃ A : List Nat, A.length ≤ 8 ∧ Erdos.IsMaximalSidon 100 A

end Erdos.Statements.E_erd156_006
