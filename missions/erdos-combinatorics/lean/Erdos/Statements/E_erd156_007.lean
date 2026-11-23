import Erdos.Core

namespace Erdos.Statements.E_erd156_007

/-- Frozen Wave 5 Frontier Contest: Does {1..100} admit a maximal Sidon subset of size ≤ 7? Prove OR refute! -/
def Claim : Prop :=
  ∃ A : List Nat, A.length ≤ 7 ∧ Erdos.IsMaximalSidon 100 A

end Erdos.Statements.E_erd156_007
