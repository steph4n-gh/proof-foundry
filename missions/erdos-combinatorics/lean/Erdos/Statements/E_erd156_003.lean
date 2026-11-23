import Erdos.Core

namespace Erdos.Statements.E_erd156_003

/--
  Frozen Wave 4 Statement (Erdős #156 Exact Minimum at N = 30):
  No list A of length ≤ 4 is a maximal Sidon subset of {1..30}.
  Combined with E-erd156-002 (5-element maximal Sidon set [1, 4, 11, 15, 17] ⊆ {1..30}),
  this completely pins down the minimum maximal Sidon set size in {1..30} as exactly 5.
-/
def Claim : Prop :=
  ∀ A : List Nat, A.length ≤ 4 → ¬ Erdos.IsMaximalSidon 30 A

end Erdos.Statements.E_erd156_003
