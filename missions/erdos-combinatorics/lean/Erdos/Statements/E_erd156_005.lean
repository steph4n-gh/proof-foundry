import Erdos.Core

namespace Erdos.Statements.E_erd156_005

/-- Frozen Wave 5 Statement: Universal Erdős #156 cubic lower bound N ≤ |A| + |A|^3 for every maximal Sidon set A ⊆ {1..N}. -/
def Claim : Prop :=
  ∀ (N : Nat) (A : List Nat), Erdos.IsMaximalSidon N A → N ≤ A.length + A.length * A.length * A.length

end Erdos.Statements.E_erd156_005
