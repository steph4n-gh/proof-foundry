import Erdos.Core

namespace Erdos.Statements.E_vdw_001

/-- Frozen Wave 5 Statement: Exact van der Waerden threshold W(3,3) = 9 (8-element 2-coloring avoids 3-AP; 9 forces one). -/
def Claim : Prop :=
  (∃ col : Fin 8 → Fin 2, Erdos.IsAPFree3 8 2 col) ∧ Erdos.VanDerWaerden3 9 2

end Erdos.Statements.E_vdw_001
