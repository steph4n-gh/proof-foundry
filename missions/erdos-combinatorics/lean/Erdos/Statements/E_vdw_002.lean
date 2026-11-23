import Erdos.Core

namespace Erdos.Statements.E_vdw_002

/-- Frozen Wave 5 Statement: 3-color van der Waerden lower bound W(3; 3) > 26 (26-element 3-coloring with no monochromatic 3-AP). -/
def Claim : Prop :=
  ∃ col : Fin 26 → Fin 3, Erdos.IsAPFree3 26 3 col

end Erdos.Statements.E_vdw_002
