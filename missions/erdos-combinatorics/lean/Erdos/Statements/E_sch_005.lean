import Erdos.Core

namespace Erdos.Statements.E_sch_005

/-- Frozen Wave 5 Statement: Schur lower bound S(4) ≥ 44 via an explicit sum-free 4-coloring of {1..44}. -/
def Claim : Prop :=
  ∃ col : Fin 44 → Fin 4, Erdos.IsSumFreeColoring 44 4 col

end Erdos.Statements.E_sch_005
