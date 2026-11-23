import Erdos.Core

namespace Erdos.Statements.E_ram_007

/-- Frozen Wave 5 Statement: Lower bound R(3,6) > 17 (17-vertex triangle-free graph with no 6-independent set). -/
def Claim : Prop :=
  ¬ Erdos.Ramsey36At 17

end Erdos.Statements.E_ram_007
