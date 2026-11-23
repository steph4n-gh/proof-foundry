import Erdos.Core

namespace Erdos.Statements.E_ram_005

/-- Frozen Wave 5 Statement: Lower bound R(4,4) > 17 (e.g. Paley graph on Z/17Z). -/
def Claim : Prop :=
  ¬ Erdos.Ramsey44At 17

end Erdos.Statements.E_ram_005
