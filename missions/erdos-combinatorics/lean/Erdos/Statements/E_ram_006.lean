import Erdos.Core

namespace Erdos.Statements.E_ram_006

/-- Frozen Wave 5 Statement: Lower bound R(3,5) > 13 (e.g. cyclic C_13(1, 5) avoidance graph). -/
def Claim : Prop :=
  ¬ Erdos.Ramsey35At 13

end Erdos.Statements.E_ram_006
