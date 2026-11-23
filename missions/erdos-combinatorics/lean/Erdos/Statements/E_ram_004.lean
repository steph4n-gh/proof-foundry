import Erdos.Core

namespace Erdos.Statements.E_ram_004

/-- Frozen Wave 5 Statement: Exact Ramsey upper bound R(3,4) ≤ 9 (closes R(3,4) = 9 with E-ram-003). -/
def Claim : Prop :=
  Erdos.Ramsey34At 9

end Erdos.Statements.E_ram_004
