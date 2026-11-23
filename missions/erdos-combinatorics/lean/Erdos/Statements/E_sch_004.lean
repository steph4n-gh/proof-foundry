import Erdos.Core

namespace Erdos.Statements.E_sch_004

/--
  Frozen Wave 4 Statement (Exact Schur Number S(3) = 13 Upper Bound):
  Every 3-coloring of {1..14} contains a monochromatic Schur triple x + y = z.
  Combined with E-sch-002 (S(3) ≥ 13), this completely closes exact S(3) = 13.
-/
def Claim : Prop :=
  Erdos.SchurForced 14 3

end Erdos.Statements.E_sch_004
