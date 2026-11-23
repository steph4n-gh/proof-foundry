import PnP.Core

namespace PnP.Statements.L_syn_003

/-- Frozen Wave 5 Frontier Contest: Can MOD3=0 on 4 bits be computed by a 7-gate B2 DAG circuit? Prove OR refute! -/
def Claim : Prop :=
  ∃ c : PnP.B2Circuit 4, c.size ≤ 7 ∧ c.Computes (PnP.mod3Eq0 4)

end PnP.Statements.L_syn_003
