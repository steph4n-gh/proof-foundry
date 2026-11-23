import PnP.Core

namespace PnP.Statements.L_syn_001

/-- Frozen Wave 5 Statement: Shared-wire B2 circuit of size ≤ 8 computing MOD3=0 on 4 bits. -/
def Claim : Prop :=
  ∃ c : PnP.B2Circuit 4, c.size ≤ 8 ∧ c.Computes (PnP.mod3Eq0 4)

end PnP.Statements.L_syn_001
