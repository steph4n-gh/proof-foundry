import PnP.Core

namespace PnP.Statements.L_clb_007

/-- Frozen Frontier Contest: Does cyclicAdj 5 require ≥ 7 gates in full B2 (or can XOR beat 7)? Prove OR refute! -/
def Claim : Prop :=
  ∀ c : PnP.B2Circuit 5, c.Computes (PnP.cyclicAdj 5) → 7 ≤ c.size

end PnP.Statements.L_clb_007
