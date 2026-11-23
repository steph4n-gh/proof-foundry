import PnP.Core

namespace PnP.Statements.L_syn_002

/-- Frozen Wave 5 Frontier Contest: Exact B2 complexity of 5-bit Majority (MAJ5) is ≥ 10 (paired with MAJ5 ≤ 10). Prove OR refute! -/
def Claim : Prop :=
  ∀ c : PnP.B2Circuit 5, c.Computes PnP.maj5 → 10 ≤ c.size

end PnP.Statements.L_syn_002
