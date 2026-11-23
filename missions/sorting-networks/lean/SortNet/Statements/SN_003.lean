import SortNet.Core

namespace SortNet.Statements.SN_003

/-- Frozen Statement: Exact optimality lower bound on 4 wires — no 4-wire sorting network has ≤ 4 comparators. -/
def Claim : Prop :=
  ∀ net : SortNet.Net 4, net.length ≤ 4 → ¬ SortNet.IsBoolSorter 4 net

end SortNet.Statements.SN_003
