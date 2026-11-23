import SortNet.Core

namespace SortNet.Statements.SN_007

/-- Frozen Statement: Optimal 12-wire sorting network (39 comparators — proved optimal in 2020). -/
def Claim : Prop :=
  ∃ net : SortNet.Net 12, net.length ≤ 39 ∧ SortNet.IsBoolSorter 12 net

end SortNet.Statements.SN_007
