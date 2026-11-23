import SortNet.Core

namespace SortNet.Statements.SN_004

/-- Frozen Statement: Optimal 8-wire sorting network (19 comparators, parallel depth ≤ 6). -/
def Claim : Prop :=
  ∃ net : SortNet.Net 8, net.length ≤ 19 ∧ SortNet.netDepth net ≤ 6 ∧ SortNet.IsBoolSorter 8 net

end SortNet.Statements.SN_004
