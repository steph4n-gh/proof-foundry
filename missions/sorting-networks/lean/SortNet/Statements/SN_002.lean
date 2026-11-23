import SortNet.Core

namespace SortNet.Statements.SN_002

/-- Frozen Statement: Optimal 4-wire (5 comparators, depth 3) AND 5-wire (9 comparators, depth 5) sorting networks. -/
def Claim : Prop :=
  (∃ net : SortNet.Net 4, net.length ≤ 5 ∧ SortNet.netDepth net ≤ 3 ∧ SortNet.IsBoolSorter 4 net) ∧
  (∃ net : SortNet.Net 5, net.length ≤ 9 ∧ SortNet.netDepth net ≤ 5 ∧ SortNet.IsBoolSorter 5 net)

end SortNet.Statements.SN_002
