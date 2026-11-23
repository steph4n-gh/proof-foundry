import SortNet.Core

namespace SortNet.Statements.SN_005

/-- Frozen Statement: Optimal 9-wire sorting network (Floyd's 25-comparator benchmark). -/
def Claim : Prop :=
  ∃ net : SortNet.Net 9, net.length ≤ 25 ∧ SortNet.IsBoolSorter 9 net

end SortNet.Statements.SN_005
