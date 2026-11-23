import SortNet.Core

namespace SortNet.Statements.SN_006

/-- Frozen Statement: Optimal 10-wire sorting network (Waksman/Green 29-comparator benchmark). -/
def Claim : Prop :=
  ∃ net : SortNet.Net 10, net.length ≤ 29 ∧ SortNet.IsBoolSorter 10 net

end SortNet.Statements.SN_006
