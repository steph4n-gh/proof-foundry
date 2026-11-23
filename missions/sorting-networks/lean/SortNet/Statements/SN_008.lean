import SortNet.Core

namespace SortNet.Statements.SN_008

/-- Frozen Statement: Match the 13-wire sorting network World Record (45 comparators). -/
def Claim : Prop :=
  ∃ net : SortNet.Net 13, net.length ≤ 45 ∧ SortNet.IsBoolSorter 13 net

end SortNet.Statements.SN_008
