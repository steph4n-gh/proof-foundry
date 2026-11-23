import SortNet.Core

namespace SortNet.Statements.SN_009

/-- Frozen OPEN WORLD RECORD BOUNTY: Beat the 13-wire sorting network record (≤ 44 comparators)!
    Proving this sets a new human world record; refuting it proves 45 is exact optimal! -/
def Claim : Prop :=
  ∃ net : SortNet.Net 13, net.length ≤ 44 ∧ SortNet.IsBoolSorter 13 net

end SortNet.Statements.SN_009
