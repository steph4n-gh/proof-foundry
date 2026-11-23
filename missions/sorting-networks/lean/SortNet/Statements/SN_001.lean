import SortNet.Core

namespace SortNet.Statements.SN_001

/-- Frozen Statement: Knuth's Zero-One Principle — any comparator network that sorts all Boolean inputs sorts all Nat inputs. -/
def Claim : Prop :=
  ∀ (n : Nat) (net : SortNet.Net n), SortNet.IsBoolSorter n net → SortNet.IsNatSorter n net

end SortNet.Statements.SN_001
