import SortNet.Core

namespace SortNet.Statements.SN_rec_015

/--
  King of the Hill Frozen Record Statement (15-Wire Sorting Network Size):
  Current world record = 56 comparators (proven lower bound = 51, Dobbelaere catalog).
  Upward-closed via `net.length ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ net : SortNet.Net 15, net.length ≤ score ∧ SortNet.IsBoolSorter 15 net

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨net, hlen, hs⟩ => ⟨net, Nat.le_trans hlen h, hs⟩

end SortNet.Statements.SN_rec_015
