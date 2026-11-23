import SortNet.Core

namespace SortNet.Statements.SN_rec_d17

/--
  King of the Hill Frozen Record Statement (17-Wire Sorting Network Parallel Depth):
  Famous open frontier: current world record = depth 10, proven lower bound = 9
  (Bundala–Závodný / Codish et al.; whether 17 wires can be sorted in depth 9 is OPEN!).
  Upward-closed via `netDepth net ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ net : SortNet.Net 17, SortNet.netDepth net ≤ score ∧ SortNet.IsBoolSorter 17 net

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨net, hd, hs⟩ => ⟨net, Nat.le_trans hd h, hs⟩

end SortNet.Statements.SN_rec_d17
