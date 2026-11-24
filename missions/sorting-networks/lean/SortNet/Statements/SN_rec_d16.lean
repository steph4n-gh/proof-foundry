import SortNet.Core

namespace SortNet.Statements.SN_rec_d16

/--
  King of the Hill Frozen Record Statement (16-Wire Sorting Network Parallel Depth — AVX-512 / FPGA Latency):
  Exact known optimum = 9 parallel layers (Green / Van Voorhis; beats Batcher bitonic's 10 layers by 10% latency!).
  Upward-closed via `netDepth net ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ net : SortNet.Net 16, SortNet.netDepth net ≤ score ∧ SortNet.IsBoolSorter 16 net

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨net, hd, hs⟩ => ⟨net, Nat.le_trans hd h, hs⟩

end SortNet.Statements.SN_rec_d16
