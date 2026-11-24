import SortNet.Core

namespace SortNet.Statements.SN_rec_016

/--
  King of the Hill Frozen Record Statement (16-Wire Sorting Network Size — AVX-512 / GPU Half-Warp Width):
  Classic Green (1969) world record = 60 comparators, proven lower bound = 53.
  Directly compiles to branchless SIMD AVX-512 (16×int32/float32) and GPU warp-level register sorts!
-/
def Record (score : Nat) : Prop :=
  ∃ net : SortNet.Net 16, net.length ≤ score ∧ SortNet.IsBoolSorter 16 net

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨net, hlen, hs⟩ => ⟨net, Nat.le_trans hlen h, hs⟩

end SortNet.Statements.SN_rec_016
