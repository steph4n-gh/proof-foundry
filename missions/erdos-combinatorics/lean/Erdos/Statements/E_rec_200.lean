import Erdos.Core

namespace Erdos.Statements.E_rec_200

/--
  King of the Hill Frozen Record Statement (Erdős #156 Smallest Maximal Sidon Set in {1..200}):
  Ascending greedy gives size 14; search finds ≤ 11. Upward-closed via `A.length ≤ score`
  so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ A : List Nat, A.length ≤ score ∧ Erdos.IsMaximalSidon 200 A

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨A, hlen, hs⟩ => ⟨A, Nat.le_trans hlen h, hs⟩

end Erdos.Statements.E_rec_200
