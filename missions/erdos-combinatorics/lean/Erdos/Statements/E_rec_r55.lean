import Erdos.Core

namespace Erdos.Statements.E_rec_r55

/--
  King of the Hill Frozen Record Statement (MAXIMIZE — Ramsey R(5,5) Avoidance Frontier):
  One of the most famous open problems in combinatorics: R(5,5) ∈ [43, 48]
  (Exoo 1989: 42-vertex avoidance graph; Angeltveit–McKay 2024: R(5,5) ≤ 48, i.e. max ≤ 47).
  Downward-closed (`score ≤ n`) so `¬ Record b` certifies upper bound `≤ b - 1` (i.e. R(5,5) ≤ b).
-/
def Record (score : Nat) : Prop :=
  ∃ (n : Nat) (G : Erdos.SimpleGraph n), score ≤ n ∧ ¬ Erdos.HasK5 G ∧ ¬ Erdos.HasIndep5 G

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record b → Record a :=
  fun ⟨n, G, hle, hk5, hi5⟩ => ⟨n, G, Nat.le_trans h hle, hk5, hi5⟩

end Erdos.Statements.E_rec_r55
