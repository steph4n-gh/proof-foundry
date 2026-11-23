import Erdos.Core

namespace Erdos.Statements.E_rec_gol11

/--
  King of the Hill Frozen Record Statement (Optimal 11-Mark Golomb Ruler):
  Used in radio astronomy interferometry & phased-array radar (distinct pairwise baselines).
  Greedy Mian–Chowla length = 97; exact optimal 11-mark Golomb ruler length = 72.
  Upward-closed via `rulerLength marks ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ marks : List Nat, marks.length = 11 ∧ Erdos.IsGolombRuler marks ∧ Erdos.rulerLength marks ≤ score

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨marks, hlen, hg, hr⟩ => ⟨marks, hlen, hg, Nat.le_trans hr h⟩

end Erdos.Statements.E_rec_gol11
