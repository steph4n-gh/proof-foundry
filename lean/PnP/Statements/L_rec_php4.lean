import PnP.Core

namespace PnP.Statements.L_rec_php4

/--
  King of the Hill Frozen Record Statement (Shortest Tree-Like Resolution Proof of PHP(4,3)):
  Measures total proof-tree nodes (`ResProof.size`) refuting 4 pigeons into 3 holes.
  Standard recursive construction uses 97 nodes; tighten the proof tree or prove `¬ Record b`!
  Upward-closed via `p.size ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ p : PnP.ResProof (PnP.PHP 4 3) [], p.size ≤ score

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨p, hsz⟩ => ⟨p, Nat.le_trans hsz h⟩

end PnP.Statements.L_rec_php4
