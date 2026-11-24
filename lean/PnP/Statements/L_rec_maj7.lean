import PnP.Core

namespace PnP.Statements.L_rec_maj7

/-- Strict conventional DAG well-formedness: every gate reads strictly earlier wires (no free out-of-range false constants). -/
def IsWellFormed (c : PnP.B2Circuit 7) : Prop :=
  c.outputWire < 7 + c.gates.length ∧
  ∀ (i : Nat) (g : PnP.B2Gate), c.gates[i]? = some g → g.w1 < 7 + i ∧ g.w2 < 7 + i

/--
  King of the Hill Frozen Record Statement (Smallest Well-Formed B2 Circuit for 7-Bit Majority MAJ7):
  Classic open frontier in exact small-n circuit synthesis (best known = 16 gates over B2;
  exact optimality of 16 vs 15 is open and drives SAT/circuit-minimization benchmarks).
  Upward-closed via `c.size ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ c : PnP.B2Circuit 7, IsWellFormed c ∧ c.size ≤ score ∧ c.Computes (PnP.thresh 7 4)

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hsz, hcomp⟩ => ⟨c, hwf, Nat.le_trans hsz h, hcomp⟩

end PnP.Statements.L_rec_maj7
