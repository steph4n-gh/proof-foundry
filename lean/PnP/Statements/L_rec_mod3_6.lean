import PnP.Core

namespace PnP.Statements.L_rec_mod3_6

/-- Strict conventional DAG well-formedness: every gate reads strictly earlier wires (no free out-of-range false constants). -/
def IsWellFormed (c : PnP.B2Circuit 6) : Prop :=
  c.outputWire < 6 + c.gates.length ∧
  ∀ (i : Nat) (g : PnP.B2Gate), c.gates[i]? = some g → g.w1 < 6 + i ∧ g.w2 < 6 + i

/--
  King of the Hill Frozen Record Statement (Smallest Well-Formed B2 Circuit for MOD3=0 on 6 Bits):
  Open frontier in exact small-n circuit complexity (Knuth / Kulikov catalog: best known = 13 gates,
  tight exact optimality proof over full B2 is open / hard).
  Upward-closed via `c.size ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ c : PnP.B2Circuit 6, IsWellFormed c ∧ c.size ≤ score ∧ c.Computes (PnP.mod3Eq0 6)

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hsz, hcomp⟩ => ⟨c, hwf, Nat.le_trans hsz h, hcomp⟩

end PnP.Statements.L_rec_mod3_6
