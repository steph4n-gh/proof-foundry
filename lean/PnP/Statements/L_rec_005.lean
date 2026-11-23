import PnP.Core

namespace PnP.Statements.L_rec_005

/-- Strict conventional DAG well-formedness: every gate reads strictly earlier wires (no free out-of-range false constants). -/
def IsWellFormed (c : PnP.B2Circuit 5) : Prop :=
  c.outputWire < 5 + c.gates.length ∧
  ∀ (i : Nat) (g : PnP.B2Gate), c.gates[i]? = some g → g.w1 < 5 + i ∧ g.w2 < 5 + i

/--
  King of the Hill Frozen Record Statement (Smallest Well-Formed B2 Circuit for MOD3=0 on 5 bits):
  Published exact optimum = 10 gates (Kulikov et al.); onboarding ceiling = 12 gates.
  Upward-closed via `c.size ≤ score` so `¬ Record b` certifies lower bound `≥ b + 1`.
-/
def Record (score : Nat) : Prop :=
  ∃ c : PnP.B2Circuit 5, IsWellFormed c ∧ c.size ≤ score ∧ c.Computes (PnP.mod3Eq0 5)

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨c, hwf, hsz, hcomp⟩ => ⟨c, hwf, Nat.le_trans hsz h, hcomp⟩

end PnP.Statements.L_rec_005
