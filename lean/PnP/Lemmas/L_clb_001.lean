import PnP.Core

namespace PnP.Lemmas.L_clb_001

private theorem monotone_eval {n : Nat} (c : Circuit n)
    (hm : c.isMonotone = true) : Monotone c.eval := by
  induction c with
  | input i =>
    intro x y hxy hx
    exact hxy i hx
  | const b =>
    intro x y _ hx
    exact hx
  | not c _ => simp [Circuit.isMonotone] at hm
  | and a b iha ihb =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hm
    intro x y hxy hx
    have ⟨hxa, hxb⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨iha ha x y hxy hxa, ihb hb x y hxy hxb⟩
  | or a b iha ihb =>
    have ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hm
    intro x y hxy hx
    rcases Bool.or_eq_true_iff.mp hx with hxa | hxb
    · exact Bool.or_eq_true_iff.mpr (Or.inl (iha ha x y hxy hxa))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (ihb hb x y hxy hxb))
  | xor a b _ _ => simp [Circuit.isMonotone] at hm

theorem xor2_no_monotone_circuit (c : Circuit 2) (hm : c.isMonotone = true) :
    ¬ c.Computes xor2 := by
  intro hc
  let x : BoolVec 2 := fun i => decide (i = 0)
  let y : BoolVec 2 := fun _ => true
  have hxy : BitLe x y := fun _ _ => rfl
  have hx : c.eval x = true := (hc x).trans (by decide)
  have hy := monotone_eval c hm x y hxy hx
  have hfalse : xor2 y = false := by decide
  rw [hc y, hfalse] at hy
  contradiction

end PnP.Lemmas.L_clb_001
