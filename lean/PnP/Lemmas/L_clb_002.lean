import PnP.Core

namespace PnP.Lemmas.L_clb_002

private theorem eval_flip_unused {n : Nat} (c : Circuit n) (i : Fin n) (x : BoolVec n)
    (h : c.usesInput i = false) : c.eval x = c.eval (flipBit x i) := by
  induction c with
  | input j =>
    simp [Circuit.usesInput] at h
    simp [Circuit.eval, flipBit, h]
  | const b => rfl
  | not c ih => simp only [Circuit.eval, ih h]
  | and a b iha ihb | or a b iha ihb | xor a b iha ihb =>
    have ⟨ha, hb⟩ := Bool.or_eq_false_iff.mp h
    simp only [Circuit.eval, iha ha, ihb hb]

theorem depends_implies_usesInput {n : Nat} (c : Circuit n) (f : BoolFn n) (i : Fin n)
    (hc : c.Computes f) (hd : DependsOn f i) : c.usesInput i = true := by
  cases h : c.usesInput i with
  | true => rfl
  | false =>
    obtain ⟨x, hdiff⟩ := hd
    have heval := eval_flip_unused c i x h
    rw [hc x, hc (flipBit x i)] at heval
    exact False.elim (hdiff heval)

end PnP.Lemmas.L_clb_002
