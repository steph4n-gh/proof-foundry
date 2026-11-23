import PnP.Core

namespace PnP.Lemmas.L_lib_001
open PnP

theorem monotone_circuit_is_monotone {n : Nat} (c : Circuit n) (hm : c.isMonotone = true) :
    Monotone c.eval := by
  induction c with
  | input i =>
    intro x y hxy hx
    exact hxy i hx
  | const b =>
    intro x y _ hx
    exact hx
  | not c ih => simp [Circuit.isMonotone] at hm
  | and a b iha ihb =>
    simp only [Circuit.isMonotone, Bool.and_eq_true] at hm
    intro x y hxy hx
    simp only [Circuit.eval, Bool.and_eq_true] at hx ⊢
    exact ⟨iha hm.1 x y hxy hx.1, ihb hm.2 x y hxy hx.2⟩
  | or a b iha ihb =>
    simp only [Circuit.isMonotone, Bool.and_eq_true] at hm
    intro x y hxy hx
    simp only [Circuit.eval, Bool.or_eq_true] at hx ⊢
    cases hx with
    | inl h => exact Or.inl (iha hm.1 x y hxy h)
    | inr h => exact Or.inr (ihb hm.2 x y hxy h)
  | xor a b iha ihb => simp [Circuit.isMonotone] at hm

end PnP.Lemmas.L_lib_001
