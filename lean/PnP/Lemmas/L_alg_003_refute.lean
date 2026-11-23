import PnP.Core

namespace PnP.Lemmas.L_alg_003_refute

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  exact h i

private theorem parity_symmetric (perm : Fin 3 → Fin 3)
    (injective : Function.Injective perm) (x : BoolVec 3) :
    parityFn 3 (fun i => x (perm i)) = parityFn 3 x := by
  have h01 : perm 0 ≠ perm 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (injective h)
  have h02 : perm 0 ≠ perm 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (injective h)
  have h12 : perm 1 ≠ perm 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (injective h)
  change (x (perm 0) ^^ (x (perm 1) ^^ (x (perm 2) ^^ false))) =
    (x 0 ^^ (x 1 ^^ (x 2 ^^ false)))
  rcases fin3_cases (perm 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (perm 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (perm 2) with h2 | h2 | h2 <;>
    simp_all [Bool.xor_comm, Bool.xor_left_comm]

private theorem monotone_eval (c : Circuit n) (hc : c.isMonotone = true) :
    Monotone c.eval := by
  induction c with
  | input i =>
      intro x y hxy hx
      exact hxy i hx
  | const b =>
      intro x y hxy hx
      exact hx
  | not _ _ => cases hc
  | xor _ _ _ _ => cases hc
  | and a b ihA ihB =>
      have hm := Bool.and_eq_true_iff.mp hc
      intro x y hxy hx
      have ht := Bool.and_eq_true_iff.mp hx
      exact Bool.and_eq_true_iff.mpr ⟨ihA hm.1 x y hxy ht.1, ihB hm.2 x y hxy ht.2⟩
  | or a b ihA ihB =>
      have hm := Bool.and_eq_true_iff.mp hc
      intro x y hxy hx
      apply Bool.or_eq_true_iff.mpr
      rcases Bool.or_eq_true_iff.mp hx with ha | hb
      · exact Or.inl (ihA hm.1 x y hxy ha)
      · exact Or.inr (ihB hm.2 x y hxy hb)

theorem counterexample :
    (∀ (perm : Fin 3 → Fin 3), Function.Injective perm → ∀ x : BoolVec 3,
      parityFn 3 (fun i => x (perm i)) = parityFn 3 x) ∧
    (∀ c : Circuit 3, c.isMonotone = true → ¬ c.Computes (parityFn 3)) := by
  refine ⟨parity_symmetric, ?_⟩
  intro c hm computes
  let x : BoolVec 3 := fun i => i == 0
  let y : BoolVec 3 := fun i => (i == 0) || (i == 1)
  have hxy : BitLe x y := by
    intro i hi
    exact Bool.or_eq_true_iff.mpr (Or.inl hi)
  have hx : c.eval x = true := (computes x).trans (by rfl)
  have hy : c.eval y = false := (computes y).trans (by rfl)
  exact Bool.noConfusion (hy.symm.trans (monotone_eval c hm x y hxy hx))

end PnP.Lemmas.L_alg_003_refute
