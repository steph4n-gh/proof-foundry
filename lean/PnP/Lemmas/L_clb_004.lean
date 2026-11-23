import PnP.Core

/-!
  L-clb-004: depth-size tradeoff for formulas. A `Circuit n` (formula over
  {NOT, AND, OR, XOR, CONST}) of depth `d` reads at most `2 ^ d` distinct inputs.

  `countDistinctInputs` is not defined in `PnP.Core`; it is defined here as the number of
  input indices `i : Fin n` with `c.usesInput i = true`.

  Proof: induction. An input leaf reads exactly one variable (`finRange` is `Nodup`);
  NOT keeps the set; a binary gate reads the union, of size at most
  `2^da + 2^db ≤ 2 · 2^(max da db) = 2^(1 + max da db)`.
  Corollary: any formula depending on all `n` inputs has depth ≥ log2 n.
-/
namespace PnP.Lemmas.L_clb_004

open PnP

/-- Number of distinct input variables read by a formula. -/
def countDistinctInputs {n : Nat} (c : Circuit n) : Nat :=
  ((List.finRange n).filter (fun i => c.usesInput i)).length

theorem filter_or_le {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter (fun x => p x || q x)).length ≤ (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

theorem count_input_le {n : Nat} (j : Fin n) :
    ((List.finRange n).filter (fun i => decide (j = i))).length ≤ 1 := by
  have h1 : (List.finRange n).filter (fun i => decide (j = i)) =
      (List.finRange n).filter (· == j) := by
    apply List.filter_congr
    intro i _
    by_cases h : j = i
    · subst h; simp
    · have h' : ¬ i = j := fun e => h e.symm
      simp [h, h']
  rw [h1, ← List.count_eq_length_filter, (List.nodup_finRange n).count]
  split <;> omega

theorem two_pow_add_le (a b : Nat) : 2 ^ a + 2 ^ b ≤ 2 ^ (1 + Nat.max a b) := by
  have ha : 2 ^ a ≤ 2 ^ Nat.max a b := Nat.pow_le_pow_right (by decide) (Nat.le_max_left a b)
  have hb : 2 ^ b ≤ 2 ^ Nat.max a b := Nat.pow_le_pow_right (by decide) (Nat.le_max_right a b)
  rw [Nat.add_comm 1, Nat.pow_succ]
  omega

theorem bin_case {n : Nat} (a b : Circuit n)
    (iha : countDistinctInputs a ≤ 2 ^ a.depth) (ihb : countDistinctInputs b ≤ 2 ^ b.depth) :
    ((List.finRange n).filter (fun i => a.usesInput i || b.usesInput i)).length ≤
      2 ^ (1 + Nat.max a.depth b.depth) :=
  Nat.le_trans (filter_or_le _ (fun i => a.usesInput i) (fun i => b.usesInput i))
    (Nat.le_trans (Nat.add_le_add iha ihb) (two_pow_add_le _ _))

theorem depth_bounds_inputs : ∀ {n : Nat} (c : Circuit n), countDistinctInputs c ≤ 2 ^ c.depth := by
  intro n c
  induction c with
  | input j => exact count_input_le j
  | const b =>
    show ((List.finRange n).filter (fun _ => false)).length ≤ 2 ^ 0
    have h0 : (List.finRange n).filter (fun _ => false) = [] :=
      List.filter_eq_nil_iff.2 (fun _ _ h => Bool.noConfusion h)
    rw [h0]
    exact Nat.zero_le _
  | not c ih =>
    show countDistinctInputs c ≤ 2 ^ (1 + c.depth)
    exact Nat.le_trans ih (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  | and a b iha ihb => exact bin_case a b iha ihb
  | or a b iha ihb => exact bin_case a b iha ihb
  | xor a b iha ihb => exact bin_case a b iha ihb

end PnP.Lemmas.L_clb_004
