import PnP.Core

namespace PnP.Lemmas.L_clb_003

private def inputOccurrences {n : Nat} : Circuit n → List (Fin n)
  | .input i => [i]
  | .const _ => []
  | .not c => inputOccurrences c
  | .and a b | .or a b | .xor a b => inputOccurrences a ++ inputOccurrences b

private theorem eval_eq_of_agree_on_inputs {n : Nat} (c : Circuit n) (x y : BoolVec n)
    (h : ∀ i ∈ inputOccurrences c, x i = y i) : c.eval x = c.eval y := by
  induction c with
  | input i => exact h i (by simp [inputOccurrences])
  | const b => rfl
  | not c ih => simp only [Circuit.eval, ih h]
  | and a b iha ihb | or a b iha ihb | xor a b iha ihb =>
    simp only [inputOccurrences, List.mem_append] at h
    simp only [Circuit.eval, iha (fun i hi => h i (Or.inl hi)),
      ihb (fun i hi => h i (Or.inr hi))]

private theorem input_occurrences_le {n : Nat} (c : Circuit n) :
    (inputOccurrences c).length ≤ c.binaryGateCount + 1 := by
  induction c with
  | input i => simp [inputOccurrences, Circuit.binaryGateCount]
  | const b => simp [inputOccurrences, Circuit.binaryGateCount]
  | not c ih => exact ih
  | and a b iha ihb | or a b iha ihb | xor a b iha ihb =>
    simp only [inputOccurrences, Circuit.binaryGateCount, List.length_append]
    omega

private theorem parity_all_false (n : Nat) : parityFn n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parityFn, ih]

private theorem parity_one_true (n : Nat) (i : Fin n) :
    parityFn n (fun j => decide (j = i)) = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [parityFn, Fin.succ_ne_zero, parity_all_false]
    · simp [parityFn, Ne.symm (Fin.succ_ne_zero j), ih]

private theorem parity_depends_on {n : Nat} (i : Fin n) : DependsOn (parityFn n) i := by
  refine ⟨fun _ => false, ?_⟩
  have hflip : flipBit (fun _ => false) i = fun j => decide (j = i) := by
    funext j
    by_cases h : j = i <;> simp [flipBit, h]
  rw [hflip, parity_all_false, parity_one_true]
  decide

theorem parity_binary_gate_lower_bound {n : Nat} (c : Circuit n)
    (hc : c.Computes (parityFn n)) : n ≤ c.binaryGateCount + 1 := by
  have hinputs (i : Fin n) : i ∈ inputOccurrences c := by
    apply Decidable.byContradiction
    intro hmissing
    obtain ⟨x, hdiff⟩ := parity_depends_on i
    have heval : c.eval x = c.eval (flipBit x i) := by
      apply eval_eq_of_agree_on_inputs
      intro j hj
      have hne : j ≠ i := fun heq => hmissing (heq ▸ hj)
      simp [flipBit, hne]
    rw [hc x, hc (flipBit x i)] at heval
    exact hdiff heval
  have hlength := (List.nodup_finRange n).length_le_of_subset (fun {i} _ => hinputs i)
  rw [List.length_finRange] at hlength
  exact Nat.le_trans hlength (input_occurrences_le c)

end PnP.Lemmas.L_clb_003
