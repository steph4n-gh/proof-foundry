import PnP.Core

/-
  L-meta-001: 3-bit Majority (MAJ3) is computable by a 4-gate monotone circuit
  and requires at least 2 binary gates in any formula circuit.
-/
namespace PnP.Lemmas.L_meta_001

private def maj3Circuit : Circuit 3 :=
  let a := Circuit.input ⟨0, by decide⟩
  let b := Circuit.input ⟨1, by decide⟩
  let c := Circuit.input ⟨2, by decide⟩
  .or (.and a b) (.and (.or a b) c)

private theorem maj3Circuit_computes : maj3Circuit.Computes maj3 := by
  intro x
  simp only [maj3Circuit, Circuit.eval, maj3]
  cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩ <;> rfl

private def inputLeaves {n : Nat} : Circuit n → List (Fin n)
  | .input i => [i]
  | .const _ => []
  | .not c => inputLeaves c
  | .and a b => inputLeaves a ++ inputLeaves b
  | .or a b => inputLeaves a ++ inputLeaves b
  | .xor a b => inputLeaves a ++ inputLeaves b

private theorem inputLeaves_length_le {n : Nat} (c : Circuit n) :
    (inputLeaves c).length ≤ c.binaryGateCount + 1 := by
  induction c with
  | input _ => simp [inputLeaves, Circuit.binaryGateCount]
  | const _ => simp [inputLeaves, Circuit.binaryGateCount]
  | not c ih => simp [inputLeaves, Circuit.binaryGateCount]; exact ih
  | and a b iha ihb =>
    simp only [inputLeaves, List.length_append, Circuit.binaryGateCount]
    omega
  | or a b iha ihb =>
    simp only [inputLeaves, List.length_append, Circuit.binaryGateCount]
    omega
  | xor a b iha ihb =>
    simp only [inputLeaves, List.length_append, Circuit.binaryGateCount]
    omega

private theorem eval_flipBit_of_not_mem {n : Nat} (c : Circuit n) (i : Fin n)
    (hi : i ∉ inputLeaves c) :
    ∀ x : BoolVec n, c.eval (flipBit x i) = c.eval x := by
  induction c with
  | input j =>
    intro x
    have hne : j ≠ i := by
      intro h
      apply hi
      simp [inputLeaves, h]
    simp [Circuit.eval, flipBit, hne]
  | const _ => intro _; rfl
  | not c ih =>
    intro x
    simp only [Circuit.eval]
    rw [ih hi x]
  | and a b iha ihb =>
    intro x
    simp only [inputLeaves, List.mem_append, not_or] at hi
    simp only [Circuit.eval]
    rw [iha hi.1 x, ihb hi.2 x]
  | or a b iha ihb =>
    intro x
    simp only [inputLeaves, List.mem_append, not_or] at hi
    simp only [Circuit.eval]
    rw [iha hi.1 x, ihb hi.2 x]
  | xor a b iha ihb =>
    intro x
    simp only [inputLeaves, List.mem_append, not_or] at hi
    simp only [Circuit.eval]
    rw [iha hi.1 x, ihb hi.2 x]

private theorem maj3_depends_0 :
    ∃ x : BoolVec 3, maj3 x ≠ maj3 (flipBit x ⟨0, by decide⟩) :=
  ⟨fun j => j.val == 1, by decide⟩

private theorem maj3_depends_1 :
    ∃ x : BoolVec 3, maj3 x ≠ maj3 (flipBit x ⟨1, by decide⟩) :=
  ⟨fun j => j.val == 0, by decide⟩

private theorem maj3_depends_2 :
    ∃ x : BoolVec 3, maj3 x ≠ maj3 (flipBit x ⟨2, by decide⟩) :=
  ⟨fun j => j.val == 0, by decide⟩

private theorem mem_inputLeaves_of_depends {n : Nat} (c : Circuit n) (f : BoolFn n)
    (hc : c.Computes f) (i : Fin n) (hdep : ∃ x : BoolVec n, f x ≠ f (flipBit x i)) :
    i ∈ inputLeaves c := by
  by_cases hmem : i ∈ inputLeaves c
  · exact hmem
  · exfalso
    rcases hdep with ⟨x, hx⟩
    apply hx
    rw [← hc x, ← hc (flipBit x i), eval_flipBit_of_not_mem c i hmem x]

private theorem list_len_ge_three (L : List (Fin 3))
    (h0 : (⟨0, by decide⟩ : Fin 3) ∈ L)
    (h1 : (⟨1, by decide⟩ : Fin 3) ∈ L)
    (h2 : (⟨2, by decide⟩ : Fin 3) ∈ L) : 3 ≤ L.length := by
  match L with
  | [] => simp at h0
  | [a] =>
    simp at h0 h1
    subst h0
    exact absurd h1 (by decide)
  | [a, b] =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h1 h2
    rcases h0 with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    all_goals first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | (rw [h1] at h2; exact absurd h2 (by decide))
      | (rw [← h1] at h2; exact absurd h2 (by decide))
  | _ :: _ :: _ :: _ => simp

theorem maj3_circuit_bounds :
    (∃ c : Circuit 3, c.isMonotone = true ∧ c.gateCount ≤ 4 ∧ c.Computes maj3) ∧
    (∀ c : Circuit 3, c.Computes maj3 → 2 ≤ c.binaryGateCount) := by
  constructor
  · exact ⟨maj3Circuit, rfl, by decide, maj3Circuit_computes⟩
  · intro c hc
    have h0 := mem_inputLeaves_of_depends c maj3 hc ⟨0, by decide⟩ maj3_depends_0
    have h1 := mem_inputLeaves_of_depends c maj3 hc ⟨1, by decide⟩ maj3_depends_1
    have h2 := mem_inputLeaves_of_depends c maj3 hc ⟨2, by decide⟩ maj3_depends_2
    have hlen := list_len_ge_three (inputLeaves c) h0 h1 h2
    have hbound := inputLeaves_length_le c
    omega

end PnP.Lemmas.L_meta_001
