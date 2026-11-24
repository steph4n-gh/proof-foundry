import PnP.Core
import PnP.Statements.L_rec_maj5

namespace PnP.Lemmas.L_rec_maj5_s9

open PnP

/-- Strictly well-formed 9-gate B2 circuit computing 5-bit Majority (MAJ5),
    beating the 10-gate incumbent (`L_rec_maj5_s10`) and achieving the true B2 optimum of 9 gates. -/
def circuit : B2Circuit 5 where
  gates := [
    ⟨.opXor, 0, 1⟩,   -- w5  = x0 ⊕ x1
    ⟨.opXor, 0, 2⟩,   -- w6  = x0 ⊕ x2
    ⟨.opXor, 2, 5⟩,   -- w7  = x0 ⊕ x1 ⊕ x2
    ⟨.opXor, 4, 7⟩,   -- w8  = x0 ⊕ x1 ⊕ x2 ⊕ x4
    ⟨.opXor, 3, 4⟩,   -- w9  = x3 ⊕ x4
    ⟨.opOr,  8, 9⟩,   -- w10 = w8 ∨ w9
    ⟨.opOr,  5, 6⟩,   -- w11 = w5 ∨ w6
    ⟨.opAnd, 10, 11⟩, -- w12 = w10 ∧ w11
    ⟨.opXor, 7, 12⟩   -- w13 = w7 ⊕ w12 = MAJ5
  ]
  outputWire := 13

theorem circuit_wf : PnP.Statements.L_rec_maj5.IsWellFormed circuit := by
  refine ⟨by decide, ?_⟩
  intro i g h
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h =>
    simp [circuit] at h; subst h; decide
  | n + 9, h => simp [circuit] at h

theorem circuit_computes : circuit.Computes maj5 := by
  intro x
  have hx : x = fun i => match i.val with
    | 0 => x 0
    | 1 => x 1
    | 2 => x 2
    | 3 => x 3
    | _ => x 4 := by
    funext i
    obtain ⟨i, hi⟩ := i
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> rfl

theorem record : PnP.Statements.L_rec_maj5.Record 9 :=
  ⟨circuit, circuit_wf, by decide, circuit_computes⟩

end PnP.Lemmas.L_rec_maj5_s9
