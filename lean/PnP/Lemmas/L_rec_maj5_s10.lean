import PnP.Core
import PnP.Statements.L_rec_maj5

namespace PnP.Lemmas.L_rec_maj5_s10

open PnP

/-- 10-gate well-formed B2 circuit for MAJ5:
    A = x0x1 ∨ x2x3, B = (x0 ∨ x1)(x2 ∨ x3), output = MAJ3(A, B, x4). -/
def circuit : B2Circuit 5 where
  gates := [
    ⟨.opAnd, 0, 1⟩,    -- w5
    ⟨.opAnd, 2, 3⟩,    -- w6
    ⟨.opOr, 5, 6⟩,     -- w7  = A
    ⟨.opOr, 0, 1⟩,     -- w8
    ⟨.opOr, 2, 3⟩,     -- w9
    ⟨.opAnd, 8, 9⟩,    -- w10 = B
    ⟨.opAnd, 7, 10⟩,   -- w11 = A ∧ B
    ⟨.opOr, 7, 10⟩,    -- w12 = A ∨ B
    ⟨.opAnd, 12, 4⟩,   -- w13 = (A ∨ B) ∧ x4
    ⟨.opOr, 11, 13⟩    -- w14 = MAJ3(A, B, x4)
  ]
  outputWire := 14

theorem circuit_wf : PnP.Statements.L_rec_maj5.IsWellFormed circuit := by
  refine ⟨by decide, ?_⟩
  intro i g h
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h =>
    simp [circuit] at h; subst h; decide
  | n + 10, h => simp [circuit] at h

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

theorem record : PnP.Statements.L_rec_maj5.Record 10 :=
  ⟨circuit, circuit_wf, by decide, circuit_computes⟩

end PnP.Lemmas.L_rec_maj5_s10
