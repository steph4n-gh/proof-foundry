import PnP.Core

namespace PnP.Lemmas.L_meta_004_refute

private def circuit : B2Circuit 5 where
  gates := [
    ⟨.opAnd, 0, 1⟩,
    ⟨.opAnd, 2, 3⟩,
    ⟨.opOr, 5, 6⟩,  -- At least one pair is full.
    ⟨.opOr, 0, 1⟩,
    ⟨.opOr, 2, 3⟩,
    ⟨.opAnd, 8, 9⟩,  -- Both pairs are nonempty.
    -- Majority of these two conditions and the fifth input.
    ⟨.opAnd, 7, 10⟩,
    ⟨.opOr, 7, 10⟩,
    ⟨.opAnd, 12, 4⟩,
    ⟨.opOr, 11, 13⟩
  ]
  outputWire := 14

theorem counterexample : ∃ c : B2Circuit 5, c.size ≤ 10 ∧ c.Computes maj5 := by
  refine ⟨circuit, by decide, ?_⟩
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

end PnP.Lemmas.L_meta_004_refute
