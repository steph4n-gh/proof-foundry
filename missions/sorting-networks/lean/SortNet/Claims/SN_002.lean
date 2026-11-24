import SortNet.Statements.SN_002

namespace SortNet.Claims.SN_002

private def net4 : SortNet.Net 4 :=
  [(0, 2), (1, 3), (0, 1), (2, 3), (1, 2)]

private def net5 : SortNet.Net 5 :=
  [(0, 3), (1, 4), (0, 2), (1, 3), (0, 1), (2, 4), (1, 2), (3, 4), (2, 3)]

private def vec4 (b0 b1 b2 b3 : Bool) : Fin 4 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3

private def vec5 (b0 b1 b2 b3 b4 : Bool) : Fin 5 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4

private theorem vec4_eta (v : Fin 4 → Bool) : v = vec4 (v 0) (v 1) (v 2) (v 3) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

private theorem vec5_eta (v : Fin 5 → Bool) : v = vec5 (v 0) (v 1) (v 2) (v 3) (v 4) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

private theorem net4_check :
    ∀ b0 b1 b2 b3 : Bool, ∀ i j : Fin 4,
      i.val ≤ j.val →
      SortNet.evalBool net4 (vec4 b0 b1 b2 b3) i = true →
      SortNet.evalBool net4 (vec4 b0 b1 b2 b3) j = true := by
  decide

private theorem net5_check :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ i j : Fin 5,
      i.val ≤ j.val →
      SortNet.evalBool net5 (vec5 b0 b1 b2 b3 b4) i = true →
      SortNet.evalBool net5 (vec5 b0 b1 b2 b3 b4) j = true := by
  decide +kernel

theorem optimal_4_and_5_sorters : SortNet.Statements.SN_002.Claim := by
  refine ⟨⟨net4, by decide, by decide, ?_⟩, ⟨net5, by decide, by decide, ?_⟩⟩
  · intro v
    rw [vec4_eta v]
    exact net4_check (v 0) (v 1) (v 2) (v 3)
  · intro v
    rw [vec5_eta v]
    exact net5_check (v 0) (v 1) (v 2) (v 3) (v 4)

end SortNet.Claims.SN_002
