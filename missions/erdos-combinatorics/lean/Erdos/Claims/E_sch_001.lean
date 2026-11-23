import Erdos.Core

/-
  E-sch-001: Exact Schur number S(2) = 4.
  {1..4} admits a sum-free 2-coloring ({1,4} | {2,3}), while every 2-coloring of {1..5}
  contains a monochromatic x + y = z.
-/
namespace Erdos.Claims.E_sch_001

open Erdos

/-- Color of the element `i + 1`: elements 1, 4 get color 0; 2, 3 get color 1. -/
def col4 : Fin 4 → Fin 2 := fun i => if i.val = 0 ∨ i.val = 3 then 0 else 1

theorem col4_sumfree : IsSumFreeColoring 4 2 col4 := by
  unfold IsSumFreeColoring
  decide

theorem forced5 : SchurForced 5 2 := by
  intro col h
  have h1 := h 0 0 1 (by decide)  -- 1 + 1 = 2
  have h2 := h 0 1 2 (by decide)  -- 1 + 2 = 3
  have h3 := h 1 1 3 (by decide)  -- 2 + 2 = 4
  have h6 := h 0 2 3 (by decide)  -- 1 + 3 = 4
  have h4 := h 1 2 4 (by decide)  -- 2 + 3 = 5
  have h5 := h 0 3 4 (by decide)  -- 1 + 4 = 5
  generalize col 0 = a at *
  generalize col 1 = b at *
  generalize col 2 = c at *
  generalize col 3 = d at *
  generalize col 4 = e at *
  revert a b c d e
  decide

theorem schur_two_exact :
    (∃ col : Fin 4 → Fin 2, IsSumFreeColoring 4 2 col) ∧ SchurForced 5 2 :=
  ⟨⟨col4, col4_sumfree⟩, forced5⟩

end Erdos.Claims.E_sch_001
