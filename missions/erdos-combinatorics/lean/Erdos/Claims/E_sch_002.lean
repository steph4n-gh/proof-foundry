import Erdos.Core

/-
  E-sch-002: Schur lower bound S(3) ≥ 13.
  Explicit sum-free 3-coloring of {1..13}: {1,4,10,13} | {2,3,11,12} | {5,6,7,8,9}.
-/
namespace Erdos.Claims.E_sch_002

open Erdos

/-- Color of the element `i + 1`. -/
def col13 : Fin 13 → Fin 3 := fun i =>
  if i.val = 0 ∨ i.val = 3 ∨ i.val = 9 ∨ i.val = 12 then 0
  else if i.val = 1 ∨ i.val = 2 ∨ i.val = 10 ∨ i.val = 11 then 1
  else 2

theorem col13_sumfree : IsSumFreeColoring 13 3 col13 := by
  unfold IsSumFreeColoring
  decide

theorem schur_three_ge_13 : ∃ col : Fin 13 → Fin 3, IsSumFreeColoring 13 3 col :=
  ⟨col13, col13_sumfree⟩

end Erdos.Claims.E_sch_002
