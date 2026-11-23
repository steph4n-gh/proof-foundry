import Erdos.Core

/-
  E-sch-003 (Red Team refutation): `SchurForced 13 3` is FALSE.
  The explicit sum-free 3-coloring {1,4,10,13} | {2,3,11,12} | {5,6,7,8,9} of {1..13}
  shows S(3) ≥ 13, refuting the conjecture S(3) ≤ 12.
-/
namespace Erdos.Claims.E_sch_003_refute

open Erdos

/-- Color of the element `i + 1`. -/
def col13 : Fin 13 → Fin 3 := fun i =>
  if i.val = 0 ∨ i.val = 3 ∨ i.val = 9 ∨ i.val = 12 then 0
  else if i.val = 1 ∨ i.val = 2 ∨ i.val = 10 ∨ i.val = 11 then 1
  else 2

theorem col13_sumfree : IsSumFreeColoring 13 3 col13 := by
  unfold IsSumFreeColoring
  decide

theorem counterexample : ¬ SchurForced 13 3 := by
  intro h
  exact h col13 col13_sumfree

end Erdos.Claims.E_sch_003_refute
