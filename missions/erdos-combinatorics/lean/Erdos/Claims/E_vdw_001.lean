import Erdos.Core
import Erdos.Statements.E_vdw_001

/-
  E-vdw-001: Exact Van der Waerden number W(3, 3) = 9.
  {1..8} admits a 3-AP-free 2-coloring (00110011), while every 2-coloring of {1..9}
  contains a monochromatic 3-term arithmetic progression.
-/
namespace Erdos.Claims.E_vdw_001

open Erdos

/-- 3-AP-free 2-coloring of {1..8}: color 0 on {1, 2, 5, 6} (indices 0, 1, 4, 5)
    and color 1 on {3, 4, 7, 8} (indices 2, 3, 6, 7). -/
private def col8 : Fin 8 → Fin 2 :=
  fun i => if i.val % 4 < 2 then 0 else 1

private theorem col8_apfree : IsAPFree3 8 2 col8 := by
  unfold IsAPFree3
  decide

private def ok3 (a b c : Bool) : Bool :=
  !((a == b) && (b == c))

private theorem ok3_of_not_mono {x y z : Fin 2} (h : ¬ (x = y ∧ y = z)) :
    ok3 (x == 0) (y == 0) (z == 0) = true := by
  revert x y z h
  decide

private def apFree9 (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Bool) : Bool :=
  ok3 c0 c1 c2 && ok3 c1 c2 c3 && ok3 c2 c3 c4 && ok3 c0 c2 c4 &&
  ok3 c3 c4 c5 && ok3 c1 c3 c5 && ok3 c4 c5 c6 && ok3 c2 c4 c6 &&
  ok3 c0 c3 c6 && ok3 c5 c6 c7 && ok3 c3 c5 c7 && ok3 c1 c4 c7 &&
  ok3 c6 c7 c8 && ok3 c4 c6 c8 && ok3 c2 c5 c8 && ok3 c0 c4 c8

private theorem apFree9_false :
    ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : Bool,
      apFree9 c0 c1 c2 c3 c4 c5 c6 c7 c8 = false := by
  decide

private theorem forced9 : VanDerWaerden3 9 2 := by
  intro col h
  have h012 := ok3_of_not_mono (h 0 1 2 (by decide) (by decide))
  have h123 := ok3_of_not_mono (h 1 2 3 (by decide) (by decide))
  have h234 := ok3_of_not_mono (h 2 3 4 (by decide) (by decide))
  have h024 := ok3_of_not_mono (h 0 2 4 (by decide) (by decide))
  have h345 := ok3_of_not_mono (h 3 4 5 (by decide) (by decide))
  have h135 := ok3_of_not_mono (h 1 3 5 (by decide) (by decide))
  have h456 := ok3_of_not_mono (h 4 5 6 (by decide) (by decide))
  have h246 := ok3_of_not_mono (h 2 4 6 (by decide) (by decide))
  have h036 := ok3_of_not_mono (h 0 3 6 (by decide) (by decide))
  have h567 := ok3_of_not_mono (h 5 6 7 (by decide) (by decide))
  have h357 := ok3_of_not_mono (h 3 5 7 (by decide) (by decide))
  have h147 := ok3_of_not_mono (h 1 4 7 (by decide) (by decide))
  have h678 := ok3_of_not_mono (h 6 7 8 (by decide) (by decide))
  have h468 := ok3_of_not_mono (h 4 6 8 (by decide) (by decide))
  have h258 := ok3_of_not_mono (h 2 5 8 (by decide) (by decide))
  have h048 := ok3_of_not_mono (h 0 4 8 (by decide) (by decide))
  have htrue :
      apFree9 (col 0 == 0) (col 1 == 0) (col 2 == 0)
              (col 3 == 0) (col 4 == 0) (col 5 == 0)
              (col 6 == 0) (col 7 == 0) (col 8 == 0) = true := by
    simp only [apFree9, h012, h123, h234, h024, h345, h135, h456, h246,
               h036, h567, h357, h147, h678, h468, h258, h048, Bool.and_self]
  rw [apFree9_false] at htrue
  exact Bool.false_ne_true htrue

theorem vdw_3_3_exact : Erdos.Statements.E_vdw_001.Claim :=
  ⟨⟨col8, col8_apfree⟩, forced9⟩

end Erdos.Claims.E_vdw_001
