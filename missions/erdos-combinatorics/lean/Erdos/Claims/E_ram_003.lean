import Erdos.Core

/-
  E-ram-003: R(3, 4) > 8 (¬ Ramsey34At 8).

  Witness: the complement of the Wagner graph (circulant C8(1, 4)), i.e. the circulant
  graph on Z/8Z with connection set {2, 3, 5, 6}. Its complement C8(1, 4) is triangle-free
  (no two of the differences {1, 4, 7} sum to a third mod 8), so the witness has no
  independent 3-set; and C8(1, 4) has independence number 3, so the witness has no K4.
  Both facts are checked exhaustively by `decide`.
-/
namespace Erdos.Claims.E_ram_003

open Erdos

/-- Circulant adjacency on Z/8Z with connection set {2, 3, 5, 6}. -/
def w8Adj (u v : Fin 8) : Bool :=
  let d := (u.val + 8 - v.val) % 8
  d == 2 || d == 3 || d == 5 || d == 6

/-- The complement of the Wagner graph C8(1, 4). -/
def W8c : SimpleGraph 8 where
  adj := w8Adj
  symm := by intro u v; revert u v; decide
  loopless := by intro v; revert v; decide

theorem w8_no_indep3 : ¬ HasIndep3 W8c := by
  rintro ⟨a, b, c, hab, hbc, hac, eab, ebc, eac⟩
  revert a b c hab hbc hac eab ebc eac; decide

theorem w8_no_k4 : ¬ HasK4 W8c := by
  rintro ⟨a, b, c, d, eab, eac, ead, ebc, ebd, ecd⟩
  revert a b c d eab eac ead ebc ebd ecd; decide

theorem ramsey34_gt_eight : ¬ Ramsey34At 8 := by
  intro h
  rcases h W8c with hi | hk
  · exact w8_no_indep3 hi
  · exact w8_no_k4 hk

end Erdos.Claims.E_ram_003
