import Erdos.Core

namespace Erdos.Claims.E_erd128_002

private def cycleAdj (u v : Fin 5) : Bool :=
  let d := (u.val + 5 - v.val) % 5
  d == 1 || d == 4

private def cycleFive : SimpleGraph 5 where
  adj := cycleAdj
  symm := by
    intro u v
    revert u v
    decide
  loopless := by
    intro v
    revert v
    decide

theorem c5_erdos128_witness : ∃ G : SimpleGraph 5, ¬ HasTriangle G ∧ HasSparseHalf G := by
  refine ⟨cycleFive, ?_, ?_⟩
  · rintro ⟨a, b, c, hab, hbc, hac⟩
    revert a b c hab hbc hac
    decide
  · refine ⟨fun v => v == 0 || v == 2, ?_, ?_⟩ <;> decide

end Erdos.Claims.E_erd128_002
