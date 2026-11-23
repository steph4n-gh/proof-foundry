import Erdos.Core

/-
  E-ram-001: Warmup witness — the 5-cycle C5 has no triangle and no 3-independent set,
  proving R(3, 3) > 5 (i.e. ¬ Ramsey33At 5).
-/
namespace Erdos.Claims.E_ram_001

def c5Adj (u v : Fin 5) : Bool :=
  let d := (u.val + 5 - v.val) % 5
  d == 1 || d == 4

def C5 : SimpleGraph 5 where
  adj := c5Adj
  symm := by intro u v; revert u v; decide
  loopless := by intro v; revert v; decide

theorem ramsey33_gt_five : ¬ Ramsey33At 5 := by
  intro h
  rcases h C5 with ⟨a, b, c, hab, hbc, hac⟩ | ⟨a, b, c, hne1, hne2, hne3, hab, hbc, hac⟩
  · revert a b c hab hbc hac; decide
  · revert a b c hne1 hne2 hne3 hab hbc hac; decide

end Erdos.Claims.E_ram_001
