import Erdos.Statements.E_sch_005

namespace Erdos.Claims.E_sch_005

private def coloring : Fin 44 → Fin 4
  | ⟨0, _⟩  => 1 | ⟨1, _⟩  => 2 | ⟨2, _⟩  => 0 | ⟨3, _⟩  => 0
  | ⟨4, _⟩  => 1 | ⟨5, _⟩  => 2 | ⟨6, _⟩  => 2 | ⟨7, _⟩  => 1
  | ⟨8, _⟩  => 0 | ⟨9, _⟩  => 2 | ⟨10, _⟩ => 2 | ⟨11, _⟩ => 1
  | ⟨12, _⟩ => 3 | ⟨13, _⟩ => 0 | ⟨14, _⟩ => 1 | ⟨15, _⟩ => 0
  | ⟨16, _⟩ => 3 | ⟨17, _⟩ => 3 | ⟨18, _⟩ => 1 | ⟨19, _⟩ => 3
  | ⟨20, _⟩ => 3 | ⟨21, _⟩ => 3 | ⟨22, _⟩ => 3 | ⟨23, _⟩ => 3
  | ⟨24, _⟩ => 3 | ⟨25, _⟩ => 2 | ⟨26, _⟩ => 3 | ⟨27, _⟩ => 3
  | ⟨28, _⟩ => 3 | ⟨29, _⟩ => 2 | ⟨30, _⟩ => 0 | ⟨31, _⟩ => 3
  | ⟨32, _⟩ => 1 | ⟨33, _⟩ => 2 | ⟨34, _⟩ => 2 | ⟨35, _⟩ => 0
  | ⟨36, _⟩ => 1 | ⟨37, _⟩ => 2 | ⟨38, _⟩ => 2 | ⟨39, _⟩ => 1
  | ⟨40, _⟩ => 0 | ⟨41, _⟩ => 0 | ⟨42, _⟩ => 0 | ⟨43, _⟩ => 1
  | ⟨_, _⟩  => 0

private theorem coloring_check :
    ∀ x y : Fin 44, (hz : x.val + y.val + 1 < 44) →
      ¬ (coloring x = coloring y ∧ coloring y = coloring ⟨x.val + y.val + 1, hz⟩) := by
  decide +kernel

theorem schur_four_ge_44 : Erdos.Statements.E_sch_005.Claim := by
  refine ⟨coloring, ?_⟩
  intro x y z hsum
  have hzval : z.val = x.val + y.val + 1 := by omega
  have hzlt : x.val + y.val + 1 < 44 := hzval ▸ z.isLt
  have hzeq : z = ⟨x.val + y.val + 1, hzlt⟩ := Fin.ext hzval
  rw [hzeq]
  exact coloring_check x y hzlt

end Erdos.Claims.E_sch_005
