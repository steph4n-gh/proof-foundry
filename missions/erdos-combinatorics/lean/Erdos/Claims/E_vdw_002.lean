import Erdos.Statements.E_vdw_002

namespace Erdos.Claims.E_vdw_002

private def coloring : Fin 26 → Fin 3
  | ⟨0, _⟩  => 0 | ⟨1, _⟩  => 0 | ⟨2, _⟩  => 1 | ⟨3, _⟩  => 1
  | ⟨4, _⟩  => 0 | ⟨5, _⟩  => 0 | ⟨6, _⟩  => 1 | ⟨7, _⟩  => 2
  | ⟨8, _⟩  => 1 | ⟨9, _⟩  => 2 | ⟨10, _⟩ => 2 | ⟨11, _⟩ => 0
  | ⟨12, _⟩ => 2 | ⟨13, _⟩ => 0 | ⟨14, _⟩ => 0 | ⟨15, _⟩ => 1
  | ⟨16, _⟩ => 0 | ⟨17, _⟩ => 1 | ⟨18, _⟩ => 1 | ⟨19, _⟩ => 2
  | ⟨20, _⟩ => 0 | ⟨21, _⟩ => 2 | ⟨22, _⟩ => 2 | ⟨23, _⟩ => 1
  | ⟨24, _⟩ => 2 | ⟨25, _⟩ => 1 | ⟨_, _⟩ => 0

private theorem coloring_check :
    ∀ x y : Fin 26, x.val < y.val → (hz : 2 * y.val - x.val < 26) →
      ¬ (coloring x = coloring y ∧ coloring y = coloring ⟨2 * y.val - x.val, hz⟩) := by
  decide +kernel

theorem vdw_3_3_3_gt_26 : Erdos.Statements.E_vdw_002.Claim := by
  refine ⟨coloring, ?_⟩
  intro x y z hxy hsum
  have hzval : z.val = 2 * y.val - x.val := by omega
  have hzlt : 2 * y.val - x.val < 26 := hzval ▸ z.isLt
  have hzeq : z = ⟨2 * y.val - x.val, hzlt⟩ := Fin.ext hzval
  rw [hzeq]
  exact coloring_check x y hxy hzlt

end Erdos.Claims.E_vdw_002
