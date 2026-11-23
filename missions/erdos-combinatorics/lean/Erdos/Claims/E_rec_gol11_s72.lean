import Erdos.Statements.E_rec_gol11

namespace Erdos.Claims.E_rec_gol11_s72

theorem record : Erdos.Statements.E_rec_gol11.Record 72 := by
  refine ⟨[0, 1, 4, 13, 28, 33, 47, 54, 64, 70, 72], by decide, ?_, by decide⟩
  unfold Erdos.IsGolombRuler
  decide +kernel

end Erdos.Claims.E_rec_gol11_s72
