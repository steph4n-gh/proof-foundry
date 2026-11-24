import Erdos.Statements.E_erd156_004

namespace Erdos.Claims.E_erd156_004

private def witness : List Nat := [1, 4, 11, 15, 17]

private theorem witness_sidon : Erdos.IsSidon witness := by
  unfold Erdos.IsSidon witness
  decide

private theorem witness_maximal :
    ∀ k : Fin 30, (k.val + 1) ∉ witness → ¬ Erdos.IsSidon ((k.val + 1) :: witness) := by
  unfold Erdos.IsSidon witness
  decide +kernel

theorem maximal_sidon_30_len5 : Erdos.Statements.E_erd156_004.Claim := by
  refine ⟨witness, rfl, by decide, by unfold Erdos.SubsetOfRange witness; decide, witness_sidon, ?_⟩
  intro x hx1 hx30 hxnot
  have h := witness_maximal ⟨x - 1, by omega⟩ (by simpa [Nat.sub_add_cancel hx1] using hxnot)
  simpa [Nat.sub_add_cancel hx1] using h

end Erdos.Claims.E_erd156_004
