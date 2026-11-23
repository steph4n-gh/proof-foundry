import PnP.Core

/-
  L-alg-001: Every Horn CNF in which every clause has at least one negative
  literal (i.e. no positive unit clauses) is satisfied by the all-false assignment.
-/
namespace PnP.Lemmas.L_alg_001

theorem horn_no_positive_unit_sat (φ : CNF) (hHorn : IsHornCNF φ = true)
    (hNeg : ∀ c ∈ φ, c.any (fun l => !l.pos) = true) : Satisfiable φ := by
  have _ := hHorn
  refine ⟨fun _ => false, ?_⟩
  rw [evalCNF, List.all_eq_true]
  intro c hc
  have hLit : evalLit (fun _ => false) = fun l => !l.pos := by
    funext l
    cases h : l.pos <;> simp [evalLit, h]
  rw [evalClause, hLit]
  exact hNeg c hc

end PnP.Lemmas.L_alg_001
