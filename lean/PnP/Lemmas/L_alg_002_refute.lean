import PnP.Core

namespace PnP.Lemmas.L_alg_002_refute

def cex_cnf : CNF :=
  [[⟨0, true⟩, ⟨1, true⟩],
   [⟨0, false⟩, ⟨1, true⟩],
   [⟨1, false⟩, ⟨2, true⟩],
   [⟨3, true⟩, ⟨2, false⟩],
   [⟨3, false⟩, ⟨2, false⟩]]

def varOcc (cnf : CNF) (v : Nat) : Nat :=
  (cnf.flatten.filter fun literal => literal.var == v).length

theorem counterexample :
    (∀ c ∈ cex_cnf, 2 ≤ c.length ∧ c.length ≤ 3) ∧
    (∀ v, varOcc cex_cnf v ≤ 3) ∧ Unsatisfiable cex_cnf := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp [cex_cnf] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v
    rcases v with _ | _ | _ | _ | v
    all_goals simp [varOcc, cex_cnf, List.flatten, List.filter]
  · intro a
    cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;> cases h3 : a 3 <;>
      simp [cex_cnf, evalCNF, evalClause, evalLit, h0, h1, h2, h3]

end PnP.Lemmas.L_alg_002_refute
