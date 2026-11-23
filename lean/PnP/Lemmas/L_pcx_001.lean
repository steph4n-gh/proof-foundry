import PnP.Core

/-
  L-pcx-001: Soundness of propositional resolution.
  Every resolution-derivable clause is satisfied by every model of φ,
  so deriving the empty clause certifies unsatisfiability.
-/
namespace PnP.Lemmas.L_pcx_001

open PnP

theorem evalCNF_clause {a : Assignment} {φ : CNF} {c : Clause}
    (hφ : evalCNF a φ = true) (hc : c ∈ φ) : evalClause a c = true := by
  unfold evalCNF at hφ
  exact List.all_eq_true.mp hφ c hc

theorem resolvent_sound {a : Assignment} {c1 c2 r : Clause} {v : Nat}
    (hr : IsResolvent c1 c2 r v)
    (h1 : evalClause a c1 = true) (h2 : evalClause a c2 = true) :
    evalClause a r = true := by
  obtain ⟨_, _, hs1, hs2, _⟩ := hr
  unfold evalClause at *
  obtain ⟨l1, hl1, he1⟩ := List.any_eq_true.mp h1
  obtain ⟨l2, hl2, he2⟩ := List.any_eq_true.mp h2
  apply List.any_eq_true.mpr
  by_cases e1 : l1 = ⟨v, true⟩
  · by_cases e2 : l2 = ⟨v, false⟩
    · subst e1; subst e2
      simp [evalLit] at he1 he2
      rw [he1] at he2
      cases he2
    · exact ⟨l2, hs2 l2 hl2 e2, he2⟩
  · exact ⟨l1, hs1 l1 hl1 e1, he1⟩

theorem derivable_sound {φ : CNF} {c : Clause} (h : ResDerivable φ c)
    (a : Assignment) (hφ : evalCNF a φ = true) : evalClause a c = true := by
  induction h with
  | axiomClause hc => exact evalCNF_clause hφ hc
  | resolve _ _ hr ih1 ih2 => exact resolvent_sound hr ih1 ih2

theorem resolution_sound (φ : CNF) (h : ResDerivable φ []) : Unsatisfiable φ := by
  intro a
  cases hv : evalCNF a φ with
  | false => rfl
  | true =>
    have := derivable_sound h a hv
    simp [evalClause] at this

end PnP.Lemmas.L_pcx_001
