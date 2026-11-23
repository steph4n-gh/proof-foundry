import PnP.Core

/-
  L-pcx-003: If every axiom clause has width ≥ 2, any resolution refutation
  has size ≥ 3 (the empty clause cannot be a leaf, so the root is a resolution
  step with two subproofs of size ≥ 1 each).
  Note: 5 ≤ size is FALSE for list-clauses: φ = [[x,x],[¬x,¬x]] has a size-3 refutation.
-/
namespace PnP.Lemmas.L_pcx_003

open PnP

theorem size_pos {φ : CNF} {c : Clause} (p : ResProof φ c) : 1 ≤ p.size := by
  cases p <;> simp [ResProof.size] <;> omega

theorem resolution_min_size_ge_three (φ : CNF) (p : ResProof φ [])
    (hlen : ∀ c ∈ φ, 2 ≤ c.length) : 3 ≤ p.size := by
  match p with
  | .leaf h => have := hlen _ h; simp at this
  | .step p1 p2 _ =>
    have := size_pos p1
    have := size_pos p2
    simp only [ResProof.size]
    omega

/-- Tightness witness: the bound 3 is attained, so `5 ≤ size` is not provable in general. -/
def tightCNF : CNF := [[⟨0, true⟩, ⟨0, true⟩], [⟨0, false⟩, ⟨0, false⟩]]

def tightProof : ResProof tightCNF [] :=
  .step (c1 := [⟨0, true⟩, ⟨0, true⟩]) (c2 := [⟨0, false⟩, ⟨0, false⟩]) (v := 0)
    (.leaf (by simp [tightCNF])) (.leaf (by simp [tightCNF]))
    ⟨by simp, by simp, by simp, by simp, by simp⟩

theorem tight_size : tightProof.size = 3 := rfl

theorem tight_hlen : ∀ c ∈ tightCNF, 2 ≤ c.length := by
  intro c hc; simp [tightCNF] at hc; rcases hc with rfl | rfl <;> simp

end PnP.Lemmas.L_pcx_003
