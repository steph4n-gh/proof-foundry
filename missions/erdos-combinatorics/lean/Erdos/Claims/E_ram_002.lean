import Erdos.Core

/-
  E-ram-002: Ramsey's Theorem R(3, 3) ≤ 6 — every simple graph on 6 vertices contains
  a triangle or a 3-element independent set (Ramsey33At 6).

  Proof: fix vertex 0. By pigeonhole, three of the five vertices 1..5 share the same
  adjacency value to 0. If they are all neighbours of 0, any edge among them closes a
  triangle with 0, otherwise they are pairwise non-adjacent. If they are all
  non-neighbours of 0, any non-edge among them gives an independent triple with 0,
  otherwise they span a triangle.
-/
namespace Erdos.Claims.E_ram_002

open Erdos

/-- Three vertices `x, y, z` sharing the same adjacency value to a fourth vertex `a`
    force either a triangle or an independent 3-set. -/
theorem triangle_or_indep3_of_monochromatic {n : Nat} (G : SimpleGraph n) (a x y z : Fin n)
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h₁ : G.adj a x = G.adj a y) (h₂ : G.adj a y = G.adj a z) :
    HasTriangle G ∨ HasIndep3 G := by
  cases hy : G.adj a y with
  | true =>
    have hx : G.adj a x = true := h₁.trans hy
    have hz : G.adj a z = true := h₂.symm.trans hy
    cases exy : G.adj x y with
    | true => exact Or.inl ⟨a, x, y, hx, exy, hy⟩
    | false =>
      cases eyz : G.adj y z with
      | true => exact Or.inl ⟨a, y, z, hy, eyz, hz⟩
      | false =>
        cases exz : G.adj x z with
        | true => exact Or.inl ⟨a, x, z, hx, exz, hz⟩
        | false => exact Or.inr ⟨x, y, z, hxy, hyz, hxz, exy, eyz, exz⟩
  | false =>
    have hx : G.adj a x = false := h₁.trans hy
    have hz : G.adj a z = false := h₂.symm.trans hy
    cases exy : G.adj x y with
    | false => exact Or.inr ⟨a, x, y, hax, hxy, hay, hx, exy, hy⟩
    | true =>
      cases eyz : G.adj y z with
      | false => exact Or.inr ⟨a, y, z, hay, hyz, haz, hy, eyz, hz⟩
      | true =>
        cases exz : G.adj x z with
        | false => exact Or.inr ⟨a, x, z, hax, hxz, haz, hx, exz, hz⟩
        | true => exact Or.inl ⟨x, y, z, exy, eyz, exz⟩

/-- Pigeonhole for five Booleans: some three of them are equal. -/
theorem three_equal_of_five (b₁ b₂ b₃ b₄ b₅ : Bool) :
    (b₁ = b₂ ∧ b₂ = b₃) ∨ (b₁ = b₂ ∧ b₂ = b₄) ∨ (b₁ = b₂ ∧ b₂ = b₅) ∨
    (b₁ = b₃ ∧ b₃ = b₄) ∨ (b₁ = b₃ ∧ b₃ = b₅) ∨ (b₁ = b₄ ∧ b₄ = b₅) ∨
    (b₂ = b₃ ∧ b₃ = b₄) ∨ (b₂ = b₃ ∧ b₃ = b₅) ∨ (b₂ = b₄ ∧ b₄ = b₅) ∨
    (b₃ = b₄ ∧ b₄ = b₅) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;> decide

theorem ramsey33_le_six : Ramsey33At 6 := by
  intro G
  have key := triangle_or_indep3_of_monochromatic G 0
  rcases three_equal_of_five (G.adj 0 1) (G.adj 0 2) (G.adj 0 3) (G.adj 0 4) (G.adj 0 5) with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂
  · exact key 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h₁ h₂

end Erdos.Claims.E_ram_002
