import Erdos.Core

/-
  E-erd156-001: Erdős Problem #156 Blocking Lemma.
  If A is a maximal Sidon subset of {1, ..., N}, then every x ∈ {1, ..., N} \ A
  satisfies either x + a = b + c or x + x = a + b for some a, b, c ∈ A.
-/
namespace Erdos.Claims.E_erd156_001

private def decidableExistsMem {α : Type} (l : List α) (P : α → Prop) [hP : ∀ x, Decidable (P x)] :
    Decidable (∃ x ∈ l, P x) :=
  match l with
  | [] => isFalse (by intro ⟨x, hx, _⟩; exact List.not_mem_nil hx)
  | y :: ys =>
    match hP y with
    | isTrue hy => isTrue ⟨y, List.mem_cons_self, hy⟩
    | isFalse hny =>
      match decidableExistsMem ys P with
      | isTrue hys => isTrue (by rcases hys with ⟨x, hx, hpx⟩; exact ⟨x, List.mem_cons_of_mem y hx, hpx⟩)
      | isFalse hnys =>
        isFalse (by
          intro ⟨x, hx, hpx⟩
          rcases List.mem_cons.mp hx with rfl | hxs
          · exact hny hpx
          · exact hnys ⟨x, hxs, hpx⟩)

private instance (l : List Nat) (P : Nat → Prop) [∀ x, Decidable (P x)] :
    Decidable (∃ x ∈ l, P x) :=
  decidableExistsMem l P

theorem maximal_sidon_blocking (N : Nat) (A : List Nat) (x : Nat)
    (hmax : IsMaximalSidon N A) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hnot : x ∉ A) :
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x + a = b + c) ∨ (∃ a ∈ A, ∃ b ∈ A, x + x = a + b) := by
  apply Decidable.byContradiction
  intro hno
  have h1 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, x + a ≠ b + c := by
    intro a ha b hb c hc heq
    exact hno (Or.inl ⟨a, ha, b, hb, c, hc, heq⟩)
  have h2 : ∀ a ∈ A, ∀ b ∈ A, x + x ≠ a + b := by
    intro a ha b hb heq
    exact hno (Or.inr ⟨a, ha, b, hb, heq⟩)
  have hsid : IsSidon A := hmax.2.2.1
  have hnot_sid : ¬ IsSidon (x :: A) := hmax.2.2.2 x hx1 hxN hnot
  apply hnot_sid
  intro a ha b hb c hc d hd hab hcd hsum
  rcases List.mem_cons.mp ha with ha' | ha' <;>
  rcases List.mem_cons.mp hb with hb' | hb' <;>
  rcases List.mem_cons.mp hc with hc' | hc' <;>
  rcases List.mem_cons.mp hd with hd' | hd'
  · exact ⟨by omega, by omega⟩
  · exact absurd ((show d = x by omega) ▸ hd') hnot
  · exact absurd ((show c = x by omega) ▸ hc') hnot
  · exact absurd (by omega : x + x = c + d) (h2 c hc' d hd')
  · exact absurd ((show b = x by omega) ▸ hb') hnot
  · exact ⟨by omega, by omega⟩
  · exact absurd ((show b = x by omega) ▸ hb') hnot
  · exact absurd (by omega : x + b = c + d) (h1 b hb' c hc' d hd')
  · exact absurd ((show a = x by omega) ▸ ha') hnot
  · exact absurd ((show a = x by omega) ▸ ha') hnot
  · exact ⟨by omega, by omega⟩
  · exact absurd (by omega : x + a = c + d) (h1 a ha' c hc' d hd')
  · exact absurd (by omega : x + x = a + b) (h2 a ha' b hb')
  · exact absurd (by omega : x + d = a + b) (h1 d hd' a ha' b hb')
  · exact absurd (by omega : x + c = a + b) (h1 c hc' a ha' b hb')
  · exact hsid a ha' b hb' c hc' d hd' hab hcd hsum

end Erdos.Claims.E_erd156_001
