import PnP.Core

/-
  L-pcx-004: PHP(n+1, n) is unsatisfiable for every n.
  Route: extract a hole function from a satisfying assignment, then apply the
  finite pigeonhole principle (no injective map {0..n} → {0..n-1}) by induction.
-/
namespace PnP.Lemmas.L_pcx_004

open PnP

/-- Finite pigeonhole on `Nat`-valued functions, by induction on `n`. -/
theorem no_injection : ∀ (n : Nat) (f : Nat → Nat),
    (∀ p, p < n + 1 → f p < n) →
    (∀ p q, p < n + 1 → q < n + 1 → f p = f q → p = q) → False
  | 0, f, hf, _ => by have := hf 0 (by omega); omega
  | n + 1, f, hf, hinj => by
    refine no_injection n (fun p => if f p = n then f (n + 1) else f p) ?_ ?_
    · intro p hp
      have hfp := hf p (by omega)
      have hlast := hf (n + 1) (by omega)
      by_cases h : f p = n
      · have hne : f (n + 1) ≠ n := by
          intro h2
          have := hinj p (n + 1) (by omega) (by omega) (by omega)
          omega
        simp only [h, ite_true]; omega
      · simp only [h, ite_false]; omega
    · intro p q hp hq hpq
      have hfp := hf p (by omega)
      have hfq := hf q (by omega)
      have hlast := hf (n + 1) (by omega)
      by_cases h1 : f p = n <;> by_cases h2 : f q = n <;> simp only [h1, h2, ite_true, ite_false] at hpq
      · exact hinj p q (by omega) (by omega) (by omega)
      · have := hinj q (n + 1) (by omega) (by omega) (by omega)
        omega
      · have := hinj p (n + 1) (by omega) (by omega) (by omega)
        omega
      · exact hinj p q (by omega) (by omega) hpq

theorem php_succ_unsat (n : Nat) : Unsatisfiable (PHP (n + 1) n) := by
  intro a
  cases hsat : evalCNF a (PHP (n + 1) n)
  · rfl
  exfalso
  have hall : ∀ c ∈ PHP (n + 1) n, evalClause a c = true := by
    intro c hc
    exact List.all_eq_true.mp hsat c hc
  -- pigeon clauses: every pigeon sits in some hole
  have hpig : ∀ p, p < n + 1 → ∃ h, h < n ∧ a (phpVar n p h) = true := by
    intro p hp
    have hc := hall (phpPigeonClause n p) (by
      unfold PHP
      exact List.mem_append_left _ (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩))
    unfold evalClause phpPigeonClause at hc
    obtain ⟨l, hl, hl2⟩ := List.any_eq_true.mp hc
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hl
    exact ⟨h, List.mem_range.mp hh, by simpa [evalLit] using hl2⟩
  -- hole clauses: no two pigeons share a hole
  have hhole : ∀ p1 p2 h, p1 < p2 → p2 < n + 1 → h < n →
      a (phpVar n p1 h) = true → a (phpVar n p2 h) = true → False := by
    intro p1 p2 h h12 hp2 hh ha1 ha2
    have hc := hall [⟨phpVar n p1 h, false⟩, ⟨phpVar n p2 h, false⟩] (by
      unfold PHP
      refine List.mem_append_right _ ?_
      unfold phpHoleClauses
      refine List.mem_flatMap.mpr ⟨h, List.mem_range.mpr hh, ?_⟩
      refine List.mem_flatMap.mpr ⟨p1, List.mem_range.mpr (by omega), ?_⟩
      refine List.mem_filterMap.mpr ⟨p2, List.mem_range.mpr hp2, ?_⟩
      simp [h12])
    simp [evalClause, evalLit, ha1, ha2] at hc
  -- choose a hole function and derive an injection
  have hch : ∀ p, ∃ h, p < n + 1 → h < n ∧ a (phpVar n p h) = true := by
    intro p
    by_cases hp : p < n + 1
    · obtain ⟨h, hh⟩ := hpig p hp
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  let f : Nat → Nat := fun p => Classical.choose (hch p)
  have hf : ∀ p, p < n + 1 → f p < n ∧ a (phpVar n p (f p)) = true :=
    fun p => Classical.choose_spec (hch p)
  refine no_injection n f (fun p hp => (hf p hp).1) ?_
  intro p q hp hq hpq
  refine Classical.byContradiction fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hhole p q (f p) hlt hq (hf p hp).1 (hf p hp).2 (hpq ▸ (hf q hq).2)
  · exact hhole q p (f q) hlt hp (hf q hq).1 (hf q hq).2 (hpq ▸ (hf p hp).2)

end PnP.Lemmas.L_pcx_004
