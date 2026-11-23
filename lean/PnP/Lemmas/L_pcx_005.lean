import PnP.Core

/-
  L-pcx-005 (Ben-Sasson–Wigderson restriction lemma, qualitative form):
  restricting a resolution refutation by a variable assignment `v := b`
  yields a resolution refutation of the restricted CNF.
  Invariant: every derived clause is either satisfied by `v := b`, or has a
  derivable subclause (over the restricted CNF) all of whose literals are
  literals of the original clause on variables other than `v`.
-/
namespace PnP.Lemmas.L_pcx_005

open PnP

/-- The clause is satisfied by `v := b`. -/
def Sat (v : Nat) (b : Bool) (c : Clause) : Prop :=
  ∃ l ∈ c, l.var = v ∧ l.pos = b

theorem restrictClause_none_iff (v : Nat) (b : Bool) (c : Clause) :
    restrictClause v b c = none ↔ Sat v b c := by
  unfold restrictClause Sat
  by_cases h : c.any (fun l => l.var == v && l.pos == b) = true
  · simp only [h, ite_true, true_iff]
    obtain ⟨l, hl, hl2⟩ := List.any_eq_true.mp h
    exact ⟨l, hl, by simpa using hl2⟩
  · simp only [h]
    constructor
    · intro h'; cases h'
    · rintro ⟨l, hl, h1, h2⟩
      exact absurd (List.any_eq_true.mpr ⟨l, hl, by simp [h1, h2]⟩) h

/-- Main invariant. -/
theorem invariant (φ : CNF) (v : Nat) (b : Bool) {c : Clause} (h : ResDerivable φ c) :
    Sat v b c ∨ ∃ c', (∀ l ∈ c', l ∈ c ∧ l.var ≠ v) ∧ ResDerivable (restrictCNF v b φ) c' := by
  induction h with
  | axiomClause hc =>
    rename_i c
    by_cases hs : Sat v b c
    · exact Or.inl hs
    · right
      refine ⟨c.filter (fun l => l.var != v), ?_, ?_⟩
      · intro l hl
        have := List.mem_filter.mp hl
        exact ⟨this.1, by simpa using this.2⟩
      · apply ResDerivable.axiomClause
        unfold restrictCNF
        refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
        have : restrictClause v b c ≠ none := fun h => hs ((restrictClause_none_iff v b c).mp h)
        unfold restrictClause at this ⊢
        by_cases h2 : c.any (fun l => l.var == v && l.pos == b) = true
        · simp [h2] at this
        · simp [h2]
  | @resolve c1 c2 r u h1 h2 hr ih1 ih2 =>
    obtain ⟨hu1, hu2, hr1, hr2, hr3⟩ := hr
    rcases ih1 with s1 | ⟨c1', h1sub, h1d⟩
    · -- c1 satisfied by v := b
      obtain ⟨l1, hl1, hv1, hb1⟩ := s1
      by_cases hl : l1 = ⟨u, true⟩
      · subst hl
        simp only at hv1 hb1
        subst hv1; subst hb1
        rcases ih2 with s2 | ⟨c2', h2sub, h2d⟩
        · obtain ⟨l2, hl2, hv2, hb2⟩ := s2
          left
          refine ⟨l2, hr2 l2 hl2 ?_, hv2, hb2⟩
          intro e; subst e; simp at hb2
        · right
          refine ⟨c2', ?_, h2d⟩
          intro l hl
          obtain ⟨hlc, hlv⟩ := h2sub l hl
          refine ⟨hr2 l hlc ?_, hlv⟩
          intro e; subst e; exact hlv rfl
      · left
        exact ⟨l1, hr1 l1 hl1 hl, hv1, hb1⟩
    · rcases ih2 with s2 | ⟨c2', h2sub, h2d⟩
      · obtain ⟨l2, hl2, hv2, hb2⟩ := s2
        by_cases hl : l2 = ⟨u, false⟩
        · subst hl
          simp only at hv2 hb2
          subst hv2; subst hb2
          right
          refine ⟨c1', ?_, h1d⟩
          intro l hl
          obtain ⟨hlc, hlv⟩ := h1sub l hl
          refine ⟨hr1 l hlc ?_, hlv⟩
          intro e; subst e; exact hlv rfl
        · left
          exact ⟨l2, hr2 l2 hl2 hl, hv2, hb2⟩
      · right
        by_cases p1 : (⟨u, true⟩ : Literal) ∈ c1'
        · by_cases p2 : (⟨u, false⟩ : Literal) ∈ c2'
          · refine ⟨c1'.filter (fun l => l ≠ ⟨u, true⟩) ++ c2'.filter (fun l => l ≠ ⟨u, false⟩), ?_, ?_⟩
            · intro l hl
              rcases List.mem_append.mp hl with hl | hl
              · obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
                have hne' : l ≠ ⟨u, true⟩ := by simpa using hne
                obtain ⟨hlc, hlv⟩ := h1sub l hl
                exact ⟨hr1 l hlc hne', hlv⟩
              · obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
                have hne' : l ≠ ⟨u, false⟩ := by simpa using hne
                obtain ⟨hlc, hlv⟩ := h2sub l hl
                exact ⟨hr2 l hlc hne', hlv⟩
            · refine ResDerivable.resolve (v := u) h1d h2d ⟨p1, p2, ?_, ?_, ?_⟩
              · intro l hl hne
                exact List.mem_append_left _ (List.mem_filter.mpr ⟨hl, by simpa using hne⟩)
              · intro l hl hne
                exact List.mem_append_right _ (List.mem_filter.mpr ⟨hl, by simpa using hne⟩)
              · intro l hl
                rcases List.mem_append.mp hl with hl | hl
                · obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
                  exact Or.inl ⟨hl, by simpa using hne⟩
                · obtain ⟨hl, hne⟩ := List.mem_filter.mp hl
                  exact Or.inr ⟨hl, by simpa using hne⟩
          · refine ⟨c2', ?_, h2d⟩
            intro l hl
            obtain ⟨hlc, hlv⟩ := h2sub l hl
            refine ⟨hr2 l hlc ?_, hlv⟩
            intro e; subst e; exact p2 hl
        · refine ⟨c1', ?_, h1d⟩
          intro l hl
          obtain ⟨hlc, hlv⟩ := h1sub l hl
          refine ⟨hr1 l hlc ?_, hlv⟩
          intro e; subst e; exact p1 hl

theorem resolution_restrict_preserves_refutation (φ : CNF) (v : Nat) (b : Bool)
    (h : ResDerivable φ []) : ResDerivable (restrictCNF v b φ) [] := by
  rcases invariant φ v b h with hs | ⟨c', hsub, hd⟩
  · obtain ⟨l, hl, _⟩ := hs
    simp at hl
  · have : c' = [] := by
      cases c' with
      | nil => rfl
      | cons l t => exact absurd (hsub l (by simp)).1 (by simp)
    subst this
    exact hd

end PnP.Lemmas.L_pcx_005
