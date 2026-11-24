import Erdos.Statements.E_sch_004

namespace Erdos.Claims.E_sch_004

private def hasConflict (c : Fin 3) : List (Fin 3) → List (Fin 3) → Bool
  | a :: as, b :: bs => (a == c && b == c) || hasConflict c as bs
  | _, _ => false

private def search : Nat → List (Fin 3) → Bool
  | 0, _ => false
  | rem + 1, rev =>
    let rev' := rev.reverse
    (hasConflict 0 rev rev' || search rem (0 :: rev)) &&
    (hasConflict 1 rev rev' || search rem (1 :: rev)) &&
    (hasConflict 2 rev rev' || search rem (2 :: rev))

private theorem hasConflict_sound (c : Fin 3) :
    ∀ (l₁ l₂ : List (Fin 3)), hasConflict c l₁ l₂ = true →
      ∃ i : Nat, ∃ (h₁ : i < l₁.length) (h₂ : i < l₂.length),
        l₁[i] = c ∧ l₂[i] = c
  | [], _, h => by simp [hasConflict] at h
  | _ :: _, [], h => by simp [hasConflict] at h
  | a :: as, b :: bs, h => by
    simp only [hasConflict, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | hrest
    · exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, rfl, rfl⟩
    · rcases hasConflict_sound c as bs hrest with ⟨i, h₁, h₂, ha, hb⟩
      exact ⟨i + 1, Nat.succ_lt_succ h₁, Nat.succ_lt_succ h₂, ha, hb⟩

private def prefixRev (col : Fin 14 → Fin 3) : (k : Nat) → k ≤ 14 → List (Fin 3)
  | 0, _ => []
  | k + 1, hk => col ⟨k, hk⟩ :: prefixRev col k (Nat.le_of_lt hk)

private theorem prefixRev_length (col : Fin 14 → Fin 3) :
    ∀ (k : Nat) (hk : k ≤ 14), (prefixRev col k hk).length = k
  | 0, _ => rfl
  | k + 1, hk => by simp [prefixRev, prefixRev_length col k (Nat.le_of_lt hk)]

private theorem prefixRev_getElem (col : Fin 14 → Fin 3) :
    ∀ (k : Nat) (hk : k ≤ 14) (i : Nat) (hi : i < (prefixRev col k hk).length),
      (prefixRev col k hk)[i] = col ⟨k - 1 - i, by rw [prefixRev_length] at hi; omega⟩
  | 0, _, i, hi => by simp [prefixRev] at hi
  | k + 1, hk, 0, _ => by simp [prefixRev]
  | k + 1, hk, i + 1, hi => by
    simp only [prefixRev, List.getElem_cons_succ]
    rw [prefixRev_getElem col k (Nat.le_of_lt hk) i (by simpa [prefixRev] using hi)]
    congr 1
    apply Fin.ext
    dsimp only
    omega

private theorem prefixRev_reverse_getElem (col : Fin 14 → Fin 3) (k : Nat) (hk : k ≤ 14)
    (i : Nat) (hi : i < (prefixRev col k hk).reverse.length) :
    (prefixRev col k hk).reverse[i] = col ⟨i, by rw [List.length_reverse, prefixRev_length] at hi; omega⟩ := by
  rw [List.getElem_reverse]
  rw [prefixRev_getElem]
  congr 1
  apply Fin.ext
  dsimp only
  rw [prefixRev_length]
  rw [List.length_reverse, prefixRev_length] at hi
  omega

private theorem search_sound (col : Fin 14 → Fin 3) (hsf : Erdos.IsSumFreeColoring 14 3 col) :
    ∀ (rem k : Nat) (hkr : k + rem = 14),
      search rem (prefixRev col k (by omega)) = true → False
  | 0, k, _, h => by simp [search] at h
  | rem + 1, k, hkr, h => by
    simp only [search, Bool.and_eq_true, Bool.or_eq_true] at h
    have hk14 : k < 14 := by omega
    let c := col ⟨k, hk14⟩
    have hc_branch :
        hasConflict c (prefixRev col k (by omega)) (prefixRev col k (by omega)).reverse = true ∨
        search rem (c :: prefixRev col k (by omega)) = true := by
      have hcval : c = 0 ∨ c = 1 ∨ c = 2 := by
        match c with
        | ⟨0, _⟩ => exact Or.inl rfl
        | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
        | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
      rcases hcval with h0 | h1 | h2
      · rw [h0]; exact h.1.1
      · rw [h1]; exact h.1.2
      · rw [h2]; exact h.2
    rcases hc_branch with hconf | hnext
    · rcases hasConflict_sound c _ _ hconf with ⟨i, h₁, h₂, ha, hb⟩
      have hi_lt : i < k := by rw [prefixRev_length] at h₁; exact h₁
      rw [prefixRev_getElem] at ha
      rw [prefixRev_reverse_getElem] at hb
      have hbad := hsf ⟨i, by omega⟩ ⟨k - 1 - i, by omega⟩ ⟨k, hk14⟩ (by dsimp only; omega)
      exact hbad ⟨hb.trans ha.symm, ha⟩
    · exact search_sound col hsf rem (k + 1) (by omega) hnext

private theorem search_14_ok : search 14 [] = true := by
  decide +kernel

theorem schur_three_forced_14 : Erdos.Statements.E_sch_004.Claim := by
  intro col hsf
  exact search_sound col hsf 14 0 rfl search_14_ok

end Erdos.Claims.E_sch_004
