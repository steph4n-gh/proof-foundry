import Erdos.Statements.E_erd156_005

namespace Erdos.Claims.E_erd156_005

private theorem mem_erase_of_ne {x y : Nat} (hne : y ≠ x) :
    ∀ {l : List Nat}, y ∈ l → y ∈ l.erase x
  | [], h => absurd h (List.not_mem_nil)
  | a :: as, h => by
    by_cases hax : a = x
    · subst hax
      simp only [List.erase_cons_head]
      rcases List.mem_cons.mp h with rfl | hy
      · exact absurd rfl hne
      · exact hy
    · have hbeq : (a == x) = false := beq_false_of_ne hax
      simp only [List.erase_cons, hbeq]
      rcases List.mem_cons.mp h with rfl | hy
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem a (mem_erase_of_ne hne hy)

private theorem nodup_subset_length_le :
    ∀ (L C : List Nat), L.Nodup → (∀ x ∈ L, x ∈ C) → L.length ≤ C.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, C, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxC : x ∈ C := hsub x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, y ∈ C.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hnd.1 (h ▸ hy)
      exact mem_erase_of_ne hne (hsub y (List.mem_cons_of_mem x hy))
    have hIH := nodup_subset_length_le xs (C.erase x) hnd.2 hxs
    have hlen := List.length_erase_of_mem hxC
    have hpos : 0 < C.length := List.length_pos_of_mem hxC
    simp only [List.length_cons]
    omega

private theorem blocked_by_sidon {A : List Nat} (hsid : Erdos.IsSidon A)
    {x : Nat} (hxnot : x ∉ A) (hnotsid : ¬ Erdos.IsSidon (x :: A)) :
    (∃ c ∈ A, ∃ d ∈ A, c < d ∧ 2 * x = c + d) ∨
    (∃ c ∈ A, ∃ u ∈ A, x + u = 2 * c) ∨
    (∃ c ∈ A, ∃ d ∈ A, ∃ u ∈ A, c < d ∧ x + u = c + d) := by
  have hne : ∃ a ∈ x :: A, ∃ b ∈ x :: A, ∃ c ∈ x :: A, ∃ d ∈ x :: A,
      a ≤ b ∧ c ≤ d ∧ a + b = c + d ∧ ¬ (a = c ∧ b = d) := by
    by_cases h : ∃ a ∈ x :: A, ∃ b ∈ x :: A, ∃ c ∈ x :: A, ∃ d ∈ x :: A,
        a ≤ b ∧ c ≤ d ∧ a + b = c + d ∧ ¬ (a = c ∧ b = d)
    · exact h
    · exfalso
      apply hnotsid
      intro a ha b hb c hc d hd hab hcd hsum
      by_cases heq : a = c ∧ b = d
      · exact heq
      · exact absurd ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hsum, heq⟩ h
  rcases hne with ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hsum, hneq⟩
  have side_case : ∀ {p q r s : Nat},
      (p = x ∨ q = x) → r ∈ A → s ∈ A → p ∈ x :: A → q ∈ x :: A →
      p ≤ q → r ≤ s → p + q = r + s →
      (∃ u ∈ A, ∃ v ∈ A, u < v ∧ 2 * x = u + v) ∨
      (∃ u ∈ A, ∃ w ∈ A, x + w = 2 * u) ∨
      (∃ u ∈ A, ∃ v ∈ A, ∃ w ∈ A, u < v ∧ x + w = u + v) := by
    intro p q r s hpq hr hs hp hq _ hrs hps
    have hboth : p = x ∧ q = x → ∃ u ∈ A, ∃ v ∈ A, u < v ∧ 2 * x = u + v := by
      intro ⟨hp1, hq1⟩
      have h2x : 2 * x = r + s := by omega
      have hlt : r < s := by
        by_cases heq : r = s
        · have hxr : x = r := by omega
          exact absurd (hxr ▸ hr) hxnot
        · omega
      exact ⟨r, hr, s, hs, hlt, h2x⟩
    have hone : ∀ w ∈ A, x + w = r + s →
        (∃ u ∈ A, ∃ w' ∈ A, x + w' = 2 * u) ∨
        (∃ u ∈ A, ∃ v ∈ A, ∃ w' ∈ A, u < v ∧ x + w' = u + v) := by
      intro w hw hxw
      by_cases hreq : r = s
      · subst hreq
        exact Or.inl ⟨r, hr, w, hw, by omega⟩
      · exact Or.inr ⟨r, hr, s, hs, w, hw, by omega, hxw⟩
    rcases hpq with rfl | rfl
    · rcases List.mem_cons.mp hq with rfl | hqA
      · exact Or.inl (hboth ⟨rfl, rfl⟩)
      · exact Or.inr (hone q hqA hps)
    · rcases List.mem_cons.mp hp with rfl | hpA
      · exact Or.inl (hboth ⟨rfl, rfl⟩)
      · exact Or.inr (hone p hpA (by omega))
  rcases List.mem_cons.mp ha with rfl | haA
  · rcases List.mem_cons.mp hc with hcx | hcA
    · exfalso; apply hneq; omega
    · rcases List.mem_cons.mp hd with hdx | hdA
      · exfalso; apply hneq; omega
      · exact side_case (Or.inl rfl) hcA hdA (List.mem_cons_self ..) hb hab hcd hsum
  · rcases List.mem_cons.mp hb with rfl | hbA
    · rcases List.mem_cons.mp hc with hcx | hcA
      · exfalso; apply hneq; omega
      · rcases List.mem_cons.mp hd with hdx | hdA
        · exfalso; apply hneq; omega
        · exact side_case (Or.inr rfl) hcA hdA (List.mem_cons_of_mem _ haA) (List.mem_cons_self ..) hab hcd hsum
    · rcases List.mem_cons.mp hc with rfl | hcA
      · exact side_case (Or.inl rfl) haA hbA (List.mem_cons_self ..) hd hcd hab hsum.symm
      · rcases List.mem_cons.mp hd with rfl | hdA
        · exact side_case (Or.inr rfl) haA hbA (List.mem_cons_of_mem _ hcA) (List.mem_cons_self ..) hcd hab hsum.symm
        · exact absurd (hsid a haA b hbA c hcA d hdA hab hcd hsum) hneq

private def unorderedPairs : List Nat → List (Nat × Nat)
  | [] => []
  | a :: as => as.map (fun b => (a, b)) ++ unorderedPairs as

private theorem unorderedPairs_length :
    ∀ A : List Nat, 2 * (unorderedPairs A).length = A.length * (A.length - 1)
  | [] => rfl
  | a :: as => by
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons]
    have ih := unorderedPairs_length as
    cases h : as.length with
    | zero => simp [h] at ih ⊢; omega
    | succ m =>
      rw [h] at ih
      simp only [Nat.add_sub_cancel] at ih ⊢
      have : (m + 1 + 1) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by
        rw [Nat.add_mul (m + 1) 1 (m + 1), Nat.one_mul, Nat.mul_add (m + 1) m 1, Nat.mul_one]
        omega
      omega

private theorem mem_unorderedPairs {c d : Nat} (hne : c ≠ d) :
    ∀ {A : List Nat}, c ∈ A → d ∈ A →
      (c, d) ∈ unorderedPairs A ∨ (d, c) ∈ unorderedPairs A
  | [], hc, _ => absurd hc (List.not_mem_nil)
  | a :: as, hc, hd => by
    simp only [unorderedPairs, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp hc with rfl | hcas
    · rcases List.mem_cons.mp hd with rfl | hdas
      · exact absurd rfl hne
      · exact Or.inl (Or.inl ⟨d, hdas, rfl⟩)
    · rcases List.mem_cons.mp hd with rfl | hdas
      · exact Or.inr (Or.inl ⟨c, hcas, rfl⟩)
      · rcases mem_unorderedPairs hne hcas hdas with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

private theorem flatMap_map_length {α β γ : Type} (f : α → β → γ) (l₁ : List α) (l₂ : List β) :
    (l₁.flatMap (fun a => l₂.map (f a))).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp
  | cons a as ih =>
    simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

private theorem cubic_arith (k P : Nat) (hP : 2 * P = k * (k - 1)) :
    P + k * k + P * k ≤ k * k * k := by
  cases k with
  | zero => simp at hP; omega
  | succ m =>
    simp only [Nat.add_sub_cancel] at hP
    have h2 : 2 * (P + (m + 1) * (m + 1) + P * (m + 1)) =
        (m + 1) * m + 2 * ((m + 1) * (m + 1)) + (m + 1) * m * (m + 1) := by
      have hPk : 2 * (P * (m + 1)) = (m + 1) * m * (m + 1) := by
        rw [← Nat.mul_assoc, hP]
      omega
    have hle : (m + 1) * m + 2 * ((m + 1) * (m + 1)) + (m + 1) * m * (m + 1) ≤
        2 * ((m + 1) * (m + 1) * (m + 1)) := by
      -- (m+1) * (m + 2*(m+1) + m*(m+1)) = (m+1) * (m^2 + 4m + 2)
      -- 2 * (m+1)^3 = (m+1) * (2m^2 + 4m + 2)
      have hfactor1 :
          (m + 1) * m + 2 * ((m + 1) * (m + 1)) + (m + 1) * m * (m + 1) =
            (m + 1) * (m * m + 4 * m + 2) := by
        have h1 : (m + 1) * m * (m + 1) = (m + 1) * (m * m + m) := by
          rw [Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
        have h2 : 2 * ((m + 1) * (m + 1)) = (m + 1) * (2 * m + 2) := by
          rw [Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_comm (m + 1) 2, Nat.mul_add, Nat.mul_one]
        rw [h1, h2, ← Nat.mul_add, ← Nat.mul_add]
        congr 1; omega
      have hfactor2 :
          2 * ((m + 1) * (m + 1) * (m + 1)) = (m + 1) * (2 * (m * m) + 4 * m + 2) := by
        have h1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
        rw [Nat.mul_assoc, h1, Nat.mul_comm 2, Nat.mul_assoc]
        congr 1
        rw [Nat.mul_comm _ 2, Nat.mul_add, Nat.mul_add]
        omega
      rw [hfactor1, hfactor2]
      exact Nat.mul_le_mul_left (m + 1) (by omega)
    omega

theorem maximal_sidon_cubic_bound : Erdos.Statements.E_erd156_005.Claim := by
  intro N A ⟨_, _, hsid, hblock⟩
  let P := unorderedPairs A
  let mids := P.map (fun p => (p.1 + p.2) / 2)
  let dbls := A.flatMap (fun c => A.map (fun u => 2 * c - u))
  let trips := P.flatMap (fun p => A.map (fun u => p.1 + p.2 - u))
  let C := A ++ mids ++ dbls ++ trips
  let L := (List.range N).map (· + 1)
  have hLnd : L.Nodup :=
    List.Pairwise.map (· + 1) (fun _ _ hne heq => hne (by omega)) List.nodup_range
  have hsub : ∀ x ∈ L, x ∈ C := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hlt : i < N := List.mem_range.mp hi
    by_cases hxA : i + 1 ∈ A
    · simp [C, hxA]
    · rcases blocked_by_sidon hsid hxA (hblock (i + 1) (by omega) (by omega) hxA) with
        ⟨c, hc, d, hd, hclt, heq⟩ | ⟨c, hc, u, hu, heq⟩ | ⟨c, hc, d, hd, u, hu, hclt, heq⟩
      · rcases mem_unorderedPairs (Nat.ne_of_lt hclt) hc hd with hcd | hdc
        · have hmem : i + 1 ∈ mids := List.mem_map.mpr ⟨(c, d), hcd, by omega⟩
          simp [C, hmem]
        · have hmem : i + 1 ∈ mids := List.mem_map.mpr ⟨(d, c), hdc, by omega⟩
          simp [C, hmem]
      · have hmem : i + 1 ∈ dbls :=
          List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨u, hu, by omega⟩⟩
        simp [C, hmem]
      · rcases mem_unorderedPairs (Nat.ne_of_lt hclt) hc hd with hcd | hdc
        · have hmem : i + 1 ∈ trips :=
            List.mem_flatMap.mpr ⟨(c, d), hcd, List.mem_map.mpr ⟨u, hu, by omega⟩⟩
          simp [C, hmem]
        · have hmem : i + 1 ∈ trips :=
            List.mem_flatMap.mpr ⟨(d, c), hdc, List.mem_map.mpr ⟨u, hu, by omega⟩⟩
          simp [C, hmem]
  have hle := nodup_subset_length_le L C hLnd hsub
  have hLlen : L.length = N := by simp [L]
  have hClen : C.length = A.length + P.length + A.length * A.length + P.length * A.length := by
    simp only [C, mids, dbls, trips, List.length_append, List.length_map, flatMap_map_length]
  have hcub := cubic_arith A.length P.length (unorderedPairs_length A)
  omega

end Erdos.Claims.E_erd156_005
