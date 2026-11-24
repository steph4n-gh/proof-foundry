import Erdos.Statements.E_erd156_003

namespace Erdos.Claims.E_erd156_003

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
    (∃ c ∈ A, ∃ u ∈ A, c ≠ u ∧ x + u = 2 * c) ∨
    (∃ c ∈ A, ∃ d ∈ A, ∃ u ∈ A, c < d ∧ u ≠ c ∧ u ≠ d ∧ x + u = c + d) := by
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
      (∃ u ∈ A, ∃ w ∈ A, u ≠ w ∧ x + w = 2 * u) ∨
      (∃ u ∈ A, ∃ v ∈ A, ∃ w ∈ A, u < v ∧ w ≠ u ∧ w ≠ v ∧ x + w = u + v) := by
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
        (∃ u ∈ A, ∃ w' ∈ A, u ≠ w' ∧ x + w' = 2 * u) ∨
        (∃ u ∈ A, ∃ v ∈ A, ∃ w' ∈ A, u < v ∧ w' ≠ u ∧ w' ≠ v ∧ x + w' = u + v) := by
      intro w hw hxw
      have hwr : w ≠ r := by
        intro h
        subst h
        have hxs : x = s := by omega
        exact hxnot (hxs ▸ hs)
      have hws : w ≠ s := by
        intro h
        subst h
        have hxr : x = r := by omega
        exact hxnot (hxr ▸ hr)
      by_cases hreq : r = s
      · subst hreq
        exact Or.inl ⟨r, hr, w, hw, Ne.symm hwr, by omega⟩
      · exact Or.inr ⟨r, hr, s, hs, w, hw, by omega, hwr, hws, hxw⟩
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

private def range30 : List Nat := (List.range 30).map (· + 1)
private def even30 : List Nat := range30.filter (fun x => x % 2 == 0)
private def odd30 : List Nat := range30.filter (fun x => x % 2 == 1)

private theorem range30_nodup : range30.Nodup := by decide
private theorem range30_length : range30.length = 30 := by decide
private theorem even30_nodup : even30.Nodup := by decide
private theorem even30_length : even30.length = 15 := by decide
private theorem odd30_nodup : odd30.Nodup := by decide
private theorem odd30_length : odd30.length = 15 := by decide

private theorem mem_range30_bounds {x : Nat} (hx : x ∈ range30) : 1 ≤ x ∧ x ≤ 30 := by
  unfold range30 at hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  have hlt : i < 30 := List.mem_range.mp hi
  omega

private theorem mem_even30_props {x : Nat} (hx : x ∈ even30) : 1 ≤ x ∧ x ≤ 30 ∧ x % 2 = 0 := by
  have ⟨h1, h2⟩ := List.mem_filter.mp hx
  have ⟨hl, hr⟩ := mem_range30_bounds h1
  exact ⟨hl, hr, beq_iff_eq.mp h2⟩

private theorem mem_odd30_props {x : Nat} (hx : x ∈ odd30) : 1 ≤ x ∧ x ≤ 30 ∧ x % 2 = 1 := by
  have ⟨h1, h2⟩ := List.mem_filter.mp hx
  have ⟨hl, hr⟩ := mem_range30_bounds h1
  exact ⟨hl, hr, beq_iff_eq.mp h2⟩

private def midList (c d : Nat) : List Nat :=
  if (c + d) % 2 == 0 then [(c + d) / 2] else []

private def subList (s u : Nat) : List Nat :=
  if u ≤ s then [s - u] else []

private theorem mem_midList {c d x : Nat} (h : 2 * x = c + d) : x ∈ midList c d := by
  unfold midList
  have hmod : ((c + d) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
  simp only [hmod, ↓reduceIte, List.mem_singleton]
  omega

private theorem mem_subList {s u x : Nat} (h : x + u = s) : x ∈ subList s u := by
  unfold subList
  have hle : u ≤ s := by omega
  simp only [hle, ↓reduceIte, List.mem_singleton]
  omega

private theorem midList_len (c d : Nat) :
    (midList c d).length = if (c + d) % 2 = 0 then 1 else 0 := by
  unfold midList
  by_cases h : (c + d) % 2 = 0
  · simp [h]
  · simp [h]

private theorem subList_len_le (s u : Nat) : (subList s u).length ≤ 1 := by
  unfold subList; split <;> simp

private theorem subList_filter_len_le (s u p : Nat) :
    ((subList s u).filter (fun x => x % 2 == p)).length ≤
      if (s + u) % 2 = p then 1 else 0 := by
  unfold subList
  split
  · rename_i hle
    have hpar : (s - u) % 2 = (s + u) % 2 := by omega
    simp only [List.filter_cons, List.filter_nil, hpar]
    by_cases hp : (s + u) % 2 = p
    · simp [hp]
    · simp [hp]
  · simp

private theorem midList_filter_len_le (c d p : Nat) :
    ((midList c d).filter (fun x => x % 2 == p)).length ≤
      if (c + d) % 2 = 0 then 1 else 0 := by
  have hle := List.length_filter_le (fun x => x % 2 == p) (midList c d)
  rw [midList_len] at hle
  exact hle

private theorem elem_filter_len (a p : Nat) :
    ([a].filter (fun x => x % 2 == p)).length = if a % 2 = p then 1 else 0 := by
  simp only [List.filter_cons, List.filter_nil]
  by_cases h : a % 2 = p
  · simp [h]
  · simp [h]

private theorem sort4 (x0 x1 x2 x3 : Nat) (hnd : [x0, x1, x2, x3].Nodup) :
    ∃ a0 a1 a2 a3 : Nat, a0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧
      ∀ z, z ∈ [x0, x1, x2, x3] ↔ z ∈ [a0, a1, a2, a3] := by
  have swap2 : ∀ a b : Nat, a ≠ b → ∃ u v : Nat, u < v ∧ (∀ z, (z = a ∨ z = b) ↔ (z = u ∨ z = v)) := by
    intro a b hab
    by_cases h : a < b
    · exact ⟨a, b, h, fun _ => Iff.rfl⟩
    · exact ⟨b, a, by omega, fun _ => or_comm⟩
  have ins3 : ∀ a b c : Nat, a < b → c ≠ a → c ≠ b →
      ∃ u v w : Nat, u < v ∧ v < w ∧
        (∀ z, (z = c ∨ z = a ∨ z = b) ↔ (z = u ∨ z = v ∨ z = w)) := by
    intro a b c hab hca hcb
    by_cases h1 : c < a
    · exact ⟨c, a, b, h1, hab, fun _ => Iff.rfl⟩
    · by_cases h2 : c < b
      · exact ⟨a, c, b, by omega, h2, fun z => by constructor <;> intro h <;> rcases h with rfl | rfl | rfl <;> simp⟩
      · exact ⟨a, b, c, hab, by omega, fun z => by constructor <;> intro h <;> rcases h with rfl | rfl | rfl <;> simp⟩
  have ins4 : ∀ a b c d : Nat, a < b → b < c → d ≠ a → d ≠ b → d ≠ c →
      ∃ u v w t : Nat, u < v ∧ v < w ∧ w < t ∧
        (∀ z, (z = d ∨ z = a ∨ z = b ∨ z = c) ↔ (z = u ∨ z = v ∨ z = w ∨ z = t)) := by
    intro a b c d hab hbc hda hdb hdc
    by_cases h1 : d < a
    · exact ⟨d, a, b, c, h1, hab, hbc, fun _ => Iff.rfl⟩
    · by_cases h2 : d < b
      · exact ⟨a, d, b, c, by omega, h2, hbc, fun z => by constructor <;> intro h <;> rcases h with rfl | rfl | rfl | rfl <;> simp⟩
      · by_cases h3 : d < c
        · exact ⟨a, b, d, c, hab, by omega, h3, fun z => by constructor <;> intro h <;> rcases h with rfl | rfl | rfl | rfl <;> simp⟩
        · exact ⟨a, b, c, d, hab, hbc, by omega, fun z => by constructor <;> intro h <;> rcases h with rfl | rfl | rfl | rfl <;> simp⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  have ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := hnd
  rcases swap2 x2 x3 h23.1 with ⟨p, q, hpq, h23eq⟩
  have h1p : x1 ≠ p := fun h => by have := (h23eq x1).mpr (Or.inl h); rcases this with rfl | rfl <;> contradiction
  have h1q : x1 ≠ q := fun h => by have := (h23eq x1).mpr (Or.inr h); rcases this with rfl | rfl <;> contradiction
  rcases ins3 p q x1 hpq h1p h1q with ⟨r, s, t, hrs, hst, h123eq⟩
  have h0r : x0 ≠ r := fun h => by
    have := (h123eq x0).mpr (Or.inl h)
    rcases this with rfl | h'
    · exact h01 rfl
    · rcases (h23eq x0).mpr h' with rfl | rfl <;> contradiction
  have h0s : x0 ≠ s := fun h => by
    have := (h123eq x0).mpr (Or.inr (Or.inl h))
    rcases this with rfl | h'
    · exact h01 rfl
    · rcases (h23eq x0).mpr h' with rfl | rfl <;> contradiction
  have h0t : x0 ≠ t := fun h => by
    have := (h123eq x0).mpr (Or.inr (Or.inr h))
    rcases this with rfl | h'
    · exact h01 rfl
    · rcases (h23eq x0).mpr h' with rfl | rfl <;> contradiction
  rcases ins4 r s t x0 hrs hst h0r h0s h0t with ⟨a0, a1, a2, a3, hlt1, hlt2, hlt3, h0123eq⟩
  refine ⟨a0, a1, a2, a3, hlt1, hlt2, hlt3, fun z => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rw [← h0123eq z, ← h123eq z, ← h23eq z]

private theorem le_three_case (A : List Nat) (hlen : A.length ≤ 3)
    (hmax : Erdos.IsMaximalSidon 30 A) : False := by
  have ⟨_, _, hsid, hblock⟩ := hmax
  match A with
  | [] =>
    have h1 : ¬ Erdos.IsSidon [1] := hblock 1 (by decide) (by decide) (by simp)
    apply h1
    intro a ha b hb c hc d hd _ _ _
    simp only [List.mem_singleton] at ha hb hc hd
    exact ⟨ha.trans hc.symm, hb.trans hd.symm⟩
  | [a] =>
    have hsub : ∀ x ∈ range30, x ∈ [a] := by
      intro x hx
      have ⟨hx1, hx30⟩ := mem_range30_bounds hx
      by_cases hxA : x ∈ [a]
      · exact hxA
      · exfalso
        rcases blocked_by_sidon hsid hxA (hblock x hx1 hx30 hxA) with
          ⟨c, hc, d, hd, hlt, _⟩ | ⟨c, hc, u, hu, hne, _⟩ | ⟨c, hc, d, hd, _, _, hlt, _, _, _⟩
        · simp at hc hd; omega
        · simp at hc hu; exact hne (hc.trans hu.symm)
        · simp at hc hd; omega
    have hle := nodup_subset_length_le range30 [a] range30_nodup hsub
    rw [range30_length] at hle
    simp at hle
  | [a, b] =>
    let C := [a, b] ++ midList a b ++ midList b a ++ subList (2 * a) b ++ subList (2 * b) a
    have hsub : ∀ x ∈ range30, x ∈ C := by
      intro x hx
      have ⟨hx1, hx30⟩ := mem_range30_bounds hx
      by_cases hxA : x ∈ [a, b]
      · simp only [C, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hxA)))
      · rcases blocked_by_sidon hsid hxA (hblock x hx1 hx30 hxA) with
          ⟨c, hc, d, hd, hlt, heq⟩ | ⟨c, hc, u, hu, hne, heq⟩ | ⟨c, hc, d, hd, u, hu, hlt, huc, hud, _⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · omega
          · simp only [C, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr (mem_midList heq))))
          · simp only [C, List.mem_append]; exact Or.inl (Or.inl (Or.inr (mem_midList heq)))
          · omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hu
          rcases hc with rfl | rfl <;> rcases hu with rfl | rfl
          · exact absurd rfl hne
          · simp only [C, List.mem_append]; exact Or.inl (Or.inr (mem_subList heq))
          · simp only [C, List.mem_append]; exact Or.inr (mem_subList heq)
          · exact absurd rfl hne
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd hu
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> rcases hu with rfl | rfl <;> omega
    have hle := nodup_subset_length_le range30 C range30_nodup hsub
    rw [range30_length] at hle
    have hClen : C.length ≤ 6 := by
      simp only [C, List.length_append, List.length_cons, List.length_nil]
      have h1 : (midList a b).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h2 : (midList b a).length ≤ 1 := by rw [midList_len]; split <;> omega
      have := subList_len_le (2 * a) b; have := subList_len_le (2 * b) a
      omega
    omega
  | [a, b, c] =>
    let C := [a, b, c] ++
      midList a b ++ midList b a ++ midList a c ++ midList c a ++ midList b c ++ midList c b ++
      subList (2 * a) b ++ subList (2 * a) c ++
      subList (2 * b) a ++ subList (2 * b) c ++
      subList (2 * c) a ++ subList (2 * c) b ++
      subList (a + b) c ++ subList (a + c) b ++ subList (b + c) a
    have hsub : ∀ x ∈ range30, x ∈ C := by
      intro x hx
      have ⟨hx1, hx30⟩ := mem_range30_bounds hx
      by_cases hxA : x ∈ [a, b, c]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxA
        rcases hxA with rfl | rfl | rfl <;> simp [C]
      · rcases blocked_by_sidon hsid hxA (hblock x hx1 hx30 hxA) with
          ⟨p, hp, q, hq, hlt, heq⟩ | ⟨p, hp, u, hu, hne, heq⟩ | ⟨p, hp, q, hq, u, hu, hlt, hup, huq, heq⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
          rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
          · omega
          · simp [C, mem_midList heq]
          · simp [C, mem_midList heq]
          · simp [C, mem_midList heq]
          · omega
          · simp [C, mem_midList heq]
          · simp [C, mem_midList heq]
          · simp [C, mem_midList heq]
          · omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hu
          rcases hp with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
          · exact absurd rfl hne
          · simp [C, mem_subList heq]
          · simp [C, mem_subList heq]
          · simp [C, mem_subList heq]
          · exact absurd rfl hne
          · simp [C, mem_subList heq]
          · simp [C, mem_subList heq]
          · simp [C, mem_subList heq]
          · exact absurd rfl hne
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq hu
          have heq' : x + u = q + p := by omega
          rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
          all_goals first
            | omega
            | exact absurd rfl hup
            | exact absurd rfl huq
            | simp [C, mem_subList heq, mem_subList heq']
    have hle := nodup_subset_length_le range30 C range30_nodup hsub
    rw [range30_length] at hle
    have hClen : C.length ≤ 18 := by
      simp only [C, List.length_append, List.length_cons, List.length_nil]
      have h1 : (midList a b).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h2 : (midList b a).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h3 : (midList a c).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h4 : (midList c a).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h5 : (midList b c).length ≤ 1 := by rw [midList_len]; split <;> omega
      have h6 : (midList c b).length ≤ 1 := by rw [midList_len]; split <;> omega
      have := subList_len_le (2 * a) b; have := subList_len_le (2 * a) c
      have := subList_len_le (2 * b) a; have := subList_len_le (2 * b) c
      have := subList_len_le (2 * c) a; have := subList_len_le (2 * c) b
      have := subList_len_le (a + b) c; have := subList_len_le (a + c) b; have := subList_len_le (b + c) a
      omega
    omega
  | _ :: _ :: _ :: _ :: _ => simp at hlen

private def inRange (s u : Nat) : List Nat :=
  if 1 + u ≤ s ∧ s ≤ 30 + u then [s - u] else []

private theorem mem_inRange {s u x : Nat} (hx1 : 1 ≤ x) (hx30 : x ≤ 30) (h : x + u = s) :
    x ∈ inRange s u := by
  unfold inRange
  have hcond : 1 + u ≤ s ∧ s ≤ 30 + u := by omega
  simp only [hcond.1, hcond.2, and_self, ↓reduceIte, List.mem_singleton]
  omega

private theorem inRange_len (s u : Nat) :
    (inRange s u).length = if 1 + u ≤ s ∧ s ≤ 30 + u then 1 else 0 := by
  unfold inRange
  by_cases h : 1 + u ≤ s ∧ s ≤ 30 + u <;> simp [h]

private theorem inRange_len_le (s u : Nat) : (inRange s u).length ≤ 1 := by
  rw [inRange_len]; split <;> omega

private theorem inRange_filter_len_le (s u p : Nat) :
    ((inRange s u).filter (fun x => x % 2 == p)).length ≤
      if (s + u) % 2 = p then 1 else 0 := by
  unfold inRange
  split
  · rename_i hcond
    have hpar : (s - u) % 2 = (s + u) % 2 := by omega
    simp only [List.filter_cons, List.filter_nil, hpar]
    by_cases hp : (s + u) % 2 = p <;> simp [hp]
  · simp

private def cand4 (a0 a1 a2 a3 : Nat) : List Nat :=
  ([a0] ++ [a1] ++ [a2] ++ [a3]) ++
  (midList a0 a1 ++ midList a0 a2 ++ midList a0 a3 ++
   midList a1 a2 ++ midList a1 a3 ++ midList a2 a3) ++
  (inRange (2 * a0) a3 ++ inRange (2 * a3) a0 ++
   inRange (2 * a0) a1 ++ inRange (2 * a0) a2 ++
   inRange (2 * a1) a0 ++ inRange (2 * a1) a2 ++ inRange (2 * a1) a3 ++
   inRange (2 * a2) a0 ++ inRange (2 * a2) a1 ++ inRange (2 * a2) a3 ++
   inRange (2 * a3) a1 ++ inRange (2 * a3) a2) ++
  (inRange (a0 + a1) a2 ++ inRange (a0 + a1) a3 ++
   inRange (a0 + a2) a1 ++ inRange (a0 + a2) a3 ++
   inRange (a0 + a3) a1 ++ inRange (a0 + a3) a2 ++
   inRange (a1 + a2) a0 ++ inRange (a1 + a2) a3 ++
   inRange (a1 + a3) a0 ++ inRange (a1 + a3) a2 ++
   inRange (a2 + a3) a0 ++ inRange (a2 + a3) a1)

private theorem special_case_8_19 :
    ∀ a1 a2 : Fin 19, 8 < a1.val → a1.val < a2.val →
      range30.all (fun x => (cand4 8 a1.val a2.val 19).contains x) = false := by
  decide +kernel

private theorem special_case_10_20 :
    ∀ a1 a2 : Fin 20, 10 < a1.val → a1.val < a2.val →
      range30.all (fun x => (cand4 10 a1.val a2.val 20).contains x) = false := by
  decide +kernel

private theorem special_case_11_21 :
    ∀ a1 a2 : Fin 21, 11 < a1.val → a1.val < a2.val →
      range30.all (fun x => (cand4 11 a1.val a2.val 21).contains x) = false := by
  decide +kernel

private theorem special_case_12_23 :
    ∀ a1 a2 : Fin 23, 12 < a1.val → a1.val < a2.val →
      range30.all (fun x => (cand4 12 a1.val a2.val 23).contains x) = false := by
  decide +kernel

private theorem eq_four_case (A : List Nat) (a0 a1 a2 a3 : Nat)
    (hlt1 : a0 < a1) (hlt2 : a1 < a2) (hlt3 : a2 < a3)
    (hmem : ∀ z, z ∈ A ↔ z ∈ [a0, a1, a2, a3])
    (hmax : Erdos.IsMaximalSidon 30 A) : False := by
  have ⟨_, _, hsid, hblock⟩ := hmax
  have hbounds : ∀ x : Nat, 1 ≤ x → x ≤ 30 →
      2 * a0 ≤ x + a3 ∧ x + a0 ≤ 2 * a3 := by
    intro x hx1 hx30
    by_cases hxA : x ∈ A
    · have hx4 := (hmem x).mp hxA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx4
      rcases hx4 with rfl | rfl | rfl | rfl <;> omega
    · rcases blocked_by_sidon hsid hxA (hblock x hx1 hx30 hxA) with
        ⟨c, hc, d, hd, _, heq⟩ | ⟨c, hc, u, hu, _, heq⟩ | ⟨c, hc, d, hd, u, hu, _, _, _, heq⟩
      · have hc4 := (hmem c).mp hc; have hd4 := (hmem d).mp hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hd4
        have : a0 ≤ c ∧ c ≤ a3 := by rcases hc4 with rfl | rfl | rfl | rfl <;> omega
        have : a0 ≤ d ∧ d ≤ a3 := by rcases hd4 with rfl | rfl | rfl | rfl <;> omega
        omega
      · have hc4 := (hmem c).mp hc; have hu4 := (hmem u).mp hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hu4
        have : a0 ≤ c ∧ c ≤ a3 := by rcases hc4 with rfl | rfl | rfl | rfl <;> omega
        have : a0 ≤ u ∧ u ≤ a3 := by rcases hu4 with rfl | rfl | rfl | rfl <;> omega
        omega
      · have hc4 := (hmem c).mp hc; have hd4 := (hmem d).mp hd; have hu4 := (hmem u).mp hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hd4 hu4
        have : a0 ≤ c ∧ c ≤ a3 := by rcases hc4 with rfl | rfl | rfl | rfl <;> omega
        have : a0 ≤ d ∧ d ≤ a3 := by rcases hd4 with rfl | rfl | rfl | rfl <;> omega
        have : a0 ≤ u ∧ u ≤ a3 := by rcases hu4 with rfl | rfl | rfl | rfl <;> omega
        omega
  have hb1 := (hbounds 1 (by decide) (by decide)).1
  have hb30 := (hbounds 30 (by decide) (by decide)).2
  let C := cand4 a0 a1 a2 a3
  have hcover : ∀ x : Nat, 1 ≤ x → x ≤ 30 → x ∈ C := by
    intro x hx1 hx30
    by_cases hxA : x ∈ A
    · have hx4 := (hmem x).mp hxA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx4
      rcases hx4 with rfl | rfl | rfl | rfl <;> simp [C, cand4]
    · rcases blocked_by_sidon hsid hxA (hblock x hx1 hx30 hxA) with
        ⟨c, hc, d, hd, hlt, heq⟩ | ⟨c, hc, u, hu, hne, heq⟩ | ⟨c, hc, d, hd, u, hu, hlt, huc, hud, heq⟩
      · have hc4 := (hmem c).mp hc; have hd4 := (hmem d).mp hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hd4
        rcases hc4 with rfl | rfl | rfl | rfl <;> rcases hd4 with rfl | rfl | rfl | rfl
        all_goals first | omega | simp [C, cand4, mem_midList heq]
      · have hc4 := (hmem c).mp hc; have hu4 := (hmem u).mp hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hu4
        rcases hc4 with rfl | rfl | rfl | rfl <;> rcases hu4 with rfl | rfl | rfl | rfl
        all_goals first | exact absurd rfl hne | simp [C, cand4, mem_inRange hx1 hx30 heq]
      · have hc4 := (hmem c).mp hc; have hd4 := (hmem d).mp hd; have hu4 := (hmem u).mp hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4 hd4 hu4
        rcases hc4 with rfl | rfl | rfl | rfl <;>
          rcases hd4 with rfl | rfl | rfl | rfl <;>
          rcases hu4 with rfl | rfl | rfl | rfl
        all_goals first
          | omega
          | exact absurd rfl huc
          | exact absurd rfl hud
          | simp [C, cand4, mem_inRange hx1 hx30 heq]
  have hfilter_bound : ∀ p : Nat,
      (C.filter (fun x => x % 2 == p)).length ≤
        (if a0 % 2 = p then 1 else 0) + (if a1 % 2 = p then 1 else 0) +
        (if a2 % 2 = p then 1 else 0) + (if a3 % 2 = p then 1 else 0) +
        (if (a0 + a1) % 2 = 0 then 1 else 0) + (if (a0 + a2) % 2 = 0 then 1 else 0) +
        (if (a0 + a3) % 2 = 0 then 1 else 0) + (if (a1 + a2) % 2 = 0 then 1 else 0) +
        (if (a1 + a3) % 2 = 0 then 1 else 0) + (if (a2 + a3) % 2 = 0 then 1 else 0) +
        (if (2 * a0 + a3) % 2 = p then 1 else 0) + (if (2 * a3 + a0) % 2 = p then 1 else 0) +
        (if (2 * a0 + a1) % 2 = p then 1 else 0) + (if (2 * a0 + a2) % 2 = p then 1 else 0) +
        (if (2 * a1 + a0) % 2 = p then 1 else 0) + (if (2 * a1 + a2) % 2 = p then 1 else 0) +
        (if (2 * a1 + a3) % 2 = p then 1 else 0) + (if (2 * a2 + a0) % 2 = p then 1 else 0) +
        (if (2 * a2 + a1) % 2 = p then 1 else 0) + (if (2 * a2 + a3) % 2 = p then 1 else 0) +
        (if (2 * a3 + a1) % 2 = p then 1 else 0) + (if (2 * a3 + a2) % 2 = p then 1 else 0) +
        (if (a0 + a1 + a2) % 2 = p then 1 else 0) + (if (a0 + a1 + a3) % 2 = p then 1 else 0) +
        (if (a0 + a2 + a1) % 2 = p then 1 else 0) + (if (a0 + a2 + a3) % 2 = p then 1 else 0) +
        (if (a0 + a3 + a1) % 2 = p then 1 else 0) + (if (a0 + a3 + a2) % 2 = p then 1 else 0) +
        (if (a1 + a2 + a0) % 2 = p then 1 else 0) + (if (a1 + a2 + a3) % 2 = p then 1 else 0) +
        (if (a1 + a3 + a0) % 2 = p then 1 else 0) + (if (a1 + a3 + a2) % 2 = p then 1 else 0) +
        (if (a2 + a3 + a0) % 2 = p then 1 else 0) + (if (a2 + a3 + a1) % 2 = p then 1 else 0) := by
    intro p
    simp only [C, cand4, List.filter_append, List.length_append]
    have hb0 := elem_filter_len a0 p; have hb1 := elem_filter_len a1 p
    have hb2 := elem_filter_len a2 p; have hb3 := elem_filter_len a3 p
    have hm1 := midList_filter_len_le a0 a1 p; have hm2 := midList_filter_len_le a0 a2 p
    have hm3 := midList_filter_len_le a0 a3 p; have hm4 := midList_filter_len_le a1 a2 p
    have hm5 := midList_filter_len_le a1 a3 p; have hm6 := midList_filter_len_le a2 a3 p
    have hd1 := inRange_filter_len_le (2 * a0) a3 p
    have hd2 := inRange_filter_len_le (2 * a3) a0 p
    have hd3 := inRange_filter_len_le (2 * a0) a1 p; have hd4 := inRange_filter_len_le (2 * a0) a2 p
    have hd5 := inRange_filter_len_le (2 * a1) a0 p; have hd6 := inRange_filter_len_le (2 * a1) a2 p
    have hd7 := inRange_filter_len_le (2 * a1) a3 p; have hd8 := inRange_filter_len_le (2 * a2) a0 p
    have hd9 := inRange_filter_len_le (2 * a2) a1 p; have hd10 := inRange_filter_len_le (2 * a2) a3 p
    have hd11 := inRange_filter_len_le (2 * a3) a1 p; have hd12 := inRange_filter_len_le (2 * a3) a2 p
    have ht1 := inRange_filter_len_le (a0 + a1) a2 p; have ht2 := inRange_filter_len_le (a0 + a1) a3 p
    have ht3 := inRange_filter_len_le (a0 + a2) a1 p; have ht4 := inRange_filter_len_le (a0 + a2) a3 p
    have ht5 := inRange_filter_len_le (a0 + a3) a1 p; have ht6 := inRange_filter_len_le (a0 + a3) a2 p
    have ht7 := inRange_filter_len_le (a1 + a2) a0 p; have ht8 := inRange_filter_len_le (a1 + a2) a3 p
    have ht9 := inRange_filter_len_le (a1 + a3) a0 p; have ht10 := inRange_filter_len_le (a1 + a3) a2 p
    have ht11 := inRange_filter_len_le (a2 + a3) a0 p; have ht12 := inRange_filter_len_le (a2 + a3) a1 p
    omega
  have htotal_bound :
      C.length ≤ 22 +
        (if (a0 + a1) % 2 = 0 then 1 else 0) + (if (a0 + a2) % 2 = 0 then 1 else 0) +
        (if (a0 + a3) % 2 = 0 then 1 else 0) + (if (a1 + a2) % 2 = 0 then 1 else 0) +
        (if (a1 + a3) % 2 = 0 then 1 else 0) + (if (a2 + a3) % 2 = 0 then 1 else 0) +
        (if 1 + a3 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a3 then 1 else 0) +
        (if 1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0 then 1 else 0) +
        (if 1 + a2 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a2 then 1 else 0) +
        (if 1 + a1 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a1 then 1 else 0) +
        (if 1 + a3 ≤ a0 + a1 ∧ a0 + a1 ≤ 30 + a3 then 1 else 0) +
        (if 1 + a0 ≤ a2 + a3 ∧ a2 + a3 ≤ 30 + a0 then 1 else 0) := by
    simp only [C, cand4, List.length_append, List.length_singleton]
    have hm1 := midList_len a0 a1; have hm2 := midList_len a0 a2
    have hm3 := midList_len a0 a3; have hm4 := midList_len a1 a2
    have hm5 := midList_len a1 a3; have hm6 := midList_len a2 a3
    have hd1 := inRange_len (2 * a0) a3; have hd2 := inRange_len (2 * a3) a0
    have hd3 := inRange_len_le (2 * a0) a1; have hd4 := inRange_len (2 * a0) a2
    have hd5 := inRange_len_le (2 * a1) a0; have hd6 := inRange_len_le (2 * a1) a2
    have hd7 := inRange_len_le (2 * a1) a3; have hd8 := inRange_len_le (2 * a2) a0
    have hd9 := inRange_len_le (2 * a2) a1; have hd10 := inRange_len_le (2 * a2) a3
    have hd11 := inRange_len (2 * a3) a1; have hd12 := inRange_len_le (2 * a3) a2
    have ht1 := inRange_len_le (a0 + a1) a2; have ht2 := inRange_len (a0 + a1) a3
    have ht3 := inRange_len_le (a0 + a2) a1; have ht4 := inRange_len_le (a0 + a2) a3
    have ht5 := inRange_len_le (a0 + a3) a1; have ht6 := inRange_len_le (a0 + a3) a2
    have ht7 := inRange_len_le (a1 + a2) a0; have ht8 := inRange_len_le (a1 + a2) a3
    have ht9 := inRange_len_le (a1 + a3) a0; have ht10 := inRange_len_le (a1 + a3) a2
    have ht11 := inRange_len (a2 + a3) a0; have ht12 := inRange_len_le (a2 + a3) a1
    omega
  have hle_all : 30 ≤ C.length := by
    have h := nodup_subset_length_le range30 C range30_nodup (fun x hx => by
      have ⟨h1, h2⟩ := mem_range30_bounds hx; exact hcover x h1 h2)
    rwa [range30_length] at h
  have hle_even : 15 ≤ (C.filter (fun x => x % 2 == 0)).length := by
    have h := nodup_subset_length_le even30 (C.filter (fun x => x % 2 == 0)) even30_nodup (fun x hx => by
      have ⟨h1, h2, h3⟩ := mem_even30_props hx
      exact List.mem_filter.mpr ⟨hcover x h1 h2, beq_iff_eq.mpr h3⟩)
    rwa [even30_length] at h
  have hle_odd : 15 ≤ (C.filter (fun x => x % 2 == 1)).length := by
    have h := nodup_subset_length_le odd30 (C.filter (fun x => x % 2 == 1)) odd30_nodup (fun x hx => by
      have ⟨h1, h2, h3⟩ := mem_odd30_props hx
      exact List.mem_filter.mpr ⟨hcover x h1 h2, beq_iff_eq.mpr h3⟩)
    rwa [odd30_length] at h
  have hfe := hfilter_bound 0
  have hfo := hfilter_bound 1
  have hmid_le3 :
      (if (a0 + a1) % 2 = 0 then 1 else 0) + (if (a0 + a2) % 2 = 0 then 1 else 0) +
      (if (a0 + a3) % 2 = 0 then 1 else 0) + (if (a1 + a2) % 2 = 0 then 1 else 0) +
      (if (a1 + a3) % 2 = 0 then 1 else 0) + (if (a2 + a3) % 2 = 0 then 1 else 0) ≤ 3 := by
    have hp0 : a0 % 2 = 0 ∨ a0 % 2 = 1 := by omega
    have hp1 : a1 % 2 = 0 ∨ a1 % 2 = 1 := by omega
    have hp2 : a2 % 2 = 0 ∨ a2 % 2 = 1 := by omega
    have hp3 : a3 % 2 = 0 ∨ a3 % 2 = 1 := by omega
    rcases hp0 with h0 | h0 <;> rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2 <;> rcases hp3 with h3 | h3 <;>
      (simp [Nat.add_mod, h0, h1, h2, h3] at hfe hfo ⊢; try omega)
  let b1 := if 1 + a3 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a3 then 1 else 0
  let b2 := if 1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0 then 1 else 0
  let b3 := if 1 + a2 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a2 then 1 else 0
  let b4 := if 1 + a1 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a1 then 1 else 0
  let b5 := if 1 + a3 ≤ a0 + a1 ∧ a0 + a1 ≤ 30 + a3 then 1 else 0
  let b6 := if 1 + a0 ≤ a2 + a3 ∧ a2 + a3 ≤ 30 + a0 then 1 else 0
  have hb_sum : 5 ≤ b1 + b2 + b3 + b4 + b5 + b6 := by
    change 5 ≤ _
    omega
  have hb12 : b1 + b2 ≤ 1 := by
    dsimp only [b1, b2]
    by_cases h1 : 1 + a3 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a3
    · by_cases h2 : 1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0
      · omega
      · simp [h1, h2]
    · by_cases h2 : 1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0 <;> simp [h1, h2]
  have hb_each : b3 ≤ 1 ∧ b4 ≤ 1 ∧ b5 ≤ 1 ∧ b6 ≤ 1 := by
    dsimp only [b3, b4, b5, b6]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> split <;> omega
  have hc12 : (1 + a3 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a3) ∨ (1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0) := by
    by_cases h1 : 1 + a3 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a3
    · exact Or.inl h1
    · by_cases h2 : 1 + a0 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a0
      · exact Or.inr h2
      · exfalso
        have : b1 = 0 := by dsimp only [b1]; simp [h1]
        have : b2 = 0 := by dsimp only [b2]; simp [h2]
        omega
  have hc3 : 1 + a2 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a2 := by
    by_cases h : 1 + a2 ≤ 2 * a0 ∧ 2 * a0 ≤ 30 + a2
    · exact h
    · exfalso; have : b3 = 0 := by dsimp only [b3]; simp [h]
      omega
  have hc4 : 1 + a1 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a1 := by
    by_cases h : 1 + a1 ≤ 2 * a3 ∧ 2 * a3 ≤ 30 + a1
    · exact h
    · exfalso; have : b4 = 0 := by dsimp only [b4]; simp [h]
      omega
  have hc5 : 1 + a3 ≤ a0 + a1 ∧ a0 + a1 ≤ 30 + a3 := by
    by_cases h : 1 + a3 ≤ a0 + a1 ∧ a0 + a1 ≤ 30 + a3
    · exact h
    · exfalso; have : b5 = 0 := by dsimp only [b5]; simp [h]
      omega
  have hc6 : 1 + a0 ≤ a2 + a3 ∧ a2 + a3 ≤ 30 + a0 := by
    by_cases h : 1 + a0 ≤ a2 + a3 ∧ a2 + a3 ≤ 30 + a0
    · exact h
    · exfalso; have : b6 = 0 := by dsimp only [b6]; simp [h]
      omega
  have hspecial :
      (a0 = 8 ∧ a3 = 19) ∨ (a0 = 10 ∧ a3 = 20) ∨ (a0 = 11 ∧ a3 = 21) ∨ (a0 = 12 ∧ a3 = 23) := by
    rcases hc12 with h1 | h2 <;> omega
  have hall_true : range30.all (fun x => C.contains x) = true := by
    rw [List.all_eq_true]
    intro x hx
    have ⟨h1, h2⟩ := mem_range30_bounds hx
    exact List.contains_iff_mem.mpr (hcover x h1 h2)
  rcases hspecial with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hfalse := special_case_8_19 ⟨a1, by omega⟩ ⟨a2, hlt3⟩ hlt1 hlt2
    exact absurd (hall_true.symm.trans hfalse) (by decide)
  · have hfalse := special_case_10_20 ⟨a1, by omega⟩ ⟨a2, hlt3⟩ hlt1 hlt2
    exact absurd (hall_true.symm.trans hfalse) (by decide)
  · have hfalse := special_case_11_21 ⟨a1, by omega⟩ ⟨a2, hlt3⟩ hlt1 hlt2
    exact absurd (hall_true.symm.trans hfalse) (by decide)
  · have hfalse := special_case_12_23 ⟨a1, by omega⟩ ⟨a2, hlt3⟩ hlt1 hlt2
    exact absurd (hall_true.symm.trans hfalse) (by decide)

theorem no_maximal_sidon_le_4_in_30 : Erdos.Statements.E_erd156_003.Claim := by
  intro A hlen hmax
  by_cases hle3 : A.length ≤ 3
  · exact le_three_case A hle3 hmax
  · match hA : A with
    | [x0, x1, x2, x3] =>
      have hnd : [x0, x1, x2, x3].Nodup := hA ▸ hmax.1
      rcases sort4 x0 x1 x2 x3 hnd with ⟨a0, a1, a2, a3, h1, h2, h3, hmem⟩
      exact eq_four_case [x0, x1, x2, x3] a0 a1 a2 a3 h1 h2 h3 hmem (hA ▸ hmax)
    | [] => simp [hA] at hle3
    | [_] => simp [hA] at hle3
    | [_, _] => simp [hA] at hle3
    | [_, _, _] => simp [hA] at hle3
    | _ :: _ :: _ :: _ :: _ :: _ => simp [hA] at hlen

end Erdos.Claims.E_erd156_003
