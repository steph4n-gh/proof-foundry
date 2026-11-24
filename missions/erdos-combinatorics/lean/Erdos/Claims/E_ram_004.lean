import Erdos.Statements.E_ram_004

namespace Erdos.Claims.E_ram_004

private def countPred {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countPred p xs

private theorem countPred_eq_filter_length {α : Type} (p : α → Bool) :
    ∀ l : List α, countPred p l = (l.filter p).length
  | [] => rfl
  | x :: xs => by
    simp only [countPred, List.filter_cons]
    cases p x <;> simp [countPred_eq_filter_length p xs, Nat.add_comm]

private theorem countPred_ext {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → countPred p l = countPred q l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [countPred, h x (List.mem_cons_self ..)]
    have hxs := countPred_ext (l := xs) (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private def sumRow {α : Type} (f : α → α → Bool) (xs : List α) : List α → Nat
  | [] => 0
  | u :: us => countPred (f u) xs + sumRow f xs us

private theorem sumRow_cons_col {α : Type} (f : α → α → Bool) (x : α) (xs : List α) :
    ∀ us : List α, sumRow f (x :: xs) us = countPred (fun u => f u x) us + sumRow f xs us
  | [] => by simp [sumRow, countPred]
  | u :: us => by
    simp only [sumRow, countPred, sumRow_cons_col f x xs us]
    omega

private theorem handshaking_even {α : Type} (f : α → α → Bool)
    (hsymm : ∀ u v, f u v = f v u) (hloop : ∀ v, f v v = false) :
    ∀ l : List α, sumRow f l l % 2 = 0
  | [] => rfl
  | x :: xs => by
    simp only [sumRow, countPred, hloop x, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    rw [sumRow_cons_col]
    have hsym : countPred (fun u => f u x) xs = countPred (f x) xs :=
      countPred_ext fun u _ => hsymm u x
    rw [hsym]
    have ih := handshaking_even f hsymm hloop xs
    omega

private theorem sumRow_const {α : Type} (f : α → α → Bool) (xs : List α) (c : Nat) :
    ∀ {us : List α}, (∀ u ∈ us, countPred (f u) xs = c) → sumRow f xs us = us.length * c
  | [], _ => by simp [sumRow]
  | u :: us, h => by
    simp only [sumRow, List.length_cons]
    rw [h u (List.mem_cons_self ..),
      sumRow_const f xs c (fun v hv => h v (List.mem_cons_of_mem u hv)),
      Nat.succ_mul, Nat.add_comm]

private theorem exists_three {α : Type} :
    ∀ {l : List α}, l.Nodup → 3 ≤ l.length →
      ∃ a b c, a ∈ l ∧ b ∈ l ∧ c ∈ l ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c
  | a :: b :: c :: _, hnd, _ => by
    rw [List.nodup_cons] at hnd
    have ⟨h1, hnd2⟩ := hnd
    rw [List.nodup_cons] at hnd2
    have ⟨h2, _⟩ := hnd2
    refine ⟨a, b, c, List.mem_cons_self ..,
      List.mem_cons_of_mem a (List.mem_cons_self ..),
      List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self ..)),
      ?_, ?_, ?_⟩
    · intro h; subst h; exact h1 (List.mem_cons_self ..)
    · intro h; subst h; exact h2 (List.mem_cons_self ..)
    · intro h; subst h; exact h1 (List.mem_cons_of_mem b (List.mem_cons_self ..))
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h

private theorem exists_four {α : Type} :
    ∀ {l : List α}, l.Nodup → 4 ≤ l.length →
      ∃ a b c d, a ∈ l ∧ b ∈ l ∧ c ∈ l ∧ d ∈ l ∧
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  | a :: b :: c :: d :: _, hnd, _ => by
    rw [List.nodup_cons] at hnd; have ⟨ha, hnd1⟩ := hnd
    rw [List.nodup_cons] at hnd1; have ⟨hb, hnd2⟩ := hnd1
    rw [List.nodup_cons] at hnd2; have ⟨hc, _⟩ := hnd2
    refine ⟨a, b, c, d,
      List.mem_cons_self ..,
      List.mem_cons_of_mem a (List.mem_cons_self ..),
      List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self ..)),
      List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_of_mem c (List.mem_cons_self ..))),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; subst h; exact ha (List.mem_cons_self ..)
    · intro h; subst h; exact ha (List.mem_cons_of_mem b (List.mem_cons_self ..))
    · intro h; subst h; exact ha (List.mem_cons_of_mem b (List.mem_cons_of_mem c (List.mem_cons_self ..)))
    · intro h; subst h; exact hb (List.mem_cons_self ..)
    · intro h; subst h; exact hb (List.mem_cons_of_mem c (List.mem_cons_self ..))
    · intro h; subst h; exact hc (List.mem_cons_self ..)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h

private theorem filter_split_length {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun x => !p x)).length = l.length
  | [] => rfl
  | x :: xs => by
    simp only [List.filter_cons, List.length_cons]
    have ih := filter_split_length p xs
    cases p x <;> simp <;> omega

private theorem ramsey33_on_list {n : Nat} (G : Erdos.SimpleGraph n) :
    ∀ {l : List (Fin n)}, l.Nodup → 6 ≤ l.length →
      Erdos.HasIndep3 G ∨
      ∃ a ∈ l, ∃ b ∈ l, ∃ c ∈ l,
        G.adj a b = true ∧ G.adj b c = true ∧ G.adj a c = true
  | [], _, h => by simp at h
  | v :: rest, hnd, hlen => by
    rw [List.nodup_cons] at hnd
    have ⟨hvnot, hrestnd⟩ := hnd
    have hrestlen : 5 ≤ rest.length := by simp at hlen; omega
    let R1 := rest.filter (G.adj v)
    let R0 := rest.filter (fun u => !G.adj v u)
    have hsum : R1.length + R0.length = rest.length := filter_split_length (G.adj v) rest
    by_cases h1 : 3 ≤ R1.length
    · have ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ :=
        exists_three (hrestnd.filter (G.adj v)) h1
      have ha' := List.mem_filter.mp ha
      have hb' := List.mem_filter.mp hb
      have hc' := List.mem_filter.mp hc
      cases hAB : G.adj a b
      · cases hBC : G.adj b c
        · cases hAC : G.adj a c
          · exact Or.inl ⟨a, b, c, hab, hbc, hac, hAB, hBC, hAC⟩
          · exact Or.inr ⟨v, List.mem_cons_self ..,
              a, List.mem_cons_of_mem v ha'.1,
              c, List.mem_cons_of_mem v hc'.1,
              ha'.2, hAC, hc'.2⟩
        · exact Or.inr ⟨v, List.mem_cons_self ..,
            b, List.mem_cons_of_mem v hb'.1,
            c, List.mem_cons_of_mem v hc'.1,
            hb'.2, hBC, hc'.2⟩
      · exact Or.inr ⟨v, List.mem_cons_self ..,
          a, List.mem_cons_of_mem v ha'.1,
          b, List.mem_cons_of_mem v hb'.1,
          ha'.2, hAB, hb'.2⟩
    · have h0 : 3 ≤ R0.length := by omega
      have ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ :=
        exists_three (hrestnd.filter (fun u => !G.adj v u)) h0
      have ha' := List.mem_filter.mp ha
      have hb' := List.mem_filter.mp hb
      have hc' := List.mem_filter.mp hc
      have hva : G.adj v a = false := by simpa using ha'.2
      have hvb : G.adj v b = false := by simpa using hb'.2
      have hvc : G.adj v c = false := by simpa using hc'.2
      have hv_ne_a : v ≠ a := fun h => hvnot (h ▸ ha'.1)
      have hv_ne_b : v ≠ b := fun h => hvnot (h ▸ hb'.1)
      have hv_ne_c : v ≠ c := fun h => hvnot (h ▸ hc'.1)
      cases hAB : G.adj a b
      · exact Or.inl ⟨v, a, b, hv_ne_a, hab, hv_ne_b, hva, hAB, hvb⟩
      · cases hBC : G.adj b c
        · exact Or.inl ⟨v, b, c, hv_ne_b, hbc, hv_ne_c, hvb, hBC, hvc⟩
        · cases hAC : G.adj a c
          · exact Or.inl ⟨v, a, c, hv_ne_a, hac, hv_ne_c, hva, hAC, hvc⟩
          · exact Or.inr ⟨a, List.mem_cons_of_mem v ha'.1,
              b, List.mem_cons_of_mem v hb'.1,
              c, List.mem_cons_of_mem v hc'.1,
              hAB, hBC, hAC⟩

private theorem deg_ge_six {n : Nat} (G : Erdos.SimpleGraph n) (v : Fin n)
    (hdeg : 6 ≤ ((List.finRange n).filter (G.adj v)).length) :
    Erdos.HasIndep3 G ∨ Erdos.HasK4 G := by
  let N := (List.finRange n).filter (G.adj v)
  have hNnd : N.Nodup := (List.nodup_finRange n).filter (G.adj v)
  rcases ramsey33_on_list G hNnd hdeg with hind | ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩
  · exact Or.inl hind
  · have hva : G.adj v a = true := (List.mem_filter.mp ha).2
    have hvb : G.adj v b = true := (List.mem_filter.mp hb).2
    have hvc : G.adj v c = true := (List.mem_filter.mp hc).2
    exact Or.inr ⟨v, a, b, c, hva, hvb, hvc, hab, hac, hbc⟩

private theorem nondeg_ge_four {n : Nat} (G : Erdos.SimpleGraph n) (v : Fin n)
    (hnon : 4 ≤ ((List.finRange n).filter (fun u => u != v && !G.adj v u)).length) :
    Erdos.HasIndep3 G ∨ Erdos.HasK4 G := by
  let M := (List.finRange n).filter (fun u => u != v && !G.adj v u)
  have hMnd : M.Nodup := (List.nodup_finRange n).filter _
  have ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := exists_four hMnd hnon
  have hprop : ∀ u ∈ M, v ≠ u ∧ G.adj v u = false := by
    intro u hu
    have h := (List.mem_filter.mp hu).2
    simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h
    exact ⟨Ne.symm h.1, h.2⟩
  have ⟨hva_ne, hva⟩ := hprop a ha
  have ⟨hvb_ne, hvb⟩ := hprop b hb
  have ⟨hvc_ne, hvc⟩ := hprop c hc
  have ⟨hvd_ne, hvd⟩ := hprop d hd
  cases hAB : G.adj a b
  · exact Or.inl ⟨v, a, b, hva_ne, hab, hvb_ne, hva, hAB, hvb⟩
  · cases hAC : G.adj a c
    · exact Or.inl ⟨v, a, c, hva_ne, hac, hvc_ne, hva, hAC, hvc⟩
    · cases hAD : G.adj a d
      · exact Or.inl ⟨v, a, d, hva_ne, had, hvd_ne, hva, hAD, hvd⟩
      · cases hBC : G.adj b c
        · exact Or.inl ⟨v, b, c, hvb_ne, hbc, hvc_ne, hvb, hBC, hvc⟩
        · cases hBD : G.adj b d
          · exact Or.inl ⟨v, b, d, hvb_ne, hbd, hvd_ne, hvb, hBD, hvd⟩
          · cases hCD : G.adj c d
            · exact Or.inl ⟨v, c, d, hvc_ne, hcd, hvd_ne, hvc, hCD, hvd⟩
            · exact Or.inr ⟨a, b, c, d, hAB, hAC, hAD, hBC, hBD, hCD⟩

private theorem deg_plus_nondeg {n : Nat} (G : Erdos.SimpleGraph n) (v : Fin n) :
    ((List.finRange n).filter (G.adj v)).length +
    ((List.finRange n).filter (fun u => u != v && !G.adj v u)).length + 1 = n := by
  have h1 : ∀ l : List (Fin n), l.Nodup → v ∈ l →
      (l.filter (G.adj v)).length +
      (l.filter (fun u => u != v && !G.adj v u)).length + 1 = l.length := by
    intro l
    induction l with
    | nil => intro _ h; exact absurd h (List.not_mem_nil)
    | cons x xs ih =>
      intro hnd hmem
      rw [List.nodup_cons] at hnd
      simp only [List.filter_cons, List.length_cons]
      by_cases hxv : x = v
      · subst hxv
        have hself : G.adj x x = false := G.loopless x
        have hnot : x ∉ xs := hnd.1
        have hsplit := filter_split_length (G.adj x) xs
        have heq : xs.filter (fun u => u != x && !G.adj x u) = xs.filter (fun u => !G.adj x u) := by
          apply List.filter_congr
          intro u hu
          have hux : u ≠ x := fun h => hnot (h ▸ hu)
          simp [hux]
        simp only [hself, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, heq]
        omega
      · have hvxs : v ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | h
          · exact absurd rfl hxv
          · exact h
        have hih := ih hnd.2 hvxs
        have hxbne : (x != v) = true := bne_iff_ne.mpr hxv
        simp only [hxbne, Bool.true_and]
        cases G.adj v x <;> simp <;> omega
  have h := h1 (List.finRange n) (List.nodup_finRange n) (List.mem_finRange v)
  simpa using h

theorem ramsey34_le_nine : Erdos.Statements.E_ram_004.Claim := by
  intro G
  by_cases h6 : ∃ v : Fin 9, 6 ≤ ((List.finRange 9).filter (G.adj v)).length
  · rcases h6 with ⟨v, hv⟩
    exact deg_ge_six G v hv
  · by_cases h4 : ∃ v : Fin 9, 4 ≤ ((List.finRange 9).filter (fun u => u != v && !G.adj v u)).length
    · rcases h4 with ⟨v, hv⟩
      exact nondeg_ge_four G v hv
    · exfalso
      have hall5 : ∀ v ∈ List.finRange 9, countPred (G.adj v) (List.finRange 9) = 5 := by
        intro v _
        rw [countPred_eq_filter_length]
        have hlt6 : ¬ (6 ≤ ((List.finRange 9).filter (G.adj v)).length) :=
          fun h => h6 ⟨v, h⟩
        have hlt4 : ¬ (4 ≤ ((List.finRange 9).filter (fun u => u != v && !G.adj v u)).length) :=
          fun h => h4 ⟨v, h⟩
        have hsum := deg_plus_nondeg G v
        omega
      have hsum45 : sumRow G.adj (List.finRange 9) (List.finRange 9) = 45 := by
        rw [sumRow_const G.adj (List.finRange 9) 5 hall5]
        decide
      have heven : sumRow G.adj (List.finRange 9) (List.finRange 9) % 2 = 0 :=
        handshaking_even G.adj G.symm G.loopless (List.finRange 9)
      rw [hsum45] at heven
      exact absurd heven (by decide)

end Erdos.Claims.E_ram_004
