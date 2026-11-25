import SortNet.Core
import SortNet.Statements.SN_rec_d17

namespace SortNet.Claims.SN_rec_d17_not_s8

open SortNet

/-!
  Pure Lean 4.36 proof of `¬ SortNet.Statements.SN_rec_d17.Record 8`, certifying
  the parallel-depth lower bound `D(17) ≥ 9` (the Yao–Yao / Parberry 2-layer
  independent-set bound `D(n) ≥ 2 ⌈log₂ n⌉ - 1`).

  Outline:
  1. Decompose any network of `netDepth net ≤ 8` into 8 parallel matchings
     represented as involutions `m_0, ..., m_7 : Fin 17 → Fin 17`.
  2. Prove that for any subset `A` and any two involutions `m1, m2`, there is
     an independent set `I ⊆ A` of both `m1` and `m2` with `2 * |I| ≥ |A|`.
  3. Maintain the invariant `Realizable f A C` (every vector agreeing with `C`
     outside `A` is in the range of `f`). Each pair of layers halves `|A|` at
     most once (`2 * |A'| ≥ |A|`).
  4. Starting from `|A_0| = 17`, after 8 layers (4 pairs) we retain
     `|A_4| ≥ 2` free wires (`17 → 9 → 5 → 3 → 2`), yielding an unsorted output.
-/

/-! ## 1. Counting and Bijections on `Fin n` -/

private def countFin {n : Nat} (P : Fin n → Bool) : Nat :=
  (List.finRange n).countP P

private theorem countFin_eq_of_eq {n : Nat} (P Q : Fin n → Bool)
    (h : ∀ w, P w = Q w) : countFin P = countFin Q := by
  have : P = Q := funext h
  rw [this]

private theorem countFin_add_disjoint {n : Nat} (P Q : Fin n → Bool)
    (hdisj : ∀ w, (P w && Q w) = false) :
    countFin (fun w => P w || Q w) = countFin P + countFin Q := by
  unfold countFin
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have hd := hdisj a
    cases hp : P a <;> cases hq : Q a <;> simp [hp, hq] at hd ⊢ <;> omega

private theorem countFin_eq_zero_iff {n : Nat} (P : Fin n → Bool) :
    countFin P = 0 ↔ ∀ w, P w = false := by
  unfold countFin
  constructor
  · intro h w
    have hmem : w ∈ List.finRange n := List.mem_finRange w
    have h0 := List.countP_eq_zero.1 h w hmem
    exact Bool.eq_false_iff.2 h0
  · intro h
    exact List.countP_eq_zero.2 (fun w _ => by simp [h w])

private theorem exists_of_countP_pos {α : Type} (P : α → Bool) :
    ∀ (l : List α), 0 < l.countP P → ∃ w ∈ l, P w = true := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
    intro h
    simp only [List.countP_cons] at h
    cases hx : P x
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      rcases ih h with ⟨w, hw, hPw⟩
      exact ⟨w, List.mem_cons_of_mem x hw, hPw⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

private theorem exists_of_countFin_pos {n : Nat} (P : Fin n → Bool)
    (h : 0 < countFin P) : ∃ w : Fin n, P w = true := by
  rcases exists_of_countP_pos P (List.finRange n) h with ⟨w, _, hw⟩
  exact ⟨w, hw⟩

private theorem countP_singleton_aux {α : Type} [DecidableEq α] (w0 : α) :
    ∀ (l : List α), l.Nodup → w0 ∈ l → l.countP (fun w => decide (w = w0)) = 1 := by
  intro l
  induction l with
  | nil => intro _ hmem; cases hmem
  | cons a xs ih =>
    intro hnd hmem
    rw [List.nodup_cons] at hnd
    simp only [List.countP_cons]
    by_cases ha : a = w0
    · subst ha
      have hz : xs.countP (fun w => decide (w = a)) = 0 :=
        List.countP_eq_zero.2 (fun w hw h => hnd.1 (of_decide_eq_true h ▸ hw))
      simp [hz]
    · have hmem' : w0 ∈ xs := by
        rcases List.mem_cons.1 hmem with rfl | h'
        · exact absurd rfl ha
        · exact h'
      simp [ha, ih hnd.2 hmem']

private theorem countFin_singleton {n : Nat} (w0 : Fin n) :
    countFin (fun w => decide (w = w0)) = 1 :=
  countP_singleton_aux w0 (List.finRange n) (List.nodup_finRange n) (List.mem_finRange w0)

private theorem countFin_update_false {n : Nat} (P : Fin n → Bool) (w0 : Fin n) (hw0 : P w0 = true) :
    countFin (fun w => if w = w0 then false else P w) + 1 = countFin P := by
  have hdisj : ∀ w, ((if w = w0 then false else P w) && decide (w = w0)) = false := by
    intro w; by_cases h : w = w0 <;> simp [h]
  have heq : ∀ w, P w = ((if w = w0 then false else P w) || decide (w = w0)) := by
    intro w; by_cases h : w = w0
    · subst h; simp [hw0]
    · simp [h]
  rw [countFin_eq_of_eq P _ heq, countFin_add_disjoint _ _ hdisj, countFin_singleton w0]

private theorem exists_two_of_countFin_ge_two {n : Nat} (P : Fin n → Bool)
    (h : 2 ≤ countFin P) : ∃ i j : Fin n, i.val < j.val ∧ P i = true ∧ P j = true := by
  obtain ⟨w1, hw1⟩ := exists_of_countFin_pos P (by omega)
  let P' : Fin n → Bool := fun w => if w = w1 then false else P w
  have hsum : countFin P' + 1 = countFin P := countFin_update_false P w1 hw1
  obtain ⟨w2, hw2⟩ := exists_of_countFin_pos P' (by omega)
  have hne : w2 ≠ w1 := by intro he; subst he; simp [P'] at hw2
  have hw2P : P w2 = true := by simpa [P', hne] using hw2
  by_cases hlt : w1.val < w2.val
  · exact ⟨w1, w2, hlt, hw1, hw2P⟩
  · have hlt2 : w2.val < w1.val := by
      have : w1.val ≠ w2.val := fun he => hne (Fin.ext he.symm)
      omega
    exact ⟨w2, w1, hlt2, hw2P, hw1⟩

private theorem nodup_map_of_inj {α β : Type} (r : α → β) (hinj : ∀ a b, r a = r b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map r).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a xs ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2⟩
    intro hm
    rcases List.mem_map.1 hm with ⟨b, hb, hba⟩
    exact hnd.1 (hinj a b hba.symm ▸ hb)

private theorem countFin_comp_invol {n : Nat} (r : Fin n → Fin n) (hr : ∀ w, r (r w) = w)
    (P : Fin n → Bool) : countFin (fun w => P (r w)) = countFin P := by
  unfold countFin
  have hinj : ∀ a b : Fin n, r a = r b → a = b := fun a b hab => by
    have := congrArg r hab; rwa [hr a, hr b] at this
  have hperm : ((List.finRange n).map r).Perm (List.finRange n) := by
    refine (List.perm_ext_iff_of_nodup (nodup_map_of_inj r hinj _ (List.nodup_finRange n))
      (List.nodup_finRange n)).2 (fun x => ?_)
    constructor
    · intro _; exact List.mem_finRange x
    · intro _; exact List.mem_map.2 ⟨r x, List.mem_finRange (r x), hr x⟩
  have hmap : ((List.finRange n).map r).countP P = (List.finRange n).countP (fun w => P (r w)) := by
    rw [List.countP_map]; rfl
  rw [← hmap, hperm.countP_eq]

private theorem countFin_true (n : Nat) : countFin (fun _ : Fin n => true) = n := by
  unfold countFin
  simp

/-! ## 2. Bipartite Independent Set for Two Involutions -/

private def iterF {n : Nat} (f : Fin n → Fin n) : Nat → Fin n → Fin n
  | 0, x => x
  | k + 1, x => f (iterF f k x)

private theorem iterF_add {n : Nat} (f : Fin n → Fin n) (a b : Nat) (x : Fin n) :
    iterF f (a + b) x = iterF f a (iterF f b x) := by
  induction a with
  | zero => simp [iterF]
  | succ a ih =>
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this, iterF, iterF, ih]

private theorem iterF_succ_right {n : Nat} (f : Fin n → Fin n) (k : Nat) (x : Fin n) :
    iterF f (k + 1) x = iterF f k (f x) := by
  have := iterF_add f k 1 x
  simpa [iterF] using this

private theorem iterF_m1_comm {n : Nat} (m1 m2 : Fin n → Fin n)
    (h1 : ∀ w, m1 (m1 w) = w) (h2 : ∀ w, m2 (m2 w) = w) :
    ∀ (k : Nat) (x : Fin n),
      m1 (iterF (fun w => m2 (m1 w)) k x) = iterF (fun w => m1 (m2 w)) k (m1 x) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [iterF, iterF_succ_right]
    have hstep : m1 (m2 (m1 (iterF (fun w => m2 (m1 w)) k x))) =
                 m1 (m2 (iterF (fun w => m1 (m2 w)) k (m1 x))) := by
      rw [ih x]
    rw [hstep]
    change iterF (fun w => m1 (m2 w)) (k + 1) (m1 x) = _
    exact iterF_succ_right (fun w => m1 (m2 w)) k (m1 x)

private theorem iterF_inv_cancel {n : Nat} (m1 m2 : Fin n → Fin n)
    (h1 : ∀ w, m1 (m1 w) = w) (h2 : ∀ w, m2 (m2 w) = w) :
    ∀ (k : Nat) (x : Fin n),
      iterF (fun w => m1 (m2 w)) k (iterF (fun w => m2 (m1 w)) k x) = x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [iterF_succ_right, iterF]
    have : m1 (m2 (m2 (m1 (iterF (fun w => m2 (m1 w)) k x)))) =
        iterF (fun w => m2 (m1 w)) k x := by
      rw [h2, h1]
    rw [this, ih x]

private theorem exists_dup_of_not_nodup_map {α β : Type} (h : α → β) :
    ∀ (l : List α), l.Nodup → ¬ (l.map h).Nodup →
      ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧ h a = h b := by
  intro l
  induction l with
  | nil => intro _ hn; exact absurd List.nodup_nil hn
  | cons x xs ih =>
    intro hnd hn
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hm : h x ∈ xs.map h
    · rcases List.mem_map.1 hm with ⟨y, hy, hyx⟩
      have hne : x ≠ y := fun he => hnd.1 (he ▸ hy)
      exact ⟨x, List.mem_cons_self, y, List.mem_cons_of_mem x hy, hne, hyx.symm⟩
    · have hndxs : ¬ (xs.map h).Nodup := fun h' => hn ⟨hm, h'⟩
      rcases ih hnd.2 hndxs with ⟨a, ha, b, hb, hab, heq⟩
      exact ⟨a, List.mem_cons_of_mem x ha, b, List.mem_cons_of_mem x hb, hab, heq⟩

private theorem two_involutions_indep {n : Nat} (m1 m2 : Fin n → Fin n)
    (h1 : ∀ w, m1 (m1 w) = w) (h2 : ∀ w, m2 (m2 w) = w) :
    ∀ (k : Nat) (A : Fin n → Bool), countFin A ≤ k →
      ∃ I : Fin n → Bool,
        (∀ w, I w = true → A w = true) ∧
        (∀ w, m1 w ≠ w → (I w && I (m1 w)) = false) ∧
        (∀ w, m2 w ≠ w → (I w && I (m2 w)) = false) ∧
        countFin A ≤ 2 * countFin I := by
  intro k
  induction k with
  | zero =>
    intro A hA
    have hz : countFin A = 0 := by omega
    refine ⟨fun _ => false, ?_, ?_, ?_, ?_⟩
    · intro w hw; cases hw
    · intro w _; rfl
    · intro w _; rfl
    · simp [hz]
  | succ k ih =>
    intro A hA
    by_cases h0 : countFin A = 0
    · exact ih A (by omega)
    · let hasDeg0 : Fin n → Bool := fun v =>
        A v && ((m1 v == v) || !A (m1 v)) && ((m2 v == v) || !A (m2 v))
      let hasDeg1_m1 : Fin n → Bool := fun v =>
        A v && (m1 v != v) && A (m1 v) && ((m2 v == v) || !A (m2 v) || (m2 v == m1 v))
      let hasDeg1_m2 : Fin n → Bool := fun v =>
        A v && (m2 v != v) && A (m2 v) && ((m1 v == v) || !A (m1 v) || (m1 v == m2 v))
      by_cases hd0 : 0 < countFin hasDeg0
      · obtain ⟨v, hv⟩ := exists_of_countFin_pos hasDeg0 hd0
        have hAv : A v = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).1
        have hm1v : m1 v = v ∨ A (m1 v) = false := by
          have h := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).2
          rcases Bool.or_eq_true_iff.1 h with h' | h'
          · exact Or.inl (beq_iff_eq.1 h')
          · exact Or.inr (by simpa using h')
        have hm2v : m2 v = v ∨ A (m2 v) = false := by
          have h := (Bool.and_eq_true_iff.1 hv).2
          rcases Bool.or_eq_true_iff.1 h with h' | h'
          · exact Or.inl (beq_iff_eq.1 h')
          · exact Or.inr (by simpa using h')
        let A' : Fin n → Bool := fun w => if w = v then false else A w
        have hcntA' : countFin A' + 1 = countFin A := countFin_update_false A v hAv
        obtain ⟨I', hI'sub, hI'm1, hI'm2, hI'cnt⟩ := ih A' (by omega)
        let I : Fin n → Bool := fun w => if w = v then true else I' w
        have hI'v : I' v = false := by
          cases h : I' v
          · rfl
          · have := hI'sub v h; simp [A'] at this
        have hcntI : countFin I' + 1 = countFin I := by
          have := countFin_update_false I v (by simp [I])
          have heq : ∀ w, (if w = v then false else I w) = I' w := by
            intro w; by_cases hw : w = v
            · subst hw; simp [hI'v]
            · simp [I, hw]
          rw [countFin_eq_of_eq _ I' heq] at this
          exact this
        refine ⟨I, ?_, ?_, ?_, by omega⟩
        · intro w hw; by_cases h : w = v
          · subst h; exact hAv
          · simp [I, h] at hw
            have := hI'sub w hw; simp [A', h] at this; exact this
        · intro w hne
          by_cases hw : w = v
          · subst hw
            rcases hm1v with heq | hf
            · exact absurd heq hne
            · have : I' (m1 w) = false := by
                cases h : I' (m1 w)
                · rfl
                · have hs := hI'sub (m1 w) h; simp [A', hne, hf] at hs
              simp [I, hne, this]
          · by_cases hmw : m1 w = v
            · have heq : w = m1 v := by rw [← hmw, h1]
              subst heq
              rcases hm1v with he | hf
              · exact absurd he hw
              · have : I' (m1 v) = false := by
                  cases h : I' (m1 v)
                  · rfl
                  · have hs := hI'sub (m1 v) h; simp [A', hw, hf] at hs
                simp [I, hw, this]
            · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm1 w hne
        · intro w hne
          by_cases hw : w = v
          · subst hw
            rcases hm2v with heq | hf
            · exact absurd heq hne
            · have : I' (m2 w) = false := by
                cases h : I' (m2 w)
                · rfl
                · have hs := hI'sub (m2 w) h; simp [A', hne, hf] at hs
              simp [I, hne, this]
          · by_cases hmw : m2 w = v
            · have heq : w = m2 v := by rw [← hmw, h2]
              subst heq
              rcases hm2v with he | hf
              · exact absurd he hw
              · have : I' (m2 v) = false := by
                  cases h : I' (m2 v)
                  · rfl
                  · have hs := hI'sub (m2 v) h; simp [A', hw, hf] at hs
                simp [I, hw, this]
            · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm2 w hne
      · by_cases hd1 : 0 < countFin hasDeg1_m1
        · obtain ⟨v, hv⟩ := exists_of_countFin_pos hasDeg1_m1 hd1
          have hAv : A v = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).1).1
          have hne_vu : m1 v ≠ v := by
            have := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).1).2
            simpa using this
          let u := m1 v
          have hAu : A u = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).2
          have hm2v : m2 v = v ∨ A (m2 v) = false ∨ m2 v = u := by
            have h := (Bool.and_eq_true_iff.1 hv).2
            rcases Bool.or_eq_true_iff.1 h with h12 | h3
            · rcases Bool.or_eq_true_iff.1 h12 with h1' | h2'
              · exact Or.inl (beq_iff_eq.1 h1')
              · exact Or.inr (Or.inl (by simpa using h2'))
            · exact Or.inr (Or.inr (beq_iff_eq.1 h3))
          let A1 : Fin n → Bool := fun w => if w = v then false else A w
          let A2 : Fin n → Bool := fun w => if w = u then false else A1 w
          have hcnt1 : countFin A1 + 1 = countFin A := countFin_update_false A v hAv
          have hne_uv : u ≠ v := hne_vu
          have hA1u : A1 u = true := by dsimp only [A1]; simp [hne_uv, hAu]
          have hcnt2 : countFin A2 + 1 = countFin A1 := countFin_update_false A1 u hA1u
          obtain ⟨I', hI'sub, hI'm1, hI'm2, hI'cnt⟩ := ih A2 (by omega)
          let I : Fin n → Bool := fun w => if w = v then true else I' w
          have hI'v : I' v = false := by
            cases h : I' v
            · rfl
            · have := hI'sub v h; simp [A2, A1] at this
          have hI'u : I' u = false := by
            cases h : I' u
            · rfl
            · have := hI'sub u h; simp [A2] at this
          have hcntI : countFin I' + 1 = countFin I := by
            have := countFin_update_false I v (by simp [I])
            have heq : ∀ w, (if w = v then false else I w) = I' w := by
              intro w; by_cases hw : w = v
              · subst hw; simp [hI'v]
              · simp [I, hw]
            rw [countFin_eq_of_eq _ I' heq] at this
            exact this
          have hIu : I u = false := by dsimp only [I]; simp [hne_uv, hI'u]
          refine ⟨I, ?_, ?_, ?_, by omega⟩
          · intro w hw; by_cases h : w = v
            · subst h; exact hAv
            · simp [I, h] at hw
              have := hI'sub w hw
              by_cases hu : w = u
              · simp [A2, hu] at this
              · simp [A2, A1, hu, h] at this; exact this
          · intro w hne
            by_cases hw : w = v
            · rw [hw]; change (I v && I u) = false; rw [hIu, Bool.and_false]
            · by_cases hmw : m1 w = v
              · have heq : w = u := by dsimp only [u]; rw [← hmw, h1]
                rw [heq, hIu, Bool.false_and]
              · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm1 w hne
          · intro w hne
            by_cases hw : w = v
            · rw [hw]
              rcases hm2v with he | hf | hu
              · exact absurd he (by rwa [hw] at hne)
              · have : I' (m2 v) = false := by
                  cases h : I' (m2 v)
                  · rfl
                  · have hs := hI'sub (m2 v) h
                    have hne_mv : m2 v ≠ v := by rwa [hw] at hne
                    by_cases hmu : m2 v = u
                    · simp [A2, hmu] at hs
                    · simp [A2, A1, hmu, hne_mv, hf] at hs
                have hne_mv : m2 v ≠ v := by rwa [hw] at hne
                simp [I, hne_mv, this]
              · rw [hu, hIu, Bool.and_false]
            · by_cases hmw : m2 w = v
              · have heq : w = m2 v := by rw [← hmw, h2]
                rw [heq]
                rcases hm2v with he | hf | hu
                · rw [he] at heq; exact absurd heq hw
                · have : I' (m2 v) = false := by
                    cases h : I' (m2 v)
                    · rfl
                    · have hs := hI'sub (m2 v) h
                      have hne_mv : m2 v ≠ v := by rwa [← heq]
                      by_cases hmu : m2 v = u
                      · simp [A2, hmu] at hs
                      · simp [A2, A1, hmu, hne_mv, hf] at hs
                  have hne_mv : m2 v ≠ v := by rwa [← heq]
                  simp [I, hne_mv, this]
                · rw [hu, hIu, Bool.false_and]
              · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm2 w hne
        · by_cases hd2 : 0 < countFin hasDeg1_m2
          · obtain ⟨v, hv⟩ := exists_of_countFin_pos hasDeg1_m2 hd2
            have hAv : A v = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).1).1
            have hne_vu : m2 v ≠ v := by
              have := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).1).2
              simpa using this
            let u := m2 v
            have hAu : A u = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hv).1).2
            have hm1v : m1 v = v ∨ A (m1 v) = false ∨ m1 v = u := by
              have h := (Bool.and_eq_true_iff.1 hv).2
              rcases Bool.or_eq_true_iff.1 h with h12 | h3
              · rcases Bool.or_eq_true_iff.1 h12 with h1' | h2'
                · exact Or.inl (beq_iff_eq.1 h1')
                · exact Or.inr (Or.inl (by simpa using h2'))
              · exact Or.inr (Or.inr (beq_iff_eq.1 h3))
            let A1 : Fin n → Bool := fun w => if w = v then false else A w
            let A2 : Fin n → Bool := fun w => if w = u then false else A1 w
            have hcnt1 : countFin A1 + 1 = countFin A := countFin_update_false A v hAv
            have hne_uv : u ≠ v := hne_vu
            have hA1u : A1 u = true := by dsimp only [A1]; simp [hne_uv, hAu]
            have hcnt2 : countFin A2 + 1 = countFin A1 := countFin_update_false A1 u hA1u
            obtain ⟨I', hI'sub, hI'm1, hI'm2, hI'cnt⟩ := ih A2 (by omega)
            let I : Fin n → Bool := fun w => if w = v then true else I' w
            have hI'v : I' v = false := by
              cases h : I' v
              · rfl
              · have := hI'sub v h; simp [A2, A1] at this
            have hI'u : I' u = false := by
              cases h : I' u
              · rfl
              · have := hI'sub u h; simp [A2] at this
            have hcntI : countFin I' + 1 = countFin I := by
              have := countFin_update_false I v (by simp [I])
              have heq : ∀ w, (if w = v then false else I w) = I' w := by
                intro w; by_cases hw : w = v
                · subst hw; simp [hI'v]
                · simp [I, hw]
              rw [countFin_eq_of_eq _ I' heq] at this
              exact this
            have hIu : I u = false := by dsimp only [I]; simp [hne_uv, hI'u]
            refine ⟨I, ?_, ?_, ?_, by omega⟩
            · intro w hw; by_cases h : w = v
              · subst h; exact hAv
              · simp [I, h] at hw
                have := hI'sub w hw
                by_cases hu : w = u
                · simp [A2, hu] at this
                · simp [A2, A1, hu, h] at this; exact this
            · intro w hne
              by_cases hw : w = v
              · rw [hw]
                rcases hm1v with he | hf | hu
                · exact absurd he (by rwa [hw] at hne)
                · have : I' (m1 v) = false := by
                    cases h : I' (m1 v)
                    · rfl
                    · have hs := hI'sub (m1 v) h
                      have hne_mv : m1 v ≠ v := by rwa [hw] at hne
                      by_cases hmu : m1 v = u
                      · simp [A2, hmu] at hs
                      · simp [A2, A1, hmu, hne_mv, hf] at hs
                  have hne_mv : m1 v ≠ v := by rwa [hw] at hne
                  simp [I, hne_mv, this]
                · rw [hu, hIu, Bool.and_false]
              · by_cases hmw : m1 w = v
                · have heq : w = m1 v := by rw [← hmw, h1]
                  rw [heq]
                  rcases hm1v with he | hf | hu
                  · rw [he] at heq; exact absurd heq hw
                  · have : I' (m1 v) = false := by
                      cases h : I' (m1 v)
                      · rfl
                      · have hs := hI'sub (m1 v) h
                        have hne_mv : m1 v ≠ v := by rwa [← heq]
                        by_cases hmu : m1 v = u
                        · simp [A2, hmu] at hs
                        · simp [A2, A1, hmu, hne_mv, hf] at hs
                    have hne_mv : m1 v ≠ v := by rwa [← heq]
                    simp [I, hne_mv, this]
                  · rw [hu, hIu, Bool.false_and]
                · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm1 w hne
            · intro w hne
              by_cases hw : w = v
              · rw [hw]; change (I v && I u) = false; rw [hIu, Bool.and_false]
              · by_cases hmw : m2 w = v
                · have heq : w = u := by dsimp only [u]; rw [← hmw, h2]
                  rw [heq, hIu, Bool.false_and]
                · simp only [I, hw, hmw, ↓reduceIte]; exact hI'm2 w hne
          · -- Every vertex v ∈ A has degree 2 in A with distinct m1 v, m2 v ∈ A!
            have hreg : ∀ v, A v = true →
                m1 v ≠ v ∧ A (m1 v) = true ∧ m2 v ≠ v ∧ A (m2 v) = true ∧ m1 v ≠ m2 v := by
              intro v hAv
              have hz0 := (countFin_eq_zero_iff hasDeg0).1 (by omega) v
              have hz1 := (countFin_eq_zero_iff hasDeg1_m1).1 (by omega) v
              have hz2 := (countFin_eq_zero_iff hasDeg1_m2).1 (by omega) v
              dsimp only [hasDeg0, hasDeg1_m1, hasDeg1_m2] at hz0 hz1 hz2
              have hm1_ok : m1 v ≠ v ∧ A (m1 v) = true := by
                by_cases he : m1 v = v
                · simp [hAv, he] at hz0 hz2
                  by_cases he2 : m2 v = v
                  · simp [he2] at hz0
                  · cases ha2 : A (m2 v)
                    · simp [ha2] at hz0
                    · simp [he2, ha2] at hz2
                · cases ha1 : A (m1 v)
                  · simp [hAv, ha1] at hz0 hz2
                    by_cases he2 : m2 v = v
                    · simp [he2] at hz0
                    · cases ha2 : A (m2 v)
                      · simp [ha2] at hz0
                      · simp [he2, ha2] at hz2
                  · exact ⟨he, rfl⟩
              have hm2_ok : m2 v ≠ v ∧ A (m2 v) = true ∧ m1 v ≠ m2 v := by
                by_cases he2 : m2 v = v
                · simp [hAv, hm1_ok.1, hm1_ok.2, he2] at hz1
                · cases ha2 : A (m2 v)
                  · simp [hAv, hm1_ok.1, hm1_ok.2, ha2] at hz1
                  · by_cases heq12 : m2 v = m1 v
                    · simp [hAv, hm1_ok.1, hm1_ok.2, heq12] at hz1
                    · exact ⟨he2, rfl, Ne.symm heq12⟩
              exact ⟨hm1_ok.1, hm1_ok.2, hm2_ok.1, hm2_ok.2.1, hm2_ok.2.2⟩
            obtain ⟨w0, hw0⟩ := exists_of_countFin_pos A (by omega)
            let f : Fin n → Fin n := fun w => m2 (m1 w)
            let g : Fin n → Fin n := fun w => m1 (m2 w)
            have hf_A : ∀ w, A w = true → A (f w) = true := fun w hw =>
              (hreg (m1 w) (hreg w hw).2.1).2.2.2.1
            have hiter_f_A : ∀ j, A (iterF f j w0) = true := by
              intro j; induction j with
              | zero => exact hw0
              | succ j ihj => exact hf_A _ ihj
            have hper_ex : ∃ p, 0 < p ∧ iterF f p w0 = w0 := by
              have hnotnd : ¬ ((List.range (n + 1)).map (fun t => iterF f t w0)).Nodup := by
                intro hnd
                have hsub : ∀ x ∈ ((List.range (n + 1)).map (fun t => iterF f t w0)), x ∈ List.finRange n :=
                  fun x _ => List.mem_finRange x
                have hle : ((List.range (n + 1)).map (fun t => iterF f t w0)).length ≤ (List.finRange n).length :=
                  List.Nodup.length_le_of_subset hnd hsub
                simp only [List.length_map, List.length_range, List.length_finRange] at hle
                omega
              obtain ⟨a, _, b, _, hab, heq⟩ :=
                exists_dup_of_not_nodup_map (fun t => iterF f t w0) (List.range (n + 1)) List.nodup_range hnotnd
              have hpair : ∃ lo hi, lo < hi ∧ iterF f lo w0 = iterF f hi w0 := by
                by_cases hlt : a < b
                · exact ⟨a, b, hlt, heq⟩
                · exact ⟨b, a, by omega, heq.symm⟩
              rcases hpair with ⟨lo, hi, hlt, hfeq⟩
              refine ⟨hi - lo, by omega, ?_⟩
              have hhi : hi = (hi - lo) + lo := by omega
              rw [hhi, iterF_add] at hfeq
              have hcancel := congrArg (iterF g lo) hfeq
              have hc1 : iterF g lo (iterF f lo w0) = w0 := iterF_inv_cancel m1 m2 h1 h2 lo w0
              have hc2 : iterF g lo (iterF f (hi - lo) (iterF f lo w0)) = iterF f (hi - lo) w0 := by
                have hcomm : iterF f (hi - lo) (iterF f lo w0) = iterF f lo (iterF f (hi - lo) w0) := by
                  rw [← iterF_add, ← iterF_add, Nat.add_comm]
                rw [hcomm, iterF_inv_cancel m1 m2 h1 h2 lo]
              rw [hc1, hc2] at hcancel
              exact hcancel.symm
            rcases hper_ex with ⟨p, hp_pos, hper⟩
            let Ceven : Fin n → Bool := fun w => (List.range p).any (fun t => iterF f t w0 == w)
            let Codd : Fin n → Bool := fun w => Ceven (m1 w)
            have hCeven_iff : ∀ w, Ceven w = true ↔ ∃ t < p, iterF f t w0 = w := by
              intro w; dsimp only [Ceven]
              rw [List.any_eq_true]
              constructor
              · rintro ⟨t, ht, hteq⟩
                exact ⟨t, List.mem_range.1 ht, beq_iff_eq.1 hteq⟩
              · rintro ⟨t, ht, hteq⟩
                exact ⟨t, List.mem_range.2 ht, beq_iff_eq.2 hteq⟩
            have hCeven_sub : ∀ w, Ceven w = true → A w = true := by
              intro w hw
              rcases (hCeven_iff w).1 hw with ⟨t, _, rfl⟩
              exact hiter_f_A t
            have hCodd_sub : ∀ w, Codd w = true → A w = true := by
              intro w hw
              have h1w : A (m1 w) = true := hCeven_sub (m1 w) hw
              have := (hreg (m1 w) h1w).2.1
              rwa [h1] at this
            have hCeven_f : ∀ w, Ceven w = true → Ceven (f w) = true := by
              intro w hw
              rcases (hCeven_iff w).1 hw with ⟨t, ht, rfl⟩
              by_cases hlast : t + 1 < p
              · exact (hCeven_iff _).2 ⟨t + 1, hlast, rfl⟩
              · have htp : t + 1 = p := by omega
                have hfw : f (iterF f t w0) = iterF f 0 w0 := by
                  change iterF f (t + 1) w0 = w0; rw [htp, hper]
                exact (hCeven_iff _).2 ⟨0, hp_pos, hfw.symm⟩
            have hCeven_g : ∀ w, Ceven w = true → Ceven (g w) = true := by
              intro w hw
              rcases (hCeven_iff w).1 hw with ⟨t, ht, rfl⟩
              cases t with
              | zero =>
                have hgw : g (iterF f 0 w0) = iterF f (p - 1) w0 := by
                  change g w0 = iterF f (p - 1) w0
                  have h1p : iterF f 1 (iterF f (p - 1) w0) = w0 := by
                    rw [← iterF_add f 1 (p - 1) w0, show 1 + (p - 1) = p by omega]
                    exact hper
                  have h2p := congrArg (iterF g 1) h1p
                  rw [iterF_inv_cancel m1 m2 h1 h2 1] at h2p
                  exact h2p.symm
                exact (hCeven_iff _).2 ⟨p - 1, by omega, hgw.symm⟩
              | succ t' =>
                have hgw : g (iterF f (t' + 1) w0) = iterF f t' w0 := by
                  change m1 (m2 (m2 (m1 (iterF f t' w0)))) = iterF f t' w0
                  rw [h2, h1]
                exact (hCeven_iff _).2 ⟨t', by omega, hgw.symm⟩
            have hdisj_eo : ∀ w, (Ceven w && Codd w) = false := by
              intro w
              cases he : Ceven w
              · rfl
              · cases ho : Codd w
                · rfl
                · exfalso
                  rcases (hCeven_iff w).1 he with ⟨b, _, hbw⟩
                  rcases (hCeven_iff (m1 w)).1 ho with ⟨a, _, ham1⟩
                  have hm1b : m1 (iterF f b w0) = iterF f a w0 := by rw [hbw, ham1]
                  have hm1a : m1 (iterF f a w0) = iterF f b w0 := by rw [← hm1b, h1]
                  have hmid_even : ∀ u v r s, r = u + s → v = r + s →
                      m1 (iterF f u w0) = iterF f v w0 → False := by
                    intro u v r s hru hvr hm1u
                    have h1' : m1 (iterF f r w0) = iterF g s (m1 (iterF f u w0)) := by
                      rw [hru, Nat.add_comm u s, iterF_add, iterF_m1_comm m1 m2 h1 h2 s]
                    rw [hm1u, hvr, Nat.add_comm r s, iterF_add, iterF_inv_cancel m1 m2 h1 h2 s] at h1'
                    exact (hreg (iterF f r w0) (hiter_f_A r)).1 h1'
                  have hmid_odd : ∀ u v r s, r = u + s → v = r + 1 + s →
                      m1 (iterF f u w0) = iterF f v w0 → False := by
                    intro u v r s hru hvr hm1u
                    have h1' : m1 (iterF f r w0) = iterF g s (m1 (iterF f u w0)) := by
                      rw [hru, Nat.add_comm u s, iterF_add, iterF_m1_comm m1 m2 h1 h2 s]
                    rw [hm1u, hvr, Nat.add_comm (r + 1) s, iterF_add, iterF_inv_cancel m1 m2 h1 h2 s] at h1'
                    have h2' : m2 (m1 (iterF f r w0)) = m1 (iterF f r w0) := h1'.symm
                    have hAm : A (m1 (iterF f r w0)) = true := (hreg (iterF f r w0) (hiter_f_A r)).2.1
                    exact (hreg _ hAm).2.2.1 h2'
                  by_cases heven : (a + b) % 2 = 0
                  · let r := (a + b) / 2
                    by_cases hra : a ≤ r
                    · exact hmid_even a b r (r - a) (by omega) (by omega) hm1a
                    · exact hmid_even b a r (r - b) (by omega) (by omega) hm1b
                  · let r := (a + b) / 2
                    by_cases hra : a ≤ r
                    · exact hmid_odd a b r (r - a) (by omega) (by omega) hm1a
                    · exact hmid_odd b a r (r - b) (by omega) (by omega) hm1b
            have hCeven_w0 : Ceven w0 = true := (hCeven_iff w0).2 ⟨0, hp_pos, rfl⟩
            have hcnt_even_pos : 0 < countFin Ceven := by
              have hnz : countFin Ceven ≠ 0 := by
                intro hz; have := (countFin_eq_zero_iff Ceven).1 hz w0
                rw [hCeven_w0] at this; cases this
              omega
            have hcnt_odd_eq : countFin Codd = countFin Ceven := countFin_comp_invol m1 h1 Ceven
            let C : Fin n → Bool := fun w => Ceven w || Codd w
            have hcntC : countFin C = countFin Ceven + countFin Ceven := by
              rw [countFin_add_disjoint Ceven Codd hdisj_eo, hcnt_odd_eq]
            let A' : Fin n → Bool := fun w => A w && !C w
            have hdisj_AC : ∀ w, (A' w && C w) = false := by
              intro w; cases hc : C w <;> simp [A', hc]
            have hA_split : ∀ w, A w = (A' w || C w) := by
              intro w
              cases hc : C w
              · simp [A', hc]
              · simp only [A', hc, Bool.not_true, Bool.and_false, Bool.false_or]
                rcases Bool.or_eq_true_iff.1 hc with he | ho
                · exact hCeven_sub w he
                · exact hCodd_sub w ho
            have hcntA_split : countFin A = countFin A' + countFin C := by
              rw [countFin_eq_of_eq A _ hA_split, countFin_add_disjoint A' C hdisj_AC]
            obtain ⟨I', hI'sub, hI'm1, hI'm2, hI'cnt⟩ := ih A' (by omega)
            let I : Fin n → Bool := fun w => I' w || Ceven w
            have hdisj_Ie : ∀ w, (I' w && Ceven w) = false := by
              intro w
              cases hi' : I' w
              · rfl
              · have := hI'sub w hi'
                cases he : Ceven w
                · rfl
                · simp [A', C, he] at this
            have hcntI : countFin I = countFin I' + countFin Ceven :=
              countFin_add_disjoint I' Ceven hdisj_Ie
            have hm1_eo : ∀ w, Ceven w = true → Codd (m1 w) = true := fun w hw => by
              dsimp only [Codd]; rwa [h1]
            have hm2_eo : ∀ w, Ceven w = true → Codd (m2 w) = true := fun w hw => hCeven_g w hw
            have hI'_not_C : ∀ w, C w = true → I' w = false := by
              intro w hcw
              cases hi' : I' w
              · rfl
              · have := hI'sub w hi'; simp [A', hcw] at this
            refine ⟨I, ?_, ?_, ?_, by omega⟩
            · intro w hw
              rcases Bool.or_eq_true_iff.1 hw with hi' | he
              · exact (Bool.and_eq_true_iff.1 (hI'sub w hi')).1
              · exact hCeven_sub w he
            · intro w hne
              cases he : Ceven w
              · cases hm1e : Ceven (m1 w)
                · simp only [I, he, hm1e, Bool.or_false]; exact hI'm1 w hne
                · have hcw : C w = true := by
                    dsimp only [C]; rw [Bool.or_eq_true_iff]; right; exact hm1e
                  simp [I, he, hm1e, hI'_not_C w hcw]
              · have hco : Codd (m1 w) = true := hm1_eo w he
                have hne_e : Ceven (m1 w) = false := by
                  have hd := hdisj_eo (m1 w)
                  cases h' : Ceven (m1 w)
                  · rfl
                  · simp [h', hco] at hd
                have hcm : C (m1 w) = true := by dsimp only [C]; simp [hco]
                simp [I, he, hne_e, hI'_not_C (m1 w) hcm]
            · intro w hne
              cases he : Ceven w
              · cases hm2e : Ceven (m2 w)
                · simp only [I, he, hm2e, Bool.or_false]; exact hI'm2 w hne
                · have hcw : C w = true := by
                    dsimp only [C]; rw [Bool.or_eq_true_iff]; right
                    have := hm2_eo (m2 w) hm2e
                    rwa [h2] at this
                  simp [I, he, hm2e, hI'_not_C w hcw]
              · have hco : Codd (m2 w) = true := hm2_eo w he
                have hne_e : Ceven (m2 w) = false := by
                  have hd := hdisj_eo (m2 w)
                  cases h' : Ceven (m2 w)
                  · rfl
                  · simp [h', hco] at hd
                have hcm : C (m2 w) = true := by dsimp only [C]; simp [hco]
                simp [I, he, hne_e, hI'_not_C (m2 w) hcm]

/-! ## 3. Layer Decomposition of `netDepth` into Involutions -/

private theorem applyCompBool_self {n : Nat} (u : Fin n) (v : Fin n → Bool) :
    applyCompBool (u, u) v = v := by
  funext k
  unfold applyCompBool
  by_cases hk : k = u
  · subst hk; simp
  · simp [hk]

private theorem applyCompBool_comm {n : Nat} (c1 c2 : Fin n × Fin n)
    (h : c1.1 ≠ c2.1 ∧ c1.1 ≠ c2.2 ∧ c1.2 ≠ c2.1 ∧ c1.2 ≠ c2.2) (v : Fin n → Bool) :
    applyCompBool c1 (applyCompBool c2 v) = applyCompBool c2 (applyCompBool c1 v) := by
  funext k
  unfold applyCompBool
  by_cases o1 : c1.1.val ≤ c1.2.val <;> by_cases o2 : c2.1.val ≤ c2.2.val <;>
    simp only [o1, o2, ↓reduceIte] <;>
    by_cases h1 : k = c1.1 <;> by_cases h2 : k = c1.2 <;>
    by_cases h3 : k = c2.1 <;> by_cases h4 : k = c2.2 <;>
    simp_all [Ne.symm]

private def InLayer {n : Nat} (w : Fin n) (L : Net n) : Prop :=
  ∃ c ∈ L, w = c.1 ∨ w = c.2

private def IsMatching {n : Nat} : Net n → Prop
  | [] => True
  | c :: L => c.1 ≠ c.2 ∧ ¬ InLayer c.1 L ∧ ¬ InLayer c.2 L ∧ IsMatching L

private theorem evalBool_cons {n : Nat} (c : Fin n × Fin n) (L : Net n) (v : Fin n → Bool) :
    evalBool (c :: L) v = evalBool L (applyCompBool c v) := rfl

private theorem evalBool_append {n : Nat} (L1 L2 : Net n) (v : Fin n → Bool) :
    evalBool (L1 ++ L2) v = evalBool L2 (evalBool L1 v) := by
  unfold evalBool
  exact List.foldl_append

private theorem applyCompBool_comm_layer {n : Nat} (c : Fin n × Fin n) (L : Net n)
    (h1 : ¬ InLayer c.1 L) (h2 : ¬ InLayer c.2 L) (v : Fin n → Bool) :
    evalBool L (applyCompBool c v) = applyCompBool c (evalBool L v) := by
  induction L generalizing v with
  | nil => rfl
  | cons p ps ih =>
    have hdisj : p.1 ≠ c.1 ∧ p.1 ≠ c.2 ∧ p.2 ≠ c.1 ∧ p.2 ≠ c.2 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro he; exact h1 ⟨p, List.mem_cons_self, Or.inl he.symm⟩
      · intro he; exact h2 ⟨p, List.mem_cons_self, Or.inl he.symm⟩
      · intro he; exact h1 ⟨p, List.mem_cons_self, Or.inr he.symm⟩
      · intro he; exact h2 ⟨p, List.mem_cons_self, Or.inr he.symm⟩
    have h1' : ¬ InLayer c.1 ps := fun ⟨q, hq, hw⟩ => h1 ⟨q, List.mem_cons_of_mem p hq, hw⟩
    have h2' : ¬ InLayer c.2 ps := fun ⟨q, hq, hw⟩ => h2 ⟨q, List.mem_cons_of_mem p hq, hw⟩
    rw [evalBool_cons, evalBool_cons, applyCompBool_comm p c hdisj, ih h1' h2']

private theorem isMatching_append_single {n : Nat} (L : Net n) (c : Fin n × Fin n)
    (hm : IsMatching L) (hne : c.1 ≠ c.2) (h1 : ¬ InLayer c.1 L) (h2 : ¬ InLayer c.2 L) :
    IsMatching (L ++ [c]) := by
  induction L with
  | nil =>
    refine ⟨hne, ?_, ?_, trivial⟩
    · rintro ⟨_, h, _⟩; cases h
    · rintro ⟨_, h, _⟩; cases h
  | cons p ps ih =>
    rcases hm with ⟨hpne, hp1, hp2, hmps⟩
    have h1' : ¬ InLayer c.1 ps := fun ⟨q, hq, hw⟩ => h1 ⟨q, List.mem_cons_of_mem p hq, hw⟩
    have h2' : ¬ InLayer c.2 ps := fun ⟨q, hq, hw⟩ => h2 ⟨q, List.mem_cons_of_mem p hq, hw⟩
    refine ⟨hpne, ?_, ?_, ih hmps h1' h2'⟩
    · rintro ⟨q, hq, hw⟩
      rcases List.mem_append.1 hq with hq' | hq'
      · exact hp1 ⟨q, hq', hw⟩
      · simp at hq'; rcases hq' with rfl
        rcases hw with he | he
        · exact h1 ⟨p, List.mem_cons_self, Or.inl he.symm⟩
        · exact h2 ⟨p, List.mem_cons_self, Or.inl he.symm⟩
    · rintro ⟨q, hq, hw⟩
      rcases List.mem_append.1 hq with hq' | hq'
      · exact hp2 ⟨q, hq', hw⟩
      · simp at hq'; rcases hq' with rfl
        rcases hw with he | he
        · exact h1 ⟨p, List.mem_cons_self, Or.inr he.symm⟩
        · exact h2 ⟨p, List.mem_cons_self, Or.inr he.symm⟩

private def mateOf {n : Nat} : Net n → Fin n → Fin n
  | [], w => w
  | (a, b) :: rest, w => if w = a then b else if w = b then a else mateOf rest w

private def applyInv {n : Nat} (m : Fin n → Fin n) (v : Fin n → Bool) (w : Fin n) : Bool :=
  if w.val ≤ (m w).val then v w && v (m w) else v (m w) || v w

private theorem mateOf_not_in {n : Nat} (L : Net n) (w : Fin n) (h : ¬ InLayer w L) :
    mateOf L w = w := by
  induction L with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    have ha : w ≠ a := fun he => h ⟨(a, b), List.mem_cons_self, Or.inl he⟩
    have hb : w ≠ b := fun he => h ⟨(a, b), List.mem_cons_self, Or.inr he⟩
    have hps : ¬ InLayer w ps := fun ⟨q, hq, hw⟩ => h ⟨q, List.mem_cons_of_mem (a, b) hq, hw⟩
    simp [mateOf, ha, hb, ih hps]

private theorem mateOf_invol {n : Nat} (L : Net n) :
    IsMatching L → ∀ w, mateOf L (mateOf L w) = w := by
  induction L with
  | nil => intro _ _; rfl
  | cons p ps ih =>
    intro hm w
    rcases p with ⟨a, b⟩
    rcases hm with ⟨hne, ha, hb, hmps⟩
    dsimp only [mateOf]
    by_cases hwa : w = a
    · subst hwa; simp [Ne.symm hne]
    · by_cases hwb : w = b
      · subst hwb; simp [hne]
      · simp only [hwa, hwb, ↓reduceIte]
        have hma : mateOf ps w ≠ a := by
          intro he
          have h1 := ih hmps w
          rw [he, mateOf_not_in ps a ha] at h1
          exact hwa h1.symm
        have hmb : mateOf ps w ≠ b := by
          intro he
          have h1 := ih hmps w
          rw [he, mateOf_not_in ps b hb] at h1
          exact hwb h1.symm
        simp [hma, hmb, ih hmps w]

private theorem evalBool_eq_applyInv {n : Nat} (L : Net n) :
    IsMatching L → ∀ v, evalBool L v = applyInv (mateOf L) v := by
  induction L with
  | nil =>
    intro _ v; funext w; simp [evalBool, applyInv, mateOf]
  | cons p ps ih =>
    intro hm v
    rcases p with ⟨a, b⟩
    rcases hm with ⟨hne, ha, hb, hmps⟩
    rw [evalBool_cons, ih hmps]
    funext w
    dsimp only [applyInv, mateOf]
    by_cases hwa : w = a
    · subst hwa
      have hma : mateOf ps w = w := mateOf_not_in ps w ha
      simp only [↓reduceIte, hma, Nat.le_refl, Bool.and_self]
      unfold applyCompBool; dsimp only
      by_cases hab : w.val ≤ b.val
      · simp [hab]
      · simp [hab, hne]
    · by_cases hwb : w = b
      · subst hwb
        have hmb : mateOf ps w = w := mateOf_not_in ps w hb
        simp only [hwa, ↓reduceIte, hmb, Nat.le_refl, Bool.and_self]
        unfold applyCompBool; dsimp only
        by_cases hab : a.val ≤ w.val
        · have hnot : ¬ (w.val ≤ a.val) := by
            have : w.val ≠ a.val := fun he => hwa (Fin.ext he)
            omega
          simp [hab, hnot, hwa]
        · have hwa_le : w.val ≤ a.val := by omega
          simp [hab, hwa_le, Bool.and_comm]
      · simp only [hwa, hwb, ↓reduceIte]
        have hma : mateOf ps w ≠ a := by
          intro he
          have h1 := mateOf_invol ps hmps w
          rw [he, mateOf_not_in ps a ha] at h1
          exact hwa h1.symm
        have hmb : mateOf ps w ≠ b := by
          intro he
          have h1 := mateOf_invol ps hmps w
          rw [he, mateOf_not_in ps b hb] at h1
          exact hwb h1.symm
        have hv1 : applyCompBool (a, b) v w = v w := by
          unfold applyCompBool; dsimp only
          split <;> simp [hwa, hwb]
        have hv2 : applyCompBool (a, b) v (mateOf ps w) = v (mateOf ps w) := by
          unfold applyCompBool; dsimp only
          split <;> simp [hma, hmb]
        rw [hv1, hv2]

private def evalBuckets {n : Nat} (d : Nat) (B : Nat → Net n) (v : Fin n → Bool) : Fin n → Bool :=
  (List.range d).foldl (fun acc t => evalBool (B (t + 1)) acc) v

private theorem evalBuckets_succ {n : Nat} (d : Nat) (B : Nat → Net n) (v : Fin n → Bool) :
    evalBuckets (d + 1) B v = evalBool (B (d + 1)) (evalBuckets d B v) := by
  unfold evalBuckets
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem evalBuckets_append_at {n : Nat} (d : Nat) (B : Nat → Net n)
    (t0 : Nat) (c : Fin n × Fin n) (ht0_pos : 1 ≤ t0) (ht0_le : t0 ≤ d)
    (hdisj : ∀ s, t0 < s → s ≤ d → ¬ InLayer c.1 (B s) ∧ ¬ InLayer c.2 (B s))
    (v : Fin n → Bool) :
    evalBuckets d (fun s => if s = t0 then B s ++ [c] else B s) v =
    applyCompBool c (evalBuckets d B v) := by
  induction d with
  | zero => omega
  | succ d ih =>
    rw [evalBuckets_succ, evalBuckets_succ]
    by_cases htd : d + 1 = t0
    · rw [htd]
      have heqB : ∀ v0, evalBuckets d (fun s => if s = t0 then B s ++ [c] else B s) v0 =
          evalBuckets d B v0 := by
        intro v0
        unfold evalBuckets
        have haux : ∀ (l : List Nat) (acc : Fin n → Bool),
            (∀ x ∈ l, x + 1 ≠ t0) →
            l.foldl (fun acc t => evalBool (if t + 1 = t0 then B (t + 1) ++ [c] else B (t + 1)) acc) acc =
            l.foldl (fun acc t => evalBool (B (t + 1)) acc) acc := by
          intro l
          induction l with
          | nil => intro acc _; rfl
          | cons x xs ihx =>
            intro acc hne
            have hx : x + 1 ≠ t0 := hne x List.mem_cons_self
            simp only [List.foldl_cons, hx, ↓reduceIte]
            exact ihx _ (fun y hy => hne y (List.mem_cons_of_mem x hy))
        exact haux (List.range d) v0 (fun x hx => by have := List.mem_range.1 hx; omega)
      simp only [↓reduceIte, heqB]
      rw [evalBool_append]
      rfl
    · have ht0_le' : t0 ≤ d := by omega
      have hdisj' : ∀ s, t0 < s → s ≤ d → ¬ InLayer c.1 (B s) ∧ ¬ InLayer c.2 (B s) :=
        fun s h1 h2 => hdisj s h1 (by omega)
      have htop := hdisj (d + 1) (by omega) (Nat.le_refl _)
      simp only [htd, ↓reduceIte]
      rw [ih ht0_le' hdisj', applyCompBool_comm_layer c (B (d + 1)) htop.1 htop.2]

private def depthStep {n : Nat} (acc : Array Nat) (c : Fin n × Fin n) : Array Nat :=
  let d := Nat.max (acc.getD c.1.val 0) (acc.getD c.2.val 0) + 1
  (acc.set! c.1.val d).set! c.2.val d

private theorem array_size_set! (a : Array Nat) (i v : Nat) : (a.set! i v).size = a.size := by
  by_cases h : i < a.size <;> simp [Array.set!, Array.setIfInBounds, h]

private theorem array_getD_set!_self (a : Array Nat) (i v : Nat) (hi : i < a.size) :
    (a.set! i v).getD i 0 = v := by
  simp [Array.set!, Array.setIfInBounds, Array.getD, hi]

private theorem nat_max_ge_left (a b : Nat) : a ≤ Nat.max a b := Nat.le_max_left a b

private theorem nat_max_ge_right (a b : Nat) : b ≤ Nat.max a b := Nat.le_max_right a b

private theorem array_getD_set!_ne (a : Array Nat) (i j v : Nat) (hne : i ≠ j) :
    (a.set! i v).getD j 0 = a.getD j 0 := by
  by_cases hi : i < a.size
  · by_cases hj : j < a.size
    · simp [Array.set!, Array.setIfInBounds, Array.getD, hi, hj, Array.getElem_set, hne]
    · simp [Array.set!, Array.setIfInBounds, Array.getD, hi, hj]
  · simp [Array.set!, Array.setIfInBounds, hi]

private theorem depthStep_size {n : Nat} (acc : Array Nat) (c : Fin n × Fin n) :
    (depthStep acc c).size = acc.size := by
  unfold depthStep; rw [array_size_set!, array_size_set!]

private theorem depthStep_mono {n : Nat} (acc : Array Nat) (hsz : acc.size = n)
    (c : Fin n × Fin n) (w : Fin n) :
    acc.getD w.val 0 ≤ (depthStep acc c).getD w.val 0 := by
  unfold depthStep
  dsimp only
  have hc1 := c.1.isLt
  have hc2 := c.2.isLt
  have hm1 := nat_max_ge_left (acc.getD c.1.val 0) (acc.getD c.2.val 0)
  have hm2 := nat_max_ge_right (acc.getD c.1.val 0) (acc.getD c.2.val 0)
  have h1 : c.1.val < acc.size := by omega
  have h2 : c.2.val < (acc.set! c.1.val (Nat.max (acc.getD c.1.val 0) (acc.getD c.2.val 0) + 1)).size := by
    rw [array_size_set!]; omega
  by_cases hw2 : w.val = c.2.val
  · rw [hw2, array_getD_set!_self _ _ _ h2]; omega
  · rw [array_getD_set!_ne _ _ _ _ (Ne.symm hw2)]
    by_cases hw1 : w.val = c.1.val
    · rw [hw1, array_getD_set!_self _ _ _ h1]; omega
    · rw [array_getD_set!_ne _ _ _ _ (Ne.symm hw1)]
      exact Nat.le_refl _

private theorem foldl_depthStep_size {n : Nat} (net : Net n) (acc : Array Nat) :
    (net.foldl depthStep acc).size = acc.size := by
  induction net generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih, depthStep_size]

private theorem foldl_depthStep_mono {n : Nat} (net : Net n) (acc : Array Nat) (hsz : acc.size = n) (w : Fin n) :
    acc.getD w.val 0 ≤ (net.foldl depthStep acc).getD w.val 0 := by
  induction net generalizing acc with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have h1 := depthStep_mono acc hsz c w
    have h2 := ih (depthStep acc c) (by rw [depthStep_size, hsz])
    omega

private theorem foldl_max_ge_init (l : List Nat) (init : Nat) :
    init ≤ l.foldl Nat.max init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h1 := nat_max_ge_left init x
    have h2 := ih (Nat.max init x)
    omega

private theorem foldl_max_ge_mem (l : List Nat) (init x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl Nat.max init := by
  induction l generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := nat_max_ge_right init x
      have h2 := foldl_max_ge_init ys (Nat.max init x)
      omega
    · exact ih (Nat.max init y) hx'

private theorem array_getD_le_foldl_max (a : Array Nat) (i : Nat) (hi : i < a.size) :
    a.getD i 0 ≤ a.foldl Nat.max 0 := by
  cases a with
  | mk l =>
    have hil : i < l.length := hi
    have hget : (Array.mk l).getD i 0 = l[i] := by simp [Array.getD, hil]
    have hfold : (Array.mk l).foldl Nat.max 0 = l.foldl Nat.max 0 := by
      rw [← Array.foldl_toList]
    rw [hget, hfold]
    exact foldl_max_ge_mem l 0 l[i] (List.getElem_mem hil)

private theorem decompose_layers {n : Nat} (net : Net n) (d : Nat) (hd : netDepth net ≤ d) :
    ∃ m : Nat → Fin n → Fin n,
      (∀ t w, m t (m t w) = w) ∧
      (∀ v, evalBool net v = (List.range d).foldl (fun acc t => applyInv (m t) acc) v) := by
  have hgen : ∀ (rest : Net n) (acc : Array Nat) (B : Nat → Net n),
      acc.size = n →
      (rest.foldl depthStep acc).foldl Nat.max 0 ≤ d →
      (∀ t, IsMatching (B t)) →
      (∀ t w, InLayer w (B t) → 1 ≤ t ∧ t ≤ acc.getD w.val 0) →
      ∃ Bf : Nat → Net n,
        (∀ t, IsMatching (Bf t)) ∧
        (∀ v, evalBool rest (evalBuckets d B v) = evalBuckets d Bf v) := by
    intro rest
    induction rest with
    | nil =>
      intro acc B _ _ hm _
      exact ⟨B, hm, fun _ => rfl⟩
    | cons c cs ih =>
      intro acc B hsz hle hm hinv
      let t0 := Nat.max (acc.getD c.1.val 0) (acc.getD c.2.val 0) + 1
      let acc' := depthStep acc c
      have hc1 := c.1.isLt
      have hc2 := c.2.isLt
      have hsz' : acc'.size = n := by rw [depthStep_size, hsz]
      have hle' : (cs.foldl depthStep acc').foldl Nat.max 0 ≤ d := hle
      have ht0_acc'1 : acc'.getD c.1.val 0 = t0 := by
        dsimp only [acc', depthStep, t0]
        by_cases h12 : c.1.val = c.2.val
        · rw [h12, array_getD_set!_self _ _ _ (by rw [array_size_set!]; omega)]
        · rw [array_getD_set!_ne _ _ _ _ (Ne.symm h12), array_getD_set!_self _ _ _ (by omega)]
      have ht0_acc'2 : acc'.getD c.2.val 0 = t0 := by
        dsimp only [acc', depthStep, t0]
        rw [array_getD_set!_self _ _ _ (by rw [array_size_set!]; omega)]
      have ht0_le : t0 ≤ d := by
        have h1 : t0 ≤ (cs.foldl depthStep acc').getD c.1.val 0 := by
          rw [← ht0_acc'1]; exact foldl_depthStep_mono cs acc' hsz' c.1
        have h2 : (cs.foldl depthStep acc').getD c.1.val 0 ≤ (cs.foldl depthStep acc').foldl Nat.max 0 :=
          array_getD_le_foldl_max _ c.1.val (by rw [foldl_depthStep_size, hsz']; exact hc1)
        omega
      by_cases hsame : c.1 = c.2
      · have hinv' : ∀ t w, InLayer w (B t) → 1 ≤ t ∧ t ≤ acc'.getD w.val 0 := by
          intro t w hw
          have ⟨h1, h2⟩ := hinv t w hw
          have hm' := depthStep_mono acc hsz c w
          exact ⟨h1, Nat.le_trans h2 hm'⟩
        obtain ⟨Bf, hmf, hevf⟩ := ih acc' B hsz' hle' hm hinv'
        refine ⟨Bf, hmf, fun v => ?_⟩
        rw [evalBool_cons]
        have hc : applyCompBool c (evalBuckets d B v) = evalBuckets d B v := by
          have : c = (c.1, c.1) := Prod.ext rfl hsame.symm
          rw [this, applyCompBool_self]
        rw [hc]
        exact hevf v
      · let B' : Nat → Net n := fun s => if s = t0 then B s ++ [c] else B s
        have hnotIn : ∀ s, t0 ≤ s → ¬ InLayer c.1 (B s) ∧ ¬ InLayer c.2 (B s) := by
          intro s hs
          have hm1 := nat_max_ge_left (acc.getD c.1.val 0) (acc.getD c.2.val 0)
          have hm2 := nat_max_ge_right (acc.getD c.1.val 0) (acc.getD c.2.val 0)
          constructor
          · intro h1; have := (hinv s c.1 h1).2; omega
          · intro h2; have := (hinv s c.2 h2).2; omega
        have hm' : ∀ t, IsMatching (B' t) := by
          intro t; dsimp only [B']
          by_cases ht : t = t0
          · rw [ht]; simp only [↓reduceIte]
            exact isMatching_append_single (B t0) c (hm t0) hsame (hnotIn t0 (Nat.le_refl _)).1 (hnotIn t0 (Nat.le_refl _)).2
          · simp [ht, hm t]
        have hinv' : ∀ t w, InLayer w (B' t) → 1 ≤ t ∧ t ≤ acc'.getD w.val 0 := by
          intro t w hw
          dsimp only [B'] at hw
          by_cases ht : t = t0
          · rw [ht] at hw ⊢; simp only [↓reduceIte] at hw
            rcases hw with ⟨q, hq, hqw⟩
            rcases List.mem_append.1 hq with hq' | hq'
            · have ⟨h1, h2⟩ := hinv t0 w ⟨q, hq', hqw⟩
              exact ⟨h1, Nat.le_trans h2 (depthStep_mono acc hsz c w)⟩
            · simp at hq'; rcases hq' with rfl
              rcases hqw with rfl | rfl
              · exact ⟨by omega, by rw [ht0_acc'1]; exact Nat.le_refl _⟩
              · exact ⟨by omega, by rw [ht0_acc'2]; exact Nat.le_refl _⟩
          · simp only [ht, ↓reduceIte] at hw
            have ⟨h1, h2⟩ := hinv t w hw
            exact ⟨h1, Nat.le_trans h2 (depthStep_mono acc hsz c w)⟩
        obtain ⟨Bf, hmf, hevf⟩ := ih acc' B' hsz' hle' hm' hinv'
        refine ⟨Bf, hmf, fun v => ?_⟩
        rw [evalBool_cons]
        have hstep := evalBuckets_append_at d B t0 c (by omega) ht0_le
          (fun s hs _ => hnotIn s (by omega)) v
        rw [← hstep]
        exact hevf v
  have hinit_empty : ∀ v : Fin n → Bool, evalBuckets d (fun _ => []) v = v := by
    intro v; unfold evalBuckets
    have : ∀ (l : List Nat) (acc : Fin n → Bool),
        l.foldl (fun acc _ => evalBool ([] : Net n) acc) acc = acc := by
      intro l; induction l with
      | nil => intro acc; rfl
      | cons _ xs ih => intro acc; exact ih acc
    exact this (List.range d) v
  obtain ⟨Bf, hmf, hevf⟩ := hgen net (Array.replicate n 0) (fun _ => [])
    (by simp) hd (fun _ => trivial) (fun _ _ ⟨_, h, _⟩ => by cases h)
  refine ⟨fun t => mateOf (Bf (t + 1)), fun t w => mateOf_invol (Bf (t + 1)) (hmf (t + 1)) w, fun v => ?_⟩
  have hv := hevf v
  rw [hinit_empty v] at hv
  rw [hv]
  unfold evalBuckets
  have haux : ∀ (l : List Nat) (acc : Fin n → Bool),
      l.foldl (fun acc t => evalBool (Bf (t + 1)) acc) acc =
      l.foldl (fun acc t => applyInv (mateOf (Bf (t + 1))) acc) acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons t ts iht =>
      intro acc
      simp only [List.foldl_cons]
      rw [evalBool_eq_applyInv (Bf (t + 1)) (hmf (t + 1)) acc, iht]
  exact haux (List.range d) v

/-! ## 4. The `Realizable` Invariant & 2-Layer Halving Lemma -/

private def Realizable {n : Nat} (f : (Fin n → Bool) → (Fin n → Bool))
    (A : Fin n → Bool) (C : Fin n → Bool) : Prop :=
  ∀ y : Fin n → Bool, (∀ w, A w = false → y w = C w) → ∃ x, f x = y

private def mixedRoute {n : Nat} (m : Fin n → Fin n) (A C : Fin n → Bool) (w : Fin n) : Fin n :=
  let u := m w
  if A w && !A u then
    if (w.val ≤ u.val && C u) || (u.val < w.val && !C u) then w else u
  else if !A w && A u then
    if (u.val ≤ w.val && C w) || (w.val < u.val && !C w) then w else u
  else w

private theorem mixedRoute_invol {n : Nat} (m : Fin n → Fin n) (hm : ∀ w, m (m w) = w)
    (A C : Fin n → Bool) (w : Fin n) :
    mixedRoute m A C (mixedRoute m A C w) = w := by
  dsimp only [mixedRoute]
  cases haw : A w <;> cases hau : A (m w)
  · simp [haw, hau]
  · simp only [haw, hau, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]
    split
    · simp [haw, hau, *]
    · simp only [hm w, hau, haw, Bool.not_false, Bool.true_and, ↓reduceIte]
      have hcond : ¬ (((m w).val ≤ w.val && C w) || (w.val < (m w).val && !C w)) = true := ‹_›
      simp [hcond]
  · simp only [haw, hau, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]
    split
    · simp [haw, hau, *]
    · simp only [hm w, hau, haw, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
        Bool.false_eq_true, ↓reduceIte]
      have hcond : ¬ ((w.val ≤ (m w).val && C (m w)) || ((m w).val < w.val && !C (m w))) = true := ‹_›
      simp [hcond]
  · simp [haw, hau]

private theorem applyInv_no_active_pairs {n : Nat} (f : (Fin n → Bool) → (Fin n → Bool))
    (A C : Fin n → Bool) (m : Fin n → Fin n) (hm : ∀ w, m (m w) = w)
    (hreal : Realizable f A C)
    (hno : ∀ w, m w ≠ w → (A w && A (m w)) = false) :
    let r := mixedRoute m A C
    let A' := fun w => A (r w)
    let C' := fun w => if !A w && !A (m w) then applyInv m C w else C (r w)
    countFin A' = countFin A ∧ Realizable (fun x => applyInv m (f x)) A' C' := by
  intro r A' C'
  have hr : ∀ w, r (r w) = w := mixedRoute_invol m hm A C
  refine ⟨countFin_comp_invol r hr A, ?_⟩
  intro y hy
  let y0 : Fin n → Bool := fun w => if A w then y (r w) else C w
  have hy0 : ∀ w, A w = false → y0 w = C w := fun w hw => by simp [y0, hw]
  obtain ⟨x, hx⟩ := hreal y0 hy0
  refine ⟨x, ?_⟩
  dsimp only
  rw [hx]
  funext w
  dsimp only [applyInv, y0]
  by_cases hfix : m w = w
  · have hrw : r w = w := by
      dsimp only [r, mixedRoute]; rw [hfix]; cases A w <;> simp
    cases haw : A w
    · have hA'w : A' w = false := by dsimp only [A']; rw [hrw, haw]
      have hyw := hy w hA'w
      dsimp only [C', applyInv] at hyw
      rw [hfix, haw] at hyw
      simp only [hfix, haw, Nat.le_refl, ↓reduceIte, Bool.and_self, Bool.not_false, Bool.and_true] at hyw ⊢
      exact hyw.symm
    · simp [hfix, haw, hrw]
  · cases haw : A w
    · cases ham : A (m w)
      · have hrw : r w = w := by dsimp only [r, mixedRoute]; simp [haw, ham]
        have hA'w : A' w = false := by dsimp only [A']; rw [hrw, haw]
        have hyw := hy w hA'w
        dsimp only [C', applyInv] at hyw
        simp only [haw, ham, Bool.not_false, Bool.and_true, ↓reduceIte] at hyw ⊢
        exact hyw.symm
      · have hne_val : w.val ≠ (m w).val := fun he => hfix (Fin.ext he.symm)
        cases hcw : C w
        · by_cases hlt : w.val ≤ (m w).val
          · have hrw : r w = w := by
              dsimp only [r, mixedRoute]
              have hnot : ¬ ((m w).val ≤ w.val) := by omega
              have hlt' : w.val < (m w).val := by omega
              simp [haw, ham, hcw, hnot, hlt']
            have hA'w : A' w = false := by dsimp only [A']; rw [hrw, haw]
            have hyw := hy w hA'w
            dsimp only [C'] at hyw
            simp only [haw, ham, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hrw, hcw] at hyw
            simp [hlt, haw, hcw, hyw]
          · have hrw : r w = m w := by
              dsimp only [r, mixedRoute]
              have hle : (m w).val ≤ w.val := by omega
              have hnot : ¬ (w.val < (m w).val) := by omega
              simp [haw, ham, hcw, hle, hnot]
            have hrm : r (m w) = w := by rw [← hrw, hr]
            simp [hlt, haw, ham, hcw, hrm]
        · by_cases hlt : w.val ≤ (m w).val
          · have hrw : r w = m w := by
              dsimp only [r, mixedRoute]
              have hnot : ¬ ((m w).val ≤ w.val) := by omega
              simp [haw, ham, hcw, hnot]
            have hrm : r (m w) = w := by rw [← hrw, hr]
            simp [hlt, haw, ham, hcw, hrm]
          · have hrw : r w = w := by
              dsimp only [r, mixedRoute]
              have hle : (m w).val ≤ w.val := by omega
              simp [haw, ham, hcw, hle]
            have hA'w : A' w = false := by dsimp only [A']; rw [hrw, haw]
            have hyw := hy w hA'w
            dsimp only [C'] at hyw
            simp only [haw, ham, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hrw, hcw] at hyw
            simp [hlt, haw, hcw, hyw]
    · have ham : A (m w) = false := by
        have h := hno w hfix
        rw [haw] at h
        cases hm' : A (m w)
        · rfl
        · simp [hm'] at h
      have hne_val : w.val ≠ (m w).val := fun he => hfix (Fin.ext he.symm)
      cases hcm : C (m w)
      · by_cases hlt : w.val ≤ (m w).val
        · have hrw : r w = m w := by
            dsimp only [r, mixedRoute]
            have hnot : ¬ ((m w).val < w.val) := by omega
            simp [haw, ham, hcm, hlt, hnot]
          have hA'w : A' w = false := by dsimp only [A']; rw [hrw, ham]
          have hyw := hy w hA'w
          dsimp only [C'] at hyw
          simp only [haw, ham, Bool.not_false, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrw, hcm] at hyw
          simp [hlt, ham, hcm, hyw]
        · have hrw : r w = w := by
            dsimp only [r, mixedRoute]
            have hlt' : (m w).val < w.val := by omega
            simp [haw, ham, hcm, hlt, hlt']
          simp [hlt, haw, ham, hcm, hrw]
      · by_cases hlt : w.val ≤ (m w).val
        · have hrw : r w = w := by
            dsimp only [r, mixedRoute]
            simp [haw, ham, hcm, hlt]
          simp [hlt, haw, ham, hcm, hrw]
        · have hrw : r w = m w := by
            dsimp only [r, mixedRoute]
            simp [haw, ham, hcm, hlt]
          have hA'w : A' w = false := by dsimp only [A']; rw [hrw, ham]
          have hyw := hy w hA'w
          dsimp only [C'] at hyw
          simp only [haw, ham, Bool.not_false, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hrw, hcm] at hyw
          simp [hlt, ham, hcm, hyw]

private theorem step_two_layers {n : Nat} (f : (Fin n → Bool) → (Fin n → Bool))
    (A C : Fin n → Bool) (m1 m2 : Fin n → Fin n)
    (hm1 : ∀ w, m1 (m1 w) = w) (hm2 : ∀ w, m2 (m2 w) = w)
    (hreal : Realizable f A C) :
    ∃ A' C', countFin A ≤ 2 * countFin A' ∧
      Realizable (fun x => applyInv m2 (applyInv m1 (f x))) A' C' := by
  let r1 := mixedRoute m1 A C
  have hr1 : ∀ w, r1 (r1 w) = w := mixedRoute_invol m1 hm1 A C
  let A1 : Fin n → Bool := fun w => A (r1 w)
  have hcntA1 : countFin A1 = countFin A := countFin_comp_invol r1 hr1 A
  let m1' : Fin n → Fin n := fun w => if A w && A (m1 w) then m1 w else w
  have hm1' : ∀ w, m1' (m1' w) = w := by
    intro w; dsimp only [m1']
    cases haw : A w <;> cases ham : A (m1 w) <;> simp [haw, ham, hm1]
  obtain ⟨I, hIsub, hIm1', hIm2, hIcnt⟩ :=
    two_involutions_indep m1' m2 hm1' hm2 (countFin A1) A1 (Nat.le_refl _)
  let Asub : Fin n → Bool := fun w => I (r1 w)
  let Csub : Fin n → Bool := fun w =>
    if A w = false then C w
    else if (A (m1 w) && (m1 w != w) && I (m1 w)) = true then
      decide ((m1 w).val ≤ w.val)
    else false
  have hreal_sub : Realizable f Asub Csub := by
    intro y hy
    apply hreal y
    intro w haw
    have hAsub_f : Asub w = false := by
      cases h : Asub w
      · rfl
      · have h1 := hIsub (r1 w) h
        dsimp only [A1] at h1
        rw [hr1, haw] at h1; cases h1
    have := hy w hAsub_f
    simpa [Csub, haw] using this
  have hno_m1 : ∀ w, m1 w ≠ w → (Asub w && Asub (m1 w)) = false := by
    intro w hne
    cases hw : Asub w
    · rfl
    · cases hmw : Asub (m1 w)
      · rfl
      · exfalso
        have hAw : A w = true := by
          have := hIsub (r1 w) hw; dsimp only [A1] at this; rwa [hr1] at this
        have hAm : A (m1 w) = true := by
          have := hIsub (r1 (m1 w)) hmw; dsimp only [A1] at this; rwa [hr1] at this
        have hr1w : r1 w = w := by dsimp only [r1, mixedRoute]; simp [hAw, hAm]
        have hr1m : r1 (m1 w) = m1 w := by dsimp only [r1, mixedRoute]; simp [hAw, hAm, hm1]
        have hIw : I w = true := by simpa [Asub, hr1w] using hw
        have hIm : I (m1 w) = true := by simpa [Asub, hr1m] using hmw
        have hm1'w : m1' w = m1 w := by dsimp only [m1']; simp [hAw, hAm]
        have hcontra := hIm1' w (by rw [hm1'w]; exact hne)
        rw [hm1'w, hIw, hIm] at hcontra
        cases hcontra
  have hstep1 := applyInv_no_active_pairs f Asub Csub m1 hm1 hreal_sub hno_m1
  have hA1s_eq_I : ∀ w, Asub (mixedRoute m1 Asub Csub w) = I w := by
    intro w
    have hcase : ∀ v, Asub v = true → mixedRoute m1 Asub Csub v = r1 v := by
      intro v hv
      have hAv : A v = true := by
        have := hIsub (r1 v) hv; dsimp only [A1] at this; rwa [hr1] at this
      by_cases hfix : m1 v = v
      · dsimp only [mixedRoute, r1]; rw [hfix]; simp [hv, hAv]
      · have hAsub_m : Asub (m1 v) = false := by
          have := hno_m1 v hfix; rw [hv] at this
          cases h' : Asub (m1 v)
          · rfl
          · simp [h'] at this
        cases hAm : A (m1 v)
        · have hCm : Csub (m1 v) = C (m1 v) := by simp [Csub, hAm]
          dsimp only [mixedRoute, r1]
          simp [hv, hAsub_m, hAv, hAm, hCm]
        · have hr1v : r1 v = v := by dsimp only [r1, mixedRoute]; simp [hAv, hAm]
          have hIv : I v = true := by simpa [Asub, hr1v] using hv
          have hCm : Csub (m1 v) = decide (v.val ≤ (m1 v).val) := by
            dsimp only [Csub]
            simp [hAm, hm1, hAv, hIv, Ne.symm hfix]
          rw [hr1v]
          dsimp only [mixedRoute]
          simp only [hv, hAsub_m, Bool.not_false, Bool.and_true, ↓reduceIte, hCm]
          by_cases hle : v.val ≤ (m1 v).val
          · simp [hle]
          · have hlt : (m1 v).val < v.val := by omega
            simp [hle, hlt]
    cases hIw : I w
    · cases hA1s : Asub (mixedRoute m1 Asub Csub w)
      · rfl
      · exfalso
        have h2 := hcase (mixedRoute m1 Asub Csub w) hA1s
        rw [mixedRoute_invol m1 hm1 Asub Csub w] at h2
        have hIw' : I (r1 (mixedRoute m1 Asub Csub w)) = true := hA1s
        rw [← h2] at hIw'
        rw [hIw] at hIw'; cases hIw'
    · have hAsub_rw : Asub (r1 w) = true := by dsimp only [Asub]; rwa [hr1]
      have hmr := hcase (r1 w) hAsub_rw
      rw [hr1] at hmr
      have hmr' := congrArg (mixedRoute m1 Asub Csub) hmr
      rw [mixedRoute_invol m1 hm1 Asub Csub (r1 w)] at hmr'
      rw [← hmr']
      exact hAsub_rw
  let C1s : Fin n → Bool :=
    fun w => if !Asub w && !Asub (m1 w) then applyInv m1 Csub w else Csub (mixedRoute m1 Asub Csub w)
  have hreal1 : Realizable (fun x => applyInv m1 (f x)) I C1s := by
    intro y hy
    apply hstep1.2 y
    intro w hw
    exact hy w (by rw [← hA1s_eq_I w]; exact hw)
  have hstep2 := applyInv_no_active_pairs (fun x => applyInv m1 (f x)) I C1s m2 hm2 hreal1 hIm2
  refine ⟨_, _, ?_, hstep2.2⟩
  omega

/-! ## 5. Main Lower Bound: `¬ SortNet.Statements.SN_rec_d17.Record 8` -/

theorem record : ¬ SortNet.Statements.SN_rec_d17.Record 8 := by
  rintro ⟨net, hd, hsort⟩
  obtain ⟨m, hm_inv, heval⟩ := decompose_layers net 8 hd
  have hreal0 : Realizable (fun x : Fin 17 → Bool => x) (fun _ => true) (fun _ => false) :=
    fun y _ => ⟨y, rfl⟩
  have hcnt0 : countFin (fun _ : Fin 17 => true) = 17 := countFin_true 17
  obtain ⟨A1, C1, hcnt1, hreal1⟩ := step_two_layers _ _ _ (m 0) (m 1) (hm_inv 0) (hm_inv 1) hreal0
  obtain ⟨A2, C2, hcnt2, hreal2⟩ := step_two_layers _ _ _ (m 2) (m 3) (hm_inv 2) (hm_inv 3) hreal1
  obtain ⟨A3, C3, hcnt3, hreal3⟩ := step_two_layers _ _ _ (m 4) (m 5) (hm_inv 4) (hm_inv 5) hreal2
  obtain ⟨A4, C4, hcnt4, hreal4⟩ := step_two_layers _ _ _ (m 6) (m 7) (hm_inv 6) (hm_inv 7) hreal3
  have hge2 : 2 ≤ countFin A4 := by omega
  obtain ⟨i, j, hij, hAi, hAj⟩ := exists_two_of_countFin_ge_two A4 hge2
  let y : Fin 17 → Bool := fun w => if w = i then true else if w = j then false else C4 w
  have hy_out : ∀ w, A4 w = false → y w = C4 w := by
    intro w hw
    have hni : w ≠ i := fun he => by subst he; rw [hAi] at hw; cases hw
    have hnj : w ≠ j := fun he => by subst he; rw [hAj] at hw; cases hw
    simp [y, hni, hnj]
  obtain ⟨x, hx⟩ := hreal4 y hy_out
  have hev_x : evalBool net x = y := by
    rw [heval x]
    simpa [List.range_succ] using hx
  have hs := hsort x i j (Nat.le_of_lt hij)
  rw [hev_x] at hs
  have hyi : y i = true := by simp [y]
  have hyj : y j = false := by
    have hne : j ≠ i := fun he => by have := congrArg Fin.val he; omega
    simp [y, hne]
  have hcontra := hs hyi
  rw [hyj] at hcontra
  cases hcontra

end SortNet.Claims.SN_rec_d17_not_s8
