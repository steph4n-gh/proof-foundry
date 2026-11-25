import Quantum.Core
import Quantum.Statements.QC_rec_n18_d4_w6

namespace Quantum.Claims.QC_rec_n18_d4_w6_not_s8

open Quantum

/-!
  Formal Lean 4 proof of `¬ Quantum.Statements.QC_rec_n18_d4_w6.Record 8`, certifying that
  every 18-qubit distance-4 binary CSS code `[[18, k, 4]]` satisfies `k ≤ 7` (matching the
  exact binary CSS linear programming upper bound).

  Proof outline:
  1. Given `IsCSSCode 18 k 4 6 hx hz lx lz` with `k ≥ 8`, construct the two binary linear
     subspaces `A = rowSpace(hx)` and `B = orth(hz)` as duplicate-free lists of `BitVec 18`.
     We have `A ⊆ B`, `0 ∈ A`, every `u ∈ Δ := B \ A` has `hammingWeight u ≥ 4` (X-distance ≥ 4),
     and the `2^8 = 256` logical-X cosets of `A` in `B` are pairwise disjoint, giving `256 * |A| ≤ |B|`.
  2. Prove the symbolic binary MacWilliams identity for any linear subspace `C ⊆ BitVec 18`:
       `∑_{u ∈ C} K_j(wt u) = |C| * |{S ∈ subsets 18 j : ∀ u ∈ C, charS S u = 1}|`.
     Setting `K_A(j) = ∑_{u ∈ A} K_j(wt u)` and `K_B(j) = ∑_{u ∈ B} K_j(wt u)`, define
       `E_j = |B| * K_A(j) - |A| * K_B(j) = |A| * |B| * (W_j(A^⊥) - W_j(B^⊥))`
       `D_j = |A| * K_B(j) = |A| * |B| * W_j(B^⊥)`.
     Since `B^⊥ ⊆ A^⊥` and Z-distance ≥ 4 implies `W_j(A^⊥) = W_j(B^⊥)` for `j ∈ {0, 1, 2, 3}`,
     we have `E_0 = E_1 = E_2 = E_3 = 0`, `E_j ≥ 0` for `j ≥ 4`, and `D_j ≥ 0` for all `j`.
  3. Contract with the exact integer dual certificate `(λ, μ)` of degree 14:
       `λ = (-20000, -5640, -2166, -451, 0, 15, 0, 0)`
       `μ = (0, 19359, 12988, 12643, 6576, 5173, 1701, 1190)`.
     On the dual side, `S := ∑ λ_j E_j + ∑ μ_j D_j ≥ 0`.
     On the primal side, `S = ∑_{u ∈ A} ((|B|-|A|) F(wt u) + |A| G(wt u)) + ∑_{u ∈ Δ} |A| (G(wt u) - F(wt u))`.
     Since `F(w) ≤ 0` for all `w ≤ 18`, `|B| - |A| ≥ 255 |A|`, `255 F(w) + G(w) ≤ 0` for `1 ≤ w ≤ 18`,
     `G(w) - F(w) ≤ 0` for `4 ≤ w ≤ 18`, and `255 F(0) + G(0) = -16824 < 0`,
     we obtain `0 ≤ S ≤ -16824 * |A| < 0`, contradiction.
-/

/-! ## 1. BitVec 18 Algebraic & Hamming Weight Helpers -/

private theorem bv_xor_comm (a b : BitVec 18) : a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bv_xor_assoc (a b c : BitVec 18) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bv_xor_self (a : BitVec 18) : a ^^^ a = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem bv_xor_zero (a : BitVec 18) : a ^^^ 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem bv_zero_xor (a : BitVec 18) : 0 ^^^ a = a := by
  rw [bv_xor_comm, bv_xor_zero]

private theorem bv_xor_cancel (a b : BitVec 18) : (a ^^^ b) ^^^ b = a := by
  rw [bv_xor_assoc, bv_xor_self, bv_xor_zero]

private def countBits (k : Nat) (f : Nat → Bool) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => countBits k' f + (if f k' then 1 else 0)

private theorem countBits_congr (k : Nat) (f g : Nat → Bool)
    (hfg : ∀ i, i < k → f i = g i) : countBits k f = countBits k g := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [countBits, hfg k' (Nat.lt_succ_self k'),
      ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]

private theorem popCountAux_eq_countBits_go :
    ∀ (k x : Nat), popCountAux k x = countBits k (fun i => Nat.testBit x i)
  | 0, _ => rfl
  | k + 1, x => by
    have hshift : ∀ (m x : Nat),
        countBits (m + 1) (fun i => Nat.testBit x i) =
        (if Nat.testBit x 0 then 1 else 0) + countBits m (fun i => Nat.testBit (x / 2) i) := by
      intro m
      induction m with
      | zero => intro y; simp [countBits]
      | succ m' ih =>
        intro y
        change countBits (m' + 1) (fun i => Nat.testBit y i) + (if Nat.testBit y (m' + 1) then 1 else 0) =
          (if Nat.testBit y 0 then 1 else 0) +
          (countBits m' (fun i => Nat.testBit (y / 2) i) + (if Nat.testBit (y / 2) m' then 1 else 0))
        rw [ih y, Nat.testBit_succ]
        omega
    rw [hshift k x, popCountAux, popCountAux_eq_countBits_go k (x / 2), Nat.testBit_zero]
    cases h : decide (x % 2 = 1)
    · have hm : x % 2 = 0 := by
        have hlt : x % 2 < 2 := Nat.mod_lt x (by decide)
        have hne : x % 2 ≠ 1 := by simpa using h
        omega
      simp [hm]
    · have hm : x % 2 = 1 := by simpa using h
      simp [hm]

private theorem hammingWeight_eq_countBits {n : Nat} (u : BitVec n) :
    hammingWeight u = countBits n (fun i => u.getLsbD i) := by
  unfold hammingWeight
  rw [popCountAux_eq_countBits_go]
  apply countBits_congr
  intro i _
  rfl

private theorem countBits_le : ∀ (k : Nat) (f : Nat → Bool), countBits k f ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, f => by
    simp only [countBits]
    have ih := countBits_le k f
    by_cases h : f k = true <;> simp [h] <;> omega

private theorem hammingWeight_le (u : BitVec 18) : hammingWeight u ≤ 18 := by
  rw [hammingWeight_eq_countBits]
  exact countBits_le 18 _

private theorem hammingWeight_zero : hammingWeight (0 : BitVec 18) = 0 := by decide +kernel

private theorem countBits_eq_zero_imp {k : Nat} {f : Nat → Bool}
    (h : countBits k f = 0) : ∀ i, i < k → f i = false := by
  induction k with
  | zero => intro i hi; omega
  | succ k' ih =>
    simp only [countBits] at h
    intro i hi
    cases hfk : f k'
    · simp only [hfk, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact ih h i hlt
      · exact hfk
    · simp only [hfk, ↓reduceIte] at h
      omega

private theorem hammingWeight_pos_of_ne_zero {u : BitVec 18} (hu : u ≠ 0) :
    0 < hammingWeight u := by
  cases Nat.eq_zero_or_pos (hammingWeight u) with
  | inl h0 =>
    exfalso
    apply hu
    rw [hammingWeight_eq_countBits] at h0
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h0' := countBits_eq_zero_imp h0 i hi
    simp [h0']
  | inr hp => exact hp

private theorem countBits_xor (k : Nat) (f g : Nat → Bool) :
    countBits k (fun i => xor (f i) (g i)) + 2 * countBits k (fun i => f i && g i) =
    countBits k f + countBits k g := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [countBits]
    by_cases hf : f k' = true <;> by_cases hg : g k' = true <;> simp [hf, hg] <;> omega

private theorem commutes_comm (u v : BitVec 18) : commutes u v = commutes v u := by
  unfold commutes
  have h : u &&& v = v &&& u := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and]
    cases u.getLsbD i <;> cases v.getLsbD i <;> rfl
  rw [h]

private theorem commutes_zero_left (v : BitVec 18) : commutes 0 v = true := by
  unfold commutes
  have h : (0 : BitVec 18) &&& v = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp
  rw [h, hammingWeight_zero]
  rfl

private theorem commutes_xor_left (a b v : BitVec 18) :
    commutes (a ^^^ b) v = (commutes a v == commutes b v) := by
  unfold commutes
  rw [hammingWeight_eq_countBits, hammingWeight_eq_countBits, hammingWeight_eq_countBits]
  have h1 : countBits 18 (fun i => ((a ^^^ b) &&& v).getLsbD i) =
      countBits 18 (fun i => xor ((a &&& v).getLsbD i) ((b &&& v).getLsbD i)) := by
    apply countBits_congr
    intro i _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases v.getLsbD i <;> rfl
  rw [h1]
  have hx := countBits_xor 18 (fun i => (a &&& v).getLsbD i) (fun i => (b &&& v).getLsbD i)
  have hmod : (countBits 18 (fun i => xor ((a &&& v).getLsbD i) ((b &&& v).getLsbD i))) % 2 =
      (countBits 18 (fun i => (a &&& v).getLsbD i) + countBits 18 (fun i => (b &&& v).getLsbD i)) % 2 := by
    omega
  rw [hmod]
  have ha := Nat.mod_lt (countBits 18 (fun i => (a &&& v).getLsbD i)) (by decide : 0 < 2)
  have hb := Nat.mod_lt (countBits 18 (fun i => (b &&& v).getLsbD i)) (by decide : 0 < 2)
  have hparity : ∀ (x y : Nat), ((x + y) % 2 == 0) = ((x % 2 == 0) == (y % 2 == 0)) := by
    intro x y
    have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hx2 with hx0 | hx1 <;> rcases hy2 with hy0 | hy1
    · have hxy : (x + y) % 2 = 0 := by omega
      simp [hx0, hy0, hxy]
    · have hxy : (x + y) % 2 = 1 := by omega
      simp [hx0, hy1, hxy]
    · have hxy : (x + y) % 2 = 1 := by omega
      simp [hx1, hy0, hxy]
    · have hxy : (x + y) % 2 = 0 := by omega
      simp [hx1, hy1, hxy]
  exact hparity _ _

private theorem commutes_xor_right (u a b : BitVec 18) :
    commutes u (a ^^^ b) = (commutes u a == commutes u b) := by
  rw [commutes_comm u (a ^^^ b), commutes_xor_left, commutes_comm a u, commutes_comm b u]

private theorem inRowSpace_of_mem {gens : List (BitVec 18)} {x : BitVec 18} (hx : x ∈ gens) :
    InRowSpace gens x := by
  induction gens with
  | nil => exact absurd hx List.not_mem_nil
  | cons g gs ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · refine ⟨true :: List.replicate gs.length false, by simp, ?_⟩
      simp [xorSubset, xorSubset_false]
    · rcases ih hx' with ⟨m, hm, rfl⟩
      refine ⟨false :: m, by simp [hm], ?_⟩
      simp [xorSubset]

private theorem commutes_of_inRowSpace {gens : List (BitVec 18)} {u v : BitVec 18}
    (hgens : ∀ g ∈ gens, commutes u g = true) (hv : InRowSpace gens v) :
    commutes u v = true := by
  rcases hv with ⟨m, hm, rfl⟩
  induction gens generalizing m with
  | nil =>
    cases m with
    | nil => rw [commutes_comm]; exact commutes_zero_left u
    | cons _ _ => simp at hm
  | cons g gs ih =>
    cases m with
    | nil => simp at hm
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hm
      simp only [xorSubset]
      rw [commutes_xor_right]
      have hrest := ih (fun x hx => hgens x (List.mem_cons_of_mem g hx)) bs hm
      have hfirst : commutes u (if b then g else 0) = true := by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [commutes_comm]; exact commutes_zero_left u
        · simp only [↓reduceIte]; exact hgens g List.mem_cons_self
      rw [hfirst, hrest]; rfl

/-! ## 2. List Nodup, Permutation, and Sum Helpers -/

private def sumInt {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldl (fun acc x => acc + f x) 0

private theorem sumInt_nil {α : Type} (f : α → Int) : sumInt [] f = 0 := rfl

private theorem sumInt_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    sumInt (x :: xs) f = f x + sumInt xs f := by
  unfold sumInt
  have haux : ∀ (l : List α) (a : Int),
      l.foldl (fun acc y => acc + f y) a = a + l.foldl (fun acc y => acc + f y) 0 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons y ys ih =>
      intro a
      simp only [List.foldl_cons, Int.zero_add]
      rw [ih (a + f y), ih (f y), Int.add_assoc]
  simp only [List.foldl_cons, Int.zero_add]
  exact haux xs (f x)

private theorem sumInt_append {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumInt (l1 ++ l2) f = sumInt l1 f + sumInt l2 f := by
  induction l1 with
  | nil => simp [sumInt_nil]
  | cons x xs ih => simp only [List.cons_append, sumInt_cons, ih, Int.add_assoc]

private theorem sumInt_map {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    sumInt (l.map g) f = sumInt l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, sumInt_cons, ih]

private theorem sumInt_congr {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, f x = g x) : sumInt l f = sumInt l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [sumInt_cons, sumInt_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem sumInt_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    sumInt l (fun x => c * f x) = c * sumInt l f := by
  induction l with
  | nil => simp [sumInt_nil]
  | cons x xs ih => simp only [sumInt_cons, ih, Int.mul_add]

private theorem sumInt_add {α : Type} (l : List α) (f g : α → Int) :
    sumInt l (fun x => f x + g x) = sumInt l f + sumInt l g := by
  induction l with
  | nil => simp [sumInt_nil]
  | cons x xs ih => simp only [sumInt_cons, ih]; omega

private theorem sumInt_swap {α β : Type} (la : List α) (lb : List β) (f : α → β → Int) :
    sumInt la (fun a => sumInt lb (fun b => f a b)) =
    sumInt lb (fun b => sumInt la (fun a => f a b)) := by
  induction la with
  | nil =>
    rw [sumInt_nil]
    induction lb with
    | nil => rfl
    | cons b bs ihb => rw [sumInt_cons, sumInt_nil, ← ihb, Int.zero_add]
  | cons a as iha =>
    rw [sumInt_cons, iha, ← sumInt_add]
    exact sumInt_congr lb _ _ (fun b _ => (sumInt_cons a as (fun a => f a b)).symm)

private theorem sumInt_le {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, f x ≤ g x) : sumInt l f ≤ sumInt l g := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons x xs ih =>
    simp only [sumInt_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private theorem sumInt_const {α : Type} (l : List α) (c : Int) :
    sumInt l (fun _ => c) = (l.length : Int) * c := by
  induction l with
  | nil => simp [sumInt_nil]
  | cons x xs ih =>
    rw [sumInt_cons, ih, List.length_cons, Int.natCast_add, Int.add_mul]
    simp [Int.add_comm]

private theorem sumInt_filter_split {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    sumInt l f = sumInt (l.filter p) f + sumInt (l.filter (fun x => !(p x))) f := by
  induction l with
  | nil => simp [sumInt_nil]
  | cons x xs ih =>
    simp only [List.filter_cons, sumInt_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, sumInt_cons]
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, sumInt_cons]
      omega

private theorem nodup_filter {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have ⟨hx, hxs⟩ := List.nodup_cons.1 h
    simp only [List.filter_cons]
    cases p x
    · exact nodup_filter hxs
    · exact List.nodup_cons.2 ⟨fun hm => hx (List.mem_filter.1 hm).1, nodup_filter hxs⟩

private theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α}
    (hnd : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have ⟨hx, hxs⟩ := List.nodup_cons.1 hnd
    apply List.nodup_cons.2
    refine ⟨?_, ih hxs (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hm
    rcases List.mem_map.1 hm with ⟨y, hy, hyx⟩
    have hxy := hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self hyx
    subst hxy
    exact hx hy

private theorem nodup_append {α : Type} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hdisj : ∀ x ∈ l1, x ∉ l2) : (l1 ++ l2).Nodup := by
  induction l1 with
  | nil => simpa using h2
  | cons x xs ih =>
    have ⟨hx, hxs⟩ := List.nodup_cons.1 h1
    apply List.nodup_cons.2
    refine ⟨?_, ih hxs (fun y hy => hdisj y (List.mem_cons_of_mem x hy))⟩
    intro hm
    rcases List.mem_append.1 hm with hm1 | hm2
    · exact hx hm1
    · exact hdisj x List.mem_cons_self hm2

private theorem mem_split {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l → ∃ p q : List α, l = p ++ x :: q
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨[], ys, rfl⟩
    · rcases mem_split h' with ⟨p, q, rfl⟩
      exact ⟨y :: p, q, rfl⟩

private theorem nodup_append_cons_remove {α : Type} {p q : List α} {x : α}
    (h : (p ++ x :: q).Nodup) : (p ++ q).Nodup ∧ x ∉ p ++ q := by
  induction p with
  | nil =>
    have ⟨hx, hq⟩ := List.nodup_cons.1 h
    exact ⟨hq, hx⟩
  | cons y ys ih =>
    have ⟨hy, hrest⟩ := List.nodup_cons.1 h
    have ⟨hnd', hnx⟩ := ih hrest
    refine ⟨List.nodup_cons.2 ⟨?_, hnd'⟩, ?_⟩
    · intro hm
      apply hy
      rcases List.mem_append.1 hm with h1 | h2
      · exact List.mem_append.2 (Or.inl h1)
      · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem x h2))
    · intro hm
      rcases List.mem_cons.1 hm with hxy | hm'
      · subst hxy
        exact hy (List.mem_append.2 (Or.inr List.mem_cons_self))
      · exact hnx hm'

private theorem nodup_length_le_of_subset {α : Type} :
    ∀ (l1 l2 : List α), l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l2, hnd, hsub => by
    have ⟨hx, hxs⟩ := List.nodup_cons.1 hnd
    have hx2 : x ∈ l2 := hsub x List.mem_cons_self
    rcases mem_split hx2 with ⟨p, q, rfl⟩
    have hsub' : ∀ y ∈ xs, y ∈ p ++ q := by
      intro y hy
      have hy2 : y ∈ p ++ x :: q := hsub y (List.mem_cons_of_mem x hy)
      rcases List.mem_append.1 hy2 with hp | hxq
      · exact List.mem_append.2 (Or.inl hp)
      · rcases List.mem_cons.1 hxq with rfl | hq
        · exact absurd hy hx
        · exact List.mem_append.2 (Or.inr hq)
    have ih := nodup_length_le_of_subset xs (p ++ q) hxs hsub'
    simp only [List.length_cons, List.length_append] at ih ⊢
    omega

private theorem sumInt_perm_eq {α : Type} (f : α → Int) :
    ∀ (l1 l2 : List α), l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) →
      sumInt l1 f = sumInt l2 f
  | [], l2, _, _, hiff => by
    cases l2 with
    | nil => rfl
    | cons y _ =>
      have hy := (hiff y).2 List.mem_cons_self
      exact absurd hy List.not_mem_nil
  | x :: xs, l2, h1, h2, hiff => by
    have ⟨hx, hxs⟩ := List.nodup_cons.1 h1
    have hx2 : x ∈ l2 := (hiff x).1 List.mem_cons_self
    rcases mem_split hx2 with ⟨p, q, rfl⟩
    have ⟨hnd', hnx⟩ := nodup_append_cons_remove h2
    have hiff' : ∀ y, y ∈ xs ↔ y ∈ p ++ q := by
      intro y
      constructor
      · intro hy
        have hne : y ≠ x := fun h => hx (h ▸ hy)
        have hy2 := (hiff y).1 (List.mem_cons_of_mem x hy)
        rcases List.mem_append.1 hy2 with hp | hxq
        · exact List.mem_append.2 (Or.inl hp)
        · rcases List.mem_cons.1 hxq with rfl | hq
          · exact absurd rfl hne
          · exact List.mem_append.2 (Or.inr hq)
      · intro hy
        have hne : y ≠ x := fun h => hnx (h ▸ hy)
        have hy2 : y ∈ p ++ x :: q := by
          rcases List.mem_append.1 hy with hp | hq
          · exact List.mem_append.2 (Or.inl hp)
          · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem x hq))
        rcases List.mem_cons.1 ((hiff y).2 hy2) with rfl | hys
        · exact absurd rfl hne
        · exact hys
    rw [sumInt_cons, sumInt_append, sumInt_cons, sumInt_perm_eq f xs (p ++ q) hxs hnd' hiff', sumInt_append]
    omega

private theorem sumInt_extract_mem {α : Type} {l : List α} {x : α} (hnd : l.Nodup) (hx : x ∈ l)
    (f : α → Int) (hrest : ∀ y ∈ l, y ≠ x → f y ≤ 0) : sumInt l f ≤ f x := by
  rcases mem_split hx with ⟨p, q, rfl⟩
  have ⟨_, hnx⟩ := nodup_append_cons_remove hnd
  rw [sumInt_append, sumInt_cons]
  have hp : sumInt p f ≤ 0 := by
    have h0 : sumInt p (fun _ => 0) = 0 := by rw [sumInt_const]; simp
    rw [← h0]
    apply sumInt_le
    intro y hy
    have hne : y ≠ x := fun h => hnx (List.mem_append.2 (Or.inl (h ▸ hy)))
    exact hrest y (List.mem_append.2 (Or.inl hy)) hne
  have hq : sumInt q f ≤ 0 := by
    have h0 : sumInt q (fun _ => 0) = 0 := by rw [sumInt_const]; simp
    rw [← h0]
    apply sumInt_le
    intro y hy
    have hne : y ≠ x := fun h => hnx (List.mem_append.2 (Or.inr (h ▸ hy)))
    exact hrest y (List.mem_append.2 (Or.inr (List.mem_cons_of_mem x hy))) hne
  omega

private theorem length_filter_le_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.filter_cons]
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hp : p x
    · cases q x <;> simp <;> omega
    · have hq : q x = true := h x List.mem_cons_self hp
      simp [hq]; omega

private theorem filter_congr_mem {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## 3. Linear Subspaces `A = rowSpace(hx)` and `B = orth(hz)` and Coset Count -/

private def allBV18 : List (BitVec 18) :=
  (List.range 262144).map (BitVec.ofNat 18)

private theorem allBV18_nodup : allBV18.Nodup := by
  unfold allBV18
  apply nodup_map_of_inj List.nodup_range
  intro a ha b hb heq
  have ha' : a < 262144 := List.mem_range.1 ha
  have hb' : b < 262144 := List.mem_range.1 hb
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hnat
  exact hnat

private theorem allBV18_mem (u : BitVec 18) : u ∈ allBV18 := by
  unfold allBV18
  apply List.mem_map.2
  refine ⟨u.toNat, List.mem_range.2 u.isLt, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt u.isLt

private def rowSpaceStep (g : BitVec 18) (l : List (BitVec 18)) : List (BitVec 18) :=
  if l.contains g then l else l ++ l.map (· ^^^ g)

private def rowSpaceList : List (BitVec 18) → List (BitVec 18)
  | [] => [0]
  | g :: gs => rowSpaceStep g (rowSpaceList gs)

private theorem rowSpaceList_props (gens : List (BitVec 18)) :
    (rowSpaceList gens).Nodup ∧
    (0 : BitVec 18) ∈ rowSpaceList gens ∧
    (∀ a ∈ rowSpaceList gens, ∀ b ∈ rowSpaceList gens, (a ^^^ b) ∈ rowSpaceList gens) ∧
    (∀ v : BitVec 18, v ∈ rowSpaceList gens ↔ InRowSpace gens v) := by
  induction gens with
  | nil =>
    refine ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, List.mem_cons_self, ?_, ?_⟩
    · intro a ha b hb
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · exact List.mem_cons_self
        · exact absurd hb' List.not_mem_nil
      · exact absurd ha' List.not_mem_nil
    · intro v
      constructor
      · intro hv
        rcases List.mem_cons.1 hv with rfl | hv'
        · exact inRowSpace_zero []
        · exact absurd hv' List.not_mem_nil
      · intro ⟨m, hm, hv⟩
        cases m with
        | nil => rw [← hv]; exact List.mem_cons_self
        | cons _ _ => simp at hm
  | cons g gs ih =>
    rcases ih with ⟨hnd, h0, hxor, hiff⟩
    simp only [rowSpaceList, rowSpaceStep]
    by_cases hg : (rowSpaceList gs).contains g = true
    · simp only [hg, ↓reduceIte]
      have hgmem : g ∈ rowSpaceList gs := List.contains_iff_mem.1 hg
      refine ⟨hnd, h0, hxor, ?_⟩
      intro v
      constructor
      · intro hv
        rcases (hiff v).1 hv with ⟨m, hm, rfl⟩
        exact ⟨false :: m, by simp [hm], by simp [xorSubset]⟩
      · intro ⟨m, hm, hv⟩
        cases m with
        | nil => simp at hm
        | cons b bs =>
          simp only [List.length_cons, Nat.succ.injEq] at hm
          simp only [xorSubset] at hv
          rw [← hv]
          have hbs : xorSubset gs bs ∈ rowSpaceList gs := (hiff _).2 ⟨bs, hm, rfl⟩
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, bv_zero_xor]; exact hbs
          · simp only [↓reduceIte]; exact hxor g hgmem _ hbs
    · have hgf : (rowSpaceList gs).contains g = false := by cases h : (rowSpaceList gs).contains g <;> simp_all
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      have hgnot : g ∉ rowSpaceList gs := fun hm => by
        have := List.contains_iff_mem.2 hm
        rw [this] at hgf; cases hgf
      have hnd_map : ((rowSpaceList gs).map (· ^^^ g)).Nodup := by
        apply nodup_map_of_inj hnd
        intro a _ b _ heq
        have := congrArg (· ^^^ g) heq
        simpa only [bv_xor_cancel] using this
      have hdisj : ∀ x ∈ rowSpaceList gs, x ∉ (rowSpaceList gs).map (· ^^^ g) := by
        intro x hx hm
        rcases List.mem_map.1 hm with ⟨y, hy, hyx⟩
        have hg_eq : g = y ^^^ x := by
          rw [← hyx, bv_xor_comm y (y ^^^ g), bv_xor_comm y g, bv_xor_cancel]
        rw [hg_eq] at hgnot
        exact hgnot (hxor y hy x hx)
      have hiff_new : ∀ v : BitVec 18,
          v ∈ rowSpaceList gs ++ (rowSpaceList gs).map (· ^^^ g) ↔ InRowSpace (g :: gs) v := by
        intro v
        constructor
        · intro hv
          rcases List.mem_append.1 hv with h1 | h2
          · rcases (hiff v).1 h1 with ⟨m, hm, rfl⟩
            exact ⟨false :: m, by simp [hm], by simp [xorSubset]⟩
          · rcases List.mem_map.1 h2 with ⟨y, hy, rfl⟩
            rcases (hiff y).1 hy with ⟨m, hm, rfl⟩
            exact ⟨true :: m, by simp [hm], by simp [xorSubset, bv_xor_comm]⟩
        · intro ⟨m, hm, hv⟩
          cases m with
          | nil => simp at hm
          | cons b bs =>
            simp only [List.length_cons, Nat.succ.injEq] at hm
            simp only [xorSubset] at hv
            rw [← hv]
            have hbs : xorSubset gs bs ∈ rowSpaceList gs := (hiff _).2 ⟨bs, hm, rfl⟩
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, bv_zero_xor]
              exact List.mem_append.2 (Or.inl hbs)
            · simp only [↓reduceIte]
              apply List.mem_append.2
              right
              apply List.mem_map.2
              exact ⟨xorSubset gs bs, hbs, bv_xor_comm _ _⟩
      refine ⟨nodup_append hnd hnd_map hdisj, List.mem_append.2 (Or.inl h0), ?_, hiff_new⟩
      intro a ha b hb
      exact (hiff_new _).2 (inRowSpace_xor ((hiff_new a).1 ha) ((hiff_new b).1 hb))

private def orthList (gens : List (BitVec 18)) : List (BitVec 18) :=
  allBV18.filter (fun u => gens.all (fun z => commutes u z))

private theorem orthList_nodup (gens : List (BitVec 18)) : (orthList gens).Nodup :=
  nodup_filter allBV18_nodup

private theorem mem_orthList_iff (gens : List (BitVec 18)) (u : BitVec 18) :
    u ∈ orthList gens ↔ ∀ z ∈ gens, commutes u z = true := by
  unfold orthList
  rw [List.mem_filter]
  constructor
  · intro ⟨_, hall⟩
    exact List.all_eq_true.1 hall
  · intro h
    exact ⟨allBV18_mem u, List.all_eq_true.2 h⟩

private theorem orthList_zero (gens : List (BitVec 18)) : (0 : BitVec 18) ∈ orthList gens :=
  (mem_orthList_iff gens 0).2 (fun z _ => commutes_zero_left z)

private theorem orthList_xor (gens : List (BitVec 18)) {a b : BitVec 18}
    (ha : a ∈ orthList gens) (hb : b ∈ orthList gens) : (a ^^^ b) ∈ orthList gens := by
  rw [mem_orthList_iff] at ha hb ⊢
  intro z hz
  rw [commutes_xor_left, ha z hz, hb z hz]
  rfl

private def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).map (false :: ·) ++ (allMasks n).map (true :: ·)

private theorem allMasks_length : ∀ n, (allMasks n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [allMasks, List.length_append, List.length_map, allMasks_length n, Nat.pow_succ]
    omega

private theorem allMasks_mem_length : ∀ n m, m ∈ allMasks n → m.length = n
  | 0, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm'
    · rfl
    · exact absurd hm' List.not_mem_nil
  | n + 1, m, hm => by
    rcases List.mem_append.1 hm with h1 | h2
    · rcases List.mem_map.1 h1 with ⟨m', hm', rfl⟩
      simp [allMasks_mem_length n m' hm']
    · rcases List.mem_map.1 h2 with ⟨m', hm', rfl⟩
      simp [allMasks_mem_length n m' hm']

private theorem allMasks_nodup : ∀ n, (allMasks n).Nodup
  | 0 => List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => by
    have ih := allMasks_nodup n
    apply nodup_append
    · exact nodup_map_of_inj ih (fun a _ b _ h => List.cons.inj h |>.2)
    · exact nodup_map_of_inj ih (fun a _ b _ h => List.cons.inj h |>.2)
    · intro x hx hm
      rcases List.mem_map.1 hx with ⟨a, _, rfl⟩
      rcases List.mem_map.1 hm with ⟨b, _, h⟩
      cases h

private theorem list_eq_of_getD_eq :
    ∀ (m1 m2 : List Bool), m1.length = m2.length →
      (∀ j, j < m1.length → m1.getD j false = m2.getD j false) → m1 = m2
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hlen, hget => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    have h0 : a = b := hget 0 (Nat.zero_lt_succ _)
    subst h0
    congr 1
    apply list_eq_of_getD_eq as bs hlen
    intro j hj
    exact hget (j + 1) (Nat.succ_lt_succ hj)
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

private theorem commutes_xorSubset_all_true (L : List (BitVec 18)) (m : List Bool) (z : BitVec 18)
    (hlen : m.length = L.length)
    (hcomm : ∀ i, i < L.length → commutes (L.getD i 0) z = true) :
    commutes (xorSubset L m) z = true := by
  induction L generalizing m with
  | nil =>
    cases m with
    | nil => exact commutes_zero_left z
    | cons _ _ => simp at hlen
  | cons g gs ih =>
    cases m with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [xorSubset]
      rw [commutes_xor_left]
      have h1 : commutes (if b then g else 0) z = true := by
        cases b
        · exact commutes_zero_left z
        · exact hcomm 0 (Nat.zero_lt_succ _)
      have h2 := ih bs hlen (fun i hi => hcomm (i + 1) (Nat.succ_lt_succ hi))
      rw [h1, h2]; rfl

private theorem commutes_xorSubset_symp (L : List (BitVec 18)) (m : List Bool) (z : BitVec 18) (j : Nat)
    (hlen : m.length = L.length) (hj : j < L.length)
    (hcomm : ∀ i, i < L.length → commutes (L.getD i 0) z = decide (i ≠ j)) :
    commutes (xorSubset L m) z = !(m.getD j false) := by
  induction L generalizing m j with
  | nil => simp at hj
  | cons g gs ih =>
    cases m with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      cases j with
      | zero =>
        simp only [xorSubset, List.getD_cons_zero]
        rw [commutes_xor_left]
        have hg : commutes g z = false := by
          have := hcomm 0 (Nat.zero_lt_succ _)
          simpa using this
        have hrest : commutes (xorSubset gs bs) z = true :=
          commutes_xorSubset_all_true gs bs z hlen (fun i hi => by
            have := hcomm (i + 1) (Nat.succ_lt_succ hi)
            simpa using this)
        rw [hrest]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          rw [commutes_zero_left]
          rfl
        · simp [hg]
      | succ j' =>
        simp only [xorSubset, List.getD_cons_succ]
        rw [commutes_xor_left]
        have hg : commutes g z = true := by
          have := hcomm 0 (Nat.zero_lt_succ _)
          simpa using this
        have hfirst : commutes (if b then g else 0) z = true := by
          cases b
          · exact commutes_zero_left z
          · exact hg
        have hrest := ih bs j' hlen (by simp at hj; omega) (fun i hi => by
          have := hcomm (i + 1) (Nat.succ_lt_succ hi)
          have hne : decide (i + 1 ≠ j' + 1) = decide (i ≠ j') := by
            by_cases h : i = j' <;> simp [h]
          rwa [hne] at this)
        rw [hfirst, hrest]
        cases bs.getD j' false <;> rfl

private theorem list_getD_take {α : Type} (l : List α) (n i : Nat) (d : α) (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  induction l generalizing n i with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases i with
      | zero => simp
      | succ i' =>
        simp only [List.take_succ_cons, List.getD_cons_succ]
        exact ih n' i' (by omega)

private theorem list_getD_mem {α : Type} (l : List α) (i : Nat) (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem x (ih i' (by simp at hi; omega))

private theorem flatMap_length_const {α β : Type} (l : List α) (f : α → List β) (c : Nat)
    (hc : ∀ x ∈ l, (f x).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hc x List.mem_cons_self, ih (fun y hy => hc y (List.mem_cons_of_mem x hy)), Nat.succ_mul]
    omega

private theorem nodup_flatMap_of_inj {α β : Type} (la : List α) (lb : List β) (f : α → β → BitVec 18)
    (ha : la.Nodup) (hb : lb.Nodup)
    (hinj : ∀ a1 ∈ la, ∀ b1 ∈ lb, ∀ a2 ∈ la, ∀ b2 ∈ lb, f a1 b1 = f a2 b2 → a1 = a2 ∧ b1 = b2) :
    (la.flatMap (fun a => lb.map (fun b => f a b))).Nodup := by
  induction la with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have ⟨hx, hxs⟩ := List.nodup_cons.1 ha
    simp only [List.flatMap_cons]
    apply nodup_append
    · apply nodup_map_of_inj hb
      intro b1 hb1 b2 hb2 heq
      exact (hinj x List.mem_cons_self b1 hb1 x List.mem_cons_self b2 hb2 heq).2
    · exact ih hxs (fun a1 ha1 b1 hb1 a2 ha2 b2 hb2 =>
        hinj a1 (List.mem_cons_of_mem x ha1) b1 hb1 a2 (List.mem_cons_of_mem x ha2) b2 hb2)
    · intro v hv hm
      rcases List.mem_map.1 hv with ⟨b1, hb1, rfl⟩
      rcases List.mem_flatMap.1 hm with ⟨a2, ha2, hm2⟩
      rcases List.mem_map.1 hm2 with ⟨b2, hb2, heq⟩
      have hxa := (hinj x List.mem_cons_self b1 hb1 a2 (List.mem_cons_of_mem x ha2) b2 hb2 heq.symm).1
      subst hxa
      exact hx ha2

/-! ## 4. Symbolic Binary MacWilliams Identity via Subsets & Characters -/

private def signBool (b : Bool) : Int := if b then -1 else 1

private theorem signBool_xor (a b : Bool) : signBool (xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

private def subsets : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 =>
    subsets n (k + 1) ++ (subsets n k).map (fun s => n :: s)

private def charS (S : List Nat) (u : BitVec 18) : Int :=
  S.foldl (fun acc i => acc * signBool (u.getLsbD i)) 1

private theorem charS_cons (n : Nat) (S : List Nat) (u : BitVec 18) :
    charS (n :: S) u = signBool (u.getLsbD n) * charS S u := by
  unfold charS
  have haux : ∀ (l : List Nat) (a : Int),
      l.foldl (fun acc i => acc * signBool (u.getLsbD i)) a =
      a * l.foldl (fun acc i => acc * signBool (u.getLsbD i)) 1 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x xs ih =>
      intro a
      simp only [List.foldl_cons, Int.one_mul]
      rw [ih (a * signBool (u.getLsbD x)), ih (signBool (u.getLsbD x)), Int.mul_assoc]
  simp only [List.foldl_cons, Int.one_mul]
  exact haux S (signBool (u.getLsbD n))

private theorem charS_xor (S : List Nat) (u v : BitVec 18) :
    charS S (u ^^^ v) = charS S u * charS S v := by
  induction S with
  | nil => rfl
  | cons i rest ih =>
    rw [charS_cons, charS_cons, charS_cons, ih]
    have hi : (u ^^^ v).getLsbD i = xor (u.getLsbD i) (v.getLsbD i) := by
      simp [BitVec.getLsbD_xor]
    rw [hi, signBool_xor]
    have hmul : ∀ a b c d : Int, (a * b) * (c * d) = (a * c) * (b * d) := by
      intro a b c d
      rw [Int.mul_assoc, ← Int.mul_assoc b c d, Int.mul_comm b c, Int.mul_assoc c b d, ← Int.mul_assoc]
    exact hmul _ _ _ _

private theorem charS_pm1 (S : List Nat) (u : BitVec 18) :
    charS S u = 1 ∨ charS S u = -1 := by
  induction S with
  | nil => left; rfl
  | cons i rest ih =>
    rw [charS_cons]
    rcases ih with h | h <;> rw [h] <;> cases u.getLsbD i <;> simp [signBool]

private def Kraw : Nat → Nat → Nat → Int
  | _, 0, _ => 1
  | 0, _ + 1, _ => 0
  | n + 1, k + 1, 0 => Kraw n (k + 1) 0 + Kraw n k 0
  | n + 1, k + 1, w + 1 => Kraw n (k + 1) w - Kraw n k w

private theorem Kraw_add_zero : ∀ (n k w : Nat), w ≤ n →
    Kraw (n + 1) (k + 1) w = Kraw n (k + 1) w + Kraw n k w := by
  intro n
  induction n with
  | zero =>
    intro k w hw
    cases w with
    | zero => rfl
    | succ _ => omega
  | succ n' ih =>
    intro k w hw
    cases w with
    | zero => rfl
    | succ w' =>
      have hw' : w' ≤ n' := by omega
      cases k with
      | zero =>
        simp only [Kraw]
        have h1 := ih 0 w' hw'
        simp only [Kraw] at h1
        omega
      | succ k' =>
        simp only [Kraw]
        have h1 := ih (k' + 1) w' hw'
        have h2 := ih k' w' hw'
        omega

private theorem sum_charS_eq_Kraw :
    ∀ (n k : Nat) (x : BitVec 18),
      sumInt (subsets n k) (fun S => charS S x) = Kraw n k (countBits n (fun i => x.getLsbD i))
  | _, 0, _ => by simp [subsets, sumInt_cons, sumInt_nil, charS, Kraw]
  | 0, k + 1, _ => by simp [subsets, sumInt_nil, Kraw]
  | n + 1, k + 1, x => by
    simp only [subsets, sumInt_append, sumInt_map, countBits]
    have hmap : sumInt (subsets n k) (fun s => charS (n :: s) x) =
        signBool (x.getLsbD n) * sumInt (subsets n k) (fun s => charS s x) := by
      rw [← sumInt_mul_left]
      exact sumInt_congr (subsets n k) _ _ (fun s _ => charS_cons n s x)
    rw [hmap, sum_charS_eq_Kraw n (k + 1) x, sum_charS_eq_Kraw n k x]
    by_cases hx : x.getLsbD n = true
    · simp only [hx, signBool, ↓reduceIte, Kraw]
      omega
    · have hxf : x.getLsbD n = false := by cases h : x.getLsbD n <;> simp_all
      simp only [hxf, signBool, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Nat.add_zero]
      exact (Kraw_add_zero n k _ (countBits_le n _)).symm

private def orthSubsets (C : List (BitVec 18)) (j : Nat) : List (List Nat) :=
  (subsets 18 j).filter (fun S => C.all (fun u => decide (charS S u = 1)))

/-- Binary MacWilliams identity for any linear subspace `C ⊆ BitVec 18`:
    `∑_{u ∈ C} K_j(wt u) = |C| * |(orthSubsets C j)|`. -/
private theorem macWilliams_linear (C : List (BitVec 18))
    (hnd : C.Nodup) (hxor : ∀ a ∈ C, ∀ b ∈ C, (a ^^^ b) ∈ C) (j : Nat) :
    sumInt C (fun u => Kraw 18 j (hammingWeight u)) =
    (C.length : Int) * ((orthSubsets C j).length : Int) := by
  have h1 : sumInt C (fun u => Kraw 18 j (hammingWeight u)) =
      sumInt (subsets 18 j) (fun S => sumInt C (fun u => charS S u)) := by
    rw [← sumInt_swap]
    apply sumInt_congr
    intro u _
    rw [hammingWeight_eq_countBits, sum_charS_eq_Kraw 18 j u]
  rw [h1]
  have hchar : ∀ S : List Nat,
      sumInt C (fun u => charS S u) =
      if C.all (fun u => decide (charS S u = 1)) then (C.length : Int) else 0 := by
    intro S
    by_cases hall : C.all (fun u => decide (charS S u = 1)) = true
    · simp only [hall, ↓reduceIte]
      have hall' : ∀ u ∈ C, charS S u = 1 := fun u hu => by
        have := List.all_eq_true.1 hall u hu
        simpa using this
      rw [sumInt_congr C (fun u => charS S u) (fun _ => 1) hall', sumInt_const, Int.mul_one]
    · have hallf : C.all (fun u => decide (charS S u = 1)) = false := by
        cases h : C.all (fun u => decide (charS S u = 1)) <;> simp_all
      simp only [hallf, Bool.false_eq_true, ↓reduceIte]
      have hex : ∃ u0 ∈ C, charS S u0 = -1 := by
        have hnot : ¬ ∀ u ∈ C, decide (charS S u = 1) = true := by
          intro h
          have := List.all_eq_true.2 h
          rw [this] at hallf; cases hallf
        have hfind : ∀ l : List (BitVec 18), (¬ ∀ u ∈ l, decide (charS S u = 1) = true) →
            ∃ u0 ∈ l, charS S u0 = -1 := by
          intro l
          induction l with
          | nil => intro h; exfalso; apply h; intro _ hm; exact absurd hm List.not_mem_nil
          | cons y ys ih =>
            intro h
            by_cases hy : decide (charS S y = 1) = true
            · rcases ih (fun hys => h (fun u hu => by
                rcases List.mem_cons.1 hu with rfl | hu'
                · exact hy
                · exact hys u hu')) with ⟨u0, hu0, hu0neg⟩
              exact ⟨u0, List.mem_cons_of_mem y hu0, hu0neg⟩
            · refine ⟨y, List.mem_cons_self, ?_⟩
              rcases charS_pm1 S y with h1 | hneg
              · exfalso; apply hy; simp [h1]
              · exact hneg
        exact hfind C hnot
      rcases hex with ⟨u0, hu0, hchar0⟩
      have hnd_map : (C.map (· ^^^ u0)).Nodup := by
        apply nodup_map_of_inj hnd
        intro a _ b _ heq
        have := congrArg (· ^^^ u0) heq
        simpa only [bv_xor_cancel] using this
      have hiff : ∀ x, x ∈ C ↔ x ∈ C.map (· ^^^ u0) := by
        intro x
        constructor
        · intro hx
          exact List.mem_map.2 ⟨x ^^^ u0, hxor x hx u0 hu0, bv_xor_cancel x u0⟩
        · intro hx
          rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
          exact hxor y hy u0 hu0
      have hperm := sumInt_perm_eq (fun u => charS S u) C (C.map (· ^^^ u0)) hnd hnd_map hiff
      rw [sumInt_map] at hperm
      have hneg : sumInt C (fun u => charS S (u ^^^ u0)) = - sumInt C (fun u => charS S u) := by
        have hstep : sumInt C (fun u => charS S (u ^^^ u0)) =
            sumInt C (fun u => (-1 : Int) * charS S u) := by
          apply sumInt_congr
          intro u _
          rw [charS_xor, hchar0, Int.mul_comm]
        rw [hstep, sumInt_mul_left C (-1 : Int) (fun u => charS S u)]
        omega
      omega
  rw [sumInt_congr (subsets 18 j) _ _ (fun S _ => hchar S)]
  unfold orthSubsets
  have hsum_ite : ∀ (l : List (List Nat)) (p : List Nat → Bool) (c : Int),
      sumInt l (fun S => if p S then c else 0) = c * ((l.filter p).length : Int) := by
    intro l p c
    induction l with
    | nil => simp [sumInt_nil]
    | cons x xs ih =>
      simp only [sumInt_cons, List.filter_cons]
      cases p x
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add]; exact ih
      · simp only [↓reduceIte, List.length_cons, Int.natCast_add, Int.mul_add]
        rw [ih]
        change c + c * ↑(List.filter p xs).length = c * ↑(List.filter p xs).length + c * 1
        rw [Int.mul_one, Int.add_comm]
  exact hsum_ite (subsets 18 j) (fun S => C.all (fun u => decide (charS S u = 1))) (C.length : Int)

/-! ## 5. Indicator Bitvectors of Subsets & Z-Distance Equality for `j ≤ 3` -/

private def vecOfSubset : List Nat → BitVec 18
  | [] => 0
  | i :: rest => (BitVec.ofNat 18 1 <<< i) ^^^ vecOfSubset rest

private theorem unit_getLsbD (i m : Nat) (hi : i < 18) :
    (BitVec.ofNat 18 1 <<< i).getLsbD m = decide (m = i) := by
  by_cases hm : m = i
  · subst hm
    simp [hi]
  · simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hm, decide_false]
    by_cases hlt : m < 18
    · by_cases hle : i ≤ m
      · have hne : m - i ≠ 0 := by omega
        cases hd : m - i with
        | zero => exact absurd hd hne
        | succ d => simp [hlt, Nat.testBit_succ]
      · simp [hlt, hle]
    · simp [hlt]

private theorem commutes_unit (i : Nat) (hi : i < 18) (u : BitVec 18) :
    commutes (BitVec.ofNat 18 1 <<< i) u = !(u.getLsbD i) := by
  unfold commutes
  rw [hammingWeight_eq_countBits]
  have h1 : countBits 18 (fun m => ((BitVec.ofNat 18 1 <<< i) &&& u).getLsbD m) =
      countBits 18 (fun m => decide (m = i) && u.getLsbD m) := by
    apply countBits_congr
    intro m _
    rw [BitVec.getLsbD_and, unit_getLsbD i m hi]
  rw [h1]
  have hcnt : ∀ (k : Nat), countBits k (fun m => decide (m = i) && u.getLsbD m) =
      if i < k then (if u.getLsbD i then 1 else 0) else 0 := by
    intro k
    induction k with
    | zero => simp [countBits]
    | succ k' ih =>
      simp only [countBits, ih]
      by_cases hk : k' = i
      · subst hk
        have hnot : ¬ (k' < k') := Nat.lt_irrefl k'
        have hlt : k' < k' + 1 := Nat.lt_succ_self k'
        simp [hnot, hlt]
      · have hne : (decide (k' = i) && u.getLsbD k') = false := by simp [hk]
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        by_cases hlt : i < k'
        · have hlt2 : i < k' + 1 := Nat.lt_succ_of_lt hlt
          simp [hlt, hlt2]
        · have hlt2 : ¬ (i < k' + 1) := by omega
          simp [hlt, hlt2]
  rw [hcnt 18]
  simp only [hi, ↓reduceIte]
  cases u.getLsbD i <;> rfl

private theorem commutes_vecOfSubset_iff (S : List Nat) (hS : ∀ i ∈ S, i < 18) (u : BitVec 18) :
    commutes (vecOfSubset S) u = decide (charS S u = 1) := by
  induction S with
  | nil =>
    simp only [vecOfSubset, charS, List.foldl_nil, decide_true]
    exact commutes_zero_left u
  | cons i rest ih =>
    have hi : i < 18 := hS i List.mem_cons_self
    have hrest := ih (fun x hx => hS x (List.mem_cons_of_mem i hx))
    simp only [vecOfSubset]
    rw [commutes_xor_left, commutes_unit i hi u, hrest, charS_cons]
    rcases charS_pm1 rest u with h1 | hneg
    · rw [h1]; cases u.getLsbD i <;> decide
    · rw [hneg]; cases u.getLsbD i <;> decide

private theorem subsets_props : ∀ (n k : Nat), n ≤ 18 →
    ∀ S ∈ subsets n k,
      (∀ i ∈ S, i < n) ∧
      (∀ m, n ≤ m → (vecOfSubset S).getLsbD m = false) ∧
      hammingWeight (vecOfSubset S) = k
  | _, 0, _, S, hS => by
    simp only [subsets] at hS
    rcases List.mem_cons.1 hS with rfl | h'
    · exact ⟨fun _ hm => absurd hm List.not_mem_nil, fun _ _ => by simp [vecOfSubset], hammingWeight_zero⟩
    · exact absurd h' List.not_mem_nil
  | 0, _ + 1, _, _, hS => absurd hS List.not_mem_nil
  | n + 1, k + 1, hn, S, hS => by
    have hn' : n ≤ 18 := by omega
    rcases List.mem_append.1 hS with h1 | h2
    · rcases subsets_props n (k + 1) hn' S h1 with ⟨hlt, hhi, hwt⟩
      refine ⟨fun i hi => Nat.lt_succ_of_lt (hlt i hi),
        fun m hm => hhi m (by omega), hwt⟩
    · rcases List.mem_map.1 h2 with ⟨rest, hrest, rfl⟩
      rcases subsets_props n k hn' rest hrest with ⟨hlt, hhi, hwt⟩
      have hn18 : n < 18 := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi'
        · exact Nat.lt_succ_self i
        · exact Nat.lt_succ_of_lt (hlt i hi')
      · intro m hm
        simp only [vecOfSubset, BitVec.getLsbD_xor, unit_getLsbD n m hn18]
        have hne : m ≠ n := by omega
        rw [hhi m (by omega)]
        simp [hne]
      · simp only [vecOfSubset]
        rw [hammingWeight_eq_countBits] at hwt ⊢
        have hbit_n : (vecOfSubset rest).getLsbD n = false := hhi n (Nat.le_refl n)
        have hstep : ∀ (t : Nat),
            countBits t (fun m => ((BitVec.ofNat 18 1 <<< n) ^^^ vecOfSubset rest).getLsbD m) =
            countBits t (fun m => (vecOfSubset rest).getLsbD m) + (if n < t then 1 else 0) := by
          intro t
          induction t with
          | zero => simp [countBits]
          | succ t' iht =>
            simp only [countBits]
            rw [iht]
            simp only [BitVec.getLsbD_xor, unit_getLsbD n t' hn18]
            by_cases htn : t' = n
            · subst htn
              have hnot : ¬ (t' < t') := Nat.lt_irrefl t'
              have hlt' : t' < t' + 1 := Nat.lt_succ_self t'
              simp [hbit_n, hnot, hlt']
            · have hne : decide (t' = n) = false := by simp [htn]
              simp only [hne, Bool.false_xor]
              by_cases hlt' : n < t'
              · have hlt2 : n < t' + 1 := Nat.lt_succ_of_lt hlt'
                simp [hlt', hlt2]; omega
              · have hlt2 : ¬ (n < t' + 1) := by omega
                simp [hlt', hlt2]
        rw [hstep 18, hwt]
        simp [hn18]

/-! ## 6. Fast DP Krawtchouk Evaluator & Exact Degree-14 Integer CSS MacWilliams LP Dual Certificate -/

private def krawRowAux : Nat → Nat → Nat → List Int
  | 0, _, m => 1 :: List.replicate m 0
  | n + 1, 0, m =>
    let prev := krawRowAux n 0 m
    1 :: List.zipWith (· + ·) (prev.drop 1) prev
  | n + 1, w + 1, m =>
    let prev := krawRowAux n w m
    1 :: List.zipWith (· - ·) (prev.drop 1) prev

private theorem krawRowAux_length : ∀ (n w m : Nat), (krawRowAux n w m).length = m + 1
  | 0, _, m => by simp [krawRowAux]
  | n + 1, 0, m => by
    simp only [krawRowAux, List.length_cons, List.length_zipWith, List.length_drop, krawRowAux_length n 0 m]
    omega
  | n + 1, w + 1, m => by
    simp only [krawRowAux, List.length_cons, List.length_zipWith, List.length_drop, krawRowAux_length n w m]
    omega

private theorem getD_zipWith_int (op : Int → Int → Int) :
    ∀ (l1 l2 : List Int) (k : Nat), k < l1.length → k < l2.length →
      (List.zipWith op l1 l2).getD k 0 = op (l1.getD k 0) (l2.getD k 0)
  | [], _, _, h1, _ => by simp at h1
  | _, [], _, _, h2 => by simp at h2
  | a :: as, b :: bs, 0, _, _ => rfl
  | a :: as, b :: bs, k + 1, h1, h2 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]
    exact getD_zipWith_int op as bs k (by simp at h1; omega) (by simp at h2; omega)

private theorem getD_drop_int (l : List Int) (k : Nat) :
    (l.drop 1).getD k 0 = l.getD (k + 1) 0 := by
  cases l with
  | nil => simp
  | cons x xs => simp

private theorem krawRowAux_getD :
    ∀ (n w m k : Nat), k ≤ m → (krawRowAux n w m).getD k 0 = Kraw n k w
  | 0, _, _, 0, _ => rfl
  | 0, _, m, k + 1, hk => by
    simp only [krawRowAux, List.getD_cons_succ, Kraw]
    have hlt : k < m := by omega
    simp [List.getD_eq_getElem?_getD, hlt]
  | n + 1, 0, _, 0, _ => rfl
  | n + 1, 0, m, k + 1, hk => by
    simp only [krawRowAux, List.getD_cons_succ, Kraw]
    have hl1 : k < ((krawRowAux n 0 m).drop 1).length := by
      rw [List.length_drop, krawRowAux_length]; omega
    have hl2 : k < (krawRowAux n 0 m).length := by
      rw [krawRowAux_length]; omega
    rw [getD_zipWith_int (· + ·) _ _ k hl1 hl2, getD_drop_int,
        krawRowAux_getD n 0 m (k + 1) hk,
        krawRowAux_getD n 0 m k (by omega)]
  | n + 1, w + 1, _, 0, _ => rfl
  | n + 1, w + 1, m, k + 1, hk => by
    simp only [krawRowAux, List.getD_cons_succ, Kraw]
    have hl1 : k < ((krawRowAux n w m).drop 1).length := by
      rw [List.length_drop, krawRowAux_length]; omega
    have hl2 : k < (krawRowAux n w m).length := by
      rw [krawRowAux_length]; omega
    rw [getD_zipWith_int (· - ·) _ _ k hl1 hl2, getD_drop_int,
        krawRowAux_getD n w m (k + 1) hk,
        krawRowAux_getD n w m k (by omega)]

private def Fpoly (w : Nat) : Int :=
  (-125416) * Kraw 18 0 w + (-32145) * Kraw 18 1 w + (-12054) * Kraw 18 2 w +
  (-2304) * Kraw 18 3 w + 59 * Kraw 18 5 w

private def Gpoly (w : Nat) : Int :=
  97195 * Kraw 18 1 w + 77218 * Kraw 18 2 w + 67912 * Kraw 18 3 w +
  42044 * Kraw 18 4 w + 28208 * Kraw 18 5 w + 12050 * Kraw 18 6 w +
  6260 * Kraw 18 7 w + 1219 * Kraw 18 11 w + 3634 * Kraw 18 12 w +
  2253 * Kraw 18 13 w + 4042 * Kraw 18 14 w

private def FpolyFast (w : Nat) : Int :=
  let r := krawRowAux 18 w 14
  (-125416) * r.getD 0 0 + (-32145) * r.getD 1 0 + (-12054) * r.getD 2 0 +
  (-2304) * r.getD 3 0 + 59 * r.getD 5 0

private def GpolyFast (w : Nat) : Int :=
  let r := krawRowAux 18 w 14
  97195 * r.getD 1 0 + 77218 * r.getD 2 0 + 67912 * r.getD 3 0 +
  42044 * r.getD 4 0 + 28208 * r.getD 5 0 + 12050 * r.getD 6 0 +
  6260 * r.getD 7 0 + 1219 * r.getD 11 0 + 3634 * r.getD 12 0 +
  2253 * r.getD 13 0 + 4042 * r.getD 14 0

private theorem Fpoly_eq_fast (w : Nat) : Fpoly w = FpolyFast w := by
  unfold Fpoly FpolyFast
  dsimp only
  rw [krawRowAux_getD 18 w 14 0 (by decide), krawRowAux_getD 18 w 14 1 (by decide),
      krawRowAux_getD 18 w 14 2 (by decide), krawRowAux_getD 18 w 14 3 (by decide),
      krawRowAux_getD 18 w 14 5 (by decide)]

private theorem Gpoly_eq_fast (w : Nat) : Gpoly w = GpolyFast w := by
  unfold Gpoly GpolyFast
  dsimp only
  rw [krawRowAux_getD 18 w 14 1 (by decide), krawRowAux_getD 18 w 14 2 (by decide),
      krawRowAux_getD 18 w 14 3 (by decide), krawRowAux_getD 18 w 14 4 (by decide),
      krawRowAux_getD 18 w 14 5 (by decide), krawRowAux_getD 18 w 14 6 (by decide),
      krawRowAux_getD 18 w 14 7 (by decide), krawRowAux_getD 18 w 14 11 (by decide),
      krawRowAux_getD 18 w 14 12 (by decide), krawRowAux_getD 18 w 14 13 (by decide),
      krawRowAux_getD 18 w 14 14 (by decide)]

private theorem dual_table_ok :
    (List.range 19).all (fun w =>
      decide (FpolyFast w ≤ 0) &&
      (if w == 0 then decide (255 * FpolyFast 0 + GpolyFast 0 = -161664)
       else decide (255 * FpolyFast w + GpolyFast w ≤ 0)) &&
      (if 4 ≤ w then decide (GpolyFast w - FpolyFast w ≤ 0) else true)) = true := by
  decide +kernel

private theorem dual_F_nonpos (w : Nat) (hw : w ≤ 18) : Fpoly w ≤ 0 := by
  rw [Fpoly_eq_fast]
  have h := List.all_eq_true.1 dual_table_ok w (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

private theorem dual_FG_zero : 255 * Fpoly 0 + Gpoly 0 = -161664 := by
  rw [Fpoly_eq_fast, Gpoly_eq_fast]
  have h := List.all_eq_true.1 dual_table_ok 0 (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at h
  exact h.1.2

private theorem dual_FG_pos_nonpos (w : Nat) (hpos : 0 < w) (hw : w ≤ 18) :
    255 * Fpoly w + Gpoly w ≤ 0 := by
  rw [Fpoly_eq_fast, Gpoly_eq_fast]
  have h := List.all_eq_true.1 dual_table_ok w (List.mem_range.2 (by omega))
  have hne : (w == 0) = false := by cases w with | zero => omega | succ _ => rfl
  simp only [Bool.and_eq_true, hne, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h
  exact h.1.2

private theorem dual_GF_d_nonpos (w : Nat) (h4 : 4 ≤ w) (hw : w ≤ 18) :
    Gpoly w - Fpoly w ≤ 0 := by
  rw [Fpoly_eq_fast, Gpoly_eq_fast]
  have h := List.all_eq_true.1 dual_table_ok w (List.mem_range.2 (by omega))
  simp only [Bool.and_eq_true, h4, ↓reduceIte, decide_eq_true_eq] at h
  exact h.2

/-! ## 7. Main Theorem: `¬ Record 8` -/

theorem record : ¬ Quantum.Statements.QC_rec_n18_d4_w6.Record 8 := by
  intro ⟨k, hx, hz, lx, lz, hk8, hlx, hlz, hcomm, _hwx, _hwz, hlxhz, hlzhx, hsymp, hdx, hdz⟩
  let A : List (BitVec 18) := rowSpaceList hx
  let B : List (BitVec 18) := orthList hz
  have ⟨hA_nd, hA_0, hA_xor, hA_iff⟩ := rowSpaceList_props hx
  have hB_nd : B.Nodup := orthList_nodup hz
  have hB_xor : ∀ a ∈ B, ∀ b ∈ B, (a ^^^ b) ∈ B := fun _ ha _ hb => orthList_xor hz ha hb
  -- 1. `A ⊆ B`
  have hAB : ∀ u ∈ A, u ∈ B := by
    intro u hu
    rw [mem_orthList_iff]
    intro z hzMem
    rw [commutes_comm]
    exact commutes_of_inRowSpace (fun x hxMem => by rw [commutes_comm]; exact hcomm x hxMem z hzMem)
      ((hA_iff u).1 hu)
  -- 2. `256 * A.length ≤ B.length` via the 128 distinct logical-X cosets of `A` in `B`
  have hcoset_len : 256 * A.length ≤ B.length := by
    let lx8 := lx.take 8
    have hlx8_len : lx8.length = 8 := by
      simp [lx8, hlx]; omega
    let masks := allMasks 8
    let cosets := masks.flatMap (fun m => A.map (fun a => a ^^^ xorSubset lx8 m))
    have hcosets_len : cosets.length = 256 * A.length := by
      have hlen := flatMap_length_const masks (fun m => A.map (fun a => a ^^^ xorSubset lx8 m))
        A.length (fun _ _ => List.length_map _)
      rw [allMasks_length 8] at hlen
      exact hlen
    have hrep_in_B : ∀ m ∈ masks, xorSubset lx8 m ∈ B := by
      intro m hm
      rw [mem_orthList_iff]
      intro z hzMem
      rw [commutes_comm]
      apply commutes_of_inRowSpace (gens := lx8)
      · intro x hxMem
        have hxLx : x ∈ lx := List.mem_of_mem_take hxMem
        rw [commutes_comm]
        exact hlxhz x hxLx z hzMem
      · exact ⟨m, by rw [allMasks_mem_length 8 m hm, hlx8_len], rfl⟩
    have hcosets_sub : ∀ v ∈ cosets, v ∈ B := by
      intro v hv
      rcases List.mem_flatMap.1 hv with ⟨m, hm, hv'⟩
      rcases List.mem_map.1 hv' with ⟨a, ha, rfl⟩
      exact hB_xor a (hAB a ha) (xorSubset lx8 m) (hrep_in_B m hm)
    have hcosets_nd : cosets.Nodup := by
      apply nodup_flatMap_of_inj masks A (fun m a => a ^^^ xorSubset lx8 m) (allMasks_nodup 8) hA_nd
      intro m1 hm1 a1 ha1 m2 hm2 a2 ha2 heq
      have hm1_len : m1.length = 8 := allMasks_mem_length 8 m1 hm1
      have hm2_len : m2.length = 8 := allMasks_mem_length 8 m2 hm2
      have hm_eq : m1 = m2 := by
        apply list_eq_of_getD_eq m1 m2 (by omega)
        intro j hj
        have hj8 : j < 8 := by omega
        have hjk : j < k := by omega
        let zj := lz.getD j 0
        have hzj_mem : zj ∈ lz := list_getD_mem lz j 0 (by rw [hlz]; exact hjk)
        have ha1_z : commutes a1 zj = true := by
          rw [commutes_comm]
          exact commutes_of_inRowSpace (fun x hxMem => hlzhx zj hzj_mem x hxMem) ((hA_iff a1).1 ha1)
        have ha2_z : commutes a2 zj = true := by
          rw [commutes_comm]
          exact commutes_of_inRowSpace (fun x hxMem => hlzhx zj hzj_mem x hxMem) ((hA_iff a2).1 ha2)
        have hsymp8 : ∀ i, i < lx8.length → commutes (lx8.getD i 0) zj = decide (i ≠ j) := by
          intro i hi
          have hi8 : i < 8 := by rw [hlx8_len] at hi; exact hi
          have hik : i < k := by omega
          rw [list_getD_take lx 8 i 0 hi8]
          exact hsymp ⟨i, hik⟩ ⟨j, hjk⟩
        have hc1 := commutes_xorSubset_symp lx8 m1 zj j (by omega) (by omega) hsymp8
        have hc2 := commutes_xorSubset_symp lx8 m2 zj j (by omega) (by omega) hsymp8
        have hceq := congrArg (fun v => commutes v zj) heq
        rw [commutes_xor_left, commutes_xor_left, ha1_z, ha2_z, hc1, hc2] at hceq
        cases hb1 : m1.getD j false <;> cases hb2 : m2.getD j false <;>
          rw [hb1, hb2] at hceq <;> first | rfl | cases hceq
      subst hm_eq
      have ha_eq : a1 = a2 := by
        have := congrArg (· ^^^ xorSubset lx8 m1) heq
        simpa only [bv_xor_cancel] using this
      exact ⟨rfl, ha_eq⟩
    have hle := nodup_length_le_of_subset cosets B hcosets_nd hcosets_sub
    omega
  -- 3. Split `B` into `A` and `Delta := B.filter (fun u => !A.contains u)`
  let Delta : List (BitVec 18) := B.filter (fun u => !(A.contains u))
  have hsumB_split : ∀ f : BitVec 18 → Int, sumInt B f = sumInt A f + sumInt Delta f := by
    intro f
    rw [sumInt_filter_split B (fun u => A.contains u) f]
    have hperm : sumInt (B.filter (fun u => A.contains u)) f = sumInt A f := by
      apply sumInt_perm_eq f _ _ (nodup_filter hB_nd) hA_nd
      intro x
      rw [List.mem_filter, List.contains_iff_mem]
      exact ⟨fun h => h.2, fun hx => ⟨hAB x hx, hx⟩⟩
    rw [hperm]
  have hDelta_wt : ∀ u ∈ Delta, 4 ≤ hammingWeight u := by
    intro u hu
    rw [List.mem_filter] at hu
    have huB : u ∈ B := hu.1
    have huNotA : u ∉ A := by
      intro hmem
      have hc := List.contains_iff_mem.2 hmem
      rw [hc] at hu; simp at hu
    have hne0 : u ≠ 0 := fun h0 => huNotA (h0 ▸ hA_0)
    have hpos : 0 < hammingWeight u := hammingWeight_pos_of_ne_zero hne0
    cases Nat.lt_or_ge (hammingWeight u) 4 with
    | inl hlt4 =>
      exfalso
      have hcommZ : ∀ z ∈ hz, commutes u z = true := (mem_orthList_iff hz u).1 huB
      exact huNotA ((hA_iff u).2 (hdx u hpos hlt4 hcommZ))
    | inr hge4 => exact hge4
  -- 4. Dual MacWilliams quantities `E_j` and `D_j`
  let aLen : Int := (A.length : Int)
  let bLen : Int := (B.length : Int)
  let KA : Nat → Int := fun j => sumInt A (fun u => Kraw 18 j (hammingWeight u))
  let KB : Nat → Int := fun j => sumInt B (fun u => Kraw 18 j (hammingWeight u))
  let KD : Nat → Int := fun j => sumInt Delta (fun u => Kraw 18 j (hammingWeight u))
  let E : Nat → Int := fun j => bLen * KA j - aLen * KB j
  let D : Nat → Int := fun j => aLen * KB j
  have hKA_mw : ∀ j, KA j = aLen * ((orthSubsets A j).length : Int) :=
    fun j => macWilliams_linear A hA_nd hA_xor j
  have hKB_mw : ∀ j, KB j = bLen * ((orthSubsets B j).length : Int) :=
    fun j => macWilliams_linear B hB_nd hB_xor j
  have hD_nonneg : ∀ j, 0 ≤ D j := by
    intro j
    change 0 ≤ aLen * KB j
    rw [hKB_mw j]
    have ha0 : (0 : Int) ≤ aLen := Int.natCast_nonneg _
    have hb0 : (0 : Int) ≤ bLen := Int.natCast_nonneg _
    have hw0 : (0 : Int) ≤ ((orthSubsets B j).length : Int) := Int.natCast_nonneg _
    exact Int.mul_nonneg ha0 (Int.mul_nonneg hb0 hw0)
  have hE_nonneg : ∀ j, 0 ≤ E j := by
    intro j
    change 0 ≤ bLen * KA j - aLen * KB j
    rw [hKA_mw j, hKB_mw j]
    have hle : (orthSubsets B j).length ≤ (orthSubsets A j).length := by
      apply length_filter_le_of_imp
      intro S _ hB_all
      apply List.all_eq_true.2
      intro u huA
      exact List.all_eq_true.1 hB_all u (hAB u huA)
    have hle_int : ((orthSubsets B j).length : Int) ≤ ((orthSubsets A j).length : Int) :=
      Int.ofNat_le.2 hle
    have hab : (0 : Int) ≤ aLen * bLen := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hdiff : 0 ≤ (aLen * bLen) * (((orthSubsets A j).length : Int) - ((orthSubsets B j).length : Int)) :=
      Int.mul_nonneg hab (by omega)
    have hring : bLen * (aLen * ((orthSubsets A j).length : Int)) -
        aLen * (bLen * ((orthSubsets B j).length : Int)) =
        (aLen * bLen) * (((orthSubsets A j).length : Int) - ((orthSubsets B j).length : Int)) := by
      rw [Int.mul_sub, Int.mul_assoc aLen bLen, Int.mul_assoc aLen bLen,
        ← Int.mul_assoc bLen aLen, Int.mul_comm bLen aLen, Int.mul_assoc]
    omega
  have hE_zero_0 : E 0 = 0 := by
    change bLen * KA 0 - aLen * KB 0 = 0
    rw [hKA_mw 0, hKB_mw 0]
    have heq : orthSubsets A 0 = orthSubsets B 0 := by
      apply filter_congr_mem
      intro S hS
      rcases List.mem_cons.1 hS with rfl | h'
      · have h1 : A.all (fun u => decide (charS [] u = 1)) = true :=
          List.all_eq_true.2 (fun _ _ => rfl)
        have h2 : B.all (fun u => decide (charS [] u = 1)) = true :=
          List.all_eq_true.2 (fun _ _ => rfl)
        rw [h1, h2]
      · exact absurd h' List.not_mem_nil
    rw [heq, ← Int.mul_assoc, Int.mul_comm bLen aLen, Int.mul_assoc]
    omega
  have hE_zero_small : ∀ j, 0 < j → j < 4 → E j = 0 := by
    intro j hjpos hjlt
    change bLen * KA j - aLen * KB j = 0
    rw [hKA_mw j, hKB_mw j]
    have heq : orthSubsets A j = orthSubsets B j := by
      apply filter_congr_mem
      intro S hS
      rcases subsets_props 18 j (Nat.le_refl 18) S hS with ⟨hS18, _, hSwt⟩
      cases hAall : A.all (fun u => decide (charS S u = 1))
      · cases hBall : B.all (fun u => decide (charS S u = 1))
        · rfl
        · exfalso
          have hAtrue : A.all (fun u => decide (charS S u = 1)) = true :=
            List.all_eq_true.2 (fun u huA => List.all_eq_true.1 hBall u (hAB u huA))
          rw [hAtrue] at hAall; cases hAall
      · symm
        apply List.all_eq_true.2
        intro u huB
        let e := vecOfSubset S
        have he_comm_hx : ∀ x ∈ hx, commutes e x = true := by
          intro x hxMem
          have hxA : x ∈ A := (hA_iff x).2 (inRowSpace_of_mem hxMem)
          have hch : decide (charS S x = 1) = true := List.all_eq_true.1 hAall x hxA
          rw [commutes_vecOfSubset_iff S hS18 x]
          exact hch
        have he_pos : 0 < hammingWeight e := by rw [hSwt]; exact hjpos
        have he_lt : hammingWeight e < 4 := by rw [hSwt]; exact hjlt
        have he_in_hz : InRowSpace hz e := hdz e he_pos he_lt he_comm_hx
        have hu_comm_e : commutes u e = true :=
          commutes_of_inRowSpace ((mem_orthList_iff hz u).1 huB) he_in_hz
        rw [← commutes_vecOfSubset_iff S hS18 u, commutes_comm]
        exact hu_comm_e
    rw [heq, ← Int.mul_assoc, Int.mul_comm bLen aLen, Int.mul_assoc]
    omega
  -- 5. Dual lower bound `0 ≤ S`
  let S : Int :=
    (-125416) * E 0 + (-32145) * E 1 + (-12054) * E 2 + (-2304) * E 3 + 59 * E 5 +
    97195 * D 1 + 77218 * D 2 + 67912 * D 3 + 42044 * D 4 + 28208 * D 5 + 12050 * D 6 +
    6260 * D 7 + 1219 * D 11 + 3634 * D 12 + 2253 * D 13 + 4042 * D 14
  have hS_nonneg : 0 ≤ S := by
    have hE0 : E 0 = 0 := hE_zero_0
    have hE1 : E 1 = 0 := hE_zero_small 1 (by decide) (by decide)
    have hE2 : E 2 = 0 := hE_zero_small 2 (by decide) (by decide)
    have hE3 : E 3 = 0 := hE_zero_small 3 (by decide) (by decide)
    have hE5 : 0 ≤ E 5 := hE_nonneg 5
    have hD1 : 0 ≤ D 1 := hD_nonneg 1
    have hD2 : 0 ≤ D 2 := hD_nonneg 2
    have hD3 : 0 ≤ D 3 := hD_nonneg 3
    have hD4 : 0 ≤ D 4 := hD_nonneg 4
    have hD5 : 0 ≤ D 5 := hD_nonneg 5
    have hD6 : 0 ≤ D 6 := hD_nonneg 6
    have hD7 : 0 ≤ D 7 := hD_nonneg 7
    have hD11 : 0 ≤ D 11 := hD_nonneg 11
    have hD12 : 0 ≤ D 12 := hD_nonneg 12
    have hD13 : 0 ≤ D 13 := hD_nonneg 13
    have hD14 : 0 ≤ D 14 := hD_nonneg 14
    dsimp only [S]
    omega
  -- 6. Primal expansion of `S` over `A` and `Delta`
  have hKB_eq : ∀ j, KB j = KA j + KD j := fun j => hsumB_split (fun u => Kraw 18 j (hammingWeight u))
  have hE_eq : ∀ j, E j = (bLen - aLen) * KA j - aLen * KD j := by
    intro j
    change bLen * KA j - aLen * KB j = (bLen - aLen) * KA j - aLen * KD j
    rw [hKB_eq j, Int.mul_add, Int.sub_mul]
    omega
  have hD_eq : ∀ j, D j = aLen * KA j + aLen * KD j := by
    intro j
    change aLen * KB j = aLen * KA j + aLen * KD j
    rw [hKB_eq j, Int.mul_add]
  have hsumA_F : sumInt A (fun u => Fpoly (hammingWeight u)) =
      (-125416) * KA 0 + (-32145) * KA 1 + (-12054) * KA 2 + (-2304) * KA 3 + 59 * KA 5 := by
    simp only [Fpoly, KA, sumInt_add, sumInt_mul_left]
  have hsumA_G : sumInt A (fun u => Gpoly (hammingWeight u)) =
      97195 * KA 1 + 77218 * KA 2 + 67912 * KA 3 + 42044 * KA 4 + 28208 * KA 5 + 12050 * KA 6 +
      6260 * KA 7 + 1219 * KA 11 + 3634 * KA 12 + 2253 * KA 13 + 4042 * KA 14 := by
    simp only [Gpoly, KA, sumInt_add, sumInt_mul_left]
  have hsumD_F : sumInt Delta (fun u => Fpoly (hammingWeight u)) =
      (-125416) * KD 0 + (-32145) * KD 1 + (-12054) * KD 2 + (-2304) * KD 3 + 59 * KD 5 := by
    simp only [Fpoly, KD, sumInt_add, sumInt_mul_left]
  have hsumD_G : sumInt Delta (fun u => Gpoly (hammingWeight u)) =
      97195 * KD 1 + 77218 * KD 2 + 67912 * KD 3 + 42044 * KD 4 + 28208 * KD 5 + 12050 * KD 6 +
      6260 * KD 7 + 1219 * KD 11 + 3634 * KD 12 + 2253 * KD 13 + 4042 * KD 14 := by
    simp only [Gpoly, KD, sumInt_add, sumInt_mul_left]
  have hS_primal :
      S = sumInt A (fun u => (bLen - aLen) * Fpoly (hammingWeight u) + aLen * Gpoly (hammingWeight u)) +
          sumInt Delta (fun u => aLen * (Gpoly (hammingWeight u) - Fpoly (hammingWeight u))) := by
    have hA_side :
        sumInt A (fun u => (bLen - aLen) * Fpoly (hammingWeight u) + aLen * Gpoly (hammingWeight u)) =
        (bLen - aLen) * sumInt A (fun u => Fpoly (hammingWeight u)) +
        aLen * sumInt A (fun u => Gpoly (hammingWeight u)) := by
      rw [sumInt_add, sumInt_mul_left, sumInt_mul_left]
    have hD_side :
        sumInt Delta (fun u => aLen * (Gpoly (hammingWeight u) - Fpoly (hammingWeight u))) =
        aLen * sumInt Delta (fun u => Gpoly (hammingWeight u)) -
        aLen * sumInt Delta (fun u => Fpoly (hammingWeight u)) := by
      have hsub : sumInt Delta (fun u => aLen * (Gpoly (hammingWeight u) - Fpoly (hammingWeight u))) =
          sumInt Delta (fun u => aLen * Gpoly (hammingWeight u) + (-aLen) * Fpoly (hammingWeight u)) := by
        apply sumInt_congr
        intro u _
        rw [Int.mul_sub, Int.neg_mul]
        omega
      rw [hsub, sumInt_add, sumInt_mul_left, sumInt_mul_left, Int.neg_mul]
      omega
    rw [hA_side, hD_side, hsumA_F, hsumA_G, hsumD_F, hsumD_G]
    dsimp only [S]
    rw [hE_eq 0, hE_eq 1, hE_eq 2, hE_eq 3, hE_eq 5,
        hD_eq 1, hD_eq 2, hD_eq 3, hD_eq 4, hD_eq 5, hD_eq 6, hD_eq 7,
        hD_eq 11, hD_eq 12, hD_eq 13, hD_eq 14]
    -- Expand linear combinations cleanly with `Int.mul_add` / `Int.mul_sub`
    have hmul_c : ∀ (c x y : Int), c * (x * y) = x * (c * y) := by
      intro c x y
      rw [← Int.mul_assoc, Int.mul_comm c x, Int.mul_assoc]
    simp only [Int.mul_add, Int.mul_sub, hmul_c]
    omega
  -- 7. Upper bound `S < 0`
  have haLen_pos : (1 : Int) ≤ aLen := by
    have hpos : 0 < (rowSpaceList hx).length := by
      cases hA : rowSpaceList hx with
      | nil => rw [hA] at hA_0; exact absurd hA_0 List.not_mem_nil
      | cons _ _ => simp
    change (1 : Int) ≤ ((rowSpaceList hx).length : Int)
    omega
  have hdiff_ge : 255 * aLen ≤ bLen - aLen := by
    change 255 * (A.length : Int) ≤ (B.length : Int) - (A.length : Int)
    omega
  have hDelta_nonpos :
      sumInt Delta (fun u => aLen * (Gpoly (hammingWeight u) - Fpoly (hammingWeight u))) ≤ 0 := by
    have h0 : sumInt Delta (fun _ => (0 : Int)) = 0 := by rw [sumInt_const]; simp
    rw [← h0]
    apply sumInt_le
    intro u hu
    have hgf : Gpoly (hammingWeight u) - Fpoly (hammingWeight u) ≤ 0 :=
      dual_GF_d_nonpos (hammingWeight u) (hDelta_wt u hu) (hammingWeight_le u)
    have hneg : 0 ≤ aLen * (-(Gpoly (hammingWeight u) - Fpoly (hammingWeight u))) :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg] at hneg
    omega
  have hA_term_le : ∀ u : BitVec 18,
      (bLen - aLen) * Fpoly (hammingWeight u) + aLen * Gpoly (hammingWeight u) ≤
      aLen * (255 * Fpoly (hammingWeight u) + Gpoly (hammingWeight u)) := by
    intro u
    have hFn : Fpoly (hammingWeight u) ≤ 0 := dual_F_nonpos (hammingWeight u) (hammingWeight_le u)
    have hmul : 0 ≤ ((bLen - aLen) - 255 * aLen) * (- Fpoly (hammingWeight u)) :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.sub_mul, Int.mul_neg, Int.mul_neg, Int.mul_assoc 255 aLen] at hmul
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm aLen 255, Int.mul_assoc]
    omega
  have hA_upper :
      sumInt A (fun u => (bLen - aLen) * Fpoly (hammingWeight u) + aLen * Gpoly (hammingWeight u)) ≤
      aLen * (-161664) := by
    have h1 := sumInt_le A _ (fun u => aLen * (255 * Fpoly (hammingWeight u) + Gpoly (hammingWeight u)))
      (fun u _ => hA_term_le u)
    have h2 : sumInt A (fun u => aLen * (255 * Fpoly (hammingWeight u) + Gpoly (hammingWeight u))) ≤
        aLen * (255 * Fpoly (hammingWeight (0 : BitVec 18)) + Gpoly (hammingWeight (0 : BitVec 18))) := by
      apply sumInt_extract_mem hA_nd hA_0
      intro u _ hne0
      have hpos : 0 < hammingWeight u := hammingWeight_pos_of_ne_zero hne0
      have hle : 255 * Fpoly (hammingWeight u) + Gpoly (hammingWeight u) ≤ 0 :=
        dual_FG_pos_nonpos (hammingWeight u) hpos (hammingWeight_le u)
      have hneg : 0 ≤ aLen * (-(255 * Fpoly (hammingWeight u) + Gpoly (hammingWeight u))) :=
        Int.mul_nonneg (by omega) (by omega)
      rw [Int.mul_neg] at hneg
      omega
    rw [hammingWeight_zero, dual_FG_zero] at h2
    omega
  have hS_lt : S ≤ aLen * (-161664) := by omega
  have hneg_strict : aLen * (-161664) ≤ -161664 := by
    have h1 : 0 ≤ (aLen - 1) * 161664 := Int.mul_nonneg (by omega) (by decide)
    rw [Int.sub_mul, Int.one_mul] at h1
    omega
  omega

end Quantum.Claims.QC_rec_n18_d4_w6_not_s8
