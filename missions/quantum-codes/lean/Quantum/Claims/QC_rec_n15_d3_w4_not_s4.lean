import Quantum.Core
import Quantum.Statements.QC_rec_n15_d3_w4

namespace Quantum.Claims.QC_rec_n15_d3_w4_not_s4

open Quantum

/-! ## 1. Elementary List & BitVec Helpers -/

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hxys : x ∈ ys := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := fun he => hxnot (he ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons_of_mem _ hz))
    have hle := ih hnd' hsub'
    have her : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hxys]
      have hpos : 0 < ys.length := List.length_pos_of_mem hxys
      omega
    simp only [List.length_cons]
    omega

private theorem nodup_map_of_inj {α β : Type} {f : α → β} {xs : List α} (hnd : xs.Nodup)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hnd' (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have heq := hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb
    exact hnot (heq ▸ hb)

private theorem nodup_filter {α : Type} (p : α → Bool) {xs : List α} (h : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp h
    cases hp : p a
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd
    · simp only [List.filter_cons, hp, ↓reduceIte]
      exact List.nodup_cons.mpr ⟨fun ha => hnot (List.mem_filter.mp ha).1, ih hnd⟩

private def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as => let ds := dedup as; if a ∈ ds then ds else a :: ds

private theorem mem_dedup {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (x : α), x ∈ dedup xs ↔ x ∈ xs
  | [], x => by simp [dedup]
  | a :: as, x => by
    simp only [dedup]
    by_cases ha : a ∈ dedup as
    · simp only [ha, ↓reduceIte, mem_dedup as, List.mem_cons]
      have ha' : a ∈ as := (mem_dedup as a).mp ha
      constructor
      · intro hx; exact Or.inr hx
      · rintro (rfl | hx); exact ha'; exact hx
    · simp only [ha, ↓reduceIte, List.mem_cons, mem_dedup as]

private theorem nodup_dedup {α : Type} [DecidableEq α] :
    ∀ (xs : List α), (dedup xs).Nodup
  | [] => List.nodup_nil
  | a :: as => by
    simp only [dedup]
    by_cases ha : a ∈ dedup as
    · simp only [ha, ↓reduceIte]; exact nodup_dedup as
    · simp only [ha, ↓reduceIte]; exact List.nodup_cons.mpr ⟨ha, nodup_dedup as⟩

private theorem replicate_add {α : Type} (a : α) :
    ∀ m n, List.replicate m a ++ List.replicate n a = List.replicate (m + n) a
  | 0, n => by simp
  | m + 1, n => by
    rw [List.replicate_succ, List.cons_append, replicate_add a m n, Nat.succ_add, List.replicate_succ]

private theorem pow2_le_imp_le {a b : Nat} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  apply Classical.byContradiction
  intro hlt
  have hgt : b < a := by omega
  have : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by omega : 1 < 2) hgt
  omega

private def unitVec (n i : Nat) : BitVec n :=
  BitVec.ofNat n 1 <<< i

private theorem unitVec_getLsbD {n i j : Nat} (hi : i < n) :
    (unitVec n i).getLsbD j = decide (j = i) := by
  unfold unitVec
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hj : j < n
  · simp only [hj, decide_true, Bool.true_and]
    by_cases hji : j = i
    · subst hji
      have h0 : 0 < n := by omega
      simp [hi, h0]
    · by_cases hle : i ≤ j
      · have hne : j - i ≠ 0 := by omega
        cases hm : j - i with
        | zero => omega
        | succ m =>
          have : (BitVec.ofNat n 1).getLsbD (m + 1) = false := by
            rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_succ]
          simp [hji, hle, this]
      · simp [hji, hle]
  · have hne : j ≠ i := by omega
    simp [hj, hne]

private def mkBitVec (n : Nat) (f : Nat → Bool) : BitVec n :=
  (List.range n).foldl (fun acc i => if f i then acc ||| unitVec n i else acc) 0

private theorem mkBitVec_getLsbD (n : Nat) (f : Nat → Bool) {j : Nat} (hj : j < n) :
    (mkBitVec n f).getLsbD j = f j := by
  unfold mkBitVec
  have hgen : ∀ k ≤ n, ((List.range k).foldl (fun acc i => if f i then acc ||| unitVec n i else acc) 0).getLsbD j =
      if j < k then f j else false := by
    intro k; induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hfk : f k = true
      · simp only [hfk, ↓reduceIte, BitVec.getLsbD_or, ih (by omega), unitVec_getLsbD (by omega : k < n)]
        by_cases hjk : j = k
        · subst hjk; simp [hfk]
        · have hlt : (j < k + 1) ↔ (j < k) := by omega
          simp [hjk, hlt]
      · have hfkf : f k = false := Bool.eq_false_iff.mpr hfk
        simp only [hfkf, Bool.false_eq_true, ↓reduceIte, ih (by omega)]
        by_cases hjk : j = k
        · subst hjk; simp [hfkf]
        · have hlt : (j < k + 1) ↔ (j < k) := by omega
          simp [hlt]
  simpa [hj] using hgen n (Nat.le_refl n)

private theorem popCountAux_bit_decomp : ∀ (k x : Nat),
    popCountAux (k + 1) x = popCountAux k x + (if Nat.testBit x k then 1 else 0)
  | 0, x => by
    simp only [popCountAux, Nat.testBit_zero]
    by_cases h : x % 2 = 1
    · simp [h]
    · have h0 : x % 2 = 0 := by omega
      simp [h0]
  | k + 1, x => by
    change x % 2 + popCountAux (k + 1) (x / 2) =
      x % 2 + popCountAux k (x / 2) + (if Nat.testBit x (k + 1) then 1 else 0)
    rw [popCountAux_bit_decomp k (x / 2), Nat.testBit_succ]
    omega

private theorem popCountAux_eq_fold {n : Nat} (v : BitVec n) :
    ∀ k ≤ n, popCountAux k v.toNat =
      (List.range k).foldl (fun acc i => if v.getLsbD i then acc + 1 else acc) 0 := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [popCountAux_bit_decomp, ih (by omega), List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hbit : v.getLsbD k = Nat.testBit v.toNat k := rfl
    rw [hbit]
    cases Nat.testBit v.toNat k <;> simp

private theorem hammingWeight_eq_sum {n : Nat} (v : BitVec n) :
    hammingWeight v = (List.range n).foldl (fun acc i => if v.getLsbD i then acc + 1 else acc) 0 :=
  popCountAux_eq_fold v n (Nat.le_refl n)

private theorem foldl_count_add {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (acc : Nat),
      xs.foldl (fun a i => if p i then a + 1 else a) acc =
      acc + xs.foldl (fun a i => if p i then a + 1 else a) 0 := by
  intro xs; induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih acc
    · rw [ih (acc + 1), ih 1]; omega

private theorem foldl_count_eq_filter_length {α : Type} (p : α → Bool) (xs : List α) :
    xs.foldl (fun a i => if p i then a + 1 else a) 0 = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.filter_cons]
    cases p x <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih
    · rw [foldl_count_add p xs 1, ih, List.length_cons]; omega

private theorem hammingWeight_eq_filter {n : Nat} (v : BitVec n) :
    hammingWeight v = ((List.range n).filter (fun i => v.getLsbD i)).length := by
  rw [hammingWeight_eq_sum, foldl_count_eq_filter_length]

private theorem commutes_symm {n : Nat} (u v : BitVec n) : commutes u v = commutes v u := by
  unfold commutes
  have : u &&& v = v &&& u := by
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp [Bool.and_comm]
  rw [this]

private theorem commutes_zero_left {n : Nat} (v : BitVec n) : commutes 0 v = true := by
  unfold commutes
  have h0 : (0 : BitVec n) &&& v = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp
  rw [h0, hammingWeight_eq_filter]
  have hf : (List.range n).filter (fun i => (0 : BitVec n).getLsbD i) = [] := by
    rw [List.filter_eq_nil_iff]; intro i _; simp
  rw [hf]; rfl

private theorem commutes_xor_left {n : Nat} (a b v : BitVec n) :
    commutes (a ^^^ b) v = (commutes a v == commutes b v) := by
  unfold commutes
  rw [hammingWeight_eq_sum, hammingWeight_eq_sum, hammingWeight_eq_sum]
  have hgen : ∀ (xs : List Nat) (x1 x2 x3 : Nat),
      (x1 % 2 == 0) = ((x2 % 2 == 0) == (x3 % 2 == 0)) →
      (xs.foldl (fun acc i => if ((a ^^^ b) &&& v).getLsbD i then acc + 1 else acc) x1 % 2 == 0) =
      ((xs.foldl (fun acc i => if (a &&& v).getLsbD i then acc + 1 else acc) x2 % 2 == 0) ==
       (xs.foldl (fun acc i => if (b &&& v).getLsbD i then acc + 1 else acc) x3 % 2 == 0)) := by
    intro xs; induction xs with
    | nil => intro x1 x2 x3 h; exact h
    | cons i xs ih =>
      intro x1 x2 x3 h
      simp only [List.foldl_cons]
      apply ih
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases v.getLsbD i <;>
        simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false,
                   Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;>
        (rcases Nat.mod_two_eq_zero_or_one x1 with h1 | h1 <;>
         rcases Nat.mod_two_eq_zero_or_one x2 with h2 | h2 <;>
         rcases Nat.mod_two_eq_zero_or_one x3 with h3 | h3 <;>
         simp [h1, h2, h3, Nat.add_mod] at h ⊢)
  exact hgen (List.range n) 0 0 0 rfl

private theorem commutes_xor_right {n : Nat} (u a b : BitVec n) :
    commutes u (a ^^^ b) = (commutes u a == commutes u b) := by
  rw [commutes_symm u, commutes_xor_left, commutes_symm a, commutes_symm b]

private theorem commutes_xorSubset_left {n : Nat} :
    ∀ (gens : List (BitVec n)) (mask : List Bool) (z : BitVec n),
      (∀ x ∈ gens, commutes x z = true) → commutes (xorSubset gens mask) z = true
  | [], _, z, _ => commutes_zero_left z
  | _ :: _, [], z, _ => commutes_zero_left z
  | g :: gs, b :: bs, z, h => by
    simp only [xorSubset]
    rw [commutes_xor_left]
    have h1 : commutes (if b then g else 0) z = true := by
      cases b
      · exact commutes_zero_left z
      · exact h g (List.mem_cons_self ..)
    have h2 : commutes (xorSubset gs bs) z = true :=
      commutes_xorSubset_left gs bs z (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [h1, h2]; rfl

private theorem commutes_inRowSpace {n : Nat} {gens : List (BitVec n)} {v z : BitVec n}
    (hv : InRowSpace gens v) (hz : ∀ x ∈ gens, commutes x z = true) : commutes v z = true := by
  obtain ⟨m, _, rfl⟩ := hv
  exact commutes_xorSubset_left gens m z hz

private theorem hammingWeight_unitVec {n i : Nat} (hi : i < n) :
    hammingWeight (unitVec n i) = 1 := by
  rw [hammingWeight_eq_filter]
  have hgen : ∀ k, ((List.range k).filter (fun j => (unitVec n i).getLsbD j)).length =
      if i < k then 1 else 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      simp only [List.filter_cons, List.filter_nil, unitVec_getLsbD hi]
      by_cases hk : k = i
      · subst hk; simp
      · have hlt : (i < k + 1) ↔ (i < k) := by omega
        simp [hk, hlt]
  simpa [hi] using hgen n

private theorem hammingWeight_xor_unitVec {n i j : Nat} (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    hammingWeight (unitVec n i ^^^ unitVec n j) = 2 := by
  rw [hammingWeight_eq_filter]
  have hbit : ∀ t, (unitVec n i ^^^ unitVec n j).getLsbD t = (decide (t = i) || decide (t = j)) := by
    intro t; rw [BitVec.getLsbD_xor, unitVec_getLsbD hi, unitVec_getLsbD hj]
    by_cases h1 : t = i <;> by_cases h2 : t = j
    · omega
    · simp [h1, h2, hne]
    · simp [h1, h2, hne.symm]
    · simp [h1, h2]
  have hgen : ∀ k, ((List.range k).filter (fun t => (unitVec n i ^^^ unitVec n j).getLsbD t)).length =
      (if i < k then 1 else 0) + (if j < k then 1 else 0) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      simp only [List.filter_cons, List.filter_nil, hbit]
      by_cases hki : k = i
      · subst hki
        have h1 : ¬ (k < k) := Nat.lt_irrefl k
        have h2 : k < k + 1 := Nat.lt_succ_self k
        have h3 : (j < k + 1) ↔ (j < k) := by omega
        simp [h1, h2, h3, hne]
        omega
      · by_cases hkj : k = j
        · subst hkj
          have h1 : ¬ (k < k) := Nat.lt_irrefl k
          have h2 : k < k + 1 := Nat.lt_succ_self k
          have h3 : (i < k + 1) ↔ (i < k) := by omega
          simp [h1, h2, h3, hne.symm]
        · have h1 : (i < k + 1) ↔ (i < k) := by omega
          have h2 : (j < k + 1) ↔ (j < k) := by omega
          simp [hki, hkj, h1, h2]
  simpa [hi, hj] using hgen n

private theorem commutes_unitVec {n i : Nat} (hi : i < n) (v : BitVec n) :
    commutes (unitVec n i) v = !(v.getLsbD i) := by
  unfold commutes
  rw [hammingWeight_eq_filter]
  have hbit : ∀ t, ((unitVec n i) &&& v).getLsbD t = (decide (t = i) && v.getLsbD t) := by
    intro t; rw [BitVec.getLsbD_and, unitVec_getLsbD hi]
  have hgen : ∀ k, ((List.range k).filter (fun t => ((unitVec n i) &&& v).getLsbD t)).length =
      if i < k ∧ v.getLsbD i = true then 1 else 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      simp only [List.filter_cons, List.filter_nil, hbit]
      by_cases hk : k = i
      · subst hk; cases hb : v.getLsbD k <;> simp [hb]
      · have hlt : (i < k + 1) ↔ (i < k) := by omega
        simp [hk, hlt]
  rw [hgen n]
  cases hb : v.getLsbD i <;> simp [hi, hb]

private theorem xorSubset_getLsbD {n : Nat} :
    ∀ (gens : List (BitVec n)) (mask : List Bool) (q : Nat),
      (xorSubset gens mask).getLsbD q =
        (List.zip gens mask).foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) false
  | [], _, _ => by simp [xorSubset]
  | _ :: _, [], _ => by simp [xorSubset]
  | g :: gs, b :: bs, q => by
    simp only [xorSubset, BitVec.getLsbD_xor, List.zip_cons_cons, List.foldl_cons]
    have hfold_xor : ∀ (xs : List (BitVec n × Bool)) (a : Bool),
        xs.foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) a =
        xor a (xs.foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) false) := by
      intro xs; induction xs with
      | nil => intro a; cases a <;> rfl
      | cons pr xs ih =>
        intro a; simp only [List.foldl_cons]
        cases pr.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact ih a
        · rw [ih, ih (xor false (pr.1.getLsbD q))]
          cases a <;> cases pr.1.getLsbD q <;> cases (xs.foldl (fun acc p => if p.2 then xor acc (p.1.getLsbD q) else acc) false) <;> rfl
    rw [xorSubset_getLsbD gs bs q]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · simp
    · rw [hfold_xor (gs.zip bs) (xor false (g.getLsbD q))]
      cases g.getLsbD q <;> rfl

/-! ## 2. Weight-1 Puncturing & X/Z Symmetry -/

private theorem isCSSCode_swap {n k d w : Nat} {hx hz lx lz : List (BitVec n)}
    (h : IsCSSCode n k d w hx hz lx lz) : IsCSSCode n k d w hz hx lz lx := by
  obtain ⟨hlx, hlz, hcomm, hwx, hwz, hlxhz, hlzhx, hsymp, hdx, hdz⟩ := h
  refine ⟨hlz, hlx, fun z hz x hx => by rw [commutes_symm]; exact hcomm x hx z hz,
          hwz, hwx, hlzhx, hlxhz, fun i j => ?_, hdz, hdx⟩
  rw [commutes_symm, hsymp j i]
  by_cases hij : i.val = j.val
  · simp [hij]
  · have hji : j.val ≠ i.val := fun he => hij he.symm
    simp [hij, hji]

private def dropBit {n : Nat} (q : Nat) (v : BitVec (n + 1)) : BitVec n :=
  mkBitVec n fun j => v.getLsbD (if j < q then j else j + 1)

private def liftBit {n : Nat} (q : Nat) (v : BitVec n) : BitVec (n + 1) :=
  mkBitVec (n + 1) fun i => if i = q then false else v.getLsbD (if i < q then i else i - 1)

private theorem dropBit_getLsbD {n : Nat} (q : Nat) (v : BitVec (n + 1)) {j : Nat} (hj : j < n) :
    (dropBit q v).getLsbD j = v.getLsbD (if j < q then j else j + 1) :=
  mkBitVec_getLsbD n _ hj

private theorem liftBit_getLsbD {n : Nat} (q : Nat) (v : BitVec n) {i : Nat} (hi : i < n + 1) :
    (liftBit q v).getLsbD i = if i = q then false else v.getLsbD (if i < q then i else i - 1) :=
  mkBitVec_getLsbD (n + 1) _ hi

private theorem dropBit_liftBit {n : Nat} {q : Nat} (v : BitVec n) :
    dropBit q (liftBit q v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [dropBit_getLsbD q _ hj]
  by_cases hlt : j < q
  · simp only [hlt, ↓reduceIte]
    rw [liftBit_getLsbD q v (by omega)]
    have hne : j ≠ q := by omega
    simp [hne, hlt]
  · simp only [hlt, ↓reduceIte]
    rw [liftBit_getLsbD q v (by omega)]
    have hne : j + 1 ≠ q := by omega
    have hnot : ¬ (j + 1 < q) := by omega
    simp [hne, hnot]

private theorem dropBit_xor {n : Nat} (q : Nat) (a b : BitVec (n + 1)) :
    dropBit q (a ^^^ b) = dropBit q a ^^^ dropBit q b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_xor, dropBit_getLsbD q _ hj, dropBit_getLsbD q _ hj, dropBit_getLsbD q _ hj, BitVec.getLsbD_xor]

private theorem dropBit_zero {n : Nat} (q : Nat) : dropBit q (0 : BitVec (n + 1)) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; rw [dropBit_getLsbD q _ hj]; simp

private theorem dropBit_and {n : Nat} (q : Nat) (a b : BitVec (n + 1)) :
    dropBit q (a &&& b) = dropBit q a &&& dropBit q b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, dropBit_getLsbD q _ hj, dropBit_getLsbD q _ hj, dropBit_getLsbD q _ hj, BitVec.getLsbD_and]

private theorem liftBit_and_eq_liftBit_dropBit {n : Nat} {q : Nat} (hq : q < n + 1)
    (e' : BitVec n) (x : BitVec (n + 1)) :
    liftBit q e' &&& x = liftBit q (e' &&& dropBit q x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, liftBit_getLsbD q _ hi, liftBit_getLsbD q _ hi]
  by_cases hiq : i = q
  · simp [hiq]
  · simp only [hiq, ↓reduceIte, BitVec.getLsbD_and]
    by_cases hlt : i < q
    · simp only [hlt, ↓reduceIte]
      rw [dropBit_getLsbD q x (by omega)]
      simp [hlt]
    · simp only [hlt, ↓reduceIte]
      rw [dropBit_getLsbD q x (by omega)]
      have hnot : ¬ (i - 1 < q) := by omega
      have hadd : i - 1 + 1 = i := by omega
      simp [hnot, hadd]

private theorem hammingWeight_split_q {n : Nat} {q : Nat} (hq : q < n + 1) (v : BitVec (n + 1)) :
    hammingWeight v = hammingWeight (dropBit q v) + (if v.getLsbD q then 1 else 0) := by
  rw [hammingWeight_eq_filter, hammingWeight_eq_filter]
  have h1 : ((List.range n).filter (fun j => (dropBit q v).getLsbD j)).length =
      ((List.range n).filter (fun j => v.getLsbD (if j < q then j else j + 1))).length := by
    congr 1; apply List.filter_congr; intro j hj
    exact dropBit_getLsbD q v (List.mem_range.mp hj)
  rw [h1]
  have hrange_split : ∀ (a b : Nat) (f : Nat → Bool),
      ((List.range (a + b)).filter f).length =
      ((List.range a).filter f).length + ((List.range b).filter (fun j => f (a + j))).length := by
    intro a b f; induction b with
    | zero => simp
    | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, List.range_succ, List.filter_append, List.length_append, ih,
          List.range_succ, List.filter_append, List.length_append]
      simp only [List.filter_cons, List.filter_nil]
      cases f (a + b) <;> simp <;> omega
  have hlen1 : List.range (n + 1) = List.range (q + (1 + (n - q))) := by congr 1; omega
  have hlen2 : List.range n = List.range (q + (n - q)) := by congr 1; omega
  have hL : ((List.range (n + 1)).filter (fun i => v.getLsbD i)).length =
      ((List.range q).filter (fun i => v.getLsbD i)).length +
      ((List.range 1).filter (fun j => v.getLsbD (q + j))).length +
      ((List.range (n - q)).filter (fun j => v.getLsbD (q + (1 + j)))).length := by
    rw [hlen1, hrange_split q (1 + (n - q)), hrange_split 1 (n - q)]
    omega
  have hR : ((List.range n).filter (fun j => v.getLsbD (if j < q then j else j + 1))).length =
      ((List.range q).filter (fun j => v.getLsbD (if j < q then j else j + 1))).length +
      ((List.range (n - q)).filter (fun j => v.getLsbD (if q + j < q then q + j else q + j + 1))).length := by
    rw [hlen2, hrange_split q (n - q)]
  have hleft : ((List.range q).filter (fun j => v.getLsbD (if j < q then j else j + 1))).length =
      ((List.range q).filter (fun j => v.getLsbD j)).length := by
    congr 1; apply List.filter_congr; intro j hj
    have : j < q := List.mem_range.mp hj
    simp [this]
  have hright : ((List.range (n - q)).filter (fun j => v.getLsbD (if q + j < q then q + j else q + j + 1))).length =
      ((List.range (n - q)).filter (fun j => v.getLsbD (q + (1 + j)))).length := by
    congr 1; apply List.filter_congr; intro j _
    have hnot : ¬ (q + j < q) := by omega
    have heq : q + j + 1 = q + (1 + j) := by omega
    simp [hnot, heq]
  have hmid : ((List.range 1).filter (fun j => v.getLsbD (q + j))).length = if v.getLsbD q then 1 else 0 := by
    rw [show List.range 1 = [0] from rfl]
    cases hb : v.getLsbD q <;> simp [hb]
  rw [hL, hR, hleft, hright, hmid]
  omega

private theorem hammingWeight_dropBit_le {n : Nat} {q : Nat} (hq : q < n + 1) (v : BitVec (n + 1)) :
    hammingWeight (dropBit q v) ≤ hammingWeight v := by
  rw [hammingWeight_split_q hq v]; omega

private theorem hammingWeight_liftBit {n : Nat} {q : Nat} (hq : q < n + 1) (v : BitVec n) :
    hammingWeight (liftBit q v) = hammingWeight v := by
  rw [hammingWeight_split_q hq, dropBit_liftBit, liftBit_getLsbD q v hq]
  simp

private theorem commutes_dropBit_of_bit_false {n : Nat} {q : Nat} (hq : q < n + 1)
    (u v : BitVec (n + 1)) (hvq : v.getLsbD q = false) :
    commutes (dropBit q u) (dropBit q v) = commutes u v := by
  unfold commutes
  rw [← dropBit_and, hammingWeight_split_q hq (u &&& v), BitVec.getLsbD_and, hvq, Bool.and_false]
  simp

private theorem commutes_liftBit {n : Nat} {q : Nat} (hq : q < n + 1)
    (e' : BitVec n) (x : BitVec (n + 1)) :
    commutes (liftBit q e') x = commutes e' (dropBit q x) := by
  unfold commutes
  rw [liftBit_and_eq_liftBit_dropBit hq, hammingWeight_liftBit hq]

private theorem xorSubset_map_dropBit {n : Nat} (q : Nat) :
    ∀ (gens : List (BitVec (n + 1))) (mask : List Bool),
      xorSubset (gens.map (dropBit q)) mask = dropBit q (xorSubset gens mask)
  | [], _ => (dropBit_zero q).symm
  | _ :: _, [] => (dropBit_zero q).symm
  | g :: gs, b :: bs => by
    simp only [List.map_cons, xorSubset]
    rw [dropBit_xor, xorSubset_map_dropBit q gs bs]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, dropBit_zero]
    · rfl

private theorem inRowSpace_dropBit {n : Nat} (q : Nat) {gens : List (BitVec (n + 1))} {v : BitVec (n + 1)}
    (h : InRowSpace gens v) : InRowSpace (gens.map (dropBit q)) (dropBit q v) := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨m, by simp [hm], xorSubset_map_dropBit q gens m⟩

private theorem puncture_of_wt1_x {n k : Nat} {hx hz lx lz : List (BitVec (n + 1))}
    (hcss : IsCSSCode (n + 1) k 3 4 hx hz lx lz)
    {q : Nat} (hq : q < n + 1) (hwt1 : InRowSpace hx (unitVec (n + 1) q)) :
    IsCSSCode n k 3 4 (hx.map (dropBit q)) (hz.map (dropBit q)) (lx.map (dropBit q)) (lz.map (dropBit q)) := by
  obtain ⟨hlx, hlz, hcomm, hwx, hwz, hlxhz, hlzhx, hsymp, hdx, hdz⟩ := hcss
  have hz_false : ∀ z ∈ hz, z.getLsbD q = false := by
    intro z hzMem
    have hc := commutes_inRowSpace hwt1 (fun x hxMem => hcomm x hxMem z hzMem)
    rw [commutes_unitVec hq] at hc
    cases hb : z.getLsbD q <;> simp [hb] at hc ⊢
  have hlz_false : ∀ z ∈ lz, z.getLsbD q = false := by
    intro z hzMem
    have hc := commutes_inRowSpace hwt1 (fun x hxMem => by rw [commutes_symm]; exact hlzhx z hzMem x hxMem)
    rw [commutes_unitVec hq] at hc
    cases hb : z.getLsbD q <;> simp [hb] at hc ⊢
  refine ⟨by simp [hlx], by simp [hlz], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x' hx' z' hz'
    obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp hz'
    rw [commutes_dropBit_of_bit_false hq x z (hz_false z hzMem)]
    exact hcomm x hxMem z hzMem
  · intro x' hx'
    obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hx'
    exact Nat.le_trans (hammingWeight_dropBit_le hq x) (hwx x hxMem)
  · intro z' hz'
    obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp hz'
    exact Nat.le_trans (hammingWeight_dropBit_le hq z) (hwz z hzMem)
  · intro x' hx' z' hz'
    obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp hz'
    rw [commutes_dropBit_of_bit_false hq x z (hz_false z hzMem)]
    exact hlxhz x hxMem z hzMem
  · intro z' hz' x' hx'
    obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp hz'
    obtain ⟨x, hxMem, rfl⟩ := List.mem_map.mp hx'
    rw [commutes_symm, commutes_dropBit_of_bit_false hq x z (hlz_false z hzMem), commutes_symm]
    exact hlzhx z hzMem x hxMem
  · intro i j
    have hi : i.val < lx.length := by omega
    have hj : j.val < lz.length := by omega
    have hgx : (lx.map (dropBit q)).getD i.val 0 = dropBit q (lx.getD i.val 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hi]
    have hgz : (lz.map (dropBit q)).getD j.val 0 = dropBit q (lz.getD j.val 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hj]
    have hzj_mem : lz.getD j.val 0 ∈ lz := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [hgx, hgz, commutes_dropBit_of_bit_false hq _ _ (hlz_false _ hzj_mem)]
    exact hsymp i j
  · intro e' hpos hlt hce
    have he := hdx (liftBit q e') (by rw [hammingWeight_liftBit hq]; exact hpos)
      (by rw [hammingWeight_liftBit hq]; exact hlt)
      (fun z hzMem => by rw [commutes_liftBit hq]; exact hce (dropBit q z) (List.mem_map.mpr ⟨z, hzMem, rfl⟩))
    simpa [dropBit_liftBit] using inRowSpace_dropBit q he
  · intro e' hpos hlt hce
    have he := hdz (liftBit q e') (by rw [hammingWeight_liftBit hq]; exact hpos)
      (by rw [hammingWeight_liftBit hq]; exact hlt)
      (fun x hxMem => by rw [commutes_liftBit hq]; exact hce (dropBit q x) (List.mem_map.mpr ⟨x, hxMem, rfl⟩))
    simpa [dropBit_liftBit] using inRowSpace_dropBit q he

/-! ## 3. GF(2) Linear Independence, Basis Extraction, and Dual-Vector Rank Bound -/

private def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allMasks k).map (false :: ·) ++ (allMasks k).map (true :: ·)

private theorem allMasks_length : ∀ k, (allMasks k).length = 2 ^ k
  | 0 => rfl
  | k + 1 => by simp [allMasks, allMasks_length k, Nat.pow_succ]; omega

private theorem allMasks_mem_iff : ∀ k (m : List Bool), m ∈ allMasks k ↔ m.length = k
  | 0, m => by cases m <;> simp [allMasks]
  | k + 1, m => by
    cases m with
    | nil => simp [allMasks]
    | cons b bs =>
      simp only [allMasks, List.mem_append, List.mem_map, List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff]
      cases b
      · simp [allMasks_mem_iff k]
      · simp [allMasks_mem_iff k]

private theorem allMasks_nodup : ∀ k, (allMasks k).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | k + 1 => by
    have ih := allMasks_nodup k
    have h1 : ((allMasks k).map (false :: ·)).Nodup :=
      nodup_map_of_inj ih (fun a _ b _ h => by injection h)
    have h2 : ((allMasks k).map (true :: ·)).Nodup :=
      nodup_map_of_inj ih (fun a _ b _ h => by injection h)
    refine List.nodup_append.mpr ⟨h1, h2, ?_⟩
    intro x hx1 y hy2 heq
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx1
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy2
    cases heq

private def allBitVecs (n : Nat) : List (BitVec n) :=
  (List.range (2 ^ n)).map (BitVec.ofNat n)

private theorem allBitVecs_mem {n : Nat} (v : BitVec n) : v ∈ allBitVecs n := by
  unfold allBitVecs
  refine List.mem_map.mpr ⟨v.toNat, List.mem_range.mpr v.isLt, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]

private theorem allBitVecs_length (n : Nat) : (allBitVecs n).length = 2 ^ n := by
  simp [allBitVecs]

private def LinIndep {n : Nat} (xs : List (BitVec n)) : Prop :=
  ∀ m : List Bool, m.length = xs.length → xorSubset xs m = 0 → m = List.replicate xs.length false

private theorem xorSubset_eq_iff_zipWith {n : Nat} {xs : List (BitVec n)} {m1 m2 : List Bool}
    (h1 : m1.length = xs.length) (h2 : m2.length = xs.length) :
    xorSubset xs m1 = xorSubset xs m2 ↔ xorSubset xs (List.zipWith Bool.xor m1 m2) = 0 := by
  rw [xorSubset_zipWith_xor xs m1 m2 h1 h2]
  constructor
  · intro h; rw [h]; apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro j _
    have hbit := congrArg (fun v : BitVec n => v.getLsbD j) h
    have hz0 : (0 : BitVec n).getLsbD j = false := by simp
    rw [BitVec.getLsbD_xor, hz0] at hbit
    cases h1b : (xorSubset xs m1).getLsbD j <;> cases h2b : (xorSubset xs m2).getLsbD j <;>
      rw [h1b, h2b] at hbit <;> first | rfl | cases hbit

private theorem zipWith_xor_eq_replicate_false :
    ∀ {m1 m2 : List Bool}, m1.length = m2.length →
      List.zipWith Bool.xor m1 m2 = List.replicate m1.length false → m1 = m2
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hlen, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.zipWith_cons_cons, List.length_cons, List.replicate_succ, List.cons.injEq] at h
    have hab : a = b := by cases a <;> cases b <;> simp at h ⊢
    rw [hab, zipWith_xor_eq_replicate_false hlen h.2]

private theorem linIndep_inj {n : Nat} {xs : List (BitVec n)} (hli : LinIndep xs)
    {m1 m2 : List Bool} (h1 : m1.length = xs.length) (h2 : m2.length = xs.length)
    (heq : xorSubset xs m1 = xorSubset xs m2) : m1 = m2 := by
  have hz := (xorSubset_eq_iff_zipWith h1 h2).mp heq
  have hrep := hli (List.zipWith Bool.xor m1 m2) (by simp [h1, h2]) hz
  rw [show xs.length = m1.length from h1.symm] at hrep
  exact zipWith_xor_eq_replicate_false (by omega) hrep

private theorem linIndep_le_of_subset {n : Nat} {A B : List (BitVec n)}
    (hli : LinIndep A) (hsub : ∀ a ∈ A, InRowSpace B a) : A.length ≤ B.length := by
  have hall : ∀ m ∈ allMasks A.length, InRowSpace B (xorSubset A m) := by
    intro m hm
    have hmlen : m.length = A.length := (allMasks_mem_iff A.length m).mp hm
    clear hm
    have hgen : ∀ (xs : List (BitVec n)) (ms : List Bool),
        (∀ x ∈ xs, InRowSpace B x) → ms.length = xs.length → InRowSpace B (xorSubset xs ms) := by
      intro xs; induction xs with
      | nil => intro _ _ _; exact inRowSpace_zero B
      | cons a as ih =>
        intro ms hs hml
        cases ms with
        | nil => simp at hml
        | cons b bs =>
          simp only [xorSubset]
          apply inRowSpace_xor
          · cases b
            · exact inRowSpace_zero B
            · exact hs a (List.mem_cons_self ..)
          · exact ih bs (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (by simpa using hml)
    exact hgen A m hsub hmlen
  have hnd : ((allMasks A.length).map (xorSubset A)).Nodup :=
    nodup_map_of_inj (allMasks_nodup A.length) (fun m1 hm1 m2 hm2 heq =>
      linIndep_inj hli ((allMasks_mem_iff _ _).mp hm1) ((allMasks_mem_iff _ _).mp hm2) heq)
  have hinc : ∀ v ∈ (allMasks A.length).map (xorSubset A), v ∈ (allMasks B.length).map (xorSubset B) := by
    intro v hv
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨mb, hmb, hbeq⟩ := hall m hm
    exact List.mem_map.mpr ⟨mb, (allMasks_mem_iff B.length mb).mpr hmb, hbeq⟩
  have hcard := nodup_length_le_of_subset hnd hinc
  rw [List.length_map, allMasks_length, List.length_map, allMasks_length] at hcard
  exact pow2_le_imp_le hcard

private theorem linIndep_cons {n : Nat} {b : BitVec n} {bs : List (BitVec n)}
    (hli : LinIndep bs) (hnot : ¬ InRowSpace bs b) : LinIndep (b :: bs) := by
  intro m hmlen hz
  cases m with
  | nil => simp at hmlen
  | cons a as =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hmlen
    simp only [xorSubset] at hz
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte] at hz
      have hz' : xorSubset bs as = 0 := by simpa using hz
      have has := hli as hmlen hz'
      rw [has]; rfl
    · simp only [↓reduceIte] at hz
      exfalso; apply hnot
      refine ⟨as, hmlen, ?_⟩
      apply BitVec.eq_of_getLsbD_eq; intro j _
      have hbit := congrArg (fun v : BitVec n => v.getLsbD j) hz
      have hz0 : (0 : BitVec n).getLsbD j = false := by simp
      rw [BitVec.getLsbD_xor, hz0] at hbit
      cases hb1 : b.getLsbD j <;> cases hb2 : (xorSubset bs as).getLsbD j <;>
        rw [hb1, hb2] at hbit <;> first | rfl | cases hbit

private theorem inRowSpace_cons_of_mem {n : Nat} {g : BitVec n} {gs : List (BitVec n)} {v : BitVec n}
    (hv : InRowSpace gs v) : InRowSpace (g :: gs) v := by
  obtain ⟨m, hm, rfl⟩ := hv
  exact ⟨false :: m, by simp [hm], by simp [xorSubset]⟩

private theorem inRowSpace_self {n : Nat} (g : BitVec n) (gs : List (BitVec n)) :
    InRowSpace (g :: gs) g := by
  refine ⟨true :: List.replicate gs.length false, by simp, ?_⟩
  simp [xorSubset, xorSubset_false]

private theorem inRowSpace_mem {n : Nat} {gens : List (BitVec n)} {g : BitVec n} (hg : g ∈ gens) :
    InRowSpace gens g := by
  induction gens with
  | nil => cases hg
  | cons a as ih =>
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact inRowSpace_self _ as
    · exact inRowSpace_cons_of_mem (ih hg')

private theorem inRowSpace_mono {n : Nat} {A B : List (BitVec n)}
    (hsub : ∀ a ∈ A, InRowSpace B a) {v : BitVec n} (hv : InRowSpace A v) : InRowSpace B v := by
  obtain ⟨m, hm, rfl⟩ := hv
  have hgen : ∀ (xs : List (BitVec n)) (ms : List Bool),
      (∀ x ∈ xs, InRowSpace B x) → ms.length = xs.length → InRowSpace B (xorSubset xs ms) := by
    intro xs; induction xs with
    | nil => intro _ _ _; exact inRowSpace_zero B
    | cons a as ih =>
      intro ms hs hml
      cases ms with
      | nil => simp at hml
      | cons b bs =>
        simp only [xorSubset]
        apply inRowSpace_xor
        · cases b
          · exact inRowSpace_zero B
          · exact hs a (List.mem_cons_self ..)
        · exact ih bs (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (by simpa using hml)
  exact hgen A m hsub hm

private theorem exists_extend_basis {n : Nat} (base extra : List (BitVec n)) (hli : LinIndep base) :
    ∃ ext : List (BitVec n),
      (∀ x ∈ ext, x ∈ extra) ∧
      LinIndep (ext ++ base) ∧
      (∀ v, InRowSpace (ext ++ base) v ↔ InRowSpace (extra ++ base) v) := by
  induction extra with
  | nil => exact ⟨[], fun _ h => h, hli, fun _ => Iff.rfl⟩
  | cons e es ih =>
    obtain ⟨ext, hmem, hli', hspan⟩ := ih
    by_cases hin : InRowSpace (ext ++ base) e
    · refine ⟨ext, fun x hx => List.mem_cons_of_mem _ (hmem x hx), hli', fun v => ?_⟩
      constructor
      · intro hv
        have := (hspan v).mp hv
        exact inRowSpace_cons_of_mem this
      · intro hv
        apply (hspan v).mpr
        apply inRowSpace_mono (A := e :: (es ++ base)) _ hv
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact (hspan _).mp hin
        · exact inRowSpace_mem ha'
    · refine ⟨e :: ext, ?_, linIndep_cons hli' hin, fun v => ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hmem x hx')
      · constructor
        · intro hv
          apply inRowSpace_mono (A := e :: (ext ++ base)) _ hv
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact inRowSpace_self _ _
          · exact inRowSpace_cons_of_mem ((hspan a).mp (inRowSpace_mem ha'))
        · intro hv
          apply inRowSpace_mono (A := e :: (es ++ base)) _ hv
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact inRowSpace_self _ _
          · exact inRowSpace_cons_of_mem ((hspan a).mpr (inRowSpace_mem ha'))

private theorem exists_basis {n : Nat} (gens : List (BitVec n)) :
    ∃ B : List (BitVec n), (∀ x ∈ B, x ∈ gens) ∧ LinIndep B ∧ (∀ v, InRowSpace B v ↔ InRowSpace gens v) := by
  have hli0 : LinIndep ([] : List (BitVec n)) := fun m hm _ => by
    cases m with
    | nil => rfl
    | cons _ _ => simp at hm
  obtain ⟨ext, hmem, hli, hspan⟩ := exists_extend_basis [] gens hli0
  rw [List.append_nil] at hli
  exact ⟨ext, hmem, hli, fun v => by have := hspan v; rw [List.append_nil, List.append_nil] at this; exact this⟩

private theorem exists_set_bit_of_ne_zero {n : Nat} {v : BitVec n} (hne : v ≠ 0) :
    ∃ p < n, v.getLsbD p = true := by
  apply Classical.byContradiction
  intro hno; apply hne
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hz0 : (0 : BitVec n).getLsbD j = false := by simp
  rw [hz0]
  cases hb : v.getLsbD j
  · rfl
  · exact absurd ⟨j, hj, hb⟩ hno

private theorem xorSubset_append {n : Nat} :
    ∀ (xs ys : List (BitVec n)) (mx my : List Bool),
      mx.length = xs.length →
      xorSubset (xs ++ ys) (mx ++ my) = xorSubset xs mx ^^^ xorSubset ys my
  | [], ys, [], my, _ => by
    simp only [List.nil_append, xorSubset]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  | x :: xs, ys, b :: mx, my, h => by
    simp only [List.cons_append, xorSubset]
    rw [xorSubset_append xs ys mx my (by simpa using h)]
    apply BitVec.eq_of_getLsbD_eq; intro j _
    simp only [BitVec.getLsbD_xor]
    cases (if b then x else 0).getLsbD j <;> cases (xorSubset xs mx).getLsbD j <;> cases (xorSubset ys my).getLsbD j <;> rfl
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

private theorem commutes_xorSubset_dual {n : Nat} :
    ∀ (xs ds : List (BitVec n)) (m : List Bool) (i : Nat)
      (hdl : ds.length = xs.length) (_ : m.length = xs.length) (hi : i < xs.length),
      (∀ a (ha : a < xs.length) b (hb : b < xs.length),
        commutes xs[a] (ds[b]'(by omega)) = decide (a ≠ b)) →
      commutes xs[i] (xorSubset ds m) = !(m.getD i false) := by
  intro xs; induction xs with
  | nil => intro _ _ i _ _ hi; simp at hi
  | cons x xs ih =>
    intro ds m i hdl hml hi hpair
    cases ds with
    | nil => simp at hdl
    | cons d ds =>
      cases m with
      | nil => simp at hml
      | cons b bs =>
        have hdl' : ds.length = xs.length := by simpa using hdl
        have hml' : bs.length = xs.length := by simpa using hml
        simp only [xorSubset]
        rw [commutes_xor_right]
        cases i with
        | zero =>
          have hrest : commutes x (xorSubset ds bs) = true := by
            rw [commutes_symm]
            apply commutes_xorSubset_left
            intro d' hd'
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
            rw [commutes_symm]
            have := hpair 0 (by simp) (j + 1) (by simp; omega)
            simpa using this
          have h0 : commutes x d = false := by
            have := hpair 0 (by simp) 0 (by simp)
            simpa using this
          have hz0 : commutes x 0 = true := by rw [commutes_symm]; exact commutes_zero_left x
          simp only [List.getElem_cons_zero, hrest, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, beq_true]; exact hz0
          · simp [h0]
        | succ i =>
          have hi' : i < xs.length := by simp at hi; omega
          have h0 : commutes xs[i] d = true := by
            have := hpair (i + 1) (by simp; omega) 0 (by simp)
            simpa using this
          have hfirst : commutes xs[i] (if b then d else 0) = true := by
            cases b
            · rw [commutes_symm]; exact commutes_zero_left _
            · exact h0
          have hih := ih ds bs i hdl' hml' hi' (fun a ha b' hb' => by
            have := hpair (a + 1) (by simp; omega) (b' + 1) (by simp; omega)
            simpa using this)
          simp only [List.getElem_cons_succ, hfirst, hih, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
          cases bs[i]?.getD false <;> rfl

private theorem exists_dual_vectors {n : Nat} (xs : List (BitVec n)) (hli : LinIndep xs) :
    ∃ ds : List (BitVec n), ∃ hlen : ds.length = xs.length,
      ∀ i (hi : i < xs.length) j (hj : j < xs.length),
        commutes xs[i] (ds[j]'(by omega)) = decide (i ≠ j) := by
  induction xs with
  | nil => exact ⟨[], rfl, fun i hi => by simp at hi⟩
  | cons x xs ih =>
    have hli' : LinIndep xs := by
      intro m hml hz
      have h := hli (false :: m) (by simp [hml]) (by simpa [xorSubset] using hz)
      rw [List.length_cons, List.replicate_succ] at h
      exact (List.cons.inj h).2
    have hnot : ¬ InRowSpace xs x := by
      intro ⟨m, hml, hmeq⟩
      have hz : xorSubset (x :: xs) (true :: m) = 0 := by
        simp only [xorSubset, ↓reduceIte, hmeq]
        apply BitVec.eq_of_getLsbD_eq; intro j _; simp
      have h := hli (true :: m) (by simp [hml]) hz
      rw [List.length_cons, List.replicate_succ] at h
      cases h
    obtain ⟨ds, hdl, hpair⟩ := ih hli'
    let mx : List Bool := ds.map (fun d => !(commutes x d))
    have hmx_len : mx.length = xs.length := by simp [mx, hdl]
    let x' : BitVec n := x ^^^ xorSubset xs mx
    have hx'_ne0 : x' ≠ 0 := by
      intro hz; apply hnot
      refine ⟨mx, hmx_len, ?_⟩
      apply BitVec.eq_of_getLsbD_eq; intro j _
      have hbit := congrArg (fun v : BitVec n => v.getLsbD j) hz
      have hz0 : (0 : BitVec n).getLsbD j = false := by simp
      dsimp only [x'] at hbit
      rw [BitVec.getLsbD_xor, hz0] at hbit
      cases hb1 : x.getLsbD j <;> cases hb2 : (xorSubset xs mx).getLsbD j <;>
        rw [hb1, hb2] at hbit <;> first | rfl | cases hbit
    have hx'_comm : ∀ j (hj : j < xs.length), commutes x' (ds[j]'(by omega)) = true := by
      intro j hj
      dsimp only [x']
      rw [commutes_xor_left, commutes_symm (xorSubset xs mx)]
      have hxs_d : commutes (ds[j]'(by omega)) (xorSubset xs mx) = !(mx.getD j false) := by
        have hsym : ∀ a (ha : a < ds.length) b (hb : b < ds.length),
            commutes ds[a] (xs[b]'(by omega)) = decide (a ≠ b) := fun a ha b hb => by
          rw [commutes_symm, hpair b (by omega) a (by omega)]
          by_cases hab : a = b
          · simp [hab]
          · have hba : b ≠ a := fun h => hab h.symm
            simp [hab, hba]
        have := commutes_xorSubset_dual ds xs mx j hdl.symm (by omega) (by omega) hsym
        simpa using this
      rw [hxs_d]
      have hmxj : mx.getD j false = !(commutes x (ds[j]'(by omega))) := by
        have hlt : j < mx.length := by omega
        simp [mx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, hlt]
      rw [hmxj]
      cases commutes x (ds[j]'(by omega)) <;> rfl
    obtain ⟨p, hp, hxp⟩ := exists_set_bit_of_ne_zero hx'_ne0
    let ep := unitVec n p
    have hep_x' : commutes x' ep = false := by
      rw [commutes_symm, commutes_unitVec hp, hxp]; rfl
    let me : List Bool := xs.map (fun a => !(commutes a ep))
    have hme_len : me.length = xs.length := by simp [me]
    let d0 : BitVec n := ep ^^^ xorSubset ds me
    have hd0_xs : ∀ i (hi : i < xs.length), commutes xs[i] d0 = true := by
      intro i hi
      dsimp only [d0]
      rw [commutes_xor_right, commutes_xorSubset_dual xs ds me i hdl hme_len hi (fun a ha b hb => hpair a ha b hb)]
      have hmei : me.getD i false = !(commutes xs[i] ep) := by
        have hlt : i < me.length := by omega
        simp [me, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, hlt]
      rw [hmei]
      cases commutes xs[i] ep <;> rfl
    have hd0_x' : commutes x' d0 = false := by
      dsimp only [d0]
      rw [commutes_xor_right, hep_x']
      have hcomm_ds : commutes x' (xorSubset ds me) = true := by
        rw [commutes_symm]
        apply commutes_xorSubset_left
        intro d' hd'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd'
        rw [commutes_symm]
        exact hx'_comm j (by omega)
      rw [hcomm_ds]; rfl
    have hd0_x : commutes x d0 = false := by
      have hxs_d0 : commutes (xorSubset xs mx) d0 = true :=
        commutes_xorSubset_left xs mx d0 (fun a ha => by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
          exact hd0_xs i hi)
      have := hd0_x'
      dsimp only [x'] at this
      rw [commutes_xor_left, hxs_d0] at this
      cases hb : commutes x d0 <;> simp [hb] at this ⊢
    let ds' : List (BitVec n) := d0 :: ds.map (fun d => if commutes x d then d else d ^^^ d0)
    refine ⟨ds', by simp [ds', hdl], ?_⟩
    intro i hi j hj
    cases i with
    | zero =>
      cases j with
      | zero => simpa [ds'] using hd0_x
      | succ j =>
        have hj' : j < ds.length := by simp at hj; omega
        simp only [ds', List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_map]
        cases hcd : commutes x ds[j]
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [commutes_xor_right, hcd, hd0_x]; rfl
        · simp [hcd]
    | succ i =>
      have hi' : i < xs.length := by simp at hi; omega
      cases j with
      | zero =>
        simpa [ds'] using hd0_xs i hi'
      | succ j =>
        have hj' : j < ds.length := by simp at hj; omega
        simp only [ds', List.getElem_cons_succ, List.getElem_map]
        have hpij := hpair i hi' j (by omega)
        have hdec : decide (i + 1 ≠ j + 1) = decide (i ≠ j) := by
          by_cases hij : i = j <;> simp [hij]
        rw [hdec]
        cases hcd : commutes x ds[j]
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [commutes_xor_right, hd0_xs i hi', hpij]
          cases decide (i ≠ j) <;> rfl
        · simp [hpij]

private theorem rank_orth_bound {n : Nat} {A B : List (BitVec n)}
    (hA : LinIndep A) (hB : LinIndep B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, commutes a b = true) :
    A.length + B.length ≤ n := by
  obtain ⟨ds, hdl, hpair⟩ := exists_dual_vectors B hB
  let f : List Bool → BitVec n := fun m =>
    xorSubset A (m.take A.length) ^^^ xorSubset ds (m.drop A.length)
  have hf_inj : ∀ m1 ∈ allMasks (A.length + B.length), ∀ m2 ∈ allMasks (A.length + B.length),
      f m1 = f m2 → m1 = m2 := by
    intro m1 hm1 m2 hm2 heq
    have hl1 : m1.length = A.length + B.length := (allMasks_mem_iff _ _).mp hm1
    have hl2 : m2.length = A.length + B.length := (allMasks_mem_iff _ _).mp hm2
    have ht1 : (m1.take A.length).length = A.length := by simp [hl1]
    have ht2 : (m2.take A.length).length = A.length := by simp [hl2]
    have hd1 : (m1.drop A.length).length = B.length := by simp [hl1]
    have hd2 : (m2.drop A.length).length = B.length := by simp [hl2]
    have hdrop_eq : m1.drop A.length = m2.drop A.length := by
      apply List.ext_getElem (by omega)
      intro i hi1 hi2
      have hiB : i < B.length := by omega
      have hc := congrArg (fun v => commutes B[i] v) heq
      dsimp only [f] at hc
      rw [commutes_xor_right, commutes_xor_right] at hc
      have hA1 : commutes B[i] (xorSubset A (m1.take A.length)) = true := by
        rw [commutes_symm]; exact commutes_xorSubset_left A _ _ (fun a ha => horth a ha B[i] (List.getElem_mem hiB))
      have hA2 : commutes B[i] (xorSubset A (m2.take A.length)) = true := by
        rw [commutes_symm]; exact commutes_xorSubset_left A _ _ (fun a ha => horth a ha B[i] (List.getElem_mem hiB))
      rw [hA1, hA2, commutes_xorSubset_dual B ds (m1.drop A.length) i hdl hd1 hiB (fun a ha b hb => hpair a ha b hb),
          commutes_xorSubset_dual B ds (m2.drop A.length) i hdl hd2 hiB (fun a ha b hb => hpair a ha b hb)] at hc
      have hg1 : (m1.drop A.length).getD i false = (m1.drop A.length)[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
      have hg2 : (m2.drop A.length).getD i false = (m2.drop A.length)[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
      rw [hg1, hg2] at hc
      cases h1 : (m1.drop A.length)[i] <;> cases h2 : (m2.drop A.length)[i] <;>
        rw [h1, h2] at hc <;> first | rfl | cases hc
    have htake_eq : m1.take A.length = m2.take A.length := by
      apply linIndep_inj hA ht1 ht2
      dsimp only [f] at heq
      rw [hdrop_eq] at heq
      apply BitVec.eq_of_getLsbD_eq; intro j _
      have hbit := congrArg (fun v : BitVec n => v.getLsbD j) heq
      simp only [BitVec.getLsbD_xor] at hbit
      cases hb1 : (xorSubset A (m1.take A.length)).getLsbD j <;>
        cases hb2 : (xorSubset A (m2.take A.length)).getLsbD j <;>
        cases hb3 : (xorSubset ds (m2.drop A.length)).getLsbD j <;>
        rw [hb1, hb2, hb3] at hbit <;> first | rfl | cases hbit
    rw [← List.take_append_drop A.length m1, ← List.take_append_drop A.length m2, htake_eq, hdrop_eq]
  have hnd : ((allMasks (A.length + B.length)).map f).Nodup :=
    nodup_map_of_inj (allMasks_nodup _) hf_inj
  have hle := nodup_length_le_of_subset hnd (fun v _ => allBitVecs_mem v)
  rw [List.length_map, allMasks_length, allBitVecs_length] at hle
  exact pow2_le_imp_le hle

private theorem linIndep_append_logical {n k : Nat} {Bx lx lz : List (BitVec n)}
    (hBx : LinIndep Bx) (hlx : lx.length = k) (hlz : lz.length = k)
    (hBxlz : ∀ z ∈ lz, ∀ x ∈ Bx, commutes z x = true)
    (hsymp : ∀ (i j : Fin k), commutes (lx.getD i.val 0) (lz.getD j.val 0) = decide (i.val ≠ j.val)) :
    LinIndep (Bx ++ lx) := by
  intro m hml hz
  rw [List.length_append] at hml
  let m1 := m.take Bx.length
  let m2 := m.drop Bx.length
  have hm1l : m1.length = Bx.length := by simp [m1, List.length_take]; omega
  have hm2l : m2.length = lx.length := by simp [m2, List.length_drop]; omega
  have hm_eq : m = m1 ++ m2 := (List.take_append_drop Bx.length m).symm
  rw [hm_eq, xorSubset_append Bx lx m1 m2 hm1l] at hz
  have hm2_false : m2 = List.replicate lx.length false := by
    apply List.ext_getElem (by simp [hm2l])
    intro j hj1 hj2
    have hjk : j < k := by omega
    have hlt_lz : j < lz.length := by omega
    have hc := congrArg (fun v => commutes (lz.getD j 0) v) hz
    rw [commutes_symm (lz.getD j 0) 0, commutes_zero_left, commutes_xor_right] at hc
    have hBx0 : commutes (lz.getD j 0) (xorSubset Bx m1) = true := by
      rw [commutes_symm]
      apply commutes_xorSubset_left
      intro x hx
      rw [commutes_symm]
      exact hBxlz _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_lz]) x hx
    have hlx_c : commutes (lz.getD j 0) (xorSubset lx m2) = !(m2.getD j false) := by
      have hpair : ∀ a (ha : a < lz.length) b (hb : b < lz.length),
          commutes lz[a] (lx[b]'(by omega)) = decide (a ≠ b) := fun a ha b hb => by
        have := hsymp ⟨b, by omega⟩ ⟨a, by omega⟩
        rw [commutes_symm]
        have ga : lz.getD a 0 = lz[a] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
        have gb : lx.getD b 0 = lx[b]'(by omega) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : b < lx.length)]
        rw [ga, gb] at this
        rw [this]
        by_cases hab : a = b
        · simp [hab]
        · have hba : b ≠ a := fun h => hab h.symm
          simp [hab, hba]
      have := commutes_xorSubset_dual lz lx m2 j (by omega) (by omega) hlt_lz hpair
      have gj : lz.getD j 0 = lz[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_lz]
      rw [gj]; exact this
    rw [hBx0, hlx_c] at hc
    have hg : m2.getD j false = m2[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]
    rw [hg] at hc
    simp only [List.getElem_replicate]
    cases hb : m2[j] <;> simp [hb] at hc ⊢
  have hm1_false : m1 = List.replicate Bx.length false := by
    apply hBx m1 hm1l
    rw [hm2_false, xorSubset_false] at hz
    simpa using hz
  rw [hm_eq, hm1_false, hm2_false, List.length_append, replicate_add]

/-! ## 4. Column Equivalence Classes, Forced Subspace, and Singleton Syndrome Bound -/

private theorem find?_some_eq {α β : Type} [DecidableEq β] {f : α → β} {target : β} {xs : List α} {a : α}
    (h : xs.find? (fun x => decide (f x = target)) = some a) : f a = target := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    by_cases hfx : f x = target
    · simp only [decide_eq_true hfx, Option.some.injEq] at h
      exact h ▸ hfx
    · simp only [decide_eq_false hfx] at h
      exact ih h

private def diffIsNonRep {α : Type} [DecidableEq α] (key : Nat → α) (qs : List Nat) (q : Nat) : Bool :=
  match qs.find? (fun r => decide (key r = key q)) with
  | some rep => decide (rep ≠ q)
  | none => false

private def diffMkVec {α : Type} [DecidableEq α] (n : Nat) (key : Nat → α) (qs : List Nat) (q : Nat) : BitVec n :=
  match qs.find? (fun r => decide (key r = key q)) with
  | some rep => unitVec n rep ^^^ unitVec n q
  | none => 0

/-- Build the list of `e_{rep} ⊕ e_q` for all non-representative elements in a list grouped by key `key`. -/
private def diffVecs {α : Type} [DecidableEq α] (n : Nat) (key : Nat → α) (qs : List Nat) : List (BitVec n) :=
  (qs.filter (diffIsNonRep key qs)).map (diffMkVec n key qs)

private theorem linIndep_diffVecs {α : Type} [DecidableEq α] (n : Nat) (key : Nat → α)
    (qs : List Nat) (hnd : qs.Nodup) (hlt : ∀ q ∈ qs, q < n) :
    LinIndep (diffVecs n key qs) := by
  let isNonRep := diffIsNonRep key qs
  let nonReps := qs.filter isNonRep
  let mkVec := diffMkVec n key qs
  change LinIndep (nonReps.map mkVec)
  have hrep_neq : ∀ q ∈ nonReps, ∀ r ∈ nonReps,
      (match qs.find? (fun t => decide (key t = key r)) with | some rep => rep ≠ q | none => True) := by
    intro q hq r hr
    have hq_nr : isNonRep q = true := (List.mem_filter.mp hq).2
    cases hfr : qs.find? (fun t => decide (key t = key r)) with
    | none => trivial
    | some rep =>
      intro hreq; subst hreq
      have hkey : key rep = key r := find?_some_eq hfr
      have hsame : qs.find? (fun t => decide (key t = key rep)) = some rep := by
        rw [← hkey] at hfr; exact hfr
      dsimp only [isNonRep, diffIsNonRep] at hq_nr
      rw [hsame] at hq_nr
      simp at hq_nr
  have hnr_nd : nonReps.Nodup := nodup_filter isNonRep hnd
  have hbit_self : ∀ q ∈ nonReps, (mkVec q).getLsbD q = true := by
    intro q hq
    have hq_mem : q ∈ qs := (List.mem_filter.mp hq).1
    have hq_nr : isNonRep q = true := (List.mem_filter.mp hq).2
    dsimp only [isNonRep, diffIsNonRep] at hq_nr
    dsimp only [mkVec, diffMkVec]
    cases hf : qs.find? (fun r => decide (key r = key q)) with
    | none => rw [hf] at hq_nr; cases hq_nr
    | some rep =>
      rw [hf] at hq_nr
      have hne : rep ≠ q := of_decide_eq_true hq_nr
      have hrep_mem : rep ∈ qs := List.mem_of_find?_eq_some hf
      rw [BitVec.getLsbD_xor, unitVec_getLsbD (hlt rep hrep_mem), unitVec_getLsbD (hlt q hq_mem)]
      simp [hne.symm]
  have hbit_other : ∀ q ∈ nonReps, ∀ r ∈ nonReps, r ≠ q → (mkVec r).getLsbD q = false := by
    intro q hq r hr hne
    have hr_mem : r ∈ qs := (List.mem_filter.mp hr).1
    have hnr := hrep_neq q hq r hr
    dsimp only [mkVec, diffMkVec]
    cases hf : qs.find? (fun t => decide (key t = key r)) with
    | none => simp
    | some rep =>
      rw [hf] at hnr
      have hrep_mem : rep ∈ qs := List.mem_of_find?_eq_some hf
      rw [BitVec.getLsbD_xor, unitVec_getLsbD (hlt rep hrep_mem), unitVec_getLsbD (hlt r hr_mem)]
      simp [hne.symm, Ne.symm hnr]
  intro m hml hz
  apply List.ext_getElem (by simp [hml])
  intro i hi1 hi2
  have hi_nr : i < nonReps.length := by simp at hml; omega
  let q := nonReps[i]
  have hq_mem : q ∈ nonReps := List.getElem_mem hi_nr
  have hbit0 : (xorSubset (nonReps.map mkVec) m).getLsbD q = false := by rw [hz]; simp
  rw [xorSubset_getLsbD] at hbit0
  have hfold_not_mem : ∀ (xs : List Nat) (ms : List Bool) (a : Bool),
      xs.length = ms.length → (∀ x ∈ xs, x ∈ nonReps) → q ∉ xs →
      (List.zip (xs.map mkVec) ms).foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) a = a := by
    intro xs; induction xs with
    | nil => intro ms a hlen _ _; cases ms <;> simp at hlen ⊢
    | cons x xs ih =>
      intro ms a hlen hsub hnot
      cases ms with
      | nil => simp at hlen
      | cons b bs =>
        simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
        have hxq : x ≠ q := fun h => hnot (h ▸ List.mem_cons_self ..)
        rw [hbit_other q hq_mem x (hsub x (List.mem_cons_self ..)) hxq]
        have ha_eq : (if b then xor a false else a) = a := by cases b <;> cases a <;> rfl
        rw [ha_eq]
        exact ih bs a (by simpa using hlen) (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) (fun hm => hnot (List.mem_cons_of_mem _ hm))
  have hfold_at : ∀ (xs : List Nat) (ms : List Bool) (k : Nat) (hk : k < xs.length) (a : Bool)
      (hlen : xs.length = ms.length), xs.Nodup → (∀ x ∈ xs, x ∈ nonReps) → xs[k] = q →
      (List.zip (xs.map mkVec) ms).foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) a =
      xor a (ms[k]'(by omega)) := by
    intro xs; induction xs with
    | nil => intro _ k hk; simp at hk
    | cons x xs ih =>
      intro ms k hk a hlen hnd' hsub hxq
      cases ms with
      | nil => simp at hlen
      | cons b bs =>
        obtain ⟨hxnot, hndxs⟩ := List.nodup_cons.mp hnd'
        simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
        cases k with
        | zero =>
          have hx_eq : x = q := by simpa using hxq
          subst hx_eq
          rw [hbit_self q (hsub q (List.mem_cons_self ..))]
          rw [hfold_not_mem xs bs _ (by simpa using hlen) (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hxnot]
          cases a <;> cases b <;> rfl
        | succ k =>
          have hk' : k < xs.length := by simp at hk; omega
          have hxk : xs[k] = q := by simpa using hxq
          have hne : x ≠ q := fun h => hxnot (h ▸ hxk ▸ List.getElem_mem hk')
          rw [hbit_other q hq_mem x (hsub x (List.mem_cons_self ..)) hne]
          have ha_eq : (if b then xor a false else a) = a := by cases b <;> cases a <;> rfl
          rw [ha_eq]
          exact ih bs k hk' a (by simpa using hlen) hndxs (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hxk
  rw [hfold_at nonReps m i hi_nr false (by simp at hml; omega) hnr_nd (fun _ h => h) rfl] at hbit0
  simp only [List.getElem_replicate]
  cases hb : m[i] <;> simp [hb] at hbit0 ⊢

private theorem diffVecs_length {α : Type} [DecidableEq α] (n : Nat) (key : Nat → α)
    (qs : List Nat) (hnd : qs.Nodup) :
    (diffVecs n key qs).length + (dedup (qs.map key)).length = qs.length := by
  let isRep (q : Nat) : Bool :=
    match qs.find? (fun r => decide (key r = key q)) with
    | some rep => decide (rep = q)
    | none => false
  have hsplit : (diffVecs n key qs).length + (qs.filter isRep).length = qs.length := by
    unfold diffVecs
    rw [List.length_map]
    have hgen' : ∀ (xs : List Nat), (∀ x ∈ xs, x ∈ qs) →
        (xs.filter (diffIsNonRep key qs)).length + (xs.filter isRep).length = xs.length := by
      intro xs; induction xs with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hsub
        have hx : x ∈ qs := hsub x (List.mem_cons_self ..)
        have ih' := ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz))
        simp only [List.filter_cons, List.length_cons]
        have hcomp : diffIsNonRep key qs x = !(isRep x) := by
          dsimp only [diffIsNonRep, isRep]
          cases hf : qs.find? (fun r => decide (key r = key x)) with
          | none =>
            have := List.find?_eq_none.mp hf x hx
            simp at this
          | some rep =>
            by_cases heq : rep = x <;> simp [heq]
        rw [hcomp]
        cases h : isRep x <;> simp [h] <;> omega
    exact hgen' qs (fun _ h => h)
  have hrep_keys_nd : ((qs.filter isRep).map key).Nodup := by
    apply nodup_map_of_inj (nodup_filter isRep hnd)
    intro a ha b hb hkab
    have ha_rep : isRep a = true := (List.mem_filter.mp ha).2
    have hb_rep : isRep b = true := (List.mem_filter.mp hb).2
    dsimp only [isRep] at ha_rep hb_rep
    rw [hkab] at ha_rep
    cases hf : qs.find? (fun r => decide (key r = key b)) with
    | none => rw [hf] at hb_rep; cases hb_rep
    | some rep =>
      rw [hf] at ha_rep hb_rep
      have h1 : rep = a := of_decide_eq_true ha_rep
      have h2 : rep = b := of_decide_eq_true hb_rep
      exact h1.symm.trans h2
  have hrep_keys_sub : ∀ y ∈ (qs.filter isRep).map key, y ∈ dedup (qs.map key) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    exact (mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩)
  have hed_sub_rep : ∀ y ∈ dedup (qs.map key), y ∈ (qs.filter isRep).map key := by
    intro y hy
    have hy' := (mem_dedup _ _).mp hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy'
    cases hf : qs.find? (fun r => decide (key r = key q)) with
    | none =>
      have := List.find?_eq_none.mp hf q hq; simp at this
    | some rep =>
      have hrep_mem : rep ∈ qs := List.mem_of_find?_eq_some hf
      have hkr : key rep = key q := find?_some_eq hf
      have hrep_is : isRep rep = true := by
        dsimp only [isRep]; rw [hkr, hf]; simp
      exact List.mem_map.mpr ⟨rep, List.mem_filter.mpr ⟨hrep_mem, hrep_is⟩, hkr⟩
  have hle1 := nodup_length_le_of_subset hrep_keys_nd hrep_keys_sub
  have hle2 := nodup_length_le_of_subset (nodup_dedup _) hed_sub_rep
  rw [List.length_map] at hle1 hle2
  omega

private theorem arith_contradiction
    (n k rX rZ n1 n2 s1 s2 rExtra t t1 t2 a1 wLen synLen : Nat)
    (hn : n ≤ 15) (hk : 4 ≤ k) (hr_le : rX ≤ rZ) (hrank : rX + k + rZ ≤ n)
    (hn12 : n1 + n2 = n) (hn2_le : n2 ≤ 4 * rX - n) (h4rX : n ≤ 4 * rX)
    (hs1 : s1 ≤ rX) (hs2 : s2 ≤ n2)
    (hrExtra : rExtra + rX + 4 ≤ s1 + s2)
    (ht1_a1 : t1 + a1 = s1) (ht1_n1 : t1 + 2 * a1 ≤ n1)
    (ht2_n2 : 2 * s2 ≤ n2 + t2) (ht_eq : t = t1 + t2)
    (hsyn_card : synLen + 1 ≤ 2 ^ rExtra)
    (hwLen_eq : wLen + synLen = t)
    (hwLen_le : wLen ≤ rX - a1)
    (hre0_imp : rExtra = 0 → t = 0) : False := by
  have hrExtra_le2 : rExtra ≤ 2 := by omega
  rcases (show rExtra = 0 ∨ rExtra = 1 ∨ rExtra = 2 by omega) with rfl | rfl | rfl
  · have := hre0_imp rfl; omega
  · simp at hsyn_card; omega
  · simp at hsyn_card; omega

/-! ## 5. Core Non-Existence Theorem for Minimal Codes (`n ≤ 15, k ≥ 4`) -/

private theorem no_minimal_css_k4 {n k : Nat} (hn : n ≤ 15) (hk : 4 ≤ k)
    {hx hz lx lz : List (BitVec n)}
    (hcss : IsCSSCode n k 3 4 hx hz lx lz)
    (hno1x : ∀ q < n, ¬ InRowSpace hx (unitVec n q))
    (hno1z : ∀ q < n, ¬ InRowSpace hz (unitVec n q)) : False := by
  obtain ⟨Bx0, hBx0_sub, hBx0_li, hBx0_span⟩ := exists_basis hx
  obtain ⟨Bz0, hBz0_sub, hBz0_li, hBz0_span⟩ := exists_basis hz
  suffices hmain : ∀ (hx hz lx lz Bx Bz : List (BitVec n)),
      IsCSSCode n k 3 4 hx hz lx lz →
      (∀ q < n, ¬ InRowSpace hx (unitVec n q)) →
      (∀ q < n, ¬ InRowSpace hz (unitVec n q)) →
      (∀ x ∈ Bx, x ∈ hx) → LinIndep Bx → (∀ v, InRowSpace Bx v ↔ InRowSpace hx v) →
      (∀ z ∈ Bz, z ∈ hz) → LinIndep Bz → (∀ v, InRowSpace Bz v ↔ InRowSpace hz v) →
      Bx.length ≤ Bz.length → False by
    by_cases hle : Bx0.length ≤ Bz0.length
    · exact hmain hx hz lx lz Bx0 Bz0 hcss hno1x hno1z hBx0_sub hBx0_li hBx0_span hBz0_sub hBz0_li hBz0_span hle
    · exact hmain hz hx lz lx Bz0 Bx0 (isCSSCode_swap hcss) hno1z hno1x hBz0_sub hBz0_li hBz0_span hBx0_sub hBx0_li hBx0_span (by omega)
  intro hx hz lx lz Bx Bz hcss hno1x hno1z hBx_sub hBx_li hBx_span hBz_sub hBz_li hBz_span hr_le
  obtain ⟨hlx, hlz, hcomm, hwx, hwz, hlxhz, hlzhx, hsymp, hdx, hdz⟩ := hcss
  let rX := Bx.length
  let rZ := Bz.length
  have hBxlx_li : LinIndep (Bx ++ lx) :=
    linIndep_append_logical hBx_li hlx hlz
      (fun z hzMem x hxMem => hlzhx z hzMem x (hBx_sub x hxMem)) hsymp
  have hBxlx_orth : ∀ a ∈ Bx ++ lx, ∀ b ∈ Bz, commutes a b = true := by
    intro a ha b hb
    rcases List.mem_append.mp ha with h1 | h2
    · exact hcomm a (hBx_sub a h1) b (hBz_sub b hb)
    · exact hlxhz a h2 b (hBz_sub b hb)
  have hrank_sum : rX + k + rZ ≤ n := by
    have := rank_orth_bound hBxlx_li hBz_li hBxlx_orth
    simp only [List.length_append, hlx] at this
    exact this
  have hrX_bound : 2 * rX + 4 ≤ n := by omega
  have hrX_le5 : rX ≤ 5 := by omega

  -- Step 3: Column vector `col q : BitVec rX` of `Bx`, weight of each column ≥ 1, and double counting!
  let col (q : Nat) : BitVec rX := mkBitVec rX fun i => (Bx.getD i 0).getLsbD q
  have hcol_bit : ∀ q (i : Nat) (hi : i < rX), (col q).getLsbD i = Bx[i].getLsbD q := by
    intro q i hi
    dsimp only [col]
    rw [mkBitVec_getLsbD rX _ hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hcol_ne0 : ∀ q < n, col q ≠ 0 := by
    intro q hq hzcol
    apply hno1z q hq
    apply hdz (unitVec n q) (by rw [hammingWeight_unitVec hq]; omega) (by rw [hammingWeight_unitVec hq]; omega)
    intro x hxMem
    have hxin : InRowSpace Bx x := (hBx_span x).mpr (inRowSpace_mem hxMem)
    rw [commutes_symm]
    apply commutes_inRowSpace hxin
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    rw [commutes_symm, commutes_unitVec hq]
    have hb0 : (col q).getLsbD i = false := by rw [hzcol]; simp
    rw [hcol_bit q i hi] at hb0
    rw [hb0]; rfl
  have hcol_wt_pos : ∀ q < n, 1 ≤ hammingWeight (col q) := by
    intro q hq
    obtain ⟨i, hi, hbit⟩ := exists_set_bit_of_ne_zero (hcol_ne0 q hq)
    rw [hammingWeight_eq_filter]
    have hmem : i ∈ (List.range rX).filter (fun j => (col q).getLsbD j) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hi, hbit⟩
    exact List.length_pos_of_mem hmem

  let qs := List.range n
  have hqs_nd : qs.Nodup := List.nodup_range
  let sumCols := qs.foldl (fun acc q => acc + hammingWeight (col q)) 0
  have hsum_le : sumCols ≤ 4 * rX := by
    have hfold_add : ∀ {α : Type} (f : α → Nat) (xs : List α) (a : Nat),
        xs.foldl (fun acc x => acc + f x) a = a + xs.foldl (fun acc x => acc + f x) 0 := by
      intro α f xs; induction xs with
      | nil => intro a; simp
      | cons x xs ih => intro a; simp only [List.foldl_cons]; rw [ih (a + f x), ih (0 + f x)]; omega
    have hswap : ∀ (ys : List Nat) (xs : List (BitVec n)),
        ys.foldl (fun acc q => acc + (xs.filter (fun row => row.getLsbD q)).length) 0 =
        xs.foldl (fun acc row => acc + (ys.filter (fun q => row.getLsbD q)).length) 0 := by
      intro ys; induction ys with
      | nil =>
        intro xs; simp only [List.foldl_nil]
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          rw [List.foldl_cons, List.filter_nil, List.length_nil, Nat.add_zero]
          exact ih
      | cons y ys ih =>
        intro xs
        simp only [List.foldl_cons]
        rw [hfold_add (fun q => (xs.filter (fun row => row.getLsbD q)).length) ys, ih xs]
        clear ih
        have hstep : ∀ (xs : List (BitVec n)) (a : Nat),
            xs.foldl (fun acc row => acc + ((y :: ys).filter (fun q => row.getLsbD q)).length) a =
            a + (xs.filter (fun row => row.getLsbD y)).length +
              xs.foldl (fun acc row => acc + (ys.filter (fun q => row.getLsbD q)).length) 0 := by
          intro xs; induction xs with
          | nil => intro a; simp
          | cons x xs ihx =>
            intro a
            rw [List.foldl_cons, List.foldl_cons, ihx,
                hfold_add (fun row => (ys.filter (fun q => row.getLsbD q)).length) xs (0 + (ys.filter (fun q => x.getLsbD q)).length)]
            simp only [List.filter_cons]
            cases hb : x.getLsbD y <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
        rw [hstep xs 0]
    have hcol_eq_Bx : ∀ q, hammingWeight (col q) = (Bx.filter (fun row => row.getLsbD q)).length := by
      intro q
      rw [hammingWeight_eq_filter]
      have hgen : ∀ (xs : List (BitVec n)),
          ((List.range xs.length).filter (fun i => (xs.getD i 0).getLsbD q)).length =
          (xs.filter (fun row => row.getLsbD q)).length := by
        intro xs; induction xs with
        | nil => rfl
        | cons x xs ih =>
          rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
          have h0 : ((x :: xs).getD 0 0).getLsbD q = x.getLsbD q := rfl
          have hcomp : ((fun i => ((x :: xs).getD i 0).getLsbD q) ∘ Nat.succ) = (fun i => (xs.getD i 0).getLsbD q) := by
            funext i; rfl
          rw [h0, hcomp, List.filter_cons]
          cases hb : x.getLsbD q <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_map, ih]
      have hcongr : ((List.range rX).filter (fun i => (col q).getLsbD i)).length =
          ((List.range Bx.length).filter (fun i => (Bx.getD i 0).getLsbD q)).length := by
        congr 1; apply List.filter_congr; intro i hi
        have hi' : i < rX := List.mem_range.mp hi
        rw [hcol_bit q i hi']
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rw [hcongr, hgen Bx]
    have hsum_eq : sumCols = Bx.foldl (fun acc row => acc + hammingWeight row) 0 := by
      dsimp only [sumCols, qs]
      have h1 : (List.range n).foldl (fun acc q => acc + hammingWeight (col q)) 0 =
          (List.range n).foldl (fun acc q => acc + (Bx.filter (fun row => row.getLsbD q)).length) 0 := by
        congr 1; funext acc q; rw [hcol_eq_Bx q]
      rw [h1, hswap]
      congr 1; funext acc row; rw [hammingWeight_eq_filter]
    rw [hsum_eq]
    have hbound : ∀ (xs : List (BitVec n)) (a : Nat), (∀ x ∈ xs, hammingWeight x ≤ 4) →
        xs.foldl (fun acc row => acc + hammingWeight row) a ≤ a + 4 * xs.length := by
      intro xs; induction xs with
      | nil => intro a _; simp
      | cons x xs ih =>
        intro a h4
        simp only [List.foldl_cons, List.length_cons]
        have hx4 := h4 x (List.mem_cons_self ..)
        have := ih (a + hammingWeight x) (fun z hz => h4 z (List.mem_cons_of_mem _ hz))
        omega
    have := hbound Bx 0 (fun x hx => hwx x (hBx_sub x hx))
    simpa [rX] using this

  -- Partition `qs = List.range n` into weight-1 columns `Q1` and weight-≥2 columns `Q2`!
  let Q1 := qs.filter (fun q => decide (hammingWeight (col q) = 1))
  let Q2 := qs.filter (fun q => decide (2 ≤ hammingWeight (col q)))
  let n1 := Q1.length
  let n2 := Q2.length
  have hn12 : n1 + n2 = n := by
    have hgen : ∀ (xs : List Nat), (∀ q ∈ xs, 1 ≤ hammingWeight (col q)) →
        (xs.filter (fun q => decide (hammingWeight (col q) = 1))).length +
        (xs.filter (fun q => decide (2 ≤ hammingWeight (col q)))).length = xs.length := by
      intro xs; induction xs with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hpos
        have hx := hpos x (List.mem_cons_self ..)
        have ih' := ih (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
        simp only [List.filter_cons, List.length_cons]
        by_cases h1 : hammingWeight (col x) = 1
        · have h1t : decide (hammingWeight (col x) = 1) = true := decide_eq_true h1
          have h2f : decide (2 ≤ hammingWeight (col x)) = false := decide_eq_false (by omega)
          simp only [h1t, h2f, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
        · have h1f : decide (hammingWeight (col x) = 1) = false := decide_eq_false h1
          have h2t : decide (2 ≤ hammingWeight (col x)) = true := decide_eq_true (by omega)
          simp only [h1f, h2t, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    have := hgen qs (fun q hq => hcol_wt_pos q (List.mem_range.mp hq))
    simpa [n1, n2, Q1, Q2, qs] using this
  have h12_sum : n1 + 2 * n2 ≤ sumCols := by
    have hgen : ∀ (xs : List Nat) (a : Nat), (∀ q ∈ xs, 1 ≤ hammingWeight (col q)) →
        a + (xs.filter (fun q => decide (hammingWeight (col q) = 1))).length +
        2 * (xs.filter (fun q => decide (2 ≤ hammingWeight (col q)))).length ≤
        xs.foldl (fun acc q => acc + hammingWeight (col q)) a := by
      intro xs; induction xs with
      | nil => intro a _; simp
      | cons x xs ih =>
        intro a hpos
        have hx := hpos x (List.mem_cons_self ..)
        have ih' := ih (a + hammingWeight (col x)) (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
        simp only [List.foldl_cons, List.filter_cons]
        by_cases h1 : hammingWeight (col x) = 1
        · have h1t : decide (hammingWeight (col x) = 1) = true := decide_eq_true h1
          have h2f : decide (2 ≤ hammingWeight (col x)) = false := decide_eq_false (by omega)
          simp only [h1t, h2f, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
        · have h1f : decide (hammingWeight (col x) = 1) = false := decide_eq_false h1
          have h2t : decide (2 ≤ hammingWeight (col x)) = true := decide_eq_true (by omega)
          simp only [h1f, h2t, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    have := hgen qs 0 (fun q hq => hcol_wt_pos q (List.mem_range.mp hq))
    simpa [n1, n2, Q1, Q2, sumCols, qs] using this
  have hn2_le : n2 ≤ 4 * rX - n := by omega
  have h4rX_ge : n ≤ 4 * rX := by omega

  -- Step 4: Forced Z-stabilizers `vf = diffVecs n col qs`, distinct columns `S1, S2`, and `rExtra`!
  let vf := diffVecs n col qs
  have hvf_li : LinIndep vf := linIndep_diffVecs n col qs hqs_nd (fun q hq => List.mem_range.mp hq)
  have hvf_in_hz : ∀ v ∈ vf, InRowSpace hz v := by
    intro v hv
    unfold vf diffVecs at hv
    obtain ⟨q, hq_f, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hq_mem, hq_nr⟩ := List.mem_filter.mp hq_f
    unfold diffIsNonRep at hq_nr
    unfold diffMkVec
    cases hf : qs.find? (fun r => decide (col r = col q)) with
    | none => rw [hf] at hq_nr; cases hq_nr
    | some rep =>
      rw [hf] at hq_nr
      have heq : rep ≠ q := of_decide_eq_true hq_nr
      have hq_lt : q < n := List.mem_range.mp hq_mem
      have hrep_lt : rep < n := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hcol_eq : col rep = col q := find?_some_eq hf
      apply hdz (unitVec n rep ^^^ unitVec n q)
        (by rw [hammingWeight_xor_unitVec hrep_lt hq_lt heq]; omega)
        (by rw [hammingWeight_xor_unitVec hrep_lt hq_lt heq]; omega)
      intro x hxMem
      have hxin : InRowSpace Bx x := (hBx_span x).mpr (inRowSpace_mem hxMem)
      rw [commutes_symm]
      apply commutes_inRowSpace hxin
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      rw [commutes_symm, commutes_xor_left, commutes_unitVec hrep_lt, commutes_unitVec hq_lt]
      have hbi := congrArg (fun c : BitVec rX => c.getLsbD i) hcol_eq
      rw [hcol_bit rep i hi, hcol_bit q i hi] at hbi
      rw [hbi]; cases Bx[i].getLsbD q <;> rfl
  let S := dedup (qs.map col)
  let S1 := dedup (Q1.map col)
  let S2 := dedup (Q2.map col)
  let s1 := S1.length
  let s2 := S2.length
  have hS_len : S.length = s1 + s2 := by
    have hdisj : ∀ c ∈ S1, c ∉ S2 := by
      intro c hc1 hc2
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc1)
      obtain ⟨q2, hq2, heq⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc2)
      have hw1 : hammingWeight (col q1) = 1 := of_decide_eq_true (List.mem_filter.mp hq1).2
      have hw2 : 2 ≤ hammingWeight (col q2) := of_decide_eq_true (List.mem_filter.mp hq2).2
      rw [heq] at hw2; omega
    have hnd12 : (S1 ++ S2).Nodup :=
      List.nodup_append.mpr ⟨nodup_dedup _, nodup_dedup _, fun a ha b hb h => hdisj a ha (h ▸ hb)⟩
    have hsub1 : ∀ c ∈ S1 ++ S2, c ∈ S := by
      intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp h1)
        exact (mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp h2)
        exact (mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, rfl⟩)
    have hsub2 : ∀ c ∈ S, c ∈ S1 ++ S2 := by
      intro c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc)
      have hpos := hcol_wt_pos q (List.mem_range.mp hq)
      by_cases h1 : hammingWeight (col q) = 1
      · exact List.mem_append_left _ ((mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, decide_eq_true h1⟩, rfl⟩))
      · exact List.mem_append_right _ ((mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, decide_eq_true (by omega)⟩, rfl⟩))
    have hle1 := nodup_length_le_of_subset hnd12 hsub1
    have hle2 := nodup_length_le_of_subset (nodup_dedup _) hsub2
    rw [List.length_append] at hle1 hle2
    exact Nat.le_antisymm hle2 hle1
  have hs1_le_rX : s1 ≤ rX := by
    have hsub : ∀ c ∈ S1, c ∈ (List.range rX).map (unitVec rX) := by
      intro c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc)
      have hw1 : hammingWeight (col q) = 1 := of_decide_eq_true (List.mem_filter.mp hq).2
      have hne : col q ≠ 0 := hcol_ne0 q (List.mem_range.mp (List.mem_filter.mp hq).1)
      obtain ⟨i, hi, hbi⟩ := exists_set_bit_of_ne_zero hne
      refine List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      rw [unitVec_getLsbD hi]
      by_cases hji : j = i
      · subst hji; simp [hbi]
      · simp only [hji, decide_false]
        cases hbj : (col q).getLsbD j
        · rfl
        · exfalso
          rw [hammingWeight_eq_filter] at hw1
          have hmemi : i ∈ (List.range rX).filter (fun t => (col q).getLsbD t) := List.mem_filter.mpr ⟨List.mem_range.mpr hi, hbi⟩
          have hmemj : j ∈ (List.range rX).filter (fun t => (col q).getLsbD t) := List.mem_filter.mpr ⟨List.mem_range.mpr hj, hbj⟩
          have h2 : ([i, j] : List Nat).Nodup := by simp [Ne.symm hji]
          have hle := nodup_length_le_of_subset h2 (fun t ht => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl <;> assumption)
          simp at hle; omega
    have hle := nodup_length_le_of_subset (nodup_dedup _) hsub
    simpa [s1] using hle
  have hs2_le_n2 : s2 ≤ n2 := by
    have hle := nodup_length_le_of_subset (nodup_dedup (Q2.map col)) (fun c hc => (mem_dedup (Q2.map col) c).mp hc)
    simpa [s2, n2] using hle
  have hvf_len : vf.length + s1 + s2 = n := by
    have := diffVecs_length n col qs hqs_nd
    dsimp only [vf, S, qs] at this hS_len ⊢
    rw [hS_len, List.length_range] at this
    omega

  -- Extend `vf` inside `Bz` to get `ext` with `LinIndep (ext ++ vf)` and `span(ext ++ vf) = span(hz)`!
  obtain ⟨ext, hext_mem, hext_li, hext_span⟩ := exists_extend_basis vf Bz hvf_li
  have hext_span_hz : ∀ v, InRowSpace (ext ++ vf) v ↔ InRowSpace hz v := by
    intro v; rw [hext_span v]; constructor
    · intro hv
      apply inRowSpace_mono (A := Bz ++ vf) _ hv
      intro a ha
      rcases List.mem_append.mp ha with h1 | h2
      · exact (hBz_span a).mp (inRowSpace_mem h1)
      · exact hvf_in_hz a h2
    · intro hv
      have := (hBz_span v).mpr hv
      exact inRowSpace_mono (fun a ha => inRowSpace_mem (List.mem_append_left _ ha)) this
  have hlen_ext_vf : ext.length + vf.length = rZ := by
    have h1 := linIndep_le_of_subset hext_li (fun a ha => (hBz_span a).mpr ((hext_span_hz a).mp (inRowSpace_mem ha)))
    have h2 := linIndep_le_of_subset hBz_li (fun a ha => (hext_span_hz a).mpr ((hBz_span a).mp (inRowSpace_mem ha)))
    rw [List.length_append] at h1 h2
    omega
  let rExtra := ext.length
  have hrExtra_le : rExtra + rX + 4 ≤ s1 + s2 := by omega

  -- Step 5: Singletons `T`, `T1`, `T2`, non-singleton weight-1 classes `A1`, and syndrome map!
  let isSingleton (q : Nat) : Bool := decide ((qs.filter (fun r => decide (col r = col q))).length = 1)
  let T := qs.filter isSingleton
  let T1 := Q1.filter isSingleton
  let T2 := Q2.filter isSingleton
  let t := T.length
  let t1 := T1.length
  let t2 := T2.length
  let A1 := S1.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))
  let a1 := A1.length
  have hclass_count : ∀ (Q : List Nat) (SQ : List (BitVec rX)),
      Q.Nodup → (∀ q ∈ Q, q ∈ qs) →
      (∀ q ∈ Q, ∀ r ∈ qs, col r = col q → r ∈ Q) →
      SQ = dedup (Q.map col) →
      let TQ := Q.filter isSingleton
      let AQ := SQ.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))
      TQ.length + AQ.length = SQ.length ∧ TQ.length + 2 * AQ.length ≤ Q.length := by
    intro Q SQ hQnd hQsub hQclosed hSQ
    have hfib_eq : ∀ c ∈ SQ, (Q.filter (fun q => decide (col q = c))).length = (qs.filter (fun q => decide (col q = c))).length := by
      intro c hc
      rw [hSQ] at hc
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc)
      have hndQ : (Q.filter (fun q => decide (col q = col q0))).Nodup := nodup_filter _ hQnd
      have hndqs : (qs.filter (fun q => decide (col q = col q0))).Nodup := nodup_filter _ hqs_nd
      have h1 : ∀ r ∈ Q.filter (fun q => decide (col q = col q0)), r ∈ qs.filter (fun q => decide (col q = col q0)) := by
        intro r hr; obtain ⟨hrQ, hrc⟩ := List.mem_filter.mp hr
        exact List.mem_filter.mpr ⟨hQsub r hrQ, hrc⟩
      have h2 : ∀ r ∈ qs.filter (fun q => decide (col q = col q0)), r ∈ Q.filter (fun q => decide (col q = col q0)) := by
        intro r hr; obtain ⟨hrqs, hrc⟩ := List.mem_filter.mp hr
        exact List.mem_filter.mpr ⟨hQclosed q0 hq0 r hrqs (of_decide_eq_true hrc), hrc⟩
      have ha := nodup_length_le_of_subset hndQ h1
      have hb := nodup_length_le_of_subset hndqs h2
      omega
    let S_sing := SQ.filter (fun c => decide ((qs.filter (fun q => decide (col q = c))).length = 1))
    let AQ := SQ.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))
    have hSQ_pos : ∀ c ∈ SQ, 1 ≤ (qs.filter (fun q => decide (col q = c))).length := by
      intro c hc; rw [hSQ] at hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hc)
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hQsub q hq, by simp⟩)
    have hSQ_split : S_sing.length + AQ.length = SQ.length := by
      have hgen : ∀ (cs : List (BitVec rX)), (∀ c ∈ cs, 1 ≤ (qs.filter (fun q => decide (col q = c))).length) →
          (cs.filter (fun c => decide ((qs.filter (fun q => decide (col q = c))).length = 1))).length +
          (cs.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))).length = cs.length := by
        intro cs; induction cs with
        | nil => intro _; rfl
        | cons c cs ih =>
          intro hpos
          have hc := hpos c (List.mem_cons_self ..)
          have ih' := ih (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
          simp only [List.filter_cons, List.length_cons]
          by_cases h1 : (qs.filter (fun q => decide (col q = c))).length = 1
          · have h1t : decide ((qs.filter (fun q => decide (col q = c))).length = 1) = true := decide_eq_true h1
            have h2f : decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length) = false := decide_eq_false (by omega)
            simp only [h1t, h2f, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
          · have h1f : decide ((qs.filter (fun q => decide (col q = c))).length = 1) = false := decide_eq_false h1
            have h2t : decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length) = true := decide_eq_true (by omega)
            simp only [h1f, h2t, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      exact hgen SQ hSQ_pos
    have hTQ_eq_Ssing : (Q.filter isSingleton).length = S_sing.length := by
      have hndTQ : (Q.filter isSingleton).Nodup := nodup_filter _ hQnd
      have hcol_inj : ∀ a ∈ Q.filter isSingleton, ∀ b ∈ Q.filter isSingleton, col a = col b → a = b := by
        intro a ha b hb hcab
        have haQ := (List.mem_filter.mp ha).1
        have ha1 : (qs.filter (fun r => decide (col r = col a))).length = 1 := of_decide_eq_true (List.mem_filter.mp ha).2
        have hbQ := (List.mem_filter.mp hb).1
        have hma : a ∈ qs.filter (fun r => decide (col r = col a)) := List.mem_filter.mpr ⟨hQsub a haQ, by simp⟩
        have hmb : b ∈ qs.filter (fun r => decide (col r = col a)) := List.mem_filter.mpr ⟨hQsub b hbQ, by simp [hcab]⟩
        apply Classical.byContradiction; intro hne
        have hle := nodup_length_le_of_subset (by simp [hne] : ([a, b] : List Nat).Nodup)
          (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> assumption)
        simp at hle; omega
      have hnd_img : ((Q.filter isSingleton).map col).Nodup := nodup_map_of_inj hndTQ hcol_inj
      have hsub1 : ∀ c ∈ (Q.filter isSingleton).map col, c ∈ S_sing := by
        intro c hc
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
        have hqQ := (List.mem_filter.mp hq).1
        have hq1 : (qs.filter (fun r => decide (col r = col q))).length = 1 := of_decide_eq_true (List.mem_filter.mp hq).2
        exact List.mem_filter.mpr ⟨by rw [hSQ]; exact (mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, hqQ, rfl⟩), decide_eq_true hq1⟩
      have hsub2 : ∀ c ∈ S_sing, c ∈ (Q.filter isSingleton).map col := by
        intro c hc
        have hcSQ := (List.mem_filter.mp hc).1
        have hc1 : (qs.filter (fun r => decide (col r = c))).length = 1 := of_decide_eq_true (List.mem_filter.mp hc).2
        rw [hSQ] at hcSQ
        obtain ⟨q, hqQ, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hcSQ)
        exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hqQ, decide_eq_true hc1⟩, rfl⟩
      have h1 := nodup_length_le_of_subset hnd_img hsub1
      have h2 := nodup_length_le_of_subset (nodup_filter _ (by rw [hSQ]; exact nodup_dedup _)) hsub2
      rw [List.length_map] at h1 h2
      exact Nat.le_antisymm h1 h2
    have hsum_fib : (Q.filter isSingleton).length + 2 * AQ.length ≤ Q.length := by
      have hpart : ∀ (cs : List (BitVec rX)), cs.Nodup → (∀ c ∈ cs, c ∈ SQ) →
          (cs.flatMap (fun c => Q.filter (fun q => decide (col q = c)))).Nodup := by
        intro cs; induction cs with
        | nil => intro _ _; exact List.nodup_nil
        | cons c cs ih =>
          intro hnd' hsub
          obtain ⟨hcnot, hndcs⟩ := List.nodup_cons.mp hnd'
          simp only [List.flatMap_cons]
          refine List.nodup_append.mpr ⟨nodup_filter _ hQnd, ih hndcs (fun z hz => hsub z (List.mem_cons_of_mem _ hz)), ?_⟩
          intro x hx y hy heq; subst heq
          have hcx : col x = c := of_decide_eq_true (List.mem_filter.mp hx).2
          obtain ⟨c', hc', hy'⟩ := List.mem_flatMap.mp hy
          have hcx' : col x = c' := of_decide_eq_true (List.mem_filter.mp hy').2
          exact hcnot (hcx.symm.trans hcx' ▸ hc')
      have hflat_sub : ∀ q ∈ SQ.flatMap (fun c => Q.filter (fun r => decide (col r = c))), q ∈ Q := by
        intro q hq
        obtain ⟨_, _, hq'⟩ := List.mem_flatMap.mp hq
        exact (List.mem_filter.mp hq').1
      have hle_Q := nodup_length_le_of_subset (hpart SQ (by rw [hSQ]; exact nodup_dedup _) (fun _ h => h)) hflat_sub
      have hflat_ge : ∀ (cs : List (BitVec rX)), (∀ c ∈ cs, c ∈ SQ) →
          (cs.filter (fun c => decide ((qs.filter (fun q => decide (col q = c))).length = 1))).length +
          2 * (cs.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))).length ≤
          (cs.flatMap (fun c => Q.filter (fun q => decide (col q = c)))).length := by
        intro cs; induction cs with
        | nil => intro _; simp
        | cons c cs ih =>
          intro hsub
          have hcSQ := hsub c (List.mem_cons_self ..)
          have hfeq := hfib_eq c hcSQ
          have hpos := hSQ_pos c hcSQ
          have ih' := ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz))
          simp only [List.flatMap_cons, List.length_append, List.filter_cons]
          by_cases h1 : (qs.filter (fun q => decide (col q = c))).length = 1
          · have h1t : decide ((qs.filter (fun q => decide (col q = c))).length = 1) = true := decide_eq_true h1
            have h2f : decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length) = false := decide_eq_false (by omega)
            simp only [h1t, h2f, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
          · have h1f : decide ((qs.filter (fun q => decide (col q = c))).length = 1) = false := decide_eq_false h1
            have h2t : decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length) = true := decide_eq_true (by omega)
            simp only [h1f, h2t, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      have hge : S_sing.length + 2 * AQ.length ≤ (SQ.flatMap (fun c => Q.filter (fun q => decide (col q = c)))).length :=
        hflat_ge SQ (fun _ h => h)
      rw [hTQ_eq_Ssing]; exact Nat.le_trans hge hle_Q
    exact ⟨by rw [hTQ_eq_Ssing]; exact hSQ_split, hsum_fib⟩

  have hQ1_cnt := hclass_count Q1 S1 (nodup_filter _ hqs_nd)
    (fun q hq => (List.mem_filter.mp hq).1)
    (fun q hq r hr heq => List.mem_filter.mpr ⟨hr, by rw [heq]; exact (List.mem_filter.mp hq).2⟩) rfl
  have hQ2_cnt := hclass_count Q2 S2 (nodup_filter _ hqs_nd)
    (fun q hq => (List.mem_filter.mp hq).1)
    (fun q hq r hr heq => List.mem_filter.mpr ⟨hr, by rw [heq]; exact (List.mem_filter.mp hq).2⟩) rfl
  have ht1_a1 : t1 + a1 = s1 := hQ1_cnt.1
  have ht1_n1 : t1 + 2 * a1 ≤ n1 := hQ1_cnt.2
  have ht2_n2 : 2 * s2 ≤ n2 + t2 := by
    have h1 : t2 + (S2.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))).length = s2 := hQ2_cnt.1
    have h2 : t2 + 2 * (S2.filter (fun c => decide (2 ≤ (qs.filter (fun q => decide (col q = c))).length))).length ≤ n2 := hQ2_cnt.2
    omega
  have ht_eq : t = t1 + t2 := by
    have hgen : ∀ (xs : List Nat), (∀ q ∈ xs, 1 ≤ hammingWeight (col q)) →
        (xs.filter isSingleton).length =
        ((xs.filter (fun q => decide (hammingWeight (col q) = 1))).filter isSingleton).length +
        ((xs.filter (fun q => decide (2 ≤ hammingWeight (col q)))).filter isSingleton).length := by
      intro xs; induction xs with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hpos
        have hx := hpos x (List.mem_cons_self ..)
        have ih' := ih (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
        simp only [List.filter_cons]
        by_cases h1 : hammingWeight (col x) = 1
        · have h1t : decide (hammingWeight (col x) = 1) = true := decide_eq_true h1
          have h2f : decide (2 ≤ hammingWeight (col x)) = false := decide_eq_false (by omega)
          cases hsx : isSingleton x <;> simp only [h1t, h2f, hsx, Bool.false_eq_true, ↓reduceIte, List.filter_cons, List.length_cons] <;> omega
        · have h1f : decide (hammingWeight (col x) = 1) = false := decide_eq_false h1
          have h2t : decide (2 ≤ hammingWeight (col x)) = true := decide_eq_true (by omega)
          cases hsx : isSingleton x <;> simp only [h1f, h2t, hsx, Bool.false_eq_true, ↓reduceIte, List.filter_cons, List.length_cons] <;> omega
    exact hgen qs (fun q hq => hcol_wt_pos q (List.mem_range.mp hq))

  -- Every `v ∈ vf` is `false` on EVERY singleton `q ∈ T`!
  have hvf_zero_on_T : ∀ v ∈ vf, ∀ q ∈ T, v.getLsbD q = false := by
    intro v hv q hq
    have hq_qs := (List.mem_filter.mp hq).1
    have hq_s : (qs.filter (fun r => decide (col r = col q))).length = 1 := of_decide_eq_true (List.mem_filter.mp hq).2
    unfold vf diffVecs at hv
    obtain ⟨r, hr_f, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hr_qs, hr_nr⟩ := List.mem_filter.mp hr_f
    unfold diffIsNonRep at hr_nr
    unfold diffMkVec
    cases hf : qs.find? (fun t => decide (col t = col r)) with
    | none => rw [hf] at hr_nr; cases hr_nr
    | some rep =>
      rw [hf] at hr_nr
      have heq : rep ≠ r := of_decide_eq_true hr_nr
      have hr_lt : r < n := List.mem_range.mp hr_qs
      have hrep_qs : rep ∈ qs := List.mem_of_find?_eq_some hf
      have hrep_lt : rep < n := List.mem_range.mp hrep_qs
      have hcol_rr : col rep = col r := find?_some_eq hf
      have hq_ne_r : q ≠ r := by
        intro hqr; subst hqr
        have h2 : ([rep, q] : List Nat).Nodup := by simp [heq]
        have hle := nodup_length_le_of_subset (ys := qs.filter (fun t => decide (col t = col q))) h2 (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_filter.mpr ⟨hrep_qs, decide_eq_true hcol_rr⟩
          · exact List.mem_filter.mpr ⟨hq_qs, decide_eq_true rfl⟩)
        simp at hle; omega
      have hq_ne_rep : q ≠ rep := by
        intro hqr; subst hqr
        have h2 : ([q, r] : List Nat).Nodup := by simp [heq]
        have hle := nodup_length_le_of_subset (ys := qs.filter (fun t => decide (col t = col q))) h2 (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact List.mem_filter.mpr ⟨hq_qs, decide_eq_true rfl⟩
          · exact List.mem_filter.mpr ⟨hr_qs, decide_eq_true hcol_rr.symm⟩)
        simp at hle; omega
      rw [BitVec.getLsbD_xor, unitVec_getLsbD hrep_lt, unitVec_getLsbD hr_lt]
      simp [hq_ne_rep, hq_ne_r]

  -- Syndrome `syn q : List Bool` of `q ∈ T` under `ext` is NEVER all-false!
  let syn (q : Nat) : List Bool := ext.map (fun z => z.getLsbD q)
  have hsyn_len : ∀ q, (syn q).length = rExtra := fun q => by simp [syn, rExtra]
  have hsyn_ne0 : ∀ q ∈ T, syn q ≠ List.replicate rExtra false := by
    intro q hq hzero
    have hq_lt : q < n := List.mem_range.mp (List.mem_filter.mp hq).1
    apply hno1x q hq_lt
    apply hdx (unitVec n q) (by rw [hammingWeight_unitVec hq_lt]; omega) (by rw [hammingWeight_unitVec hq_lt]; omega)
    intro z hzMem
    have hzin : InRowSpace (ext ++ vf) z := (hext_span_hz z).mpr (inRowSpace_mem hzMem)
    rw [commutes_symm]
    apply commutes_inRowSpace hzin
    intro w hw
    rw [commutes_symm, commutes_unitVec hq_lt]
    rcases List.mem_append.mp hw with h1 | h2
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h1
      have hbit := congrArg (fun bs : List Bool => bs.getD j false) hzero
      have hlt_r : j < (List.replicate rExtra false).length := by simp [rExtra, hj]
      simp [syn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_r, hj] at hbit
      rw [hbit]; rfl
    · rw [hvf_zero_on_T w h2 q hq]; rfl

  have hsyn_card : (dedup (T.map syn)).length + 1 ≤ 2 ^ rExtra := by
    let zeroMask := List.replicate rExtra false
    have hz_not : zeroMask ∉ dedup (T.map syn) := by
      intro hmem
      obtain ⟨q, hq, heq⟩ := List.mem_map.mp ((mem_dedup _ _).mp hmem)
      exact hsyn_ne0 q hq heq
    have hnd : (zeroMask :: dedup (T.map syn)).Nodup := List.nodup_cons.mpr ⟨hz_not, nodup_dedup _⟩
    have hsub : ∀ m ∈ zeroMask :: dedup (T.map syn), m ∈ allMasks rExtra := by
      intro m hm
      rw [allMasks_mem_iff]
      rcases List.mem_cons.mp hm with rfl | hm'
      · simp [zeroMask]
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hm')
        exact hsyn_len q
    have hle := nodup_length_le_of_subset hnd hsub
    rw [List.length_cons, allMasks_length] at hle
    exact hle

  -- Build `wVecs = diffVecs n syn T`: linearly independent, EVERY `w ∈ wVecs` is in `InRowSpace Bx` AND zero outside `T`!
  let wVecs := diffVecs n syn T
  have hT_nd : T.Nodup := nodup_filter _ hqs_nd
  have hwVecs_li : LinIndep wVecs :=
    linIndep_diffVecs n syn T hT_nd (fun q hq => List.mem_range.mp (List.mem_filter.mp hq).1)
  have hwVecs_len : wVecs.length + (dedup (T.map syn)).length = t :=
    diffVecs_length n syn T hT_nd
  have hwVecs_spec : ∀ w ∈ wVecs, InRowSpace Bx w ∧ ∀ q < n, q ∉ T → w.getLsbD q = false := by
    intro w hw
    unfold wVecs diffVecs at hw
    obtain ⟨q, hq_f, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hq_T, hq_nr⟩ := List.mem_filter.mp hq_f
    unfold diffIsNonRep at hq_nr
    unfold diffMkVec
    cases hf : T.find? (fun r => decide (syn r = syn q)) with
    | none => rw [hf] at hq_nr; cases hq_nr
    | some rep =>
      rw [hf] at hq_nr
      have heq : rep ≠ q := of_decide_eq_true hq_nr
      have hrep_T : rep ∈ T := List.mem_of_find?_eq_some hf
      have hq_lt : q < n := List.mem_range.mp (List.mem_filter.mp hq_T).1
      have hrep_lt : rep < n := List.mem_range.mp (List.mem_filter.mp hrep_T).1
      have hsyn_eq : syn rep = syn q := find?_some_eq hf
      refine ⟨?_, ?_⟩
      · rw [hBx_span]
        apply hdx (unitVec n rep ^^^ unitVec n q)
          (by rw [hammingWeight_xor_unitVec hrep_lt hq_lt heq]; omega)
          (by rw [hammingWeight_xor_unitVec hrep_lt hq_lt heq]; omega)
        intro z hzMem
        have hzin : InRowSpace (ext ++ vf) z := (hext_span_hz z).mpr (inRowSpace_mem hzMem)
        rw [commutes_symm]
        apply commutes_inRowSpace hzin
        intro u hu
        rw [commutes_symm, commutes_xor_left, commutes_unitVec hrep_lt, commutes_unitVec hq_lt]
        rcases List.mem_append.mp hu with h1 | h2
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h1
          have hbit := congrArg (fun bs : List Bool => bs.getD j false) hsyn_eq
          simp [syn, List.getD_eq_getElem?_getD, hj] at hbit
          rw [hbit]; cases ext[j].getLsbD q <;> rfl
        · rw [hvf_zero_on_T u h2 rep hrep_T, hvf_zero_on_T u h2 q hq_T]; rfl
      · intro r hr hnotT
        have hr1 : r ≠ rep := fun h => hnotT (h ▸ hrep_T)
        have hr2 : r ≠ q := fun h => hnotT (h ▸ hq_T)
        rw [BitVec.getLsbD_xor, unitVec_getLsbD hrep_lt, unitVec_getLsbD hq_lt]
        simp [hr1, hr2]

  -- Bound `wVecs.length ≤ rX - a1`!
  let locked (i : Nat) : Bool := decide (unitVec rX i ∈ A1)
  let freeIdxs := (List.range rX).filter (fun i => !(locked i))
  let lockedIdxs := (List.range rX).filter locked
  have hlocked_len : lockedIdxs.length = a1 := by
    have hnd_l : (lockedIdxs.map (unitVec rX)).Nodup :=
      nodup_map_of_inj (nodup_filter locked List.nodup_range) (fun i hi j hj heq => by
        have hi' : i < rX := List.mem_range.mp (List.mem_filter.mp hi).1
        have hj' : j < rX := List.mem_range.mp (List.mem_filter.mp hj).1
        have hbit := congrArg (fun v : BitVec rX => v.getLsbD i) heq
        rw [unitVec_getLsbD hi', unitVec_getLsbD hj'] at hbit
        simpa using hbit.symm)
    have hsub1 : ∀ c ∈ lockedIdxs.map (unitVec rX), c ∈ A1 := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    have hsub2 : ∀ c ∈ A1, c ∈ lockedIdxs.map (unitVec rX) := by
      intro c hc
      have hcS1 : c ∈ S1 := (List.mem_filter.mp hc).1
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((mem_dedup _ _).mp hcS1)
      have hw1 : hammingWeight (col q) = 1 := of_decide_eq_true (List.mem_filter.mp hq).2
      have hne : col q ≠ 0 := hcol_ne0 q (List.mem_range.mp (List.mem_filter.mp hq).1)
      obtain ⟨i, hi, hbi⟩ := exists_set_bit_of_ne_zero hne
      have hceq : unitVec rX i = col q := by
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [unitVec_getLsbD hi]
        by_cases hji : j = i
        · subst hji; simp [hbi]
        · simp only [hji, decide_false]
          cases hbj : (col q).getLsbD j
          · rfl
          · exfalso
            rw [hammingWeight_eq_filter] at hw1
            have hmemi : i ∈ (List.range rX).filter (fun t => (col q).getLsbD t) := List.mem_filter.mpr ⟨List.mem_range.mpr hi, hbi⟩
            have hmemj : j ∈ (List.range rX).filter (fun t => (col q).getLsbD t) := List.mem_filter.mpr ⟨List.mem_range.mpr hj, hbj⟩
            have hle := nodup_length_le_of_subset (by simp [Ne.symm hji] : ([i, j] : List Nat).Nodup)
              (fun t ht => by simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with rfl | rfl <;> assumption)
            simp at hle; omega
      refine List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, ?_⟩, hceq⟩
      dsimp only [locked]; rw [hceq]; exact decide_eq_true hc
    have h1 := nodup_length_le_of_subset hnd_l hsub1
    have h2 := nodup_length_le_of_subset (nodup_filter _ (nodup_dedup _)) hsub2
    rw [List.length_map] at h1 h2
    exact Nat.le_antisymm h1 h2
  have hfree_len : freeIdxs.length + a1 = rX := by
    have hsplit : ∀ (xs : List Nat), (xs.filter (fun i => !(locked i))).length + (xs.filter locked).length = xs.length := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ih => cases h : locked x <;> simp [h] <;> omega
    have := hsplit (List.range rX)
    rw [List.length_range] at this
    dsimp only [freeIdxs, lockedIdxs] at hlocked_len ⊢
    omega
  let Bfree := freeIdxs.map (fun i => Bx.getD i 0)
  have hwVecs_in_free : ∀ w ∈ wVecs, InRowSpace Bfree w := by
    intro w hw
    obtain ⟨hwBx, hwZero⟩ := hwVecs_spec w hw
    obtain ⟨m, hml, hmeq⟩ := hwBx
    have hlocked_zero : ∀ i (hi : i < rX), locked i = true → m.getD i false = false := by
      intro i hi hlock
      have hcA1 : unitVec rX i ∈ A1 := of_decide_eq_true hlock
      have hcS1 : unitVec rX i ∈ S1 := (List.mem_filter.mp hcA1).1
      have hge2 : 2 ≤ (qs.filter (fun q => decide (col q = unitVec rX i))).length :=
        of_decide_eq_true (List.mem_filter.mp hcA1).2
      obtain ⟨q, hq, hcol_q⟩ := List.mem_map.mp ((mem_dedup _ _).mp hcS1)
      have hq_qs : q ∈ qs := (List.mem_filter.mp hq).1
      have hq_lt : q < n := List.mem_range.mp hq_qs
      have hq_notT : q ∉ T := by
        intro hqT
        have h1 : (qs.filter (fun r => decide (col r = col q))).length = 1 := of_decide_eq_true (List.mem_filter.mp hqT).2
        rw [hcol_q] at h1; omega
      have hwq0 : w.getLsbD q = false := hwZero q hq_lt hq_notT
      rw [← hmeq, xorSubset_getLsbD] at hwq0
      have hbit_Bx : ∀ j (hj : j < rX), Bx[j].getLsbD q = decide (j = i) := by
        intro j hj
        rw [← hcol_bit q j hj, hcol_q, unitVec_getLsbD hi]
      have hfold_sel : ∀ (k : Nat) (hk : k ≤ rX),
          (List.zip (Bx.take k) (m.take k)).foldl (fun acc pr => if pr.2 then xor acc (pr.1.getLsbD q) else acc) false =
          if i < k then m.getD i false else false := by
        intro k; induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have hkBx : k < Bx.length := by omega
          have hkm : k < m.length := by omega
          have htk1 : Bx.take (k + 1) = Bx.take k ++ [Bx[k]] := List.take_succ_eq_append_getElem hkBx
          have htk2 : m.take (k + 1) = m.take k ++ [m[k]] := List.take_succ_eq_append_getElem hkm
          have hlen_tk : (Bx.take k).length = (m.take k).length := by simp; omega
          rw [htk1, htk2, List.zip_append hlen_tk, List.foldl_append, ih (by omega)]
          simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, hbit_Bx k hkBx]
          by_cases hki : k = i
          · subst hki
            have hgi : m.getD k false = m[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkm]
            have hnotlt : ¬ (k < k) := Nat.lt_irrefl k
            have hlt1 : k < k + 1 := Nat.lt_succ_self k
            simp only [hnotlt, hlt1, ↓reduceIte, decide_true, hgi]
            cases m[k] <;> rfl
          · have hlt : (i < k + 1) ↔ (i < k) := by omega
            simp only [hki, decide_false, hlt]
            cases m[k] <;> cases (if i < k then m.getD i false else false) <;> rfl
      have hres := hfold_sel rX (Nat.le_refl rX)
      have htBx : Bx.take rX = Bx := List.take_of_length_le (Nat.le_refl _)
      have htm : m.take rX = m := List.take_of_length_le (by omega)
      rw [htBx, htm, if_pos hi] at hres
      rw [hres] at hwq0
      exact hwq0
    refine ⟨freeIdxs.map (fun i => m.getD i false), by simp [Bfree], ?_⟩
    rw [← hmeq]
    have hfold_gen : ∀ (k : Nat) (hk : k ≤ rX),
        xorSubset (((List.range k).filter (fun i => !(locked i))).map (fun i => Bx.getD i 0))
                  (((List.range k).filter (fun i => !(locked i))).map (fun i => m.getD i false)) =
        xorSubset (Bx.take k) (m.take k) := by
      intro k; induction k with
      | zero => intro _; simp [xorSubset]
      | succ k ih =>
        intro hk
        have hkBx : k < Bx.length := by omega
        have hkm : k < m.length := by omega
        have htk1 : Bx.take (k + 1) = Bx.take k ++ [Bx[k]] := List.take_succ_eq_append_getElem hkBx
        have htk2 : m.take (k + 1) = m.take k ++ [m[k]] := List.take_succ_eq_append_getElem hkm
        have hlen_tk : (m.take k).length = (Bx.take k).length := by simp; omega
        rw [List.range_succ, List.filter_append, List.map_append, List.map_append,
            xorSubset_append _ _ _ _ (by simp), ih (by omega),
            htk1, htk2, xorSubset_append _ _ _ _ hlen_tk]
        have hgk : Bx.getD k 0 = Bx[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkBx]
        have hmk : m.getD k false = m[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkm]
        cases hlk : locked k
        · simp only [List.filter_cons, List.filter_nil, hlk, Bool.not_false, ↓reduceIte,
                     List.map_cons, List.map_nil, hgk, hmk]
        · have hm0 := hlocked_zero k hkBx hlk
          rw [hmk] at hm0
          simp only [List.filter_cons, List.filter_nil, hlk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                     List.map_nil, xorSubset, hm0]
          apply BitVec.eq_of_getLsbD_eq; intro j _; simp
    have := hfold_gen rX (Nat.le_refl rX)
    have htBx : Bx.take rX = Bx := List.take_of_length_le (Nat.le_refl _)
    have htm : m.take rX = m := List.take_of_length_le (by omega)
    simpa [Bfree, freeIdxs, htBx, htm] using this

  have hwVecs_le : wVecs.length ≤ rX - a1 := by
    have hle := linIndep_le_of_subset hwVecs_li hwVecs_in_free
    simp only [Bfree, List.length_map] at hle
    omega

  -- Final arithmetic contradiction!
  exact arith_contradiction n k rX rZ n1 n2 s1 s2 rExtra t t1 t2 a1 wVecs.length (dedup (T.map syn)).length
    hn hk hr_le hrank_sum hn12 hn2_le h4rX_ge hs1_le_rX hs2_le_n2 hrExtra_le
    ht1_a1 ht1_n1 ht2_n2 ht_eq hsyn_card hwVecs_len hwVecs_le (fun hre0 => by
      cases hTeq : T with
      | nil => simp [t, hTeq]
      | cons q _ =>
        exfalso
        have hmem : syn q ∈ dedup (T.map syn) :=
          (mem_dedup _ _).mpr (List.mem_map.mpr ⟨q, by rw [hTeq]; exact List.mem_cons_self .., rfl⟩)
        have hpos : 0 < (dedup (T.map syn)).length := List.length_pos_of_mem hmem
        have hpow0 : 2 ^ rExtra = 1 := by rw [hre0]
        rw [hpow0] at hsyn_card
        omega)

/-! ## 6. Strong Induction on `n ≤ 15` & Main Theorem -/

private theorem no_css_k4_le15 : ∀ (n : Nat), n ≤ 15 →
    ∀ (k : Nat) (hx hz lx lz : List (BitVec n)),
      4 ≤ k → ¬ IsCSSCode n k 3 4 hx hz lx lz := by
  intro n; induction n with
  | zero =>
    intro _ k hx hz lx lz hk hcss
    obtain ⟨hlx, hlz, _, _, _, _, _, hsymp, _, _⟩ := hcss
    have h0 := hsymp ⟨0, by omega⟩ ⟨0, by omega⟩
    have hc : commutes (lx.getD 0 0) (lz.getD 0 0) = true := by
      unfold commutes; rfl
    rw [hc] at h0; simp at h0
  | succ n ih =>
    intro hn k hx hz lx lz hk hcss
    by_cases hexX : ∃ q < n + 1, InRowSpace hx (unitVec (n + 1) q)
    · obtain ⟨q, hq, hwt1⟩ := hexX
      exact ih (by omega) k _ _ _ _ hk (puncture_of_wt1_x hcss hq hwt1)
    · by_cases hexZ : ∃ q < n + 1, InRowSpace hz (unitVec (n + 1) q)
      · obtain ⟨q, hq, hwt1⟩ := hexZ
        exact ih (by omega) k _ _ _ _ hk (puncture_of_wt1_x (isCSSCode_swap hcss) hq hwt1)
      · exact no_minimal_css_k4 hn hk hcss
          (fun q hq h => hexX ⟨q, hq, h⟩)
          (fun q hq h => hexZ ⟨q, hq, h⟩)

theorem record : ¬ Quantum.Statements.QC_rec_n15_d3_w4.Record 4 := by
  rintro ⟨k, hx, hz, lx, lz, hk, hcss⟩
  exact no_css_k4_le15 15 (Nat.le_refl 15) k hx hz lx lz hk hcss

end Quantum.Claims.QC_rec_n15_d3_w4_not_s4
