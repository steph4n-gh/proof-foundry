import MatMul.Statements.MM_rec_3x3x3_hw

namespace MatMul.Claims.MM_rec_3x3x3_hw_not_s34

open MatMul
open MatMul.Statements.MM_rec_3x3x3_hw

private def parity (x : Int) : Bool := (x % 2 != 0)

private theorem parity_zero : parity 0 = false := by decide
private theorem parity_one : parity 1 = true := by decide

private theorem parity_add (x y : Int) : parity (x + y) = (parity x ^^ parity y) := by
  unfold parity
  have h : (x + y) % 2 = (x % 2 + y % 2) % 2 := Int.add_emod x y 2
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rw [h]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

private theorem parity_mul (x y : Int) : parity (x * y) = (parity x && parity y) := by
  unfold parity
  have h : (x * y) % 2 = ((x % 2) * (y % 2)) % 2 := Int.mul_emod x y 2
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rw [h]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

private theorem parity_unit {x : Int} (h : x = -1 ∨ x = 0 ∨ x = 1) :
    parity x = (x != 0) := by
  rcases h with rfl | rfl | rfl <;> decide

private def xorSum {α : Type} (l : List α) (f : α → Bool) : Bool :=
  l.foldl (fun acc x => acc ^^ f x) false

private theorem foldl_xor_shift {α : Type} (l : List α) (f : α → Bool) (init : Bool) :
    l.foldl (fun acc x => acc ^^ f x) init = (init ^^ xorSum l f) := by
  induction l generalizing init with
  | nil => simp [xorSum]
  | cons x xs ih =>
    unfold xorSum
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (init ^^ f x), ih (f x)]
    cases init <;> cases f x <;> cases xorSum xs f <;> rfl

private theorem xorSum_cons {α : Type} (x : α) (xs : List α) (f : α → Bool) :
    xorSum (x :: xs) f = (f x ^^ xorSum xs f) := by
  unfold xorSum
  simp only [List.foldl_cons, Bool.false_xor]
  exact foldl_xor_shift xs f (f x)

private theorem xorSum_nil {α : Type} (f : α → Bool) : xorSum ([] : List α) f = false := rfl

private theorem xorSum_congr {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : xorSum l f = xorSum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [xorSum_cons, xorSum_cons, h x List.mem_cons_self]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem xorSum_filter_eq {α : Type} (l : List α) (p f : α → Bool)
    (h : ∀ x ∈ l, p x = false → f x = false) :
    xorSum (l.filter p) f = xorSum l f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      rw [xorSum_cons, h x List.mem_cons_self hp, Bool.false_xor]
      exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    · simp only [List.filter_cons, hp, ↓reduceIte]
      rw [xorSum_cons, xorSum_cons]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem xorSum_filter_and {α : Type} (l : List α) (p f : α → Bool) :
    xorSum (l.filter p) f = xorSum l (fun x => p x && f x) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      rw [xorSum_cons, hp, Bool.false_and, Bool.false_xor, ih]
    · simp only [List.filter_cons, hp, ↓reduceIte]
      rw [xorSum_cons, xorSum_cons, hp, Bool.true_and, ih]

private theorem xorSum_xor {α : Type} (l : List α) (f g : α → Bool) :
    xorSum l (fun x => f x ^^ g x) = (xorSum l f ^^ xorSum l g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [xorSum_cons, xorSum_cons, xorSum_cons, ih]
    cases f x <;> cases g x <;> cases xorSum xs f <;> cases xorSum xs g <;> rfl

private theorem xorSum_false {α : Type} (l : List α) : xorSum l (fun _ => false) = false := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [xorSum_cons, Bool.false_xor, ih]

private theorem xorSum_and_const_left {α : Type} (l : List α) (b : Bool) (f : α → Bool) :
    xorSum l (fun x => b && f x) = (b && xorSum l f) := by
  cases b
  · simpa using xorSum_false l
  · simp

private theorem xorSum_and_const_right {α : Type} (l : List α) (f : α → Bool) (b : Bool) :
    xorSum l (fun x => f x && b) = (xorSum l f && b) := by
  cases b
  · simpa using xorSum_false l
  · simp

private theorem xorSum_swap {α β : Type} (la : List α) (lb : List β) (f : α → β → Bool) :
    xorSum la (fun a => xorSum lb (fun b => f a b)) =
    xorSum lb (fun b => xorSum la (fun a => f a b)) := by
  induction la with
  | nil =>
    rw [xorSum_nil]
    symm
    exact xorSum_false lb
  | cons a as ih =>
    rw [xorSum_cons, ih]
    have hstep : xorSum lb (fun b => xorSum (a :: as) (fun x => f x b)) =
                 xorSum lb (fun b => f a b ^^ xorSum as (fun x => f x b)) := by
      apply xorSum_congr
      intro b _
      exact xorSum_cons a as (fun x => f x b)
    rw [hstep, xorSum_xor]

private theorem foldl_int_parity_aux (l : List (Int × (Fin 9 → Int))) (c : Fin 9) (init : Int) :
    parity (l.foldl (fun acc p => acc + p.1 * p.2 c) init) =
    (parity init ^^ xorSum l (fun p => parity p.1 && parity (p.2 c))) := by
  induction l generalizing init with
  | nil => simp [xorSum]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (init + p.1 * p.2 c), xorSum_cons, parity_add, parity_mul]
    cases parity init <;> cases parity p.1 <;> cases parity (p.2 c) <;> cases xorSum ps _ <;> rfl

private theorem parity_coeffInt_unit (s : SchemeInt 3 3 3) (hunit : IsUnitCoeff s)
    (a b c : Fin 9) :
    parity (coeffInt s a b c) =
    xorSum s (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) := by
  unfold coeffInt
  rw [foldl_int_parity_aux, parity_zero, Bool.false_xor]
  induction s with
  | nil => rfl
  | cons t ts ih =>
    have ht := hunit t List.mem_cons_self
    have hts : IsUnitCoeff ts := fun x hx => hunit x (List.mem_cons_of_mem t hx)
    have hrest := ih hts
    have hL := parity_unit (ht.1 a)
    have hR := parity_unit (ht.2.1 b)
    have hO := parity_unit (ht.2.2 c)
    cases hk : (t.left a * t.right b == 0)
    · simp only [List.filterMap_cons, hk, Bool.false_eq_true, ↓reduceIte]
      rw [xorSum_cons, xorSum_cons, hrest, parity_mul, hL, hR, hO]
    · simp only [List.filterMap_cons, hk, ↓reduceIte]
      rw [hrest, xorSum_cons]
      have hzero : ((t.left a != 0) && (t.right b != 0)) = false := by
        have hmul0 : t.left a * t.right b = 0 := beq_iff_eq.mp hk
        rcases ht.1 a with h1 | h1 | h1 <;> rcases ht.2.1 b with h2 | h2 | h2 <;>
          simp [h1, h2] at hmul0 ⊢
      rw [hzero, Bool.false_and, Bool.false_xor]

-- Finite GF(2)^3 linear algebra helpers via BitVec 3 (64 and 512 cases)
private def dot3 (u v : BitVec 3) : Bool :=
  (u.getLsbD 0 && v.getLsbD 0) ^^ (u.getLsbD 1 && v.getLsbD 1) ^^ (u.getLsbD 2 && v.getLsbD 2)

private def vec3Of (f : Fin 3 → Bool) : BitVec 3 :=
  (if f 0 then 1#3 else 0#3) ||| (if f 1 then 2#3 else 0#3) ||| (if f 2 then 4#3 else 0#3)

private theorem vec3Of_getLsbD (f : Fin 3 → Bool) (k : Fin 3) :
    (vec3Of f).getLsbD k.val = f k := by
  have h0 : f 0 = f 0 := rfl
  match k with
  | ⟨0, _⟩ =>
    change (vec3Of f).getLsbD 0 = f 0
    unfold vec3Of
    cases f 0 <;> cases f 1 <;> cases f 2 <;> decide
  | ⟨1, _⟩ =>
    change (vec3Of f).getLsbD 1 = f 1
    unfold vec3Of
    cases f 0 <;> cases f 1 <;> cases f 2 <;> decide
  | ⟨2, _⟩ =>
    change (vec3Of f).getLsbD 2 = f 2
    unfold vec3Of
    cases f 0 <;> cases f 1 <;> cases f 2 <;> decide

private theorem finRange3_eq : List.finRange 3 = [0, 1, 2] := by decide

private theorem dot3_eq_xorSum (f : Fin 3 → Bool) (x : BitVec 3) :
    dot3 (vec3Of f) x = xorSum (List.finRange 3) (fun k => f k && x.getLsbD k.val) := by
  have h0 : (vec3Of f).getLsbD 0 = f 0 := vec3Of_getLsbD f 0
  have h1 : (vec3Of f).getLsbD 1 = f 1 := vec3Of_getLsbD f 1
  have h2 : (vec3Of f).getLsbD 2 = f 2 := vec3Of_getLsbD f 2
  rw [finRange3_eq]
  unfold dot3 xorSum
  rw [h0, h1, h2]
  simp only [List.foldl_cons, List.foldl_nil, Bool.false_xor]
  rfl

private theorem xorSum_finRange3_id :
    ∀ (j : Fin 3) (x : BitVec 3),
      xorSum (List.finRange 3) (fun k => (j == k) && x.getLsbD k.val) = x.getLsbD j.val := by
  decide

private theorem no_inj_pair :
    ∀ v1 v2 : BitVec 3, ∃ x y : BitVec 3,
      x ≠ y ∧ dot3 v1 x = dot3 v1 y ∧ dot3 v2 x = dot3 v2 y := by
  decide

private theorem dual_basis_triple :
    ∀ v1 v2 v3 : BitVec 3,
      (∀ x y : BitVec 3, dot3 v1 x = dot3 v1 y → dot3 v2 x = dot3 v2 y →
        dot3 v3 x = dot3 v3 y → x = y) →
      (∃ x1 : BitVec 3, dot3 v1 x1 = true ∧ dot3 v2 x1 = false ∧ dot3 v3 x1 = false) ∧
      (∃ x2 : BitVec 3, dot3 v1 x2 = false ∧ dot3 v2 x2 = true ∧ dot3 v3 x2 = false) ∧
      (∃ x3 : BitVec 3, dot3 v1 x3 = false ∧ dot3 v2 x3 = false ∧ dot3 v3 x3 = true) := by
  decide

private theorem eq_of_getLsbD_3 {x y : BitVec 3}
    (h : ∀ j : Fin 3, x.getLsbD j.val = y.getLsbD j.val) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i, hi⟩

-- Rank-3 identity slice lemma: any list of rank-1 Bool matrices summing to I_3 has length >= 3
private theorem rank3_len_ge_3 {α : Type} (M : List α)
    (U V : α → Fin 3 → Bool)
    (hI : ∀ j k : Fin 3, xorSum M (fun t => U t j && V t k) = (j == k)) :
    M.length ≥ 3 := by
  have heval : ∀ (x : BitVec 3) (j : Fin 3),
      xorSum M (fun t => U t j && dot3 (vec3Of (V t)) x) = x.getLsbD j.val := by
    intro x j
    have h1 : xorSum M (fun t => U t j && dot3 (vec3Of (V t)) x) =
              xorSum M (fun t => xorSum (List.finRange 3) (fun k => (U t j && V t k) && x.getLsbD k.val)) := by
      apply xorSum_congr
      intro t _
      rw [dot3_eq_xorSum, ← xorSum_and_const_left]
      apply xorSum_congr
      intro k _
      cases U t j <;> cases V t k <;> cases x.getLsbD k.val <;> rfl
    rw [h1, xorSum_swap]
    have h2 : xorSum (List.finRange 3) (fun k => xorSum M (fun t => (U t j && V t k) && x.getLsbD k.val)) =
              xorSum (List.finRange 3) (fun k => (j == k) && x.getLsbD k.val) := by
      apply xorSum_congr
      intro k _
      rw [xorSum_and_const_right, hI j k]
    rw [h2, xorSum_finRange3_id]
  match M with
  | [] =>
    have h0 := heval 1#3 0
    simp [xorSum_nil] at h0
  | [t1] =>
    exfalso
    obtain ⟨x, y, hxy, hd1, _⟩ := no_inj_pair (vec3Of (V t1)) 0#3
    apply hxy
    apply eq_of_getLsbD_3
    intro j
    rw [← heval x j, ← heval y j]
    simp [xorSum_cons, xorSum_nil, hd1]
  | [t1, t2] =>
    exfalso
    obtain ⟨x, y, hxy, hd1, hd2⟩ := no_inj_pair (vec3Of (V t1)) (vec3Of (V t2))
    apply hxy
    apply eq_of_getLsbD_3
    intro j
    rw [← heval x j, ← heval y j]
    simp [xorSum_cons, xorSum_nil, hd1, hd2]
  | _ :: _ :: _ :: _ =>
    simp

-- Tight-degree isolation for length = 3
private theorem tight3_vanish_left {α : Type} (t1 t2 t3 : α)
    (P : α → Fin 9 → Bool) (Q : α → Fin 9 → Bool)
    (rowOf colOf : Fin 3 → Fin 9)
    (hI : ∀ j k : Fin 3, xorSum [t1, t2, t3] (fun t => P t (rowOf j) && Q t (colOf k)) = (j == k))
    (u : Fin 9)
    (h0 : ∀ k : Fin 3, xorSum [t1, t2, t3] (fun t => P t u && Q t (colOf k)) = false) :
    P t1 u = false ∧ P t2 u = false ∧ P t3 u = false := by
  let v1 := vec3Of (fun k => Q t1 (colOf k))
  let v2 := vec3Of (fun k => Q t2 (colOf k))
  let v3 := vec3Of (fun k => Q t3 (colOf k))
  have heval : ∀ (x : BitVec 3) (j : Fin 3),
      xorSum [t1, t2, t3] (fun t => P t (rowOf j) && dot3 (vec3Of (fun k => Q t (colOf k))) x) = x.getLsbD j.val := by
    intro x j
    have h1 : xorSum [t1, t2, t3] (fun t => P t (rowOf j) && dot3 (vec3Of (fun k => Q t (colOf k))) x) =
              xorSum [t1, t2, t3] (fun t => xorSum (List.finRange 3) (fun k => (P t (rowOf j) && Q t (colOf k)) && x.getLsbD k.val)) := by
      apply xorSum_congr
      intro t _
      rw [dot3_eq_xorSum, ← xorSum_and_const_left]
      apply xorSum_congr
      intro k _
      cases P t (rowOf j) <;> cases Q t (colOf k) <;> cases x.getLsbD k.val <;> rfl
    rw [h1, xorSum_swap]
    have h2 : xorSum (List.finRange 3) (fun k => xorSum [t1, t2, t3] (fun t => (P t (rowOf j) && Q t (colOf k)) && x.getLsbD k.val)) =
              xorSum (List.finRange 3) (fun k => (j == k) && x.getLsbD k.val) := by
      apply xorSum_congr
      intro k _
      rw [xorSum_and_const_right, hI j k]
    rw [h2, xorSum_finRange3_id]
  have hinj : ∀ x y : BitVec 3, dot3 v1 x = dot3 v1 y → dot3 v2 x = dot3 v2 y →
      dot3 v3 x = dot3 v3 y → x = y := by
    intro x y hd1 hd2 hd3
    apply eq_of_getLsbD_3
    intro j
    rw [← heval x j, ← heval y j]
    simp only [xorSum_cons, xorSum_nil]
    have h1 : dot3 (vec3Of (fun k => Q t1 (colOf k))) x = dot3 (vec3Of (fun k => Q t1 (colOf k))) y := hd1
    have h2 : dot3 (vec3Of (fun k => Q t2 (colOf k))) x = dot3 (vec3Of (fun k => Q t2 (colOf k))) y := hd2
    have h3 : dot3 (vec3Of (fun k => Q t3 (colOf k))) x = dot3 (vec3Of (fun k => Q t3 (colOf k))) y := hd3
    rw [h1, h2, h3]
  have hzero : ∀ x : BitVec 3,
      (((P t1 u && dot3 v1 x) ^^ (P t2 u && dot3 v2 x)) ^^ (P t3 u && dot3 v3 x)) = false := by
    intro x
    have h1 : xorSum [t1, t2, t3] (fun t => P t u && dot3 (vec3Of (fun k => Q t (colOf k))) x) =
              xorSum [t1, t2, t3] (fun t => xorSum (List.finRange 3) (fun k => (P t u && Q t (colOf k)) && x.getLsbD k.val)) := by
      apply xorSum_congr
      intro t _
      rw [dot3_eq_xorSum, ← xorSum_and_const_left]
      apply xorSum_congr
      intro k _
      cases P t u <;> cases Q t (colOf k) <;> cases x.getLsbD k.val <;> rfl
    have h2 : xorSum [t1, t2, t3] (fun t => P t u && dot3 (vec3Of (fun k => Q t (colOf k))) x) = false := by
      rw [h1, xorSum_swap]
      have h3 : xorSum (List.finRange 3) (fun k => xorSum [t1, t2, t3] (fun t => (P t u && Q t (colOf k)) && x.getLsbD k.val)) =
                xorSum (List.finRange 3) (fun _ => false) := by
        apply xorSum_congr
        intro k _
        rw [xorSum_and_const_right, h0 k, Bool.false_and]
      rw [h3, xorSum_false]
    simp only [xorSum_cons, xorSum_nil, Bool.xor_false] at h2
    have h2' : ((P t1 u && dot3 v1 x) ^^ ((P t2 u && dot3 v2 x) ^^ (P t3 u && dot3 v3 x))) = false := h2
    cases ha : (P t1 u && dot3 v1 x) <;> cases hb : (P t2 u && dot3 v2 x) <;>
      cases hc : (P t3 u && dot3 v3 x) <;> simp [ha, hb, hc] at h2' ⊢
  obtain ⟨⟨x1, hx1a, hx1b, hx1c⟩, ⟨x2, hx2a, hx2b, hx2c⟩, ⟨x3, hx3a, hx3b, hx3c⟩⟩ :=
    dual_basis_triple v1 v2 v3 hinj
  refine ⟨?_, ?_, ?_⟩
  · have h := hzero x1; simp [hx1a, hx1b, hx1c] at h; exact h
  · have h := hzero x2; simp [hx2a, hx2b, hx2c] at h; exact h
  · have h := hzero x3; simp [hx3a, hx3b, hx3c] at h; exact h

-- List counting helpers
private def sumNat {α : Type} (l : List α) (f : α → Nat) : Nat :=
  l.foldl (fun acc x => acc + f x) 0

private theorem foldl_nat_shift {α : Type} (l : List α) (f : α → Nat) (init : Nat) :
    l.foldl (fun acc x => acc + f x) init = init + sumNat l f := by
  induction l generalizing init with
  | nil => simp [sumNat]
  | cons x xs ih =>
    unfold sumNat
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + f x), ih (f x)]
    omega

private theorem sumNat_cons {α : Type} (x : α) (xs : List α) (f : α → Nat) :
    sumNat (x :: xs) f = f x + sumNat xs f := by
  unfold sumNat
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_nat_shift xs f (f x)

private theorem sumNat_nil {α : Type} (f : α → Nat) : sumNat ([] : List α) f = 0 := rfl

private theorem sumNat_add {α : Type} (l : List α) (f g : α → Nat) :
    sumNat l (fun x => f x + g x) = sumNat l f + sumNat l g := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    rw [sumNat_cons, sumNat_cons, sumNat_cons, ih]
    omega

private theorem sumNat_const {α : Type} (l : List α) (c : Nat) :
    sumNat l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    rw [sumNat_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem sumNat_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : sumNat l f ≤ sumNat l g := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    rw [sumNat_cons, sumNat_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private theorem sumNat_congr {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x = g x) : sumNat l f = sumNat l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [sumNat_cons, sumNat_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem sumNat_filter_len {α : Type} (l : List α) (p : α → Bool) :
    sumNat l (fun x => if p x then 1 else 0) = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [sumNat_cons, List.filter_cons, ih]
    cases p x <;> simp <;> omega

private theorem sumNat_swap {α β : Type} (la : List α) (lb : List β) (f : α → β → Nat) :
    sumNat la (fun a => sumNat lb (fun b => f a b)) =
    sumNat lb (fun b => sumNat la (fun a => f a b)) := by
  induction la with
  | nil =>
    rw [sumNat_nil]
    symm
    have h : sumNat lb (fun _ => 0) = 0 := by rw [sumNat_const]; omega
    exact h
  | cons a as ih =>
    rw [sumNat_cons, ih]
    have hstep : sumNat lb (fun b => sumNat (a :: as) (fun x => f x b)) =
                 sumNat lb (fun b => f a b + sumNat as (fun x => f x b)) := by
      apply sumNat_congr
      intro b _
      exact sumNat_cons a as (fun x => f x b)
    rw [hstep, sumNat_add]

private theorem length_filter_split {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases p x <;> simp <;> omega

private theorem filter_len_le_one_of_unique {α : Type} [DecidableEq α] (l : List α) (p : α → Bool)
    (hnd : l.Nodup) (hu : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) :
    (l.filter p).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2 (fun a ha b hb => hu a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
    · simp only [List.filter_cons, hpx, ↓reduceIte]
      have hall : ∀ y ∈ xs, p y = false := by
        intro y hy
        cases hpy : p y
        · rfl
        · have heq := hu x List.mem_cons_self y (List.mem_cons_of_mem x hy) hpx hpy
          subst heq
          exact absurd hy hnd.1
      have hempty : xs.filter p = [] := by
        clear ih hnd hu hpx
        induction xs with
        | nil => rfl
        | cons z zs ih2 =>
          simp only [List.filter_cons, hall z List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]
          exact ih2 (fun y hy => hall y (List.mem_cons_of_mem z hy))
      simp [hempty]

private theorem filter_len_eq_one_of_mem {α : Type} [DecidableEq α] (l : List α) (p : α → Bool)
    (hnd : l.Nodup) (hu : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y)
    (hmem : ∃ x ∈ l, p x = true) :
    (l.filter p).length = 1 := by
  have hle := filter_len_le_one_of_unique l p hnd hu
  obtain ⟨x, hx, hpx⟩ := hmem
  have hge : 1 ≤ (l.filter p).length := by
    have hin : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
    cases h : l.filter p with
    | nil => rw [h] at hin; cases hin
    | cons _ _ => simp
  omega

private theorem nodup_filter {α : Type} {l : List α} {p : α → Bool} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
      exact ih h.2
    · simp only [List.filter_cons, hpx, ↓reduceIte]
      rw [List.nodup_cons]
      refine ⟨fun hmem => h.1 (List.mem_filter.mp hmem).1, ih h.2⟩

private theorem filter_eq_nil_of_all_false {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, h x List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem finRange9_nodup : (List.finRange 9).Nodup := by decide
private theorem finRange9_len : (List.finRange 9).length = 9 := by decide

-- THE UNIFIED DEGREE-SUM LOWER BOUND (>= 30) FOR ANY FACTOR WITH R <= 23!
private theorem unified_degree_sum_ge_30 {α : Type} (L : List α)
    (P Q R : α → Fin 9 → Bool)
    (rowOf colOf : Fin 9 → Fin 3 → Fin 9)
    (hLen : L.length ≤ 23)
    (hNonzero : ∀ t ∈ L, (∃ u : Fin 9, P t u = true) ∧ (∃ v : Fin 9, Q t v = true))
    (hSlice : ∀ z u v : Fin 9,
      xorSum L (fun t => P t u && Q t v && R t z) =
      (List.finRange 3).any (fun j => (u == rowOf z j) && (v == colOf z j)))
    (hRowInj : ∀ z : Fin 9, ∀ j k : Fin 3, rowOf z j = rowOf z k → j = k)
    (hColInj : ∀ z : Fin 9, ∀ j k : Fin 3, colOf z j = colOf z k → j = k)
    (hDisj : ∀ z1 z2 : Fin 9, z1 ≠ z2 →
      (∀ j k : Fin 3, rowOf z1 j ≠ rowOf z2 k) ∨ (∀ j k : Fin 3, colOf z1 j ≠ colOf z2 k)) :
    sumNat (List.finRange 9) (fun z => (L.filter (fun t => R t z)).length) ≥ 30 := by
  have hMatchI : ∀ (z : Fin 9) (j k : Fin 3),
      (List.finRange 3).any (fun m => (rowOf z j == rowOf z m) && (colOf z k == colOf z m)) = (j == k) := by
    intro z j k
    cases hjk : (j == k)
    · simp only [List.any_eq_false]
      intro m _
      by_cases hj : rowOf z j == rowOf z m
      · have hjm : j = m := hRowInj z j m (beq_iff_eq.mp hj)
        subst hjm
        have hne : colOf z k ≠ colOf z j := fun heq => by
          have := hColInj z k j heq
          subst this
          simp at hjk
        have hbf : (colOf z k == colOf z j) = false := beq_false_of_ne hne
        simp [hbf]
      · simp [hj]
    · have heq : j = k := beq_iff_eq.mp hjk
      subst heq
      rw [List.any_eq_true]
      exact ⟨j, List.mem_finRange j, by simp⟩

  -- Step 1: Every z has deg(z) >= 3
  have hdeg_ge3 : ∀ z : Fin 9, (L.filter (fun t => R t z)).length ≥ 3 := by
    intro z
    apply rank3_len_ge_3 (L.filter (fun t => R t z))
      (fun t j => P t (rowOf z j)) (fun t k => Q t (colOf z k))
    intro j k
    rw [xorSum_filter_and]
    have hc : xorSum L (fun t => R t z && (P t (rowOf z j) && Q t (colOf z k))) =
              xorSum L (fun t => P t (rowOf z j) && Q t (colOf z k) && R t z) := by
      apply xorSum_congr
      intro t _
      cases R t z <;> cases P t (rowOf z j) <;> cases Q t (colOf z k) <;> rfl
    rw [hc, hSlice z (rowOf z j) (colOf z k), hMatchI z j k]

  -- Step 2: Tight-degree isolation for any z with deg(z) = 3
  have hIsol : ∀ (z : Fin 9), (L.filter (fun t => R t z)).length = 3 →
      ∀ t ∈ L, R t z = true →
        (∀ u : Fin 9, P t u = true → ∃ j : Fin 3, u = rowOf z j) ∧
        (∀ v : Fin 9, Q t v = true → ∃ k : Fin 3, v = colOf z k) := by
    intro z hdeg3
    have hL3 : ∃ t1 t2 t3, L.filter (fun t => R t z) = [t1, t2, t3] := by
      match h : L.filter (fun t => R t z) with
      | [t1, t2, t3] => exact ⟨t1, t2, t3, rfl⟩
      | [] => rw [h] at hdeg3; simp at hdeg3
      | [_] => rw [h] at hdeg3; simp at hdeg3
      | [_, _] => rw [h] at hdeg3; simp at hdeg3
      | _ :: _ :: _ :: _ :: _ => rw [h] at hdeg3; simp at hdeg3
    obtain ⟨t1, t2, t3, hlist⟩ := hL3
    have hI : ∀ j k : Fin 3, xorSum [t1, t2, t3] (fun t => P t (rowOf z j) && Q t (colOf z k)) = (j == k) := by
      intro j k
      rw [← hlist, xorSum_filter_and]
      have hc : xorSum L (fun t => R t z && (P t (rowOf z j) && Q t (colOf z k))) =
                xorSum L (fun t => P t (rowOf z j) && Q t (colOf z k) && R t z) := by
        apply xorSum_congr; intro t _; cases R t z <;> cases P t (rowOf z j) <;> cases Q t (colOf z k) <;> rfl
      rw [hc, hSlice z (rowOf z j) (colOf z k), hMatchI z j k]
    have hIsolP : ∀ u : Fin 9, (∀ j : Fin 3, u ≠ rowOf z j) →
        P t1 u = false ∧ P t2 u = false ∧ P t3 u = false := by
      intro u hu
      apply tight3_vanish_left t1 t2 t3 P Q (rowOf z) (colOf z) hI u
      intro k
      rw [← hlist, xorSum_filter_and]
      have hc : xorSum L (fun t => R t z && (P t u && Q t (colOf z k))) =
                xorSum L (fun t => P t u && Q t (colOf z k) && R t z) := by
        apply xorSum_congr; intro t _; cases R t z <;> cases P t u <;> cases Q t (colOf z k) <;> rfl
      rw [hc, hSlice z u (colOf z k)]
      rw [List.any_eq_false]
      intro m _
      have hne : (u == rowOf z m) = false := beq_false_of_ne (hu m)
      simp [hne]
    have hIswap : ∀ j k : Fin 3, xorSum [t1, t2, t3] (fun t => Q t (colOf z j) && P t (rowOf z k)) = (j == k) := by
      intro j k
      have hc : xorSum [t1, t2, t3] (fun t => Q t (colOf z j) && P t (rowOf z k)) =
                xorSum [t1, t2, t3] (fun t => P t (rowOf z k) && Q t (colOf z j)) := by
        apply xorSum_congr; intro t _; exact Bool.and_comm _ _
      rw [hc, hI k j]
      cases hkj : (k == j)
      · have hne : k ≠ j := fun h => by subst h; simp at hkj
        exact (beq_false_of_ne (Ne.symm hne)).symm
      · have heq : k = j := beq_iff_eq.mp hkj; subst heq; simp
    have hIsolQ : ∀ v : Fin 9, (∀ k : Fin 3, v ≠ colOf z k) →
        Q t1 v = false ∧ Q t2 v = false ∧ Q t3 v = false := by
      intro v hv
      apply tight3_vanish_left t1 t2 t3 Q P (colOf z) (rowOf z) hIswap v
      intro j
      have hc : xorSum [t1, t2, t3] (fun t => Q t v && P t (rowOf z j)) =
                xorSum L (fun t => P t (rowOf z j) && Q t v && R t z) := by
        rw [← hlist, xorSum_filter_and]
        apply xorSum_congr; intro t _; cases R t z <;> cases P t (rowOf z j) <;> cases Q t v <;> rfl
      rw [hc, hSlice z (rowOf z j) v, List.any_eq_false]
      intro m _
      have hne : (v == colOf z m) = false := beq_false_of_ne (hv m)
      simp [hne]
    intro t ht hRtz
    have hmem : t ∈ [t1, t2, t3] := by
      rw [← hlist]
      exact List.mem_filter.mpr ⟨ht, hRtz⟩
    have hcases : t = t1 ∨ t = t2 ∨ t = t3 := by simpa using hmem
    constructor
    · intro u hPtu
      by_cases h0 : u = rowOf z 0
      · exact ⟨0, h0⟩
      · by_cases h1 : u = rowOf z 1
        · exact ⟨1, h1⟩
        · by_cases h2 : u = rowOf z 2
          · exact ⟨2, h2⟩
          · exfalso
            have hne : ∀ j : Fin 3, u ≠ rowOf z j := fun j =>
              match j with | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2
            obtain ⟨ha, hb, hc⟩ := hIsolP u hne
            rcases hcases with rfl | rfl | rfl <;> simp_all
    · intro v hQtv
      by_cases h0 : v = colOf z 0
      · exact ⟨0, h0⟩
      · by_cases h1 : v = colOf z 1
        · exact ⟨1, h1⟩
        · by_cases h2 : v = colOf z 2
          · exact ⟨2, h2⟩
          · exfalso
            have hne : ∀ k : Fin 3, v ≠ colOf z k := fun k =>
              match k with | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2
            obtain ⟨ha, hb, hc⟩ := hIsolQ v hne
            rcases hcases with rfl | rfl | rfl <;> simp_all

  -- Step 3: Let U be the list of z : Fin 9 with deg(z) = 3. Prove U.length <= 6!
  let U := (List.finRange 9).filter (fun z => (L.filter (fun t => R t z)).length == 3)
  have hU_nodup : U.Nodup := nodup_filter finRange9_nodup
  have hU_unique : ∀ t ∈ L, ∀ z1 ∈ U, ∀ z2 ∈ U, R t z1 = true → R t z2 = true → z1 = z2 := by
    intro t ht z1 hz1 z2 hz2 hR1 hR2
    exact Decidable.byContradiction fun hne => by
      have hdeg1 : (L.filter (fun s => R s z1)).length = 3 :=
        beq_iff_eq.mp (List.mem_filter.mp hz1).2
      have hdeg2 : (L.filter (fun s => R s z2)).length = 3 :=
        beq_iff_eq.mp (List.mem_filter.mp hz2).2
      obtain ⟨hP1, hQ1⟩ := hIsol z1 hdeg1 t ht hR1
      obtain ⟨hP2, hQ2⟩ := hIsol z2 hdeg2 t ht hR2
      obtain ⟨⟨u, hPtu⟩, ⟨v, hQtv⟩⟩ := hNonzero t ht
      obtain ⟨j1, hj1⟩ := hP1 u hPtu
      obtain ⟨j2, hj2⟩ := hP2 u hPtu
      obtain ⟨k1, hk1⟩ := hQ1 v hQtv
      obtain ⟨k2, hk2⟩ := hQ2 v hQtv
      rcases hDisj z1 z2 hne with hrow | hcol
      · exact hrow j1 j2 (hj1.symm.trans hj2)
      · exact hcol k1 k2 (hk1.symm.trans hk2)

  let inU : α → Bool := fun t => U.any (fun z => R t z)

  -- Double counting: (L.filter inU).length = 3 * U.length
  have hDouble : (L.filter inU).length = 3 * U.length := by
    have hLHS : sumNat U (fun z => (L.filter (fun t => R t z)).length) = 3 * U.length := by
      have hcongr : sumNat U (fun z => (L.filter (fun t => R t z)).length) = sumNat U (fun _ => 3) := by
        apply sumNat_congr
        intro z hz
        exact beq_iff_eq.mp (List.mem_filter.mp hz).2
      rw [hcongr, sumNat_const]
      omega
    have hSwap : sumNat U (fun z => (L.filter (fun t => R t z)).length) =
                 sumNat L (fun t => (U.filter (fun z => R t z)).length) := by
      have h1 : sumNat U (fun z => (L.filter (fun t => R t z)).length) =
                sumNat U (fun z => sumNat L (fun t => if R t z then 1 else 0)) := by
        apply sumNat_congr; intro z _; exact (sumNat_filter_len L (fun t => R t z)).symm
      have h2 : sumNat L (fun t => (U.filter (fun z => R t z)).length) =
                sumNat L (fun t => sumNat U (fun z => if R t z then 1 else 0)) := by
        apply sumNat_congr; intro t _; exact (sumNat_filter_len U (fun z => R t z)).symm
      rw [h1, h2, sumNat_swap]
    have hRHS : sumNat L (fun t => (U.filter (fun z => R t z)).length) = (L.filter inU).length := by
      rw [← sumNat_filter_len L inU]
      apply sumNat_congr
      intro t ht
      cases hin : inU t
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnone : ∀ z ∈ U, R t z = false := by
          intro z hz
          have hfalse : U.any (fun z => R t z) = false := hin
          exact Bool.eq_false_iff.mpr (List.any_eq_false.mp hfalse z hz)
        have hempty : U.filter (fun z => R t z) = [] :=
          filter_eq_nil_of_all_false U (fun z => R t z) hnone
        rw [hempty]; rfl
      · simp only [↓reduceIte]
        have hex : ∃ z ∈ U, R t z = true := List.any_eq_true.mp hin
        exact filter_len_eq_one_of_mem U (fun z => R t z) hU_nodup (hU_unique t ht) hex
    omega

  have hFiltLe : (L.filter inU).length ≤ L.length := by
    have := length_filter_split L inU
    omega
  have hU_lt9 : U.length < 9 := by omega

  -- There exists z0 : Fin 9 with z0 ∉ U (from (finRange 9).filter (!p) being non-empty)
  let notU := (List.finRange 9).filter (fun z => !((L.filter (fun t => R t z)).length == 3))
  have hNotU_pos : notU.length > 0 := by
    have hsp := length_filter_split (List.finRange 9) (fun z => (L.filter (fun t => R t z)).length == 3)
    rw [finRange9_len] at hsp
    change U.length + notU.length = 9 at hsp
    omega
  have hex_z0 : ∃ z0 : Fin 9, z0 ∉ U := by
    cases h : notU with
    | nil => rw [h] at hNotU_pos; simp at hNotU_pos
    | cons z0 _ =>
      have hmem : z0 ∈ notU := by rw [h]; exact List.mem_cons_self
      have hcond := (List.mem_filter.mp hmem).2
      refine ⟨z0, fun hzU => ?_⟩
      have hcond2 := (List.mem_filter.mp hzU).2
      simp [hcond2] at hcond
  obtain ⟨z0, hz0_notU⟩ := hex_z0

  -- Every t ∈ L with inU t = true vanishes on (rowOf z0 j, colOf z0 k)!
  have hVanish_inU : ∀ t ∈ L, inU t = true → ∀ j k : Fin 3,
      (P t (rowOf z0 j) && Q t (colOf z0 k)) = false := by
    intro t ht hin j k
    obtain ⟨z, hzU, hRtz⟩ := List.any_eq_true.mp hin
    have hne : z ≠ z0 := fun heq => hz0_notU (heq ▸ hzU)
    have hdegz : (L.filter (fun s => R s z)).length = 3 :=
      beq_iff_eq.mp (List.mem_filter.mp hzU).2
    obtain ⟨hPz, hQz⟩ := hIsol z hdegz t ht hRtz
    rcases hDisj z z0 hne with hrow | hcol
    · cases hP : P t (rowOf z0 j)
      · rfl
      · obtain ⟨j', hj'⟩ := hPz (rowOf z0 j) hP
        exact absurd hj'.symm (hrow j' j)
    · cases hQ : Q t (colOf z0 k)
      · simp
      · obtain ⟨k', hk'⟩ := hQz (colOf z0 k) hQ
        exact absurd hk'.symm (hcol k' k)

  -- Therefore L.filter (fun t => !inU t) still computes the I_3 slice at z0!
  have hRem_ge3 : (L.filter (fun t => !inU t)).length ≥ 3 := by
    apply rank3_len_ge_3 (L.filter (fun t => !inU t))
      (fun t j => P t (rowOf z0 j) && R t z0) (fun t k => Q t (colOf z0 k))
    intro j k
    have hfilt : xorSum (L.filter (fun t => !inU t)) (fun t => (P t (rowOf z0 j) && R t z0) && Q t (colOf z0 k)) =
                 xorSum L (fun t => (P t (rowOf z0 j) && R t z0) && Q t (colOf z0 k)) := by
      apply xorSum_filter_eq
      intro t ht hnot
      have hin : inU t = true := by
        cases h : inU t
        · rw [h] at hnot; cases hnot
        · rfl
      have hv := hVanish_inU t ht hin j k
      cases hp : P t (rowOf z0 j) <;> cases hq : Q t (colOf z0 k) <;>
        simp [hp, hq] at hv ⊢
    rw [hfilt]
    have hc : xorSum L (fun t => (P t (rowOf z0 j) && R t z0) && Q t (colOf z0 k)) =
              xorSum L (fun t => P t (rowOf z0 j) && Q t (colOf z0 k) && R t z0) := by
      apply xorSum_congr; intro t _; cases P t (rowOf z0 j) <;> cases Q t (colOf z0 k) <;> cases R t z0 <;> rfl
    rw [hc, hSlice z0 (rowOf z0 j) (colOf z0 k), hMatchI z0 j k]

  have hSplit := length_filter_split L inU
  have hU_le6 : U.length ≤ 6 := by omega

  -- Step 4: Sum of degrees >= 3 * U.length + 4 * (9 - U.length) = 36 - U.length >= 30!
  have hLB : sumNat (List.finRange 9) (fun z => if ((L.filter (fun t => R t z)).length == 3) then 3 else 4) ≤
             sumNat (List.finRange 9) (fun z => (L.filter (fun t => R t z)).length) := by
    apply sumNat_le
    intro z _
    have h3 := hdeg_ge3 z
    cases heq : ((L.filter (fun t => R t z)).length == 3)
    · have hne : (L.filter (fun t => R t z)).length ≠ 3 := fun h => by simp [h] at heq
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte]
      omega
  have hSum34 :
      sumNat (List.finRange 9) (fun z => if ((L.filter (fun t => R t z)).length == 3) then 3 else 4) +
      sumNat (List.finRange 9) (fun z => if ((L.filter (fun t => R t z)).length == 3) then 1 else 0) = 36 := by
    rw [← sumNat_add]
    have h4 : sumNat (List.finRange 9) (fun z =>
        (if ((L.filter (fun t => R t z)).length == 3) then 3 else 4) +
        (if ((L.filter (fun t => R t z)).length == 3) then 1 else 0)) =
        sumNat (List.finRange 9) (fun _ => 4) := by
      apply sumNat_congr
      intro z _
      cases ((L.filter (fun t => R t z)).length == 3) <;> rfl
    rw [h4, sumNat_const, finRange9_len]
  have hU_cnt : sumNat (List.finRange 9) (fun z => if ((L.filter (fun t => R t z)).length == 3) then 1 else 0) = U.length :=
    sumNat_filter_len (List.finRange 9) (fun z => (L.filter (fun t => R t z)).length == 3)
  omega

-- Three coordinate-slice maps for C, A, B
private def rowC (c : Fin 9) (j : Fin 3) : Fin 9 := ⟨(c.val / 3) * 3 + j.val, by omega⟩
private def colC (c : Fin 9) (j : Fin 3) : Fin 9 := ⟨j.val * 3 + c.val % 3, by omega⟩

private def rowA (a : Fin 9) (k : Fin 3) : Fin 9 := ⟨(a.val % 3) * 3 + k.val, by omega⟩
private def colA (a : Fin 9) (k : Fin 3) : Fin 9 := ⟨(a.val / 3) * 3 + k.val, by omega⟩

private def rowB (b : Fin 9) (i : Fin 3) : Fin 9 := ⟨i.val * 3 + b.val / 3, by omega⟩
private def colB (b : Fin 9) (i : Fin 3) : Fin 9 := ⟨i.val * 3 + b.val % 3, by omega⟩

private theorem contributes_eq_C : ∀ c a b : Fin 9,
    contributes (m := 3) (n := 3) (p := 3) a b c =
    (List.finRange 3).any (fun j => (a == rowC c j) && (b == colC c j)) := by decide

private theorem contributes_eq_A : ∀ a b c : Fin 9,
    contributes (m := 3) (n := 3) (p := 3) a b c =
    (List.finRange 3).any (fun k => (b == rowA a k) && (c == colA a k)) := by decide

private theorem contributes_eq_B : ∀ b a c : Fin 9,
    contributes (m := 3) (n := 3) (p := 3) a b c =
    (List.finRange 3).any (fun i => (a == rowB b i) && (c == colB b i)) := by decide

private theorem rowC_inj : ∀ z : Fin 9, ∀ j k : Fin 3, rowC z j = rowC z k → j = k := by decide
private theorem colC_inj : ∀ z : Fin 9, ∀ j k : Fin 3, colC z j = colC z k → j = k := by decide
private theorem disjC : ∀ z1 z2 : Fin 9, z1 ≠ z2 →
    (∀ j k : Fin 3, rowC z1 j ≠ rowC z2 k) ∨ (∀ j k : Fin 3, colC z1 j ≠ colC z2 k) := by decide

private theorem rowA_inj : ∀ z : Fin 9, ∀ j k : Fin 3, rowA z j = rowA z k → j = k := by decide
private theorem colA_inj : ∀ z : Fin 9, ∀ j k : Fin 3, colA z j = colA z k → j = k := by decide
private theorem disjA : ∀ z1 z2 : Fin 9, z1 ≠ z2 →
    (∀ j k : Fin 3, rowA z1 j ≠ rowA z2 k) ∨ (∀ j k : Fin 3, colA z1 j ≠ colA z2 k) := by decide

private theorem rowB_inj : ∀ z : Fin 9, ∀ j k : Fin 3, rowB z j = rowB z k → j = k := by decide
private theorem colB_inj : ∀ z : Fin 9, ∀ j k : Fin 3, colB z j = colB z k → j = k := by decide
private theorem disjB : ∀ z1 z2 : Fin 9, z1 ≠ z2 →
    (∀ j k : Fin 3, rowB z1 j ≠ rowB z2 k) ∨ (∀ j k : Fin 3, colB z1 j ≠ colB z2 k) := by decide

-- Connecting nnz and schemeAdditions to sumNat
private theorem nnz_eq_sumNat (v : Fin 9 → Int) :
    nnz v = sumNat (List.finRange 9) (fun i => if v i != 0 then 1 else 0) := by
  unfold nnz sumNat
  suffices h : ∀ (l : List (Fin 9)) (acc : Nat),
      l.foldl (fun acc i => if v i == 0 then acc else acc + 1) acc =
      l.foldl (fun acc i => acc + if v i != 0 then 1 else 0) acc by
    exact h (List.finRange 9) 0
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons i is ih =>
    intro acc
    simp only [List.foldl_cons]
    have hstep : (if v i == 0 then acc else acc + 1) = acc + if v i != 0 then 1 else 0 := by
      cases hv : (v i == 0) <;> simp [bne, hv]
    rw [hstep, ih]

private theorem exists_nz_of_nnz_pos {v : Fin 9 → Int} (h : nnz v ≠ 0) :
    ∃ i : Fin 9, (v i != 0) = true := by
  rw [nnz_eq_sumNat, sumNat_filter_len] at h
  cases hf : (List.finRange 9).filter (fun i => v i != 0) with
  | nil => rw [hf] at h; exact absurd rfl h
  | cons i _ =>
    have hmem : i ∈ (List.finRange 9).filter (fun i => v i != 0) := by rw [hf]; exact List.mem_cons_self
    exact ⟨i, (List.mem_filter.mp hmem).2⟩

private theorem all_zero_of_nnz_zero {v : Fin 9 → Int} (h : nnz v = 0) (i : Fin 9) :
    (v i != 0) = false := by
  cases hv : (v i != 0)
  · rfl
  · exfalso
    have hin : i ∈ (List.finRange 9).filter (fun k => v k != 0) :=
      List.mem_filter.mpr ⟨List.mem_finRange i, hv⟩
    rw [nnz_eq_sumNat, sumNat_filter_len] at h
    cases hf : (List.finRange 9).filter (fun k => v k != 0) with
    | nil => rw [hf] at hin; cases hin
    | cons _ _ => rw [hf] at h; simp at h

private theorem foldl_add_assoc {α : Type} (l : List α) (f g : α → Nat) (init : Nat) :
    l.foldl (fun acc x => acc + f x + g x) init =
    l.foldl (fun acc x => acc + (f x + g x)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, Nat.add_assoc]
    exact ih (init + (f x + g x))

private theorem schemeAdditions_eq_sumNat (s : SchemeInt 3 3 3) :
    schemeAdditions s =
      sumNat s (fun t => (nnz t.left - 1) + (nnz t.right - 1)) +
      sumNat (List.finRange 9) (fun k => (s.filter (fun t => t.output k != 0)).length - 1) := by
  unfold schemeAdditions sumNat
  rw [foldl_add_assoc]

private theorem filter_sub_le_sumNat {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    sumNat (l.filter p) f ≤ sumNat l f := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
      rw [sumNat_cons]; omega
    · simp only [List.filter_cons, hpx, ↓reduceIte]
      rw [sumNat_cons, sumNat_cons]; omega

private theorem filter_filter_len_le {α : Type} (l : List α) (p q : α → Bool) :
    ((l.filter p).filter q).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases hpx : p x <;> cases hqx : q x <;>
      simp only [List.filter_cons, hpx, hqx, Bool.false_eq_true, ↓reduceIte, List.length_cons]
    all_goals omega

private theorem filter_len_le {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length ≤ l.length := by
  have := length_filter_split l p
  omega

theorem record : ¬ MatMul.Statements.MM_rec_3x3x3_hw.Record 34 := by
  rintro ⟨S, hlen, hunit, hadd, hvalid⟩
  let active : Term Int 3 3 3 → Bool := fun t =>
    (nnz t.left != 0) && (nnz t.right != 0) && (nnz t.output != 0)
  let S' := S.filter active
  have hlen' : S'.length ≤ 23 := Nat.le_trans (filter_len_le S active) hlen
  have hadd' : schemeAdditions S' ≤ schemeAdditions S := by
    rw [schemeAdditions_eq_sumNat, schemeAdditions_eq_sumNat]
    have h1 : sumNat S' (fun t => (nnz t.left - 1) + (nnz t.right - 1)) ≤
              sumNat S (fun t => (nnz t.left - 1) + (nnz t.right - 1)) :=
      filter_sub_le_sumNat S active (fun t => (nnz t.left - 1) + (nnz t.right - 1))
    have h2 : sumNat (List.finRange 9) (fun k => (S'.filter (fun t => t.output k != 0)).length - 1) ≤
              sumNat (List.finRange 9) (fun k => (S.filter (fun t => t.output k != 0)).length - 1) := by
      apply sumNat_le
      intro k _
      have hk : (S'.filter (fun t => t.output k != 0)).length ≤ (S.filter (fun t => t.output k != 0)).length :=
        filter_filter_len_le S active (fun t => t.output k != 0)
      omega
    omega
  have hGF2 : ∀ a b c : Fin 9,
      xorSum S' (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) =
      contributes (m := 3) (n := 3) (p := 3) a b c := by
    intro a b c
    have hS := parity_coeffInt_unit S hunit a b c
    rw [hvalid a b c] at hS
    have hpar : parity (if contributes (m := 3) (n := 3) (p := 3) a b c then 1 else 0) =
                contributes (m := 3) (n := 3) (p := 3) a b c := by
      cases contributes (m := 3) (n := 3) (p := 3) a b c <;> decide
    rw [hpar] at hS
    have hfilt : xorSum S' (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) =
                 xorSum S (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) := by
      apply xorSum_filter_eq
      intro t _ hinact
      have hzero : nnz t.left = 0 ∨ nnz t.right = 0 ∨ nnz t.output = 0 := by
        dsimp only [active] at hinact
        cases h1 : (nnz t.left != 0) <;> cases h2 : (nnz t.right != 0) <;> cases h3 : (nnz t.output != 0)
        all_goals simp_all [bne]
      rcases hzero with hz | hz | hz
      · rw [all_zero_of_nnz_zero hz a]; rfl
      · rw [all_zero_of_nnz_zero hz b]; simp
      · rw [all_zero_of_nnz_zero hz c]; simp
    exact hfilt.trans hS.symm
  have hActive_mem : ∀ t ∈ S', nnz t.left ≠ 0 ∧ nnz t.right ≠ 0 ∧ nnz t.output ≠ 0 := by
    intro t ht
    have ha := (List.mem_filter.mp ht).2
    dsimp only [active] at ha
    cases h1 : (nnz t.left != 0) <;> cases h2 : (nnz t.right != 0) <;> cases h3 : (nnz t.output != 0)
    all_goals simp_all [bne]

  -- Apply unified_degree_sum_ge_30 to all three factors C, A, B!
  have hDegC : sumNat (List.finRange 9) (fun c => (S'.filter (fun t => t.output c != 0)).length) ≥ 30 := by
    apply unified_degree_sum_ge_30 S'
      (fun t a => t.left a != 0) (fun t b => t.right b != 0) (fun t c => t.output c != 0)
      rowC colC hlen'
    · intro t ht
      obtain ⟨hL, hR, _⟩ := hActive_mem t ht
      exact ⟨exists_nz_of_nnz_pos hL, exists_nz_of_nnz_pos hR⟩
    · intro c a b
      rw [hGF2 a b c, contributes_eq_C]
    · exact rowC_inj
    · exact colC_inj
    · exact disjC

  have hDegA : sumNat (List.finRange 9) (fun a => (S'.filter (fun t => t.left a != 0)).length) ≥ 30 := by
    apply unified_degree_sum_ge_30 S'
      (fun t b => t.right b != 0) (fun t c => t.output c != 0) (fun t a => t.left a != 0)
      rowA colA hlen'
    · intro t ht
      obtain ⟨_, hR, hO⟩ := hActive_mem t ht
      exact ⟨exists_nz_of_nnz_pos hR, exists_nz_of_nnz_pos hO⟩
    · intro a b c
      have hc : xorSum S' (fun t => (t.right b != 0) && (t.output c != 0) && (t.left a != 0)) =
                xorSum S' (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) := by
        apply xorSum_congr; intro t _; cases t.left a != 0 <;> cases t.right b != 0 <;> cases t.output c != 0 <;> rfl
      rw [hc, hGF2 a b c, contributes_eq_A]
    · exact rowA_inj
    · exact colA_inj
    · exact disjA

  have hDegB : sumNat (List.finRange 9) (fun b => (S'.filter (fun t => t.right b != 0)).length) ≥ 30 := by
    apply unified_degree_sum_ge_30 S'
      (fun t a => t.left a != 0) (fun t c => t.output c != 0) (fun t b => t.right b != 0)
      rowB colB hlen'
    · intro t ht
      obtain ⟨hL, _, hO⟩ := hActive_mem t ht
      exact ⟨exists_nz_of_nnz_pos hL, exists_nz_of_nnz_pos hO⟩
    · intro b a c
      have hc : xorSum S' (fun t => (t.left a != 0) && (t.output c != 0) && (t.right b != 0)) =
                xorSum S' (fun t => (t.left a != 0) && (t.right b != 0) && (t.output c != 0)) := by
        apply xorSum_congr; intro t _; cases t.left a != 0 <;> cases t.right b != 0 <;> cases t.output c != 0 <;> rfl
      rw [hc, hGF2 a b c, contributes_eq_B]
    · exact rowB_inj
    · exact colB_inj
    · exact disjB

  have hSumL : sumNat S' (fun t => nnz t.left) =
      sumNat (List.finRange 9) (fun a => (S'.filter (fun t => t.left a != 0)).length) := by
    have h1 : sumNat S' (fun t => nnz t.left) =
              sumNat S' (fun t => sumNat (List.finRange 9) (fun a => if t.left a != 0 then 1 else 0)) := by
      apply sumNat_congr; intro t _; exact nnz_eq_sumNat t.left
    have h2 : sumNat (List.finRange 9) (fun a => (S'.filter (fun t => t.left a != 0)).length) =
              sumNat (List.finRange 9) (fun a => sumNat S' (fun t => if t.left a != 0 then 1 else 0)) := by
      apply sumNat_congr; intro a _; exact (sumNat_filter_len S' (fun t => t.left a != 0)).symm
    rw [h1, h2, sumNat_swap]

  have hSumR : sumNat S' (fun t => nnz t.right) =
      sumNat (List.finRange 9) (fun b => (S'.filter (fun t => t.right b != 0)).length) := by
    have h1 : sumNat S' (fun t => nnz t.right) =
              sumNat S' (fun t => sumNat (List.finRange 9) (fun b => if t.right b != 0 then 1 else 0)) := by
      apply sumNat_congr; intro t _; exact nnz_eq_sumNat t.right
    have h2 : sumNat (List.finRange 9) (fun b => (S'.filter (fun t => t.right b != 0)).length) =
              sumNat (List.finRange 9) (fun b => sumNat S' (fun t => if t.right b != 0 then 1 else 0)) := by
      apply sumNat_congr; intro b _; exact (sumNat_filter_len S' (fun t => t.right b != 0)).symm
    rw [h1, h2, sumNat_swap]

  have hAddLR : sumNat S' (fun t => (nnz t.left - 1) + (nnz t.right - 1)) + 2 * S'.length =
      sumNat S' (fun t => nnz t.left) + sumNat S' (fun t => nnz t.right) := by
    have hc : 2 * S'.length = sumNat S' (fun _ => 2) := by
      rw [sumNat_const]; omega
    rw [hc, ← sumNat_add, ← sumNat_add]
    apply sumNat_congr
    intro t ht
    obtain ⟨hL, hR, _⟩ := hActive_mem t ht
    omega

  have hAddO : sumNat (List.finRange 9) (fun k => (S'.filter (fun t => t.output k != 0)).length - 1) + 9 ≥
      sumNat (List.finRange 9) (fun k => (S'.filter (fun t => t.output k != 0)).length) := by
    have h1 : sumNat (List.finRange 9) (fun _ => 1) = 9 := by
      rw [sumNat_const, finRange9_len]
    have h2 : sumNat (List.finRange 9) (fun k => (S'.filter (fun t => t.output k != 0)).length) ≤
              sumNat (List.finRange 9) (fun k => ((S'.filter (fun t => t.output k != 0)).length - 1) + 1) := by
      apply sumNat_le; intro k _; omega
    rw [sumNat_add, h1] at h2
    exact h2

  rw [schemeAdditions_eq_sumNat] at hadd'
  omega

end MatMul.Claims.MM_rec_3x3x3_hw_not_s34
