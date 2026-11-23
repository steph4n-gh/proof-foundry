import Std

namespace PFOracle

structure Dyadic where
  m : Int
  e : Int

def Dyadic.value (d : Dyadic) : Rat :=
  (d.m : Rat) * (2 : Rat) ^ d.e

def dyadicAdd (a b : Dyadic) : Dyadic :=
  if a.m = 0 then b
  else if b.m = 0 then a
  else if a.e ≤ b.e then
    ⟨a.m + b.m * 2 ^ (b.e - a.e).toNat, a.e⟩
  else
    ⟨a.m * 2 ^ (a.e - b.e).toNat + b.m, b.e⟩

def dyadicSub (a b : Dyadic) : Dyadic :=
  dyadicAdd a ⟨-b.m, b.e⟩

def dyadicMul (a b : Dyadic) : Dyadic :=
  if a.m = 0 ∨ b.m = 0 then ⟨0, 0⟩
  else ⟨a.m * b.m, a.e + b.e⟩

def dyadicEq (a b : Dyadic) : Bool :=
  (dyadicSub a b).m == 0

def dyadicSign (a : Dyadic) : Int :=
  if 0 < a.m then 1 else if a.m < 0 then -1 else 0

def rationalSign (a : Rat) : Int :=
  if 0 < a then 1 else if a < 0 then -1 else 0

private theorem dyadic_shift {e f : Int} (h : e ≤ f) :
    (2 : Rat) ^ (f - e).toNat * (2 : Rat) ^ e = (2 : Rat) ^ f := by
  rw [← Rat.zpow_natCast, ← Rat.zpow_add (by decide)]
  congr 1
  omega

theorem dyadicAdd_sound (a b : Dyadic) :
    (dyadicAdd a b).value = a.value + b.value := by
  unfold dyadicAdd
  split
  · simp [Dyadic.value, *, Rat.zero_add]
  split
  · simp [Dyadic.value, *, Rat.add_zero]
  split
  · simp only [Dyadic.value, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_ofNat, Rat.add_mul,
      Rat.mul_assoc, dyadic_shift ‹a.e ≤ b.e›]
  · simp only [Dyadic.value, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_pow, Rat.intCast_ofNat, Rat.add_mul,
      Rat.mul_assoc, dyadic_shift (Int.le_of_lt (Int.lt_of_not_ge ‹¬ a.e ≤ b.e›))]

theorem dyadicSub_sound (a b : Dyadic) :
    (dyadicSub a b).value = a.value - b.value := by
  rw [dyadicSub, dyadicAdd_sound, Rat.sub_eq_add_neg]
  simp [Dyadic.value, Rat.neg_mul]

theorem dyadicMul_sound (a b : Dyadic) :
    (dyadicMul a b).value = a.value * b.value := by
  unfold dyadicMul
  split
  · rcases ‹a.m = 0 ∨ b.m = 0› with h | h <;> simp [Dyadic.value, h]
  · simp only [Dyadic.value, Rat.intCast_mul, Rat.zpow_add (by decide : (2 : Rat) ≠ 0)]
    grind

private theorem dyadicValue_zero_iff (a : Dyadic) : a.value = 0 ↔ a.m = 0 := by
  have hp : 0 < (2 : Rat) ^ a.e := Rat.zpow_pos (by decide)
  simp [Dyadic.value, Rat.mul_eq_zero, Rat.ne_of_gt hp]

theorem dyadicEq_iff (a b : Dyadic) : dyadicEq a b = true ↔ a.value = b.value := by
  simp only [dyadicEq, beq_iff_eq, ← dyadicValue_zero_iff, dyadicSub_sound]
  grind

theorem dyadicSign_sound (a : Dyadic) : dyadicSign a = rationalSign a.value := by
  have hp : 0 < (2 : Rat) ^ a.e := Rat.zpow_pos (by decide)
  simp [dyadicSign, rationalSign, Dyadic.value, Rat.mul_pos_iff_of_pos_right hp,
    Rat.mul_neg_iff_of_pos_right hp, Rat.intCast_pos, Rat.intCast_neg_iff]

def exactDot (pairs : List (Dyadic × Dyadic)) : Dyadic :=
  pairs.foldl (fun acc (a, b) => dyadicAdd acc (dyadicMul a b)) ⟨0, 0⟩

theorem exactDot_sound (pairs : List (Dyadic × Dyadic)) :
    (exactDot pairs).value = pairs.foldl (fun acc (a, b) => acc + a.value * b.value) 0 := by
  have sound (acc : Dyadic) :
      (pairs.foldl (fun acc (a, b) => dyadicAdd acc (dyadicMul a b)) acc).value =
        pairs.foldl (fun acc (a, b) => acc + a.value * b.value) acc.value := by
    induction pairs generalizing acc with
    | nil => rfl
    | cons pair rest ih =>
      rcases pair with ⟨a, b⟩
      simp only [List.foldl_cons, ih, dyadicAdd_sound, dyadicMul_sound]
  simpa [exactDot, Dyadic.value] using sound ⟨0, 0⟩

def orient2dSign (ax ay bx yb cx cy : Dyadic) : Int :=
  dyadicSign (dyadicSub
    (dyadicMul (dyadicSub ax cx) (dyadicSub yb cy))
    (dyadicMul (dyadicSub ay cy) (dyadicSub bx cx)))

theorem orient2d_sign_exact (ax ay bx yb cx cy : Dyadic) :
    orient2dSign ax ay bx yb cx cy =
      rationalSign ((ax.value - cx.value) * (yb.value - cy.value) -
        (ay.value - cy.value) * (bx.value - cx.value)) := by
  simp [orient2dSign, dyadicSign_sound, dyadicSub_sound, dyadicMul_sound]

theorem tdiv_error (a d : Int) (hd : 0 < d) :
    (a - a.tdiv d * d).natAbs < d.toNat := by
  have h := Int.tmod_add_tdiv_mul a d
  have hlo := Int.lt_tmod_of_pos a hd
  have hhi := Int.tmod_lt_of_pos a hd
  have he : a - a.tdiv d * d = a.tmod d := by omega
  rw [he]
  omega

def fixOne : Nat := 2 ^ 128

private theorem fixOne_int_pos : 0 < (fixOne : Int) := by decide
private theorem fixOne_rat_pos : 0 < (fixOne : Rat) := by decide

def dyadicToFixed128 (a : Dyadic) : Int :=
  let shift := a.e + 128
  if a.m = 0 then 0
  else if 0 ≤ shift then a.m * 2 ^ shift.toNat
  else a.m.tdiv (2 ^ (-shift).toNat)

def fixedValue (n : Int) : Rat := (n : Rat) / (fixOne : Rat)

def expStep (x : Int) (k : Nat) (term : Int) : Int :=
  (term * x).tdiv ((fixOne : Int) * k)

def sinSquare (x : Int) : Int :=
  (x * x).tdiv fixOne

def sinDen (k : Nat) : Nat := 2 * k * (2 * k + 1)

def sinStep (x : Int) (k : Nat) (term : Int) : Int :=
  (-(term * sinSquare x)).tdiv ((fixOne : Int) * sinDen k)

def termAt (step : Nat → α → α) (initial : α) : Nat → α
  | 0 => initial
  | k + 1 => step (k + 1) (termAt step initial k)

def prefixSum [Add α] (term : Nat → α) : Nat → α
  | 0 => term 0
  | k + 1 => prefixSum term k + term (k + 1)

def sumWithBreak (step : Nat → Int → Int) (initial : Int) : Nat → Nat → Int
  | 0, _ => initial
  | fuel + 1, k =>
    let next := step (Nat.succ k) initial
    if next = 0 then initial else initial + sumWithBreak step next fuel (Nat.succ k)

def expTerm (x : Int) := termAt (expStep x) (fixOne : Int)
def sinTerm (x : Int) := termAt (sinStep x) x

def fixed128Exp (x : Int) : Int := sumWithBreak (expStep x) fixOne 34 0
def fixed128Sin (x : Int) : Int := sumWithBreak (sinStep x) x 20 0

def followingSum [Add α] [OfNat α 0] (term : Nat → α) (k : Nat) : Nat → α
  | 0 => 0
  | n + 1 => term k + followingSum term (k + 1) n

private theorem followingSum_one (term : Nat → Int) (k n : Nat) :
    followingSum term k (n + 1) = followingSum term k n + term (k + n) := by
  induction n generalizing k with
  | zero => simp [followingSum]
  | succ n ih =>
    change term k + followingSum term (k + 1) (n + 1) =
      (term k + followingSum term (k + 1) n) + term (k + (n + 1))
    rw [ih (k + 1)]
    have he : k + 1 + n = k + (n + 1) := by omega
    rw [he, Int.add_assoc]

private theorem sumWithBreak_exact (step : Nat → Int → Int) (term : Nat → Int)
    (hz : ∀ i, step i 0 = 0) (ht : ∀ i, term (i + 1) = step (i + 1) (term i))
    (k n : Nat) :
    sumWithBreak step (term k) n k = followingSum term k (n + 1) := by
  induction n generalizing k with
  | zero => simp [sumWithBreak, followingSum]
  | succ n ih =>
    rw [sumWithBreak, ← ht, followingSum]
    split
    · have allZero (i : Nat) : term (k + 1 + i) = 0 := by
        induction i with
        | zero => exact ‹term (k + 1) = 0›
        | succ i hi => rw [Nat.add_succ, ht, hi, hz]
      have tailZero (j fuel : Nat) : followingSum term (k + 1 + j) fuel = 0 := by
        induction fuel generalizing j with
        | zero => rfl
        | succ fuel hi =>
          rw [followingSum, allZero, Int.zero_add, Nat.add_assoc]
          exact hi (j + 1)
      rw [show followingSum term (k + 1) (n + 1) = 0 from tailZero 0 (n + 1), Int.add_zero]
    · rw [ih]

private theorem prefixSum_eq (term : Nat → Int) (n : Nat) :
    prefixSum term n = followingSum term 0 (n + 1) := by
  induction n with
  | zero => simp [prefixSum, followingSum]
  | succ n ih => rw [prefixSum, ih, followingSum_one term 0 (n + 1), Nat.zero_add]

theorem fixed128Exp_early_exit_exact (x : Int) :
    fixed128Exp x = prefixSum (expTerm x) 34 := by
  rw [fixed128Exp, prefixSum_eq]
  exact sumWithBreak_exact (expStep x) (expTerm x) (by simp [expStep]) (fun _ => rfl) 0 34

theorem fixed128Sin_early_exit_exact (x : Int) :
    fixed128Sin x = prefixSum (sinTerm x) 20 := by
  rw [fixed128Sin, prefixSum_eq]
  exact sumWithBreak_exact (sinStep x) (sinTerm x) (by simp [sinStep]) (fun _ => rfl) 0 20

private theorem abs_le_iff {a b : Rat} : a.abs ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  unfold Rat.abs
  split <;> grind

private theorem abs_lt_iff {a b : Rat} : a.abs < b ↔ -b < a ∧ a < b := by
  unfold Rat.abs
  split <;> grind

private theorem abs_mul (a b : Rat) : (a * b).abs = a.abs * b.abs := by
  by_cases ha : 0 ≤ a
  · rw [Rat.abs_of_nonneg ha]
    by_cases hb : 0 ≤ b
    · rw [Rat.abs_of_nonneg hb, Rat.abs_of_nonneg (Rat.mul_nonneg ha hb)]
    · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
      rw [Rat.abs_of_nonpos hb', Rat.abs_of_nonpos (by simpa using Rat.mul_le_mul_of_nonneg_left hb' ha), Rat.mul_neg]
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    rw [Rat.abs_of_nonpos ha']
    by_cases hb : 0 ≤ b
    · rw [Rat.abs_of_nonneg hb, Rat.abs_of_nonpos (by simpa using Rat.mul_le_mul_of_nonneg_right ha' hb), Rat.neg_mul]
    · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
      rw [Rat.abs_of_nonpos hb', Rat.abs_of_nonneg (by
        simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using
          Rat.mul_nonneg (a := -a) (b := -b) (by simpa using Rat.neg_le_neg ha') (by simpa using Rat.neg_le_neg hb')), Rat.mul_neg, Rat.neg_mul,
        Rat.neg_neg]

private theorem abs_div_pos (a : Rat) {d : Rat} (hd : 0 < d) :
    (a / d).abs = a.abs / d := by
  rw [Rat.div_def, abs_mul, Rat.abs_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hd)), ← Rat.div_def]

private theorem abs_add_le (a b : Rat) : (a + b).abs ≤ a.abs + b.abs := by
  have ha := abs_le_iff.mp (Rat.le_refl (a := a.abs))
  have hb := abs_le_iff.mp (Rat.le_refl (a := b.abs))
  apply abs_le_iff.mpr
  grind

private theorem abs_sub_le (a b c : Rat) :
    (a - c).abs ≤ (a - b).abs + (b - c).abs := by
  simpa only [show a - b + (b - c) = a - c by grind] using abs_add_le (a - b) (b - c)

private theorem tdiv_rat_error (a d : Int) (hd : 0 < d) :
    ((a.tdiv d : Rat) - (a : Rat) / (d : Rat)).abs < 1 := by
  have hr := tdiv_error a d hd
  have hd' : 0 < (d : Rat) := Rat.intCast_pos.mpr hd
  have hmul : (a.tdiv d : Rat) - (a : Rat) / (d : Rat) =
      ((a.tdiv d * d - a : Int) : Rat) / (d : Rat) := by
    push_cast
    grind
  rw [hmul, abs_div_pos _ hd', Rat.div_lt_iff hd', Rat.one_mul, abs_lt_iff]
  rw [← Rat.intCast_neg]
  exact ⟨Rat.intCast_lt_intCast.mpr (by omega), Rat.intCast_lt_intCast.mpr (by omega)⟩

private theorem scaled_error {a b c : Rat} (h : (a - b).abs < c) :
    (a / fixOne - b / fixOne).abs < c / fixOne := by
  rw [show a / fixOne - b / fixOne = (a - b) / (fixOne : Rat) by grind,
    abs_div_pos _ fixOne_rat_pos]
  apply (Rat.div_lt_iff fixOne_rat_pos).mpr
  rwa [Rat.div_mul_cancel (Rat.ne_of_gt fixOne_rat_pos)]

def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => factorial k * (k + 1)

private theorem factorial_pos (k : Nat) : 0 < factorial k := by
  induction k with
  | zero => decide
  | succ _ ih => exact Nat.mul_pos ih (Nat.succ_pos _)

def expTaylorTerm (x : Rat) (k : Nat) : Rat :=
  x ^ k / (factorial k : Rat)

def sinTaylorTerm (x : Rat) (k : Nat) : Rat :=
  (-1 : Rat) ^ k * x ^ (2 * k + 1) / (factorial (2 * k + 1) : Rat)

def expTaylor (x : Rat) (n : Nat) : Rat := prefixSum (expTaylorTerm x) n
def sinTaylor (x : Rat) (n : Nat) : Rat := prefixSum (sinTaylorTerm x) n

private theorem expTaylorTerm_succ (x : Rat) (k : Nat) :
    expTaylorTerm x (k + 1) = expTaylorTerm x k * (x / (k + 1 : Nat)) := by
  have hf := Rat.natCast_pos.mpr (factorial_pos k)
  have hk := Rat.natCast_pos.mpr (Nat.succ_pos k)
  simp only [expTaylorTerm, Rat.pow_succ, factorial, Rat.natCast_mul]
  grind

private theorem sinTaylorTerm_succ (x : Rat) (k : Nat) :
    sinTaylorTerm x (k + 1) = sinTaylorTerm x k * (-(x * x) / (sinDen (k + 1) : Rat)) := by
  have he : 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 := by omega
  have hden : factorial (2 * (k + 1) + 1) = factorial (2 * k + 1) * sinDen (k + 1) := by
    rw [he, factorial, factorial, sinDen]
    have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [h, Nat.mul_assoc]
  have hf := Rat.natCast_pos.mpr (factorial_pos (2 * k + 1))
  have hk : 0 < (sinDen (k + 1) : Rat) := Rat.natCast_pos.mpr
    (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos k)) (Nat.succ_pos _))
  simp only [sinTaylorTerm, hden, Rat.natCast_mul, Rat.pow_succ (q := (-1 : Rat))]
  rw [he, Rat.pow_succ, Rat.pow_succ]
  grind

private theorem int_abs_cast (x : Int) : (x : Rat).abs = (x.natAbs : Rat) := by
  by_cases hx : 0 ≤ x
  · rw [Rat.abs_of_nonneg (Rat.intCast_nonneg.mpr hx), ← Rat.intCast_natCast,
      Int.natAbs_of_nonneg hx]
  · have h : x ≤ 0 := by omega
    rw [Rat.abs_of_nonpos (Rat.intCast_nonpos.mpr h), ← Rat.intCast_neg, ← Rat.intCast_natCast,
      Int.ofNat_natAbs_of_nonpos h]

private theorem unit_div_pos : 0 < (1 : Rat) / fixOne := by
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr fixOne_rat_pos

private theorem realDiv_le {a d b : Rat} (hd : 0 < d) (h : a ≤ b * d) : a / d ≤ b := by
  apply Rat.le_of_mul_le_mul_right _ hd
  rwa [Rat.div_mul_cancel (Rat.ne_of_gt hd)]

private theorem abs_div_le {a d b : Rat} (hd : 0 < d) (h : a.abs ≤ b * d) :
    (a / d).abs ≤ b := by
  rw [abs_div_pos _ hd]
  exact realDiv_le hd h

private theorem abs_mul_le {a b A B : Rat} (ha : a.abs ≤ A) (hb : b.abs ≤ B) :
    (a * b).abs ≤ A * B := by
  rw [abs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ha Rat.abs_nonneg)
    (Rat.mul_le_mul_of_nonneg_left hb (Rat.le_trans Rat.abs_nonneg ha))

private theorem exp_input_bound (x : Int) (hx : x.natAbs ≤ 2 ^ 127) :
    (fixedValue x).abs ≤ 1 / 2 := by
  apply abs_div_le fixOne_rat_pos
  rw [int_abs_cast]
  exact Rat.le_trans (Rat.natCast_le_natCast.mpr hx)
    (by decide +kernel : ((2 ^ 127 : Nat) : Rat) ≤ (1 / 2) * fixOne)

private theorem sin_input_bound (x : Int) (hx : x.natAbs ≤ 4 * fixOne / 5) :
    (fixedValue x).abs ≤ 4 / 5 := by
  apply abs_div_le fixOne_rat_pos
  rw [int_abs_cast]
  exact Rat.le_trans (Rat.natCast_le_natCast.mpr hx)
    (by decide +kernel : ((4 * fixOne / 5 : Nat) : Rat) ≤ (4 / 5) * fixOne)

private theorem fixedStep_error (t m : Int) (d : Nat) (hd : 0 < d) :
    (((t * m).tdiv ((fixOne : Int) * d) : Rat) -
      (t : Rat) * (fixedValue m / (d : Rat))).abs < 1 := by
  have h := tdiv_rat_error (t * m) ((fixOne : Int) * d)
    (Int.mul_pos fixOne_int_pos (by omega))
  have hd' := Rat.natCast_pos.mpr hd
  have he : ((t * m : Int) : Rat) / (((fixOne : Int) * (d : Int) : Int) : Rat) =
      (t : Rat) * (fixedValue m / (d : Rat)) := by
    push_cast
    unfold fixedValue
    have := fixOne_rat_pos
    grind
  rwa [he] at h

private theorem exp_ratio_bound {x : Rat} (hx : x.abs ≤ 1 / 2) (k : Nat) :
    (x / (k + 1 : Nat)).abs ≤ 1 / 2 := by
  have hk : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := Rat.natCast_le_natCast.mpr (Nat.succ_le_succ (Nat.zero_le k))
  apply abs_div_le (by grind)
  grind

private theorem sinDen_ge (k : Nat) : 4 ≤ sinDen (k + 1) := by
  unfold sinDen
  have h₁ : 2 ≤ 2 * (k + 1) := by omega
  have h₂ : 2 ≤ 2 * (k + 1) + 1 := by omega
  exact Nat.mul_le_mul h₁ h₂

private theorem sinDen_pos (k : Nat) : 0 < sinDen (k + 1) :=
  Nat.lt_of_lt_of_le (by decide) (sinDen_ge k)

private theorem sin_ratio_bound {x : Rat} (hx : x.abs ≤ 1) (k : Nat) :
    (-(x * x) / (sinDen (k + 1) : Rat)).abs ≤ 1 / 4 := by
  have hd : (4 : Rat) ≤ (sinDen (k + 1) : Rat) := Rat.natCast_le_natCast.mpr (sinDen_ge k)
  apply abs_div_le (by grind)
  rw [Rat.abs_neg]
  have h := abs_mul_le hx hx
  grind

theorem fixed128Sin_square_error (x : Int) :
    (fixedValue (sinSquare x) - fixedValue x * fixedValue x).abs < 1 / fixOne := by
  have h := scaled_error (tdiv_rat_error (x * x) (fixOne : Int) fixOne_int_pos)
  have he : ((x * x : Int) : Rat) / (fixOne : Rat) / (fixOne : Rat) =
      fixedValue x * fixedValue x := by
    unfold fixedValue
    push_cast
    grind
  simpa only [sinSquare, fixedValue, Rat.intCast_natCast] using
    (show (((x * x).tdiv fixOne : Rat) / (fixOne : Rat) -
      fixedValue x * fixedValue x).abs < 1 / fixOne from by
        rw [← he]
        simpa only [Rat.intCast_natCast] using h)

private theorem sin_square_bound (x : Int) (hx : (fixedValue x).abs ≤ 1) :
    (fixedValue (sinSquare x)).abs ≤ 1 := by
  have hp : 0 ≤ x * x := by
    rcases Int.le_total 0 x with h | h
    · exact Int.mul_nonneg h h
    · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
  have hs : 0 ≤ sinSquare x := Int.tdiv_nonneg hp (Int.le_of_lt fixOne_int_pos)
  have hr := Int.tmod_add_tdiv_mul (x * x) (fixOne : Int)
  have hm := Int.tmod_nonneg (fixOne : Int) hp
  have hi : sinSquare x * (fixOne : Int) ≤ x * x := by
    unfold sinSquare
    omega
  have hrat := Rat.intCast_le_intCast.mpr hi
  push_cast at hrat
  have hq := fixOne_rat_pos
  have hxy : fixedValue (sinSquare x) ≤ fixedValue x * fixedValue x := by
    apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hq hq)
    unfold fixedValue
    grind
  have hsq := abs_mul_le hx hx
  have hn : 0 ≤ fixedValue (sinSquare x) := Rat.mul_nonneg (Rat.intCast_nonneg.mpr hs)
    (Rat.le_of_lt (Rat.inv_pos.mpr hq))
  rw [Rat.abs_of_nonneg hn]
  have hle := (abs_le_iff.mp hsq).2
  grind

private theorem sin_ratio_error (x : Int) (k : Nat) :
    ((-fixedValue (sinSquare x) / (sinDen (k + 1) : Rat)) -
      (-(fixedValue x * fixedValue x) / (sinDen (k + 1) : Rat))).abs ≤ (1 / fixOne) / 4 := by
  have hd : (4 : Rat) ≤ (sinDen (k + 1) : Rat) := Rat.natCast_le_natCast.mpr (sinDen_ge k)
  have hp : 0 < (sinDen (k + 1) : Rat) := by grind
  have he : -fixedValue (sinSquare x) / (sinDen (k + 1) : Rat) -
      -(fixedValue x * fixedValue x) / (sinDen (k + 1) : Rat) =
      -(fixedValue (sinSquare x) - fixedValue x * fixedValue x) /
        (sinDen (k + 1) : Rat) := by grind
  rw [he]
  apply abs_div_le hp
  rw [Rat.abs_neg]
  have h := Rat.le_of_lt (fixed128Sin_square_error x)
  have hm := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt unit_div_pos)
  grind

theorem fixed128Exp_term_error (x : Int) (hx : x.natAbs ≤ 2 ^ 127) (k : Nat) :
    ((expTerm x k : Rat) - (fixOne : Rat) * expTaylorTerm (fixedValue x) k).abs < 2 := by
  induction k with
  | zero =>
    rw [show expTaylorTerm (fixedValue x) 0 = 1 by simp [expTaylorTerm, factorial, Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide +kernel]]
    change ((fixOne : Rat) - (fixOne : Rat) * 1).abs < 2
    rw [Rat.mul_one, Rat.sub_self, Rat.abs_zero]
    decide
  | succ k ih =>
    let r := fixedValue x / ((k + 1 : Nat) : Rat)
    let t : Rat := expTerm x k
    let exactTerm := (fixOne : Rat) * expTaylorTerm (fixedValue x) k
    let rounded : Rat := expTerm x (k + 1)
    have hRound : (rounded - t * r).abs < 1 := fixedStep_error _ _ _ (Nat.succ_pos k)
    have hRatio : r.abs ≤ 1 / 2 := exp_ratio_bound (exp_input_bound x hx) k
    have hProp := abs_mul_le (Rat.le_of_lt ih) hRatio
    change (((t - exactTerm) * r).abs ≤ 2 * (1 / 2)) at hProp
    rw [show (t - exactTerm) * r = t * r - exactTerm * r by grind] at hProp
    have h := abs_sub_le rounded (t * r) (exactTerm * r)
    rw [expTaylorTerm_succ]
    change (rounded - (fixOne : Rat) * (expTaylorTerm (fixedValue x) k * r)).abs < 2
    rw [← Rat.mul_assoc]
    change (rounded - exactTerm * r).abs < 2
    grind

private theorem sinTaylorTerm_abs {x : Rat} (hx : x.abs ≤ 1) (k : Nat) :
    (sinTaylorTerm x k).abs ≤ 1 := by
  induction k with
  | zero =>
    have he : sinTaylorTerm x 0 = x := by simp [sinTaylorTerm, factorial, Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide +kernel]
    rwa [he]
  | succ k ih =>
    rw [sinTaylorTerm_succ]
    have h := abs_mul_le ih (sin_ratio_bound hx k)
    grind

theorem fixed128Sin_term_error (x : Int) (hx : x.natAbs ≤ 4 * fixOne / 5) (k : Nat) :
    ((sinTerm x k : Rat) - (fixOne : Rat) * sinTaylorTerm (fixedValue x) k).abs < 2 := by
  have hx' : (fixedValue x).abs ≤ 1 := Rat.le_trans (sin_input_bound x hx) (by decide +kernel)
  induction k with
  | zero =>
    rw [show sinTaylorTerm (fixedValue x) 0 = fixedValue x by
        simp [sinTaylorTerm, factorial, Rat.div_def, show (1 : Rat)⁻¹ = 1 by decide +kernel]]
    change ((x : Rat) - (fixOne : Rat) * fixedValue x).abs < 2
    have := fixOne_rat_pos
    unfold fixedValue
    have he : (fixOne : Rat) * ((x : Rat) / fixOne) = (x : Rat) := by grind
    rw [he, Rat.sub_self, Rat.abs_zero]
    decide
  | succ k ih =>
    let d := sinDen (k + 1)
    let q := -fixedValue (sinSquare x) / (d : Rat)
    let r := -(fixedValue x * fixedValue x) / (d : Rat)
    let t : Rat := sinTerm x k
    let exactTerm := (fixOne : Rat) * sinTaylorTerm (fixedValue x) k
    let rounded : Rat := sinTerm x (k + 1)
    have hd : (4 : Rat) ≤ (d : Rat) := Rat.natCast_le_natCast.mpr (sinDen_ge k)
    have hRound : (rounded - t * q).abs < 1 := by
      have h := fixedStep_error (sinTerm x k) (-sinSquare x) d (sinDen_pos k)
      have he : fixedValue (-sinSquare x) = -fixedValue (sinSquare x) := by
        simp only [fixedValue, Rat.intCast_neg, Rat.div_def, Rat.neg_mul]
      rw [Int.mul_neg, he] at h
      exact h
    have hRatio : q.abs ≤ 1 / 4 := by
      apply abs_div_le (by grind)
      rw [Rat.abs_neg]
      have h := sin_square_bound x hx'
      grind
    have hProp := abs_mul_le (Rat.le_of_lt ih) hRatio
    change (((t - exactTerm) * q).abs ≤ 2 * (1 / 4)) at hProp
    rw [show (t - exactTerm) * q = t * q - exactTerm * q by grind] at hProp
    have hExact : exactTerm.abs ≤ (fixOne : Rat) := by
      rw [show exactTerm.abs = (fixOne : Rat) * (sinTaylorTerm (fixedValue x) k).abs by
        rw [abs_mul, Rat.abs_of_nonneg (Rat.le_of_lt fixOne_rat_pos)]]
      simpa using Rat.mul_le_mul_of_nonneg_left (sinTaylorTerm_abs hx' k)
        (Rat.le_of_lt fixOne_rat_pos)
    have hSquare := abs_mul_le hExact (sin_ratio_error x k)
    change ((exactTerm * (q - r)).abs ≤ (fixOne : Rat) * ((1 / fixOne) / 4)) at hSquare
    rw [show exactTerm * (q - r) = exactTerm * q - exactTerm * r by grind] at hSquare
    have h := abs_sub_le rounded (t * q) (exactTerm * r)
    have h' := abs_sub_le (t * q) (exactTerm * q) (exactTerm * r)
    rw [sinTaylorTerm_succ]
    change (rounded - (fixOne : Rat) * (sinTaylorTerm (fixedValue x) k * r)).abs < 2
    rw [← Rat.mul_assoc]
    change (rounded - exactTerm * r).abs < 2
    have he : (fixOne : Rat) * ((1 / fixOne) / 4) = 1 / 4 := by
      have := fixOne_rat_pos
      grind
    rw [he] at hSquare
    grind

private theorem prefix_rounding_bound (t : Nat → Int) (u : Nat → Rat)
    (h₀ : (t 0 : Rat) = (fixOne : Rat) * u 0)
    (hstep : ∀ k, ((t k : Rat) - (fixOne : Rat) * u k).abs < 2) (n : Nat) :
    ((prefixSum (α := Int) t n : Rat) - (fixOne : Rat) * prefixSum u n).abs ≤ 2 * (n : Rat) ∧
    (0 < n → ((prefixSum (α := Int) t n : Rat) - (fixOne : Rat) * prefixSum u n).abs < 2 * (n : Rat)) := by
  induction n with
  | zero => simp [prefixSum, h₀, Rat.sub_self]
  | succ n ih =>
    have h := abs_add_le ((prefixSum (α := Int) t n : Rat) - (fixOne : Rat) * prefixSum u n)
      ((t (n + 1) : Rat) - (fixOne : Rat) * u (n + 1))
    have he : (prefixSum (α := Int) t (n + 1) : Rat) - (fixOne : Rat) * prefixSum u (n + 1) =
        ((prefixSum (α := Int) t n : Rat) - (fixOne : Rat) * prefixSum u n) +
          ((t (n + 1) : Rat) - (fixOne : Rat) * u (n + 1)) := by
      simp only [prefixSum, Rat.intCast_add]
      grind
    have hs := hstep (n + 1)
    have hi := ih.1
    rw [he]
    push_cast
    grind

theorem fixed128Exp_rounding_error (x : Int) (hx : x.natAbs ≤ 2 ^ 127) :
    (fixedValue (fixed128Exp x) - expTaylor (fixedValue x) 34).abs < 68 / fixOne := by
  have h₀ : (expTerm x 0 : Rat) = (fixOne : Rat) * expTaylorTerm (fixedValue x) 0 := by
    simp [expTerm, termAt, expTaylorTerm, factorial, Rat.div_def, Rat.intCast_natCast,
      show (1 : Rat)⁻¹ = 1 by decide +kernel]
  have h := (prefix_rounding_bound (expTerm x) (expTaylorTerm (fixedValue x)) h₀
    (fixed128Exp_term_error x hx) 34).2 (by decide)
  have hp := scaled_error h
  have hq := fixOne_rat_pos
  rw [show (fixOne : Rat) * prefixSum (expTaylorTerm (fixedValue x)) 34 / fixOne =
    expTaylor (fixedValue x) 34 by unfold expTaylor; grind] at hp
  rw [fixed128Exp_early_exit_exact]
  simpa only [fixedValue, show (2 : Rat) * (34 : Nat) = 68 by decide +kernel] using hp

theorem fixed128Sin_rounding_error (x : Int) (hx : x.natAbs ≤ 4 * fixOne / 5) :
    (fixedValue (fixed128Sin x) - sinTaylor (fixedValue x) 20).abs < 40 / fixOne := by
  have hq := fixOne_rat_pos
  have h₀ : (sinTerm x 0 : Rat) = (fixOne : Rat) * sinTaylorTerm (fixedValue x) 0 := by
    simp only [sinTerm, termAt, sinTaylorTerm, Rat.pow_zero, Nat.mul_zero, Nat.zero_add, Rat.pow_one,
      Rat.one_mul]
    have he : (factorial 1 : Rat) = 1 := by decide
    rw [he, show ∀ y : Rat, y / 1 = y by intro; grind]
    unfold fixedValue
    grind
  have h := (prefix_rounding_bound (sinTerm x) (sinTaylorTerm (fixedValue x)) h₀
    (fixed128Sin_term_error x hx) 20).2 (by decide)
  have hp := scaled_error h
  rw [show (fixOne : Rat) * prefixSum (sinTaylorTerm (fixedValue x)) 20 / fixOne =
    sinTaylor (fixedValue x) 20 by unfold sinTaylor; grind] at hp
  rw [fixed128Sin_early_exit_exact]
  simpa only [fixedValue, show (2 : Rat) * (20 : Nat) = 40 by decide +kernel] using hp

private theorem prefixSum_add (term : Nat → Rat) (k n : Nat) :
    prefixSum term (k + n) = prefixSum term k + followingSum term (k + 1) n := by
  induction n generalizing k with
  | zero => simp [followingSum, Rat.add_zero]
  | succ n ih =>
    have he : k + (n + 1) = k + 1 + n := by omega
    rw [he, ih, prefixSum, followingSum, Rat.add_assoc]

private theorem abs_pow (a : Rat) (k : Nat) : (a ^ k).abs = a.abs ^ k := by
  induction k with
  | zero => simp; decide
  | succ k ih => rw [Rat.pow_succ, abs_mul, ih, Rat.pow_succ]

private theorem abs_pow_le {a b : Rat} (hab : a.abs ≤ b) (k : Nat) :
    (a ^ k).abs ≤ b ^ k := by
  induction k with
  | zero => simp; decide
  | succ k ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    exact abs_mul_le ih hab

private theorem expTail_bound (x : Rat) (hx : x.abs ≤ 1 / 2) (k n : Nat) :
    (followingSum (expTaylorTerm x) k n).abs ≤ 2 * (expTaylorTerm x k).abs := by
  induction n generalizing k with
  | zero =>
    simp only [followingSum, Rat.abs_zero]
    exact Rat.mul_nonneg (by decide) Rat.abs_nonneg
  | succ n ih =>
    have hr := exp_ratio_bound hx k
    have hc : (expTaylorTerm x (k + 1)).abs ≤ (expTaylorTerm x k).abs * (1 / 2) := by
      rw [expTaylorTerm_succ]
      exact abs_mul_le (Rat.le_refl) hr
    have h := ih (k + 1)
    have ht := abs_add_le (expTaylorTerm x k) (followingSum (expTaylorTerm x) (k + 1) n)
    rw [followingSum]
    grind

private theorem sinTail_factor (x : Rat) (hx : x.abs ≤ 1) (k n : Nat) :
    ∃ u : Rat, 0 ≤ u ∧ u ≤ 1 ∧ followingSum (sinTaylorTerm x) k n = sinTaylorTerm x k * u := by
  induction n generalizing k with
  | zero => exact ⟨0, by decide, by decide, (Rat.mul_zero _).symm⟩
  | succ n ih =>
    obtain ⟨v, hv₀, hv₁, hv⟩ := ih (k + 1)
    let r := x * x / (sinDen (k + 1) : Rat)
    have hd := Rat.natCast_pos.mpr (sinDen_pos k)
    have hr₀ : 0 ≤ r := by
      have hs : 0 ≤ x * x := by
        rcases Rat.le_total (a := 0) (b := x) with h | h
        · exact Rat.mul_nonneg h h
        · have h' : 0 ≤ -x := by grind
          simpa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using Rat.mul_nonneg h' h'
      exact Rat.mul_nonneg hs (Rat.le_of_lt (Rat.inv_pos.mpr hd))
    have hr : (-r).abs ≤ 1 / 4 := by
      simpa only [r, Rat.div_def, Rat.neg_mul] using sin_ratio_bound hx k
    rw [Rat.abs_neg, Rat.abs_of_nonneg hr₀] at hr
    have hrv₀ : 0 ≤ r * v := Rat.mul_nonneg hr₀ hv₀
    have hrv₁ : r * v ≤ r := by simpa using Rat.mul_le_mul_of_nonneg_left hv₁ hr₀
    refine ⟨1 - r * v, by grind, by grind, ?_⟩
    rw [followingSum, hv, sinTaylorTerm_succ]
    change sinTaylorTerm x k + sinTaylorTerm x k * (-(x * x) / (sinDen (k + 1) : Rat)) * v =
      sinTaylorTerm x k * (1 - r * v)
    simp only [r, Rat.div_def, Rat.neg_mul]
    grind

theorem expTaylor_remainder_bound (x : Rat) (hx : x.abs ≤ 1 / 2) (n : Nat) :
    (expTaylor x (34 + n) - expTaylor x 34).abs ≤ 2 * (1 / 2 : Rat) ^ 35 / factorial 35 := by
  unfold expTaylor
  rw [prefixSum_add, Rat.add_comm (prefixSum _ _), Rat.add_sub_cancel]
  have h := expTail_bound x hx 35 n
  have hd := Rat.natCast_pos.mpr (factorial_pos 35)
  have he : (expTaylorTerm x 35).abs ≤ (1 / 2 : Rat) ^ 35 / factorial 35 := by
    rw [expTaylorTerm, abs_div_pos _ hd]
    apply Rat.mul_le_mul_of_nonneg_right (abs_pow_le hx 35)
    exact Rat.le_of_lt (Rat.inv_pos.mpr hd)
  exact Rat.le_trans h (by
    rw [Rat.div_def, Rat.mul_assoc, ← Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_left he (by decide))

theorem sinTaylor_remainder_bound (x : Rat) (hx : x.abs ≤ 4 / 5) (n : Nat) :
    (sinTaylor x (20 + n) - sinTaylor x 20).abs ≤ (4 / 5 : Rat) ^ 43 / factorial 43 := by
  unfold sinTaylor
  rw [prefixSum_add, Rat.add_comm (prefixSum _ _), Rat.add_sub_cancel]
  obtain ⟨u, hu₀, hu₁, hu⟩ := sinTail_factor x (Rat.le_trans hx (by decide +kernel)) 21 n
  rw [hu]
  have h : (sinTaylorTerm x 21).abs ≤ (4 / 5 : Rat) ^ 43 / factorial 43 := by
    have hd := Rat.natCast_pos.mpr (factorial_pos 43)
    change (((-1 : Rat) ^ (21 : Nat) * x ^ (43 : Nat)) / (factorial 43 : Rat)).abs ≤ _
    rw [abs_div_pos _ hd, abs_mul, abs_pow, show (-1 : Rat).abs ^ (21 : Nat) = 1 by decide +kernel,
      Rat.one_mul]
    exact Rat.mul_le_mul_of_nonneg_right (abs_pow_le hx 43) (Rat.le_of_lt (Rat.inv_pos.mpr hd))
  rw [abs_mul, Rat.abs_of_nonneg hu₀]
  exact Rat.le_trans (by simpa using Rat.mul_le_mul_of_nonneg_left hu₁ Rat.abs_nonneg) h

theorem expTaylor_tail_lt_ulp :
    2 * (1 / 2 : Rat) ^ 35 / factorial 35 < 1 / fixOne := by decide +kernel

theorem sinTaylor_tail_lt_ulp :
    (4 / 5 : Rat) ^ 43 / factorial 43 < 1 / fixOne := by decide +kernel

theorem oracle_bound_decimal : 100 * 10 ^ 36 < fixOne := by decide +kernel

theorem oracle_bound_lt_decimal : (100 : Rat) / fixOne < 1 / (10 : Rat) ^ (36 : Nat) := by
  decide +kernel

/--
The tail estimates hold for every finite Taylor partial sum. Their rational
bounds also enclose the real series limits, with a strict margin below 100 ULPs.
-/
theorem fixed128Exp_total_error_bound (x : Int) (hx : x.natAbs ≤ 2 ^ 127) (n : Nat) :
    (fixedValue (fixed128Exp x) - expTaylor (fixedValue x) 34).abs +
      (expTaylor (fixedValue x) (34 + n) - expTaylor (fixedValue x) 34).abs < 69 / fixOne := by
  have hr := fixed128Exp_rounding_error x hx
  have ht := expTaylor_remainder_bound (fixedValue x) (exp_input_bound x hx) n
  have hu := expTaylor_tail_lt_ulp
  grind

theorem fixed128Sin_total_error_bound (x : Int) (hx : x.natAbs ≤ 4 * fixOne / 5) (n : Nat) :
    (fixedValue (fixed128Sin x) - sinTaylor (fixedValue x) 20).abs +
      (sinTaylor (fixedValue x) (20 + n) - sinTaylor (fixedValue x) 20).abs < 41 / fixOne := by
  have hr := fixed128Sin_rounding_error x hx
  have ht := sinTaylor_remainder_bound (fixedValue x) (sin_input_bound x hx) n
  have hu := sinTaylor_tail_lt_ulp
  grind

theorem fixed128Exp_series_enclosure (x : Int) (hx : x.natAbs ≤ 2 ^ 127) (n : Nat) :
    (fixedValue (fixed128Exp x) - expTaylor (fixedValue x) (34 + n)).abs < 69 / fixOne := by
  have h := abs_sub_le (fixedValue (fixed128Exp x)) (expTaylor (fixedValue x) 34)
    (expTaylor (fixedValue x) (34 + n))
  rw [Rat.abs_sub_comm (x := expTaylor (fixedValue x) 34)] at h
  grind [fixed128Exp_total_error_bound x hx n]

theorem fixed128Sin_series_enclosure (x : Int) (hx : x.natAbs ≤ 4 * fixOne / 5) (n : Nat) :
    (fixedValue (fixed128Sin x) - sinTaylor (fixedValue x) (20 + n)).abs < 41 / fixOne := by
  have h := abs_sub_le (fixedValue (fixed128Sin x)) (sinTaylor (fixedValue x) 20)
    (sinTaylor (fixedValue x) (20 + n))
  rw [Rat.abs_sub_comm (x := sinTaylor (fixedValue x) 20)] at h
  grind [fixed128Sin_total_error_bound x hx n]

def ceilScore (diffFix scale : Nat) : Nat :=
  (diffFix * scale + (fixOne - 1)) / fixOne

theorem ceilScore_spec (diffFix scale : Nat) :
    diffFix * scale ≤ ceilScore diffFix scale * fixOne ∧
    ∀ m : Nat, diffFix * scale ≤ m * fixOne → ceilScore diffFix scale ≤ m := by
  have hq : 0 < fixOne := by decide
  let p := diffFix * scale
  change p ≤ (p + (fixOne - 1)) / fixOne * fixOne ∧
    ∀ m : Nat, p ≤ m * fixOne → (p + (fixOne - 1)) / fixOne ≤ m
  constructor
  · have h := Nat.mod_add_div (p + (fixOne - 1)) fixOne
    have hr := Nat.mod_lt (p + (fixOne - 1)) hq
    rw [Nat.mul_comm fixOne] at h
    omega
  · intro m hm
    apply (Nat.div_le_iff_le_mul hq).mpr
    omega

private theorem ceilScore_previous (diffFix scale : Nat) :
    ((ceilScore diffFix scale : Rat) - 1) * fixOne < (diffFix * scale : Nat) := by
  have hq : 0 < fixOne := by decide
  have h := Nat.div_mul_le_self (diffFix * scale + (fixOne - 1)) fixOne
  change ceilScore diffFix scale * fixOne ≤ diffFix * scale + (fixOne - 1) at h
  have hr := Rat.natCast_le_natCast.mpr h
  have he : ((fixOne - 1 : Nat) : Rat) = (fixOne : Rat) - 1 := by decide +kernel
  push_cast at hr
  rw [he] at hr
  grind

theorem ceilScore_eq_ceil (diffFix scale : Nat) :
    (ceilScore diffFix scale : Int) = (((diffFix * scale : Nat) : Rat) / fixOne).ceil := by
  let q := ((diffFix * scale : Nat) : Rat) / fixOne
  let s := (ceilScore diffFix scale : Int)
  have h := Rat.natCast_le_natCast.mpr (ceilScore_spec diffFix scale).1
  rw [Rat.natCast_mul] at h
  have hu : q.ceil ≤ s := Rat.ceil_le_iff.mpr
    (realDiv_le fixOne_rat_pos (by simpa only [s, Rat.intCast_natCast, Rat.natCast_mul] using h))
  have hl : s - 1 < q.ceil := Rat.lt_ceil_iff.mpr ((Rat.lt_div_iff fixOne_rat_pos).mpr
    (by simpa only [s, Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_ofNat] using
      ceilScore_previous diffFix scale))
  change s = q.ceil
  omega

theorem ceilScore_decision_robustness (diffFix scale : Nat) (err : Rat) (E : Nat)
    (herror : (err - ((diffFix : Rat) / fixOne)).abs ≤ (E : Rat) / fixOne)
    (hmargin : ∀ m : Int,
      (E : Rat) * scale < (((diffFix * scale : Nat) : Rat) - (m : Rat) * fixOne).abs) :
    (ceilScore diffFix scale : Int) = (err * (scale : Rat)).ceil := by
  have hq := fixOne_rat_pos
  let p : Rat := (diffFix * scale : Nat)
  let y : Rat := err * (scale : Rat)
  have hs := Rat.natCast_nonneg (a := scale)
  have hp := abs_mul_le herror (b := (scale : Rat)) (B := scale)
    (by rw [Rat.abs_of_nonneg hs]; exact Rat.le_refl)
  have he : (err - ((diffFix : Rat) / fixOne)) * (scale : Rat) = (y * fixOne - p) / fixOne := by
    unfold y p
    push_cast
    grind
  have hd : (y * fixOne - p).abs ≤ (E : Rat) * scale := by
    rw [he, abs_div_pos _ hq] at hp
    have hs' : (E : Rat) / fixOne * scale = ((E : Rat) * scale) / fixOne := by grind
    rw [hs'] at hp
    have h := Rat.mul_le_mul_of_nonneg_right hp (Rat.le_of_lt hq)
    simpa only [Rat.div_mul_cancel (Rat.ne_of_gt hq)] using h
  have hside (m : Int) : y ≤ (m : Rat) ↔ p ≤ (m : Rat) * fixOne := by
    have hm := hmargin m
    change (E : Rat) * scale < (p - (m : Rat) * fixOne).abs at hm
    have hband := abs_le_iff.mp hd
    constructor
    · intro hy
      have hz := Rat.mul_le_mul_of_nonneg_right hy (Rat.le_of_lt hq)
      by_cases h : p ≤ (m : Rat) * fixOne
      · exact h
      · rw [Rat.abs_of_nonneg (by grind)] at hm
        grind
    · intro hp'
      apply Rat.le_of_mul_le_mul_right _ hq
      rw [Rat.abs_of_nonpos (by grind)] at hm
      grind
  change (ceilScore diffFix scale : Int) = y.ceil
  apply Int.le_antisymm
  · apply Int.not_lt.mp
    intro hlt
    have hprev := ceilScore_previous diffFix scale
    have hle : y ≤ ((ceilScore diffFix scale : Int) - 1 : Int) :=
      Rat.le_trans (Rat.le_ceil (x := y))
        (Rat.intCast_le_intCast.mpr (by omega))
    have hm := (hside ((ceilScore diffFix scale : Int) - 1)).mp hle
    push_cast at hm
    change ((ceilScore diffFix scale : Rat) - 1) * fixOne < p at hprev
    grind
  · apply Rat.ceil_le_iff.mpr
    apply (hside (ceilScore diffFix scale : Int)).mpr
    simpa only [Rat.intCast_natCast, ← Rat.natCast_mul] using
      Rat.natCast_le_natCast.mpr (ceilScore_spec diffFix scale).1

end PFOracle
