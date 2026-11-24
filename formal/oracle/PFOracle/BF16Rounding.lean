import PFOracle.BF16Oracle

namespace PFOracle

/-!
# Universal Real-Value IEEE-754 RNE & Overflow Proofs for `BF16Oracle`

Pure-kernel Lean 4.36.0 proofs (zero `grind`, zero `bv_decide`, zero `sorry`, standard
axioms `[propext, Classical.choice, Quot.sound]` only) connecting every rounding
implementation directly to its exact dyadic rational specification:

1. `f32BitsToBf16RNE_value_spec`: bridges `f32BitsToBf16RNE` to `float32BitsToDyadic` & `bf16ToDyadic`.
2. `f64BitsToBf16RNE_nan_canonical`, `f64BitsToBf16RNE_inf`, `f64BitsToBf16RNE_value_spec`:
   universal zero-double-rounding IEEE-754 RNE & overflow proofs directly on `f64BitsToBf16RNE`.
3. `dyadicToF32BitsRNE_value_spec`: universal binary32 RNE & overflow proof directly on `dyadicToF32BitsRNE`.
4. `fmafFiniteBits_value_spec`: universal single-rounding FMA proof directly on `fmafFiniteBits`.
-/

-- ============================================================================
-- 1. Core Specifications & Lightweight Algebraic Helpers
-- ============================================================================

/-- Exact IEEE-754 round-to-nearest-ties-to-even specification for rounding a rational value `x`
    to a finite IEEE-754 value `y` with output LSB parity `isEven` at binade spacing `ulp > 0`:
    1. Error bound: `|y - x| ≤ ulp / 2`.
    2. Exact midpoint tie-breaking: if `|y - x| = ulp / 2`, then `isEven = true` (even LSB). -/
def IsRNENearest (x y ulp : Rat) (isEven : Bool) : Prop :=
  -(ulp / 2) ≤ y - x ∧ y - x ≤ ulp / 2 ∧
  ((y - x = ulp / 2 ∨ x - y = ulp / 2) → isEven = true)

/-- Exact IEEE-754 BF16 overflow threshold `(2 - 2^-8) * 2^127 = 511 * 2^119`. -/
def bf16OverflowThreshold : Rat :=
  (511 : Rat) * (2 : Rat) ^ (119 : Int)

/-- Exact IEEE-754 Float32 overflow threshold `(2 - 2^-24) * 2^127 = (2^25 - 1) * 2^103`. -/
def f32OverflowThreshold : Rat :=
  ((2 ^ 25 - 1 : Nat) : Rat) * (2 : Rat) ^ (103 : Int)

/-- BF16 ULP spacing of the binade containing magnitude bit prefix `q < 0x7f80`. -/
def bf16UlpAt (q : Nat) : Rat :=
  if q / 128 = 0 then (2 : Rat) ^ (-133 : Int)
  else (2 : Rat) ^ (((q / 128 : Nat) : Int) - 134)

/-- Binade BF16 ULP spacing for a finite IEEE-754 float64 value. -/
def f64Bf16Ulp (bits : BitVec 64) : Rat :=
  let rawExp : Nat := ((bits >>> 52) &&& 0x7ff#64).toNat
  if rawExp = 0 then (2 : Rat) ^ (-133 : Int)
  else
    let exp64 : Int := (rawExp : Int) - 1023
    if exp64 ≥ -126 then (2 : Rat) ^ (exp64 - 7)
    else (2 : Rat) ^ (-133 : Int)

/-- Binade binary32 ULP spacing for a dyadic value `m * 2^e`. -/
def dyadicF32Ulp (m e : Int) : Rat :=
  if m = 0 then (2 : Rat) ^ (-149 : Int)
  else
    let topExp : Int := e + (bitLength m.natAbs : Int) - 1
    if topExp ≥ -126 then (2 : Rat) ^ (topExp - 23)
    else (2 : Rat) ^ (-149 : Int)

/-- Exact binade binary32 ULP spacing of the infinite-precision FMA result `a * b + c`. -/
def fmafUlp (a b c : BitVec 32) : Rat :=
  let s := fmafDyadicSum a b c
  dyadicF32Ulp s.m s.e

private theorem rat_natCast_eq_intCast (n : Nat) : (n : Rat) = ((n : Int) : Rat) :=
  (Rat.intCast_natCast n).symm

private theorem rat_natCast_mul (a b : Nat) :
    ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  rw [rat_natCast_eq_intCast, Int.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast]

private theorem rat_natCast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  rw [rat_natCast_eq_intCast, rat_natCast_eq_intCast]
  exact Rat.intCast_le_intCast.mpr (Int.ofNat_le.mpr h)

private theorem rat_natCast_lt {a b : Nat} (h : a < b) : (a : Rat) < (b : Rat) := by
  rw [rat_natCast_eq_intCast, rat_natCast_eq_intCast]
  exact Rat.intCast_lt_intCast.mpr (Int.ofNat_lt.mpr h)

private theorem rat_natCast_nonneg (a : Nat) : (0 : Rat) ≤ (a : Rat) :=
  rat_natCast_le (Nat.zero_le a)

private theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rcases Rat.le_iff_lt_or_eq.mp h2 with hlt | heq
  · exact Std.lt_trans h1 hlt
  · rw [← heq]; exact h1

private theorem rat_natCast_two_pow (k : Nat) :
    ((2 ^ k : Nat) : Rat) = (2 : Rat) ^ (k : Int) := by
  rw [Rat.zpow_natCast]
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, rat_natCast_mul, ih, Rat.pow_succ]
    rfl

private theorem rat_two_zpow_div_two (e : Int) :
    (2 : Rat) ^ e / 2 = (2 : Rat) ^ (e - 1) := by
  have h1 : (2 : Rat) ^ e = (2 : Rat) ^ (e - 1) * (2 : Rat) ^ (1 : Int) := by
    rw [← Rat.zpow_add (by decide)]; congr 1; omega
  have h2 : (2 : Rat) ^ (1 : Int) = 2 := by decide
  rw [h1, h2, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel 2 (by decide), Rat.mul_one]

private theorem rat_sub_mul (a b c : Rat) : (a - b) * c = a * c - b * c := by
  rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, ← Rat.sub_eq_add_neg]

private theorem rat_mul_right_cancel {a b c : Rat} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 := congrArg (· * c⁻¹) h
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel c hc, Rat.mul_one, Rat.mul_one] at h1
  exact h1

private theorem rat_two_zpow_mono {a b : Int} (h : a ≤ b) :
    (2 : Rat) ^ a ≤ (2 : Rat) ^ b := by
  have hd : (2 : Rat) ^ b = (2 : Rat) ^ a * (2 : Rat) ^ (b - a) := by
    rw [← Rat.zpow_add (by decide)]; congr 1; omega
  rw [hd]
  have hge1 : (1 : Rat) ≤ (2 : Rat) ^ (b - a) := by
    have heq : b - a = ((b - a).toNat : Int) := by omega
    rw [heq, ← rat_natCast_two_pow]
    exact rat_natCast_le Nat.one_le_two_pow
  simpa [Rat.mul_one] using
    Rat.mul_le_mul_of_nonneg_left hge1 (Rat.le_of_lt (Rat.zpow_pos (a := 2) (n := a) (by decide)))

private theorem rat_two_zpow_strict_mono {a b : Int} (h : a < b) :
    (2 : Rat) ^ a < (2 : Rat) ^ b := by
  have hle : (2 : Rat) ^ (a + 1) ≤ (2 : Rat) ^ b := rat_two_zpow_mono (by omega)
  have hlt : (2 : Rat) ^ a < (2 : Rat) ^ (a + 1) := by
    have hp : (0 : Rat) < (2 : Rat) ^ a := Rat.zpow_pos (by decide)
    rw [Rat.zpow_add (by decide), show (2 : Rat) ^ (1 : Int) = 2 by decide]
    have h12 : (1 : Rat) < 2 := by decide
    simpa [Rat.mul_one] using Rat.mul_lt_mul_of_pos_left h12 hp
  exact rat_lt_of_lt_of_le hlt hle

private theorem rat_neg_one_mul (a : Rat) : (-1 : Rat) * a = -a := by
  rw [Rat.neg_mul, Rat.one_mul]

private theorem rat_mag_of_signed_mul {sign : Nat} {v : Rat} :
    (if sign = 1 then -((if sign = 1 then (-1 : Rat) else 1) * v)
     else (if sign = 1 then (-1 : Rat) else 1) * v) = v := by
  by_cases hs : sign = 1
  · simp only [hs, ↓reduceIte, rat_neg_one_mul, Rat.neg_neg]
  · simp only [hs, ↓reduceIte, Rat.one_mul]

private theorem rat_isRNENearest_from_mag {sign : Nat} {x y xMag yMag ulp : Rat} {isEven : Bool}
    (hx : (if sign = 1 then -x else x) = xMag)
    (hy : (if sign = 1 then -y else y) = yMag)
    (h : IsRNENearest xMag yMag ulp isEven) :
    IsRNENearest x y ulp isEven := by
  by_cases hs : sign = 1
  · simp only [hs, ↓reduceIte] at hx hy
    rcases h with ⟨h1, h2, h3⟩
    have hdiff : y - x = -(yMag - xMag) := by
      rw [← hx, ← hy, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.neg_neg, Rat.add_comm]
    have hdiff2 : x - y = yMag - xMag := by
      rw [← hx, ← hy, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_neg, Rat.add_comm]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdiff]; exact Rat.neg_le_neg h2
    · rw [hdiff]; simpa [Rat.neg_neg] using Rat.neg_le_neg h1
    · intro htie
      apply h3
      rcases htie with ht | ht
      · right
        have : xMag - yMag = -(yMag - xMag) := by
          rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm]
        rw [this, ← hdiff]; exact ht
      · left; rw [← hdiff2]; exact ht
  · simp only [hs, ↓reduceIte] at hx hy
    rw [hx, hy]; exact h

private theorem isRNENearest_exact (x ulp : Rat) (hulp : 0 < ulp) (isEven : Bool) :
    IsRNENearest x x ulp isEven := by
  have hhalf_pos : (0 : Rat) < ulp / 2 := by
    rw [Rat.div_def]; exact Rat.mul_pos hulp (Rat.inv_pos.mpr (by decide))
  have hneg_half : -(ulp / 2) ≤ 0 := by
    have h1 := Rat.neg_lt_neg hhalf_pos; rw [Rat.neg_zero] at h1; exact Rat.le_of_lt h1
  refine ⟨by rw [Rat.sub_self]; exact hneg_half, by rw [Rat.sub_self]; exact Rat.le_of_lt hhalf_pos, ?_⟩
  intro h; rw [Rat.sub_self] at h
  rcases h with h1 | h1 <;> exact absurd h1.symm (Rat.ne_of_gt hhalf_pos)

private theorem isRNENearest_zero_of_mag_lt {sign : Nat} {x ulp : Rat}
    (hnn : 0 ≤ (if sign = 1 then -x else x))
    (hlt : (if sign = 1 then -x else x) < ulp / 2) :
    IsRNENearest x 0 ulp true := by
  have hmag : IsRNENearest (if sign = 1 then -x else x) 0 ulp true := by
    refine ⟨?_, ?_, fun _ => rfl⟩
    · rw [Rat.sub_eq_add_neg, Rat.zero_add]; exact Rat.le_of_lt (Rat.neg_lt_neg hlt)
    · rw [Rat.sub_eq_add_neg, Rat.zero_add]
      have hle0 : -(if sign = 1 then -x else x) ≤ 0 := by
        simpa [Rat.neg_zero] using Rat.neg_le_neg hnn
      have hp : (0 : Rat) < ulp / 2 := Std.lt_of_le_of_lt hnn hlt
      exact Rat.le_trans hle0 (Rat.le_of_lt hp)
  have hy : (if sign = 1 then -(0 : Rat) else 0) = 0 := by split <;> decide
  exact rat_isRNENearest_from_mag rfl hy hmag

private theorem roundShiftEven_mul_two_pow (k s : Nat) (hs : 0 < s) :
    roundShiftEven (k * 2 ^ s) s = k := by
  unfold roundShiftEven
  have hne : s ≠ 0 := by omega
  have hp : 0 < 2 ^ s := Nat.pow_pos (by decide)
  have hh : 0 < 2 ^ (s - 1) := Nat.pow_pos (by decide)
  simp only [hne, ↓reduceIte, Nat.mul_div_cancel _ hp, Nat.mul_mod_left]
  split <;> omega

private theorem roundShiftEven_add_even_mul (a b s : Nat) (hs : 0 < s) (heven : a % 2 = 0) :
    roundShiftEven (a * 2 ^ s + b) s = a + roundShiftEven b s := by
  unfold roundShiftEven
  have hne : s ≠ 0 := by omega
  have hp : 0 < 2 ^ s := Nat.pow_pos (by decide)
  simp only [hne, ↓reduceIte]
  have hdiv : (a * 2 ^ s + b) / 2 ^ s = a + b / 2 ^ s := by
    rw [Nat.mul_comm a (2 ^ s), Nat.mul_add_div hp]
  have hmod : (a * 2 ^ s + b) % 2 ^ s = b % 2 ^ s := by
    rw [Nat.mul_comm a (2 ^ s), Nat.mul_add_mod]
  have hpar : (a + b / 2 ^ s) % 2 = (b / 2 ^ s) % 2 := by
    rw [Nat.add_mod, heven, Nat.zero_add, Nat.mod_mod]
  rw [hdiv, hmod, hpar]
  split <;> omega

private theorem isRNENearest_of_roundShiftEven (mag shift : Nat) (e : Int) (hs : 0 < shift) :
    IsRNENearest
      ((mag : Rat) * (2 : Rat) ^ (e - (shift : Int)))
      (((roundShiftEven mag shift : Nat) : Rat) * (2 : Rat) ^ e)
      ((2 : Rat) ^ e)
      (roundShiftEven mag shift % 2 == 0) := by
  let r := roundShiftEven mag shift
  have hp : 0 < (2 : Rat) ^ (e - (shift : Int)) := Rat.zpow_pos (by decide)
  have hpow : (2 : Rat) ^ e = ((2 ^ shift : Nat) : Rat) * (2 : Rat) ^ (e - (shift : Int)) := by
    rw [rat_natCast_two_pow shift, ← Rat.zpow_add (by decide)]; congr 1; omega
  have hhalf_pow : (2 : Rat) ^ e / 2 = ((2 ^ (shift - 1) : Nat) : Rat) * (2 : Rat) ^ (e - (shift : Int)) := by
    rw [rat_two_zpow_div_two, rat_natCast_two_pow (shift - 1), ← Rat.zpow_add (by decide)]
    congr 1; omega
  have hdiff : ((r : Rat) * (2 : Rat) ^ e) - ((mag : Rat) * (2 : Rat) ^ (e - (shift : Int))) =
      ((((r * 2 ^ shift : Nat) : Int) - (mag : Int) : Int) : Rat) * (2 : Rat) ^ (e - (shift : Int)) := by
    rw [hpow, ← Rat.mul_assoc, ← rat_natCast_mul, ← rat_sub_mul,
        Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast]
  have herr := roundShiftEven_err_le_half mag shift hs
  have hle_int : -((2 ^ (shift - 1) : Nat) : Int) ≤ ((r * 2 ^ shift : Nat) : Int) - (mag : Int) ∧
      ((r * 2 ^ shift : Nat) : Int) - (mag : Int) ≤ ((2 ^ (shift - 1) : Nat) : Int) := by
    change (((r * 2 ^ shift : Nat) : Int) - (mag : Int)).natAbs ≤ 2 ^ (shift - 1) at herr
    omega
  have hle_rat1 : -(((2 ^ (shift - 1) : Nat) : Rat)) ≤ ((((r * 2 ^ shift : Nat) : Int) - (mag : Int) : Int) : Rat) := by
    have h1 := Rat.intCast_le_intCast.mpr hle_int.1
    rw [Rat.intCast_neg, Rat.intCast_natCast] at h1; exact h1
  have hle_rat2 : ((((r * 2 ^ shift : Nat) : Int) - (mag : Int) : Int) : Rat) ≤ ((2 ^ (shift - 1) : Nat) : Rat) := by
    have h2 := Rat.intCast_le_intCast.mpr hle_int.2
    rw [Rat.intCast_natCast] at h2; exact h2
  refine ⟨?_, ?_, ?_⟩
  · change -(2 ^ e / 2) ≤ (r : Rat) * 2 ^ e - (mag : Rat) * 2 ^ (e - shift)
    rw [hdiff, hhalf_pow]
    have hm := Rat.mul_le_mul_of_nonneg_right hle_rat1 (Rat.le_of_lt hp)
    rw [Rat.neg_mul] at hm; exact hm
  · change (r : Rat) * 2 ^ e - (mag : Rat) * 2 ^ (e - shift) ≤ 2 ^ e / 2
    rw [hdiff, hhalf_pow]
    exact Rat.mul_le_mul_of_nonneg_right hle_rat2 (Rat.le_of_lt hp)
  · intro htie
    have hne0 : (2 : Rat) ^ (e - (shift : Int)) ≠ 0 := Rat.ne_of_gt hp
    have habs : ((((r * 2 ^ shift : Nat) : Int) - (mag : Int)).natAbs) = 2 ^ (shift - 1) := by
      rcases htie with h1 | h2
      · change (r : Rat) * 2 ^ e - (mag : Rat) * 2 ^ (e - shift) = 2 ^ e / 2 at h1
        rw [hdiff, hhalf_pow] at h1
        have hcancel := rat_mul_right_cancel hne0 h1
        have hint : ((r * 2 ^ shift : Nat) : Int) - (mag : Int) = ((2 ^ (shift - 1) : Nat) : Int) :=
          Rat.intCast_inj.mp (by rw [Rat.intCast_natCast]; exact hcancel)
        omega
      · change (mag : Rat) * 2 ^ (e - shift) - (r : Rat) * 2 ^ e = 2 ^ e / 2 at h2
        have hneg : (r : Rat) * 2 ^ e - (mag : Rat) * 2 ^ (e - shift) = -((2 : Rat) ^ e / 2) := by
          rw [← h2, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm]
        rw [hdiff, hhalf_pow, ← Rat.neg_mul] at hneg
        have hcancel := rat_mul_right_cancel hne0 hneg
        have hint : ((r * 2 ^ shift : Nat) : Int) - (mag : Int) = -((2 ^ (shift - 1) : Nat) : Int) :=
          Rat.intCast_inj.mp (by rw [Rat.intCast_neg, Rat.intCast_natCast]; exact hcancel)
        omega
    have heven := roundShiftEven_tie_even mag shift hs habs
    change (roundShiftEven mag shift % 2 == 0) = true
    simp only [heven, beq_self_eq_true]

private theorem nat_or_add_mul {a b k : Nat} (hb : b < 2 ^ k) :
    (a <<< k) ||| b = a * 2 ^ k + b := by
  rw [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < k
  · have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by rw [← Nat.pow_add]; congr 1; omega
    have hpos : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have hge2 : 2 ∣ 2 ^ (k - i) := by
      have hk1 : k - i = (k - i - 1) + 1 := by omega
      rw [hk1, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
    rcases hge2 with ⟨m, hm⟩
    have h1 : (a * 2 ^ k) / 2 ^ i = a * (2 * m) := by
      rw [hpow, hm, ← Nat.mul_assoc, Nat.mul_div_cancel _ hpos]
    have h2 : (a * 2 ^ k + b) / 2 ^ i = a * (2 * m) + b / 2 ^ i := by
      rw [hpow, hm, ← Nat.mul_assoc, Nat.mul_comm (a * (2 * m)) (2 ^ i), Nat.mul_add_div hpos]
    rw [h1, h2]
    have hm1 : (a * (2 * m)) % 2 = 0 := by
      rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]; omega
    have hm2 : (a * (2 * m) + b / 2 ^ i) % 2 = (b / 2 ^ i) % 2 := by
      rw [Nat.add_mod, hm1, Nat.zero_add, Nat.mod_mod]
    simp [hm1, hm2]
  · have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add]; congr 1; omega
    have hpk : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hb_div0 : b / 2 ^ k = 0 := Nat.div_eq_of_lt hb
    have hb_divi : b / 2 ^ i = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    have h1 : (a * 2 ^ k) / 2 ^ i = a / 2 ^ (i - k) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpk]
    have h2 : (a * 2 ^ k + b) / 2 ^ i = a / 2 ^ (i - k) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_comm a (2 ^ k),
          Nat.mul_add_div hpk, hb_div0, Nat.add_zero]
    rw [h1, h2, hb_divi]; simp

private theorem bv16_and_pow2 (x : BitVec 16) (k : Nat) (hk : k ≤ 16) :
    (x &&& BitVec.ofNat 16 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hlt : 2 ^ k - 1 < 2 ^ 16 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have := Nat.pow_pos (a := 2) (n := k) (by decide)
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod]

private theorem bv32_and_pow2 (x : BitVec 32) (k : Nat) (hk : k ≤ 32) :
    (x &&& BitVec.ofNat 32 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hlt : 2 ^ k - 1 < 2 ^ 32 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have := Nat.pow_pos (a := 2) (n := k) (by decide)
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod]

private theorem bv64_and_pow2 (x : BitVec 64) (k : Nat) (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hlt : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have := Nat.pow_pos (a := 2) (n := k) (by decide)
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod]

private theorem bf16OverflowThreshold_le_two_pow_128 :
    bf16OverflowThreshold ≤ (2 : Rat) ^ (128 : Int) := by
  unfold bf16OverflowThreshold
  have h1 : (2 : Rat) ^ (128 : Int) = (512 : Rat) * (2 : Rat) ^ (119 : Int) := by
    rw [show (512 : Rat) = (2 : Rat) ^ (9 : Int) by decide, ← Rat.zpow_add (by decide)]; rfl
  rw [h1]
  exact Rat.mul_le_mul_of_nonneg_right (by decide) (Rat.le_of_lt (Rat.zpow_pos (by decide)))

private theorem f32OverflowThreshold_le_two_pow_128 :
    f32OverflowThreshold ≤ (2 : Rat) ^ (128 : Int) := by
  unfold f32OverflowThreshold
  have h1 : (2 : Rat) ^ (128 : Int) = ((2 ^ 25 : Nat) : Rat) * (2 : Rat) ^ (103 : Int) := by
    rw [rat_natCast_two_pow 25, ← Rat.zpow_add (by decide)]; rfl
  rw [h1]
  exact Rat.mul_le_mul_of_nonneg_right (rat_natCast_le (by omega)) (Rat.le_of_lt (Rat.zpow_pos (by decide)))

private theorem dyadicF32Ulp_pos (m e : Int) : 0 < dyadicF32Ulp m e := by
  unfold dyadicF32Ulp; dsimp only
  split
  · exact Rat.zpow_pos (by decide)
  · split <;> exact Rat.zpow_pos (by decide)

private theorem bitLength_bounds {n : Nat} (hn : n ≠ 0) :
    2 ^ (bitLength n - 1) ≤ n ∧ n < 2 ^ (bitLength n) := by
  unfold bitLength
  simp only [hn, ↓reduceIte, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le hn, Nat.lt_log2_self⟩

-- ============================================================================
-- 2. BitVec Parts Decoders (BF16 & Float32)
-- ============================================================================

private theorem bf16_ofNat_parts_toNat {sign bexp frac : Nat}
    (hs : sign < 2) (he : bexp < 256) (hf : frac < 128) :
    (BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| frac)).toNat =
      sign * 32768 + bexp * 128 + frac := by
  have h1 : (sign <<< 15) ||| (bexp <<< 7) = (sign * 256 + bexp) <<< 7 := by
    have hlt : bexp <<< 7 < 2 ^ 15 := by rw [Nat.shiftLeft_eq]; omega
    rw [nat_or_add_mul hlt, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; omega
  have h2 : ((sign <<< 15) ||| (bexp <<< 7)) ||| frac = sign * 32768 + bexp * 128 + frac := by
    rw [h1, nat_or_add_mul (k := 7) (by omega)]; omega
  rw [BitVec.toNat_ofNat, h2, Nat.mod_eq_of_lt (by omega)]

private theorem bf16_ofNat_parts_spec {sign bexp frac : Nat}
    (hs : sign < 2) (he : bexp < 255) (hf : frac < 128) :
    let b := BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| frac)
    bf16IsFinite b = true ∧
    bf16IsNaN b = false ∧
    ((b &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    b.toNat % 2 = frac % 2 ∧
    (bf16ToDyadic b).value =
      (if sign = 1 then (-1 : Rat) else 1) *
      (if bexp = 0 then (frac : Rat) * (2 : Rat) ^ (-133 : Int)
       else ((128 + frac : Nat) : Rat) * (2 : Rat) ^ ((bexp : Int) - 134)) := by
  intro b
  have hto : b.toNat = sign * 32768 + bexp * 128 + frac :=
    bf16_ofNat_parts_toNat hs (by omega) hf
  have hexp : ((b >>> 7) &&& 0xff#16).toNat = bexp := by
    have h1 := bv16_and_pow2 (b >>> 7) 8 (by decide)
    change ((b >>> 7) &&& BitVec.ofNat 16 (2 ^ 8 - 1)).toNat = bexp
    rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hto]; omega
  have hfrac : (b &&& 0x7f#16).toNat = frac := by
    have h1 := bv16_and_pow2 b 7 (by decide)
    change (b &&& BitVec.ofNat 16 (2 ^ 7 - 1)).toNat = frac
    rw [h1, hto]; omega
  have hfin : bf16IsFinite b = true := by
    unfold bf16IsFinite; rw [bne_iff_ne]; intro hc
    have hsh : ((b &&& 0x7f80#16) >>> 7).toNat = (0x7f80#16 >>> 7).toNat := by rw [hc]
    have hshr : ((b &&& 0x7f80#16) >>> 7) = (b >>> 7) &&& 0xff#16 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      rw [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_ushiftRight, BitVec.getLsbD_and]
      have hbit : (0x7f80#16).getLsbD (7 + i) = (0xff#16)[i] := by revert i hi; decide
      rw [hbit]
    rw [hshr, hexp] at hsh
    change bexp = 255 at hsh; omega
  have hnan : bf16IsNaN b = false := by
    unfold bf16IsNaN
    have hne : ((b &&& 0x7f80#16) == 0x7f80#16) = false := by
      unfold bf16IsFinite at hfin; rw [bne_iff_ne] at hfin; exact beq_false_of_ne hfin
    rw [hne, Bool.false_and]
  have hsign : ((b &&& 0x8000#16) != 0#16) = decide (sign = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [bne_iff_ne, decide_eq_true_eq]
    have hsh : ((b &&& 0x8000#16) >>> 15).toNat = sign := by
      have h1 : ((b &&& 0x8000#16) >>> 15) = b >>> 15 := by
        apply BitVec.eq_of_getElem_eq; intro i hi
        rw [BitVec.getElem_ushiftRight, BitVec.getElem_ushiftRight, BitVec.getLsbD_and]
        by_cases h0 : i = 0
        · subst h0; simp
        · have hge : 16 ≤ 15 + i := by omega
          rw [BitVec.getLsbD_of_ge _ _ hge, Bool.false_and]
      rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hto]; omega
    constructor
    · intro hne
      by_cases hs0 : sign = 0
      · exfalso; apply hne; apply BitVec.eq_of_toNat_eq
        have hlt : b.toNat < 32768 := by omega
        rw [BitVec.toNat_and, BitVec.toNat_ofNat]
        change (b.toNat &&& 32768) = 0
        apply Nat.eq_of_testBit_eq; intro k
        rw [Nat.testBit_and, Nat.zero_testBit]
        by_cases hk : k = 15
        · subst hk; rw [Nat.testBit_lt_two_pow hlt]; rfl
        · have : (32768 : Nat).testBit k = false := by
            rw [show (32768 : Nat) = 2 ^ 15 by decide, Nat.testBit_two_pow]
            simp [Ne.symm hk]
          rw [this, Bool.and_false]
      · omega
    · intro hs1 hc
      have : ((b &&& 0x8000#16) >>> 15).toNat = 0 := by rw [hc]; rfl
      omega
  have hmod2 : b.toNat % 2 = frac % 2 := by rw [hto]; omega
  refine ⟨hfin, hnan, hsign, hmod2, ?_⟩
  unfold bf16ToDyadic Dyadic.value; dsimp only; rw [hsign, hexp, hfrac]
  by_cases hbe : bexp = 0
  · simp only [hbe, ↓reduceIte]
    by_cases hfr : frac = 0
    · simp [hfr]
    · simp only [hfr, ↓reduceIte]
      by_cases hs1 : sign = 1
      · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
          Rat.intCast_ofNat, Rat.intCast_natCast, Rat.mul_assoc]
      · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul,
          Rat.intCast_natCast, Rat.one_mul]
  · simp only [hbe, ↓reduceIte]
    by_cases hs1 : sign = 1
    · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
        Rat.intCast_ofNat, Rat.intCast_natCast, Rat.mul_assoc]
    · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul,
        Rat.intCast_natCast, Rat.one_mul]

private theorem f32_ofNat_parts_toNat {sign exp frac : Nat}
    (hs : sign < 2) (he : exp < 256) (hf : frac < 2 ^ 23) :
    (BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| frac)).toNat =
      sign * 2 ^ 31 + exp * 2 ^ 23 + frac := by
  have h1 : (sign <<< 31) ||| (exp <<< 23) = (sign * 256 + exp) <<< 23 := by
    have hlt : exp <<< 23 < 2 ^ 31 := by rw [Nat.shiftLeft_eq]; omega
    rw [nat_or_add_mul hlt, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; omega
  have h2 : ((sign <<< 31) ||| (exp <<< 23)) ||| frac = sign * 2 ^ 31 + exp * 2 ^ 23 + frac := by
    rw [h1, nat_or_add_mul (k := 23) hf]; omega
  rw [BitVec.toNat_ofNat, h2, Nat.mod_eq_of_lt (by omega)]

private theorem f32_ofNat_parts_spec {sign exp frac : Nat}
    (hs : sign < 2) (he : exp < 255) (hf : frac < 2 ^ 23) :
    let u := BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| frac)
    f32IsFinite u = true ∧
    f32IsNaN u = false ∧
    ((u >>> 31) != 0#32) = decide (sign = 1) ∧
    u.toNat % 2 = frac % 2 ∧
    (float32BitsToDyadic u).value =
      (if sign = 1 then (-1 : Rat) else 1) *
      (if exp = 0 then (frac : Rat) * (2 : Rat) ^ (-149 : Int)
       else ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150)) := by
  intro u
  have hto : u.toNat = sign * 2 ^ 31 + exp * 2 ^ 23 + frac :=
    f32_ofNat_parts_toNat hs (by omega) hf
  have hexp : ((u >>> 23) &&& 0xff#32).toNat = exp := by
    have h1 := bv32_and_pow2 (u >>> 23) 8 (by decide)
    change ((u >>> 23) &&& BitVec.ofNat 32 (2 ^ 8 - 1)).toNat = exp
    rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hto]; omega
  have hfrac : (u &&& 0x7fffff#32).toNat = frac := by
    have h1 := bv32_and_pow2 u 23 (by decide)
    change (u &&& BitVec.ofNat 32 (2 ^ 23 - 1)).toNat = frac
    rw [h1, hto]; omega
  have hfin : f32IsFinite u = true := by
    unfold f32IsFinite; rw [bne_iff_ne]; intro hc
    have : ((u >>> 23) &&& 0xff#32).toNat = (0xff#32).toNat := by rw [hc]
    rw [hexp] at this; change exp = 255 at this; omega
  have hnan : f32IsNaN u = false := by
    unfold f32IsNaN
    have hne : (((u >>> 23) &&& 0xff#32) == 0xff#32) = false := by
      unfold f32IsFinite at hfin; rw [bne_iff_ne] at hfin; exact beq_false_of_ne hfin
    rw [hne, Bool.false_and]
  have hsign : ((u >>> 31) != 0#32) = decide (sign = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq, bne_iff_ne]
    have hsh : (u >>> 31).toNat = sign := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hto]; omega
    constructor
    · intro hne; have : (u >>> 31).toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz); omega
    · intro h1 hz; have : (u >>> 31).toNat = 0 := by rw [hz]; rfl
      omega
  have hmod2 : u.toNat % 2 = frac % 2 := by rw [hto]; omega
  refine ⟨hfin, hnan, hsign, hmod2, ?_⟩
  unfold float32BitsToDyadic Dyadic.value; dsimp only; rw [hsign, hexp, hfrac]
  by_cases he0 : exp = 0
  · simp only [he0, ↓reduceIte]
    by_cases hf0 : frac = 0
    · simp [hf0]
    · simp only [hf0, ↓reduceIte]
      by_cases hs1 : sign = 1
      · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
          Rat.intCast_ofNat, Rat.intCast_natCast, Rat.mul_assoc]
      · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul,
          Rat.intCast_natCast, Rat.one_mul]
  · simp only [he0, ↓reduceIte]
    have h1s : (1 <<< 23) + frac = 2 ^ 23 + frac := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1s]
    by_cases hs1 : sign = 1
    · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
        Rat.intCast_ofNat, Rat.intCast_natCast, Rat.mul_assoc]
    · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul,
        Rat.intCast_natCast, Rat.one_mul]

-- ============================================================================
-- 3. Shared Packaging Helpers (Plain Nat/Rat Parameters — Zero BitVec `omega`!)
-- ============================================================================

private theorem bf16_pack_inf {sign : Nat} {x ulp : Rat}
    (hs : sign < 2) (hmag : bf16OverflowThreshold ≤ (if sign = 1 then -x else x)) :
    let rInf := BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80)
    bf16IsNaN rInf = false ∧
    ((rInf &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    (if bf16IsFinite rInf = true then
      IsRNENearest x (bf16ToDyadic rInf).value ulp (rInf.toNat % 2 == 0)
    else
      if decide (sign = 1) = true then rInf = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else rInf = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro rInf
  have hcases : sign = 0 ∨ sign = 1 := by omega
  rcases hcases with h0 | h1
  · subst h0
    have hr : rInf = 0x7f80#16 := by decide
    have hnf : bf16IsFinite 0x7f80#16 = false := by decide
    rw [hr]; simp only [Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte] at hmag ⊢
    rw [hnf]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, trivial, hmag⟩
  · subst h1
    have hr : rInf = 0xff80#16 := by decide
    have hnf : bf16IsFinite 0xff80#16 = false := by decide
    rw [hr]; simp only [decide_true, ↓reduceIte] at hmag ⊢
    rw [hnf]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, trivial, by simpa [Rat.neg_neg] using Rat.neg_le_neg hmag⟩

private theorem bf16_pack_zero {sign : Nat} {x : Rat}
    (hs : sign < 2)
    (hnn : 0 ≤ (if sign = 1 then -x else x))
    (hlt : (if sign = 1 then -x else x) < (2 : Rat) ^ (-134 : Int)) :
    let rZ := BitVec.ofNat 16 (sign <<< 15)
    bf16IsNaN rZ = false ∧
    ((rZ &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    (if bf16IsFinite rZ = true then
      IsRNENearest x (bf16ToDyadic rZ).value ((2 : Rat) ^ (-133 : Int)) (rZ.toNat % 2 == 0)
    else
      if decide (sign = 1) = true then rZ = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else rZ = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro rZ
  have hrZ : rZ = BitVec.ofNat 16 ((sign <<< 15) ||| (0 <<< 7) ||| 0) := by
    simp only [rZ, Nat.zero_shiftLeft, Nat.or_zero]
  have hsp := bf16_ofNat_parts_spec hs (by decide : 0 < 255) (by decide : 0 < 128)
  rw [← hrZ] at hsp
  rcases hsp with ⟨hfinZ, hnanZ, hsgnZ, hmodZ, hvalZ⟩
  rw [hfinZ, hnanZ, hsgnZ, hmodZ]
  simp only [↓reduceIte, Nat.zero_mod, beq_self_eq_true]
  have hval0 : (bf16ToDyadic rZ).value = 0 := by rw [hvalZ]; simp
  rw [hval0]
  refine ⟨trivial, trivial, isRNENearest_zero_of_mag_lt hnn ?_⟩
  rw [rat_two_zpow_div_two]; exact hlt

private theorem bf16_pack_finite {sign bexp frac : Nat} {x ulp yMag : Rat} {isEven : Bool}
    (hs : sign < 2) (he : bexp < 255) (hf : frac < 128)
    (hx : (if sign = 1 then -x else x) = xMag)
    (hy : (if bexp = 0 then (frac : Rat) * (2 : Rat) ^ (-133 : Int)
           else ((128 + frac : Nat) : Rat) * (2 : Rat) ^ ((bexp : Int) - 134)) = yMag)
    (hpar : (frac % 2 == 0) = isEven)
    (hrne : IsRNENearest xMag yMag ulp isEven) :
    let res := BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| frac)
    bf16IsNaN res = false ∧
    ((res &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    (if bf16IsFinite res = true then
      IsRNENearest x (bf16ToDyadic res).value ulp (res.toNat % 2 == 0)
    else
      if decide (sign = 1) = true then res = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else res = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro res
  have hsp := bf16_ofNat_parts_spec hs he hf
  rcases hsp with ⟨hfinR, hnanR, hsgnR, hmodR, hvalR⟩
  rw [hfinR, hnanR, hsgnR, hmodR, hpar]
  simp only [↓reduceIte]
  refine ⟨trivial, trivial, ?_⟩
  have hval_mag : (if sign = 1 then -(bf16ToDyadic res).value else (bf16ToDyadic res).value) = yMag := by
    rw [hvalR, rat_mag_of_signed_mul, hy]
  exact rat_isRNENearest_from_mag hx hval_mag hrne

private theorem f32_pack_inf {m : Int} {sign : Nat} {x ulp : Rat}
    (hsign : sign = if m < 0 then 1 else 0)
    (hmag : f32OverflowThreshold ≤ (if sign = 1 then -x else x)) :
    let rInf := BitVec.ofNat 32 ((sign <<< 31) ||| 0x7f800000)
    f32IsNaN rInf = false ∧
    ((rInf >>> 31) != 0#32) = decide (m < 0) ∧
    (if f32IsFinite rInf = true then
      IsRNENearest x (float32BitsToDyadic rInf).value ulp (rInf.toNat % 2 == 0)
    else
      if m < 0 then rInf = 0xff800000#32 ∧ x ≤ -f32OverflowThreshold
      else rInf = 0x7f800000#32 ∧ f32OverflowThreshold ≤ x) := by
  intro rInf
  by_cases hneg : m < 0
  · have hs1 : sign = 1 := by simp only [hsign, hneg, ↓reduceIte]
    have hr : rInf = 0xff800000#32 := by simp only [rInf, hs1]; decide
    have hnf : f32IsFinite 0xff800000#32 = false := by decide
    simp only [hs1, ↓reduceIte] at hmag
    rw [hr, hnf]; simp only [hneg, decide_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, trivial, by simpa [Rat.neg_neg] using Rat.neg_le_neg hmag⟩
  · have hs0 : sign = 0 := by simp only [hsign, hneg, ↓reduceIte]
    have hr : rInf = 0x7f800000#32 := by simp only [rInf, hs0]; decide
    have hnf : f32IsFinite 0x7f800000#32 = false := by decide
    simp only [hs0, Nat.zero_ne_one, ↓reduceIte] at hmag
    rw [hr, hnf]; simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, trivial, hmag⟩

private theorem f32_pack_finite {m : Int} {sign exp frac : Nat} {x ulp xMag yMag : Rat} {isEven : Bool}
    (hs : sign < 2) (hseq : decide (sign = 1) = decide (m < 0)) (he : exp < 255) (hf : frac < 2 ^ 23)
    (hx : (if sign = 1 then -x else x) = xMag)
    (hy : (if exp = 0 then (frac : Rat) * (2 : Rat) ^ (-149 : Int)
           else ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150)) = yMag)
    (hpar : (frac % 2 == 0) = isEven)
    (hrne : IsRNENearest xMag yMag ulp isEven) :
    let res := BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| frac)
    f32IsNaN res = false ∧
    ((res >>> 31) != 0#32) = decide (m < 0) ∧
    (if f32IsFinite res = true then
      IsRNENearest x (float32BitsToDyadic res).value ulp (res.toNat % 2 == 0)
    else
      if m < 0 then res = 0xff800000#32 ∧ x ≤ -f32OverflowThreshold
      else res = 0x7f800000#32 ∧ f32OverflowThreshold ≤ x) := by
  intro res
  have hsp := f32_ofNat_parts_spec hs he hf
  rcases hsp with ⟨hfinR, hnanR, hsgnR, hmodR, hvalR⟩
  rw [hfinR, hnanR, hsgnR, hseq, hmodR, hpar]
  simp only [↓reduceIte]
  refine ⟨trivial, trivial, ?_⟩
  have hval_mag : (if sign = 1 then -(float32BitsToDyadic res).value else (float32BitsToDyadic res).value) = yMag := by
    rw [hvalR, rat_mag_of_signed_mul, hy]
  exact rat_isRNENearest_from_mag hx hval_mag hrne

-- ============================================================================
-- 4. `f32BitsToBf16RNE_value_spec` (Plain-Nat Core + BitVec Wrapper)
-- ============================================================================

private theorem f32_to_bf16_core (sign exp frac : Nat) (x : Rat)
    (hs : sign < 2) (he : exp < 255) (hf : frac < 2 ^ 23)
    (hx : (if sign = 1 then -x else x) =
      (if exp = 0 then (frac : Rat) * (2 : Rat) ^ (-149 : Int)
       else ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150))) :
    let magR := roundShiftEven (exp * 2 ^ 23 + frac) 16
    let res := BitVec.ofNat 16 (sign * 32768 + magR)
    let ulp := if exp = 0 then (2 : Rat) ^ (-133 : Int) else (2 : Rat) ^ ((exp : Int) - 134)
    bf16IsNaN res = false ∧
    ((res &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    (if bf16IsFinite res = true then
      IsRNENearest x (bf16ToDyadic res).value ulp (res.toNat % 2 == 0)
    else
      if decide (sign = 1) = true then res = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else res = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro magR res ulp
  have hmagU_le : exp * 2 ^ 23 + frac ≤ 0x7f80 * 2 ^ 16 := by omega
  have hmagR_le : magR ≤ 0x7f80 := by
    have h1 := roundShiftEven_mono 16 hmagU_le
    have h2 := roundShiftEven_mul_two_pow 0x7f80 16 (by decide)
    omega
  by_cases hovf : magR = 0x7f80
  · have herr := roundShiftEven_err_le_half (exp * 2 ^ 23 + frac) 16 (by decide)
    have hge : 511 * 2 ^ 15 ≤ exp * 2 ^ 23 + frac := by
      change (((magR * 2 ^ 16 : Nat) : Int) - ((exp * 2 ^ 23 + frac : Nat) : Int)).natAbs ≤ 2 ^ 15 at herr
      rw [hovf] at herr; omega
    have he254 : exp = 254 := by omega
    have hf_ge : 2 ^ 23 - 2 ^ 15 ≤ frac := by omega
    have hres_inf : res = BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, hovf, nat_or_add_mul (k := 15) (by decide : 0x7f80 < 2 ^ 15),
          BitVec.toNat_ofNat]
    rw [hres_inf]
    apply bf16_pack_inf hs
    rw [hx, he254]
    simp only [show (254 : Nat) ≠ 0 by decide, ↓reduceIte]
    have h1 : ((511 * 2 ^ 15 : Nat) : Rat) * (2 : Rat) ^ ((254 : Int) - 150) ≤
        ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((254 : Int) - 150) :=
      Rat.mul_le_mul_of_nonneg_right (rat_natCast_le (by omega)) (Rat.le_of_lt (Rat.zpow_pos (by decide)))
    have h2 : bf16OverflowThreshold = ((511 * 2 ^ 15 : Nat) : Rat) * (2 : Rat) ^ ((254 : Int) - 150) := by
      unfold bf16OverflowThreshold
      rw [rat_natCast_mul, rat_natCast_two_pow 15, Rat.mul_assoc, ← Rat.zpow_add (by decide)]; rfl
    rw [h2]; exact h1
  · have hmagR_lt : magR < 0x7f80 := by omega
    have hres_parts : res = BitVec.ofNat 16 ((sign <<< 15) ||| ((magR / 128) <<< 7) ||| (magR % 128)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          bf16_ofNat_parts_toNat hs (by omega : magR / 128 < 256) (by omega : magR % 128 < 128)]
      omega
    rw [hres_parts]
    by_cases he0 : exp = 0
    · have hmag_eq : magR = roundShiftEven frac 16 := by simp only [magR, he0, Nat.zero_mul, Nat.zero_add]
      have hle128 : magR ≤ 128 := by
        have h1 := roundShiftEven_mono 16 (by omega : frac ≤ 128 * 2 ^ 16)
        have h2 := roundShiftEven_mul_two_pow 128 16 (by decide)
        omega
      have hrne := isRNENearest_of_roundShiftEven frac 16 (-133) (by decide)
      rw [show (-133 : Int) - ((16 : Nat) : Int) = -149 by omega, ← hmag_eq] at hrne
      have hx' : (if sign = 1 then -x else x) = (frac : Rat) * (2 : Rat) ^ (-149 : Int) := by
        rw [hx]; simp only [he0, ↓reduceIte]
      have hy : (if magR / 128 = 0 then ((magR % 128 : Nat) : Rat) * (2 : Rat) ^ (-133 : Int)
           else ((128 + magR % 128 : Nat) : Rat) * (2 : Rat) ^ (((magR / 128 : Nat) : Int) - 134)) =
          (magR : Rat) * (2 : Rat) ^ (-133 : Int) := by
        by_cases h128 : magR = 128
        · rw [h128]
          simp only [show (128 / 128 : Nat) = 1 by decide, Nat.one_ne_zero,
            show (128 % 128 : Nat) = 0 by decide, ↓reduceIte, Nat.add_zero]
          rfl
        · have hd : magR / 128 = 0 := by omega
          have hm : magR % 128 = magR := by omega
          rw [hd, hm]; simp only [↓reduceIte]
      have hpar : (magR % 128 % 2 == 0) = (magR % 2 == 0) := by
        have : magR % 128 % 2 = magR % 2 := by omega
        rw [this]
      have hulp' : ulp = (2 : Rat) ^ (-133 : Int) := by simp only [ulp, he0, ↓reduceIte]
      rw [hulp']
      exact bf16_pack_finite hs (by omega) (by omega) hx' hy hpar hrne
    · have hrel : exp * 2 ^ 23 + frac = ((exp - 1) * 128) * 2 ^ 16 + (2 ^ 23 + frac) := by omega
      have hmag_eq : magR = (exp - 1) * 128 + roundShiftEven (2 ^ 23 + frac) 16 := by
        change roundShiftEven (exp * 2 ^ 23 + frac) 16 = _
        rw [hrel]
        exact roundShiftEven_add_even_mul ((exp - 1) * 128) (2 ^ 23 + frac) 16 (by decide) (by omega)
      have hrlo : 128 ≤ roundShiftEven (2 ^ 23 + frac) 16 := by
        have h1 := roundShiftEven_mono 16 (by omega : 128 * 2 ^ 16 ≤ 2 ^ 23 + frac)
        have h2 := roundShiftEven_mul_two_pow 128 16 (by decide)
        omega
      have hrhi : roundShiftEven (2 ^ 23 + frac) 16 ≤ 256 := by
        have h1 := roundShiftEven_mono 16 (by omega : 2 ^ 23 + frac ≤ 256 * 2 ^ 16)
        have h2 := roundShiftEven_mul_two_pow 256 16 (by decide)
        omega
      have hrne := isRNENearest_of_roundShiftEven (2 ^ 23 + frac) 16 ((exp : Int) - 134) (by decide)
      rw [show ((exp : Int) - 134) - ((16 : Nat) : Int) = (exp : Int) - 150 by omega] at hrne
      have hx' : (if sign = 1 then -x else x) = ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150) := by
        rw [hx]; simp only [he0, ↓reduceIte]
      have hy : (if magR / 128 = 0 then ((magR % 128 : Nat) : Rat) * (2 : Rat) ^ (-133 : Int)
           else ((128 + magR % 128 : Nat) : Rat) * (2 : Rat) ^ (((magR / 128 : Nat) : Int) - 134)) =
          ((roundShiftEven (2 ^ 23 + frac) 16 : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 134) := by
        by_cases hc : roundShiftEven (2 ^ 23 + frac) 16 = 256
        · have hd : magR / 128 = exp + 1 := by omega
          have hm : magR % 128 = 0 := by omega
          rw [hd, hm, hc]; simp only [show exp + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_zero]
          have hbe : (((exp + 1 : Nat) : Int) - 134) = (1 : Int) + ((exp : Int) - 134) := by omega
          have h128_2 : ((128 : Nat) : Rat) * (2 : Rat) ^ (1 : Int) = ((256 : Nat) : Rat) := by
            rw [show (2 : Rat) ^ (1 : Int) = ((2 : Nat) : Rat) by decide, ← rat_natCast_mul]
          rw [hbe, Rat.zpow_add (by decide), ← Rat.mul_assoc, h128_2]
        · have hd : magR / 128 = exp := by omega
          have hm : magR % 128 = roundShiftEven (2 ^ 23 + frac) 16 - 128 := by omega
          rw [hd, hm]; simp only [he0, ↓reduceIte]
          have h128 : 128 + (roundShiftEven (2 ^ 23 + frac) 16 - 128) = roundShiftEven (2 ^ 23 + frac) 16 := by omega
          rw [h128]
      have hpar : (magR % 128 % 2 == 0) = (roundShiftEven (2 ^ 23 + frac) 16 % 2 == 0) := by
        have : magR % 128 % 2 = roundShiftEven (2 ^ 23 + frac) 16 % 2 := by omega
        rw [this]
      have hulp' : ulp = (2 : Rat) ^ ((exp : Int) - 134) := by simp only [ulp, he0, ↓reduceIte]
      rw [hulp']
      exact bf16_pack_finite hs (by omega) (by omega) hx' hy hpar hrne

/-- Real-value IEEE-754 RNE bridge for `f32BitsToBf16RNE`: connects the fast hardware bit-trick
    directly to `float32BitsToDyadic` and `bf16ToDyadic` across ALL finite float32 values. -/
theorem f32BitsToBf16RNE_value_spec (u : BitVec 32) (hfin : f32IsFinite u = true) :
    let x := (float32BitsToDyadic u).value
    let res := f32BitsToBf16RNE u
    let isNeg := (u >>> 31) != 0#32
    let ulp := bf16UlpAt ((u &&& 0x7fffffff#32).toNat / 2 ^ 16)
    bf16IsNaN res = false ∧
    ((res &&& 0x8000#16) != 0#16) = isNeg ∧
    (if bf16IsFinite res = true then
      IsRNENearest x (bf16ToDyadic res).value ulp (res.toNat % 2 == 0)
    else
      if isNeg = true then res = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else res = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro x res isNeg ulp
  have hu_lt := u.isLt
  have hsign_eq : (u >>> 31).toNat = u.toNat / 2 ^ 31 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hexp_eq : ((u >>> 23) &&& 0xff#32).toNat = (u.toNat / 2 ^ 23) % 256 := by
    have h1 := bv32_and_pow2 (u >>> 23) 8 (by decide)
    change ((u >>> 23) &&& BitVec.ofNat 32 (2 ^ 8 - 1)).toNat = _
    rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hfrac_eq : (u &&& 0x7fffff#32).toNat = u.toNat % 2 ^ 23 := by
    have h1 := bv32_and_pow2 u 23 (by decide)
    change (u &&& BitVec.ofNat 32 (2 ^ 23 - 1)).toNat = _
    rw [h1]
  have habs_eq : (u &&& 0x7fffffff#32).toNat = u.toNat % 2 ^ 31 := by
    have h1 := bv32_and_pow2 u 31 (by decide)
    change (u &&& BitVec.ofNat 32 (2 ^ 31 - 1)).toNat = _
    rw [h1]
  have hexp_ne : ((u >>> 23) &&& 0xff#32).toNat ≠ 255 := by
    unfold f32IsFinite at hfin; rw [bne_iff_ne] at hfin
    intro hc; apply hfin; apply BitVec.eq_of_toNat_eq; exact hc
  generalize hs_def : (u >>> 31).toNat = sign at hsign_eq
  generalize he_def : ((u >>> 23) &&& 0xff#32).toNat = exp at hexp_eq hexp_ne
  generalize hf_def : (u &&& 0x7fffff#32).toNat = frac at hfrac_eq
  have hsign_lt : sign < 2 := by omega
  have hexp_lt : exp < 255 := by omega
  have hfrac_lt : frac < 2 ^ 23 := by omega
  have hu_decomp : u.toNat = sign * 2 ^ 31 + exp * 2 ^ 23 + frac := by omega
  have hq_exp : (u &&& 0x7fffffff#32).toNat / 2 ^ 16 / 128 = exp := by omega
  have hisNeg : isNeg = decide (sign = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
    change ((u >>> 31) != 0#32) = true ↔ sign = 1
    rw [bne_iff_ne]
    constructor
    · intro hne; have : sign ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq (hs_def.trans hz)); omega
    · intro h1 hz; have : sign = 0 := by rw [← hs_def, hz]; rfl
      omega
  have hu_parts : u = BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| frac) := by
    apply BitVec.eq_of_toNat_eq
    rw [f32_ofNat_parts_toNat hsign_lt (by omega) hfrac_lt]; exact hu_decomp
  have hx : (if sign = 1 then -x else x) =
      (if exp = 0 then (frac : Rat) * (2 : Rat) ^ (-149 : Int)
       else ((2 ^ 23 + frac : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150)) := by
    have hsp := (f32_ofNat_parts_spec hsign_lt hexp_lt hfrac_lt).2.2.2.2
    rw [← hu_parts] at hsp
    change (if sign = 1 then -(float32BitsToDyadic u).value else (float32BitsToDyadic u).value) = _
    rw [hsp]; exact rat_mag_of_signed_mul
  have hres_eq : res = BitVec.ofNat 16 (sign * 32768 + roundShiftEven (exp * 2 ^ 23 + frac) 16) := by
    apply BitVec.eq_of_toNat_eq
    have h1 := f32BitsToBf16RNE_eq_roundShiftEven u hfin
    have h2 : u.toNat = (sign * 32768) * 2 ^ 16 + (exp * 2 ^ 23 + frac) := by
      rw [hu_decomp, Nat.mul_assoc, show (32768 : Nat) * 2 ^ 16 = 2 ^ 31 by decide, Nat.add_assoc]
    have h3 : roundShiftEven u.toNat 16 = sign * 32768 + roundShiftEven (exp * 2 ^ 23 + frac) 16 := by
      rw [h2]
      exact roundShiftEven_add_even_mul (sign * 32768) (exp * 2 ^ 23 + frac) 16 (by decide) (by omega)
    have hle : roundShiftEven (exp * 2 ^ 23 + frac) 16 ≤ 0x7f80 := by
      have ha := roundShiftEven_mono 16 (by omega : exp * 2 ^ 23 + frac ≤ 0x7f80 * 2 ^ 16)
      have hb := roundShiftEven_mul_two_pow 0x7f80 16 (by decide)
      omega
    rw [h1, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hulp_eq : ulp = (if exp = 0 then (2 : Rat) ^ (-133 : Int) else (2 : Rat) ^ ((exp : Int) - 134)) := by
    unfold ulp bf16UlpAt; rw [hq_exp]
  rw [hres_eq, hisNeg, hulp_eq]
  exact f32_to_bf16_core sign exp frac x hsign_lt hexp_lt hfrac_lt hx

-- ============================================================================
-- 5. Direct Theorems on `f64BitsToBf16RNE` (Plain-Nat Core + BitVec Wrapper)
-- ============================================================================

theorem f64BitsToBf16RNE_nan_canonical (bits : BitVec 64)
    (hexp : ((bits >>> 52) &&& 0x7ff#64).toNat = 0x7ff)
    (hfrac : (bits &&& 0xfffffffffffff#64).toNat ≠ 0) :
    f64BitsToBf16RNE bits = 0x7fc0#16 := by
  unfold f64BitsToBf16RNE; dsimp only
  simp only [hexp, ne_eq, hfrac, not_false_eq_true, ↓reduceIte]

theorem f64BitsToBf16RNE_inf (bits : BitVec 64)
    (hexp : ((bits >>> 52) &&& 0x7ff#64).toNat = 0x7ff)
    (hfrac : (bits &&& 0xfffffffffffff#64).toNat = 0) :
    f64BitsToBf16RNE bits =
      if ((bits >>> 63) &&& 1#64) != 0#64 then 0xff80#16 else 0x7f80#16 := by
  unfold f64BitsToBf16RNE; dsimp only
  simp only [hexp, hfrac, ne_eq, not_true_eq_false, ↓reduceIte]
  have hs_lt : ((bits >>> 63) &&& 1#64).toNat < 2 := by
    have h1 := bv64_and_pow2 (bits >>> 63) 1 (by decide)
    change ((bits >>> 63) &&& BitVec.ofNat 64 (2 ^ 1 - 1)).toNat < 2
    rw [h1]; omega
  by_cases hs : ((bits >>> 63) &&& 1#64) != 0#64
  · simp only [hs, ↓reduceIte]
    have hs1 : ((bits >>> 63) &&& 1#64).toNat = 1 := by
      rw [bne_iff_ne] at hs
      have hne : ((bits >>> 63) &&& 1#64).toNat ≠ 0 := fun hz => hs (BitVec.eq_of_toNat_eq hz)
      omega
    rw [hs1]; decide
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have hs0 : ((bits >>> 63) &&& 1#64).toNat = 0 := by
      have : ((bits >>> 63) &&& 1#64) = 0#64 := by simpa [bne_iff_ne] using hs
      rw [this]; rfl
    rw [hs0]; decide

private def f64Core (sign rawExp frac52 : Nat) : BitVec 16 :=
  if rawExp = 0 then
    BitVec.ofNat 16 (sign <<< 15)
  else
    let exp64 : Int := (rawExp : Int) - 1023
    let sig53 : Nat := (1 <<< 52) ||| frac52
    if exp64 > 127 then
      BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80)
    else if exp64 < -134 then
      BitVec.ofNat 16 (sign <<< 15)
    else if exp64 ≥ -126 then
      let rounded := roundShiftEven sig53 45
      let (r', bexp) :=
        if rounded ≥ 256 then (rounded >>> 1, (exp64 + 128).toNat)
        else (rounded, (exp64 + 127).toNat)
      if bexp ≥ 255 then
        BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80)
      else
        BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| (r' &&& 0x7f))
    else
      let shift := (-81 - exp64).toNat
      let rounded := roundShiftEven sig53 shift
      if rounded ≥ 128 then
        BitVec.ofNat 16 ((sign <<< 15) ||| 0x0080)
      else
        BitVec.ofNat 16 ((sign <<< 15) ||| (rounded &&& 0x7f))

private def f64UlpCore (rawExp : Nat) : Rat :=
  if rawExp = 0 then (2 : Rat) ^ (-133 : Int)
  else
    let exp64 : Int := (rawExp : Int) - 1023
    if exp64 ≥ -126 then (2 : Rat) ^ (exp64 - 7)
    else (2 : Rat) ^ (-133 : Int)

private theorem f64_to_bf16_core (sign rawExp frac52 : Nat) (x : Rat)
    (hs : sign < 2) (hraw : rawExp < 0x7ff) (hf : frac52 < 2 ^ 52)
    (hx : (if sign = 1 then -x else x) =
      (if rawExp = 0 then (frac52 : Rat) * (2 : Rat) ^ (-1074 : Int)
       else ((2 ^ 52 + frac52 : Nat) : Rat) * (2 : Rat) ^ ((rawExp : Int) - 1075))) :
    let res := f64Core sign rawExp frac52
    bf16IsNaN res = false ∧
    ((res &&& 0x8000#16) != 0#16) = decide (sign = 1) ∧
    (if bf16IsFinite res = true then
      IsRNENearest x (bf16ToDyadic res).value (f64UlpCore rawExp) (res.toNat % 2 == 0)
    else
      if decide (sign = 1) = true then res = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else res = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro res
  by_cases hraw0 : rawExp = 0
  · have hres : res = BitVec.ofNat 16 (sign <<< 15) := by
      unfold res f64Core; simp only [hraw0, ↓reduceIte]
    have hulp : f64UlpCore rawExp = (2 : Rat) ^ (-133 : Int) := by
      unfold f64UlpCore; simp only [hraw0, ↓reduceIte]
    have hx0 : (if sign = 1 then -x else x) = (frac52 : Rat) * (2 : Rat) ^ (-1074 : Int) := by
      rw [hx]; simp only [hraw0, ↓reduceIte]
    have hnn : 0 ≤ (if sign = 1 then -x else x) := by
      rw [hx0]; exact Rat.mul_nonneg (rat_natCast_nonneg frac52) (Rat.le_of_lt (Rat.zpow_pos (by decide)))
    have hlt : (if sign = 1 then -x else x) < (2 : Rat) ^ (-134 : Int) := by
      rw [hx0]
      have h1 := Rat.mul_lt_mul_of_pos_right (rat_natCast_lt hf) (Rat.zpow_pos (a := 2) (n := -1074) (by decide))
      have h2 : ((2 ^ 52 : Nat) : Rat) * (2 : Rat) ^ (-1074 : Int) < (2 : Rat) ^ (-134 : Int) := by
        rw [rat_natCast_two_pow 52, ← Rat.zpow_add (by decide)]
        exact rat_two_zpow_strict_mono (by decide)
      exact Std.lt_trans h1 h2
    rw [hres, hulp]
    exact bf16_pack_zero hs hnn hlt
  · have hsig_eq : (1 <<< 52) ||| frac52 = 2 ^ 52 + frac52 := by
      have := nat_or_add_mul (a := 1) (b := frac52) (k := 52) hf
      simpa using this
    generalize hexp64 : (rawExp : Int) - 1023 = exp64
    generalize hsig53 : (2 ^ 52 + frac52 : Nat) = sig53 at hsig_eq
    have hsig_lo : 2 ^ 52 ≤ sig53 := by omega
    have hsig_hi : sig53 < 2 ^ 53 := by omega
    have hx_mag : (if sign = 1 then -x else x) = (sig53 : Rat) * (2 : Rat) ^ (exp64 - 52) := by
      rw [hx]; simp only [hraw0, ↓reduceIte]
      rw [hsig53, show (rawExp : Int) - 1075 = exp64 - 52 by omega]
    by_cases hgt127 : exp64 > 127
    · have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80) := by
        unfold res f64Core; dsimp only; rw [hexp64]
        simp only [hraw0, hgt127, ↓reduceIte]
      rw [hres]; apply bf16_pack_inf hs; rw [hx_mag]
      have h1 := Rat.mul_le_mul_of_nonneg_right (rat_natCast_le hsig_lo)
        (Rat.le_of_lt (Rat.zpow_pos (a := 2) (n := exp64 - 52) (by decide)))
      have h2 : (2 : Rat) ^ (128 : Int) ≤ ((2 ^ 52 : Nat) : Rat) * (2 : Rat) ^ (exp64 - 52) := by
        rw [rat_natCast_two_pow 52, ← Rat.zpow_add (by decide), show ((52 : Nat) : Int) + (exp64 - 52) = exp64 by omega]
        exact rat_two_zpow_mono (by omega)
      exact Rat.le_trans bf16OverflowThreshold_le_two_pow_128 (Rat.le_trans h2 h1)
    · by_cases hlt134 : exp64 < -134
      · have hres : res = BitVec.ofNat 16 (sign <<< 15) := by
          unfold res f64Core; dsimp only; rw [hexp64]
          simp only [hraw0, hgt127, hlt134, ↓reduceIte]
        have hulp : f64UlpCore rawExp = (2 : Rat) ^ (-133 : Int) := by
          unfold f64UlpCore; dsimp only; rw [hexp64]
          have hnot : ¬ (exp64 ≥ -126) := by omega
          simp only [hraw0, hnot, ↓reduceIte]
        have hnn : 0 ≤ (if sign = 1 then -x else x) := by
          rw [hx_mag]; exact Rat.mul_nonneg (rat_natCast_nonneg sig53) (Rat.le_of_lt (Rat.zpow_pos (by decide)))
        have hlt : (if sign = 1 then -x else x) < (2 : Rat) ^ (-134 : Int) := by
          rw [hx_mag]
          have h1 := Rat.mul_lt_mul_of_pos_right (rat_natCast_lt hsig_hi)
            (Rat.zpow_pos (a := 2) (n := exp64 - 52) (by decide))
          have h2 : ((2 ^ 53 : Nat) : Rat) * (2 : Rat) ^ (exp64 - 52) ≤ (2 : Rat) ^ (-134 : Int) := by
            rw [rat_natCast_two_pow 53, ← Rat.zpow_add (by decide), show ((53 : Nat) : Int) + (exp64 - 52) = exp64 + 1 by omega]
            exact rat_two_zpow_mono (by omega)
          exact rat_lt_of_lt_of_le h1 h2
        rw [hres, hulp]; exact bf16_pack_zero hs hnn hlt
      · by_cases hge126 : exp64 ≥ -126
        · have hulp : f64UlpCore rawExp = (2 : Rat) ^ (exp64 - 7) := by
            unfold f64UlpCore; dsimp only; rw [hexp64]; simp only [hraw0, hge126, ↓reduceIte]
          have hrne_mag := isRNENearest_of_roundShiftEven sig53 45 (exp64 - 7) (by decide)
          rw [show (exp64 - 7) - ((45 : Nat) : Int) = exp64 - 52 by omega] at hrne_mag
          have hlo_r : 128 ≤ roundShiftEven sig53 45 := by
            have h1 := roundShiftEven_mono 45 (by omega : 128 * 2 ^ 45 ≤ sig53)
            have h2 := roundShiftEven_mul_two_pow 128 45 (by decide); omega
          have hhi_r : roundShiftEven sig53 45 ≤ 256 := by
            have h1 := roundShiftEven_mono 45 (by omega : sig53 ≤ 256 * 2 ^ 45)
            have h2 := roundShiftEven_mul_two_pow 256 45 (by decide); omega
          have herr45 := roundShiftEven_err_le_half sig53 45 (by decide)
          generalize hr_def : roundShiftEven sig53 45 = rounded at hrne_mag hlo_r hhi_r herr45
          by_cases hcarry : rounded ≥ 256
          · have hr256 : rounded = 256 := by omega
            by_cases hovf : (exp64 + 128).toNat ≥ 255
            · have he127 : exp64 = 127 := by omega
              have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| 0x7f80) := by
                unfold res f64Core; dsimp only; rw [hexp64, hsig_eq, hr_def]
                simp only [hraw0, hgt127, hlt134, hge126, hcarry, hovf, ↓reduceIte]
              rw [hres]; apply bf16_pack_inf hs; rw [hx_mag, he127]
              have hsig_ge : 511 * 2 ^ 44 ≤ sig53 := by rw [hr256] at herr45; omega
              have h1 := Rat.mul_le_mul_of_nonneg_right (rat_natCast_le hsig_ge)
                (Rat.le_of_lt (Rat.zpow_pos (a := 2) (n := 127 - 52) (by decide)))
              have h2 : bf16OverflowThreshold = ((511 * 2 ^ 44 : Nat) : Rat) * (2 : Rat) ^ (127 - 52 : Int) := by
                unfold bf16OverflowThreshold
                rw [rat_natCast_mul, rat_natCast_two_pow 44, Rat.mul_assoc, ← Rat.zpow_add (by decide)]; rfl
              rw [h2]; exact h1
            · generalize hbe_def : (exp64 + 128).toNat = bexp at hovf
              have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| 0) := by
                unfold res f64Core; dsimp only; rw [hexp64, hsig_eq, hr_def]
                simp only [hraw0, hgt127, hlt134, hge126, hcarry, ↓reduceIte]
                rw [hbe_def]; simp only [hovf, ↓reduceIte]
                have hr0 : (rounded >>> 1) &&& 0x7f = 0 := by rw [hr256]; decide
                rw [hr0]
              rw [hres, hulp]
              have hy : (if bexp = 0 then ((0 : Nat) : Rat) * (2 : Rat) ^ (-133 : Int)
                   else ((128 + 0 : Nat) : Rat) * (2 : Rat) ^ ((bexp : Int) - 134)) =
                  (rounded : Rat) * (2 : Rat) ^ (exp64 - 7) := by
                simp only [show bexp ≠ 0 by omega, ↓reduceIte, Nat.add_zero, hr256]
                have hbe : (bexp : Int) - 134 = (1 : Int) + (exp64 - 7) := by omega
                have h128_2 : ((128 : Nat) : Rat) * (2 : Rat) ^ (1 : Int) = ((256 : Nat) : Rat) := by
                  rw [show (2 : Rat) ^ (1 : Int) = ((2 : Nat) : Rat) by decide, ← rat_natCast_mul]
                rw [hbe, Rat.zpow_add (by decide), ← Rat.mul_assoc, h128_2]
              have hpar : (0 % 2 == 0) = (rounded % 2 == 0) := by rw [hr256]
              exact bf16_pack_finite hs (by omega) (by decide) hx_mag hy hpar hrne_mag
          · generalize hbe_def : (exp64 + 127).toNat = bexp
            have hnot_ovf : ¬ (bexp ≥ 255) := by omega
            have hfrac_eq : rounded &&& 0x7f = rounded - 128 := by
              have : rounded &&& (2 ^ 7 - 1) = rounded % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod rounded 7
              change rounded &&& (2 ^ 7 - 1) = _; rw [this]; omega
            have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| (bexp <<< 7) ||| (rounded - 128)) := by
              unfold res f64Core; dsimp only; rw [hexp64, hsig_eq, hr_def]
              simp only [hraw0, hgt127, hlt134, hge126, hcarry, ↓reduceIte]
              rw [hbe_def]; simp only [hnot_ovf, ↓reduceIte, hfrac_eq]
            rw [hres, hulp]
            have hy : (if bexp = 0 then ((rounded - 128 : Nat) : Rat) * (2 : Rat) ^ (-133 : Int)
                 else ((128 + (rounded - 128) : Nat) : Rat) * (2 : Rat) ^ ((bexp : Int) - 134)) =
                (rounded : Rat) * (2 : Rat) ^ (exp64 - 7) := by
              simp only [show bexp ≠ 0 by omega, ↓reduceIte]
              rw [show 128 + (rounded - 128) = rounded by omega,
                  show (bexp : Int) - 134 = exp64 - 7 by omega]
            have hpar : ((rounded - 128) % 2 == 0) = (rounded % 2 == 0) := by
              have hmod : (rounded - 128) % 2 = rounded % 2 := by omega
              rw [hmod]
            exact bf16_pack_finite hs (by omega) (by omega) hx_mag hy hpar hrne_mag
        · have hulp : f64UlpCore rawExp = (2 : Rat) ^ (-133 : Int) := by
            unfold f64UlpCore; dsimp only; rw [hexp64]; simp only [hraw0, hge126, ↓reduceIte]
          generalize hsh_def : (-81 - exp64).toNat = shift
          have hsh_pos : 0 < shift := by omega
          have hhi_r : roundShiftEven sig53 shift ≤ 128 := by
            have h1 : 2 ^ 46 ≤ 2 ^ shift := Nat.pow_le_pow_right (by decide) (by omega)
            have h2 := roundShiftEven_mono shift (by omega : sig53 ≤ 128 * 2 ^ shift)
            have h3 := roundShiftEven_mul_two_pow 128 shift hsh_pos; omega
          have hrne_mag := isRNENearest_of_roundShiftEven sig53 shift (-133) hsh_pos
          rw [show (-133 : Int) - (shift : Int) = exp64 - 52 by omega] at hrne_mag
          generalize hr_def : roundShiftEven sig53 shift = rounded at hhi_r hrne_mag
          by_cases hcarry : rounded ≥ 128
          · have hr128 : rounded = 128 := by omega
            have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| (1 <<< 7) ||| 0) := by
              unfold res f64Core; dsimp only; rw [hexp64, hsig_eq, hsh_def, hr_def]
              simp only [hraw0, hgt127, hlt134, hge126, hcarry, ↓reduceIte, Nat.or_zero,
                show (1 <<< 7 : Nat) = 128 by decide]
            rw [hres, hulp]
            have hy : (if (1 : Nat) = 0 then ((0 : Nat) : Rat) * (2 : Rat) ^ (-133 : Int)
                 else ((128 + 0 : Nat) : Rat) * (2 : Rat) ^ ((1 : Int) - 134)) =
                (rounded : Rat) * (2 : Rat) ^ (-133 : Int) := by
              rw [hr128]; simp only [Nat.one_ne_zero, ↓reduceIte, Nat.add_zero]; rfl
            have hpar : (0 % 2 == 0) = (rounded % 2 == 0) := by rw [hr128]
            exact bf16_pack_finite hs (by decide) (by decide) hx_mag hy hpar hrne_mag
          · have hfrac_eq : rounded &&& 0x7f = rounded := by
              have : rounded &&& (2 ^ 7 - 1) = rounded % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod rounded 7
              change rounded &&& (2 ^ 7 - 1) = _; rw [this]; omega
            have hres : res = BitVec.ofNat 16 ((sign <<< 15) ||| (0 <<< 7) ||| rounded) := by
              unfold res f64Core; dsimp only; rw [hexp64, hsig_eq, hsh_def, hr_def]
              simp only [hraw0, hgt127, hlt134, hge126, hcarry, ↓reduceIte, hfrac_eq,
                Nat.zero_shiftLeft, Nat.or_zero]
            rw [hres, hulp]
            have hy : (if (0 : Nat) = 0 then (rounded : Rat) * (2 : Rat) ^ (-133 : Int)
                 else ((128 + rounded : Nat) : Rat) * (2 : Rat) ^ ((0 : Int) - 134)) =
                (rounded : Rat) * (2 : Rat) ^ (-133 : Int) := by simp only [↓reduceIte]
            exact bf16_pack_finite hs (by decide) (by omega) hx_mag hy rfl hrne_mag

/-- Proves universal mathematical IEEE-754 RNE correctness (zero double rounding) directly on
    `f64BitsToBf16RNE` against the independent rational specification `float64BitsToDyadic`. -/
theorem f64BitsToBf16RNE_value_spec (bits : BitVec 64) (hfin : f64IsFinite bits = true) :
    let x := (float64BitsToDyadic bits).value
    let res := f64BitsToBf16RNE bits
    let isNeg := ((bits >>> 63) &&& 1#64) != 0#64
    bf16IsNaN res = false ∧
    ((res &&& 0x8000#16) != 0#16) = isNeg ∧
    (if bf16IsFinite res = true then
      IsRNENearest x (bf16ToDyadic res).value (f64Bf16Ulp bits) (res.toNat % 2 == 0)
    else
      if isNeg = true then res = 0xff80#16 ∧ x ≤ -bf16OverflowThreshold
      else res = 0x7f80#16 ∧ bf16OverflowThreshold ≤ x) := by
  intro x res isNeg
  have hsign_lt : ((bits >>> 63) &&& 1#64).toNat < 2 := by
    have h1 := bv64_and_pow2 (bits >>> 63) 1 (by decide)
    change ((bits >>> 63) &&& BitVec.ofNat 64 (2 ^ 1 - 1)).toNat < 2; rw [h1]; omega
  have hfrac_lt : (bits &&& 0xfffffffffffff#64).toNat < 2 ^ 52 := by
    have h1 := bv64_and_pow2 bits 52 (by decide)
    change (bits &&& BitVec.ofNat 64 (2 ^ 52 - 1)).toNat < 2 ^ 52; rw [h1]; omega
  have hraw_lt : ((bits >>> 52) &&& 0x7ff#64).toNat < 0x7ff := by
    have h1 := bv64_and_pow2 (bits >>> 52) 11 (by decide)
    have hlt2048 : ((bits >>> 52) &&& 0x7ff#64).toNat < 2 ^ 11 := by
      change ((bits >>> 52) &&& BitVec.ofNat 64 (2 ^ 11 - 1)).toNat < 2 ^ 11; rw [h1]; omega
    unfold f64IsFinite at hfin; rw [bne_iff_ne] at hfin
    have hne : ((bits >>> 52) &&& 0x7ff#64).toNat ≠ 0x7ff := fun hc =>
      hfin (BitVec.eq_of_toNat_eq hc)
    omega
  have hisNeg : isNeg = decide (((bits >>> 63) &&& 1#64).toNat = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
    change (((bits >>> 63) &&& 1#64) != 0#64) = true ↔ _
    rw [bne_iff_ne]
    constructor
    · intro hne; have : ((bits >>> 63) &&& 1#64).toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz); omega
    · intro h1 hz; have : ((bits >>> 63) &&& 1#64).toNat = 0 := by rw [hz]; rfl
      omega
  have hraw_ne : ((bits >>> 52) &&& 0x7ff#64).toNat ≠ 0x7ff := by omega
  have hres_eq : res = f64Core ((bits >>> 63) &&& 1#64).toNat ((bits >>> 52) &&& 0x7ff#64).toNat (bits &&& 0xfffffffffffff#64).toNat := by
    change f64BitsToBf16RNE bits = _
    unfold f64BitsToBf16RNE f64Core; dsimp only; simp only [hraw_ne, ↓reduceIte]
  have hulp_eq : f64Bf16Ulp bits = f64UlpCore ((bits >>> 52) &&& 0x7ff#64).toNat := rfl
  have hx : (if ((bits >>> 63) &&& 1#64).toNat = 1 then -x else x) =
      (if ((bits >>> 52) &&& 0x7ff#64).toNat = 0 then ((bits &&& 0xfffffffffffff#64).toNat : Rat) * (2 : Rat) ^ (-1074 : Int)
       else ((2 ^ 52 + (bits &&& 0xfffffffffffff#64).toNat : Nat) : Rat) * (2 : Rat) ^ ((((bits >>> 52) &&& 0x7ff#64).toNat : Int) - 1075)) := by
    change (if ((bits >>> 63) &&& 1#64).toNat = 1 then -(float64BitsToDyadic bits).value else (float64BitsToDyadic bits).value) = _
    unfold float64BitsToDyadic Dyadic.value; dsimp only
    rw [show (((bits >>> 63) &&& 1#64) != 0#64) = decide (((bits >>> 63) &&& 1#64).toNat = 1) from hisNeg]
    by_cases hr0 : ((bits >>> 52) &&& 0x7ff#64).toNat = 0
    · simp only [hr0, ↓reduceIte]
      by_cases hf0 : (bits &&& 0xfffffffffffff#64).toNat = 0
      · simp only [hf0, ↓reduceIte, show ((0 : Nat) : Rat) = 0 from rfl,
          show ((0 : Int) : Rat) = 0 from rfl, Rat.zero_mul, Rat.neg_zero]
        split <;> rfl
      · simp only [hf0, ↓reduceIte]
        by_cases hs1 : ((bits >>> 63) &&& 1#64).toNat = 1
        · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
            Rat.intCast_ofNat, Rat.intCast_natCast, Rat.neg_mul, Rat.one_mul, Rat.neg_neg]
        · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Rat.intCast_natCast]
    · simp only [hr0, ↓reduceIte]
      have h1s : (1 <<< 52) + (bits &&& 0xfffffffffffff#64).toNat = 2 ^ 52 + (bits &&& 0xfffffffffffff#64).toNat := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [h1s]
      by_cases hs1 : ((bits >>> 63) &&& 1#64).toNat = 1
      · simp only [hs1, decide_true, ↓reduceIte, Rat.intCast_mul, Rat.intCast_neg,
          Rat.intCast_ofNat, Rat.intCast_natCast, Rat.neg_mul, Rat.one_mul, Rat.neg_neg]
      · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Rat.intCast_natCast]
  rw [hres_eq, hulp_eq, hisNeg]
  exact f64_to_bf16_core _ _ _ x hsign_lt hraw_lt hfrac_lt hx

-- ============================================================================
-- 6. Direct Theorems on `dyadicToF32BitsRNE` & `fmafFiniteBits`
-- ============================================================================

private theorem dyadic_to_f32_core (m e : Int) (sign mag bitLen : Nat) (topExp : Int)
    (hm0 : m ≠ 0) (hsign : sign = if m < 0 then 1 else 0) (hmag : mag = m.natAbs)
    (hbl : bitLen = bitLength mag) (htop : topExp = e + (bitLen : Int) - 1) :
    let x := (Dyadic.mk m e).value
    let res := dyadicToF32BitsRNE m e
    f32IsNaN res = false ∧
    ((res >>> 31) != 0#32) = decide (m < 0) ∧
    (if f32IsFinite res = true then
      IsRNENearest x (float32BitsToDyadic res).value (dyadicF32Ulp m e) (res.toNat % 2 == 0)
    else
      if m < 0 then res = 0xff800000#32 ∧ x ≤ -f32OverflowThreshold
      else res = 0x7f800000#32 ∧ f32OverflowThreshold ≤ x) := by
  intro x res
  have hsign_lt : sign < 2 := by rw [hsign]; split <;> decide
  have hsign_eq : decide (sign = 1) = decide (m < 0) := by rw [hsign]; split <;> simp [*]
  have hmag_ne : mag ≠ 0 := by omega
  have hbl_pos : 1 ≤ bitLen := by rw [hbl]; unfold bitLength; simp only [hmag_ne, ↓reduceIte]; omega
  have ⟨hmag_lo, hmag_hi⟩ := bitLength_bounds hmag_ne
  rw [← hbl] at hmag_lo hmag_hi
  have hx_mag : (if sign = 1 then -x else x) = (mag : Rat) * (2 : Rat) ^ e := by
    change (if sign = 1 then -((m : Rat) * (2 : Rat) ^ e) else (m : Rat) * (2 : Rat) ^ e) = _
    by_cases hneg : m < 0
    · have hs1 : sign = 1 := by simp only [hsign, hneg, ↓reduceIte]
      have hm_eq : m = -((mag : Nat) : Int) := by omega
      simp only [hs1, ↓reduceIte, hm_eq, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul, Rat.neg_neg]
    · have hs0 : sign = 0 := by simp only [hsign, hneg, ↓reduceIte]
      have hm_eq : m = ((mag : Nat) : Int) := by omega
      simp only [hs0, Nat.zero_ne_one, ↓reduceIte, hm_eq, Rat.intCast_natCast]
  by_cases hgt127 : topExp > 127
  · have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| 0x7f800000) := by
      change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
      rw [← hsign, ← hmag, ← hbl, ← htop]; simp only [hm0, hgt127, ↓reduceIte]
    rw [hres]
    apply f32_pack_inf hsign; rw [hx_mag]
    have h1 := Rat.mul_le_mul_of_nonneg_right (rat_natCast_le hmag_lo)
      (Rat.le_of_lt (Rat.zpow_pos (a := 2) (n := e) (by decide)))
    have h2 : (2 : Rat) ^ (128 : Int) ≤ ((2 ^ (bitLen - 1) : Nat) : Rat) * (2 : Rat) ^ e := by
      rw [rat_natCast_two_pow (bitLen - 1), ← Rat.zpow_add (by decide),
          show ((bitLen - 1 : Nat) : Int) + e = topExp by omega]
      exact rat_two_zpow_mono (by omega)
    exact Rat.le_trans f32OverflowThreshold_le_two_pow_128 (Rat.le_trans h2 h1)
  · by_cases hlt150 : topExp < -150
    · have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| (0 <<< 23) ||| 0) := by
        change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
        rw [← hsign, ← hmag, ← hbl, ← htop]
        simp only [hm0, hgt127, hlt150, ↓reduceIte, Nat.zero_shiftLeft, Nat.or_zero]
      have hulp : dyadicF32Ulp m e = (2 : Rat) ^ (-149 : Int) := by
        unfold dyadicF32Ulp; dsimp only; rw [← hmag, ← hbl, ← htop]
        have hnot : ¬ (topExp ≥ -126) := by omega
        simp only [hm0, hnot, ↓reduceIte]
      have hnn : 0 ≤ (if sign = 1 then -x else x) := by
        rw [hx_mag]; exact Rat.mul_nonneg (rat_natCast_nonneg mag) (Rat.le_of_lt (Rat.zpow_pos (by decide)))
      have hlt : (if sign = 1 then -x else x) < (2 : Rat) ^ (-150 : Int) := by
        rw [hx_mag]
        have h1 := Rat.mul_lt_mul_of_pos_right (rat_natCast_lt hmag_hi) (Rat.zpow_pos (a := 2) (n := e) (by decide))
        have h2 : ((2 ^ bitLen : Nat) : Rat) * (2 : Rat) ^ e ≤ (2 : Rat) ^ (-150 : Int) := by
          rw [rat_natCast_two_pow bitLen, ← Rat.zpow_add (by decide), show (bitLen : Int) + e = topExp + 1 by omega]
          exact rat_two_zpow_mono (by omega)
        exact rat_lt_of_lt_of_le h1 h2
      rw [hres, hulp]
      have hsp := f32_ofNat_parts_spec hsign_lt (by decide : 0 < 255) (by omega : 0 < 2 ^ 23)
      rcases hsp with ⟨hfinZ, hnanZ, hsgnZ, hmodZ, hvalZ⟩
      rw [hfinZ, hnanZ, hsgnZ, hsign_eq, hmodZ]
      simp only [↓reduceIte, Nat.zero_mod, beq_self_eq_true]
      have hval0 : (float32BitsToDyadic (BitVec.ofNat 32 ((sign <<< 31) ||| (0 <<< 23) ||| 0))).value = 0 := by
        rw [hvalZ]; simp
      rw [hval0]
      refine ⟨trivial, trivial, isRNENearest_zero_of_mag_lt hnn ?_⟩
      rw [rat_two_zpow_div_two]; exact hlt
    · by_cases hge126 : topExp ≥ -126
      · have hulp : dyadicF32Ulp m e = (2 : Rat) ^ (topExp - 23) := by
          unfold dyadicF32Ulp; dsimp only; rw [← hmag, ← hbl, ← htop]; simp only [hm0, hge126, ↓reduceIte]
        generalize hsh_def : (bitLen : Int) - 24 = shift
        generalize hsig_def : (if shift ≤ 0 then mag <<< (-shift).toNat else roundShiftEven mag shift.toNat) = sig
        have hsig_bounds : 2 ^ 23 ≤ sig ∧ sig ≤ 2 ^ 24 := by
          by_cases hsh : shift ≤ 0
          · have hsig_eq : sig = mag * 2 ^ (-shift).toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte, Nat.shiftLeft_eq]
            have hp1 : (bitLen - 1) + (-shift).toNat = 23 := by omega
            have hp2 : bitLen + (-shift).toNat = 24 := by omega
            have hlo : 2 ^ 23 ≤ mag * 2 ^ (-shift).toNat := by
              rw [← hp1, Nat.pow_add]; exact Nat.mul_le_mul_right _ hmag_lo
            have hhi : mag * 2 ^ (-shift).toNat < 2 ^ 24 := by
              rw [← hp2, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hmag_hi (Nat.pow_pos (by decide))
            omega
          · have hsig_eq : sig = roundShiftEven mag shift.toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte]
            have hsp : 0 < shift.toNat := by omega
            have hlo_m : 2 ^ 23 * 2 ^ shift.toNat ≤ mag := by
              rw [← Nat.pow_add, show 23 + shift.toNat = bitLen - 1 by omega]; exact hmag_lo
            have hhi_m : mag ≤ 2 ^ 24 * 2 ^ shift.toNat := by
              rw [← Nat.pow_add, show 24 + shift.toNat = bitLen by omega]; omega
            have h1 := roundShiftEven_mono shift.toNat hlo_m
            have h2 := roundShiftEven_mul_two_pow (2 ^ 23) shift.toNat hsp
            have h3 := roundShiftEven_mono shift.toNat hhi_m
            have h4 := roundShiftEven_mul_two_pow (2 ^ 24) shift.toNat hsp
            omega
        have hrne_sig : IsRNENearest ((mag : Rat) * (2 : Rat) ^ e)
            ((sig : Rat) * (2 : Rat) ^ (topExp - 23)) ((2 : Rat) ^ (topExp - 23)) (sig % 2 == 0) := by
          by_cases hsh : shift ≤ 0
          · have hsig_eq : sig = mag * 2 ^ (-shift).toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte, Nat.shiftLeft_eq]
            have hval_eq : (sig : Rat) * (2 : Rat) ^ (topExp - 23) = (mag : Rat) * (2 : Rat) ^ e := by
              rw [hsig_eq, rat_natCast_mul, Rat.mul_assoc,
                  rat_natCast_two_pow (-shift).toNat, ← Rat.zpow_add (by decide)]
              congr 2; omega
            rw [hval_eq]; exact isRNENearest_exact _ _ (Rat.zpow_pos (by decide)) _
          · have hsig_eq : sig = roundShiftEven mag shift.toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte]
            have hr := isRNENearest_of_roundShiftEven mag shift.toNat (topExp - 23) (by omega)
            rw [show (topExp - 23) - (shift.toNat : Int) = e by omega, ← hsig_eq] at hr
            exact hr
        by_cases hcarry : sig ≥ (1 <<< 24)
        · have hs24 : sig = 2 ^ 24 := by
            have : (1 <<< 24 : Nat) = 2 ^ 24 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
            omega
          by_cases hovf : (topExp + 128).toNat ≥ 255
          · have ht127 : topExp = 127 := by omega
            have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| 0x7f800000) := by
              change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
              rw [← hsign, ← hmag, ← hbl, ← htop]
              simp only [hm0, hgt127, hlt150, hge126, ↓reduceIte]
              rw [hsh_def, hsig_def]; simp only [hcarry, hovf, ↓reduceIte]
            rw [hres]; apply f32_pack_inf hsign; rw [hx_mag]
            have hle := hrne_sig.2.1; rw [hs24, ht127] at hle
            have hsub : ((2 ^ 24 : Nat) : Rat) * (2 : Rat) ^ (127 - 23 : Int) -
                (2 : Rat) ^ (127 - 23 : Int) / 2 ≤ (mag : Rat) * (2 : Rat) ^ e := by
              have h1 : (mag : Rat) * (2 : Rat) ^ e +
                  (((2 ^ 24 : Nat) : Rat) * (2 : Rat) ^ (127 - 23 : Int) - (mag : Rat) * (2 : Rat) ^ e) ≤
                  (mag : Rat) * (2 : Rat) ^ e + (2 : Rat) ^ (127 - 23 : Int) / 2 :=
                Rat.add_le_add_left.mpr hle
              have h2 : (mag : Rat) * (2 : Rat) ^ e +
                  (((2 ^ 24 : Nat) : Rat) * (2 : Rat) ^ (127 - 23 : Int) - (mag : Rat) * (2 : Rat) ^ e) =
                  ((2 ^ 24 : Nat) : Rat) * (2 : Rat) ^ (127 - 23 : Int) := by
                rw [Rat.add_comm, Rat.sub_add_cancel]
              rw [h2] at h1
              have h3 := Rat.add_le_add_left (c := -((2 : Rat) ^ (127 - 23 : Int) / 2)).mpr h1
              rw [Rat.add_comm (-_), ← Rat.sub_eq_add_neg,
                  Rat.add_comm (-_), ← Rat.sub_eq_add_neg, Rat.add_sub_cancel] at h3
              exact h3
            have hth : ((2 ^ 24 : Nat) : Rat) * (2 : Rat) ^ (127 - 23 : Int) -
                (2 : Rat) ^ (127 - 23 : Int) / 2 = f32OverflowThreshold := by
              unfold f32OverflowThreshold
              have hpow104 : (2 : Rat) ^ (127 - 23 : Int) = (2 : Rat) * (2 : Rat) ^ (103 : Int) := by
                have h1 : (2 : Rat) ^ (127 - 23 : Int) = (2 : Rat) ^ (1 : Int) * (2 : Rat) ^ (103 : Int) := by
                  rw [← Rat.zpow_add (by decide)]; rfl
                rw [h1, show (2 : Rat) ^ (1 : Int) = 2 by decide]
              rw [rat_two_zpow_div_two (127 - 23), hpow104, ← Rat.mul_assoc,
                  show (2 : Rat) ^ (127 - 23 - 1 : Int) = (1 : Rat) * (2 : Rat) ^ (103 : Int) by
                    rw [Rat.one_mul]; rfl,
                  ← rat_sub_mul]
              congr 1
              rw [show ((2 ^ 25 - 1 : Nat) : Rat) = ((2 ^ 25 - 1 : Nat) : Int) from rat_natCast_eq_intCast _,
                  show ((2 ^ 24 : Nat) : Rat) = ((2 ^ 24 : Nat) : Int) from rat_natCast_eq_intCast _,
                  show (2 : Rat) = ((2 : Int) : Rat) from rfl,
                  show (1 : Rat) = ((1 : Int) : Rat) from rfl,
                  ← Rat.intCast_mul, ← Rat.intCast_sub]
              exact congrArg (Int.cast : Int → Rat) (by omega)
            rw [← hth]; exact hsub
          · generalize hexp_def : (topExp + 128).toNat = exp at hovf
            have hsig_r : (sig >>> 1) &&& 0x7fffff = 0 := by
              rw [hs24, Nat.shiftRight_eq_div_pow, show (2 ^ 24 : Nat) / 2 ^ 1 = 2 ^ 23 by omega]
              exact (Nat.and_two_pow_sub_one_eq_mod (2 ^ 23) 23).trans (Nat.mod_self (2 ^ 23))
            have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| 0) := by
              change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
              rw [← hsign, ← hmag, ← hbl, ← htop]
              simp only [hm0, hgt127, hlt150, hge126, ↓reduceIte]
              rw [hsh_def, hsig_def]; simp only [hcarry, ↓reduceIte]
              rw [hexp_def]; simp only [hovf, ↓reduceIte, hsig_r]
            rw [hres, hulp]
            have hy : (if exp = 0 then ((0 : Nat) : Rat) * (2 : Rat) ^ (-149 : Int)
                 else ((2 ^ 23 + 0 : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150)) =
                (sig : Rat) * (2 : Rat) ^ (topExp - 23) := by
              simp only [show exp ≠ 0 by omega, ↓reduceIte, Nat.add_zero, hs24]
              have hbe : (exp : Int) - 150 = (1 : Int) + (topExp - 23) := by omega
              rw [hbe, Rat.zpow_add (by decide), ← Rat.mul_assoc,
                  rat_natCast_two_pow 23, rat_natCast_two_pow 24, ← Rat.zpow_add (by decide)]; rfl
            have hpar : (0 % 2 == 0) = (sig % 2 == 0) := by rw [hs24]
            exact f32_pack_finite hsign_lt hsign_eq (by omega) (by omega) hx_mag hy hpar hrne_sig
        · generalize hexp_def : (topExp + 127).toNat = exp
          have hsig_lt : sig < 2 ^ 24 := by
            have : (1 <<< 24 : Nat) = 2 ^ 24 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
            omega
          have hnot_ovf : ¬ (exp ≥ 255) := by omega
          have hfrac_eq : sig &&& 0x7fffff = sig - 2 ^ 23 := by
            have : sig &&& (2 ^ 23 - 1) = sig % 2 ^ 23 := Nat.and_two_pow_sub_one_eq_mod sig 23
            change sig &&& (2 ^ 23 - 1) = _; rw [this]; omega
          have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| (exp <<< 23) ||| (sig - 2 ^ 23)) := by
            change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
            rw [← hsign, ← hmag, ← hbl, ← htop]
            simp only [hm0, hgt127, hlt150, hge126, ↓reduceIte]
            rw [hsh_def, hsig_def]; simp only [hcarry, ↓reduceIte]
            rw [hexp_def]; simp only [hnot_ovf, ↓reduceIte, hfrac_eq]
          rw [hres, hulp]
          have hy : (if exp = 0 then ((sig - 2 ^ 23 : Nat) : Rat) * (2 : Rat) ^ (-149 : Int)
               else ((2 ^ 23 + (sig - 2 ^ 23) : Nat) : Rat) * (2 : Rat) ^ ((exp : Int) - 150)) =
              (sig : Rat) * (2 : Rat) ^ (topExp - 23) := by
            simp only [show exp ≠ 0 by omega, ↓reduceIte]
            rw [show 2 ^ 23 + (sig - 2 ^ 23) = sig by omega,
                show (exp : Int) - 150 = topExp - 23 by omega]
          have hpar : ((sig - 2 ^ 23) % 2 == 0) = (sig % 2 == 0) := by
            have hmod : (sig - 2 ^ 23) % 2 = sig % 2 := by omega
            rw [hmod]
          exact f32_pack_finite hsign_lt hsign_eq (by omega) (by omega) hx_mag hy hpar hrne_sig
      · have hulp : dyadicF32Ulp m e = (2 : Rat) ^ (-149 : Int) := by
          unfold dyadicF32Ulp; dsimp only; rw [← hmag, ← hbl, ← htop]; simp only [hm0, hge126, ↓reduceIte]
        generalize hsh_def : (-149 : Int) - e = shift
        generalize hsig_def : (if shift ≤ 0 then mag <<< (-shift).toNat else roundShiftEven mag shift.toNat) = sig
        have hsig_le : sig ≤ 2 ^ 23 := by
          by_cases hsh : shift ≤ 0
          · have hsig_eq : sig = mag * 2 ^ (-shift).toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte, Nat.shiftLeft_eq]
            have h1 := Nat.mul_lt_mul_of_pos_right hmag_hi (Nat.pow_pos (a := 2) (n := (-shift).toNat) (by decide))
            rw [← Nat.pow_add] at h1
            have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bitLen + (-shift).toNat ≤ 23)
            omega
          · have hsig_eq : sig = roundShiftEven mag shift.toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte]
            have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bitLen ≤ 23 + shift.toNat)
            rw [Nat.pow_add] at h2
            have h1 := roundShiftEven_mono shift.toNat (by omega : mag ≤ 2 ^ 23 * 2 ^ shift.toNat)
            have h3 := roundShiftEven_mul_two_pow (2 ^ 23) shift.toNat (by omega)
            omega
        have hrne_sig : IsRNENearest ((mag : Rat) * (2 : Rat) ^ e)
            ((sig : Rat) * (2 : Rat) ^ (-149 : Int)) ((2 : Rat) ^ (-149 : Int)) (sig % 2 == 0) := by
          by_cases hsh : shift ≤ 0
          · have hsig_eq : sig = mag * 2 ^ (-shift).toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte, Nat.shiftLeft_eq]
            have hval_eq : (sig : Rat) * (2 : Rat) ^ (-149 : Int) = (mag : Rat) * (2 : Rat) ^ e := by
              rw [hsig_eq, rat_natCast_mul, Rat.mul_assoc,
                  rat_natCast_two_pow (-shift).toNat, ← Rat.zpow_add (by decide)]
              congr 2; omega
            rw [hval_eq]; exact isRNENearest_exact _ _ (Rat.zpow_pos (by decide)) _
          · have hsig_eq : sig = roundShiftEven mag shift.toNat := by
              rw [← hsig_def]; simp only [hsh, ↓reduceIte]
            have hr := isRNENearest_of_roundShiftEven mag shift.toNat (-149) (by omega)
            rw [show (-149 : Int) - (shift.toNat : Int) = e by omega, ← hsig_eq] at hr
            exact hr
        by_cases hcarry : sig ≥ (1 <<< 23)
        · have hs23 : sig = 2 ^ 23 := by
            have : (1 <<< 23 : Nat) = 2 ^ 23 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
            omega
          have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| (1 <<< 23) ||| 0) := by
            change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
            rw [← hsign, ← hmag, ← hbl, ← htop]
            simp only [hm0, hgt127, hlt150, hge126, ↓reduceIte]
            rw [hsh_def, hsig_def]; simp only [hcarry, ↓reduceIte, Nat.or_zero]
          rw [hres, hulp]
          have hy : (if (1 : Nat) = 0 then ((0 : Nat) : Rat) * (2 : Rat) ^ (-149 : Int)
               else ((2 ^ 23 + 0 : Nat) : Rat) * (2 : Rat) ^ ((1 : Int) - 150)) =
              (sig : Rat) * (2 : Rat) ^ (-149 : Int) := by
            rw [hs23]; simp only [Nat.one_ne_zero, ↓reduceIte, Nat.add_zero]; rfl
          have hpar : (0 % 2 == 0) = (sig % 2 == 0) := by rw [hs23]
          exact f32_pack_finite hsign_lt hsign_eq (by decide) (by omega) hx_mag hy hpar hrne_sig
        · have hs_lt : sig < 2 ^ 23 := by
            have : (1 <<< 23 : Nat) = 2 ^ 23 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
            omega
          have hfrac_eq : sig &&& 0x7fffff = sig := by
            have : sig &&& (2 ^ 23 - 1) = sig % 2 ^ 23 := Nat.and_two_pow_sub_one_eq_mod sig 23
            change sig &&& (2 ^ 23 - 1) = _; rw [this]; omega
          have hres : res = BitVec.ofNat 32 ((sign <<< 31) ||| (0 <<< 23) ||| sig) := by
            change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; dsimp only
            rw [← hsign, ← hmag, ← hbl, ← htop]
            simp only [hm0, hgt127, hlt150, hge126, ↓reduceIte]
            rw [hsh_def, hsig_def]; simp only [hcarry, ↓reduceIte, hfrac_eq, Nat.zero_shiftLeft, Nat.or_zero]
          rw [hres, hulp]
          have hy : (if (0 : Nat) = 0 then (sig : Rat) * (2 : Rat) ^ (-149 : Int)
               else ((2 ^ 23 + sig : Nat) : Rat) * (2 : Rat) ^ ((0 : Int) - 150)) =
              (sig : Rat) * (2 : Rat) ^ (-149 : Int) := by simp only [↓reduceIte]
          exact f32_pack_finite hsign_lt hsign_eq (by decide) hs_lt hx_mag hy rfl hrne_sig

/-- Proves universal mathematical IEEE-754 binary32 RNE correctness directly on `dyadicToF32BitsRNE`. -/
theorem dyadicToF32BitsRNE_value_spec (m e : Int) :
    let x := (Dyadic.mk m e).value
    let res := dyadicToF32BitsRNE m e
    f32IsNaN res = false ∧
    (m = 0 → res = 0x00000000#32) ∧
    (m ≠ 0 →
      ((res >>> 31) != 0#32) = decide (m < 0) ∧
      (if f32IsFinite res = true then
        IsRNENearest x (float32BitsToDyadic res).value (dyadicF32Ulp m e) (res.toNat % 2 == 0)
      else
        if m < 0 then res = 0xff800000#32 ∧ x ≤ -f32OverflowThreshold
        else res = 0x7f800000#32 ∧ f32OverflowThreshold ≤ x)) := by
  intro x res
  by_cases hm0 : m = 0
  · have hres : res = 0x00000000#32 := by
      change dyadicToF32BitsRNE m e = _; unfold dyadicToF32BitsRNE; simp only [hm0, ↓reduceIte]
    rw [hres]; exact ⟨by decide, fun _ => rfl, fun h => absurd hm0 h⟩
  · have hmain := dyadic_to_f32_core m e (if m < 0 then 1 else 0) m.natAbs (bitLength m.natAbs)
      (e + (bitLength m.natAbs : Int) - 1) hm0 rfl rfl rfl rfl
    exact ⟨hmain.1, fun h => absurd h hm0, fun _ => ⟨hmain.2.1, hmain.2.2⟩⟩

private theorem f32IsZero_iff_dyadic_m_zero (u : BitVec 32) :
    f32IsZero u = true ↔ (float32BitsToDyadic u).m = 0 := by
  have habs : (u &&& 0x7fffffff#32).toNat = u.toNat % 2 ^ 31 := by
    have h1 := bv32_and_pow2 u 31 (by decide)
    change (u &&& BitVec.ofNat 32 (2 ^ 31 - 1)).toNat = _; rw [h1]
  have hexp : ((u >>> 23) &&& 0xff#32).toNat = (u.toNat / 2 ^ 23) % 256 := by
    have h1 := bv32_and_pow2 (u >>> 23) 8 (by decide)
    change ((u >>> 23) &&& BitVec.ofNat 32 (2 ^ 8 - 1)).toNat = _
    rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hfrac : (u &&& 0x7fffff#32).toNat = u.toNat % 2 ^ 23 := by
    have h1 := bv32_and_pow2 u 23 (by decide)
    change (u &&& BitVec.ofNat 32 (2 ^ 23 - 1)).toNat = _; rw [h1]
  have hlt := u.isLt
  unfold f32IsZero float32BitsToDyadic; dsimp only; rw [beq_iff_eq]
  constructor
  · intro hz
    have h0 : (u &&& 0x7fffffff#32).toNat = 0 := by rw [hz]; rfl
    have he0 : ((u >>> 23) &&& 0xff#32).toNat = 0 := by omega
    have hf0 : (u &&& 0x7fffff#32).toNat = 0 := by omega
    simp only [he0, hf0, ↓reduceIte]
  · intro hm
    apply BitVec.eq_of_toNat_eq
    change (u &&& 0x7fffffff#32).toNat = 0
    by_cases he0 : ((u >>> 23) &&& 0xff#32).toNat = 0
    · simp only [he0, ↓reduceIte] at hm
      by_cases hf0 : (u &&& 0x7fffff#32).toNat = 0
      · omega
      · simp only [hf0, ↓reduceIte] at hm
        have hnz : (if (u >>> 31) != 0#32 then (-1 : Int) else 1) * ((u &&& 0x7fffff#32).toNat : Int) ≠ 0 := by
          split <;> omega
        exact absurd hm hnz
    · simp only [he0, ↓reduceIte] at hm
      have hnz : (if (u >>> 31) != 0#32 then (-1 : Int) else 1) * (((1 <<< 23) + (u &&& 0x7fffff#32).toNat : Nat) : Int) ≠ 0 := by
        have : 1 <<< 23 = 2 ^ 23 := by rw [Nat.shiftLeft_eq, Nat.one_mul]
        split <;> omega
      exact absurd hm hnz

/-- Universal single-rounding IEEE-754 FMA correctness theorem proved DIRECTLY on `fmafFiniteBits`. -/
theorem fmafFiniteBits_value_spec (a b c : BitVec 32)
    (ha : f32IsFinite a = true) (hb : f32IsFinite b = true) (hc : f32IsFinite c = true) :
    let exact := (float32BitsToDyadic a).value * (float32BitsToDyadic b).value + (float32BitsToDyadic c).value
    let res := fmafFiniteBits a b c
    f32IsNaN res = false ∧
    (if f32IsFinite res = true then
      IsRNENearest exact (float32BitsToDyadic res).value (fmafUlp a b c) (res.toNat % 2 == 0)
    else
      if exact < 0 then res = 0xff800000#32 ∧ exact ≤ -f32OverflowThreshold
      else res = 0x7f800000#32 ∧ f32OverflowThreshold ≤ exact) := by
  intro exact res
  have _ : f32IsFinite a = true ∧ f32IsFinite b = true := ⟨ha, hb⟩
  have hsum_val : (fmafDyadicSum a b c).value = exact := fmafDyadicSum_sound a b c
  by_cases hab0 : (f32IsZero a || f32IsZero b) = true
  · have hprod0 : (float32BitsToDyadic a).value * (float32BitsToDyadic b).value = 0 := by
      rw [Bool.or_eq_true] at hab0
      rcases hab0 with ha0 | hb0
      · have hm := (f32IsZero_iff_dyadic_m_zero a).mp ha0; simp [Dyadic.value, hm]
      · have hm := (f32IsZero_iff_dyadic_m_zero b).mp hb0; simp [Dyadic.value, hm]
    have hexact_c : exact = (float32BitsToDyadic c).value := by
      dsimp only [exact]; rw [hprod0, Rat.zero_add]
    by_cases hc0 : f32IsZero c = true
    · have hcm := (f32IsZero_iff_dyadic_m_zero c).mp hc0
      have hexact0 : exact = 0 := by rw [hexact_c]; simp [Dyadic.value, hcm]
      have hres_z : res = 0x80000000#32 ∨ res = 0x00000000#32 := by
        change fmafFiniteBits a b c = _ ∨ fmafFiniteBits a b c = _
        unfold fmafFiniteBits; simp only [hab0, hc0, ↓reduceIte]; split <;> simp
      rcases hres_z with hr | hr
      · rw [hr, hexact0]; refine ⟨by decide, ?_⟩
        have hf : f32IsFinite 0x80000000#32 = true := by decide
        have hm : (float32BitsToDyadic 0x80000000#32).m = 0 := by decide
        have hv : (float32BitsToDyadic 0x80000000#32).value = 0 := by simp [Dyadic.value, hm]
        rw [hf, hv]; simp only [↓reduceIte]; exact isRNENearest_exact 0 _ (dyadicF32Ulp_pos _ _) _
      · rw [hr, hexact0]; refine ⟨by decide, ?_⟩
        have hf : f32IsFinite 0x00000000#32 = true := by decide
        have hm : (float32BitsToDyadic 0x00000000#32).m = 0 := by decide
        have hv : (float32BitsToDyadic 0x00000000#32).value = 0 := by simp [Dyadic.value, hm]
        rw [hf, hv]; simp only [↓reduceIte]; exact isRNENearest_exact 0 _ (dyadicF32Ulp_pos _ _) _
    · have hres_c : res = c := by
        change fmafFiniteBits a b c = c; unfold fmafFiniteBits
        simp only [hab0, hc0, Bool.false_eq_true, ↓reduceIte]
      have hnan_c : f32IsNaN c = false := by
        unfold f32IsNaN; unfold f32IsFinite at hc; rw [bne_iff_ne] at hc; rw [beq_false_of_ne hc, Bool.false_and]
      rw [hres_c, hnan_c, hc, hexact_c]; simp only [↓reduceIte]
      exact ⟨trivial, isRNENearest_exact _ _ (dyadicF32Ulp_pos _ _) _⟩
  · by_cases hc0 : f32IsZero c = true
    · let d := dyadicMul (float32BitsToDyadic a) (float32BitsToDyadic b)
      have hcm := (f32IsZero_iff_dyadic_m_zero c).mp hc0
      have hdm : d.m ≠ 0 := by
        have ha_nz : (float32BitsToDyadic a).m ≠ 0 := fun hm =>
          hab0 (by rw [(f32IsZero_iff_dyadic_m_zero a).mpr hm]; rfl)
        have hb_nz : (float32BitsToDyadic b).m ≠ 0 := fun hm =>
          hab0 (by rw [(f32IsZero_iff_dyadic_m_zero b).mpr hm]; simp)
        unfold d dyadicMul
        have hno : ¬ ((float32BitsToDyadic a).m = 0 ∨ (float32BitsToDyadic b).m = 0) := by
          intro h; rcases h with h | h <;> contradiction
        simp only [hno, ↓reduceIte]; exact Int.mul_ne_zero ha_nz hb_nz
      have hsum_eq : fmafDyadicSum a b c = d := by
        unfold fmafDyadicSum dyadicAdd
        change (if d.m = 0 then float32BitsToDyadic c else if (float32BitsToDyadic c).m = 0 then d else _) = d
        simp only [hdm, hcm, ↓reduceIte]
      have hres_d : res = dyadicToF32BitsRNE d.m d.e := by
        change fmafFiniteBits a b c = _; unfold fmafFiniteBits
        simp only [hab0, hc0, Bool.false_eq_true, ↓reduceIte]; rfl
      have hexact_d : exact = (Dyadic.mk d.m d.e).value := by rw [← hsum_val, hsum_eq]
      have hulp_d : fmafUlp a b c = dyadicF32Ulp d.m d.e := by unfold fmafUlp; rw [hsum_eq]
      have hsp := dyadicToF32BitsRNE_value_spec d.m d.e
      have hneg_iff : d.m < 0 ↔ exact < 0 := by
        rw [hexact_d]
        have hp : 0 < (2 : Rat) ^ d.e := Rat.zpow_pos (by decide)
        simp [Dyadic.value, Rat.mul_neg_iff_of_pos_right hp, Rat.intCast_neg_iff]
      rw [hres_d, hulp_d]; refine ⟨hsp.1, ?_⟩
      have hbody := (hsp.2.2 hdm).2; rw [← hexact_d] at hbody
      by_cases hf : f32IsFinite (dyadicToF32BitsRNE d.m d.e) = true
      · simp only [hf, ↓reduceIte] at hbody ⊢; exact hbody
      · simp only [hf] at hbody ⊢
        by_cases hn : d.m < 0
        · have he : exact < 0 := hneg_iff.mp hn; simp only [hn, he, ↓reduceIte] at hbody ⊢; exact hbody
        · have he : ¬ (exact < 0) := fun h => hn (hneg_iff.mpr h); simp only [hn, he, ↓reduceIte] at hbody ⊢; exact hbody
    · let s := fmafDyadicSum a b c
      by_cases hsm0 : s.m = 0
      · have hexact0 : exact = 0 := by rw [← hsum_val]; simp [s, Dyadic.value, hsm0]
        have hres0 : res = 0x00000000#32 := by
          change fmafFiniteBits a b c = _; unfold fmafFiniteBits
          simp only [hab0, hc0, Bool.false_eq_true, ↓reduceIte]
          change (if s.m = 0 then 0x00000000#32 else dyadicToF32BitsRNE s.m s.e) = 0x00000000#32
          simp only [hsm0, ↓reduceIte]
        rw [hres0, hexact0]; refine ⟨by decide, ?_⟩
        have hf : f32IsFinite 0x00000000#32 = true := by decide
        have hm : (float32BitsToDyadic 0x00000000#32).m = 0 := by decide
        have hv : (float32BitsToDyadic 0x00000000#32).value = 0 := by simp [Dyadic.value, hm]
        rw [hf, hv]; simp only [↓reduceIte]; exact isRNENearest_exact 0 _ (dyadicF32Ulp_pos _ _) _
      · have hres_s : res = dyadicToF32BitsRNE s.m s.e := by
          change fmafFiniteBits a b c = _; unfold fmafFiniteBits
          simp only [hab0, hc0, Bool.false_eq_true, ↓reduceIte]
          change (if s.m = 0 then 0x00000000#32 else dyadicToF32BitsRNE s.m s.e) = dyadicToF32BitsRNE s.m s.e
          simp only [hsm0, ↓reduceIte]
        have hsp := dyadicToF32BitsRNE_value_spec s.m s.e
        have hneg_iff : s.m < 0 ↔ exact < 0 := by
          rw [← hsum_val]
          have hp : 0 < (2 : Rat) ^ s.e := Rat.zpow_pos (by decide)
          simp [s, Dyadic.value, Rat.mul_neg_iff_of_pos_right hp, Rat.intCast_neg_iff]
        rw [hres_s]; refine ⟨hsp.1, ?_⟩
        have hbody := (hsp.2.2 hsm0).2
        have hval_s : (Dyadic.mk s.m s.e).value = exact := hsum_val
        rw [hval_s] at hbody
        change if f32IsFinite (dyadicToF32BitsRNE s.m s.e) = true then
          IsRNENearest exact (float32BitsToDyadic (dyadicToF32BitsRNE s.m s.e)).value (dyadicF32Ulp s.m s.e) _
          else _
        by_cases hf : f32IsFinite (dyadicToF32BitsRNE s.m s.e) = true
        · simp only [hf, ↓reduceIte] at hbody ⊢; exact hbody
        · simp only [hf] at hbody ⊢
          by_cases hn : s.m < 0
          · have he : exact < 0 := hneg_iff.mp hn; simp only [hn, he, ↓reduceIte] at hbody ⊢; exact hbody
          · have he : ¬ (exact < 0) := fun h => hn (hneg_iff.mpr h); simp only [hn, he, ↓reduceIte] at hbody ⊢; exact hbody

end PFOracle
