import Codes.Core
import Codes.Statements.EC_rec_17_6

namespace Codes.Claims.EC_rec_17_6_not_s341

open Codes

/-!
  Formal Lean 4 proof of the classic Best–Brouwer–MacWilliams–Odlyzko–Sloane (1978)
  upper bound `A(17, 6) ≤ 340`, certifying `¬ Codes.Statements.EC_rec_17_6.Record 341`.

  Proof outline:
  1. Reduction to an even-weight `(17, M, 6)` code `C'`: puncture coordinate 16 to get a
     `(16, M, 5)` code, then append an overall parity bit to obtain an even-weight `(17, M, 6)`
     code `C'` of the same cardinality `M`, in which all pairwise Hamming distances are even
     (`∈ {0, 6, 8, 10, 12, 14, 16}`).
  2. For each codeword `u ∈ C'`, prove the elementary packing bound
       `deg_14(u) + 5 * deg_16(u) ≤ 5`
     using the complements `v ⊕ ~u`: `wt = 1` for `dist = 16` and `wt = 3` for `dist = 14`.
  3. Apply the degree-4 Krawtchouk / Fourier dual polynomial
       `P15(i) = 15 K_0(i) + 5 K_1(i) + 5 K_2(i) + K_3(i) + K_4(i)`.
     On even distances `i ∈ {0, 6, 8, 10, 12, 14, 16}`,
       `P15(0) = 3840`, `P15(6) = P15(8) = P15(10) = P15(12) = 0`,
       `P15(14) = 256`, `P15(16) = 1280 = 5 * 256`.
     Hence `∑_{u,v ∈ C'} P15(dist u v) ≤ 5120 * M`.
  4. By Fourier expansion over all `k`-element subsets of `{0..16}` (`k ≤ 4`),
       `∑_{u,v ∈ C'} P15(dist u v) = 15 M^2 + 5 ∑_{|S|=1} s_S^2 + 5 ∑_{|S|=2} s_S^2 + ∑_{|S|=3} s_S^2 + ∑_{|S|=4} s_S^2`.
     - If `M ≥ 342`, non-negativity gives `15 M^2 ≤ 5120 M`, impossible since `15 * 342 = 5130 > 5120`.
     - If `M = 341` (odd), every `s_S = ∑_{u ∈ C'} ±1` is odd, so `s_S^2 ≥ 1`, adding at least
       `5·17 + 5·136 + 680 + 2380 = 3825` to the LHS:
       `15 · 341^2 + 3825 = 1,748,040 ≤ 5120 · 341 = 1,745,920`, contradiction.
-/

/-! ## 1. Bit-level & Hamming Weight Helpers -/

private theorem popCountAux_succ_shift (k x : Nat) :
    popCountAux (k + 1) x = x % 2 + popCountAux k (x / 2) := rfl

private def bitAt {n : Nat} (u : BitVec n) (i : Nat) : Bool := u.getLsbD i

private def countBits (k : Nat) (f : Nat → Bool) : Nat :=
  match k with
  | 0 => 0
  | k' + 1 => countBits k' f + (if f k' then 1 else 0)

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
    rw [hshift k x, popCountAux, popCountAux_eq_countBits_go k (x / 2)]
    rw [Nat.testBit_zero]
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
  have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
      (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
    intro k f g hfg
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [countBits, hfg k' (Nat.lt_succ_self k'),
        ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
  apply hcongr
  intro i _
  rfl

private theorem countBits_le : ∀ (k : Nat) (f : Nat → Bool), countBits k f ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, f => by
    simp only [countBits]
    have ih := countBits_le k f
    by_cases h : f k = true <;> simp [h] <;> omega

private theorem countBits_xor (k : Nat) (f g : Nat → Bool) :
    countBits k (fun i => xor (f i) (g i)) + 2 * countBits k (fun i => f i && g i) =
    countBits k f + countBits k g := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [countBits]
    by_cases hf : f k' = true <;> by_cases hg : g k' = true <;> simp [hf, hg] <;> omega

private theorem countBits_not (k : Nat) (f : Nat → Bool) :
    countBits k (fun i => !(f i)) + countBits k f = k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [countBits]
    by_cases hf : f k' = true <;> simp [hf] <;> omega

private theorem countBits_le_add_xor (k : Nat) (f g : Nat → Bool) :
    countBits k (fun i => xor (f i) (g i)) ≤ countBits k f + countBits k g := by
  have h := countBits_xor k f g
  omega

private theorem hammingDist_eq_countBits {n : Nat} (u v : BitVec n) :
    hammingDist u v = countBits n (fun i => xor (u.getLsbD i) (v.getLsbD i)) := by
  unfold hammingDist
  rw [hammingWeight_eq_countBits]
  have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
      (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
    intro k f g hfg
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [countBits, hfg k' (Nat.lt_succ_self k'),
        ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
  apply hcongr
  intro i hi
  simp [BitVec.getLsbD_xor, hi]

private theorem hammingDist_le (n : Nat) (u v : BitVec n) : hammingDist u v ≤ n := by
  rw [hammingDist_eq_countBits]
  exact countBits_le n _

private theorem hammingDist_xor_right {n : Nat} (u v w : BitVec n) :
    hammingDist (u ^^^ w) (v ^^^ w) = hammingDist u v := by
  unfold hammingDist
  have h : (u ^^^ w) ^^^ (v ^^^ w) = u ^^^ v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor]
    cases u.getLsbD i <;> cases v.getLsbD i <;> cases w.getLsbD i <;> rfl
  rw [h]

private theorem hammingDist_triangle {n : Nat} (u v w : BitVec n) :
    hammingDist u w ≤ hammingDist u v + hammingDist v w := by
  rw [hammingDist_eq_countBits, hammingDist_eq_countBits, hammingDist_eq_countBits]
  have heq : ∀ i, xor (u.getLsbD i) (w.getLsbD i) =
      xor (xor (u.getLsbD i) (v.getLsbD i)) (xor (v.getLsbD i) (w.getLsbD i)) := by
    intro i
    cases u.getLsbD i <;> cases v.getLsbD i <;> cases w.getLsbD i <;> rfl
  have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
      (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
    intro k f g hfg
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [countBits, hfg k' (Nat.lt_succ_self k'),
        ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
  rw [hcongr n _ _ (fun i _ => heq i)]
  exact countBits_le_add_xor n _ _

private theorem hammingWeight_not {n : Nat} (u : BitVec n) :
    hammingWeight (~~~u) + hammingWeight u = n := by
  rw [hammingWeight_eq_countBits, hammingWeight_eq_countBits]
  have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
      (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
    intro k f g hfg
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [countBits, hfg k' (Nat.lt_succ_self k'),
        ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
  rw [hcongr n (fun i => (~~~u).getLsbD i) (fun i => !(u.getLsbD i))
        (fun i hi => by simp [BitVec.getLsbD_not, hi])]
  exact countBits_not n _

private theorem hammingDist_not_left {n : Nat} (u v : BitVec n) :
    hammingDist (~~~u) v + hammingDist u v = n := by
  unfold hammingDist
  have h : (~~~u) ^^^ v = ~~~(u ^^^ v) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases u.getLsbD i <;> cases v.getLsbD i <;> rfl
  rw [h]
  exact hammingWeight_not (u ^^^ v)

/-! ## 2. Reduction of Any `(17, M, 6)` Code to an Even-Weight `(17, M, 6)` Code -/

/-- Replace bit 16 of `u : BitVec 17` with the XOR parity of bits `0..15`. -/
private def makeEven (u : BitVec 17) : BitVec 17 :=
  let low := u.toNat % 65536
  let p := popCountAux 16 low % 2
  BitVec.ofNat 17 (low + p * 65536)

private theorem makeEven_getLsbD_lt16 (u : BitVec 17) (i : Nat) (hi : i < 16) :
    (makeEven u).getLsbD i = u.getLsbD i := by
  unfold makeEven
  have hi17 : i < 17 := by omega
  simp only [BitVec.getLsbD_ofNat, hi17, decide_true, Bool.true_and]
  have htb : ∀ a b, (a + b * 65536).testBit i = a.testBit i := by
    intro a b
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h65536 : 65536 = 2 ^ (16 - i) * 2 ^ i := by
      rw [← Nat.pow_add]
      have : 16 - i + i = 16 := by omega
      rw [this]
    have hdiv : (a + b * 65536) / 2 ^ i = a / 2 ^ i + b * 2 ^ (16 - i) := by
      rw [h65536, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    rw [hdiv]
    have heven : 2 ∣ 2 ^ (16 - i) := by
      have : 2 ^ (16 - i) = 2 * 2 ^ (16 - i - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      exact ⟨2 ^ (16 - i - 1), this⟩
    rcases heven with ⟨q, hq⟩
    rw [hq, Nat.one_and_eq_mod_two, Nat.one_and_eq_mod_two]
    have hmod : (a / 2 ^ i + b * (2 * q)) % 2 = (a / 2 ^ i) % 2 := by
      have hmul : b * (2 * q) = (b * q) * 2 := by
        rw [Nat.mul_comm 2 q, ← Nat.mul_assoc]
      rw [hmul, Nat.add_mul_mod_self_right]
    rw [hmod]
  rw [htb]
  have hlow : (u.toNat % 65536).testBit i = u.toNat.testBit i := by
    have : (65536 : Nat) = 2 ^ 16 := rfl
    rw [this, Nat.testBit_mod_two_pow]
    simp [hi]
  rw [hlow]
  rfl

private theorem makeEven_getLsbD_16 (u : BitVec 17) :
    (makeEven u).getLsbD 16 = decide (countBits 16 (fun i => u.getLsbD i) % 2 = 1) := by
  unfold makeEven
  have h1 : u.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_ofNat, show (16 : Nat) < 17 by decide, decide_true, Bool.true_and]
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 16 = 65536 by rfl,
      Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt h1, Nat.zero_add,
      Nat.one_and_eq_mod_two, Nat.mod_mod]
  have hpop : popCountAux 16 (u.toNat % 65536) = countBits 16 (fun i => u.getLsbD i) := by
    rw [show (65536 : Nat) = 2 ^ 16 by rfl, popCountAux_mod, popCountAux_eq_countBits_go]
    rfl
  rw [hpop]
  cases h : decide (countBits 16 (fun i => u.getLsbD i) % 2 = 1)
  · have hm : countBits 16 (fun i => u.getLsbD i) % 2 = 0 := by
      have := Nat.mod_lt (countBits 16 (fun i => u.getLsbD i)) (by decide : 0 < 2)
      have hne : countBits 16 (fun i => u.getLsbD i) % 2 ≠ 1 := by simpa using h
      omega
    simp [hm]
  · have hm : countBits 16 (fun i => u.getLsbD i) % 2 = 1 := by simpa using h
    simp [hm]

private theorem makeEven_weight_even (u : BitVec 17) : hammingWeight (makeEven u) % 2 = 0 := by
  rw [hammingWeight_eq_countBits]
  have hstep : countBits 17 (fun i => (makeEven u).getLsbD i) =
      countBits 16 (fun i => (makeEven u).getLsbD i) + (if (makeEven u).getLsbD 16 then 1 else 0) := rfl
  rw [hstep]
  have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
      (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
    intro k f g hfg
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [countBits, hfg k' (Nat.lt_succ_self k'),
        ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
  rw [hcongr 16 (fun i => (makeEven u).getLsbD i) (fun i => u.getLsbD i) (makeEven_getLsbD_lt16 u)]
  rw [makeEven_getLsbD_16]
  cases h : decide (countBits 16 (fun i => u.getLsbD i) % 2 = 1)
  · have hne : countBits 16 (fun i => u.getLsbD i) % 2 ≠ 1 := by simpa using h
    simp; omega
  · have heq : countBits 16 (fun i => u.getLsbD i) % 2 = 1 := by simpa using h
    simp; omega

private theorem dist_even_of_weights_even {n : Nat} {u v : BitVec n}
    (hu : hammingWeight u % 2 = 0) (hv : hammingWeight v % 2 = 0) :
    hammingDist u v % 2 = 0 := by
  rw [hammingDist_eq_countBits]
  rw [hammingWeight_eq_countBits] at hu hv
  have hx := countBits_xor n (fun i => u.getLsbD i) (fun i => v.getLsbD i)
  omega

private theorem makeEven_dist_ge_6 {u v : BitVec 17} (huv : 6 ≤ hammingDist u v) :
    6 ≤ hammingDist (makeEven u) (makeEven v) := by
  have h17 : hammingDist u v = countBits 16 (fun i => xor (u.getLsbD i) (v.getLsbD i)) +
      (if xor (u.getLsbD 16) (v.getLsbD 16) then 1 else 0) := by
    rw [hammingDist_eq_countBits]; rfl
  have hle1 : (if xor (u.getLsbD 16) (v.getLsbD 16) then 1 else 0) ≤ 1 := by
    split <;> decide
  have h16 : 5 ≤ countBits 16 (fun i => xor (u.getLsbD i) (v.getLsbD i)) := by omega
  have hme : hammingDist (makeEven u) (makeEven v) =
      countBits 16 (fun i => xor (u.getLsbD i) (v.getLsbD i)) +
      (if xor ((makeEven u).getLsbD 16) ((makeEven v).getLsbD 16) then 1 else 0) := by
    rw [hammingDist_eq_countBits]
    have hstep : countBits 17 (fun i => xor ((makeEven u).getLsbD i) ((makeEven v).getLsbD i)) =
        countBits 16 (fun i => xor ((makeEven u).getLsbD i) ((makeEven v).getLsbD i)) +
        (if xor ((makeEven u).getLsbD 16) ((makeEven v).getLsbD 16) then 1 else 0) := rfl
    rw [hstep]
    have hcongr : ∀ (k : Nat) (f g : Nat → Bool),
        (∀ i, i < k → f i = g i) → countBits k f = countBits k g := by
      intro k f g hfg
      induction k with
      | zero => rfl
      | succ k' ih =>
        simp only [countBits, hfg k' (Nat.lt_succ_self k'),
          ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))]
    rw [hcongr 16
      (fun i => xor ((makeEven u).getLsbD i) ((makeEven v).getLsbD i))
      (fun i => xor (u.getLsbD i) (v.getLsbD i))
      (fun i hi => by rw [makeEven_getLsbD_lt16 u i hi, makeEven_getLsbD_lt16 v i hi])]
  have heven : hammingDist (makeEven u) (makeEven v) % 2 = 0 :=
    dist_even_of_weights_even (makeEven_weight_even u) (makeEven_weight_even v)
  have hge5 : 5 ≤ hammingDist (makeEven u) (makeEven v) := by omega
  omega

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

private theorem reduce_to_even_code {C : List (BitVec 17)} (hc : IsBinaryCode 17 6 C) :
    ∃ C' : List (BitVec 17), C'.length = C.length ∧ IsBinaryCode 17 6 C' ∧
      ∀ u ∈ C', ∀ v ∈ C', hammingDist u v % 2 = 0 := by
  refine ⟨C.map makeEven, by simp, ⟨?_, ?_⟩, ?_⟩
  · apply nodup_map_of_inj hc.1
    intro a ha b hb heq
    by_cases hab : a = b
    · exact hab
    · have h6 := makeEven_dist_ge_6 (hc.2 a ha b hb hab)
      rw [heq, hammingDist_self] at h6
      omega
  · intro u' hu' v' hv' hne
    rcases List.mem_map.1 hu' with ⟨u, hu, rfl⟩
    rcases List.mem_map.1 hv' with ⟨v, hv, rfl⟩
    have huv : u ≠ v := fun h => hne (congrArg makeEven h)
    exact makeEven_dist_ge_6 (hc.2 u hu v hv huv)
  · intro u' hu' v' hv'
    rcases List.mem_map.1 hu' with ⟨u, _, rfl⟩
    rcases List.mem_map.1 hv' with ⟨v, _, rfl⟩
    exact dist_even_of_weights_even (makeEven_weight_even u) (makeEven_weight_even v)

/-! ## 3. Local Packing Bound `deg_14(u) + 5 * deg_16(u) ≤ 5` -/

private theorem nodup_filter {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have ⟨hx, hxs⟩ := List.nodup_cons.1 h
    simp only [List.filter_cons]
    cases p x
    · exact nodup_filter hxs
    · exact List.nodup_cons.2 ⟨fun hm => hx (List.mem_filter.1 hm).1, nodup_filter hxs⟩

private theorem sum_weight_le_of_disjoint :
    ∀ (k : Nat) (S : List (BitVec 17)),
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w → ∀ i, i < k → !(v.getLsbD i && w.getLsbD i) = true) →
      S.Nodup →
      (S.map (fun v => countBits k (fun i => v.getLsbD i))).sum ≤ k := by
  intro k
  induction k with
  | zero =>
    intro S _ _
    have h0 : ∀ l : List (BitVec 17), (l.map (fun _ => 0)).sum = 0 := by
      intro l; induction l with | nil => rfl | cons _ _ ih => simp [ih]
    simpa [countBits] using Nat.le_of_eq (h0 S)
  | succ k' ih =>
    intro S hdisj hnd
    have hsplit : ∀ l : List (BitVec 17),
        (l.map (fun v => countBits k' (fun i => v.getLsbD i) + (if v.getLsbD k' then 1 else 0))).sum =
        (l.map (fun v => countBits k' (fun i => v.getLsbD i))).sum +
        (l.map (fun v => if v.getLsbD k' then 1 else 0)).sum := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih2 => simp only [List.map_cons, List.sum_cons, ih2]; omega
    simp only [countBits]
    rw [hsplit]
    have hprev := ih S
      (fun v hv w hw hne i hi => hdisj v hv w hw hne i (Nat.lt_succ_of_lt hi)) hnd
    have hlast : (S.map (fun v => if v.getLsbD k' then 1 else 0)).sum ≤ 1 := by
      have haux : ∀ (l : List (BitVec 17)), l.Nodup →
          (∀ v ∈ l, ∀ w ∈ l, v ≠ w → !(v.getLsbD k' && w.getLsbD k') = true) →
          (l.map (fun v => if v.getLsbD k' then 1 else 0)).sum ≤ 1 := by
        intro l
        induction l with
        | nil => intro _ _; simp
        | cons x xs ih3 =>
          intro hnd' hd'
          have ⟨hx, hxs⟩ := List.nodup_cons.1 hnd'
          simp only [List.map_cons, List.sum_cons]
          cases hxk : x.getLsbD k'
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
            exact ih3 hxs (fun v hv w hw => hd' v (List.mem_cons_of_mem x hv) w (List.mem_cons_of_mem x hw))
          · simp only [↓reduceIte]
            have hrest0 : ∀ l' : List (BitVec 17),
                (∀ y ∈ l', y.getLsbD k' = false) →
                (l'.map (fun v => if v.getLsbD k' then 1 else 0)).sum = 0 := by
              intro l' hf
              induction l' with
              | nil => rfl
              | cons z zs ih4 =>
                simp only [List.map_cons, List.sum_cons, hf z List.mem_cons_self,
                  Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
                exact ih4 (fun y hy => hf y (List.mem_cons_of_mem z hy))
            have hallf : ∀ y ∈ xs, y.getLsbD k' = false := by
              intro y hy
              have hne : x ≠ y := fun h => hx (h ▸ hy)
              have h0 := hd' x List.mem_cons_self y (List.mem_cons_of_mem x hy) hne
              rw [hxk] at h0
              cases hyk : y.getLsbD k'
              · rfl
              · rw [hyk] at h0; cases h0
            rw [hrest0 xs hallf]
            omega
      exact haux S hnd (fun v hv w hw hne => hdisj v hv w hw hne k' (Nat.lt_succ_self k'))
    omega

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

private theorem local_packing_bound {C : List (BitVec 17)} (hc : IsBinaryCode 17 6 C)
    (u : BitVec 17) :
    (C.filter (fun v => hammingDist u v == 14)).length +
      5 * (C.filter (fun v => hammingDist u v == 16)).length ≤ 5 := by
  let S14 := C.filter (fun v => hammingDist u v == 14)
  let S16 := C.filter (fun v => hammingDist u v == 16)
  have h16_le : S16.length ≤ 1 := by
    cases hS16 : S16 with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
        exfalso
        have hnd : (a :: b :: rest').Nodup := by rw [← hS16]; exact nodup_filter hc.1
        have hab : a ≠ b := fun h => (List.nodup_cons.1 hnd).1 (h ▸ List.mem_cons_self)
        have ha : a ∈ S16 := by rw [hS16]; exact List.mem_cons_self
        have hb : b ∈ S16 := by rw [hS16]; exact List.mem_cons_of_mem a List.mem_cons_self
        rcases List.mem_filter.1 ha with ⟨haC, ha16⟩
        rcases List.mem_filter.1 hb with ⟨hbC, hb16⟩
        have ha16' : hammingDist u a = 16 := eq_of_beq ha16
        have hb16' : hammingDist u b = 16 := eq_of_beq hb16
        have hda : hammingDist (~~~u) a = 1 := by have := hammingDist_not_left u a; omega
        have hdb : hammingDist (~~~u) b = 1 := by have := hammingDist_not_left u b; omega
        have htri : hammingDist a b ≤ hammingDist a (~~~u) + hammingDist (~~~u) b :=
          hammingDist_triangle a (~~~u) b
        rw [hammingDist_comm a (~~~u), hda, hdb] at htri
        have h6 := hc.2 a haC b hbC hab
        omega
  by_cases h16pos : S16.length = 1
  · have h14zero : S14.length = 0 := by
      cases hS14 : S14 with
      | nil => rfl
      | cons w _ =>
        exfalso
        cases hS16 : S16 with
        | nil => rw [hS16] at h16pos; cases h16pos
        | cons v _ =>
          have hv : v ∈ S16 := by rw [hS16]; exact List.mem_cons_self
          have hw : w ∈ S14 := by rw [hS14]; exact List.mem_cons_self
          rcases List.mem_filter.1 hv with ⟨hvC, hv16⟩
          rcases List.mem_filter.1 hw with ⟨hwC, hw14⟩
          have hv16' : hammingDist u v = 16 := eq_of_beq hv16
          have hw14' : hammingDist u w = 14 := eq_of_beq hw14
          have hne : v ≠ w := by intro h; subst h; omega
          have hdv : hammingDist (~~~u) v = 1 := by have := hammingDist_not_left u v; omega
          have hdw : hammingDist (~~~u) w = 3 := by have := hammingDist_not_left u w; omega
          have htri : hammingDist v w ≤ hammingDist v (~~~u) + hammingDist (~~~u) w :=
            hammingDist_triangle v (~~~u) w
          rw [hammingDist_comm v (~~~u), hdv, hdw] at htri
          have h6 := hc.2 v hvC w hwC hne
          omega
    change S14.length + 5 * S16.length ≤ 5
    omega
  · have h16zero : S16.length = 0 := by omega
    -- Map S14 to shifted vectors `w ⊕ (~~~u)` of weight 3 that are pairwise disjoint
    let T := S14.map (fun w => w ^^^ ~~~u)
    have hTnd : T.Nodup := by
      apply nodup_map_of_inj (nodup_filter hc.1)
      intro a _ b _ heq
      have h := congrArg (fun x => x ^^^ ~~~u) heq
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at h
      exact h
    have hTwt : ∀ x ∈ T, countBits 17 (fun i => x.getLsbD i) = 3 := by
      intro x hx
      rcases List.mem_map.1 hx with ⟨w, hw, rfl⟩
      have hw14 : hammingDist u w = 14 := eq_of_beq (List.mem_filter.1 hw).2
      have hdw : hammingDist (~~~u) w = 3 := by have := hammingDist_not_left u w; omega
      rw [hammingDist_comm] at hdw
      unfold hammingDist at hdw
      rw [hammingWeight_eq_countBits] at hdw
      exact hdw
    have hTdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ i, i < 17 → !(x.getLsbD i && y.getLsbD i) = true := by
      intro x hx y hy hne
      rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
      rcases List.mem_map.1 hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun h => hne (congrArg (fun z => z ^^^ ~~~u) h)
      have haC : a ∈ C := (List.mem_filter.1 ha).1
      have hbC : b ∈ C := (List.mem_filter.1 hb).1
      have h6 : 6 ≤ hammingDist (a ^^^ ~~~u) (b ^^^ ~~~u) := by
        rw [hammingDist_xor_right]
        exact hc.2 a haC b hbC hab
      rw [hammingDist_eq_countBits] at h6
      have hx3 := hTwt (a ^^^ ~~~u) (List.mem_map.2 ⟨a, ha, rfl⟩)
      have hy3 := hTwt (b ^^^ ~~~u) (List.mem_map.2 ⟨b, hb, rfl⟩)
      have hxor := countBits_xor 17 (fun i => (a ^^^ ~~~u).getLsbD i) (fun i => (b ^^^ ~~~u).getLsbD i)
      have hand0 : countBits 17 (fun i => (a ^^^ ~~~u).getLsbD i && (b ^^^ ~~~u).getLsbD i) = 0 := by omega
      intro i hi
      rw [countBits_eq_zero_imp hand0 i hi]
      rfl
    have hsum := sum_weight_le_of_disjoint 17 T hTdisj hTnd
    have hsum3 : ∀ (l : List (BitVec 17)),
        (∀ x ∈ l, countBits 17 (fun i => x.getLsbD i) = 3) →
        (l.map (fun v => countBits 17 (fun i => v.getLsbD i))).sum = 3 * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          hl z List.mem_cons_self, ih (fun x hx => hl x (List.mem_cons_of_mem z hx))]
        omega
    have hTlen : T.length = S14.length := by simp [T]
    rw [hsum3 T hTwt, hTlen] at hsum
    change S14.length + 5 * S16.length ≤ 5
    omega

/-! ## 4. Fourier / Krawtchouk Identity on `{0, 1}^{17}` -/

private def signBool (b : Bool) : Int := if b then -1 else 1

private theorem signBool_xor (a b : Bool) : signBool (xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

/-- All `k`-element subsets of `{0, ..., n - 1}` represented as sorted lists of indices. -/
private def subsets : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 =>
    subsets n (k + 1) ++ (subsets n k).map (fun s => n :: s)

private def charS (S : List Nat) (u : BitVec 17) : Int :=
  S.foldl (fun acc i => acc * signBool (u.getLsbD i)) 1

private theorem charS_cons (n : Nat) (S : List Nat) (u : BitVec 17) :
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

private theorem charS_xor (S : List Nat) (u v : BitVec 17) :
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

private theorem charS_pm1 (S : List Nat) (u : BitVec 17) :
    charS S u = 1 ∨ charS S u = -1 := by
  induction S with
  | nil => left; rfl
  | cons i rest ih =>
    rw [charS_cons]
    rcases ih with h | h <;> rw [h] <;> cases u.getLsbD i <;> simp [signBool]

/-- Krawtchouk polynomial `K n k w` via the standard recurrence. -/
private def Kraw : Nat → Nat → Nat → Int
  | _, 0, _ => 1
  | 0, _ + 1, _ => 0
  | n + 1, k + 1, 0 => Kraw n (k + 1) 0 + Kraw n k 0
  | n + 1, k + 1, w + 1 => Kraw n (k + 1) w - Kraw n k w

private theorem Kraw_step_zero : ∀ (n k w : Nat),
    Kraw (n + 1) (k + 1) w = Kraw n (k + 1) w + Kraw n k w →
    True := fun _ _ _ _ => trivial

/-- Key Pascal identity for Krawtchouk polynomials (for valid weights `w ≤ n`):
    adding a `0`-bit (weight unchanged) gives `K n (k+1) w + K n k w`,
    adding a `1`-bit (weight `w+1`) gives `K n (k+1) w - K n k w`. -/
private theorem Kraw_add_zero : ∀ (n k w : Nat), w ≤ n →
    Kraw (n + 1) (k + 1) w = Kraw n (k + 1) w + Kraw n k w := by
  intro n
  induction n with
  | zero =>
    intro k w hw
    cases w with
    | zero => rfl
    | succ w' => omega
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
    | cons z zs ih =>
      intro a
      simp only [List.foldl_cons, Int.zero_add]
      rw [ih (a + f z), ih (f z), Int.add_assoc]
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
    have hcongr : ∀ (l : List β) (g1 g2 : β → Int), (∀ x, g1 x = g2 x) → sumInt l g1 = sumInt l g2 := by
      intro l g1 g2 hfg
      induction l with | nil => rfl | cons x xs ih => rw [sumInt_cons, sumInt_cons, hfg x, ih]
    exact hcongr lb _ _ (fun b => (sumInt_cons a as (fun a => f a b)).symm)

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

private theorem sum_charS_eq_Kraw :
    ∀ (n k : Nat) (x : BitVec 17),
      sumInt (subsets n k) (fun S => charS S x) = Kraw n k (countBits n (fun i => x.getLsbD i))
  | _, 0, _ => by simp [subsets, sumInt_cons, sumInt_nil, charS, Kraw]
  | 0, k + 1, _ => by simp [subsets, sumInt_nil, Kraw]
  | n + 1, k + 1, x => by
    simp only [subsets, sumInt_append, sumInt_map, countBits]
    have hmap : sumInt (subsets n k) (fun s => charS (n :: s) x) =
        signBool (x.getLsbD n) * sumInt (subsets n k) (fun s => charS s x) := by
      rw [← sumInt_mul_left]
      have heq : ∀ (l : List (List Nat)),
          sumInt l (fun s => charS (n :: s) x) = sumInt l (fun s => signBool (x.getLsbD n) * charS s x) := by
        intro l
        induction l with
        | nil => rfl
        | cons s ss ih => rw [sumInt_cons, sumInt_cons, charS_cons, ih]
      exact heq _
    rw [hmap, sum_charS_eq_Kraw n (k + 1) x, sum_charS_eq_Kraw n k x]
    by_cases hx : x.getLsbD n = true
    · simp only [hx, signBool, ↓reduceIte, Kraw]
      omega
    · have hxf : x.getLsbD n = false := by cases h : x.getLsbD n <;> simp_all
      simp only [hxf, signBool, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Nat.add_zero]
      exact (Kraw_add_zero n k _ (countBits_le n _)).symm

private theorem sum_pair_Kraw (k : Nat) (C : List (BitVec 17)) :
    sumInt C (fun u => sumInt C (fun v => Kraw 17 k (hammingDist u v))) =
    sumInt (subsets 17 k) (fun S => (sumInt C (fun u => charS S u)) * (sumInt C (fun u => charS S u))) := by
  have hinner : ∀ u v : BitVec 17,
      Kraw 17 k (hammingDist u v) = sumInt (subsets 17 k) (fun S => charS S u * charS S v) := by
    intro u v
    unfold hammingDist
    rw [hammingWeight_eq_countBits, ← sum_charS_eq_Kraw 17 k (u ^^^ v)]
    have heq : ∀ (l : List (List Nat)),
        sumInt l (fun S => charS S (u ^^^ v)) = sumInt l (fun S => charS S u * charS S v) := by
      intro l
      induction l with
      | nil => rfl
      | cons s ss ih => simp only [sumInt_cons, charS_xor, ih]
    exact heq _
  have h1 : sumInt C (fun u => sumInt C (fun v => Kraw 17 k (hammingDist u v))) =
      sumInt C (fun u => sumInt C (fun v => sumInt (subsets 17 k) (fun S => charS S u * charS S v))) := by
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
    apply hcongr; intro u; apply hcongr; intro v; exact hinner u v
  rw [h1]
  have h2 : ∀ u : BitVec 17,
      sumInt C (fun v => sumInt (subsets 17 k) (fun S => charS S u * charS S v)) =
      sumInt (subsets 17 k) (fun S => charS S u * sumInt C (fun v => charS S v)) := by
    intro u
    rw [sumInt_swap]
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
    apply hcongr; intro S
    exact sumInt_mul_left C (charS S u) (fun v => charS S v)
  have h3 : sumInt C (fun u => sumInt C (fun v => sumInt (subsets 17 k) (fun S => charS S u * charS S v))) =
      sumInt C (fun u => sumInt (subsets 17 k) (fun S => charS S u * sumInt C (fun v => charS S v))) := by
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
    apply hcongr; intro u; exact h2 u
  rw [h3, sumInt_swap]
  have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
    intro α l f g hfg
    induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
  apply hcongr; intro S
  have hmul : sumInt C (fun u => charS S u * sumInt C (fun v => charS S v)) =
      sumInt C (fun u => sumInt C (fun v => charS S v) * charS S u) := by
    apply hcongr; intro u; exact Int.mul_comm _ _
  rw [hmul, sumInt_mul_left, Int.mul_comm]

/-! ## 5. Parity Strengthening for Odd `|C|` & Final Contradiction -/

private theorem sumInt_pm1_mod2 (C : List (BitVec 17)) (S : List Nat) :
    sumInt C (fun u => charS S u) % 2 = (C.length : Int) % 2 := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumInt_cons, List.length_cons]
    rcases charS_pm1 S x with h | h <;> rw [h] <;> omega

private theorem sq_ge_one_of_odd {a : Int} (h : a % 2 = 1) : (1 : Int) ≤ a * a := by
  have hne : a ≠ 0 := by omega
  by_cases hpos : 0 < a
  · have hge : 1 ≤ a := by omega
    have := Int.mul_le_mul hge hge (by decide) (by omega)
    simpa using this
  · have hle : a ≤ -1 := by omega
    have hneg : 1 ≤ -a := by omega
    have hsq : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have := Int.mul_le_mul hneg hneg (by decide) (by omega)
    omega

private theorem sq_ge_zero (a : Int) : (0 : Int) ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a := by omega
    have hmul := Int.mul_nonneg hneg hneg
    have heq : (-a) * (-a) = a * a := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private def P15 (w : Nat) : Int :=
  15 * Kraw 17 0 w + 5 * Kraw 17 1 w + 5 * Kraw 17 2 w + Kraw 17 3 w + Kraw 17 4 w

private theorem P15_values :
    P15 0 = 3840 ∧ P15 6 = 0 ∧ P15 8 = 0 ∧ P15 10 = 0 ∧ P15 12 = 0 ∧
    P15 14 = 256 ∧ P15 16 = 1280 := by
  decide +kernel

private theorem subsets_lengths :
    (subsets 17 0).length = 1 ∧
    (subsets 17 1).length = 17 ∧
    (subsets 17 2).length = 136 ∧
    (subsets 17 3).length = 680 ∧
    (subsets 17 4).length = 2380 := by
  decide +kernel

private theorem sum_P15_row_le {C : List (BitVec 17)} (hc : IsBinaryCode 17 6 C)
    (heven : ∀ u ∈ C, ∀ v ∈ C, hammingDist u v % 2 = 0) {u : BitVec 17} (hu : u ∈ C) :
    sumInt C (fun v => P15 (hammingDist u v)) ≤ 5120 := by
  rcases P15_values with ⟨hp0, hp6, hp8, hp10, hp12, hp14, hp16⟩
  have hpoint : ∀ v ∈ C,
      P15 (hammingDist u v) =
      (if v == u then (3840 : Int) else 0) +
      (if hammingDist u v == 14 then (256 : Int) else 0) +
      (if hammingDist u v == 16 then (1280 : Int) else 0) := by
    intro v hv
    by_cases hvu : v = u
    · subst hvu
      simp [hammingDist_self, hp0]
    · have hne : (v == u) = false := beq_false_of_ne hvu
      have hge6 := hc.2 u hu v hv (Ne.symm hvu)
      have hle17 := hammingDist_le 17 u v
      have hev := heven u hu v hv
      have hcases : hammingDist u v = 6 ∨ hammingDist u v = 8 ∨ hammingDist u v = 10 ∨
          hammingDist u v = 12 ∨ hammingDist u v = 14 ∨ hammingDist u v = 16 := by omega
      rcases hcases with hd | hd | hd | hd | hd | hd <;>
        simp [hne, hd, hp6, hp8, hp10, hp12, hp14, hp16]
  have hsum_eq : sumInt C (fun v => P15 (hammingDist u v)) =
      sumInt C (fun v => if v == u then (3840 : Int) else 0) +
      sumInt C (fun v => if hammingDist u v == 14 then (256 : Int) else 0) +
      sumInt C (fun v => if hammingDist u v == 16 then (1280 : Int) else 0) := by
    rw [← sumInt_add, ← sumInt_add]
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int),
        (∀ x ∈ l, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [sumInt_cons, hfg x List.mem_cons_self,
          ih (fun y hy => hfg y (List.mem_cons_of_mem x hy))]
    exact hcongr C _ _ hpoint
  have hsum_filter : ∀ (l : List (BitVec 17)) (p : BitVec 17 → Bool) (c : Int),
      sumInt l (fun v => if p v then c else 0) = ((l.filter p).length : Int) * c := by
    intro l p c
    induction l with
    | nil => simp [sumInt_nil]
    | cons x xs ih =>
      rw [sumInt_cons, List.filter_cons, ih]
      cases p x
      · simp
      · simp only [↓reduceIte, List.length_cons, Int.natCast_add, Int.add_mul]
        simp [Int.add_comm]
  have hself : (C.filter (fun v => v == u)).length ≤ 1 := by
    have haux : ∀ (l : List (BitVec 17)), l.Nodup → (l.filter (fun v => v == u)).length ≤ 1 := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons x xs ih =>
        intro hnd
        have ⟨hx, hxs⟩ := List.nodup_cons.1 hnd
        simp only [List.filter_cons]
        by_cases hxu : x = u
        · subst hxu
          simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
          have h0 : ∀ l' : List (BitVec 17), x ∉ l' → (l'.filter (fun v => v == x)).length = 0 := by
            intro l' hnl
            induction l' with
            | nil => rfl
            | cons z zs ih2 =>
              have hne : z ≠ x := fun h => hnl (h ▸ List.mem_cons_self)
              have hbeq : (z == x) = false := beq_false_of_ne hne
              simp only [List.filter_cons, hbeq]
              exact ih2 (fun hm => hnl (List.mem_cons_of_mem z hm))
          rw [h0 xs hx]
          omega
        · have hbeq : (x == u) = false := beq_false_of_ne hxu
          simp only [hbeq]
          exact ih hxs
    exact haux C hc.1
  rw [hsum_eq, hsum_filter, hsum_filter, hsum_filter]
  have hpack := local_packing_bound hc u
  omega

private theorem main_fourier_ineq {C : List (BitVec 17)} (hc : IsBinaryCode 17 6 C)
    (heven : ∀ u ∈ C, ∀ v ∈ C, hammingDist u v % 2 = 0) :
    let M : Int := C.length
    15 * M * M + (if C.length % 2 = 1 then (3825 : Int) else 0) ≤ 5120 * M := by
  intro M
  -- Upper bound on double sum of P15
  have hupper : sumInt C (fun u => sumInt C (fun v => P15 (hammingDist u v))) ≤ 5120 * M := by
    have h1 : sumInt C (fun u => sumInt C (fun v => P15 (hammingDist u v))) ≤
        sumInt C (fun _ => (5120 : Int)) :=
      sumInt_le C _ _ (fun u hu => sum_P15_row_le hc heven hu)
    rw [sumInt_const] at h1
    omega
  -- Expand double sum of P15 into linear combination of K_0..K_4 double sums
  have hlin : sumInt C (fun u => sumInt C (fun v => P15 (hammingDist u v))) =
      15 * sumInt C (fun u => sumInt C (fun v => Kraw 17 0 (hammingDist u v))) +
      5 * sumInt C (fun u => sumInt C (fun v => Kraw 17 1 (hammingDist u v))) +
      5 * sumInt C (fun u => sumInt C (fun v => Kraw 17 2 (hammingDist u v))) +
      sumInt C (fun u => sumInt C (fun v => Kraw 17 3 (hammingDist u v))) +
      sumInt C (fun u => sumInt C (fun v => Kraw 17 4 (hammingDist u v))) := by
    have hinner : ∀ u, sumInt C (fun v => P15 (hammingDist u v)) =
        15 * sumInt C (fun v => Kraw 17 0 (hammingDist u v)) +
        5 * sumInt C (fun v => Kraw 17 1 (hammingDist u v)) +
        5 * sumInt C (fun v => Kraw 17 2 (hammingDist u v)) +
        sumInt C (fun v => Kraw 17 3 (hammingDist u v)) +
        sumInt C (fun v => Kraw 17 4 (hammingDist u v)) := by
      intro u
      unfold P15
      rw [sumInt_add, sumInt_add, sumInt_add, sumInt_add,
          sumInt_mul_left, sumInt_mul_left, sumInt_mul_left]
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
    rw [hcongr C _ _ hinner, sumInt_add, sumInt_add, sumInt_add, sumInt_add,
        sumInt_mul_left, sumInt_mul_left, sumInt_mul_left]
  -- Evaluate k = 0 term = M * M
  have hk0 : sumInt C (fun u => sumInt C (fun v => Kraw 17 0 (hammingDist u v))) = M * M := by
    have h1 : ∀ u, sumInt C (fun v => Kraw 17 0 (hammingDist u v)) = M := by
      intro u
      have : sumInt C (fun _ => (1 : Int)) = M := by rw [sumInt_const]; omega
      exact this
    have hcongr : ∀ {α : Type} (l : List α) (f g : α → Int), (∀ x, f x = g x) → sumInt l f = sumInt l g := by
      intro α l f g hfg
      induction l with | nil => rfl | cons x xs ih => simp only [sumInt_cons, hfg x, ih]
    rw [hcongr C _ _ h1, sumInt_const]
  -- Lower bound each k ∈ {1,2,3,4} term
  have hk_ge : ∀ k, (if C.length % 2 = 1 then ((subsets 17 k).length : Int) else 0) ≤
      sumInt C (fun u => sumInt C (fun v => Kraw 17 k (hammingDist u v))) := by
    intro k
    rw [sum_pair_Kraw k C]
    split
    · rename_i hodd
      have h1 : sumInt (subsets 17 k) (fun _ => (1 : Int)) ≤
          sumInt (subsets 17 k) (fun S => (sumInt C (fun u => charS S u)) * (sumInt C (fun u => charS S u))) := by
        apply sumInt_le
        intro S _
        apply sq_ge_one_of_odd
        rw [sumInt_pm1_mod2]
        omega
      rw [sumInt_const] at h1
      omega
    · have h0 : sumInt (subsets 17 k) (fun _ => (0 : Int)) ≤
          sumInt (subsets 17 k) (fun S => (sumInt C (fun u => charS S u)) * (sumInt C (fun u => charS S u))) :=
        sumInt_le _ _ _ (fun S _ => sq_ge_zero _)
      rw [sumInt_const] at h0
      omega
  rcases subsets_lengths with ⟨_, hl1, hl2, hl3, hl4⟩
  have h1 := hk_ge 1; rw [hl1] at h1
  have h2 := hk_ge 2; rw [hl2] at h2
  have h3 := hk_ge 3; rw [hl3] at h3
  have h4 := hk_ge 4; rw [hl4] at h4
  rw [hlin] at hupper
  rw [hk0] at hupper
  have hassoc : 15 * M * M = 15 * (M * M) := Int.mul_assoc 15 M M
  rw [hassoc]
  by_cases hodd : C.length % 2 = 1
  · simp only [hodd, ↓reduceIte] at h1 h2 h3 h4 ⊢
    omega
  · simp only [hodd, ↓reduceIte] at h1 h2 h3 h4 ⊢
    omega

theorem record : ¬ Codes.Statements.EC_rec_17_6.Record 341 := by
  rintro ⟨C, hlen, hc⟩
  rcases reduce_to_even_code hc with ⟨C', hlen', hc', heven⟩
  have hineq := main_fourier_ineq hc' heven
  dsimp only at hineq
  have hge : 341 ≤ C'.length := by omega
  by_cases h341 : C'.length = 341
  · rw [h341] at hineq
    have hodd : (341 : Nat) % 2 = 1 := rfl
    simp only [hodd, ↓reduceIte] at hineq
    omega
  · have hge342 : 342 ≤ C'.length := by omega
    have h0 : 15 * (C'.length : Int) * (C'.length : Int) ≤ 5120 * (C'.length : Int) := by
      split at hineq <;> omega
    have hmul : (5130 : Int) * (C'.length : Int) ≤ 15 * (C'.length : Int) * (C'.length : Int) := by
      have h1 : (5130 : Int) ≤ 15 * (C'.length : Int) := by omega
      exact Int.mul_le_mul_of_nonneg_right h1 (by omega)
    omega

end Codes.Claims.EC_rec_17_6_not_s341
