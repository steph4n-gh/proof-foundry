import Crypto.Core
import Crypto.Statements.CZ_rec_ascon_gates

/-!
  CZ-rec-ascon-gates exact optimality lower bound:
    `¬ Crypto.Statements.CZ_rec_ascon_gates.Record 14`

  Proves that no well-formed 5-input 5-output B2 circuit with ≤ 5 non-linear gates and
  AND-depth ≤ 1 can compute the NIST SP 800-232 Ascon 5-bit S-box in ≤ 14 total gates,
  closing `CZ-rec-ascon-gates` to exact optimality (matching the 15-gate circuit in
  `CZ_rec_ascon_gates_s15`, and improving the published lower bound from 13 to 15).

  Proof outline:
  1. Every wire of AND-depth ≤ 1 evaluates (mod constants) to a degree-≤-2 polynomial
     in GF(2)[x0..x4], uniquely encoded as a 15-bit `Nat` (5 linear bits + 10 quadratic bits).
  2. The 5 Ascon outputs have linearly independent quadratic parts spanning a 5-dim
     subspace `Q ⊆ GF(2)^10`. Thus a valid depth-1 circuit has exactly 5 depth-1 non-linear
     gates whose quadratic parts form a basis of `Q` chosen from the 10 rank-1 forms in `Q`.
  3. No Ascon output equals any non-linear gate mod constants, so the 5 outputs require 5
     distinct depth-1 linear gates, leaving ≤ 4 linear gates for depth-0 prerequisites and
     any helper wire.
  4. All 121 bases × 243 factor-pair choices are discharged in the Lean 4 kernel:
     - Every zero-helper configuration (|pre| = 4, or |pre| = 3 with a linear helper `h < 32`)
       is refuted by single-gate domain filtering (zero 5-tuple enumeration needed).
     - All 27 depth-0-reachable |pre| = 3 configurations with a quadratic helper `h` satisfy
       a block-disjointness invariant separating `{y0, y3, y4}` from `{y1, y2}` and are refuted
       by checking all 64 linear-shift choices for `(g0, g3, g4)`.
-/

namespace Crypto.Claims.CZ_rec_ascon_gates_not_s14

open Crypto

/-! ## 1. Degree-≤-2 polynomials over GF(2)^5 (mod constants) -/

private def evalLin (l : Nat) (x : BitVec 5) : Bool :=
  xor (if l.testBit 0 then x.getLsbD 0 else false)
  (xor (if l.testBit 1 then x.getLsbD 1 else false)
  (xor (if l.testBit 2 then x.getLsbD 2 else false)
  (xor (if l.testBit 3 then x.getLsbD 3 else false)
       (if l.testBit 4 then x.getLsbD 4 else false))))

private def evalQuad (q : Nat) (x : BitVec 5) : Bool :=
  let b0 := x.getLsbD 0; let b1 := x.getLsbD 1; let b2 := x.getLsbD 2
  let b3 := x.getLsbD 3; let b4 := x.getLsbD 4
  xor (if q.testBit 0 then b0 && b1 else false)
  (xor (if q.testBit 1 then b0 && b2 else false)
  (xor (if q.testBit 2 then b0 && b3 else false)
  (xor (if q.testBit 3 then b0 && b4 else false)
  (xor (if q.testBit 4 then b1 && b2 else false)
  (xor (if q.testBit 5 then b1 && b3 else false)
  (xor (if q.testBit 6 then b1 && b4 else false)
  (xor (if q.testBit 7 then b2 && b3 else false)
  (xor (if q.testBit 8 then b2 && b4 else false)
       (if q.testBit 9 then b3 && b4 else false)))))))))

private def evalPoly (p : Nat) (x : BitVec 5) : Bool :=
  xor (evalLin p x) (evalQuad (p >>> 5) x)

private def prodQ (a b : Nat) : Nat :=
  let pair (i j k : Nat) : Nat :=
    if xor (a.testBit i && b.testBit j) (a.testBit j && b.testBit i) then 1 <<< k else 0
  pair 0 1 0 ||| pair 0 2 1 ||| pair 0 3 2 ||| pair 0 4 3 |||
  pair 1 2 4 ||| pair 1 3 5 ||| pair 1 4 6 ||| pair 2 3 7 |||
  pair 2 4 8 ||| pair 3 4 9

private def prodPoly (a b : Nat) : Nat :=
  ((a &&& b) &&& 31) ||| (prodQ a b <<< 5)

private theorem testBit_xor_cond (c1 c2 v : Bool) :
    (if xor c1 c2 then v else false) = xor (if c1 then v else false) (if c2 then v else false) := by
  cases c1 <;> cases c2 <;> cases v <;> rfl

private theorem xor_swap5 (a1 a2 b1 b2 : Bool) :
    xor (xor a1 a2) (xor b1 b2) = xor (xor a1 b1) (xor a2 b2) := by
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> rfl

private theorem evalLin_xor (a b : Nat) (x : BitVec 5) :
    evalLin (a ^^^ b) x = xor (evalLin a x) (evalLin b x) := by
  unfold evalLin
  simp only [Nat.testBit_xor, testBit_xor_cond]
  apply Eq.symm
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  exact xor_swap5 _ _ _ _

private theorem evalQuad_xor (a b : Nat) (x : BitVec 5) :
    evalQuad (a ^^^ b) x = xor (evalQuad a x) (evalQuad b x) := by
  unfold evalQuad
  simp only [Nat.testBit_xor, testBit_xor_cond]
  apply Eq.symm
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  rw [xor_swap5]; congr 1
  exact xor_swap5 _ _ _ _

private theorem evalPoly_xor (p1 p2 : Nat) (x : BitVec 5) :
    evalPoly (p1 ^^^ p2) x = xor (evalPoly p1 x) (evalPoly p2 x) := by
  unfold evalPoly
  rw [Nat.shiftRight_xor_distrib, evalLin_xor, evalQuad_xor]
  exact xor_swap5 _ _ _ _

private theorem evalPoly_zero (x : BitVec 5) : evalPoly 0 x = false := by
  simp [evalPoly, evalLin, evalQuad]

private theorem evalPoly_input (i : Fin 5) (x : BitVec 5) :
    evalPoly (1 <<< i.val) x = x.getLsbD i.val := by
  revert i x; decide +kernel

private theorem evalQuad_zero_of_lt32 {a : Nat} (ha : a < 32) (x : BitVec 5) :
    evalQuad (a >>> 5) x = false := by
  have h : a >>> 5 = 0 := by omega
  simp [h, evalQuad]

private theorem evalPoly_lt32 {a : Nat} (ha : a < 32) (x : BitVec 5) :
    evalPoly a x = evalLin a x := by
  simp [evalPoly, evalQuad_zero_of_lt32 ha]

private theorem evalPoly_prodPoly_fin :
    ∀ a : Fin 32, ∀ b : Fin 32, ∀ x : BitVec 5,
      evalPoly (prodPoly a.val b.val) x = (evalLin a.val x && evalLin b.val x) := by
  have hstep : ∀ a b : Fin 32,
      (∀ x : BitVec 5, evalPoly (prodPoly a.val b.val) x = (evalLin a.val x && evalLin b.val x)) := by
    intro a b x
    -- Prove directly by splitting bits of x via bool algebra (no 32^3 decide!)
    have hbit : ∀ k, (prodPoly a.val b.val).testBit k =
        if k < 5 then a.val.testBit k && b.val.testBit k
        else if k < 15 then (prodQ a.val b.val).testBit (k - 5)
        else false := by
      intro k
      unfold prodPoly
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hk5 : k < 5
      · have hge : ¬ (5 ≤ k) := by omega
        have h31 : (31 : Nat).testBit k = true := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk5
        simp [hk5, hge, Nat.testBit_and, h31]
      · have h31 : (31 : Nat).testBit k = false := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false hk5
        have hge : 5 ≤ k := by omega
        by_cases hk15 : k < 15
        · simp [hk5, hk15, hge, Nat.testBit_and, h31]
        · have hqlt : prodQ a.val b.val < 2 ^ 10 := by
            unfold prodQ
            have hp : ∀ c : Bool, ∀ s, s < 10 → (if c then 1 <<< s else 0) < 2 ^ 10 := by
              intro c s hs; cases c
              · exact Nat.two_pow_pos 10
              · simp [Nat.shiftLeft_eq]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) hs
            repeat first | apply Nat.or_lt_two_pow | exact hp _ _ (by decide)
          have hq0 : (prodQ a.val b.val).testBit (k - 5) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hqlt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
          simp [hk5, hk15, hge, Nat.testBit_and, h31, hq0]
    have hqbit : ∀ k, k < 10 → ((prodPoly a.val b.val) >>> 5).testBit k = (prodQ a.val b.val).testBit k := by
      intro k hk
      rw [Nat.testBit_shiftRight, hbit (5 + k)]
      have h1 : ¬ (5 + k < 5) := by omega
      have h2 : 5 + k < 15 := by omega
      simp [h1, h2]
    have hprodQ_bits :
        ((prodQ a.val b.val).testBit 0 = xor (a.val.testBit 0 && b.val.testBit 1) (a.val.testBit 1 && b.val.testBit 0)) ∧
        ((prodQ a.val b.val).testBit 1 = xor (a.val.testBit 0 && b.val.testBit 2) (a.val.testBit 2 && b.val.testBit 0)) ∧
        ((prodQ a.val b.val).testBit 2 = xor (a.val.testBit 0 && b.val.testBit 3) (a.val.testBit 3 && b.val.testBit 0)) ∧
        ((prodQ a.val b.val).testBit 3 = xor (a.val.testBit 0 && b.val.testBit 4) (a.val.testBit 4 && b.val.testBit 0)) ∧
        ((prodQ a.val b.val).testBit 4 = xor (a.val.testBit 1 && b.val.testBit 2) (a.val.testBit 2 && b.val.testBit 1)) ∧
        ((prodQ a.val b.val).testBit 5 = xor (a.val.testBit 1 && b.val.testBit 3) (a.val.testBit 3 && b.val.testBit 1)) ∧
        ((prodQ a.val b.val).testBit 6 = xor (a.val.testBit 1 && b.val.testBit 4) (a.val.testBit 4 && b.val.testBit 1)) ∧
        ((prodQ a.val b.val).testBit 7 = xor (a.val.testBit 2 && b.val.testBit 3) (a.val.testBit 3 && b.val.testBit 2)) ∧
        ((prodQ a.val b.val).testBit 8 = xor (a.val.testBit 2 && b.val.testBit 4) (a.val.testBit 4 && b.val.testBit 2)) ∧
        ((prodQ a.val b.val).testBit 9 = xor (a.val.testBit 3 && b.val.testBit 4) (a.val.testBit 4 && b.val.testBit 3)) := by
      unfold prodQ
      have hite : ∀ (c : Bool) (k j : Nat), (if c then 1 <<< k else 0).testBit j = (c && decide (j = k)) := by
        intro c k j; cases c
        · simp
        · simp [Nat.testBit_shiftLeft]
          by_cases h : j = k
          · subst h; simp
          · by_cases hle : k ≤ j
            · cases hm : j - k with
              | zero => omega
              | succ m => simp [h, hle, Nat.testBit_succ]
            · simp [h, hle]
      simp only [Nat.testBit_or, hite]
      refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    unfold evalPoly evalLin evalQuad
    rw [hbit 0, hbit 1, hbit 2, hbit 3, hbit 4]
    rw [hqbit 0 (by decide), hqbit 1 (by decide), hqbit 2 (by decide), hqbit 3 (by decide),
        hqbit 4 (by decide), hqbit 5 (by decide), hqbit 6 (by decide), hqbit 7 (by decide),
        hqbit 8 (by decide), hqbit 9 (by decide)]
    rw [hprodQ_bits.1, hprodQ_bits.2.1, hprodQ_bits.2.2.1, hprodQ_bits.2.2.2.1,
        hprodQ_bits.2.2.2.2.1, hprodQ_bits.2.2.2.2.2.1, hprodQ_bits.2.2.2.2.2.2.1,
        hprodQ_bits.2.2.2.2.2.2.2.1, hprodQ_bits.2.2.2.2.2.2.2.2.1, hprodQ_bits.2.2.2.2.2.2.2.2.2]
    simp only [show (0 < 5) = True by decide, show (1 < 5) = True by decide,
               show (2 < 5) = True by decide, show (3 < 5) = True by decide,
               show (4 < 5) = True by decide, ite_true]
    generalize a.val.testBit 0 = a0; generalize a.val.testBit 1 = a1; generalize a.val.testBit 2 = a2
    generalize a.val.testBit 3 = a3; generalize a.val.testBit 4 = a4
    generalize b.val.testBit 0 = b0; generalize b.val.testBit 1 = b1; generalize b.val.testBit 2 = b2
    generalize b.val.testBit 3 = b3; generalize b.val.testBit 4 = b4
    generalize x.getLsbD 0 = x0; generalize x.getLsbD 1 = x1; generalize x.getLsbD 2 = x2
    generalize x.getLsbD 3 = x3; generalize x.getLsbD 4 = x4
    have hl : ∀ c v : Bool, (if c then v else false) = (c && v) := fun c v => by cases c <;> simp
    simp only [hl]
    have hre1 : ∀ a b x : Bool, ((a && b) && x) = ((a && x) && (b && x)) := by decide
    have hre2 : ∀ a b c d x y : Bool, ((xor (a && b) (c && d)) && (x && y)) =
        xor ((a && x) && (b && y)) ((c && y) && (d && x)) := by decide
    rw [hre1 a0 b0 x0, hre1 a1 b1 x1, hre1 a2 b2 x2, hre1 a3 b3 x3, hre1 a4 b4 x4]
    rw [hre2 a0 b1 a1 b0 x0 x1, hre2 a0 b2 a2 b0 x0 x2, hre2 a0 b3 a3 b0 x0 x3,
        hre2 a0 b4 a4 b0 x0 x4, hre2 a1 b2 a2 b1 x1 x2, hre2 a1 b3 a3 b1 x1 x3,
        hre2 a1 b4 a4 b1 x1 x4, hre2 a2 b3 a3 b2 x2 x3, hre2 a2 b4 a4 b2 x2 x4,
        hre2 a3 b4 a4 b3 x3 x4]
    generalize (a0 && x0) = u0; generalize (a1 && x1) = u1; generalize (a2 && x2) = u2
    generalize (a3 && x3) = u3; generalize (a4 && x4) = u4
    generalize (b0 && x0) = v0; generalize (b1 && x1) = v1; generalize (b2 && x2) = v2
    generalize (b3 && x3) = v3; generalize (b4 && x4) = v4
    revert u0 u1 u2 u3 u4 v0 v1 v2 v3 v4
    decide +kernel
  exact hstep

private theorem evalPoly_prodPoly {a b : Nat} (ha : a < 32) (hb : b < 32) (x : BitVec 5) :
    evalPoly (prodPoly a b) x = (evalPoly a x && evalPoly b x) := by
  rw [evalPoly_lt32 ha, evalPoly_lt32 hb]
  exact evalPoly_prodPoly_fin ⟨a, ha⟩ ⟨b, hb⟩ x

private theorem prodPoly_lt (a b : Nat) : prodPoly a b < 32768 := by
  have h1 : ((a &&& b) &&& 31) < 2 ^ 15 := by
    have : ((a &&& b) &&& 31) < 32 := Nat.and_lt_two_pow _ (by decide : 31 < 2 ^ 5)
    omega
  have hq : prodQ a b < 2 ^ 10 := by
    unfold prodQ
    have hp : ∀ c : Bool, ∀ s, s < 10 → (if c then 1 <<< s else 0) < 2 ^ 10 := by
      intro c s hs; cases c
      · exact Nat.two_pow_pos 10
      · simp [Nat.shiftLeft_eq]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) hs
    repeat first | apply Nat.or_lt_two_pow | exact hp _ _ (by decide)
  have h2 : (prodQ a b <<< 5) < 2 ^ 15 := by
    rw [Nat.shiftLeft_eq]; omega
  exact Nat.or_lt_two_pow h1 h2

private theorem prodPoly_quad {a b : Nat} (ha : a < 32) (hb : b < 32) (ca cb : Bool) :
    (((prodPoly a b ^^^ (if ca then a else 0)) ^^^ (if cb then b else 0)) >>> 5) = prodQ a b := by
  rw [Nat.shiftRight_xor_distrib, Nat.shiftRight_xor_distrib]
  have ha0 : (if ca then a else 0) >>> 5 = 0 := by cases ca <;> simp <;> omega
  have hb0 : (if cb then b else 0) >>> 5 = 0 := by cases cb <;> simp <;> omega
  rw [ha0, hb0, Nat.xor_zero, Nat.xor_zero]
  unfold prodPoly
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have h1 : ((a &&& b) &&& 31).testBit (5 + k) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (by decide : 31 < 2 ^ 5))
      (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
  have h2 : 5 ≤ 5 + k := by omega
  simp [h1, h2]

private theorem evalPoly_at_0 (p : Nat) : evalPoly p (BitVec.ofNat 5 0) = false := by
  simp [evalPoly, evalLin, evalQuad]

private theorem evalPoly_at_e (p : Nat) (i : Fin 5) :
    evalPoly p (BitVec.ofNat 5 (1 <<< i.val)) = p.testBit i.val := by
  rcases i with ⟨i, hi⟩; match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [evalPoly, evalLin, evalQuad]

private theorem evalPoly_at_pair (p : Nat) (i j k : Nat)
    (h : (i = 0 ∧ j = 1 ∧ k = 0) ∨ (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 0 ∧ j = 3 ∧ k = 2) ∨
         (i = 0 ∧ j = 4 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 4) ∨ (i = 1 ∧ j = 3 ∧ k = 5) ∨
         (i = 1 ∧ j = 4 ∧ k = 6) ∨ (i = 2 ∧ j = 3 ∧ k = 7) ∨ (i = 2 ∧ j = 4 ∧ k = 8) ∨
         (i = 3 ∧ j = 4 ∧ k = 9)) :
    evalPoly p (BitVec.ofNat 5 ((1 <<< i) ||| (1 <<< j))) =
      xor (p.testBit i) (xor (p.testBit j) (p.testBit (5 + k))) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
                ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
                ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  simp [evalPoly, evalLin, evalQuad, Nat.testBit_shiftRight]

private theorem poly_unique {p1 p2 : Nat} (h1 : p1 < 32768) (h2 : p2 < 32768) {c0 : Bool}
    (heq : ∀ x : BitVec 5, evalPoly p1 x = xor c0 (evalPoly p2 x)) : p1 = p2 := by
  have hc0 : c0 = false := by
    have h0 := heq (BitVec.ofNat 5 0)
    rw [evalPoly_at_0, evalPoly_at_0] at h0
    cases c0 <;> simp at h0 ⊢
  subst hc0
  have heq' : ∀ x : BitVec 5, evalPoly p1 x = evalPoly p2 x := by
    intro x; simpa using heq x
  have hlin : ∀ i : Fin 5, p1.testBit i.val = p2.testBit i.val := by
    intro i; have := heq' (BitVec.ofNat 5 (1 <<< i.val))
    rwa [evalPoly_at_e, evalPoly_at_e] at this
  have hpair : ∀ i j k,
      ((i = 0 ∧ j = 1 ∧ k = 0) ∨ (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 0 ∧ j = 3 ∧ k = 2) ∨
       (i = 0 ∧ j = 4 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 4) ∨ (i = 1 ∧ j = 3 ∧ k = 5) ∨
       (i = 1 ∧ j = 4 ∧ k = 6) ∨ (i = 2 ∧ j = 3 ∧ k = 7) ∨ (i = 2 ∧ j = 4 ∧ k = 8) ∨
       (i = 3 ∧ j = 4 ∧ k = 9)) →
      p1.testBit (5 + k) = p2.testBit (5 + k) := by
    intro i j k hijk
    have hi : p1.testBit i = p2.testBit i := by
      rcases hijk with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ |
                       ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ |
                       ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> exact hlin ⟨_, by decide⟩
    have hj : p1.testBit j = p2.testBit j := by
      rcases hijk with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
                       ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
                       ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> exact hlin ⟨_, by decide⟩
    have hp := heq' (BitVec.ofNat 5 ((1 <<< i) ||| (1 <<< j)))
    rw [evalPoly_at_pair p1 i j k hijk, evalPoly_at_pair p2 i j k hijk, hi, hj] at hp
    revert hp
    cases p2.testBit i <;> cases p2.testBit j <;> cases p1.testBit (5 + k) <;> cases p2.testBit (5 + k) <;> decide
  apply Nat.eq_of_testBit_eq
  intro k
  match k with
  | 0 => exact hlin ⟨0, by decide⟩
  | 1 => exact hlin ⟨1, by decide⟩
  | 2 => exact hlin ⟨2, by decide⟩
  | 3 => exact hlin ⟨3, by decide⟩
  | 4 => exact hlin ⟨4, by decide⟩
  | 5 => exact hpair 0 1 0 (by simp)
  | 6 => exact hpair 0 2 1 (by simp)
  | 7 => exact hpair 0 3 2 (by simp)
  | 8 => exact hpair 0 4 3 (by simp)
  | 9 => exact hpair 1 2 4 (by simp)
  | 10 => exact hpair 1 3 5 (by simp)
  | 11 => exact hpair 1 4 6 (by simp)
  | 12 => exact hpair 2 3 7 (by simp)
  | 13 => exact hpair 2 4 8 (by simp)
  | 14 => exact hpair 3 4 9 (by simp)
  | m + 15 =>
    have h1' : p1 < 2 ^ 15 := h1
    have h2' : p2 < 2 ^ 15 := h2
    have hle : 2 ^ 15 ≤ 2 ^ (m + 15) := Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1' hle),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2' hle)]

/-! ## 2. Exact Ascon S-box polynomials -/

private def asconLin : Fin 5 → Nat
  | ⟨0, _⟩ => 11   -- x0 ^ x1 ^ x3
  | ⟨1, _⟩ => 31   -- x0 ^ x1 ^ x2 ^ x3 ^ x4
  | ⟨2, _⟩ => 13   -- x0 ^ x2 ^ x3
  | ⟨3, _⟩ => 31   -- x0 ^ x1 ^ x2 ^ x3 ^ x4
  | ⟨4, _⟩ => 30   -- x1 ^ x2 ^ x3 ^ x4

private def asconQuad : Fin 5 → Nat
  | ⟨0, _⟩ => 516  -- x0x3 ^ x3x4
  | ⟨1, _⟩ => 72   -- x0x4 ^ x1x4
  | ⟨2, _⟩ => 1    -- x0x1
  | ⟨3, _⟩ => 176  -- x1x2 ^ x1x3 ^ x2x3
  | ⟨4, _⟩ => 644  -- x0x3 ^ x2x3 ^ x3x4

private def asconPoly (j : Fin 5) : Nat :=
  asconLin j ||| (asconQuad j <<< 5)

private theorem asconPoly_lt : ∀ j : Fin 5, asconPoly j < 32768 := by
  decide

private theorem asconPoly_quad : ∀ j : Fin 5, asconPoly j >>> 5 = asconQuad j := by
  decide

private theorem asconPoly_lin : ∀ j : Fin 5, asconPoly j &&& 31 = asconLin j := by
  decide
private theorem asconQuad_inj : ∀ j1 j2 : Fin 5, asconQuad j1 = asconQuad j2 → j1 = j2 := by decide
private theorem asconPoly_inj : ∀ j1 j2 : Fin 5, asconPoly j1 = asconPoly j2 → j1 = j2 := by decide
private theorem asconQuad_ne_zero : ∀ j : Fin 5, asconQuad j ≠ 0 := by decide
private theorem asconPoly_ge32 : ∀ j : Fin 5, ¬ (asconPoly j < 32) := by decide
private theorem asconPoly_ne_zero : ∀ j : Fin 5, asconPoly j ≠ 0 := by decide


private theorem ascon_matches_poly :
    ∀ j : Fin 5, ∀ x : BitVec 5,
      (Crypto.asconSBox x).getLsbD j.val = xor (j.val == 2) (evalPoly (asconPoly j) x) := by
  decide +kernel

/-! ## 3. Exact B2Op affine / quadratic normal forms & circuit simulation -/

private def opLinC0 (op : B2Op) : Bool := op.b00
private def opLinCa (op : B2Op) : Bool := xor op.b00 op.b10
private def opLinCb (op : B2Op) : Bool := xor op.b00 op.b01

private theorem b2op_linear_eval (op : B2Op) (h : op.isLinear = true) (a b : Bool) :
    op.eval a b = xor (opLinC0 op) (xor (if opLinCa op then a else false) (if opLinCb op then b else false)) := by
  rcases op with ⟨b00, b01, b10, b11⟩
  revert h a b
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide

private theorem b2op_nonlinear_eval (op : B2Op) (h : op.isLinear = false) (a b : Bool) :
    op.eval a b = xor (opLinC0 op)
      (xor (a && b) (xor (if opLinCa op then a else false) (if opLinCb op then b else false))) := by
  rcases op with ⟨b00, b01, b10, b11⟩
  revert h a b
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide

/-- Simulation entry for each wire: `(depth, poly, constBit)`. -/
private structure SimWire where
  depth : Nat
  poly  : Nat
  cbit  : Bool

private def stepSim (acc : Array SimWire) (g : B2Gate) : SimWire :=
  let s1 := acc.getD g.w1 ⟨0, 0, false⟩
  let s2 := acc.getD g.w2 ⟨0, 0, false⟩
  let base := Nat.max s1.depth s2.depth
  if g.op.isLinear then
    let ca := opLinCa g.op
    let cb := opLinCb g.op
    let p := (if ca then s1.poly else 0) ^^^ (if cb then s2.poly else 0)
    let c := xor (opLinC0 g.op) (xor (if ca then s1.cbit else false) (if cb then s2.cbit else false))
    ⟨base, p, c⟩
  else
    let ca := xor (opLinCa g.op) s2.cbit
    let cb := xor (opLinCb g.op) s1.cbit
    let p := (prodPoly s1.poly s2.poly ^^^ (if ca then s1.poly else 0)) ^^^ (if cb then s2.poly else 0)
    let c := xor (opLinC0 g.op)
      (xor (s1.cbit && s2.cbit) (xor (if opLinCa g.op then s1.cbit else false) (if opLinCb g.op then s2.cbit else false)))
    ⟨base + 1, p, c⟩

private def simInit : Array SimWire :=
  Array.ofFn (fun i : Fin 5 => ⟨0, 1 <<< i.val, false⟩)

private def simWires (gates : List B2Gate) : Array SimWire :=
  gates.foldl (fun acc g => acc.push (stepSim acc g)) simInit

private theorem array_getD_push' {α : Type} (arr : Array α) (v d : α) (w : Nat) :
    (arr.push v).getD w d =
      if w < arr.size then arr.getD w d else if w = arr.size then v else d := by
  by_cases hw : w < arr.size
  · have hw1 : w < arr.size + 1 := by omega
    simp [Array.getD, hw, hw1, Array.getElem_push_lt]
  · by_cases hweq : w = arr.size
    · subst hweq; simp [Array.getD]
    · have hnot : ¬ (w < arr.size + 1) := by omega
      simp [Array.getD, hw, hweq, hnot]

private theorem xor_lt_32768 {a b : Nat} (ha : a < 32768) (hb : b < 32768) : a ^^^ b < 32768 :=
  Nat.xor_lt_two_pow (n := 15) ha hb

private theorem xor_lt_32 {a b : Nat} (ha : a < 32) (hb : b < 32) : a ^^^ b < 32 :=
  Nat.xor_lt_two_pow (n := 5) ha hb

private theorem nat_max_eq (a b : Nat) : Nat.max a b = if a ≤ b then b else a := rfl

private theorem simWires_sound (gates : List B2Gate) :
    let sw := simWires gates
    let ds := gates.foldl (fun (acc : Array Nat) g =>
      let base := Nat.max (acc.getD g.w1 0) (acc.getD g.w2 0)
      acc.push (if g.op.isLinear then base else base + 1)) (Array.replicate 5 0)
    sw.size = ds.size ∧
    (∀ w, (sw.getD w ⟨0, 0, false⟩).depth = ds.getD w 0) ∧
    (∀ w, (sw.getD w ⟨0, 0, false⟩).poly < 32768) ∧
    (∀ w, (sw.getD w ⟨0, 0, false⟩).depth = 0 → (sw.getD w ⟨0, 0, false⟩).poly < 32) ∧
    (∀ x : BitVec 5, ∀ w, (sw.getD w ⟨0, 0, false⟩).depth ≤ 1 →
      (MultiCircuit.evalWires x gates).getD w false =
        xor (sw.getD w ⟨0, 0, false⟩).cbit (evalPoly (sw.getD w ⟨0, 0, false⟩).poly x)) := by
  have hgen : ∀ (gs : List B2Gate) (accS : Array SimWire) (accD : Array Nat)
      (accB : BitVec 5 → Array Bool),
      accS.size = accD.size →
      (∀ x, (accB x).size = accS.size) →
      (∀ w, (accS.getD w ⟨0, 0, false⟩).depth = accD.getD w 0) →
      (∀ w, (accS.getD w ⟨0, 0, false⟩).poly < 32768) →
      (∀ w, (accS.getD w ⟨0, 0, false⟩).depth = 0 → (accS.getD w ⟨0, 0, false⟩).poly < 32) →
      (∀ x w, (accS.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        (accB x).getD w false =
          xor (accS.getD w ⟨0, 0, false⟩).cbit (evalPoly (accS.getD w ⟨0, 0, false⟩).poly x)) →
      let sw := gs.foldl (fun acc g => acc.push (stepSim acc g)) accS
      let ds := gs.foldl (fun (acc : Array Nat) g =>
        let base := Nat.max (acc.getD g.w1 0) (acc.getD g.w2 0)
        acc.push (if g.op.isLinear then base else base + 1)) accD
      let bw := fun x => gs.foldl (fun acc g => acc.push (g.op.eval (acc.getD g.w1 false) (acc.getD g.w2 false))) (accB x)
      sw.size = ds.size ∧
      (∀ w, (sw.getD w ⟨0, 0, false⟩).depth = ds.getD w 0) ∧
      (∀ w, (sw.getD w ⟨0, 0, false⟩).poly < 32768) ∧
      (∀ w, (sw.getD w ⟨0, 0, false⟩).depth = 0 → (sw.getD w ⟨0, 0, false⟩).poly < 32) ∧
      (∀ x w, (sw.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        (bw x).getD w false =
          xor (sw.getD w ⟨0, 0, false⟩).cbit (evalPoly (sw.getD w ⟨0, 0, false⟩).poly x)) := by
    intro gs
    induction gs with
    | nil =>
      intro accS accD accB hsz _ hdep hlt h0 hev
      exact ⟨hsz, hdep, hlt, h0, hev⟩
    | cons g gs ih =>
      intro accS accD accB hsz hszB hdep hlt h0 hev
      apply ih
      · simp [Array.size_push, hsz]
      · intro x; simp [Array.size_push, hszB x]
      · intro w
        rw [array_getD_push', array_getD_push', ← hsz]
        by_cases hltw : w < accS.size
        · simp only [hltw, ↓reduceIte]; exact hdep w
        · by_cases heqw : w = accS.size
          · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte, stepSim, hdep g.w1, hdep g.w2]
            cases g.op.isLinear <;> rfl
          · simp only [hltw, heqw, ↓reduceIte]
      · intro w
        rw [array_getD_push']
        by_cases hltw : w < accS.size
        · simp only [hltw, ↓reduceIte]; exact hlt w
        · by_cases heqw : w = accS.size
          · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte, stepSim]
            cases hlin : g.op.isLinear
            · simp only [Bool.false_eq_true, ↓reduceIte]
              apply xor_lt_32768
              · apply xor_lt_32768 (prodPoly_lt _ _)
                cases xor (opLinCa g.op) (accS.getD g.w2 ⟨0, 0, false⟩).cbit with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hlt g.w1
              · cases xor (opLinCb g.op) (accS.getD g.w1 ⟨0, 0, false⟩).cbit with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hlt g.w2
            · simp only [↓reduceIte]
              apply xor_lt_32768
              · cases opLinCa g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hlt g.w1
              · cases opLinCb g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hlt g.w2
          · simp only [hltw, heqw, ↓reduceIte]; decide
      · intro w hw0
        rw [array_getD_push'] at hw0 ⊢
        by_cases hltw : w < accS.size
        · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact h0 w hw0
        · by_cases heqw : w = accS.size
          · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte, stepSim] at hw0 ⊢
            cases hlin : g.op.isLinear
            · simp only [hlin, Bool.false_eq_true, ↓reduceIte] at hw0; omega
            · simp only [hlin, ↓reduceIte] at hw0 ⊢
              have hd1 : (accS.getD g.w1 ⟨0, 0, false⟩).depth = 0 := by
                rw [nat_max_eq] at hw0; split at hw0 <;> omega
              have hd2 : (accS.getD g.w2 ⟨0, 0, false⟩).depth = 0 := by
                rw [nat_max_eq] at hw0; split at hw0 <;> omega
              apply xor_lt_32
              · cases opLinCa g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact h0 g.w1 hd1
              · cases opLinCb g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact h0 g.w2 hd2
          · simp only [hltw, heqw, ↓reduceIte]; decide
      · intro x w hdw
        rw [array_getD_push'] at hdw ⊢
        rw [array_getD_push', hszB x]
        by_cases hltw : w < accS.size
        · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hev x w hdw
        · by_cases heqw : w = accS.size
          · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte, stepSim] at hdw ⊢
            cases hlin : g.op.isLinear
            · simp only [hlin, Bool.false_eq_true, ↓reduceIte] at hdw ⊢
              have hd1 : (accS.getD g.w1 ⟨0, 0, false⟩).depth = 0 := by
                rw [nat_max_eq] at hdw; split at hdw <;> omega
              have hd2 : (accS.getD g.w2 ⟨0, 0, false⟩).depth = 0 := by
                rw [nat_max_eq] at hdw; split at hdw <;> omega
              have hp1 : (accS.getD g.w1 ⟨0, 0, false⟩).poly < 32 := h0 g.w1 hd1
              have hp2 : (accS.getD g.w2 ⟨0, 0, false⟩).poly < 32 := h0 g.w2 hd2
              rw [hev x g.w1 (by omega), hev x g.w2 (by omega), b2op_nonlinear_eval g.op hlin,
                  evalPoly_xor, evalPoly_xor, evalPoly_prodPoly hp1 hp2]
              have hcond : ∀ (c : Bool) (p : Nat), evalPoly (if c then p else 0) x = if c then evalPoly p x else false := by
                intro c p; cases c <;> simp [evalPoly_zero]
              rw [hcond, hcond]
              generalize opLinC0 g.op = c0; generalize opLinCa g.op = ca; generalize opLinCb g.op = cb
              generalize (accS.getD g.w1 ⟨0, 0, false⟩).cbit = c1; generalize (accS.getD g.w2 ⟨0, 0, false⟩).cbit = c2
              generalize evalPoly (accS.getD g.w1 ⟨0, 0, false⟩).poly x = p1
              generalize evalPoly (accS.getD g.w2 ⟨0, 0, false⟩).poly x = p2
              cases c0 <;> cases ca <;> cases cb <;> cases c1 <;> cases c2 <;> cases p1 <;> cases p2 <;> rfl
            · simp only [hlin, ↓reduceIte] at hdw ⊢
              have hd12 : (accS.getD g.w1 ⟨0, 0, false⟩).depth ≤ 1 ∧ (accS.getD g.w2 ⟨0, 0, false⟩).depth ≤ 1 :=
                Nat.max_le.mp hdw
              have hd1 : (accS.getD g.w1 ⟨0, 0, false⟩).depth ≤ 1 := hd12.1
              have hd2 : (accS.getD g.w2 ⟨0, 0, false⟩).depth ≤ 1 := hd12.2
              rw [hev x g.w1 hd1, hev x g.w2 hd2, b2op_linear_eval g.op hlin, evalPoly_xor]
              have hcond : ∀ (c : Bool) (p : Nat), evalPoly (if c then p else 0) x = if c then evalPoly p x else false := by
                intro c p; cases c <;> simp [evalPoly_zero]
              rw [hcond, hcond]
              generalize opLinC0 g.op = c0; generalize opLinCa g.op = ca; generalize opLinCb g.op = cb
              generalize (accS.getD g.w1 ⟨0, 0, false⟩).cbit = c1; generalize (accS.getD g.w2 ⟨0, 0, false⟩).cbit = c2
              generalize evalPoly (accS.getD g.w1 ⟨0, 0, false⟩).poly x = p1
              generalize evalPoly (accS.getD g.w2 ⟨0, 0, false⟩).poly x = p2
              cases c0 <;> cases ca <;> cases cb <;> cases c1 <;> cases c2 <;> cases p1 <;> cases p2 <;> rfl
          · simp only [hltw, heqw, ↓reduceIte, evalPoly_zero]; rfl
  apply hgen gates simInit (Array.replicate 5 0) (fun x => Array.ofFn (fun i : Fin 5 => x.getLsbD i.val))
  · decide
  · intro x; simp [simInit]
  · intro w; by_cases hw : w < 5 <;> simp [simInit, Array.getD, hw]
  · intro w
    by_cases hw : w < 5
    · simp [simInit, Array.getD, hw]
      match w with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
    · simp [simInit, Array.getD, hw]
  · intro w _
    by_cases hw : w < 5
    · simp [simInit, Array.getD, hw]
      match w with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
    · simp [simInit, Array.getD, hw]
  · intro x w _
    by_cases hw : w < 5
    · simp [simInit, Array.getD, hw, evalPoly_input ⟨w, hw⟩ x]
    · simp [simInit, Array.getD, hw, evalPoly_zero]

/-! ## 4. The 10 rank-1 quadratic forms in Q and exact linear algebra over GF(2) -/

/-- The 10 decomposable quadratic forms in `Q = span(asconQuad 0..4)`:
    `(mask_in_Q, quad_10bit, t0, t1, t2)` where `{t0, t1, t2}` is the unique factor triple. -/
private structure Decomp where
  mask : Nat
  quad : Nat
  t0   : Nat
  t1   : Nat
  t2   : Nat
  deriving Repr, DecidableEq, Inhabited

private def decomps : Array Decomp := #[
  ⟨1,  516,  8,  17, 25⟩, -- x3 * (x0+x4)
  ⟨2,  72,   3,  16, 19⟩, -- (x0+x1) * x4
  ⟨4,  1,    1,  2,  3⟩,  -- x0 * x1
  ⟨6,  73,   3,  17, 18⟩, -- (x0+x1) * (x0+x4)
  ⟨7,  589,  11, 17, 26⟩, -- (x0+x1+x3) * (x0+x4)
  ⟨8,  176,  6,  10, 12⟩, -- (x1+x2) * (x1+x3)
  ⟨16, 644,  8,  21, 29⟩, -- x3 * (x0+x2+x4)
  ⟨17, 128,  4,  8,  12⟩, -- x2 * x3
  ⟨25, 48,   2,  12, 14⟩, -- x1 * (x2+x3)
  ⟨29, 49,   2,  13, 15⟩  -- x1 * (x0+x2+x3)
]

private def qOfMask (m : Nat) : Nat :=
  (if m.testBit 0 then asconQuad ⟨0, by decide⟩ else 0) ^^^
  (if m.testBit 1 then asconQuad ⟨1, by decide⟩ else 0) ^^^
  (if m.testBit 2 then asconQuad ⟨2, by decide⟩ else 0) ^^^
  (if m.testBit 3 then asconQuad ⟨3, by decide⟩ else 0) ^^^
  (if m.testBit 4 then asconQuad ⟨4, by decide⟩ else 0)

private theorem asconQuad_indep : ∀ m : Fin 32, m.val ≠ 0 → qOfMask m.val ≠ 0 := by
  decide +kernel

private theorem nat_xor_swap (a1 a2 b1 b2 : Nat) :
    (a1 ^^^ a2) ^^^ (b1 ^^^ b2) = (a1 ^^^ b1) ^^^ (a2 ^^^ b2) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_xor]
  cases a1.testBit k <;> cases a2.testBit k <;> cases b1.testBit k <;> cases b2.testBit k <;> rfl

private theorem qOfMask_xor (m1 m2 : Nat) : qOfMask (m1 ^^^ m2) = qOfMask m1 ^^^ qOfMask m2 := by
  have h1 : ∀ (c1 c2 : Bool) (v : Nat),
      (if xor c1 c2 then v else 0) = (if c1 then v else 0) ^^^ (if c2 then v else 0) := by
    intro c1 c2 v; cases c1 <;> cases c2 <;> simp
  unfold qOfMask
  simp only [Nat.testBit_xor, h1]
  apply Eq.symm
  rw [nat_xor_swap]; congr 1
  rw [nat_xor_swap]; congr 1
  rw [nat_xor_swap]; congr 1
  exact nat_xor_swap _ _ _ _

private theorem qOfMask_bit : ∀ j : Fin 5, qOfMask (1 <<< j.val) = asconQuad j := by
  decide

private theorem decomp_quad_eq : ∀ i : Fin 10, qOfMask (decomps[i.val]).mask = (decomps[i.val]).quad := by
  decide +kernel

/-- Every pair `(a, b)` with `prodQ a b ∈ Q \ {0}` matches one of the 10 decomposable forms,
    and `(a, b)` is a pair of distinct elements of its unique factor triple `{t0, t1, t2}`. -/
private def qMaskLookup : Array Nat :=
  -- Map 10-bit `q`? Even simpler: check directly over `(a, b) ∈ Fin 32 × Fin 32`!
  #[0]

private theorem prodQ_in_Q_classified_aux :
    (List.range 32).all (fun a =>
      (List.range 32).all (fun b =>
        let q := prodQ a b
        if q == 0 then true
        else
          match (List.range 31).find? (fun m => qOfMask (m + 1) == q) with
          | none => true
          | some m =>
            let mv := m + 1
            (List.finRange 10).any fun i =>
              let d := decomps[i.val]
              d.mask == mv && (a == d.t0 || a == d.t1 || a == d.t2) &&
              (b == d.t0 || b == d.t1 || b == d.t2) && (a != b))) = true := by
  decide +kernel

private theorem prodQ_in_Q_classified :
    ∀ a : Fin 32, ∀ b : Fin 32, ∀ m : Fin 32,
      m.val ≠ 0 → prodQ a.val b.val = qOfMask m.val →
      ∃ i : Fin 10,
        (decomps[i.val]).mask = m.val ∧
        (a.val = (decomps[i.val]).t0 ∨ a.val = (decomps[i.val]).t1 ∨ a.val = (decomps[i.val]).t2) ∧
        (b.val = (decomps[i.val]).t0 ∨ b.val = (decomps[i.val]).t1 ∨ b.val = (decomps[i.val]).t2) ∧
        a.val ≠ b.val := by
  intro a b m hm0 hq
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp prodQ_in_Q_classified_aux a.val (List.mem_range.mpr a.isLt))
    b.val (List.mem_range.mpr b.isLt)
  dsimp only at h1
  have hq_nz : prodQ a.val b.val ≠ 0 := by
    rw [hq]; exact asconQuad_indep m hm0
  simp only [beq_false_of_ne hq_nz, Bool.false_eq_true, ↓reduceIte] at h1
  cases hfind : (List.range 31).find? (fun k => qOfMask (k + 1) == prodQ a.val b.val) with
  | none =>
    have hnone := List.find?_eq_none.mp hfind (m.val - 1) (List.mem_range.mpr (by omega))
    have he1 : m.val - 1 + 1 = m.val := by omega
    rw [he1] at hnone
    exact absurd (beq_iff_eq.mpr hq.symm) hnone
  | some k =>
    rw [hfind] at h1
    have hk_mem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
    have hk_eq := by simpa using List.find?_some hfind
    have hkm : k + 1 = m.val := by
      apply Classical.byContradiction; intro hne
      have hnz : (k + 1) ^^^ m.val ≠ 0 := fun hz => hne (by have h := congrArg (· ^^^ m.val) hz; simpa [Nat.xor_assoc, Nat.xor_self] using h)
      have hlt : (k + 1) ^^^ m.val < 32 := xor_lt_32 (by omega) m.isLt
      have h0 := asconQuad_indep ⟨_, hlt⟩ hnz
      rw [qOfMask_xor, hk_eq, hq, Nat.xor_self] at h0
      exact h0 rfl
    rw [List.any_eq_true] at h1
    obtain ⟨i, _, hi⟩ := h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, hkm, or_assoc] at hi
    exact ⟨i, hi.1.1.1, hi.1.1.2, hi.1.2, hi.2⟩

private def shiftOf (a b c : Nat) : Nat :=
  (a &&& b) ^^^ (if c.testBit 0 then a else 0) ^^^ (if c.testBit 1 then b else 0)

/-- No Ascon output polynomial equals any nonlinear gate `(a & b) ^ ca*a ^ cb*b | (prodQ a b <<< 5)`! -/
private theorem no_free_output_aux :
    (List.finRange 5).all (fun j =>
      (List.finRange 10).all (fun i =>
        let d := decomps[i.val]
        if d.quad != asconQuad j then true
        else
          let ts := [d.t0, d.t1, d.t2]
          ts.all fun a => ts.all fun b =>
            (List.range 4).all fun c =>
              shiftOf a b c != asconLin j)) = true := by
  decide +kernel

private theorem no_free_output :
    ∀ a : Fin 32, ∀ b : Fin 32, ∀ ca cb : Bool, ∀ j : Fin 5,
      ((prodPoly a.val b.val ^^^ (if ca then a.val else 0)) ^^^ (if cb then b.val else 0)) ≠ asconPoly j := by
  intro a b ca cb j heq
  have hq : prodQ a.val b.val = asconQuad j := by
    have := congrArg (fun x => x >>> 5) heq
    rw [prodPoly_quad a.isLt b.isLt ca cb] at this
    have hjq : asconPoly j >>> 5 = asconQuad j := asconPoly_quad j
    exact this.trans hjq
  have hm_eq : qOfMask (1 <<< j.val) = asconQuad j := qOfMask_bit j
  have hm_lt : 1 <<< j.val < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) j.isLt
  have hm_nz : 1 <<< j.val ≠ 0 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.ne_of_gt (Nat.two_pow_pos _)
  obtain ⟨i, hmask, ha, hb, _⟩ := prodQ_in_Q_classified a b ⟨1 <<< j.val, hm_lt⟩ hm_nz (hq.trans hm_eq.symm)
  have hdq : (decomps[i.val]).quad = asconQuad j := by
    rw [← decomp_quad_eq i, hmask, hm_eq]
  have haux := List.all_eq_true.mp (List.all_eq_true.mp no_free_output_aux j (List.mem_finRange j)) i (List.mem_finRange i)
  simp only [hdq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at haux
  have ha_mem : a.val ∈ [(decomps[i.val]).t0, (decomps[i.val]).t1, (decomps[i.val]).t2] := by
    simp [ha]
  have hb_mem : b.val ∈ [(decomps[i.val]).t0, (decomps[i.val]).t1, (decomps[i.val]).t2] := by
    simp [hb]
  let c : Nat := (if ca then 1 else 0) + (if cb then 2 else 0)
  have hc4 : c < 4 := by cases ca <;> cases cb <;> decide
  have hne := bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp haux a.val ha_mem) b.val hb_mem) c (List.mem_range.mpr hc4))
  apply hne
  have hlin : ((prodPoly a.val b.val ^^^ (if ca then a.val else 0)) ^^^ (if cb then b.val else 0)) &&& 31 = asconLin j := by
    have := congrArg (fun x => x &&& 31) heq
    have hjl : asconPoly j &&& 31 = asconLin j := asconPoly_lin j
    exact this.trans hjl
  rw [← hlin]
  apply Nat.eq_of_testBit_eq; intro bit
  unfold shiftOf prodPoly
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hc0 : c.testBit 0 = ca := by cases ca <;> cases cb <;> decide
  have hc1 : c.testBit 1 = cb := by cases ca <;> cases cb <;> decide
  rw [hc0, hc1]
  by_cases h5 : bit < 5
  · have h31 : (31 : Nat).testBit bit = true := by
      have : (31 : Nat) = 2 ^ 5 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
    have hge : ¬ (5 ≤ bit) := by omega
    simp [h31, hge]
  · have h31 : (31 : Nat).testBit bit = false := by
      have : (31 : Nat) = 2 ^ 5 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h5
    have ha0 : a.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show a.val < 2 ^ 5 from a.isLt) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
    have hb0 : b.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show b.val < 2 ^ 5 from b.isLt) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
    cases ca <;> cases cb <;> simp [h31, ha0, hb0]

/-! ## 5. Kernel-verified refutation of all 121 bases × 243 factor-pair choices -/

private def pop5 (x : Nat) : Nat :=
  (if x.testBit 0 then 1 else 0) + (if x.testBit 1 then 1 else 0) +
  (if x.testBit 2 then 1 else 0) + (if x.testBit 3 then 1 else 0) +
  (if x.testBit 4 then 1 else 0)

private def maskSubset (ms : Fin 5 → Nat) (s : Nat) : Nat :=
  (if s.testBit 0 then ms ⟨0, by decide⟩ else 0) ^^^
  (if s.testBit 1 then ms ⟨1, by decide⟩ else 0) ^^^
  (if s.testBit 2 then ms ⟨2, by decide⟩ else 0) ^^^
  (if s.testBit 3 then ms ⟨3, by decide⟩ else 0) ^^^
  (if s.testBit 4 then ms ⟨4, by decide⟩ else 0)

private theorem maskSubset_xor (ms : Fin 5 → Nat) (s1 s2 : Nat) :
    maskSubset ms (s1 ^^^ s2) = maskSubset ms s1 ^^^ maskSubset ms s2 := by
  have h1 : ∀ (c1 c2 : Bool) (v : Nat),
      (if xor c1 c2 then v else 0) = (if c1 then v else 0) ^^^ (if c2 then v else 0) := by
    intro c1 c2 v; cases c1 <;> cases c2 <;> simp
  unfold maskSubset
  simp only [Nat.testBit_xor, h1]
  apply Eq.symm
  rw [nat_xor_swap]; congr 1
  rw [nat_xor_swap]; congr 1
  rw [nat_xor_swap]; congr 1
  exact nat_xor_swap _ _ _ _

private theorem maskSubset_bit (ms : Fin 5 → Nat) (k : Fin 5) :
    maskSubset ms (1 <<< k.val) = ms k := by
  rcases k with ⟨k, hk⟩
  match k, hk with
  | 0, _ => simp [maskSubset, show (1 : Nat).testBit 0 = true by decide, show (1 : Nat).testBit 1 = false by decide, show (1 : Nat).testBit 2 = false by decide, show (1 : Nat).testBit 3 = false by decide, show (1 : Nat).testBit 4 = false by decide]
  | 1, _ => simp [maskSubset, show (2 : Nat).testBit 0 = false by decide, show (2 : Nat).testBit 1 = true by decide, show (2 : Nat).testBit 2 = false by decide, show (2 : Nat).testBit 3 = false by decide, show (2 : Nat).testBit 4 = false by decide]
  | 2, _ => simp [maskSubset, show (4 : Nat).testBit 0 = false by decide, show (4 : Nat).testBit 1 = false by decide, show (4 : Nat).testBit 2 = true by decide, show (4 : Nat).testBit 3 = false by decide, show (4 : Nat).testBit 4 = false by decide]
  | 3, _ => simp [maskSubset, show (8 : Nat).testBit 0 = false by decide, show (8 : Nat).testBit 1 = false by decide, show (8 : Nat).testBit 2 = false by decide, show (8 : Nat).testBit 3 = true by decide, show (8 : Nat).testBit 4 = false by decide]
  | 4, _ => simp [maskSubset, show (16 : Nat).testBit 0 = false by decide, show (16 : Nat).testBit 1 = false by decide, show (16 : Nat).testBit 2 = false by decide, show (16 : Nat).testBit 3 = false by decide, show (16 : Nat).testBit 4 = true by decide]

private def isBasis5 (m0 m1 m2 m3 m4 : Nat) : Bool :=
  let ms : Fin 5 → Nat
    | ⟨0, _⟩ => m0 | ⟨1, _⟩ => m1 | ⟨2, _⟩ => m2 | ⟨3, _⟩ => m3 | ⟨4, _⟩ => m4
  (List.range 31).all fun k => maskSubset ms (k + 1) != 0

private def findInvRow (m0 m1 m2 m3 m4 target : Nat) : Nat :=
  let ms : Fin 5 → Nat
    | ⟨0, _⟩ => m0 | ⟨1, _⟩ => m1 | ⟨2, _⟩ => m2 | ⟨3, _⟩ => m3 | ⟨4, _⟩ => m4
  match (List.range 32).find? (fun s => maskSubset ms s == target) with
  | some s => s
  | none => 0

private def pairOfSkip (d : Decomp) (skip : Nat) : Nat × Nat :=
  match skip with
  | 0 => (d.t1, d.t2)
  | 1 => (d.t0, d.t2)
  | _ => (d.t0, d.t1)

/-- Depth-0 forward XOR closure starting from `{0, x0..x4}` over a target mask `tmask`. -/
private def d0Step (tmask av : Nat) : Nat :=
  (List.range 32).foldl (fun acc t =>
    if tmask.testBit t && !(av.testBit t) then
      let ok := (List.range 32).any (fun a => av.testBit a && av.testBit (t ^^^ a))
      if ok then acc ||| (1 <<< t) else acc
    else acc) av

private def baseBm : Nat :=
  1 ||| (1 <<< 1) ||| (1 <<< 2) ||| (1 <<< 4) ||| (1 <<< 8) ||| (1 <<< 16)

private def d0ClosureOk (tmask : Nat) : Bool :=
  let av4 := d0Step tmask (d0Step tmask (d0Step tmask (d0Step tmask baseBm)))
  (av4 &&& tmask) == tmask

/-- 1-var domain refutation for zero-helper configurations: returns `true` iff NO `(c0..c4)`
    allows every output `y_j` to be written as `u ^^^ v` with `u, v ∈ bm0 ∪ {g0..g4} ∪ {y_{j'} | j' ≠ j}`. -/
private def zeroHelperRefuted (inv : Fin 5 → Nat) (A B : Fin 5 → Nat) (bm0 : Nat) : Bool :=
  let dom0 : Array Nat := #[15, 15, 15, 15, 15]
  let res := (List.finRange 5).foldl (fun (st : Bool × Array Nat) j =>
    if st.1 then st
    else
      let dom := st.2
      let yq := inv j
      let yl := asconLin j
      let constOk := (List.finRange 5).any fun j1 =>
        j1 != j && (List.finRange 5).any fun j2 =>
          j2 != j && j1.val < j2.val && (inv j1 ^^^ inv j2 == yq) && (asconLin j1 ^^^ asconLin j2 == yl)
      if constOk then (false, dom)
      else
        let has2 := (List.finRange 5).any fun ka =>
          (List.finRange 5).any fun kb =>
            ka.val < kb.val && (yq == ((1 <<< ka.val) ||| (1 <<< kb.val))) &&
            (List.range 4).any fun ca => (List.range 4).any fun cb =>
              (shiftOf (A ka) (B ka) ca ^^^ shiftOf (A kb) (B kb) cb) == yl
        if has2 then (false, dom)
        else
          -- Only single-gate equations can satisfy output j
          let (sk, mk) := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
            let mask := (List.range 4).foldl (fun m c =>
              let sh := shiftOf (A k) (B k) c
              let ok1 := (yq == (1 <<< k.val)) && bm0.testBit (yl ^^^ sh)
              let ok2 := (List.finRange 5).any fun j2 =>
                j2 != j && ((yq ^^^ inv j2) == (1 <<< k.val)) && ((yl ^^^ asconLin j2) == sh)
              if ok1 || ok2 then m ||| (1 <<< c) else m) 0
            if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask)
            else acc) (0, #[0, 0, 0, 0, 0])
          if sk == 0 then (true, dom)
          else if pop5 sk == 1 then
            let k := if sk == 1 then 0 else if sk == 2 then 1 else if sk == 4 then 2 else if sk == 8 then 3 else 4
            let nd := (dom.getD k 0) &&& (mk.getD k 0)
            if nd == 0 then (true, dom)
            else (false, dom.set! k nd)
          else (false, dom)
  ) (false, dom0)
  res.1

private def inXors (s : List Nat) (t : Nat) : Bool :=
  s.any fun a => s.any fun b => a != b && (a ^^^ b == t)

/-- Refutation of a `|pre| = 3` configuration with 1 quadratic helper `h`:
    checks that `inv` has the block-disjoint pattern `(1, {2,6}, {2,4,6}, 24, 9)` and that
    no `(c0, c3, c4) ∈ {0..3}^3` allows reaching both `y3` and `y4` from `bm0 ∪ {g0, g3, g4, y0}`
    with at most 1 helper `h = u ^^^ v`. -/
private def pop8 (x : Nat) : Nat :=
  let x := x - ((x >>> 1) &&& 0x55)
  let x := (x &&& 0x33) + ((x >>> 2) &&& 0x33)
  (x + (x >>> 4)) &&& 0x0f

private def pop32Byte (x : Nat) : Nat :=
  pop8 (x &&& 255) + pop8 ((x >>> 8) &&& 255) + pop8 ((x >>> 16) &&& 255) + pop8 ((x >>> 24) &&& 255)

private def preMaskOf (A B : Fin 5 → Nat) : Nat :=
  (List.finRange 5).foldl (fun m k =>
    let m1 := if pop5 (A k) > 1 then m ||| (1 <<< A k) else m
    if pop5 (B k) > 1 then m1 ||| (1 <<< B k) else m1) 0

private def pairMask (a b : Nat) : Nat :=
  (if pop5 a > 1 then 1 <<< a else 0) ||| (if pop5 b > 1 then 1 <<< b else 0)

private def pop32 (m : Nat) : Nat :=
  (List.range 32).foldl (fun acc i => if m.testBit i then acc + 1 else acc) 0

private theorem pop8_eq_fold : ∀ n : Fin 256,
    pop8 n.val = (List.range 8).foldl (fun acc i => if n.val.testBit i then acc + 1 else acc) 0 := by
  decide +kernel

private theorem pop32Byte_eq_pop32 (m : Nat) : pop32Byte m = pop32 m := by
  have hfold_shift : ∀ (k off : Nat) (acc : Nat),
      (List.range k).foldl (fun a i => if m.testBit (off + i) then a + 1 else a) acc =
      acc + (List.range k).foldl (fun a i => if ((m >>> off) &&& 255).testBit i then a + 1 else a) 0 ∨ k > 8 := by
    intro k off acc
    by_cases hk : k ≤ 8
    · left
      have hgen : ∀ (n : Nat), n ≤ 8 → ∀ acc,
          (List.range n).foldl (fun a i => if m.testBit (off + i) then a + 1 else a) acc =
          acc + (List.range n).foldl (fun a i => if ((m >>> off) &&& 255).testBit i then a + 1 else a) 0 := by
        intro n; induction n with
        | zero => intro _ acc; simp
        | succ n ih =>
          intro hn acc
          rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
          rw [ih (by omega) acc]
          have hbit : ((m >>> off) &&& 255).testBit n = m.testBit (off + n) := by
            rw [Nat.testBit_and, Nat.testBit_shiftRight]
            have h255 : (255 : Nat).testBit n = true := by
              have : (255 : Nat) = 2 ^ 8 - 1 := rfl
              rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
            rw [h255, Bool.and_true]
          rw [hbit]; cases m.testBit (off + n) <;> simp <;> omega
      exact hgen k hk acc
    · exact Or.inr (by omega)
  have hbyte : ∀ off, pop8 ((m >>> off) &&& 255) =
      (List.range 8).foldl (fun a i => if m.testBit (off + i) then a + 1 else a) 0 := by
    intro off
    have hlt : (m >>> off) &&& 255 < 256 := Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8)
    have h1 := pop8_eq_fold ⟨_, hlt⟩
    rcases hfold_shift 8 off 0 with h2 | hbad
    · simp only [Nat.zero_add] at h2; exact h1.trans h2.symm
    · omega
  have hsplit : ∀ (off off2 a b : Nat) (hoff : off2 = off + a) (acc : Nat),
      (List.range (a + b)).foldl (fun x i => if m.testBit (off + i) then x + 1 else x) acc =
      (List.range b).foldl (fun x i => if m.testBit (off2 + i) then x + 1 else x)
        ((List.range a).foldl (fun x i => if m.testBit (off + i) then x + 1 else x) acc) := by
    intro off off2 a b hoff
    induction b with
    | zero => intro acc; simp
    | succ b ih =>
      intro acc
      rw [show a + (b + 1) = (a + b) + 1 by omega, List.range_succ, List.range_succ,
          List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil,
          ih acc, show off + (a + b) = off2 + b by omega]
  have hacc : ∀ (k off acc : Nat),
      (List.range k).foldl (fun x i => if m.testBit (off + i) then x + 1 else x) acc =
      acc + (List.range k).foldl (fun x i => if m.testBit (off + i) then x + 1 else x) 0 := by
    intro k off; induction k with
    | zero => intro acc; simp
    | succ k ih =>
      intro acc
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil, ih acc, ih 0, Nat.zero_add]
      cases m.testBit (off + k) <;> simp <;> omega
  unfold pop32Byte pop32
  have h0 : pop8 (m &&& 255) = pop8 ((m >>> 0) &&& 255) := by simp
  rw [h0, hbyte 0, hbyte 8, hbyte 16, hbyte 24]
  have h32 : (List.range 32).foldl (fun x i => if m.testBit i then x + 1 else x) 0 =
      (List.range 32).foldl (fun x i => if m.testBit (0 + i) then x + 1 else x) 0 := by
    simp only [Nat.zero_add]
  have hr32 : List.range 32 = List.range (8 + 24) := rfl
  have hr24 : List.range 24 = List.range (8 + 16) := rfl
  have hr16 : List.range 16 = List.range (8 + 8) := rfl
  rw [h32, hr32, hsplit 0 8 8 24 rfl 0, hacc 24 8]
  rw [hr24, hsplit 8 16 8 16 rfl 0, hacc 16 16]
  rw [hr16, hsplit 16 24 8 8 rfl 0, hacc 8 24 ((List.range 8).foldl (fun x i => if m.testBit (16 + i) then x + 1 else x) 0)]
  simp only [Nat.add_assoc]

private theorem preMaskOf_eq_or (A B : Fin 5 → Nat) :
    preMaskOf A B =
      pairMask (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) |||
      pairMask (A ⟨1, by decide⟩) (B ⟨1, by decide⟩) |||
      pairMask (A ⟨2, by decide⟩) (B ⟨2, by decide⟩) |||
      pairMask (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) |||
      pairMask (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) := by
  have hstep : ∀ (m a b : Nat),
      (let m1 := if pop5 a > 1 then m ||| (1 <<< a) else m
       if pop5 b > 1 then m1 ||| (1 <<< b) else m1) = m ||| pairMask a b := by
    intro m a b; unfold pairMask
    by_cases ha : pop5 a > 1 <;> by_cases hb : pop5 b > 1 <;> simp [ha, hb, Nat.or_assoc]
  unfold preMaskOf
  have hfr : List.finRange 5 = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩] := by decide
  rw [hfr]
  simp only [List.foldl_cons, List.foldl_nil, hstep, Nat.zero_or]

private def bitSet (m i : Nat) : Bool := ((m >>> i) &&& 1) != 0

private theorem bitSet_eq_testBit (m i : Nat) : bitSet m i = m.testBit i := by
  unfold bitSet Nat.testBit; rw [Nat.and_comm]

private def inXorsAvO1 (g0 g3 g4 y0 bm0 h : Nat) : Bool :=
  let q := h >>> 5
  let l := h &&& 31
  if q == 0 then
    (l != 0 && (g0 ^^^ y0 == l)) ||
    (List.range 32).any (fun b => bitSet bm0 b && b != (l ^^^ b) && bitSet bm0 (l ^^^ b))
  else if q == 1 then bitSet bm0 ((g0 &&& 31) ^^^ l) || bitSet bm0 ((y0 &&& 31) ^^^ l)
  else if q == 8 then bitSet bm0 ((g3 &&& 31) ^^^ l)
  else if q == 16 then bitSet bm0 ((g4 &&& 31) ^^^ l)
  else if q == 9 then (g0 ^^^ g3 == h) || (y0 ^^^ g3 == h)
  else if q == 17 then (g0 ^^^ g4 == h) || (y0 ^^^ g4 == h)
  else if q == 24 then g3 ^^^ g4 == h
  else false

private def p3QuadHelperRefutedO1 (i0 i1 i2 i3 i4 a0 b0 a3 b3 a4 b4 bm0 : Nat) : Bool :=
  let invOk := i0 == 1 && (i1 == 2 || i1 == 6) && (i2 == 2 || i2 == 4 || i2 == 6) && i3 == 24 && i4 == 9
  if !invOk then false
  else
    let bmList := (List.range 32).filter (fun a => bm0.testBit a)
    let y0 := (1 <<< 5) ||| 11
    let y3 := (24 <<< 5) ||| 31
    let y4 := (9 <<< 5) ||| 30
    ([0,1,2,3]).all fun c0 =>
      let g0 := (1 <<< 5) ||| shiftOf a0 b0 c0
      ([0,1,2,3]).all fun c3 =>
        let g3 := (8 <<< 5) ||| shiftOf a3 b3 c3
        if g0 ^^^ g3 == y4 || y0 ^^^ g3 == y4 then false
        else
        ([0,1,2,3]).all fun c4 =>
          let g4 := (16 <<< 5) ||| shiftOf a4 b4 c4
          if g3 ^^^ g4 == y3 then false
          else
            let av := g0 :: g3 :: g4 :: y0 :: bmList
            let ok3 := av.all fun w1 =>
              let h := y3 ^^^ w1
              if av.any (fun w2 => (h ^^^ w2 == y4) || (y3 ^^^ w2 == y4)) then
                !inXorsAvO1 g0 g3 g4 y0 bm0 h
              else true
            let ok4 := av.all fun w1 =>
              let h := y4 ^^^ w1
              if av.any (fun w2 => (h ^^^ w2 == y3) || (y4 ^^^ w2 == y3)) then
                !inXorsAvO1 g0 g3 g4 y0 bm0 h
              else true
            ok3 && ok4

set_option maxRecDepth 200000 in
private def allBases5 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 10).flatMap fun i0 =>
  (List.range 10).flatMap fun i1 =>
  if i1 ≤ i0 then [] else
  (List.range 10).flatMap fun i2 =>
  if i2 ≤ i1 then [] else
  (List.range 10).flatMap fun i3 =>
  if i3 ≤ i2 then [] else
  (List.range 10).filterMap fun i4 =>
  if i4 ≤ i3 then none
  else
    let d0 := decomps[i0]!; let d1 := decomps[i1]!; let d2 := decomps[i2]!
    let d3 := decomps[i3]!; let d4 := decomps[i4]!
    if isBasis5 d0.mask d1.mask d2.mask d3.mask d4.mask then some (i0, i1, i2, i3, i4) else none

/-- For every decomposable form, all 3 factor pairs produce the exact same 4-element shift coset. -/
private theorem shift_coset_eq :
    ∀ (i : Fin 10) (s : Fin 3) (c : Fin 4),
      ∃ c' : Fin 4,
        shiftOf (pairOfSkip (decomps[i.val]) s.val).1 (pairOfSkip (decomps[i.val]) s.val).2 c.val =
        shiftOf (decomps[i.val]).t0 (decomps[i.val]).t1 c'.val := by
  decide +kernel

/-- 1. All 120 non-diagonal bases are refuted for ALL zero-helper and linear-helper circuits
    (even with all 32 linear masks available!). -/
private theorem cert_zero_helper :
    allBases5.all (fun b =>
      if b == (0, 1, 2, 5, 6) then true
      else
        let d0 := decomps[b.1]!; let d1 := decomps[b.2.1]!; let d2 := decomps[b.2.2.1]!
        let d3 := decomps[b.2.2.2.1]!; let d4 := decomps[b.2.2.2.2]!
        let i0 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 1
        let i1 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 2
        let i2 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 4
        let i3 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 8
        let i4 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 16
        let inv : Fin 5 → Nat | ⟨0,_⟩ => i0 | ⟨1,_⟩ => i1 | ⟨2,_⟩ => i2 | ⟨3,_⟩ => i3 | ⟨4,_⟩ => i4
        let A : Fin 5 → Nat | ⟨0,_⟩ => d0.t0 | ⟨1,_⟩ => d1.t0 | ⟨2,_⟩ => d2.t0 | ⟨3,_⟩ => d3.t0 | ⟨4,_⟩ => d4.t0
        let B : Fin 5 → Nat | ⟨0,_⟩ => d0.t1 | ⟨1,_⟩ => d1.t1 | ⟨2,_⟩ => d2.t1 | ⟨3,_⟩ => d3.t1 | ⟨4,_⟩ => d4.t1
        zeroHelperRefuted inv A B 4294967295) = true := by
  decide +kernel

/-- 2. The unique diagonal basis `(0, 1, 2, 5, 6)` always requires ≥ 5 depth-0 linear pre-masks. -/
private theorem cert_diag_np5 :
    let d0 := decomps[0]!; let d1 := decomps[1]!; let d2 := decomps[2]!
    let d3 := decomps[5]!; let d4 := decomps[6]!
    ([0,1,2]).all (fun s0 =>
      let p0 := pairOfSkip d0 s0; let pm0 := pairMask p0.1 p0.2
      ([0,1,2]).all (fun s1 =>
        let p1 := pairOfSkip d1 s1; let pm1 := pm0 ||| pairMask p1.1 p1.2
        ([0,1,2]).all (fun s2 =>
          let p2 := pairOfSkip d2 s2; let pm2 := pm1 ||| pairMask p2.1 p2.2
          ([0,1,2]).all (fun s3 =>
            let p3 := pairOfSkip d3 s3; let pm3 := pm2 ||| pairMask p3.1 p3.2
            ([0,1,2]).all (fun s4 =>
              let p4 := pairOfSkip d4 s4; let pm := pm3 ||| pairMask p4.1 p4.2
              pop32Byte pm ≥ 5))))) = true := by
  decide +kernel

/-- 3. Across all 121 bases × 243 factor-pair choices, whenever `pop32 pm ≤ 3`, we have `pop32 pm = 3`
    and if `d0ClosureOk pm = true` then `p3QuadHelperRefutedO1` holds! -/
private theorem cert_p3_quad :
    allBases5.all (fun b =>
      let d0 := decomps[b.1]!; let d1 := decomps[b.2.1]!; let d2 := decomps[b.2.2.1]!
      let d3 := decomps[b.2.2.2.1]!; let d4 := decomps[b.2.2.2.2]!
      ([0,1,2]).all fun s0 =>
        let p0 := pairOfSkip d0 s0; let pm0 := pairMask p0.1 p0.2
        ([0,1,2]).all fun s1 =>
          let p1 := pairOfSkip d1 s1; let pm1 := pm0 ||| pairMask p1.1 p1.2
          if pop32Byte pm1 > 3 then true else
          ([0,1,2]).all fun s2 =>
            let p2 := pairOfSkip d2 s2; let pm2 := pm1 ||| pairMask p2.1 p2.2
            if pop32Byte pm2 > 3 then true else
            ([0,1,2]).all fun s3 =>
              let p3 := pairOfSkip d3 s3; let pm3 := pm2 ||| pairMask p3.1 p3.2
              if pop32Byte pm3 > 3 then true else
              ([0,1,2]).all fun s4 =>
                let p4 := pairOfSkip d4 s4; let pm := pm3 ||| pairMask p4.1 p4.2
                if pop32Byte pm > 3 then true
                else if pop32Byte pm < 3 then false
                else if !d0ClosureOk pm then true
                else
                  let i0 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 1
                  let i1 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 2
                  let i2 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 4
                  let i3 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 8
                  let i4 := findInvRow d0.mask d1.mask d2.mask d3.mask d4.mask 16
                  p3QuadHelperRefutedO1 i0 i1 i2 i3 i4 p0.1 p0.2 p3.1 p3.2 p4.1 p4.2 (baseBm ||| pm)) = true := by
  decide +kernel

private theorem pop32_mono_or (a b : Nat) : pop32 a ≤ pop32 (a ||| b) := by
  unfold pop32
  suffices ∀ (xs : List Nat) (n1 n2 : Nat), n1 ≤ n2 →
      xs.foldl (fun acc i => if a.testBit i then acc + 1 else acc) n1 ≤
      xs.foldl (fun acc i => if (a ||| b).testBit i then acc + 1 else acc) n2 from this _ 0 0 (Nat.le_refl _)
  intro xs; induction xs with
  | nil => intro n1 n2 h; exact h
  | cons x xs ih =>
    intro n1 n2 h; rw [List.foldl_cons, List.foldl_cons, Nat.testBit_or]
    apply ih; cases a.testBit x <;> cases b.testBit x <;> simp <;> omega

private theorem inXorsAvO1_of_pair {l0 l3 l4 bm0 u v : Nat}
    (hl0 : l0 < 32) (hl3 : l3 < 32) (hl4 : l4 < 32)
    (hbm32 : ∀ x, bm0.testBit x = true → x < 32) :
    let g0 := (1 <<< 5) ||| l0
    let g3 := (8 <<< 5) ||| l3
    let g4 := (16 <<< 5) ||| l4
    let y0 := (1 <<< 5) ||| 11
    let bmList := (List.range 32).filter (fun a => bm0.testBit a)
    let av := g0 :: g3 :: g4 :: y0 :: bmList
    u ∈ av → v ∈ av → u ≠ v → inXorsAvO1 g0 g3 g4 y0 bm0 (u ^^^ v) = true := by
  intro g0 g3 g4 y0 bmList av hu hv hne
  have hparts : ∀ q l, l < 32 → (((q <<< 5) ||| l) >>> 5 = q ∧ ((q <<< 5) ||| l) &&& 31 = l) := by
    intro q l hl
    refine ⟨?_, ?_⟩
    · apply Nat.eq_of_testBit_eq; intro bit
      rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
      have h0 : l.testBit (5 + bit) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show l < 2 ^ 5 from hl) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
      simp [h0]
    · apply Nat.eq_of_testBit_eq; intro bit
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases h5 : bit < 5
      · have h31 : (31 : Nat).testBit bit = true := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
        have hge : ¬ (5 ≤ bit) := by omega
        simp [h31, hge]
      · have h31 : (31 : Nat).testBit bit = false := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h5
        have h0 : l.testBit bit = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show l < 2 ^ 5 from hl) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
        simp [h31, h0]
  have hlt32_p : ∀ x, x < 32 → x >>> 5 = 0 ∧ x &&& 31 = x := by
    intro x hx; have := hparts 0 x hx; simpa using this
  have hx_and : ∀ a b, (a ^^^ b) &&& 31 = (a &&& 31) ^^^ (b &&& 31) := by
    intro a b; apply Nat.eq_of_testBit_eq; intro bit; simp only [Nat.testBit_and, Nat.testBit_xor]
    cases a.testBit bit <;> cases b.testBit bit <;> cases (31 : Nat).testBit bit <;> rfl
  have hg0p := hparts 1 l0 hl0
  have hg3p := hparts 8 l3 hl3
  have hg4p := hparts 16 l4 hl4
  have hy0p := hparts 1 11 (by decide)
  have hg0l : g0 &&& 31 = l0 := hg0p.2
  have hg3l : g3 &&& 31 = l3 := hg3p.2
  have hg4l : g4 &&& 31 = l4 := hg4p.2
  have hy0l : y0 &&& 31 = 11 := hy0p.2
  have hneq0 : ∀ a b, a ≠ b → a ^^^ b ≠ 0 := fun a b h hz => h (by have h' := congrArg (· ^^^ b) hz; simpa [Nat.xor_assoc, Nat.xor_self] using h')
  have hsym : ∀ a b, inXorsAvO1 g0 g3 g4 y0 bm0 (a ^^^ b) = inXorsAvO1 g0 g3 g4 y0 bm0 (b ^^^ a) := by
    intro a b; rw [Nat.xor_comm]
  simp only [av, List.mem_cons] at hu hv
  -- Helper for (q <<< 5 | l) ^ b where b ∈ bmList
  have hq1 : ∀ (l b : Nat), l < 32 → (l = l0 ∨ l = 11) → b ∈ bmList →
      inXorsAvO1 g0 g3 g4 y0 bm0 (((1 <<< 5) ||| l) ^^^ b) = true := by
    intro l b hl hlor hb
    have hb32 : b < 32 := List.mem_range.mp (List.mem_filter.mp hb).1
    have hbb : bm0.testBit b = true := (List.mem_filter.mp hb).2
    have hq : (((1 <<< 5) ||| l) ^^^ b) >>> 5 = 1 := by
      rw [Nat.shiftRight_xor_distrib, (hparts 1 l hl).1, (hlt32_p b hb32).1]; rfl
    have hl' : (((1 <<< 5) ||| l) ^^^ b) &&& 31 = l ^^^ b := by
      rw [hx_and, (hparts 1 l hl).2, (hlt32_p b hb32).2]
    unfold inXorsAvO1; simp only [hq, hl', bitSet_eq_testBit, hg0l, hy0l]
    rcases hlor with hl_eq | hl_eq
    · subst hl_eq; simp [← Nat.xor_assoc, Nat.xor_self, hbb]
    · subst hl_eq; simp [← Nat.xor_assoc, Nat.xor_self, hbb]
  rcases hu with rfl | rfl | rfl | rfl | hub <;> rcases hv with rfl | rfl | rfl | rfl | hvb
  · exact absurd rfl hne
  · -- g0 ^ g3: q = 9
    have hq : (g0 ^^^ g3) >>> 5 = 9 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hg3p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · -- g0 ^ g4: q = 17
    have hq : (g0 ^^^ g4) >>> 5 = 17 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · -- g0 ^ y0: q = 0
    have hq : (g0 ^^^ y0) >>> 5 = 0 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hy0p.1]; rfl
    have hgy_lt : g0 ^^^ y0 < 32 := by
      have : (g0 ^^^ y0) >>> 5 = 0 := hq
      omega
    have hl' : (g0 ^^^ y0) &&& 31 = g0 ^^^ y0 := (hlt32_p _ hgy_lt).2
    unfold inXorsAvO1; simp [hq, hl', hneq0 _ _ hne]
  · exact hq1 l0 _ hl0 (Or.inl rfl) hvb
  · rw [hsym]; have hq : (g0 ^^^ g3) >>> 5 = 9 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hg3p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · exact absurd rfl hne
  · -- g3 ^ g4: q = 24
    have hq : (g3 ^^^ g4) >>> 5 = 24 := by rw [Nat.shiftRight_xor_distrib, hg3p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · -- g3 ^ y0: q = 9
    rw [hsym]; have hq : (y0 ^^^ g3) >>> 5 = 9 := by rw [Nat.shiftRight_xor_distrib, hy0p.1, hg3p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · -- g3 ^ b: q = 8
    have hb32 : v < 32 := List.mem_range.mp (List.mem_filter.mp hvb).1
    have hbb : bm0.testBit v = true := (List.mem_filter.mp hvb).2
    have hq : (g3 ^^^ v) >>> 5 = 8 := by rw [Nat.shiftRight_xor_distrib, hg3p.1, (hlt32_p v hb32).1]; rfl
    have hl' : (g3 ^^^ v) &&& 31 = l3 ^^^ v := by rw [hx_and, hg3p.2, (hlt32_p v hb32).2]
    unfold inXorsAvO1; simp [hq, hl', bitSet_eq_testBit, hg3l, ← Nat.xor_assoc, Nat.xor_self, hbb]
  · rw [hsym]; have hq : (g0 ^^^ g4) >>> 5 = 17 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · rw [hsym]; have hq : (g3 ^^^ g4) >>> 5 = 24 := by rw [Nat.shiftRight_xor_distrib, hg3p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · exact absurd rfl hne
  · rw [hsym]; have hq : (y0 ^^^ g4) >>> 5 = 17 := by rw [Nat.shiftRight_xor_distrib, hy0p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · -- g4 ^ b: q = 16
    have hb32 : v < 32 := List.mem_range.mp (List.mem_filter.mp hvb).1
    have hbb : bm0.testBit v = true := (List.mem_filter.mp hvb).2
    have hq : (g4 ^^^ v) >>> 5 = 16 := by rw [Nat.shiftRight_xor_distrib, hg4p.1, (hlt32_p v hb32).1]; rfl
    have hl' : (g4 ^^^ v) &&& 31 = l4 ^^^ v := by rw [hx_and, hg4p.2, (hlt32_p v hb32).2]
    unfold inXorsAvO1; simp [hq, hl', bitSet_eq_testBit, hg4l, ← Nat.xor_assoc, Nat.xor_self, hbb]
  · rw [hsym]
    have hq : (g0 ^^^ y0) >>> 5 = 0 := by rw [Nat.shiftRight_xor_distrib, hg0p.1, hy0p.1]; rfl
    have hgy_lt : g0 ^^^ y0 < 32 := by
      have : (g0 ^^^ y0) >>> 5 = 0 := hq
      omega
    have hl' : (g0 ^^^ y0) &&& 31 = g0 ^^^ y0 := (hlt32_p _ hgy_lt).2
    unfold inXorsAvO1; simp [hq, hl', hneq0 _ _ hne.symm]
  · have hq : (y0 ^^^ g3) >>> 5 = 9 := by rw [Nat.shiftRight_xor_distrib, hy0p.1, hg3p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · have hq : (y0 ^^^ g4) >>> 5 = 17 := by rw [Nat.shiftRight_xor_distrib, hy0p.1, hg4p.1]; rfl
    unfold inXorsAvO1; simp [hq]
  · exact absurd rfl hne
  · exact hq1 11 _ (by decide) (Or.inr rfl) hvb
  · rw [hsym]; exact hq1 l0 _ hl0 (Or.inl rfl) hub
  · rw [hsym]
    have hb32 : u < 32 := List.mem_range.mp (List.mem_filter.mp hub).1
    have hbb : bm0.testBit u = true := (List.mem_filter.mp hub).2
    have hq : (g3 ^^^ u) >>> 5 = 8 := by rw [Nat.shiftRight_xor_distrib, hg3p.1, (hlt32_p u hb32).1]; rfl
    have hl' : (g3 ^^^ u) &&& 31 = l3 ^^^ u := by rw [hx_and, hg3p.2, (hlt32_p u hb32).2]
    unfold inXorsAvO1; simp [hq, hl', bitSet_eq_testBit, hg3l, ← Nat.xor_assoc, Nat.xor_self, hbb]
  · rw [hsym]
    have hb32 : u < 32 := List.mem_range.mp (List.mem_filter.mp hub).1
    have hbb : bm0.testBit u = true := (List.mem_filter.mp hub).2
    have hq : (g4 ^^^ u) >>> 5 = 16 := by rw [Nat.shiftRight_xor_distrib, hg4p.1, (hlt32_p u hb32).1]; rfl
    have hl' : (g4 ^^^ u) &&& 31 = l4 ^^^ u := by rw [hx_and, hg4p.2, (hlt32_p u hb32).2]
    unfold inXorsAvO1; simp [hq, hl', bitSet_eq_testBit, hg4l, ← Nat.xor_assoc, Nat.xor_self, hbb]
  · rw [hsym]; exact hq1 11 _ (by decide) (Or.inr rfl) hub
  · -- b1 ^ b2: q = 0
    have hu32 : u < 32 := List.mem_range.mp (List.mem_filter.mp hub).1
    have hv32 : v < 32 := List.mem_range.mp (List.mem_filter.mp hvb).1
    have hubb : bm0.testBit u = true := (List.mem_filter.mp hub).2
    have hvbb : bm0.testBit v = true := (List.mem_filter.mp hvb).2
    have huv32 : u ^^^ v < 32 := xor_lt_32 hu32 hv32
    have hq : (u ^^^ v) >>> 5 = 0 := (hlt32_p _ huv32).1
    have hl' : (u ^^^ v) &&& 31 = u ^^^ v := (hlt32_p _ huv32).2
    unfold inXorsAvO1; simp only [hq, hl', beq_self_eq_true, ↓reduceIte, Bool.or_eq_true]
    right; rw [List.any_eq_true]
    refine ⟨u, List.mem_range.mpr hu32, ?_⟩
    have huvu : (u ^^^ v) ^^^ u = v := by rw [Nat.xor_comm u v, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    simp [bitSet_eq_testBit, hubb, huvu, hne, hvbb]

/-! ## 6. Soundness of `d0ClosureOk`, `zeroHelperRefuted`, `p3QuadHelperRefuted` -/

private theorem d0Step_monotone (tmask av t : Nat) (h : av.testBit t = true) :
    (d0Step tmask av).testBit t = true := by
  unfold d0Step
  suffices ∀ (xs : List Nat) (acc : Nat), acc.testBit t = true →
      (xs.foldl (fun acc x =>
        if tmask.testBit x && !(av.testBit x) then
          let ok := (List.range 32).any (fun a => av.testBit a && av.testBit (x ^^^ a))
          if ok then acc ||| (1 <<< x) else acc
        else acc) acc).testBit t = true from this (List.range 32) av h
  intro xs
  induction xs with
  | nil => intro acc hacc; exact hacc
  | cons x xs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    split
    · split
      · simp [Nat.testBit_or, hacc]
      · exact hacc
    · exact hacc

private theorem d0Step_add (tmask av x a b : Nat) (hx : x < 32) (ht : tmask.testBit x = true)
    (ha : a < 32) (hav_a : av.testBit a = true) (hav_b : av.testBit b = true) (hab : a ^^^ b = x) :
    (d0Step tmask av).testBit x = true := by
  by_cases hax : av.testBit x = true
  · exact d0Step_monotone tmask av x hax
  · have haxf : av.testBit x = false := Bool.eq_false_iff.mpr hax
    have hmem : x ∈ List.range 32 := List.mem_range.mpr hx
    have hxa : x ^^^ a = b := by
      rw [← hab, Nat.xor_comm a b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have hok : (List.range 32).any (fun u => av.testBit u && av.testBit (x ^^^ u)) = true := by
      rw [List.any_eq_true]
      exact ⟨a, List.mem_range.mpr ha, by simp [hav_a, hxa, hav_b]⟩
    unfold d0Step
    suffices ∀ (xs : List Nat) (acc : Nat), x ∈ xs ∨ acc.testBit x = true →
        (xs.foldl (fun acc y =>
          if tmask.testBit y && !(av.testBit y) then
            let ok := (List.range 32).any (fun u => av.testBit u && av.testBit (y ^^^ u))
            if ok then acc ||| (1 <<< y) else acc
          else acc) acc).testBit x = true from this (List.range 32) av (Or.inl hmem)
    intro xs
    induction xs with
    | nil =>
      intro acc h
      rcases h with h | h
      · cases h
      · exact h
    | cons y ys ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rcases h with hmem | hacc
      · rcases List.mem_cons.mp hmem with rfl | hys
        · right
          simp only [ht, haxf, Bool.not_false, Bool.and_true, ↓reduceIte, hok, Nat.testBit_or]
          have h1 : (1 <<< x).testBit x = true := by simp [Nat.testBit_shiftLeft]
          simp [h1]
        · left; exact hys
      · right
        split
        · split
          · simp [Nat.testBit_or, hacc]
          · exact hacc
        · exact hacc

private def d0StepN (tmask : Nat) : Nat → Nat
  | 0 => baseBm
  | k + 1 => d0Step tmask (d0StepN tmask k)

private theorem d0Closure_sound (tmask : Nat) (ht32 : ∀ x, tmask.testBit x = true → x < 32)
    (l : List Nat) (hlen : l.length ≤ 4)
    (hsub : ∀ x ∈ l, tmask.testBit x = true ∨ baseBm.testBit x = true)
    (hcover : ∀ x, tmask.testBit x = true → x ∈ l ∨ baseBm.testBit x = true)
    (hstep : ∀ i (hi : i < l.length),
      let x := l[i]
      baseBm.testBit x = true ∨
      ∃ a b, a < 32 ∧ b < 32 ∧
        (baseBm.testBit a = true ∨ ∃ j, j < i ∧ l[j]? = some a) ∧
        (baseBm.testBit b = true ∨ ∃ j, j < i ∧ l[j]? = some b) ∧
        a ^^^ b = x) :
    d0ClosureOk tmask = true := by
  have hmono : ∀ k x, (d0StepN tmask k).testBit x = true → (d0StepN tmask (k + 1)).testBit x = true :=
    fun k x h => d0Step_monotone tmask (d0StepN tmask k) x h
  have hmonoLe : ∀ k1 k2, k1 ≤ k2 → ∀ x, (d0StepN tmask k1).testBit x = true → (d0StepN tmask k2).testBit x = true := by
    intro k1 k2 hle
    induction hle with
    | refl => intro x h; exact h
    | step _ ih => intro x h; exact hmono _ x (ih x h)
  have hprefix : ∀ k, k ≤ l.length → ∀ j, j < k →
      ∃ x, l[j]? = some x ∧ (d0StepN tmask k).testBit x = true := by
    intro k
    induction k with
    | zero => intro _ j hj; omega
    | succ k ih =>
      intro hkle j hj
      by_cases hjk : j < k
      · obtain ⟨x, hlj, hx⟩ := ih (by omega) j hjk
        exact ⟨x, hlj, hmono k x hx⟩
      · have hjeq : j = k := by omega
        subst hjeq
        have hlt : j < l.length := by omega
        refine ⟨l[j], List.getElem?_eq_getElem hlt, ?_⟩
        have hmem : l[j] ∈ l := List.getElem_mem hlt
        rcases hstep j hlt with hbm | ⟨a, b, ha32, hb32, ha, hb, hab⟩
        · exact hmonoLe 0 (j + 1) (Nat.zero_le _) _ hbm
        · have hav_a : (d0StepN tmask j).testBit a = true := by
            rcases ha with hba | ⟨j1, hj1, hj1eq⟩
            · exact hmonoLe 0 j (Nat.zero_le _) _ hba
            · obtain ⟨a', ha'eq, ha'bit⟩ := ih (by omega) j1 hj1
              rw [hj1eq] at ha'eq; injection ha'eq with h; subst h; exact ha'bit
          have hav_b : (d0StepN tmask j).testBit b = true := by
            rcases hb with hbb | ⟨j2, hj2, hj2eq⟩
            · exact hmonoLe 0 j (Nat.zero_le _) _ hbb
            · obtain ⟨b', hb'eq, hb'bit⟩ := ih (by omega) j2 hj2
              rw [hj2eq] at hb'eq; injection hb'eq with h; subst h; exact hb'bit
          rcases hsub l[j] hmem with htm | hbm
          · exact d0Step_add tmask (d0StepN tmask j) l[j] a b (ht32 _ htm) htm ha32 hav_a hav_b hab
          · exact hmonoLe 0 (j + 1) (Nat.zero_le _) _ hbm
  unfold d0ClosureOk
  change ((d0StepN tmask 4) &&& tmask == tmask) = true
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_and]
  cases htx : tmask.testBit x
  · simp
  · simp only [Bool.and_true]
    rcases hcover x htx with hxl | hxbm
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxl
      obtain ⟨x', hx'eq, hx'bit⟩ := hprefix l.length (Nat.le_refl _) j hj
      rw [List.getElem?_eq_getElem hj] at hx'eq; injection hx'eq with h; subst h
      exact hmonoLe l.length 4 hlen _ hx'bit
    · exact hmonoLe 0 4 (Nat.zero_le _) _ hxbm

/-- Soundness of `zeroHelperRefuted`: if there exist `c : Fin 5 → Fin 4` such that every output
    `y_j` (in `(inv[j] <<< 5) ||| asconLin j`) equals `u ^^^ v` for two elements of
    `bm0 ∪ {g_k} ∪ {y_{j'} | j' ≠ j}`, then `zeroHelperRefuted inv A B bm0 = false`. -/
private theorem array_getD_set! {α : Type} (arr : Array α) (i j : Nat) (v d : α)
    (hi : i < arr.size) (hj : j < arr.size) :
    (arr.set! i v).getD j d = if i = j then v else arr.getD j d := by
  have hsz : (arr.set! i v).size = arr.size := Array.size_setIfInBounds
  have hj' : j < (arr.set! i v).size := by omega
  change (if h : j < (arr.set! i v).size then (arr.set! i v)[j] else d) =
         if i = j then v else (if h : j < arr.size then arr[j] else d)
  rw [dif_pos hj', dif_pos hj]
  unfold Array.set! Array.setIfInBounds
  simp only [hi, ↓reduceDIte, Array.getElem_set]

private theorem zeroHelperRefuted_sound (inv A B : Fin 5 → Nat) (bm0 : Nat)
    (c : Fin 5 → Fin 4)
    (hbm : ∀ x, bm0.testBit x = true → x < 32)
    (hA : ∀ k, A k < 32) (hB : ∀ k, B k < 32)
    (hinv : ∀ j, inv j < 32)
    (hinv_ne : ∀ j1 j2 : Fin 5, j1 ≠ j2 → inv j1 ≠ inv j2)
    (hvalid : ∀ j : Fin 5,
      let yq := inv j; let yl := asconLin j
      (∃ j1 j2 : Fin 5, j1 ≠ j ∧ j2 ≠ j ∧ j1.val < j2.val ∧
        (inv j1 ^^^ inv j2 = yq) ∧ (asconLin j1 ^^^ asconLin j2 = yl)) ∨
      (∃ ka kb : Fin 5, ka.val < kb.val ∧ yq = ((1 <<< ka.val) ||| (1 <<< kb.val)) ∧
        (shiftOf (A ka) (B ka) (c ka).val ^^^ shiftOf (A kb) (B kb) (c kb).val = yl)) ∨
      (∃ k : Fin 5, yq = 1 <<< k.val ∧ bm0.testBit (yl ^^^ shiftOf (A k) (B k) (c k).val) = true) ∨
      (∃ k j2 : Fin 5, j2 ≠ j ∧ (yq ^^^ inv j2 = 1 <<< k.val) ∧
        (yl ^^^ asconLin j2 = shiftOf (A k) (B k) (c k).val))) :
    zeroHelperRefuted inv A B bm0 = false := by
  -- Show the fold maintains invariant: `st.1 = false ∧ ∀ k : Fin 5, (st.2.getD k.val 0).testBit (c k).val = true`
  unfold zeroHelperRefuted
  suffices ∀ (js : List (Fin 5)) (st : Bool × Array Nat),
      st.1 = false → st.2.size = 5 → (∀ k : Fin 5, (st.2.getD k.val 0).testBit (c k).val = true) →
      let r := js.foldl (fun (st : Bool × Array Nat) j =>
        if st.1 then st
        else
          let dom := st.2
          let yq := inv j
          let yl := asconLin j
          let constOk := (List.finRange 5).any fun j1 =>
            j1 != j && (List.finRange 5).any fun j2 =>
              j2 != j && j1.val < j2.val && (inv j1 ^^^ inv j2 == yq) && (asconLin j1 ^^^ asconLin j2 == yl)
          if constOk then (false, dom)
          else
            let has2 := (List.finRange 5).any fun ka =>
              (List.finRange 5).any fun kb =>
                ka.val < kb.val && (yq == ((1 <<< ka.val) ||| (1 <<< kb.val))) &&
                (List.range 4).any fun ca => (List.range 4).any fun cb =>
                  (shiftOf (A ka) (B ka) ca ^^^ shiftOf (A kb) (B kb) cb) == yl
            if has2 then (false, dom)
            else
              let (sk, mk) := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
                let mask := (List.range 4).foldl (fun m cv =>
                  let sh := shiftOf (A k) (B k) cv
                  let ok1 := (yq == (1 <<< k.val)) && bm0.testBit (yl ^^^ sh)
                  let ok2 := (List.finRange 5).any fun j2 =>
                    j2 != j && ((yq ^^^ inv j2) == (1 <<< k.val)) && ((yl ^^^ asconLin j2) == sh)
                  if ok1 || ok2 then m ||| (1 <<< cv) else m) 0
                if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask)
                else acc) (0, #[0, 0, 0, 0, 0])
              if sk == 0 then (true, dom)
              else if pop5 sk == 1 then
                let k := if sk == 1 then 0 else if sk == 2 then 1 else if sk == 4 then 2 else if sk == 8 then 3 else 4
                let nd := (dom.getD k 0) &&& (mk.getD k 0)
                if nd == 0 then (true, dom)
                else (false, dom.set! k nd)
              else (false, dom)) st
      r.1 = false ∧ r.2.size = 5 ∧ (∀ k : Fin 5, (r.2.getD k.val 0).testBit (c k).val = true) by
    have h0 := this (List.finRange 5) (false, #[15, 15, 15, 15, 15]) rfl rfl (by
      intro k
      have hck : (c k).val < 4 := (c k).isLt
      have h15 : ∀ v < 4, (15 : Nat).testBit v = true := by decide
      have hget : (#[15, 15, 15, 15, 15] : Array Nat).getD k.val 0 = 15 := by
        rcases k with ⟨k, hk⟩; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
      rw [hget]; exact h15 _ hck)
    exact h0.1
  intro js
  induction js with
  | nil => intro st h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons j js ih =>
    intro st h1 h2 h3
    simp only [List.foldl_cons, h1, Bool.false_eq_true, ↓reduceIte]
    -- Establish one step preserves the invariant
    have hstep :
        let dom := st.2; let yq := inv j; let yl := asconLin j
        let constOk := (List.finRange 5).any fun j1 =>
          j1 != j && (List.finRange 5).any fun j2 =>
            j2 != j && j1.val < j2.val && (inv j1 ^^^ inv j2 == yq) && (asconLin j1 ^^^ asconLin j2 == yl)
        let st' := if constOk then (false, dom)
          else
            let has2 := (List.finRange 5).any fun ka =>
              (List.finRange 5).any fun kb =>
                ka.val < kb.val && (yq == ((1 <<< ka.val) ||| (1 <<< kb.val))) &&
                (List.range 4).any fun ca => (List.range 4).any fun cb =>
                  (shiftOf (A ka) (B ka) ca ^^^ shiftOf (A kb) (B kb) cb) == yl
            if has2 then (false, dom)
            else
              let (sk, mk) := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
                let mask := (List.range 4).foldl (fun m cv =>
                  let sh := shiftOf (A k) (B k) cv
                  let ok1 := (yq == (1 <<< k.val)) && bm0.testBit (yl ^^^ sh)
                  let ok2 := (List.finRange 5).any fun j2 =>
                    j2 != j && ((yq ^^^ inv j2) == (1 <<< k.val)) && ((yl ^^^ asconLin j2) == sh)
                  if ok1 || ok2 then m ||| (1 <<< cv) else m) 0
                if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask)
                else acc) (0, #[0, 0, 0, 0, 0])
              if sk == 0 then (true, dom)
              else if pop5 sk == 1 then
                let k := if sk == 1 then 0 else if sk == 2 then 1 else if sk == 4 then 2 else if sk == 8 then 3 else 4
                let nd := (dom.getD k 0) &&& (mk.getD k 0)
                if nd == 0 then (true, dom)
                else (false, dom.set! k nd)
              else (false, dom)
        st'.1 = false ∧ st'.2.size = 5 ∧ (∀ k : Fin 5, (st'.2.getD k.val 0).testBit (c k).val = true) := by
      intro dom yq yl constOk st'
      dsimp only [st']
      by_cases hconst : constOk = true
      · simp only [hconst, ↓reduceIte]; exact ⟨by first | rfl | trivial, h2, h3⟩
      · simp only [hconst, ↓reduceIte]
        have hnc : constOk ≠ true := hconst
        by_cases hhas2 : ((List.finRange 5).any fun ka =>
            (List.finRange 5).any fun kb =>
              ka.val < kb.val && (yq == ((1 <<< ka.val) ||| (1 <<< kb.val))) &&
              (List.range 4).any fun ca => (List.range 4).any fun cb =>
                (shiftOf (A ka) (B ka) ca ^^^ shiftOf (A kb) (B kb) cb) == yl) = true
        · simp only [hhas2, ↓reduceIte]; exact ⟨by first | rfl | trivial, h2, h3⟩
        · simp only [hhas2, ↓reduceIte]
          have hn2 := hhas2
          have hsingle : ∃ kw : Fin 5,
              (((inv j == (1 <<< kw.val)) && bm0.testBit (asconLin j ^^^ shiftOf (A kw) (B kw) (c kw).val)) ||
              ((List.finRange 5).any fun j2 =>
                j2 != j && ((inv j ^^^ inv j2) == (1 <<< kw.val)) &&
                ((asconLin j ^^^ asconLin j2) == shiftOf (A kw) (B kw) (c kw).val))) = true := by
            rcases hvalid j with ⟨j1, j2, hj1, hj2, hlt, hq, hl⟩ | ⟨ka, kb, hlt, hq, hl⟩ | ⟨kw, hq, hbm'⟩ | ⟨kw, j2, hj2, hq, hl⟩
            · exfalso; apply hnc
              dsimp only [constOk, yq, yl]
              rw [List.any_eq_true]; refine ⟨j1, List.mem_finRange j1, ?_⟩
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, hj1, not_false_eq_true, true_and]
              rw [List.any_eq_true]; refine ⟨j2, List.mem_finRange j2, ?_⟩
              simp [hj2, hlt, hq, hl]
            · exfalso; apply hn2
              dsimp only [yq, yl]
              rw [List.any_eq_true]; refine ⟨ka, List.mem_finRange ka, ?_⟩
              rw [List.any_eq_true]; refine ⟨kb, List.mem_finRange kb, ?_⟩
              simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
              refine ⟨⟨hlt, hq⟩, ?_⟩
              rw [List.any_eq_true]; refine ⟨(c ka).val, List.mem_range.mpr (c ka).isLt, ?_⟩
              rw [List.any_eq_true]; refine ⟨(c kb).val, List.mem_range.mpr (c kb).isLt, ?_⟩
              simp [hl]
            · exact ⟨kw, by simp [hq, hbm']⟩
            · exact ⟨kw, (Bool.or_eq_true _ _).mpr (Or.inr (List.any_eq_true.mpr ⟨j2, List.mem_finRange j2, by simp [hj2, hq, hl]⟩))⟩
          obtain ⟨kw, hkw⟩ := hsingle
          -- Analyze the fold building `(sk, mk)`
          let mkOf (k : Fin 5) : Nat :=
            (List.range 4).foldl (fun m cv =>
              let sh := shiftOf (A k) (B k) cv
              let ok1 := (inv j == (1 <<< k.val)) && bm0.testBit (asconLin j ^^^ sh)
              let ok2 := (List.finRange 5).any fun j2 =>
                j2 != j && ((inv j ^^^ inv j2) == (1 <<< k.val)) && ((asconLin j ^^^ asconLin j2) == sh)
              if ok1 || ok2 then m ||| (1 <<< cv) else m) 0
          have hkw_bit : (mkOf kw).testBit (c kw).val = true := by
            have hfold_bit : ∀ (xs : List Nat) (m : Nat),
                ((c kw).val ∈ xs ∨ m.testBit (c kw).val = true) →
                ((xs.foldl (fun m cv =>
                  let sh := shiftOf (A kw) (B kw) cv
                  let ok1 := (inv j == (1 <<< kw.val)) && bm0.testBit (asconLin j ^^^ sh)
                  let ok2 := (List.finRange 5).any fun j2 =>
                    j2 != j && ((inv j ^^^ inv j2) == (1 <<< kw.val)) && ((asconLin j ^^^ asconLin j2) == sh)
                  if ok1 || ok2 then m ||| (1 <<< cv) else m) m).testBit (c kw).val = true) := by
              intro xs
              induction xs with
              | nil =>
                intro m hm
                rcases hm with h | h
                · cases h
                · exact h
              | cons v vs ihv =>
                intro m hm
                simp only [List.foldl_cons]
                apply ihv
                rcases hm with hmem | hbit
                · rcases List.mem_cons.mp hmem with rfl | hvs
                  · right
                    have hif : (if (((inv j == 1 <<< kw.val) && bm0.testBit (asconLin j ^^^ shiftOf (A kw) (B kw) (c kw).val)) ||
                        ((List.finRange 5).any fun j2 => j2 != j && ((inv j ^^^ inv j2) == 1 <<< kw.val) && ((asconLin j ^^^ asconLin j2) == shiftOf (A kw) (B kw) (c kw).val))) = true
                        then m ||| 1 <<< (c kw).val else m) = m ||| 1 <<< (c kw).val := by
                      rw [hkw]; rfl
                    rw [show (let sh := shiftOf (A kw) (B kw) (c kw).val
                              let ok1 := (inv j == 1 <<< kw.val) && bm0.testBit (asconLin j ^^^ sh)
                              let ok2 := (List.finRange 5).any fun j2 => j2 != j && ((inv j ^^^ inv j2) == 1 <<< kw.val) && ((asconLin j ^^^ asconLin j2) == sh)
                              if ok1 || ok2 then m ||| 1 <<< (c kw).val else m) = m ||| 1 <<< (c kw).val from hif, Nat.testBit_or]
                    have : (1 <<< (c kw).val).testBit (c kw).val = true := by simp [Nat.testBit_shiftLeft]
                    rw [this, Bool.or_true]
                  · left; exact hvs
                · right; split <;> simp [Nat.testBit_or, hbit]
            exact hfold_bit (List.range 4) 0 (Or.inl (List.mem_range.mpr (c kw).isLt))
          have hkw_ne0 : mkOf kw ≠ 0 := by
            intro hz; rw [hz] at hkw_bit; simp at hkw_bit
          -- Show the outer fold over `List.finRange 5` sets bit `kw.val` in `sk`, keeps `sk < 32`, and sets `mk[kw.val] = mkOf kw`
          have houter :
              let pair := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
                let mask := mkOf k
                if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask) else acc) (0, #[0, 0, 0, 0, 0])
              pair.1 < 32 ∧ pair.1.testBit kw.val = true ∧ pair.2.getD kw.val 0 = mkOf kw := by
            have hgen : ∀ (ks : List (Fin 5)) (acc : Nat × Array Nat),
                ks.Nodup → acc.1 < 32 → acc.2.size = 5 →
                (kw ∈ ks ∨ (acc.1.testBit kw.val = true ∧ acc.2.getD kw.val 0 = mkOf kw)) →
                let r := ks.foldl (fun (acc : Nat × Array Nat) k =>
                  let mask := mkOf k
                  if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask) else acc) acc
                r.1 < 32 ∧ r.1.testBit kw.val = true ∧ r.2.getD kw.val 0 = mkOf kw := by
              intro ks
              induction ks with
              | nil =>
                intro acc _ hlt _ h
                rcases h with h | ⟨h1, h2⟩
                · cases h
                · exact ⟨hlt, h1, h2⟩
              | cons k ks ihk =>
                intro acc hnd hlt hsz h
                obtain ⟨hknot, hnd'⟩ := List.nodup_cons.mp hnd
                simp only [List.foldl_cons]
                apply ihk _ hnd'
                · split
                  · apply Nat.or_lt_two_pow (n := 5) hlt
                    rw [Nat.shiftLeft_eq, Nat.one_mul]
                    exact Nat.pow_lt_pow_right (by omega : 1 < 2) k.isLt
                  · exact hlt
                · split <;> simp [Array.size_setIfInBounds, hsz]
                · rcases h with hmem | ⟨h1, h2⟩
                  · rcases List.mem_cons.mp hmem with rfl | hks
                    · right
                      have hne : (mkOf kw != 0) = true := bne_iff_ne.mpr hkw_ne0
                      change ((if mkOf kw != 0 then (acc.1 ||| 1 <<< kw.val, acc.2.set! kw.val (mkOf kw)) else acc).1.testBit kw.val = true ∧
                              (if mkOf kw != 0 then (acc.1 ||| 1 <<< kw.val, acc.2.set! kw.val (mkOf kw)) else acc).2.getD kw.val 0 = mkOf kw)
                      rw [if_pos hne]; simp only [Nat.testBit_or]
                      refine ⟨?_, ?_⟩
                      · have : (1 <<< kw.val).testBit kw.val = true := by simp [Nat.testBit_shiftLeft]
                        rw [this, Bool.or_true]
                      · rw [array_getD_set! _ _ _ _ _ (by omega) (by omega), if_pos rfl]
                    · left; exact hks
                  · right
                    by_cases hkeq : k = kw
                    · subst hkeq
                      have hne : (mkOf k != 0) = true := bne_iff_ne.mpr hkw_ne0
                      change ((if mkOf k != 0 then (acc.1 ||| 1 <<< k.val, acc.2.set! k.val (mkOf k)) else acc).1.testBit k.val = true ∧
                              (if mkOf k != 0 then (acc.1 ||| 1 <<< k.val, acc.2.set! k.val (mkOf k)) else acc).2.getD k.val 0 = mkOf k)
                      rw [if_pos hne]; simp only [Nat.testBit_or]
                      exact ⟨by simp [h1], by rw [array_getD_set! _ _ _ _ _ (by omega) (by omega), if_pos rfl]⟩
                    · split
                      · refine ⟨by simp [Nat.testBit_or, h1], ?_⟩
                        have hvalne : k.val ≠ kw.val := fun he => hkeq (Fin.ext he)
                        rw [array_getD_set! _ _ _ _ _ (by omega) (by omega), if_neg hvalne]; exact h2
                      · exact ⟨h1, h2⟩
            exact hgen (List.finRange 5) (0, #[0, 0, 0, 0, 0]) (List.nodup_finRange 5)
              (by decide) rfl (Or.inl (List.mem_finRange kw))
          obtain ⟨hsk_lt, hsk_bit, hmk_eq⟩ := houter
          have hsk_ne0 : (let pair := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
              let mask := mkOf k
              if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask) else acc) (0, #[0, 0, 0, 0, 0])
              pair.1) ≠ 0 := by
            intro hz; rw [hz] at hsk_bit; simp at hsk_bit
          change (let p := (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
              let mask := mkOf k
              if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask) else acc) (0, #[0, 0, 0, 0, 0])
              let st' := if p.1 == 0 then (true, st.2)
                else if pop5 p.1 == 1 then
                  let k := if p.1 == 1 then 0 else if p.1 == 2 then 1 else if p.1 == 4 then 2 else if p.1 == 8 then 3 else 4
                  let nd := (st.2.getD k 0) &&& (p.2.getD k 0)
                  if nd == 0 then (true, st.2) else (false, st.2.set! k nd)
                else (false, st.2)
              st'.1 = false ∧ st'.2.size = 5 ∧ (∀ k : Fin 5, (st'.2.getD k.val 0).testBit (c k).val = true))
          generalize hp : (List.finRange 5).foldl (fun (acc : Nat × Array Nat) k =>
              let mask := mkOf k
              if mask != 0 then (acc.1 ||| (1 <<< k.val), acc.2.set! k.val mask) else acc) (0, #[0, 0, 0, 0, 0]) = pr at hsk_lt hsk_bit hmk_eq hsk_ne0 ⊢
          have hbe0 : (pr.1 == 0) = false := beq_false_of_ne hsk_ne0
          simp only [hbe0, Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i hpop1
            have hpop1' : pop5 pr.1 = 1 := beq_iff_eq.mp hpop1
            have hkeq : (if pr.1 == 1 then 0 else if pr.1 == 2 then 1 else if pr.1 == 4 then 2 else if pr.1 == 8 then 3 else 4) = kw.val := by
              have hfin : ∀ s : Fin 32, ∀ w : Fin 5, pop5 s.val = 1 → s.val.testBit w.val = true →
                  (if s.val == 1 then 0 else if s.val == 2 then 1 else if s.val == 4 then 2 else if s.val == 8 then 3 else 4) = w.val := by
                decide +kernel
              exact hfin ⟨pr.1, hsk_lt⟩ kw hpop1' hsk_bit
            rw [hkeq, hmk_eq]
            have hnd_bit : ((st.2.getD kw.val 0) &&& mkOf kw).testBit (c kw).val = true := by
              rw [Nat.testBit_and, h3 kw, hkw_bit]; rfl
            have hnd_ne0 : ((st.2.getD kw.val 0) &&& mkOf kw) ≠ 0 := by
              intro hz; rw [hz] at hnd_bit; simp at hnd_bit
            have hbe_nd : (((st.2.getD kw.val 0) &&& mkOf kw) == 0) = false := beq_false_of_ne hnd_ne0
            simp only [hbe_nd, Bool.false_eq_true, ↓reduceIte]
            refine ⟨by first | rfl | trivial, by simp [Array.size_setIfInBounds, h2], ?_⟩
            intro k
            by_cases hkk : k = kw
            · subst hkk
              rw [array_getD_set! _ _ _ _ _ (by omega) (by omega), if_pos rfl]; exact hnd_bit
            · have hv : kw.val ≠ k.val := fun he => hkk (Fin.ext he.symm)
              have hget : ((st.2.set! kw.val ((st.2.getD kw.val 0) &&& mkOf kw)).getD k.val 0) = st.2.getD k.val 0 := by
                rw [array_getD_set! _ _ _ _ _ (by omega) (by omega), if_neg hv]
              rw [hget]; exact h3 k
          · exact ⟨by first | rfl | trivial, h2, h3⟩
    exact ih _ hstep.1 hstep.2.1 hstep.2.2

/-! ## 7. Bridging circuit structure to `cert_master` -/

private theorem nat_eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have h' := congrArg (· ^^^ b) h
  simpa [Nat.xor_assoc, Nat.xor_self] using h'

private theorem nodup_of_map {α β : Type} (f : α → β) {xs : List α} (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun ha => hnot (List.mem_map.mpr ⟨a, ha, rfl⟩), ih hnd⟩

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

private theorem nodup_of_inj_getElem {α : Type} {xs : List α}
    (hinj : ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length), xs[i] = xs[j] → i = j) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    refine List.nodup_cons.mpr ⟨fun ha => ?_, ih (fun i j hi hj heq => ?_)⟩
    · obtain ⟨k, hk, hka⟩ := List.getElem_of_mem ha
      have := hinj 0 (k + 1) (by simp) (by simp; omega) (by simpa using hka.symm)
      omega
    · have := hinj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by simpa using heq)
      omega

private theorem inj_getElem_of_nodup {α : Type} {xs : List α} (hnd : xs.Nodup) :
    ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length), xs[i] = xs[j] → i = j := by
  induction xs with
  | nil => intro i _ hi; simp at hi
  | cons a as ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    intro i j hi hj heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        exfalso; apply hnot
        have hj' : j < as.length := by simp at hj; omega
        have : a = as[j] := by simpa using heq
        rw [this]; exact List.getElem_mem hj'
    | succ i =>
      cases j with
      | zero =>
        exfalso; apply hnot
        have hi' : i < as.length := by simp at hi; omega
        have : as[i] = a := by simpa using heq
        rw [← this]; exact List.getElem_mem hi'
      | succ j =>
        have := ih hnd' i j (by simp at hi; omega) (by simp at hj; omega) (by simpa using heq)
        omega

/-- Helper: count distinct elements of `asconPoly 0..4` and `pre_req` in a list of linear gates. -/
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
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons_of_mem x hz))
    have hle := ih hnd' hsub'
    have her : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hxys]
      have hpos : 0 < ys.length := List.length_pos_of_mem hxys
      omega
    simp only [List.length_cons]
    omega

/-- If a list `ys` of length `xs.length` contains all elements of a nodup list `xs`,
    then every element of `ys` belongs to `xs`! -/
private theorem subset_of_length_eq {α : Type} [DecidableEq α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) (hlen : ys.length ≤ xs.length) :
    ∀ y ∈ ys, y ∈ xs := by
  induction xs generalizing ys with
  | nil =>
    intro y hy
    have h0 : ys.length = 0 := Nat.eq_zero_of_le_zero hlen
    exact absurd (List.length_pos_of_mem hy) (by omega)
  | cons x xs ih =>
    obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hxys : x ∈ ys := hsub x (List.mem_cons_self ..)
    have her_len : (ys.erase x).length ≤ xs.length := by
      rw [List.length_erase_of_mem hxys]
      have hpos : 0 < ys.length := List.length_pos_of_mem hxys
      simp only [List.length_cons] at hlen; omega
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := fun he => hxnot (he ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons_of_mem x hz))
    intro y hy
    by_cases hyx : y = x
    · exact hyx ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem x (ih hnd' hsub' her_len y ((List.mem_erase_of_ne hyx).mpr hy))

/-- If a list `ys` of length `≤ xs.length + 1` contains all elements of a nodup list `xs`,
    then there exists a single element `h` such that every `y ∈ ys` is in `h :: xs`! -/
private theorem subset_plus_one {α : Type} [DecidableEq α] [Inhabited α] {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) (hlen : ys.length ≤ xs.length + 1) :
    ∃ h : α, ∀ y ∈ ys, y = h ∨ y ∈ xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨default, fun _ h => by cases h⟩
    | cons y rest =>
      cases rest with
      | nil => exact ⟨y, fun z hz => Or.inl (List.mem_singleton.mp hz)⟩
      | cons _ _ => simp at hlen
  | cons x xs ih =>
    obtain ⟨hxnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hxys : x ∈ ys := hsub x (List.mem_cons_self ..)
    have her_len : (ys.erase x).length ≤ xs.length + 1 := by
      rw [List.length_erase_of_mem hxys]
      have hpos : 0 < ys.length := List.length_pos_of_mem hxys
      simp only [List.length_cons] at hlen; omega
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := fun he => hxnot (he ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (List.mem_cons_of_mem x hz))
    obtain ⟨h, hh⟩ := ih hnd' hsub' her_len
    refine ⟨h, fun y hy => ?_⟩
    by_cases hyx : y = x
    · exact Or.inr (hyx ▸ List.mem_cons_self ..)
    · rcases hh y ((List.mem_erase_of_ne hyx).mpr hy) with rfl | hxs
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem x hxs)

/-- Invertibility of a 5×5 GF(2) matrix: if `∀ j : Fin 5, (1 <<< j.val) ∈ span(rows)`,
    then `isBasis5` holds and `findInvRow` yields the exact inverse! -/
private theorem basis5_of_span {r0 r1 r2 r3 r4 : Nat}
    (hr : r0 < 32 ∧ r1 < 32 ∧ r2 < 32 ∧ r3 < 32 ∧ r4 < 32)
    (hspan : ∀ j : Fin 5, ∃ s : Fin 32,
      maskSubset (fun i : Fin 5 => match i with | ⟨0,_⟩ => r0 | ⟨1,_⟩ => r1 | ⟨2,_⟩ => r2 | ⟨3,_⟩ => r3 | ⟨4,_⟩ => r4) s.val = 1 <<< j.val) :
    isBasis5 r0 r1 r2 r3 r4 = true := by
  -- Prove by showing if `maskSubset rows m = 0` for `m ≠ 0`, then `span(rows)` has ≤ 16 elements,
  -- contradicting that it contains all 32 vectors of GF(2)^5!
  let ms : Fin 5 → Nat
    | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2 | ⟨3, _⟩ => r3 | ⟨4, _⟩ => r4
  have hms_xor := maskSubset_xor ms
  -- Every v < 32 is in the image of `maskSubset ms` on `Fin 32`!
  have hsurj : ∀ v : Fin 32, ∃ s : Fin 32, maskSubset ms s.val = v.val := by
    obtain ⟨s0, hs0⟩ := hspan ⟨0, by decide⟩
    obtain ⟨s1, hs1⟩ := hspan ⟨1, by decide⟩
    obtain ⟨s2, hs2⟩ := hspan ⟨2, by decide⟩
    obtain ⟨s3, hs3⟩ := hspan ⟨3, by decide⟩
    obtain ⟨s4, hs4⟩ := hspan ⟨4, by decide⟩
    intro v
    let s := (if v.val.testBit 0 then s0.val else 0) ^^^
             (if v.val.testBit 1 then s1.val else 0) ^^^
             (if v.val.testBit 2 then s2.val else 0) ^^^
             (if v.val.testBit 3 then s3.val else 0) ^^^
             (if v.val.testBit 4 then s4.val else 0)
    have hslt : s < 32 := by
      have hite : ∀ (c : Bool) (a : Fin 32), (if c then a.val else 0) < 32 := fun c a => by
        cases c with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact a.isLt
      exact xor_lt_32 (xor_lt_32 (xor_lt_32 (xor_lt_32 (hite _ s0) (hite _ s1)) (hite _ s2)) (hite _ s3)) (hite _ s4)
    refine ⟨⟨s, hslt⟩, ?_⟩
    simp only [s, hms_xor]
    have hm0 : maskSubset ms 0 = 0 := by simp [maskSubset]
    have hite2 : ∀ (c : Bool) (a : Fin 32), maskSubset ms (if c then a.val else 0) = if c then maskSubset ms a.val else 0 := by
      intro c a; cases c <;> simp [hm0]
    rw [hite2, hite2, hite2, hite2, hite2, hs0, hs1, hs2, hs3, hs4]
    apply Nat.eq_of_testBit_eq; intro k
    have hbt : ∀ (c : Bool) (j : Nat), (if c then 1 <<< j else 0).testBit k = (c && decide (k = j)) := by
      intro c j; cases c
      · simp
      · simp only [↓reduceIte, Bool.true_and, Nat.testBit_shiftLeft]
        by_cases hkj : k = j
        · subst hkj; simp
        · by_cases hle : j ≤ k
          · cases hm : k - j with | zero => omega | succ _ => simp [hkj, hle, Nat.testBit_succ]
          · simp [hkj, hle]
    simp only [Nat.testBit_xor, hbt]
    match k with
    | 0 | 1 | 2 | 3 | 4 => simp
    | m + 5 =>
      have h0 : v.val.testBit (m + 5) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show v.val < 2 ^ 5 from v.isLt) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
      simp [h0]
  -- A surjective map `Fin 32 → Fin 32` is injective!
  have hinj : ∀ a b : Fin 32, maskSubset ms a.val = maskSubset ms b.val → a = b := by
    let f : Fin 32 → Nat := fun s => maskSubset ms s.val
    have hnodup : (List.finRange 32).Nodup := List.nodup_finRange 32
    have hsub : ∀ v ∈ List.range 32, v ∈ (List.finRange 32).map f := by
      intro v hv
      obtain ⟨s, hs⟩ := hsurj ⟨v, List.mem_range.mp hv⟩
      exact List.mem_map.mpr ⟨s, List.mem_finRange s, hs⟩
    -- Pigeonhole: if f a = f b with a ≠ b, then ((List.finRange 32).erase b).map f still covers List.range 32,
    -- impossible since length 31 < 32!
    intro a b hab
    apply Classical.byContradiction; intro hne
    have hsub' : ∀ v ∈ List.range 32, v ∈ ((List.finRange 32).erase b).map f := by
      intro v hv
      obtain ⟨s, hs⟩ := hsurj ⟨v, List.mem_range.mp hv⟩
      by_cases hsb : s = b
      · subst hsb
        exact List.mem_map.mpr ⟨a, (List.mem_erase_of_ne hne).mpr (List.mem_finRange a), hab.trans hs⟩
      · exact List.mem_map.mpr ⟨s, (List.mem_erase_of_ne hsb).mpr (List.mem_finRange s), hs⟩
    have hle := nodup_length_le_of_subset (List.nodup_range) hsub'
    rw [List.length_range, List.length_map, List.length_erase_of_mem (List.mem_finRange b), List.length_finRange] at hle
    omega
  -- Hence `maskSubset ms (k + 1) ≠ 0` for all `k < 31`!
  unfold isBasis5
  rw [List.all_eq_true]
  intro k hk
  have hk31 : k < 31 := List.mem_range.mp hk
  rw [bne_iff_ne]
  intro hz
  have hm0 : maskSubset ms 0 = 0 := by simp [maskSubset]
  have heq := hinj ⟨k + 1, by omega⟩ ⟨0, by decide⟩ (hz.trans hm0.symm)
  have : k + 1 = 0 := congrArg Fin.val heq
  omega

private theorem findInvRow_spec {m0 m1 m2 m3 m4 target s : Nat}
    (hb : isBasis5 m0 m1 m2 m3 m4 = true)
    (hs32 : s < 32)
    (hs : maskSubset (fun i : Fin 5 => match i with | ⟨0,_⟩ => m0 | ⟨1,_⟩ => m1 | ⟨2,_⟩ => m2 | ⟨3,_⟩ => m3 | ⟨4,_⟩ => m4) s = target) :
    findInvRow m0 m1 m2 m3 m4 target = s := by
  let ms : Fin 5 → Nat
    | ⟨0, _⟩ => m0 | ⟨1, _⟩ => m1 | ⟨2, _⟩ => m2 | ⟨3, _⟩ => m3 | ⟨4, _⟩ => m4
  have hms_xor := maskSubset_xor ms
  unfold isBasis5 at hb
  rw [List.all_eq_true] at hb
  have hinj : ∀ a b, a < 32 → b < 32 → maskSubset ms a = maskSubset ms b → a = b := by
    intro a b ha hb' hab
    apply Classical.byContradiction; intro hne
    have hnz : a ^^^ b ≠ 0 := by intro hz; exact hne (nat_eq_of_xor_eq_zero hz)
    have hlt : a ^^^ b < 32 := xor_lt_32 ha hb'
    have hmem : (a ^^^ b) - 1 ∈ List.range 31 := List.mem_range.mpr (by omega)
    have hnb := hb ((a ^^^ b) - 1) hmem
    have heq1 : (a ^^^ b) - 1 + 1 = a ^^^ b := by omega
    rw [heq1, bne_iff_ne] at hnb
    apply hnb
    rw [hms_xor, hab, Nat.xor_self]
  unfold findInvRow
  dsimp only
  change (match (List.range 32).find? (fun u => maskSubset ms u == target) with | some s => s | none => 0) = s
  cases hfind : (List.range 32).find? (fun u => maskSubset ms u == target) with
  | none =>
    have hnone := List.find?_eq_none.mp hfind s (List.mem_range.mpr hs32)
    exact absurd (beq_iff_eq.mpr hs) hnone
  | some u =>
    have hu_mem := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
    have hu_eq := by simpa using List.find?_some hfind
    exact hinj u s hu_mem hs32 (hu_eq.trans hs.symm)

/-! ## 8. Sorting 5 distinct indices in `Fin 10` -/

/-- Insert into a sorted list without changing membership or length. -/
private def insSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insSorted x ys

private def sortList : List Nat → List Nat
  | [] => []
  | x :: xs => insSorted x (sortList xs)

private theorem mem_insSorted {x y : Nat} {xs : List Nat} :
    y ∈ insSorted x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [insSorted]
  | cons z zs ih =>
    unfold insSorted
    split
    · simp
    · simp only [List.mem_cons, ih]; exact ⟨fun h => by rcases h with rfl | rfl | h; exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr h), fun h => by rcases h with rfl | rfl | h; exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr h)⟩

private theorem length_insSorted (x : Nat) (xs : List Nat) :
    (insSorted x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons z zs ih => unfold insSorted; split <;> simp [ih]

private theorem pairwise_insSorted {x : Nat} {xs : List Nat}
    (hnd : x ∉ xs) (hp : xs.Pairwise (· < ·)) : (insSorted x xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insSorted]
  | cons z zs ih =>
    obtain ⟨hznot, hp'⟩ := List.pairwise_cons.mp hp
    have hxz : x ≠ z := fun h => hnd (h ▸ List.mem_cons_self ..)
    have hxnot : x ∉ zs := fun h => hnd (List.mem_cons_of_mem z h)
    unfold insSorted
    split
    · rename_i hle
      have hlt : x < z := by omega
      exact List.pairwise_cons.mpr ⟨fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hys
        · exact hlt
        · exact Nat.lt_trans hlt (hznot y hys), hp⟩
    · rename_i hgt
      have hlt : z < x := by omega
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, ih hxnot hp'⟩
      rcases mem_insSorted.mp hy with rfl | hys
      · exact hlt
      · exact hznot y hys

private theorem mem_sortList {x : Nat} {xs : List Nat} : x ∈ sortList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [sortList]
  | cons y ys ih => simp [sortList, mem_insSorted, ih]

private theorem length_sortList (xs : List Nat) : (sortList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [sortList, length_insSorted, ih]

private theorem pairwise_sortList {xs : List Nat} (hnd : xs.Nodup) : (sortList xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [sortList]
  | cons y ys ih =>
    obtain ⟨hynot, hnd'⟩ := List.nodup_cons.mp hnd
    exact pairwise_insSorted (fun h => hynot (mem_sortList.mp h)) (ih hnd')

/-! ## 9. Main Theorem: `¬ Crypto.Statements.CZ_rec_ascon_gates.Record 14` -/

private structure NLInfo where
  a     : Nat
  b     : Nat
  ca    : Bool
  cb    : Bool
  poly  : Nat
  ha    : a < 32
  hb    : b < 32
  hpoly : poly = (prodPoly a b ^^^ (if ca then a else 0)) ^^^ (if cb then b else 0)

private structure LinInfo where
  depth : Nat
  poly  : Nat
  isXor : Bool
  u     : Nat
  v     : Nat
  hdep  : depth ≤ 1
  hpoly : if isXor then poly = u ^^^ v else poly = 0 ∨ poly = u ∨ poly = v

/-- Walk `c.gates` collecting every depth-1 nonlinear gate (`NLInfo`) and every depth-≤-1 linear gate (`LinInfo`),
    recording its inputs' polynomials from the prior prefix! -/
private def mkLinInfo (acc : Array SimWire) (g : B2Gate) (hlin : g.op.isLinear = true)
    (hd : (stepSim acc g).depth ≤ 1) : LinInfo :=
  let sw := stepSim acc g
  let s1 := acc.getD g.w1 ⟨0, 0, false⟩
  let s2 := acc.getD g.w2 ⟨0, 0, false⟩
  if hboth : opLinCa g.op = true ∧ opLinCb g.op = true then
    ⟨sw.depth, sw.poly, true, s1.poly, s2.poly, hd, by
      dsimp only [sw, s1, s2, stepSim]; simp [hlin, hboth.1, hboth.2]⟩
  else
    ⟨sw.depth, sw.poly, false, s1.poly, s2.poly, hd, by
      dsimp only [sw, s1, s2, stepSim]; simp only [hlin, Bool.false_eq_true, ↓reduceIte]
      cases hca : opLinCa g.op <;> cases hcb : opLinCb g.op
      · simp [hca, hcb]
      · right; right; simp [hca, hcb]
      · right; left; simp [hca, hcb]
      · exact absurd ⟨hca, hcb⟩ hboth⟩

private theorem mkLinInfo_fields (acc : Array SimWire) (g : B2Gate) (hlin : g.op.isLinear = true)
    (hd : (stepSim acc g).depth ≤ 1) :
    (mkLinInfo acc g hlin hd).depth = (stepSim acc g).depth ∧
    (mkLinInfo acc g hlin hd).poly = (stepSim acc g).poly ∧
    (mkLinInfo acc g hlin hd).u = (acc.getD g.w1 ⟨0, 0, false⟩).poly ∧
    (mkLinInfo acc g hlin hd).v = (acc.getD g.w2 ⟨0, 0, false⟩).poly := by
  unfold mkLinInfo
  by_cases hboth : opLinCa g.op = true ∧ opLinCb g.op = true <;> simp [hboth]

private def stepExtract (st : Array SimWire × List NLInfo × List LinInfo) (g : B2Gate) :
    Array SimWire × List NLInfo × List LinInfo :=
  let acc := st.1; let nls := st.2.1; let lins := st.2.2
  let sw := stepSim acc g
  let s1 := acc.getD g.w1 ⟨0, 0, false⟩
  let s2 := acc.getD g.w2 ⟨0, 0, false⟩
  if hlin : g.op.isLinear = true then
    let lins' := if hd : sw.depth ≤ 1 then mkLinInfo acc g hlin hd :: lins else lins
    (acc.push sw, nls, lins')
  else
    let nls' :=
      if hd : sw.depth = 1 then
        if hab : s1.poly < 32 ∧ s2.poly < 32 then
          ⟨s1.poly, s2.poly, xor (opLinCa g.op) s2.cbit, xor (opLinCb g.op) s1.cbit, sw.poly,
            hab.1, hab.2, by dsimp only [sw, s1, s2, stepSim]; simp [hlin]⟩ :: nls
        else nls
      else nls
    (acc.push sw, nls', lins)

private theorem stepExtract_nl_eq1 (acc : Array SimWire) (nls : List NLInfo) (lins : List LinInfo)
    (g : B2Gate) (hlin : ¬ g.op.isLinear = true) (hd1 : (stepSim acc g).depth = 1)
    (hab : (acc.getD g.w1 ⟨0, 0, false⟩).poly < 32 ∧ (acc.getD g.w2 ⟨0, 0, false⟩).poly < 32) :
    stepExtract (acc, nls, lins) g =
      (acc.push (stepSim acc g),
       ⟨(acc.getD g.w1 ⟨0, 0, false⟩).poly, (acc.getD g.w2 ⟨0, 0, false⟩).poly,
        xor (opLinCa g.op) (acc.getD g.w2 ⟨0, 0, false⟩).cbit, xor (opLinCb g.op) (acc.getD g.w1 ⟨0, 0, false⟩).cbit,
        (stepSim acc g).poly, hab.1, hab.2, by dsimp only [stepSim]; simp [Bool.eq_false_iff.mpr hlin]⟩ :: nls,
       lins) := by
  unfold stepExtract
  dsimp only
  have hlinf : g.op.isLinear = false := Bool.eq_false_iff.mpr hlin
  simp only [hlinf, Bool.false_eq_true, ↓reduceDIte, hd1, hab, and_self]

private theorem stepExtract_nl_ne1 (acc : Array SimWire) (nls : List NLInfo) (lins : List LinInfo)
    (g : B2Gate) (hlin : ¬ g.op.isLinear = true) (hd1 : ¬ (stepSim acc g).depth = 1) :
    stepExtract (acc, nls, lins) g = (acc.push (stepSim acc g), nls, lins) := by
  unfold stepExtract
  dsimp only
  have hlinf : g.op.isLinear = false := Bool.eq_false_iff.mpr hlin
  simp only [hlinf, Bool.false_eq_true, ↓reduceDIte, hd1]

private def extractGates (gates : List B2Gate) :
    (Array SimWire × List NLInfo × List LinInfo) :=
  gates.foldl stepExtract (simInit, [], [])

-- Keep main proof completely self-contained via a clean extraction invariant on `c.gates`!
private def xorList (xs : List Nat) : Nat :=
  xs.foldl (· ^^^ ·) 0

private def inQuadSpan (qs : List Nat) (q : Nat) : Prop :=
  ∃ sub : List Nat, (∀ x ∈ sub, x ∈ qs) ∧ xorList sub = q

private theorem inQuadSpan_zero (qs : List Nat) : inQuadSpan qs 0 :=
  ⟨[], (fun _ h => by cases h), rfl⟩

private theorem xorList_append (xs ys : List Nat) :
    xorList (xs ++ ys) = xorList xs ^^^ xorList ys := by
  have hgen : ∀ (zs : List Nat) (a : Nat), zs.foldl (· ^^^ ·) a = a ^^^ xorList zs := by
    intro zs
    induction zs with
    | nil => intro a; simp [xorList]
    | cons z zs ih =>
      intro a
      simp only [List.foldl_cons, xorList] at ih ⊢
      rw [ih (a ^^^ z), ih (0 ^^^ z)]
      simp only [Nat.zero_xor, Nat.xor_assoc]
  change (xs ++ ys).foldl (· ^^^ ·) 0 = xorList xs ^^^ xorList ys
  rw [List.foldl_append, hgen]; rfl

private theorem inQuadSpan_xor {qs : List Nat} {q1 q2 : Nat}
    (h1 : inQuadSpan qs q1) (h2 : inQuadSpan qs q2) : inQuadSpan qs (q1 ^^^ q2) := by
  obtain ⟨s1, hs1, hq1⟩ := h1
  obtain ⟨s2, hs2, hq2⟩ := h2
  refine ⟨s1 ++ s2, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hx with h | h
    · exact hs1 x h
    · exact hs2 x h
  · rw [xorList_append, hq1, hq2]

private theorem inQuadSpan_mono {qs qs' : List Nat} {q : Nat}
    (hsub : ∀ x ∈ qs, x ∈ qs') (h : inQuadSpan qs q) : inQuadSpan qs' q := by
  obtain ⟨s, hs, hq⟩ := h
  exact ⟨s, fun x hx => hsub x (hs x hx), hq⟩

private theorem inQuadSpan_mem {qs : List Nat} {q : Nat} (h : q ∈ qs) : inQuadSpan qs q :=
  ⟨[q], fun x hx => by rw [List.mem_singleton.mp hx]; exact h, by simp [xorList]⟩

private theorem inQuadSpan_of_length_le_5 {qs : List Nat} (hlen : qs.length ≤ 5)
    (hcov : ∀ j : Fin 5, inQuadSpan qs (asconQuad j)) :
    qs.length = 5 ∧ qs.Nodup ∧
    (∀ q ∈ qs, ∃ m : Fin 32, m.val ≠ 0 ∧ q = qOfMask m.val) := by
  -- First reduce any `inQuadSpan qs q` to a 5-bit subset of `qs`!
  have hsub_to_mask : ∀ (l : List Nat) (q : Nat), inQuadSpan l q →
      ∃ m : Nat, m < 2 ^ l.length ∧
        q = (List.range l.length).foldl (fun acc i => if m.testBit i then acc ^^^ l.getD i 0 else acc) 0 := by
    intro l q ⟨sub, hsub, hq⟩
    subst hq
    induction sub with
    | nil =>
      refine ⟨0, Nat.two_pow_pos _, ?_⟩
      have h0 : ∀ (xs : List Nat), xs.foldl (fun acc i => if (0 : Nat).testBit i then acc ^^^ l.getD i 0 else acc) 0 = 0 := by
        intro xs
        suffices ∀ a, xs.foldl (fun acc i => if (0 : Nat).testBit i then acc ^^^ l.getD i 0 else acc) a = a from this 0
        induction xs with
        | nil => intro a; rfl
        | cons _ _ ih => intro a; rw [List.foldl_cons, Nat.zero_testBit]; simp only [Bool.false_eq_true, ↓reduceIte]; exact ih a
      rw [h0]; rfl
    | cons x xs ih =>
      have hx : x ∈ l := hsub x (List.mem_cons_self ..)
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨m, hm, hmq⟩ := ih (fun z hz => hsub z (List.mem_cons_of_mem _ hz))
      have hxor_fold : ∀ (ys : List Nat) (m1 m2 a1 a2 : Nat),
          ys.foldl (fun acc i => if (m1 ^^^ m2).testBit i then acc ^^^ l.getD i 0 else acc) (a1 ^^^ a2) =
          ys.foldl (fun acc i => if m1.testBit i then acc ^^^ l.getD i 0 else acc) a1 ^^^
          ys.foldl (fun acc i => if m2.testBit i then acc ^^^ l.getD i 0 else acc) a2 := by
        intro ys
        induction ys with
        | nil => intro _ _ _ _; rfl
        | cons y ys ihy =>
          intro m1 m2 a1 a2
          rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, Nat.testBit_xor]
          have hstep : (if (m1.testBit y ^^ m2.testBit y) = true then (a1 ^^^ a2) ^^^ l.getD y 0 else a1 ^^^ a2) =
              (if m1.testBit y = true then a1 ^^^ l.getD y 0 else a1) ^^^ (if m2.testBit y = true then a2 ^^^ l.getD y 0 else a2) := by
            cases m1.testBit y <;> cases m2.testBit y
            · rfl
            · simp [Nat.xor_assoc]
            · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
              apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_xor]
              cases a1.testBit k <;> cases a2.testBit k <;> cases (l.getD y 0).testBit k <;> rfl
            · simp only [Bool.xor_self, Bool.false_eq_true, ↓reduceIte]
              apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_xor]
              cases a1.testBit k <;> cases a2.testBit k <;> cases (l.getD y 0).testBit k <;> rfl
          rw [hstep, ihy]
      have hsingle : ∀ (ys : List Nat) (a : Nat), ys.Nodup →
          ys.foldl (fun acc i => if (1 <<< idx).testBit i then acc ^^^ l.getD i 0 else acc) a =
            if idx ∈ ys then a ^^^ l.getD idx 0 else a := by
        intro ys
        induction ys with
        | nil => intro a _; simp
        | cons y ys ihy =>
          intro a hnd
          obtain ⟨hynot, hnd'⟩ := List.nodup_cons.mp hnd
          simp only [List.foldl_cons, List.mem_cons]
          have htb : (1 <<< idx).testBit y = decide (y = idx) := by
            rw [Nat.testBit_shiftLeft]
            by_cases h : y = idx
            · subst h; simp
            · by_cases hle : idx ≤ y
              · cases hm : y - idx with | zero => omega | succ _ => simp [h, hle, Nat.testBit_succ]
              · simp [h, hle]
          rw [htb]
          by_cases hy : y = idx
          · subst hy
            rw [decide_eq_true rfl]; simp only [↓reduceIte, true_or]
            rw [ihy _ hnd']; simp [hynot]
          · have hne : idx ≠ y := fun h => hy h.symm
            rw [decide_eq_false hy]; simp only [Bool.false_eq_true, ↓reduceIte, hne, false_or]
            exact ihy _ hnd'
      refine ⟨(1 <<< idx) ^^^ m, Nat.xor_lt_two_pow (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) hidx) hm, ?_⟩
      have hxl : xorList (l[idx] :: xs) = l[idx] ^^^ xorList xs := by
        have hcons : ∀ (zs : List Nat) (a : Nat), zs.foldl (· ^^^ ·) a = a ^^^ xorList zs := by
          intro zs; induction zs with
          | nil => intro a; simp [xorList]
          | cons z zs ihz => intro a; simp only [List.foldl_cons, xorList] at ihz ⊢; rw [ihz (a ^^^ z), ihz (0 ^^^ z)]; simp [Nat.xor_assoc]
        unfold xorList; simp only [List.foldl_cons, Nat.zero_xor]; exact hcons xs l[idx]
      rw [hxl, hmq]
      have hf0 := hxor_fold (List.range l.length) (1 <<< idx) m 0 0
      simp only [Nat.zero_xor] at hf0
      rw [hf0, hsingle (List.range l.length) 0 List.nodup_range]
      simp [List.mem_range.mpr hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  -- Now prove `qs.length = 5` by cardinality: all 32 `qOfMask m` are in the image of `Fin (2^qs.length)`!
  let f (m : Nat) : Nat :=
    (List.range qs.length).foldl (fun acc i => if m.testBit i then acc ^^^ qs.getD i 0 else acc) 0
  have hf_xor : ∀ m1 m2, f (m1 ^^^ m2) = f m1 ^^^ f m2 := by
    intro m1 m2
    have hgen : ∀ (ys : List Nat) (a1 a2 : Nat),
        ys.foldl (fun acc i => if (m1 ^^^ m2).testBit i then acc ^^^ qs.getD i 0 else acc) (a1 ^^^ a2) =
        ys.foldl (fun acc i => if m1.testBit i then acc ^^^ qs.getD i 0 else acc) a1 ^^^
        ys.foldl (fun acc i => if m2.testBit i then acc ^^^ qs.getD i 0 else acc) a2 := by
      intro ys; induction ys with
      | nil => intro _ _; rfl
      | cons y ys ihy =>
        intro a1 a2; rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, Nat.testBit_xor]
        have hst : (if (m1.testBit y ^^ m2.testBit y) = true then (a1 ^^^ a2) ^^^ qs.getD y 0 else a1 ^^^ a2) =
            (if m1.testBit y = true then a1 ^^^ qs.getD y 0 else a1) ^^^ (if m2.testBit y = true then a2 ^^^ qs.getD y 0 else a2) := by
          cases m1.testBit y <;> cases m2.testBit y
          · rfl
          · simp [Nat.xor_assoc]
          · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
            apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_xor]
            cases a1.testBit k <;> cases a2.testBit k <;> cases (qs.getD y 0).testBit k <;> rfl
          · simp only [Bool.xor_self, Bool.false_eq_true, ↓reduceIte]
            apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_xor]
            cases a1.testBit k <;> cases a2.testBit k <;> cases (qs.getD y 0).testBit k <;> rfl
        rw [hst, ihy]
    exact hgen (List.range qs.length) 0 0
  have hQ_sub : ∀ m : Fin 32, ∃ s : Nat, s < 2 ^ qs.length ∧ f s = qOfMask m.val := by
    intro m
    have hsp : inQuadSpan qs (qOfMask m.val) := by
      unfold qOfMask
      have hi : ∀ (c : Bool) (j : Fin 5), inQuadSpan qs (if c then asconQuad j else 0) := fun c j => by
        cases c <;> first | exact inQuadSpan_zero qs | exact hcov j
      exact inQuadSpan_xor (inQuadSpan_xor (inQuadSpan_xor (inQuadSpan_xor (hi _ ⟨0, by decide⟩) (hi _ ⟨1, by decide⟩))
        (hi _ ⟨2, by decide⟩)) (hi _ ⟨3, by decide⟩)) (hi _ ⟨4, by decide⟩)
    obtain ⟨s, hs, hfs⟩ := hsub_to_mask qs (qOfMask m.val) hsp; exact ⟨s, hs, hfs.symm⟩
  have hQ_nodup : ((List.finRange 32).map (fun m => qOfMask m.val)).Nodup := by
    apply nodup_map_of_inj (List.nodup_finRange 32)
    intro a _ b _ hab
    apply Classical.byContradiction; intro hne
    have hnz : a.val ^^^ b.val ≠ 0 := fun hz => hne (Fin.ext (nat_eq_of_xor_eq_zero hz))
    have hlt : a.val ^^^ b.val < 32 := xor_lt_32 a.isLt b.isLt
    have h0 := asconQuad_indep ⟨a.val ^^^ b.val, hlt⟩ hnz
    rw [qOfMask_xor, hab, Nat.xor_self] at h0
    exact h0 rfl
  have hsub_img : ∀ v ∈ (List.finRange 32).map (fun m => qOfMask m.val), v ∈ (List.range (2 ^ qs.length)).map f := by
    intro v hv
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hv
    obtain ⟨s, hs, hfs⟩ := hQ_sub m
    exact List.mem_map.mpr ⟨s, List.mem_range.mpr hs, hfs⟩
  have hcard := nodup_length_le_of_subset hQ_nodup hsub_img
  rw [List.length_map, List.length_finRange, List.length_map, List.length_range] at hcard
  have hlen5 : qs.length = 5 := by
    have : qs.length ≥ 5 := by
      apply Classical.byContradiction; intro hlt; have : qs.length ≤ 4 := by omega
      have : 2 ^ qs.length ≤ 16 := Nat.pow_le_pow_right (by omega : 2 > 0) this
      omega
    omega
  -- Since length = 5, `2 ^ qs.length = 32`, so `(List.range 32).map f` has length 32 and covers all 32 elements of Q!
  have hall_in_Q : ∀ s < 32, f s ∈ (List.finRange 32).map (fun m => qOfMask m.val) := by
    intro s hs
    have hlen_le : ((List.range (2 ^ qs.length)).map f).length ≤ ((List.finRange 32).map (fun m => qOfMask m.val)).length := by
      simp [hlen5]
    exact subset_of_length_eq hQ_nodup hsub_img hlen_le (f s) (List.mem_map.mpr ⟨s, List.mem_range.mpr (by omega), rfl⟩)
  -- Also `f` is injective on `0..31`!
  have hf_inj : ∀ a b, a < 32 → b < 32 → f a = f b → a = b := by
    intro a b ha hb hab
    apply Classical.byContradiction; intro hne
    have hsub' : ∀ v ∈ (List.finRange 32).map (fun m => qOfMask m.val), v ∈ ((List.range 32).erase b).map f := by
      intro v hv
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hv
      obtain ⟨s, hs, hfs⟩ := hQ_sub m
      rw [hlen5] at hs
      by_cases hsb : s = b
      · subst hsb; exact List.mem_map.mpr ⟨a, (List.mem_erase_of_ne hne).mpr (List.mem_range.mpr ha), hab.trans hfs⟩
      · exact List.mem_map.mpr ⟨s, (List.mem_erase_of_ne hsb).mpr (List.mem_range.mpr hs), hfs⟩
    have hle := nodup_length_le_of_subset hQ_nodup hsub'
    rw [List.length_map, List.length_finRange, List.length_map, List.length_erase_of_mem (List.mem_range.mpr hb), List.length_range] at hle
    omega
  have hf_single : ∀ (idx : Nat) (hidx : idx < qs.length), f (1 <<< idx) = qs[idx] := by
    intro idx hidx
    have hsingle : ∀ (ys : List Nat) (a : Nat), ys.Nodup →
        ys.foldl (fun acc i => if (1 <<< idx).testBit i then acc ^^^ qs.getD i 0 else acc) a =
          if idx ∈ ys then a ^^^ qs.getD idx 0 else a := by
      intro ys; induction ys with
      | nil => intro a _; simp
      | cons y ys ihy =>
        intro a hnd; obtain ⟨hynot, hnd'⟩ := List.nodup_cons.mp hnd
        simp only [List.foldl_cons, List.mem_cons]
        have htb : (1 <<< idx).testBit y = decide (y = idx) := by
          rw [Nat.testBit_shiftLeft]
          by_cases h : y = idx
          · subst h; simp
          · by_cases hle : idx ≤ y
            · cases hm : y - idx with | zero => omega | succ _ => simp [h, hle, Nat.testBit_succ]
            · simp [h, hle]
        rw [htb]
        by_cases hy : y = idx
        · subst hy
          rw [decide_eq_true rfl]; simp only [↓reduceIte, true_or]
          rw [ihy _ hnd']; simp [hynot]
        · have hne : idx ≠ y := fun h => hy h.symm
          rw [decide_eq_false hy]; simp only [Bool.false_eq_true, ↓reduceIte, hne, false_or]
          exact ihy _ hnd'
    unfold f
    rw [hsingle (List.range qs.length) 0 List.nodup_range]
    simp [List.mem_range.mpr hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  have hf0 : f 0 = 0 := by
    unfold f
    suffices ∀ (xs : List Nat) a, xs.foldl (fun acc i => if (0 : Nat).testBit i then acc ^^^ qs.getD i 0 else acc) a = a from this _ 0
    intro xs; induction xs with | nil => intro a; rfl | cons _ _ ih => intro a; rw [List.foldl_cons, Nat.zero_testBit]; simp only [Bool.false_eq_true, ↓reduceIte]; exact ih a
  refine ⟨hlen5, ?_, ?_⟩
  · -- Nodup via injectivity of `f (1 <<< i)`
    apply nodup_of_inj_getElem
    intro i j hi hj heq
    have h1 : 1 <<< i < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ i < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
    have h2 : 1 <<< j < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ j < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
    have hsh := hf_inj (1 <<< i) (1 <<< j) h1 h2 (by rw [hf_single i hi, hf_single j hj, heq])
    have hb : (1 <<< i).testBit i = (1 <<< j).testBit i := congrArg (fun n => n.testBit i) hsh
    simp only [Nat.testBit_shiftLeft] at hb
    by_cases hij : i = j
    · exact hij
    · exfalso
      by_cases hle : j ≤ i
      · cases hm : i - j with | zero => omega | succ _ => simp [hle, hm, Nat.testBit_succ] at hb
      · simp [hle] at hb
  · intro q hq
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hq
    have h1 : 1 <<< idx < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ idx < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
    have hmem := hall_in_Q (1 <<< idx) h1
    obtain ⟨m, _, hm⟩ := List.mem_map.mp hmem
    rw [hf_single idx hidx] at hm
    refine ⟨m, ?_, hm.symm⟩
    intro hm0
    have hq0 : qs[idx] = 0 := by rw [← hm, hm0]; decide
    have hsh := hf_inj (1 <<< idx) 0 h1 (by decide) (by rw [hf_single idx hidx, hq0, hf0])
    have hpos : 0 < 1 <<< idx := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos idx
    omega

private theorem extractGates_inv : ∀ (gs : List B2Gate),
    let r := extractGates gs
    r.1 = simWires gs ∧
    r.2.1.length ≤ (gs.filter (fun g => !g.op.isLinear)).length ∧
    r.2.2.length ≤ (gs.filter (fun g => g.op.isLinear)).length ∧
    (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth ≤ 1 →
      inQuadSpan (r.2.1.map (fun n => prodQ n.a n.b)) ((r.1.getD w ⟨0, 0, false⟩).poly >>> 5)) ∧
    (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth = 0 →
      baseBm.testBit (r.1.getD w ⟨0, 0, false⟩).poly = true ∨
      ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = (r.1.getD w ⟨0, 0, false⟩).poly) ∧
    (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth ≤ 1 →
      baseBm.testBit (r.1.getD w ⟨0, 0, false⟩).poly = true ∨
      (∃ n ∈ r.2.1, n.poly = (r.1.getD w ⟨0, 0, false⟩).poly) ∨
      (∃ l ∈ r.2.2, l.poly = (r.1.getD w ⟨0, 0, false⟩).poly)) ∧
    (∀ n ∈ r.2.1,
      (baseBm.testBit n.a = true ∨ ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = n.a) ∧
      (baseBm.testBit n.b = true ∨ ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = n.b)) ∧
    (∀ i (hi : i < r.2.2.length),
      let l := r.2.2[i]
      let earlier := r.2.2.drop (i + 1)
      (l.depth = 0 →
        (baseBm.testBit l.u = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.u) ∧
        (baseBm.testBit l.v = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.v)) ∧
      ((baseBm.testBit l.u = true ∨ (∃ n ∈ r.2.1, n.poly = l.u) ∨ ∃ e ∈ earlier, e.poly = l.u) ∧
       (baseBm.testBit l.v = true ∨ (∃ n ∈ r.2.1, n.poly = l.v) ∨ ∃ e ∈ earlier, e.poly = l.v))) := by
  intro gs
  have hfold : ∀ (rest : List B2Gate) (acc : Array SimWire) (nls : List NLInfo) (lins : List LinInfo),
      (∀ w, (acc.getD w ⟨0, 0, false⟩).depth = 0 → (acc.getD w ⟨0, 0, false⟩).poly < 32) →
      (∀ w, (acc.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        inQuadSpan (nls.map (fun n => prodQ n.a n.b)) ((acc.getD w ⟨0, 0, false⟩).poly >>> 5)) →
      (∀ w, (acc.getD w ⟨0, 0, false⟩).depth = 0 →
        baseBm.testBit (acc.getD w ⟨0, 0, false⟩).poly = true ∨ ∃ l ∈ lins, l.depth = 0 ∧ l.poly = (acc.getD w ⟨0, 0, false⟩).poly) →
      (∀ w, (acc.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        baseBm.testBit (acc.getD w ⟨0, 0, false⟩).poly = true ∨
        (∃ n ∈ nls, n.poly = (acc.getD w ⟨0, 0, false⟩).poly) ∨
        (∃ l ∈ lins, l.poly = (acc.getD w ⟨0, 0, false⟩).poly)) →
      (∀ n ∈ nls,
        (baseBm.testBit n.a = true ∨ ∃ l ∈ lins, l.depth = 0 ∧ l.poly = n.a) ∧
        (baseBm.testBit n.b = true ∨ ∃ l ∈ lins, l.depth = 0 ∧ l.poly = n.b)) →
      (∀ i (hi : i < lins.length),
        let l := lins[i]
        let earlier := lins.drop (i + 1)
        (l.depth = 0 →
          (baseBm.testBit l.u = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.u) ∧
          (baseBm.testBit l.v = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.v)) ∧
        ((baseBm.testBit l.u = true ∨ (∃ n ∈ nls, n.poly = l.u) ∨ ∃ e ∈ earlier, e.poly = l.u) ∧
         (baseBm.testBit l.v = true ∨ (∃ n ∈ nls, n.poly = l.v) ∨ ∃ e ∈ earlier, e.poly = l.v))) →
      let r := rest.foldl stepExtract (acc, nls, lins)
      r.1 = rest.foldl (fun a g => a.push (stepSim a g)) acc ∧
      r.2.1.length ≤ nls.length + (rest.filter (fun g => !g.op.isLinear)).length ∧
      r.2.2.length ≤ lins.length + (rest.filter (fun g => g.op.isLinear)).length ∧
      (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        inQuadSpan (r.2.1.map (fun n => prodQ n.a n.b)) ((r.1.getD w ⟨0, 0, false⟩).poly >>> 5)) ∧
      (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth = 0 →
        baseBm.testBit (r.1.getD w ⟨0, 0, false⟩).poly = true ∨ ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = (r.1.getD w ⟨0, 0, false⟩).poly) ∧
      (∀ w, (r.1.getD w ⟨0, 0, false⟩).depth ≤ 1 →
        baseBm.testBit (r.1.getD w ⟨0, 0, false⟩).poly = true ∨
        (∃ n ∈ r.2.1, n.poly = (r.1.getD w ⟨0, 0, false⟩).poly) ∨
        (∃ l ∈ r.2.2, l.poly = (r.1.getD w ⟨0, 0, false⟩).poly)) ∧
      (∀ n ∈ r.2.1,
        (baseBm.testBit n.a = true ∨ ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = n.a) ∧
        (baseBm.testBit n.b = true ∨ ∃ l ∈ r.2.2, l.depth = 0 ∧ l.poly = n.b)) ∧
      (∀ i (hi : i < r.2.2.length),
        let l := r.2.2[i]
        let earlier := r.2.2.drop (i + 1)
        (l.depth = 0 →
          (baseBm.testBit l.u = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.u) ∧
          (baseBm.testBit l.v = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.v)) ∧
        ((baseBm.testBit l.u = true ∨ (∃ n ∈ r.2.1, n.poly = l.u) ∨ ∃ e ∈ earlier, e.poly = l.u) ∧
         (baseBm.testBit l.v = true ∨ (∃ n ∈ r.2.1, n.poly = l.v) ∨ ∃ e ∈ earlier, e.poly = l.v))) := by
    intro rest
    induction rest with
    | nil =>
      intro acc nls lins _ hq hd0 hall hnl_in hlin_in
      exact ⟨rfl, by simp, by simp, hq, hd0, hall, hnl_in, hlin_in⟩
    | cons g rest ih =>
      intro acc nls lins hd0lt hq hd0 hall hnl_in hlin_in
      simp only [List.foldl_cons]
      by_cases hlin : g.op.isLinear = true
      · simp only [stepExtract, hlin, ↓reduceDIte]
        have hflt1 : ((g :: rest).filter (fun g => !g.op.isLinear)).length = (rest.filter (fun g => !g.op.isLinear)).length := by simp [hlin]
        have hflt2 : ((g :: rest).filter (fun g => g.op.isLinear)).length = (rest.filter (fun g => g.op.isLinear)).length + 1 := by simp [hlin]
        have hsw_dep : (stepSim acc g).depth = Nat.max (acc.getD g.w1 ⟨0, 0, false⟩).depth (acc.getD g.w2 ⟨0, 0, false⟩).depth := by
          simp [stepSim, hlin]
        by_cases hd1 : (stepSim acc g).depth ≤ 1
        · simp only [hd1, ↓reduceDIte]
          let newL := mkLinInfo acc g hlin hd1
          obtain ⟨hnewL_dep, hnewL_poly, hnewL_u, hnewL_v⟩ := mkLinInfo_fields acc g hlin hd1
          have hs1d : (acc.getD g.w1 ⟨0, 0, false⟩).depth ≤ 1 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
          have hs2d : (acc.getD g.w2 ⟨0, 0, false⟩).depth ≤ 1 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
          have hres := ih (acc.push (stepSim acc g)) nls (newL :: lins)
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0lt w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0 ⊢
                    have h10 : (acc.getD g.w1 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
                    have h20 : (acc.getD g.w2 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
                    simp only [stepSim, hlin, ↓reduceIte]
                    apply xor_lt_32
                    · cases opLinCa g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hd0lt g.w1 h10
                    · cases opLinCb g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hd0lt g.w2 h20
                  · simp only [hltw, heqw, ↓reduceIte]; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hq w hdw
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte, stepSim, hlin, Nat.shiftRight_xor_distrib]
                    apply inQuadSpan_xor
                    · cases opLinCa g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact inQuadSpan_zero _ | true => simp only [↓reduceIte]; exact hq g.w1 hs1d
                    · cases opLinCb g.op with | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact inQuadSpan_zero _ | true => simp only [↓reduceIte]; exact hq g.w2 hs2d
                  · simp only [hltw, heqw, ↓reduceIte]; exact inQuadSpan_zero _)
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢
                  rcases hd0 w hw0 with hb | ⟨l, hl, hl0, hlp⟩
                  · exact Or.inl hb
                  · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, hl0, hlp⟩
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0 ⊢
                    exact Or.inr ⟨newL, List.mem_cons_self .., hnewL_dep.trans hw0, hnewL_poly⟩
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢
                  rcases hall w hdw with hb | hn | ⟨l, hl, hlp⟩
                  · exact Or.inl hb
                  · exact Or.inr (Or.inl hn)
                  · exact Or.inr (Or.inr ⟨l, List.mem_cons_of_mem _ hl, hlp⟩)
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte]
                    exact Or.inr (Or.inr ⟨newL, List.mem_cons_self .., hnewL_poly⟩)
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro n hn
                obtain ⟨ha, hb⟩ := hnl_in n hn
                refine ⟨ha.imp id (fun ⟨l, hl, h1, h2⟩ => ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩),
                        hb.imp id (fun ⟨l, hl, h1, h2⟩ => ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩)⟩)
            (by intro i hi
                cases i with
                | zero =>
                  simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero]
                  refine ⟨fun hdep0 => ?_, ?_⟩
                  · have hsw0 : (stepSim acc g).depth = 0 := hnewL_dep.symm.trans hdep0
                    have h10 : (acc.getD g.w1 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
                    have h20 : (acc.getD g.w2 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
                    rw [hnewL_u, hnewL_v]; exact ⟨hd0 g.w1 h10, hd0 g.w2 h20⟩
                  · rw [hnewL_u, hnewL_v]; exact ⟨hall g.w1 hs1d, hall g.w2 hs2d⟩
                | succ i =>
                  simp only [List.getElem_cons_succ, List.drop_succ_cons]
                  exact hlin_in i (by simp at hi; omega))
          have h1 := hres.2.1; have h2 := hres.2.2.1; dsimp only [newL] at h1 h2; simp only [List.length_cons] at h2
          exact ⟨hres.1, by rw [hflt1]; exact Nat.le_trans h1 (Nat.le_refl _), by rw [hflt2]; omega,
                 hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1, hres.2.2.2.2.2.2.1, hres.2.2.2.2.2.2.2⟩
        · simp only [hd1, ↓reduceDIte]
          have hres := ih (acc.push (stepSim acc g)) nls lins
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0lt w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hq w hdw
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hdw; exact absurd hdw hd1
                  · simp only [hltw, heqw, ↓reduceIte]; exact inQuadSpan_zero _)
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0 w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hall w hdw
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hdw; exact absurd hdw hd1
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            hnl_in hlin_in
          have h1 := hres.2.1; have h2 := hres.2.2.1
          exact ⟨hres.1, by rw [hflt1]; omega, by rw [hflt2]; omega,
                 hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1, hres.2.2.2.2.2.2.1, hres.2.2.2.2.2.2.2⟩
      · have hlinf : g.op.isLinear = false := Bool.eq_false_iff.mpr hlin
        have hflt1 : ((g :: rest).filter (fun g => !g.op.isLinear)).length = (rest.filter (fun g => !g.op.isLinear)).length + 1 := by simp [hlinf]
        have hflt2 : ((g :: rest).filter (fun g => g.op.isLinear)).length = (rest.filter (fun g => g.op.isLinear)).length := by simp [hlinf]
        have hsw_dep : (stepSim acc g).depth = Nat.max (acc.getD g.w1 ⟨0, 0, false⟩).depth (acc.getD g.w2 ⟨0, 0, false⟩).depth + 1 := by
          simp [stepSim, hlinf]
        by_cases hd1 : (stepSim acc g).depth = 1
        · have hs10 : (acc.getD g.w1 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
          have hs20 : (acc.getD g.w2 ⟨0, 0, false⟩).depth = 0 := by rw [nat_max_eq] at hsw_dep; split at hsw_dep <;> omega
          have hab : (acc.getD g.w1 ⟨0, 0, false⟩).poly < 32 ∧ (acc.getD g.w2 ⟨0, 0, false⟩).poly < 32 := ⟨hd0lt g.w1 hs10, hd0lt g.w2 hs20⟩
          have hstep : stepExtract (acc, nls, lins) g = (acc.push (stepSim acc g),
              ⟨(acc.getD g.w1 ⟨0, 0, false⟩).poly, (acc.getD g.w2 ⟨0, 0, false⟩).poly,
                xor (opLinCa g.op) (acc.getD g.w2 ⟨0, 0, false⟩).cbit, xor (opLinCb g.op) (acc.getD g.w1 ⟨0, 0, false⟩).cbit,
                (stepSim acc g).poly, hab.1, hab.2, by dsimp only [stepSim]; simp [hlinf]⟩ :: nls, lins) :=
            stepExtract_nl_eq1 acc nls lins g hlin hd1 hab
          simp only [hstep]
          let newN : NLInfo := ⟨(acc.getD g.w1 ⟨0, 0, false⟩).poly, (acc.getD g.w2 ⟨0, 0, false⟩).poly,
            xor (opLinCa g.op) (acc.getD g.w2 ⟨0, 0, false⟩).cbit, xor (opLinCb g.op) (acc.getD g.w1 ⟨0, 0, false⟩).cbit,
            (stepSim acc g).poly, hab.1, hab.2, by dsimp only [stepSim]; simp [hlinf]⟩
          have hres := ih (acc.push (stepSim acc g)) (newN :: nls) lins
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0lt w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢
                  exact inQuadSpan_mono (fun x hx => List.mem_cons_of_mem _ hx) (hq w hdw)
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte]
                    have hqeq : (stepSim acc g).poly >>> 5 = prodQ newN.a newN.b := by
                      change newN.poly >>> 5 = prodQ newN.a newN.b; rw [newN.hpoly]; exact prodPoly_quad newN.ha newN.hb _ _
                    rw [hqeq]; exact inQuadSpan_mem (List.mem_cons_self ..)
                  · simp only [hltw, heqw, ↓reduceIte]; exact inQuadSpan_zero _)
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0 w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢
                  rcases hall w hdw with hb | ⟨n, hn, hnp⟩ | hl
                  · exact Or.inl hb
                  · exact Or.inr (Or.inl ⟨n, List.mem_cons_of_mem _ hn, hnp⟩)
                  · exact Or.inr (Or.inr hl)
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte]
                    exact Or.inr (Or.inl ⟨newN, List.mem_cons_self .., rfl⟩)
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro n hn
                rcases List.mem_cons.mp hn with rfl | hn'
                · exact ⟨hd0 g.w1 hs10, hd0 g.w2 hs20⟩
                · exact hnl_in n hn')
            (by intro i hi
                obtain ⟨h0', h1u, h1v⟩ := hlin_in i hi
                refine ⟨h0', h1u.imp id (fun h => h.imp (fun ⟨n, hn, hnp⟩ => ⟨n, List.mem_cons_of_mem _ hn, hnp⟩) id),
                             h1v.imp id (fun h => h.imp (fun ⟨n, hn, hnp⟩ => ⟨n, List.mem_cons_of_mem _ hn, hnp⟩) id)⟩)
          have h1 := hres.2.1; have h2 := hres.2.2.1; dsimp only [newN] at h1 h2; simp only [List.length_cons] at h1
          exact ⟨hres.1, by rw [hflt1]; omega, by rw [hflt2]; exact Nat.le_trans h2 (Nat.le_refl _),
                 hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1, hres.2.2.2.2.2.2.1, hres.2.2.2.2.2.2.2⟩
        · have hstep := stepExtract_nl_ne1 acc nls lins g hlin hd1
          simp only [hstep]
          have hgt1 : (stepSim acc g).depth > 1 := by omega
          have hres := ih (acc.push (stepSim acc g)) nls lins
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0lt w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hq w hdw
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hdw; omega
                  · simp only [hltw, heqw, ↓reduceIte]; exact inQuadSpan_zero _)
            (by intro w hw0; rw [array_getD_push'] at hw0 ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hw0 ⊢; exact hd0 w hw0
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hw0; omega
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            (by intro w hdw; rw [array_getD_push'] at hdw ⊢
                by_cases hltw : w < acc.size
                · simp only [hltw, ↓reduceIte] at hdw ⊢; exact hall w hdw
                · by_cases heqw : w = acc.size
                  · subst heqw; simp only [Nat.lt_irrefl, ↓reduceIte] at hdw; omega
                  · simp only [hltw, heqw, ↓reduceIte]; left; decide)
            hnl_in hlin_in
          have h1 := hres.2.1; have h2 := hres.2.2.1
          exact ⟨hres.1, by rw [hflt1]; omega, by rw [hflt2]; omega,
                 hres.2.2.2.1, hres.2.2.2.2.1, hres.2.2.2.2.2.1, hres.2.2.2.2.2.2.1, hres.2.2.2.2.2.2.2⟩
  have hsim_ge5 : ∀ n : Nat, simInit.getD (n + 5) ⟨0, 0, false⟩ = ⟨0, 0, false⟩ := by
    intro n; simp only [Array.getD, simInit, Array.size_ofFn]
    have hnot : ¬ (n + 5 < 5) := by omega
    simp [hnot]
  have hres := hfold gs simInit [] []
    (by intro w _; match w with | 0 | 1 | 2 | 3 | 4 => decide | n + 5 => rw [hsim_ge5 n]; decide)
    (by intro w _; match w with
        | 0 | 1 | 2 | 3 | 4 => change inQuadSpan _ 0; exact inQuadSpan_zero _
        | n + 5 => rw [hsim_ge5 n]; change inQuadSpan _ 0; exact inQuadSpan_zero _)
    (by intro w _; left; match w with | 0 | 1 | 2 | 3 | 4 => decide | n + 5 => rw [hsim_ge5 n]; decide)
    (by intro w _; left; match w with | 0 | 1 | 2 | 3 | 4 => decide | n + 5 => rw [hsim_ge5 n]; decide)
    (by intro _ h; cases h)
    (by intro _ h; simp at h)
  simpa [extractGates, simWires] using hres


/-- Standalone contradiction theorem for the quadratic-helper case (`|pre| = 3`, `d0ClosureOk pm = true`),
    driven by `p3QuadHelperRefutedO1` and `inXorsAvO1_of_pair`. -/
private theorem p3_quad_contradiction
    (nls : List NLInfo) (lins d0Lins d1Lins : List LinInfo)
    (nlArr : Fin 5 → NLInfo) (inv A B : Fin 5 → Nat) (cArr : Fin 5 → Fin 4)
    (coordToQuad : Nat → Nat) (pm h : Nat)
    (hd0_eq : d0Lins = lins.filter (fun l => l.depth == 0))
    (hd1_eq : d1Lins = lins.filter (fun l => l.depth != 0))
    (hnl_mem : ∀ k : Fin 5, nlArr k ∈ nls)
    (hnls_eq : ∀ n ∈ nls, ∃ k : Fin 5, n = nlArr k)
    (hnl_lin : ∀ k : Fin 5, ((nlArr k).poly &&& 31) = shiftOf (A k) (B k) (cArr k).val)
    (hnl_quad : ∀ k : Fin 5, ((nlArr k).poly >>> 5) = prodQ (nlArr k).a (nlArr k).b)
    (hq_cov : ∀ j : Fin 5, inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (asconQuad j))
    (hinv_spec : ∀ j : Fin 5, inv j < 32)
    (hctq_xor : ∀ s1 s2, coordToQuad (s1 ^^^ s2) = coordToQuad s1 ^^^ coordToQuad s2)
    (hctq_inj : ∀ s1 s2, s1 < 32 → s2 < 32 → coordToQuad s1 = coordToQuad s2 → s1 = s2)
    (hctq_k : ∀ k : Fin 5, coordToQuad (1 <<< k.val) = prodQ (nlArr k).a (nlArr k).b)
    (hctq_inv : ∀ j : Fin 5, coordToQuad (inv j) = asconQuad j)
    (hctq_0 : coordToQuad 0 = 0)
    (hascon_in_d1 : ∀ j : Fin 5, asconPoly j ∈ d1Lins.map (·.poly))
    (hex_lin_in : ∀ i (hi : i < lins.length),
      let l := lins[i]
      let earlier := lins.drop (i + 1)
      (baseBm.testBit l.u = true ∨ (∃ n ∈ nls, n.poly = l.u) ∨ ∃ e ∈ earlier, e.poly = l.u) ∧
      (baseBm.testBit l.v = true ∨ (∃ n ∈ nls, n.poly = l.v) ∨ ∃ e ∈ earlier, e.poly = l.v))
    (hpm_bits32 : ∀ x, pm.testBit x = true → x < 32)
    (hd0_sub : ∀ l ∈ d0Lins, pm.testBit l.poly = true)
    (hh : ∀ x ∈ d1Lins.map (·.poly), x = h ∨ x ∈ (List.finRange 5).map asconPoly)
    (hh_lin : ¬ (h < 32))
    (href : p3QuadHelperRefutedO1 (inv ⟨0, by decide⟩) (inv ⟨1, by decide⟩) (inv ⟨2, by decide⟩)
      (inv ⟨3, by decide⟩) (inv ⟨4, by decide⟩)
      (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) (A ⟨3, by decide⟩) (B ⟨3, by decide⟩)
      (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) (baseBm ||| pm) = true) :
    False := by
  unfold p3QuadHelperRefutedO1 at href
  dsimp only at href
  have hinvOk :
      inv ⟨0, by decide⟩ = 1 ∧
      (inv ⟨1, by decide⟩ = 2 ∨ inv ⟨1, by decide⟩ = 6) ∧
      (inv ⟨2, by decide⟩ = 2 ∨ inv ⟨2, by decide⟩ = 4 ∨ inv ⟨2, by decide⟩ = 6) ∧
      inv ⟨3, by decide⟩ = 24 ∧
      inv ⟨4, by decide⟩ = 9 := by
    split at href
    · cases href
    · rename_i hok
      have hok' : (inv ⟨0, by decide⟩ == 1 && (inv ⟨1, by decide⟩ == 2 || inv ⟨1, by decide⟩ == 6) &&
          (inv ⟨2, by decide⟩ == 2 || inv ⟨2, by decide⟩ == 4 || inv ⟨2, by decide⟩ == 6) &&
          inv ⟨3, by decide⟩ == 24 && inv ⟨4, by decide⟩ == 9) = true := by
        cases hb : (inv ⟨0, by decide⟩ == 1 && (inv ⟨1, by decide⟩ == 2 || inv ⟨1, by decide⟩ == 6) &&
          (inv ⟨2, by decide⟩ == 2 || inv ⟨2, by decide⟩ == 4 || inv ⟨2, by decide⟩ == 6) &&
          inv ⟨3, by decide⟩ == 24 && inv ⟨4, by decide⟩ == 9)
        · exfalso; apply hok; rw [hb]; rfl
        · rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hok'
      exact ⟨hok'.1.1.1.1, hok'.1.1.1.2, hok'.1.1.2, hok'.1.2, hok'.2⟩
  split at href
  · cases href
  · have hmem4 : ∀ c : Fin 4, c.val ∈ [0, 1, 2, 3] := fun c => by
      rcases c with ⟨c, hc⟩; match c, hc with | 0, _ | 1, _ | 2, _ | 3, _ => simp
    have hc0 := List.all_eq_true.mp href (cArr ⟨0, by decide⟩).val (hmem4 _)
    have hc3 := List.all_eq_true.mp hc0 (cArr ⟨3, by decide⟩).val (hmem4 _)
    have hnot_y4_dir :
        (((1 <<< 5) ||| shiftOf (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) (cArr ⟨0, by decide⟩).val) ^^^
          ((8 <<< 5) ||| shiftOf (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) (cArr ⟨3, by decide⟩).val) ≠ ((9 <<< 5) ||| 30)) ∧
        ((((1 <<< 5) ||| 11) ^^^
          ((8 <<< 5) ||| shiftOf (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) (cArr ⟨3, by decide⟩).val)) ≠ ((9 <<< 5) ||| 30)) := by
      split at hc3
      · cases hc3
      · rename_i hne; simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne; exact hne
    split at hc3
    · cases hc3
    · have hc4 := List.all_eq_true.mp hc3 (cArr ⟨4, by decide⟩).val (hmem4 _)
      have hnot_y3_dir :
          (((8 <<< 5) ||| shiftOf (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) (cArr ⟨3, by decide⟩).val) ^^^
            ((16 <<< 5) ||| shiftOf (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) (cArr ⟨4, by decide⟩).val) ≠ ((24 <<< 5) ||| 31)) := by
        split at hc4
        · cases hc4
        · rename_i hne; simp only [beq_iff_eq] at hne; exact hne
      split at hc4
      · cases hc4
      · simp only [Bool.and_eq_true] at hc4
        obtain ⟨hok3, hok4⟩ := hc4
        -- Project EVERY polynomial `p` of depth ≤ 1 into 10-bit `(coord(p >>> 5) <<< 5) ||| (p &&& 31)`!
        let proj (p : Nat) : Nat :=
          let q := p >>> 5
          let s := match (List.range 32).find? (fun s => coordToQuad s == q) with | some s => s | none => 0
          (s <<< 5) ||| (p &&& 31)
        have hproj_in : ∀ p, inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (p >>> 5) →
            ∃ s < 32, coordToQuad s = p >>> 5 ∧ proj p = (s <<< 5) ||| (p &&& 31) := by
          intro p hp
          obtain ⟨sub, hsub, hqeq⟩ := hp
          have hex_s : ∃ s < 32, coordToQuad s = xorList sub := by
            clear hqeq
            induction sub with
            | nil => exact ⟨0, by decide, hctq_0⟩
            | cons q rest ih =>
              obtain ⟨s, hs32, hs⟩ := ih (fun x hx => hsub x (List.mem_cons_of_mem q hx))
              obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (hsub q (List.mem_cons_self ..))
              obtain ⟨k, rfl⟩ := hnls_eq n hn
              have h1 : 1 <<< k.val < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ k.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) k.isLt
              refine ⟨(1 <<< k.val) ^^^ s, xor_lt_32 h1 hs32, ?_⟩
              rw [hctq_xor, hctq_k k, hs]
              have hxl : xorList (prodQ (nlArr k).a (nlArr k).b :: rest) = prodQ (nlArr k).a (nlArr k).b ^^^ xorList rest := by
                have hcons : ∀ (zs : List Nat) (a : Nat), zs.foldl (· ^^^ ·) a = a ^^^ xorList zs := by
                  intro zs; induction zs with
                  | nil => intro a; simp [xorList]
                  | cons z zs ihz => intro a; simp only [List.foldl_cons, xorList] at ihz ⊢; rw [ihz (a ^^^ z), ihz (0 ^^^ z)]; simp [Nat.xor_assoc]
                unfold xorList; simp only [List.foldl_cons, Nat.zero_xor]; exact hcons rest _
              exact hxl.symm
          obtain ⟨s, hs32, hs⟩ := hex_s
          rw [hqeq] at hs
          refine ⟨s, hs32, hs, ?_⟩
          unfold proj; dsimp only
          cases hfind : (List.range 32).find? (fun u => coordToQuad u == p >>> 5) with
          | none => exact absurd (beq_iff_eq.mpr hs) (List.find?_eq_none.mp hfind s (List.mem_range.mpr hs32))
          | some u =>
            have hu32 := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
            have hueq : coordToQuad u = p >>> 5 := by simpa using List.find?_some hfind
            rw [hctq_inj u s hu32 hs32 (hueq.trans hs.symm)]
        have hproj_xor : ∀ p1 p2,
            inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (p1 >>> 5) →
            inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (p2 >>> 5) →
            proj (p1 ^^^ p2) = proj p1 ^^^ proj p2 := by
          intro p1 p2 h1 h2
          obtain ⟨s1, hs1, hq1, hp1⟩ := hproj_in p1 h1
          obtain ⟨s2, hs2, hq2, hp2⟩ := hproj_in p2 h2
          have hq12 : coordToQuad (s1 ^^^ s2) = (p1 ^^^ p2) >>> 5 := by
            rw [hctq_xor, hq1, hq2, Nat.shiftRight_xor_distrib]
          obtain ⟨s12, hs12, hq12', hp12⟩ := hproj_in (p1 ^^^ p2) (by rw [Nat.shiftRight_xor_distrib]; exact inQuadSpan_xor h1 h2)
          have hs_eq : s12 = s1 ^^^ s2 := hctq_inj s12 (s1 ^^^ s2) hs12 (xor_lt_32 hs1 hs2) (hq12'.trans hq12.symm)
          rw [hp12, hs_eq, hp1, hp2]
          apply Nat.eq_of_testBit_eq; intro bit
          simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft]
          by_cases h5 : bit < 5
          · have h31 : (31 : Nat).testBit bit = true := by
              have : (31 : Nat) = 2 ^ 5 - 1 := rfl
              rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
            have hge : ¬ (5 ≤ bit) := by omega
            simp [h31, hge]
          · have h31 : (31 : Nat).testBit bit = false := by
              have : (31 : Nat) = 2 ^ 5 - 1 := rfl
              rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h5
            have hge : 5 ≤ bit := by omega
            simp [h31, hge]
        have hproj_lt32 : ∀ x, x < 32 → proj x = x := by
          intro x hx
          have h0 : x >>> 5 = 0 := by omega
          obtain ⟨s, hs32, hs, hpx⟩ := hproj_in x (by rw [h0]; exact inQuadSpan_zero _)
          have hs0 : s = 0 := hctq_inj s 0 hs32 (by decide) (hs.trans (h0.trans hctq_0.symm))
          rw [hpx, hs0]; simp only [Nat.zero_shiftLeft, Nat.zero_or]
          apply Nat.eq_of_testBit_eq; intro bit; rw [Nat.testBit_and]
          by_cases h5 : bit < 5
          · have h31 : (31 : Nat).testBit bit = true := by
              have : (31 : Nat) = 2 ^ 5 - 1 := rfl
              rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
            simp [h31]
          · have h0' : x.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show x < 2 ^ 5 from hx) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
            simp [h0']
        have hproj_nl : ∀ k : Fin 5, proj (nlArr k).poly = ((1 <<< k.val) <<< 5) ||| shiftOf (A k) (B k) (cArr k).val := by
          intro k
          have hq : (nlArr k).poly >>> 5 = coordToQuad (1 <<< k.val) := by rw [hnl_quad k, hctq_k k]
          obtain ⟨s, hs32, hs, hpx⟩ := hproj_in (nlArr k).poly (by rw [hnl_quad k]; exact inQuadSpan_mem (List.mem_map.mpr ⟨nlArr k, hnl_mem k, rfl⟩))
          have hsk : s = 1 <<< k.val := hctq_inj s (1 <<< k.val) hs32
            (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ k.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) k.isLt) (hs.trans hq)
          rw [hpx, hsk, hnl_lin k]
        have hproj_ascon : ∀ j : Fin 5, proj (asconPoly j) = (inv j <<< 5) ||| asconLin j := by
          intro j
          have hq : asconPoly j >>> 5 = coordToQuad (inv j) := by rw [hctq_inv j]; exact asconPoly_quad j
          obtain ⟨s, hs32, hs, hpx⟩ := hproj_in (asconPoly j) (by rw [hq, hctq_inv j]; exact hq_cov j)
          have hsj : s = inv j := hctq_inj s (inv j) hs32 (hinv_spec j) (hs.trans hq)
          rw [hpx, hsj, asconPoly_lin j]
        have hbm32_all : ∀ x, (baseBm ||| pm).testBit x = true → x < 32 := by
          intro x hx; rw [Nat.testBit_or] at hx
          rcases Bool.or_eq_true_iff.mp hx with hb | hp
          · apply Classical.byContradiction; intro hge
            have hlt : baseBm < 2 ^ 32 := by decide
            have h0 : baseBm.testBit x = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 32 ≤ x)))
            rw [h0] at hb; cases hb
          · exact hpm_bits32 x hp
        have hlin_qspan : ∀ i (hi : i < lins.length), inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (lins[i].poly >>> 5) := by
          intro i hi
          have hgen : ∀ k, k ≤ lins.length → ∀ idx (hidx : idx < lins.length),
              lins.length - idx ≤ k → inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (lins[idx].poly >>> 5) := by
            intro k; induction k with
            | zero => intro _ idx hidx hle; omega
            | succ k ihk =>
              intro _ idx hidx hle
              obtain ⟨hu, hv⟩ := hex_lin_in idx hidx
              have hq_of : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (idx + 1), e.poly = x) →
                  inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) := by
                intro x hx; rcases hx with hbx | ⟨n, hn, rfl⟩ | ⟨e, he, rfl⟩
                · have hx32 : x < 32 := hbm32_all x (by simp [Nat.testBit_or, hbx])
                  rw [show x >>> 5 = 0 by omega]; exact inQuadSpan_zero _
                · obtain ⟨kk, rfl⟩ := hnls_eq n hn
                  rw [hnl_quad kk]; exact inQuadSpan_mem (List.mem_map.mpr ⟨nlArr kk, hnl_mem kk, rfl⟩)
                · obtain ⟨j', hj', heq⟩ := List.getElem_of_mem he
                  rw [List.getElem_drop] at heq; subst heq
                  exact ihk (by omega) (idx + 1 + j') (by simp at hj'; omega) (by omega)
              have hqu := hq_of _ hu; have hqv := hq_of _ hv
              have hpl := lins[idx].hpoly
              cases hix : lins[idx].isXor
              · simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl
                rcases hpl with h0 | h1 | h2
                · rw [h0]; exact inQuadSpan_zero _
                · rw [h1]; exact hqu
                · rw [h2]; exact hqv
              · simp only [hix, ↓reduceIte] at hpl
                rw [hpl, Nat.shiftRight_xor_distrib]; exact inQuadSpan_xor hqu hqv
          exact hgen lins.length (Nat.le_refl _) i hi (by omega)
        let bm0 := baseBm ||| pm
        let bmList := (List.range 32).filter (fun a => bm0.testBit a)
        let g0p := (1 <<< 5) ||| shiftOf (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) (cArr ⟨0, by decide⟩).val
        let g3p := (8 <<< 5) ||| shiftOf (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) (cArr ⟨3, by decide⟩).val
        let g4p := (16 <<< 5) ||| shiftOf (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) (cArr ⟨4, by decide⟩).val
        let y0p := (1 <<< 5) ||| 11
        let y3p := (24 <<< 5) ||| 31
        let y4p := (9 <<< 5) ||| 30
        let av0 := g0p :: g3p :: g4p :: y0p :: bmList
        let q12 (v : Nat) : Nat := (v >>> 6) &&& 3
        let q034 (v : Nat) : Nat := (v >>> 5) &&& 25
        have hq12_xor : ∀ a b, q12 (a ^^^ b) = q12 a ^^^ q12 b := by
          intro a b; unfold q12; rw [Nat.shiftRight_xor_distrib]
          apply Nat.eq_of_testBit_eq; intro bit; simp only [Nat.testBit_and, Nat.testBit_xor]
          cases (a >>> 6).testBit bit <;> cases (b >>> 6).testBit bit <;> cases (3 : Nat).testBit bit <;> rfl
        have hq034_xor : ∀ a b, q034 (a ^^^ b) = q034 a ^^^ q034 b := by
          intro a b; unfold q034; rw [Nat.shiftRight_xor_distrib]
          apply Nat.eq_of_testBit_eq; intro bit; simp only [Nat.testBit_and, Nat.testBit_xor]
          cases (a >>> 5).testBit bit <;> cases (b >>> 5).testBit bit <;> cases (25 : Nat).testBit bit <;> rfl
        have hsh_lt : ∀ k : Fin 5, shiftOf (A k) (B k) (cArr k).val < 32 := fun k => by
          rw [← hnl_lin k]; exact Nat.and_lt_two_pow _ (by decide : 31 < 2 ^ 5)
        have hq_of_or : ∀ q l, l < 32 → q12 ((q <<< 5) ||| l) = (q >>> 1) &&& 3 ∧ q034 ((q <<< 5) ||| l) = q &&& 25 := by
          intro q l hl
          have hsr : ((q <<< 5) ||| l) >>> 5 = q := by
            apply Nat.eq_of_testBit_eq; intro bit
            rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
            have hl0 : l.testBit (5 + bit) = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show l < 2 ^ 5 from hl) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
            simp [hl0]
          have hsr6 : ((q <<< 5) ||| l) >>> 6 = q >>> 1 := by
            rw [show 6 = 5 + 1 by rfl, Nat.shiftRight_add, hsr]
          exact ⟨by unfold q12; rw [hsr6], by unfold q034; rw [hsr]⟩
        have hbm0_mem : ∀ x, bm0.testBit x = true → x ∈ bmList := fun x hx =>
          List.mem_filter.mpr ⟨List.mem_range.mpr (hbm32_all x hx), hx⟩
        have hav0_q12 : ∀ v ∈ av0, q12 v = 0 ∧ (q034 v = 0 ∨ q034 v = 1 ∨ q034 v = 8 ∨ q034 v = 16) := by
          intro v hv; simp only [av0, List.mem_cons] at hv
          rcases hv with rfl | rfl | rfl | rfl | hbm_v
          · have := hq_of_or 1 _ (hsh_lt ⟨0, by decide⟩); exact ⟨by dsimp only [g0p]; rw [this.1]; rfl, Or.inr (Or.inl (by dsimp only [g0p]; rw [this.2]; rfl))⟩
          · have := hq_of_or 8 _ (hsh_lt ⟨3, by decide⟩); exact ⟨by dsimp only [g3p]; rw [this.1]; rfl, Or.inr (Or.inr (Or.inl (by dsimp only [g3p]; rw [this.2]; rfl)))⟩
          · have := hq_of_or 16 _ (hsh_lt ⟨4, by decide⟩); exact ⟨by dsimp only [g4p]; rw [this.1]; rfl, Or.inr (Or.inr (Or.inr (by dsimp only [g4p]; rw [this.2]; rfl)))⟩
          · have := hq_of_or 1 11 (by decide); exact ⟨by dsimp only [y0p]; rw [this.1]; rfl, Or.inr (Or.inl (by dsimp only [y0p]; rw [this.2]; rfl))⟩
          · have hv32 : v < 32 := List.mem_range.mp (List.mem_filter.mp hbm_v).1
            exact ⟨by unfold q12; rw [show v >>> 6 = 0 by omega]; rfl, Or.inl (by unfold q034; rw [show v >>> 5 = 0 by omega]; rfl)⟩
        have hnot_direct : inXors av0 y3p = false ∧ inXors av0 y4p = false := by
          have hg0q : q034 g0p = 1 := (hq_of_or 1 _ (hsh_lt ⟨0, by decide⟩)).2
          have hg3q : q034 g3p = 8 := (hq_of_or 8 _ (hsh_lt ⟨3, by decide⟩)).2
          have hg4q : q034 g4p = 16 := (hq_of_or 16 _ (hsh_lt ⟨4, by decide⟩)).2
          have hy0q : q034 y0p = 1 := (hq_of_or 1 11 (by decide)).2
          have hy3q : q034 y3p = 24 := by decide
          have hy4q : q034 y4p = 9 := by decide
          have hbmq : ∀ b ∈ bmList, q034 b = 0 := fun b hb => by
            have : b < 32 := List.mem_range.mp (List.mem_filter.mp hb).1
            unfold q034; rw [show b >>> 5 = 0 by omega]; rfl
          have hno : ∀ t, (t = y3p ∨ t = y4p) → ∀ u ∈ av0, ∀ v ∈ av0, u ^^^ v ≠ t := by
            intro t ht u hu v hv heq
            have hq := congrArg q034 heq; rw [hq034_xor] at hq
            simp only [av0, List.mem_cons] at hu hv
            rcases hu with rfl | rfl | rfl | rfl | hub <;> rcases hv with rfl | rfl | rfl | rfl | hvb
            · rw [hg0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rcases ht with rfl | rfl
              · rw [hg0q, hg3q, hy3q] at hq; simp at hq
              · exact hnot_y4_dir.1 heq
            · rw [hg0q, hg4q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hg0q, hy0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hg0q, hbmq _ hvb] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rcases ht with rfl | rfl
              · rw [hg3q, hg0q, hy3q] at hq; simp at hq
              · exact hnot_y4_dir.1 (Nat.xor_comm _ _ ▸ heq)
            · rw [hg3q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rcases ht with rfl | rfl
              · exact hnot_y3_dir heq
              · rw [hg3q, hg4q, hy4q] at hq; simp at hq
            · rcases ht with rfl | rfl
              · rw [hg3q, hy0q, hy3q] at hq; simp at hq
              · exact hnot_y4_dir.2 (Nat.xor_comm _ _ ▸ heq)
            · rw [hg3q, hbmq _ hvb] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hg4q, hg0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rcases ht with rfl | rfl
              · exact hnot_y3_dir (Nat.xor_comm _ _ ▸ heq)
              · rw [hg4q, hg3q, hy4q] at hq; simp at hq
            · rw [hg4q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hg4q, hy0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hg4q, hbmq _ hvb] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hy0q, hg0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rcases ht with rfl | rfl
              · rw [hy0q, hg3q, hy3q] at hq; simp at hq
              · exact hnot_y4_dir.2 heq
            · rw [hy0q, hg4q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hy0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hy0q, hbmq _ hvb] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hbmq _ hub, hg0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hbmq _ hub, hg3q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hbmq _ hub, hg4q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hbmq _ hub, hy0q] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
            · rw [hbmq _ hub, hbmq _ hvb] at hq; rcases ht with rfl | rfl <;> simp [hy3q, hy4q] at hq
          refine ⟨?_, ?_⟩
          · cases h : inXors av0 y3p; · rfl
            unfold inXors at h; rw [List.any_eq_true] at h
            obtain ⟨u, hu, hv⟩ := h; rw [List.any_eq_true] at hv
            obtain ⟨v, hv, hcond⟩ := hv; simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            exact absurd hcond.2 (hno y3p (Or.inl rfl) u hu v hv)
          · cases h : inXors av0 y4p; · rfl
            unfold inXors at h; rw [List.any_eq_true] at h
            obtain ⟨u, hu, hv⟩ := h; rw [List.any_eq_true] at hv
            obtain ⟨v, hv, hcond⟩ := hv; simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            exact absurd hcond.2 (hno y4p (Or.inr rfl) u hu v hv)
        -- Classify pre-wires
        have hclass_pre : ∀ x,
            (baseBm.testBit x = true ∨ (∃ l ∈ d0Lins, l.poly = x) ∨ (∃ n ∈ nls, n.poly = x) ∨
             x = asconPoly ⟨0, by decide⟩ ∨ x = asconPoly ⟨1, by decide⟩ ∨ x = asconPoly ⟨2, by decide⟩) →
            inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) ∧
            (proj x ∈ av0 ∨ (q12 (proj x) ≠ 0 ∧ q034 (proj x) = 0)) := by
          intro x hx
          rcases hx with hbx | ⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩ | rfl | rfl | rfl
          · have hx32 := hbm32_all x (by simp [Nat.testBit_or, hbx])
            refine ⟨by rw [show x >>> 5 = 0 by omega]; exact inQuadSpan_zero _, Or.inl ?_⟩
            rw [hproj_lt32 x hx32]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hbm0_mem x (by simp [bm0, Nat.testBit_or, hbx])))))
          · have hlpm := hd0_sub l hl; have hl32 := hpm_bits32 l.poly hlpm
            refine ⟨by rw [show l.poly >>> 5 = 0 by omega]; exact inQuadSpan_zero _, Or.inl ?_⟩
            rw [hproj_lt32 l.poly hl32]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hbm0_mem l.poly (by simp [bm0, Nat.testBit_or, hlpm])))))
          · obtain ⟨k, rfl⟩ := hnls_eq n hn
            refine ⟨by rw [hnl_quad k]; exact inQuadSpan_mem (List.mem_map.mpr ⟨nlArr k, hnl_mem k, rfl⟩), ?_⟩
            rw [hproj_nl k]
            match k with
            | ⟨0, _⟩ => exact Or.inl (by simp [av0, g0p])
            | ⟨1, _⟩ => right; have := hq_of_or 2 _ (hsh_lt ⟨1, by decide⟩); rw [show (1 <<< (1 : Nat)) = 2 by rfl]; exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
            | ⟨2, _⟩ => right; have := hq_of_or 4 _ (hsh_lt ⟨2, by decide⟩); rw [show (1 <<< (2 : Nat)) = 4 by rfl]; exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
            | ⟨3, _⟩ => exact Or.inl (by simp [av0, g3p])
            | ⟨4, _⟩ => exact Or.inl (by simp [av0, g4p])
          · refine ⟨by rw [asconPoly_quad ⟨0, by decide⟩]; exact hq_cov ⟨0, by decide⟩, Or.inl ?_⟩
            rw [hproj_ascon ⟨0, by decide⟩, hinvOk.1]; simp [av0, y0p, asconLin]
          · refine ⟨by rw [asconPoly_quad ⟨1, by decide⟩]; exact hq_cov ⟨1, by decide⟩, Or.inr ?_⟩
            rw [hproj_ascon ⟨1, by decide⟩]
            rcases hinvOk.2.1 with h2 | h6
            · rw [h2]; have := hq_of_or 2 (asconLin ⟨1, by decide⟩) (by decide); exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
            · rw [h6]; have := hq_of_or 6 (asconLin ⟨1, by decide⟩) (by decide); exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
          · refine ⟨by rw [asconPoly_quad ⟨2, by decide⟩]; exact hq_cov ⟨2, by decide⟩, Or.inr ?_⟩
            rw [hproj_ascon ⟨2, by decide⟩]
            rcases hinvOk.2.2.1 with h2 | h4 | h6
            · rw [h2]; have := hq_of_or 2 (asconLin ⟨2, by decide⟩) (by decide); exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
            · rw [h4]; have := hq_of_or 4 (asconLin ⟨2, by decide⟩) (by decide); exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
            · rw [h6]; have := hq_of_or 6 (asconLin ⟨2, by decide⟩) (by decide); exact ⟨by rw [this.1]; decide, by rw [this.2]; decide⟩
        have hex_first_of : ∀ (target : Nat), target ∈ lins.map (·.poly) →
            ∃ pos, ∃ hpos : pos < lins.length, lins[pos].poly = target ∧
              ∀ e ∈ lins.drop (pos + 1), e.poly ≠ target := by
          intro target hmem
          have hgen : ∀ (ls : List LinInfo), target ∈ ls.map (·.poly) →
              ∃ pos, ∃ hpos : pos < ls.length, ls[pos].poly = target ∧
                ∀ e ∈ ls.drop (pos + 1), e.poly ≠ target := by
            intro ls; induction ls with
            | nil => intro h; simp at h
            | cons a as ih =>
              intro h; by_cases hin : target ∈ as.map (·.poly)
              · obtain ⟨pos, hpos, hpeq, hdrop⟩ := ih hin
                exact ⟨pos + 1, by simp; omega, hpeq, fun e he => hdrop e (by simpa using he)⟩
              · have ha : a.poly = target := by
                  simp only [List.map_cons, List.mem_cons] at h
                  rcases h with h | h
                  · exact h.symm
                  · exact absurd h hin
                exact ⟨0, by simp, ha, fun e he hpe => hin (List.mem_map.mpr ⟨e, by simpa using he, hpe⟩)⟩
          exact hgen lins hmem
        have h3_in : asconPoly ⟨3, by decide⟩ ∈ lins.map (·.poly) := by
          obtain ⟨l, hl, hlp⟩ := List.mem_map.mp (hascon_in_d1 ⟨3, by decide⟩)
          rw [hd1_eq] at hl; exact List.mem_map.mpr ⟨l, (List.mem_filter.mp hl).1, hlp⟩
        have h4_in : asconPoly ⟨4, by decide⟩ ∈ lins.map (·.poly) := by
          obtain ⟨l, hl, hlp⟩ := List.mem_map.mp (hascon_in_d1 ⟨4, by decide⟩)
          rw [hd1_eq] at hl; exact List.mem_map.mpr ⟨l, (List.mem_filter.mp hl).1, hlp⟩
        obtain ⟨p3, hp3, hp3_eq, hp3_first⟩ := hex_first_of _ h3_in
        obtain ⟨p4, hp4, hp4_eq, hp4_first⟩ := hex_first_of _ h4_in
        have hnot_pre_xor : ∀ (t : Nat), (t = y3p ∨ t = y4p) →
            ∀ x1 x2,
              (proj x1 ∈ av0 ∨ (q12 (proj x1) ≠ 0 ∧ q034 (proj x1) = 0)) →
              (proj x2 ∈ av0 ∨ (q12 (proj x2) ≠ 0 ∧ q034 (proj x2) = 0)) →
              proj x1 ^^^ proj x2 ≠ t := by
          intro t ht x1 x2 h1 h2 heq
          have ht_q : q12 t = 0 ∧ (q034 t = 24 ∨ q034 t = 9) := by rcases ht with rfl | rfl <;> decide
          rcases h1 with h1a | ⟨h1n, h1z⟩ <;> rcases h2 with h2a | ⟨h2n, h2z⟩
          · by_cases heq12 : proj x1 = proj x2
            · rw [heq12, Nat.xor_self] at heq; rcases ht with rfl | rfl <;> (dsimp only [y3p, y4p] at heq; exact absurd heq (by decide))
            · have hinx : inXors av0 t = true := by
                unfold inXors; rw [List.any_eq_true]; refine ⟨proj x1, h1a, ?_⟩
                rw [List.any_eq_true]; exact ⟨proj x2, h2a, by simp [heq12, heq]⟩
              rcases ht with rfl | rfl
              · rw [hnot_direct.1] at hinx; cases hinx
              · rw [hnot_direct.2] at hinx; cases hinx
          · have := congrArg q12 heq; rw [hq12_xor, (hav0_q12 _ h1a).1, Nat.zero_xor, ht_q.1] at this; exact h2n this
          · have := congrArg q12 heq; rw [hq12_xor, (hav0_q12 _ h2a).1, Nat.xor_zero, ht_q.1] at this; exact h1n this
          · have := congrArg q034 heq; rw [hq034_xor, h1z, h2z] at this
            rcases ht_q.2 with h' | h' <;> rw [h'] at this <;> simp at this
        have hfirst_xor : ∀ (j : Fin 5) (pos : Nat) (hpos : pos < lins.length),
            (j = ⟨3, by decide⟩ ∨ j = ⟨4, by decide⟩) →
            lins[pos].poly = asconPoly j →
            (∀ e ∈ lins.drop (pos + 1), e.poly ≠ asconPoly j) →
            lins[pos].u ^^^ lins[pos].v = asconPoly j := by
          intro j pos hpos hj hpeq hne
          have hpl := lins[pos].hpoly
          cases hix : lins[pos].isXor
          · exfalso
            simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl; rw [hpeq] at hpl
            obtain ⟨hu, hv⟩ := hex_lin_in pos hpos
            have hnot_in : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (pos + 1), e.poly = x) →
                x ≠ asconPoly j := by
              intro x hx heq; subst heq
              rcases hx with hbx | ⟨n, hn, hnp⟩ | ⟨e, he, hep⟩
              · have hbf : ∀ j' : Fin 5, baseBm.testBit (asconPoly j') = false := by decide
                rw [hbf j] at hbx; cases hbx
              · rw [n.hpoly] at hnp; exact no_free_output ⟨n.a, n.ha⟩ ⟨n.b, n.hb⟩ n.ca n.cb j hnp
              · exact hne e he hep
            rcases hpl with h0 | hu' | hv'
            · exact asconPoly_ne_zero j h0
            · exact hnot_in _ hu hu'.symm
            · exact hnot_in _ hv hv'.symm
          · simp only [hix, ↓reduceIte] at hpl; rw [hpeq] at hpl; exact hpl.symm
        have hdrop_class : ∀ pos (e : LinInfo), e ∈ lins.drop (pos + 1) →
            e.poly = h ∨ e.depth = 0 ∨
            e.poly = asconPoly ⟨0, by decide⟩ ∨ e.poly = asconPoly ⟨1, by decide⟩ ∨
            e.poly = asconPoly ⟨2, by decide⟩ ∨ e.poly = asconPoly ⟨3, by decide⟩ ∨
            e.poly = asconPoly ⟨4, by decide⟩ := by
          intro pos e he
          have hel : e ∈ lins := List.mem_of_mem_drop he
          by_cases he0 : e.depth = 0
          · exact Or.inr (Or.inl he0)
          · have hmemd1 : e ∈ d1Lins := by rw [hd1_eq]; exact List.mem_filter.mpr ⟨hel, bne_iff_ne.mpr he0⟩
            rcases hh e.poly (List.mem_map.mpr ⟨e, hmemd1, rfl⟩) with rfl | hmem
            · exact Or.inl rfl
            · obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem
              rw [← hj]
              match j with
              | ⟨0, _⟩ => exact Or.inr (Or.inr (Or.inl rfl))
              | ⟨1, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              | ⟨2, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              | ⟨3, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
              | ⟨4, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
        have hdrop_sub : ∀ {a b : Nat} {e : LinInfo}, a < b → e ∈ lins.drop (b + 1) → e ∈ lins.drop (a + 1) := by
          intro a b e hlt he
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
          rw [List.getElem_drop]
          have hlt' : b + 1 + k < lins.length := by simp at hk; omega
          have : lins[b + 1 + k] = (lins.drop (a + 1))[b - a + k]'(by simp; omega) := by
            simp [List.getElem_drop, show a + 1 + (b - a + k) = b + 1 + k by omega]
          rw [this]; exact List.getElem_mem _
        have hp34_ne : p3 ≠ p4 := by
          intro heq; subst heq; rw [hp3_eq] at hp4_eq; simp [asconPoly, asconLin, asconQuad] at hp4_eq
        have hh_before : ∃ ph, ∃ hph : ph < lins.length,
            lins[ph].poly = h ∧ ph > p3 ∧ ph > p4 ∧ ∀ e ∈ lins.drop (ph + 1), e.poly ≠ h := by
          have hmust_h : ∀ (j : Fin 5) (pos : Nat) (hpos : pos < lins.length),
              (j = ⟨3, by decide⟩ ∨ j = ⟨4, by decide⟩) →
              lins[pos].poly = asconPoly j →
              (∀ e ∈ lins.drop (pos + 1), e.poly ≠ asconPoly ⟨3, by decide⟩ ∧ e.poly ≠ asconPoly ⟨4, by decide⟩) →
              h ∈ (lins.drop (pos + 1)).map (·.poly) := by
            intro j pos hpos hj hpeq hno34
            have hxor := hfirst_xor j pos hpos hj hpeq (fun e he => by rcases hj with rfl | rfl; exact (hno34 e he).1; exact (hno34 e he).2)
            obtain ⟨hu, hv⟩ := hex_lin_in pos hpos
            apply Classical.byContradiction; intro hnoh
            have hpre_of : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (pos + 1), e.poly = x) →
                inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) ∧
                (proj x ∈ av0 ∨ (q12 (proj x) ≠ 0 ∧ q034 (proj x) = 0)) := by
              intro x hx; apply hclass_pre x
              rcases hx with hbx | hn | ⟨e, he, rfl⟩
              · exact Or.inl hbx
              · exact Or.inr (Or.inr (Or.inl hn))
              · rcases hdrop_class pos e he with heh | he0 | h0 | h1 | h2 | h3 | h4
                · exact absurd (List.mem_map.mpr ⟨e, he, heh⟩) hnoh
                · exact Or.inr (Or.inl ⟨e, by rw [hd0_eq]; exact List.mem_filter.mpr ⟨List.mem_of_mem_drop he, beq_iff_eq.mpr he0⟩, rfl⟩)
                · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))
                · exact absurd h3 (hno34 e he).1
                · exact absurd h4 (hno34 e he).2
            obtain ⟨hqu, hcu⟩ := hpre_of _ hu; obtain ⟨hqv, hcv⟩ := hpre_of _ hv
            have hpx : proj lins[pos].u ^^^ proj lins[pos].v = proj (asconPoly j) := by rw [← hproj_xor _ _ hqu hqv, hxor]
            have hpt : proj (asconPoly j) = y3p ∨ proj (asconPoly j) = y4p := by
              rcases hj with rfl | rfl
              · left; rw [hproj_ascon ⟨3, by decide⟩, hinvOk.2.2.2.1]; rfl
              · right; rw [hproj_ascon ⟨4, by decide⟩, hinvOk.2.2.2.2]; rfl
            exact hnot_pre_xor _ hpt _ _ hcu hcv hpx
          have hh_in_drop : h ∈ (lins.drop (Nat.max p3 p4 + 1)).map (·.poly) := by
            by_cases hlt : p3 < p4
            · rw [show Nat.max p3 p4 = p4 by rw [nat_max_eq]; split <;> omega]
              exact hmust_h ⟨4, by decide⟩ p4 hp4 (Or.inr rfl) hp4_eq (fun e he => ⟨hp3_first e (hdrop_sub hlt he), hp4_first e he⟩)
            · rw [show Nat.max p3 p4 = p3 by rw [nat_max_eq]; split <;> omega]
              exact hmust_h ⟨3, by decide⟩ p3 hp3 (Or.inl rfl) hp3_eq (fun e he => ⟨hp3_first e he, hp4_first e (hdrop_sub (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hp34_ne.symm) he)⟩)
          have hgen : ∀ (ls : List LinInfo), h ∈ ls.map (·.poly) →
              ∃ pos, ∃ hpos : pos < ls.length, ls[pos].poly = h ∧ ∀ e ∈ ls.drop (pos + 1), e.poly ≠ h := by
            intro ls; induction ls with
            | nil => intro h'; simp at h'
            | cons a as ih =>
              intro h'; by_cases hin : h ∈ as.map (·.poly)
              · obtain ⟨pos, hpos, hpeq, hdrop⟩ := ih hin
                exact ⟨pos + 1, by simp; omega, hpeq, fun e he => hdrop e (by simpa using he)⟩
              · have ha : a.poly = h := by
                  simp only [List.map_cons, List.mem_cons] at h'
                  rcases h' with h' | h'
                  · exact h'.symm
                  · exact absurd h' hin
                exact ⟨0, by simp, ha, fun e he hpe => hin (List.mem_map.mpr ⟨e, by simpa using he, hpe⟩)⟩
          obtain ⟨off, hoff, hoff_eq, hoff_first⟩ := hgen _ hh_in_drop
          have hmax_ge : p3 ≤ Nat.max p3 p4 ∧ p4 ≤ Nat.max p3 p4 := by rw [nat_max_eq]; split <;> omega
          have hph : Nat.max p3 p4 + 1 + off < lins.length := by simp at hoff; omega
          refine ⟨Nat.max p3 p4 + 1 + off, hph, ?_, by omega, by omega, ?_⟩
          · rw [List.getElem_drop] at hoff_eq; exact hoff_eq
          · intro e he
            have he' : e ∈ (lins.drop (Nat.max p3 p4 + 1)).drop (off + 1) := by
              rw [List.drop_drop, show Nat.max p3 p4 + 1 + (off + 1) = Nat.max p3 p4 + 1 + off + 1 by omega]; exact he
            exact hoff_first e he'
        obtain ⟨ph, hph, hph_eq, hph_gt3, hph_gt4, hph_first⟩ := hh_before
        have hpre_before_ph : ∀ x,
            (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (ph + 1), e.poly = x) →
            inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) ∧
            (proj x ∈ av0 ∨ (q12 (proj x) ≠ 0 ∧ q034 (proj x) = 0)) := by
          intro x hx; apply hclass_pre x
          rcases hx with hbx | hn | ⟨e, he, rfl⟩
          · exact Or.inl hbx
          · exact Or.inr (Or.inr (Or.inl hn))
          · rcases hdrop_class ph e he with heh | he0 | h0 | h1 | h2 | h3 | h4
            · exact absurd heh (hph_first e he)
            · exact Or.inr (Or.inl ⟨e, by rw [hd0_eq]; exact List.mem_filter.mpr ⟨List.mem_of_mem_drop he, beq_iff_eq.mpr he0⟩, rfl⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))
            · exact absurd h3 (hp3_first e (hdrop_sub hph_gt3 he))
            · exact absurd h4 (hp4_first e (hdrop_sub hph_gt4 he))
        have hproj_h_cases :
            (∃ u ∈ av0, ∃ v ∈ av0, proj h = u ^^^ v) ∨
            (q12 (proj h) ≠ 0 ∧ (q034 (proj h) = 0 ∨ q034 (proj h) = 1 ∨ q034 (proj h) = 8 ∨ q034 (proj h) = 16)) ∨
            q034 (proj h) = 0 ∨ proj h ∈ av0 := by
          obtain ⟨hu, hv⟩ := hex_lin_in ph hph
          obtain ⟨hqu, hcu⟩ := hpre_before_ph _ hu; obtain ⟨hqv, hcv⟩ := hpre_before_ph _ hv
          have hpl := lins[ph].hpoly; rw [hph_eq] at hpl
          cases hix : lins[ph].isXor
          · simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl
            rcases hpl with h0 | hu' | hv'
            · right; right; left; rw [h0, hproj_lt32 0 (by decide)]; decide
            · rw [hu']; rcases hcu with h1 | ⟨h1, h2⟩
              · exact Or.inr (Or.inr (Or.inr h1))
              · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
            · rw [hv']; rcases hcv with h1 | ⟨h1, h2⟩
              · exact Or.inr (Or.inr (Or.inr h1))
              · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
          · simp only [hix, ↓reduceIte] at hpl
            have hpx : proj h = proj lins[ph].u ^^^ proj lins[ph].v := by rw [hpl, hproj_xor _ _ hqu hqv]
            rcases hcu with h1a | ⟨h1n, h1z⟩ <;> rcases hcv with h2a | ⟨h2n, h2z⟩
            · exact Or.inl ⟨proj lins[ph].u, h1a, proj lins[ph].v, h2a, hpx⟩
            · right; left; rw [hpx, hq12_xor, hq034_xor, (hav0_q12 _ h1a).1, Nat.zero_xor, h2z, Nat.xor_zero]
              exact ⟨h2n, (hav0_q12 _ h1a).2⟩
            · right; left; rw [hpx, hq12_xor, hq034_xor, (hav0_q12 _ h2a).1, Nat.xor_zero, h1z, Nat.zero_xor]
              exact ⟨h1n, (hav0_q12 _ h2a).2⟩
            · right; right; left; rw [hpx, hq034_xor, h1z, h2z]; rfl
        have h0_av0 : 0 ∈ av0 :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (hbm0_mem 0 (by dsimp only [bm0]; rw [Nat.testBit_or, show baseBm.testBit 0 = true by decide]; rfl)))))
        have hfirst_bad_of_q12 : q12 (proj h) ≠ 0 →
            (q034 (proj h) = 0 ∨ q034 (proj h) = 1 ∨ q034 (proj h) = 8 ∨ q034 (proj h) = 16) → False := by
          intro hq12h hq034h
          have hbad : ∀ (j : Fin 5) (pos : Nat) (hpos : pos < lins.length),
              (j = ⟨3, by decide⟩ ∨ j = ⟨4, by decide⟩) →
              lins[pos].poly = asconPoly j →
              (∀ e ∈ lins.drop (pos + 1), e.poly ≠ asconPoly ⟨3, by decide⟩ ∧ e.poly ≠ asconPoly ⟨4, by decide⟩) → False := by
            intro j pos hpos hj hpeq hno34
            have hxor := hfirst_xor j pos hpos hj hpeq (fun e he => by rcases hj with rfl | rfl; exact (hno34 e he).1; exact (hno34 e he).2)
            obtain ⟨hu, hv⟩ := hex_lin_in pos hpos
            have hcl : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (pos + 1), e.poly = x) →
                inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) ∧
                (x = h ∨ proj x ∈ av0 ∨ (q12 (proj x) ≠ 0 ∧ q034 (proj x) = 0)) := by
              intro x hx
              rcases hx with hbx | hn | ⟨e, he, rfl⟩
              · have := hclass_pre x (Or.inl hbx); exact ⟨this.1, Or.inr this.2⟩
              · have := hclass_pre x (Or.inr (Or.inr (Or.inl hn))); exact ⟨this.1, Or.inr this.2⟩
              · rcases hdrop_class pos e he with heh | he0 | h0 | h1 | h2 | h3 | h4
                · subst heh; exact ⟨by rw [← hph_eq]; exact hlin_qspan ph hph, Or.inl rfl⟩
                · have := hclass_pre e.poly (Or.inr (Or.inl ⟨e, by rw [hd0_eq]; exact List.mem_filter.mpr ⟨List.mem_of_mem_drop he, beq_iff_eq.mpr he0⟩, rfl⟩)); exact ⟨this.1, Or.inr this.2⟩
                · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inl h0)))); exact ⟨this.1, Or.inr this.2⟩
                · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))); exact ⟨this.1, Or.inr this.2⟩
                · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))); exact ⟨this.1, Or.inr this.2⟩
                · exact absurd h3 (hno34 e he).1
                · exact absurd h4 (hno34 e he).2
            obtain ⟨hqu, hcu⟩ := hcl _ hu; obtain ⟨hqv, hcv⟩ := hcl _ hv
            have hpx : proj lins[pos].u ^^^ proj lins[pos].v = proj (asconPoly j) := by rw [← hproj_xor _ _ hqu hqv, hxor]
            have ht : proj (asconPoly j) = y3p ∨ proj (asconPoly j) = y4p := by
              rcases hj with rfl | rfl
              · left; rw [hproj_ascon ⟨3, by decide⟩, hinvOk.2.2.2.1]; rfl
              · right; rw [hproj_ascon ⟨4, by decide⟩, hinvOk.2.2.2.2]; rfl
            have ht_q : q12 (proj (asconPoly j)) = 0 ∧ (q034 (proj (asconPoly j)) = 24 ∨ q034 (proj (asconPoly j)) = 9) := by
              rcases ht with h' | h' <;> rw [h'] <;> decide
            rcases hcu with huh | h1 <;> rcases hcv with hvh | h2
            · rw [huh, hvh, Nat.xor_self] at hpx
              rcases ht with h' | h'
              · rw [h'] at hpx; exact absurd hpx (by dsimp only [y3p]; decide)
              · rw [h'] at hpx; exact absurd hpx (by dsimp only [y4p]; decide)
            · rw [huh] at hpx
              rcases h2 with h2a | ⟨_, h2z⟩
              · have := congrArg q12 hpx; rw [hq12_xor, (hav0_q12 _ h2a).1, Nat.xor_zero, ht_q.1] at this; exact hq12h this
              · have := congrArg q034 hpx; rw [hq034_xor, h2z, Nat.xor_zero] at this
                rcases hq034h with h' | h' | h' | h' <;> rw [h'] at this <;>
                (rcases ht_q.2 with ht' | ht' <;> rw [ht'] at this <;> simp at this)
            · rw [hvh] at hpx
              rcases h1 with h1a | ⟨_, h1z⟩
              · have := congrArg q12 hpx; rw [hq12_xor, (hav0_q12 _ h1a).1, Nat.zero_xor, ht_q.1] at this; exact hq12h this
              · have := congrArg q034 hpx; rw [hq034_xor, h1z, Nat.zero_xor] at this
                rcases hq034h with h' | h' | h' | h' <;> rw [h'] at this <;>
                (rcases ht_q.2 with ht' | ht' <;> rw [ht'] at this <;> simp at this)
            · exact hnot_pre_xor _ ht _ _ h1 h2 hpx
          by_cases hlt : p3 < p4
          · exact hbad ⟨4, by decide⟩ p4 hp4 (Or.inr rfl) hp4_eq (fun e he => ⟨hp3_first e (hdrop_sub hlt he), hp4_first e he⟩)
          · exact hbad ⟨3, by decide⟩ p3 hp3 (Or.inl rfl) hp3_eq (fun e he => ⟨hp3_first e he, hp4_first e (hdrop_sub (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hp34_ne.symm) he)⟩)
        have hh_eq_av0_xor : ∃ u ∈ av0, ∃ v ∈ av0, proj h = u ^^^ v := by
          rcases hproj_h_cases with hex | ⟨hq12h, hq034h⟩ | hq034h0 | hmem_av0
          · exact hex
          · exact False.elim (hfirst_bad_of_q12 hq12h hq034h)
          · exfalso
            by_cases hq12z : q12 (proj h) = 0
            · obtain ⟨s, hs32, hs, hph_p⟩ := hproj_in h (by rw [← hph_eq]; exact hlin_qspan ph hph)
              have hs0 : s = 0 := by
                have hsr : proj h >>> 5 = s := by
                  rw [hph_p]; apply Nat.eq_of_testBit_eq; intro bit
                  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
                  have h31 : (h &&& 31).testBit (5 + bit) = false :=
                    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (by decide : 31 < 2 ^ 5))
                      (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
                  simp [h31]
                have h1 : (s >>> 1) &&& 3 = 0 := by unfold q12 at hq12z; rw [show 6 = 5 + 1 by rfl, Nat.shiftRight_add, hsr] at hq12z; exact hq12z
                have h2 : s &&& 25 = 0 := by unfold q034 at hq034h0; rw [hsr] at hq034h0; exact hq034h0
                have : ∀ n : Fin 32, (n.val >>> 1) &&& 3 = 0 → n.val &&& 25 = 0 → n.val = 0 := by decide
                exact this ⟨s, hs32⟩ h1 h2
              rw [hs0, hctq_0] at hs
              exact hh_lin (by omega)
            · exact hfirst_bad_of_q12 hq12z (Or.inl hq034h0)
          · exact ⟨proj h, hmem_av0, 0, h0_av0, by simp⟩
        obtain ⟨hu_v, hhu_mem, hv_v, hhv_mem, hproj_h_eq⟩ := hh_eq_av0_xor
        have hq12_hp : q12 (proj h) = 0 := by
          rw [hproj_h_eq, hq12_xor, (hav0_q12 _ hhu_mem).1, (hav0_q12 _ hhv_mem).1]; rfl
        have hph_ne0 : proj h ≠ 0 := by
          intro hz
          obtain ⟨s, hs32, hs, hph_p⟩ := hproj_in h (by rw [← hph_eq]; exact hlin_qspan ph hph)
          rw [hz] at hph_p
          have hs0 : s = 0 := by
            have := congrArg (fun x => x >>> 5) hph_p.symm
            have hsr : ((s <<< 5) ||| (h &&& 31)) >>> 5 = s := by
              apply Nat.eq_of_testBit_eq; intro bit; rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
              have h31 : (h &&& 31).testBit (5 + bit) = false :=
                Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (by decide : 31 < 2 ^ 5))
                  (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
              simp [h31]
            rw [hsr] at this; exact this
          rw [hs0, hctq_0] at hs; exact hh_lin (by omega)
        have hhu_ne_hv : hu_v ≠ hv_v := by intro heq; subst heq; rw [Nat.xor_self] at hproj_h_eq; exact hph_ne0 hproj_h_eq
        have hinO1 : inXorsAvO1 g0p g3p g4p y0p bm0 (proj h) = true := by
          rw [hproj_h_eq]
          exact inXorsAvO1_of_pair (hsh_lt ⟨0, by decide⟩) (hsh_lt ⟨3, by decide⟩) (hsh_lt ⟨4, by decide⟩)
            hbm32_all hhu_mem hhv_mem hhu_ne_hv
        -- Reachability lemma
        have hreach : ∀ (j : Fin 5) (pos : Nat) (hpos : pos < lins.length) (extra : List Nat),
            (j = ⟨3, by decide⟩ ∨ j = ⟨4, by decide⟩) →
            lins[pos].poly = asconPoly j →
            (∀ e ∈ lins.drop (pos + 1), e.poly ≠ asconPoly j) →
            (∀ e ∈ lins.drop (pos + 1), e.poly = asconPoly ⟨3, by decide⟩ → y3p ∈ extra) →
            (∀ e ∈ lins.drop (pos + 1), e.poly = asconPoly ⟨4, by decide⟩ → y4p ∈ extra) →
            (∀ v ∈ extra, q12 v = 0) →
            inXors (extra ++ proj h :: av0) (proj (asconPoly j)) = true := by
          intro j pos hpos extra hj hpeq hnej h3ex h4ex hex_q12
          have hxor := hfirst_xor j pos hpos hj hpeq hnej
          obtain ⟨hu, hv⟩ := hex_lin_in pos hpos
          have hcl : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (pos + 1), e.poly = x) →
              inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (x >>> 5) ∧
              (proj x ∈ extra ++ proj h :: av0 ∨ (q12 (proj x) ≠ 0 ∧ q034 (proj x) = 0)) := by
            intro x hx
            rcases hx with hbx | hn | ⟨e, he, rfl⟩
            · have := hclass_pre x (Or.inl hbx); exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
            · have := hclass_pre x (Or.inr (Or.inr (Or.inl hn))); exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
            · rcases hdrop_class pos e he with heh | he0 | h0 | h1 | h2 | h3 | h4
              · subst heh; exact ⟨by rw [← hph_eq]; exact hlin_qspan ph hph, Or.inl (List.mem_append_right _ (List.mem_cons_self ..))⟩
              · have := hclass_pre e.poly (Or.inr (Or.inl ⟨e, by rw [hd0_eq]; exact List.mem_filter.mpr ⟨List.mem_of_mem_drop he, beq_iff_eq.mpr he0⟩, rfl⟩))
                exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
              · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inl h0)))); exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
              · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))); exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
              · have := hclass_pre e.poly (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))); exact ⟨this.1, this.2.imp (fun h' => List.mem_append_right _ (List.mem_cons_of_mem _ h')) id⟩
              · refine ⟨by rw [h3, asconPoly_quad ⟨3, by decide⟩]; exact hq_cov ⟨3, by decide⟩, Or.inl (List.mem_append_left _ ?_)⟩
                rw [h3, hproj_ascon ⟨3, by decide⟩, hinvOk.2.2.2.1]; exact h3ex e he h3
              · refine ⟨by rw [h4, asconPoly_quad ⟨4, by decide⟩]; exact hq_cov ⟨4, by decide⟩, Or.inl (List.mem_append_left _ ?_)⟩
                rw [h4, hproj_ascon ⟨4, by decide⟩, hinvOk.2.2.2.2]; exact h4ex e he h4
          obtain ⟨hqu, hcu⟩ := hcl _ hu; obtain ⟨hqv, hcv⟩ := hcl _ hv
          have hpx : proj lins[pos].u ^^^ proj lins[pos].v = proj (asconPoly j) := by rw [← hproj_xor _ _ hqu hqv, hxor]
          have ht : proj (asconPoly j) = y3p ∨ proj (asconPoly j) = y4p := by
            rcases hj with rfl | rfl
            · left; rw [hproj_ascon ⟨3, by decide⟩, hinvOk.2.2.2.1]; rfl
            · right; rw [hproj_ascon ⟨4, by decide⟩, hinvOk.2.2.2.2]; rfl
          have ht_q : q12 (proj (asconPoly j)) = 0 ∧ (q034 (proj (asconPoly j)) = 24 ∨ q034 (proj (asconPoly j)) = 9) := by
            rcases ht with h' | h' <;> rw [h'] <;> decide
          have hlist_q12 : ∀ v ∈ extra ++ proj h :: av0, q12 v = 0 := by
            intro v hv; rcases List.mem_append.mp hv with h' | h'
            · exact hex_q12 v h'
            · rcases List.mem_cons.mp h' with rfl | h'
              · exact hq12_hp
              · exact (hav0_q12 v h').1
          rcases hcu with h1 | ⟨h1n, h1z⟩ <;> rcases hcv with h2 | ⟨h2n, h2z⟩
          · by_cases heq12 : proj lins[pos].u = proj lins[pos].v
            · rw [heq12, Nat.xor_self] at hpx
              rcases ht with h' | h'
              · rw [h'] at hpx; exact absurd hpx (by dsimp only [y3p]; decide)
              · rw [h'] at hpx; exact absurd hpx (by dsimp only [y4p]; decide)
            · unfold inXors; rw [List.any_eq_true]; refine ⟨proj lins[pos].u, h1, ?_⟩
              rw [List.any_eq_true]; exact ⟨proj lins[pos].v, h2, by simp [heq12, hpx]⟩
          · exfalso; have := congrArg q12 hpx; rw [hq12_xor, hlist_q12 _ h1, Nat.zero_xor, ht_q.1] at this; exact h2n this
          · exfalso; have := congrArg q12 hpx; rw [hq12_xor, hlist_q12 _ h2, Nat.xor_zero, ht_q.1] at this; exact h1n this
          · exfalso; have := congrArg q034 hpx; rw [hq034_xor, h1z, h2z] at this
            rcases ht_q.2 with h' | h' <;> rw [h'] at this <;> simp at this
        -- Helper: unpack `inXors (proj h :: av0) t` when `inXors av0 t = false`
        have hunpack1 : ∀ t, inXors av0 t = false → inXors (proj h :: av0) t = true →
            ∃ w1 ∈ av0, proj h = t ^^^ w1 := by
          intro t hno hin
          unfold inXors at hin; rw [List.any_eq_true] at hin
          obtain ⟨a, ha, hb⟩ := hin; rw [List.any_eq_true] at hb
          obtain ⟨b, hb, hcond⟩ := hb; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
          rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
          · exact absurd rfl hcond.1
          · exact ⟨b, hb', by rw [← hcond.2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩
          · exact ⟨a, ha', by rw [← hcond.2, Nat.xor_comm a (proj h), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]⟩
          · exfalso
            have : inXors av0 t = true := by
              unfold inXors; rw [List.any_eq_true]; exact ⟨a, ha', List.any_eq_true.mpr ⟨b, hb', by simp [hcond.1, hcond.2]⟩⟩
            rw [hno] at this; cases this
        -- Helper: unpack `inXors (t1 :: proj h :: av0) t2` when `inXors av0 t2 = false` and `proj h = t1 ^^^ w1` with `w1 ∈ av0` (`w1 ≠ t2`)
        have hunpack2 : ∀ t1 t2 w1, w1 ∈ av0 → (t2 = y3p ∨ t2 = y4p) → proj h = t1 ^^^ w1 →
            inXors av0 t2 = false → inXors (t1 :: proj h :: av0) t2 = true →
            ∃ w2 ∈ av0, proj h ^^^ w2 = t2 ∨ t1 ^^^ w2 = t2 := by
          intro t1 t2 w1 hw1 ht2 hphw hno hin
          have hw1_ne : w1 ≠ t2 := by
            intro heq; subst heq
            have hq := (hav0_q12 w1 hw1).2
            have hy3 : q034 y3p = 24 := by decide
            have hy4 : q034 y4p = 9 := by decide
            rcases ht2 with rfl | rfl
            · rw [hy3] at hq; omega
            · rw [hy4] at hq; omega
          unfold inXors at hin; rw [List.any_eq_true] at hin
          obtain ⟨a, ha, hb⟩ := hin; rw [List.any_eq_true] at hb
          obtain ⟨b, hb, hcond⟩ := hb; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
          rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
          · exact absurd rfl hcond.1
          · rcases List.mem_cons.mp hb' with rfl | hb''
            · exfalso; apply hw1_ne
              rw [hphw, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hcond; exact hcond.2
            · exact ⟨b, hb'', Or.inr hcond.2⟩
          · rcases List.mem_cons.mp ha' with rfl | ha''
            · exfalso; apply hw1_ne
              rw [Nat.xor_comm, hphw, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hcond; exact hcond.2
            · exact ⟨a, ha'', Or.inr (by rw [Nat.xor_comm]; exact hcond.2)⟩
          · rcases List.mem_cons.mp ha' with rfl | ha'' <;> rcases List.mem_cons.mp hb' with rfl | hb''
            · exact absurd rfl hcond.1
            · exact ⟨b, hb'', Or.inl hcond.2⟩
            · exact ⟨a, ha'', Or.inl (Nat.xor_comm a (proj h) ▸ hcond.2)⟩
            · exfalso
              have : inXors av0 t2 = true := by
                unfold inXors; rw [List.any_eq_true]; exact ⟨a, ha'', List.any_eq_true.mpr ⟨b, hb'', by simp [hcond.1, hcond.2]⟩⟩
              rw [hno] at this; cases this
        have hy3_eq : proj (asconPoly ⟨3, by decide⟩) = y3p := by rw [hproj_ascon ⟨3, by decide⟩, hinvOk.2.2.2.1]; rfl
        have hy4_eq : proj (asconPoly ⟨4, by decide⟩) = y4p := by rw [hproj_ascon ⟨4, by decide⟩, hinvOk.2.2.2.2]; rfl
        by_cases hlt : p3 < p4
        · -- `p4` first, then `p3`! Contradicts `hok4`!
          have hr4 : inXors (proj h :: av0) y4p = true := by
            rw [← hy4_eq]
            exact hreach ⟨4, by decide⟩ p4 hp4 [] (Or.inr rfl) hp4_eq hp4_first
              (fun e he he3 => absurd he3 (hp3_first e (hdrop_sub hlt he)))
              (fun e he he4 => absurd he4 (hp4_first e he)) (fun _ h' => by cases h')
          have hr3 : inXors (y4p :: proj h :: av0) y3p = true := by
            rw [← hy3_eq]
            exact hreach ⟨3, by decide⟩ p3 hp3 [y4p] (Or.inl rfl) hp3_eq hp3_first
              (fun e he he3 => absurd he3 (hp3_first e he))
              (fun _ _ _ => List.mem_cons_self ..) (fun v hv => by rw [List.mem_singleton.mp hv]; decide)
          obtain ⟨w1, hw1, hphw⟩ := hunpack1 y4p hnot_direct.2 hr4
          obtain ⟨w2, hw2, hw2eq⟩ := hunpack2 y4p y3p w1 hw1 (Or.inl rfl) hphw hnot_direct.1 hr3
          have hcert := List.all_eq_true.mp hok4 w1 hw1
          rw [← hphw] at hcert
          have hany : (av0.any fun w2 => (proj h ^^^ w2 == y3p) || (y4p ^^^ w2 == y3p)) = true := by
            rw [List.any_eq_true]; refine ⟨w2, hw2, ?_⟩
            rcases hw2eq with h' | h' <;> simp [h']
          rw [if_pos hany, hinO1] at hcert
          cases hcert
        · -- `p3` first, then `p4`! Contradicts `hok3`!
          have hr3 : inXors (proj h :: av0) y3p = true := by
            rw [← hy3_eq]
            exact hreach ⟨3, by decide⟩ p3 hp3 [] (Or.inl rfl) hp3_eq hp3_first
              (fun e he he3 => absurd he3 (hp3_first e he))
              (fun e he he4 => absurd he4 (hp4_first e (hdrop_sub (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hp34_ne.symm) he))) (fun _ h' => by cases h')
          have hr4 : inXors (y3p :: proj h :: av0) y4p = true := by
            rw [← hy4_eq]
            exact hreach ⟨4, by decide⟩ p4 hp4 [y3p] (Or.inr rfl) hp4_eq hp4_first
              (fun _ _ _ => List.mem_cons_self ..)
              (fun e he he4 => absurd he4 (hp4_first e he)) (fun v hv => by rw [List.mem_singleton.mp hv]; decide)
          obtain ⟨w1, hw1, hphw⟩ := hunpack1 y3p hnot_direct.1 hr3
          obtain ⟨w2, hw2, hw2eq⟩ := hunpack2 y3p y4p w1 hw1 (Or.inr rfl) hphw hnot_direct.2 hr4
          have hcert := List.all_eq_true.mp hok3 w1 hw1
          rw [← hphw] at hcert
          have hany : (av0.any fun w2 => (proj h ^^^ w2 == y4p) || (y3p ^^^ w2 == y4p)) = true := by
            rw [List.any_eq_true]; refine ⟨w2, hw2, ?_⟩
            rcases hw2eq with h' | h' <;> simp [h']
          rw [if_pos hany, hinO1] at hcert
          cases hcert


/-- Standalone contradiction theorem for any zero-helper or linear-helper configuration
    when `zeroHelperRefuted inv T0 T1 4294967295 = true`. -/
private theorem no_lin_helper_contradiction
    (nls : List NLInfo) (lins d0Lins d1Lins : List LinInfo)
    (nlArr : Fin 5 → NLInfo) (inv T0 T1 : Fin 5 → Nat) (cArr' : Fin 5 → Fin 4)
    (coordToQuad : Nat → Nat)
    (hd0_eq : d0Lins = lins.filter (fun l => l.depth == 0))
    (hd1_eq : d1Lins = lins.filter (fun l => l.depth != 0))
    (hnls_eq : ∀ n ∈ nls, ∃ k : Fin 5, n = nlArr k)
    (hT_lt : ∀ k : Fin 5, T0 k < 32 ∧ T1 k < 32)
    (hnl_lin' : ∀ k : Fin 5, ((nlArr k).poly &&& 31) = shiftOf (T0 k) (T1 k) (cArr' k).val)
    (hnl_quad : ∀ k : Fin 5, ((nlArr k).poly >>> 5) = prodQ (nlArr k).a (nlArr k).b)
    (hinv_spec : ∀ j : Fin 5, inv j < 32)
    (hctq_xor : ∀ s1 s2, coordToQuad (s1 ^^^ s2) = coordToQuad s1 ^^^ coordToQuad s2)
    (hctq_inj : ∀ s1 s2, s1 < 32 → s2 < 32 → coordToQuad s1 = coordToQuad s2 → s1 = s2)
    (hctq_k : ∀ k : Fin 5, coordToQuad (1 <<< k.val) = prodQ (nlArr k).a (nlArr k).b)
    (hctq_inv : ∀ j : Fin 5, coordToQuad (inv j) = asconQuad j)
    (hctq_0 : coordToQuad 0 = 0)
    (hascon_in_d1 : ∀ j : Fin 5, asconPoly j ∈ d1Lins.map (·.poly))
    (hex_lin_in : ∀ i (hi : i < lins.length),
      let l := lins[i]
      let earlier := lins.drop (i + 1)
      (l.depth = 0 →
        (baseBm.testBit l.u = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.u) ∧
        (baseBm.testBit l.v = true ∨ ∃ e ∈ earlier, e.depth = 0 ∧ e.poly = l.v)) ∧
      ((baseBm.testBit l.u = true ∨ (∃ n ∈ nls, n.poly = l.u) ∨ ∃ e ∈ earlier, e.poly = l.u) ∧
       (baseBm.testBit l.v = true ∨ (∃ n ∈ nls, n.poly = l.v) ∨ ∃ e ∈ earlier, e.poly = l.v)))
    (hzh_raw : zeroHelperRefuted inv T0 T1 4294967295 = true)
    (hd1_lin : ∀ l ∈ d1Lins, l.poly < 32 ∨ ∃ j : Fin 5, l.poly = asconPoly j) :
    False := by
  have hbm_all32 : ∀ x, (4294967295 : Nat).testBit x = true ↔ x < 32 := by
    intro x; have : (4294967295 : Nat) = 2 ^ 32 - 1 := rfl
    rw [this, Nat.testBit_two_pow_sub_one]; simp
  have hbm32 : ∀ x, baseBm.testBit x = true → x < 32 := by
    intro x hx; apply Classical.byContradiction; intro hge
    have hlt : baseBm < 2 ^ 32 := by decide
    have h0 : baseBm.testBit x = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 32 ≤ x)))
    rw [h0] at hx; cases hx
  have hd0_lt32 : ∀ l ∈ d0Lins, l.poly < 32 := by
    have hall32 : ∀ k, k ≤ lins.length → ∀ i (hi : i < lins.length),
        lins.length - i ≤ k → lins[i].depth = 0 → lins[i].poly < 32 := by
      intro k; induction k with
      | zero => intro _ i hi hle; omega
      | succ k ihk =>
        intro _ i hi hle hdi0
        obtain ⟨h0', _⟩ := hex_lin_in i hi
        obtain ⟨hu', hv'⟩ := h0' hdi0
        have hget32 : ∀ x, (baseBm.testBit x = true ∨ ∃ e ∈ lins.drop (i + 1), e.depth = 0 ∧ e.poly = x) → x < 32 := by
          intro x hx; rcases hx with hbx | ⟨e, he, he0, rfl⟩
          · exact hbm32 x hbx
          · obtain ⟨j', hj', heq⟩ := List.getElem_of_mem he
            rw [List.getElem_drop] at heq; subst heq
            exact ihk (by omega) (i + 1 + j') (by simp at hj'; omega) (by omega) he0
        have hu32 := hget32 _ hu'; have hv32 := hget32 _ hv'
        have hpl := lins[i].hpoly
        cases hix : lins[i].isXor
        · simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl
          rcases hpl with h | h | h
          · rw [h]; decide
          · rw [h]; exact hu32
          · rw [h]; exact hv32
        · simp only [hix, ↓reduceIte] at hpl; rw [hpl]; exact xor_lt_32 hu32 hv32
    intro l hl
    rw [hd0_eq] at hl
    obtain ⟨hl_in, hl0⟩ := List.mem_filter.mp hl
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hl_in
    exact hall32 lins.length (Nat.le_refl _) idx hidx (by omega) (beq_iff_eq.mp hl0)
  have hfalse := zeroHelperRefuted_sound inv T0 T1 4294967295 cArr'
    (fun x hx => (hbm_all32 x).mp hx)
    (fun k => (hT_lt k).1) (fun k => (hT_lt k).2) hinv_spec
    (fun j1 j2 hne heq => hne (asconQuad_inj j1 j2 ((hctq_inv j1).symm.trans (by rw [heq]; exact hctq_inv j2))))
    (by
      intro j
      have hex_first : ∀ (ls : List LinInfo), asconPoly j ∈ ls.map (·.poly) →
          ∃ pos, ∃ hpos : pos < ls.length, ls[pos].poly = asconPoly j ∧
            ∀ e ∈ ls.drop (pos + 1), e.poly ≠ asconPoly j := by
        intro ls; induction ls with
        | nil => intro h; simp at h
        | cons a as ih =>
          intro h; by_cases hin : asconPoly j ∈ as.map (·.poly)
          · obtain ⟨pos, hpos, hpeq, hdrop⟩ := ih hin
            exact ⟨pos + 1, by simp; omega, hpeq, fun e he => hdrop e (by simpa using he)⟩
          · have ha : a.poly = asconPoly j := by
              simp only [List.map_cons, List.mem_cons] at h
              rcases h with h | h
              · exact h.symm
              · exact absurd h hin
            exact ⟨0, by simp, ha, fun e he hpe => hin (List.mem_map.mpr ⟨e, by simpa using he, hpe⟩)⟩
      have hj_in_lins : asconPoly j ∈ lins.map (·.poly) := by
        obtain ⟨l, hl, hlp⟩ := List.mem_map.mp (hascon_in_d1 j)
        rw [hd1_eq] at hl; exact List.mem_map.mpr ⟨l, (List.mem_filter.mp hl).1, hlp⟩
      obtain ⟨pos, hpos, hpeq, hnot_earlier⟩ := hex_first lins hj_in_lins
      obtain ⟨_, ⟨hu_in, hv_in⟩⟩ := hex_lin_in pos hpos
      have hclass : ∀ x, (baseBm.testBit x = true ∨ (∃ n ∈ nls, n.poly = x) ∨ ∃ e ∈ lins.drop (pos + 1), e.poly = x) →
          x < 32 ∨ (∃ k : Fin 5, x = (nlArr k).poly) ∨ (∃ j' : Fin 5, j' ≠ j ∧ x = asconPoly j') := by
        intro x hx
        rcases hx with hbx | ⟨n, hn, rfl⟩ | ⟨e, he, rfl⟩
        · exact Or.inl (hbm32 x hbx)
        · obtain ⟨k, rfl⟩ := hnls_eq n hn; exact Or.inr (Or.inl ⟨k, rfl⟩)
        · have hel : e ∈ lins := List.mem_of_mem_drop he
          by_cases he0 : e.depth = 0
          · exact Or.inl (hd0_lt32 e (by rw [hd0_eq]; exact List.mem_filter.mpr ⟨hel, beq_iff_eq.mpr he0⟩))
          · rcases hd1_lin e (by rw [hd1_eq]; exact List.mem_filter.mpr ⟨hel, bne_iff_ne.mpr he0⟩) with hlt32 | ⟨j', hj'⟩
            · exact Or.inl hlt32
            · refine Or.inr (Or.inr ⟨j', ?_, hj'⟩)
              intro hjj; subst hjj; exact hnot_earlier e he hj'
      have hcu := hclass _ hu_in; have hcv := hclass _ hv_in
      have hnot_lt32_y : ¬ (asconPoly j < 32) := asconPoly_ge32 j
      have hnot_nl_y : ∀ k : Fin 5, asconPoly j ≠ (nlArr k).poly := fun k heq => by
        rw [(nlArr k).hpoly] at heq
        exact no_free_output ⟨(nlArr k).a, (nlArr k).ha⟩ ⟨(nlArr k).b, (nlArr k).hb⟩ (nlArr k).ca (nlArr k).cb j heq.symm
      have hnot_other_y : ∀ j' : Fin 5, j' ≠ j → asconPoly j ≠ asconPoly j' := fun j' hne heq => hne (asconPoly_inj j j' heq).symm
      have hxor_eq : lins[pos].u ^^^ lins[pos].v = asconPoly j := by
        have hpl := lins[pos].hpoly
        cases hix : lins[pos].isXor
        · exfalso; simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl; rw [hpeq] at hpl
          rcases hpl with h0 | hu | hv
          · exact asconPoly_ne_zero j h0
          · rw [← hu] at hcu; rcases hcu with h | ⟨k, h⟩ | ⟨j', hne, h⟩
            · exact hnot_lt32_y h
            · exact hnot_nl_y k h
            · exact hnot_other_y j' hne h
          · rw [← hv] at hcv; rcases hcv with h | ⟨k, h⟩ | ⟨j', hne, h⟩
            · exact hnot_lt32_y h
            · exact hnot_nl_y k h
            · exact hnot_other_y j' hne h
        · simp only [hix, ↓reduceIte] at hpl; rw [hpeq] at hpl; exact hpl.symm
      have hlin_part : (lins[pos].u &&& 31) ^^^ (lins[pos].v &&& 31) = asconLin j := by
        have := congrArg (fun x => x &&& 31) hxor_eq
        have hand_xor : ∀ a b : Nat, (a ^^^ b) &&& 31 = (a &&& 31) ^^^ (b &&& 31) := by
          intro a b; apply Nat.eq_of_testBit_eq; intro bit; simp only [Nat.testBit_and, Nat.testBit_xor]
          cases a.testBit bit <;> cases b.testBit bit <;> cases (31 : Nat).testBit bit <;> rfl
        rw [hand_xor] at this; exact this.trans (asconPoly_lin j)
      have hquad_part : (lins[pos].u >>> 5) ^^^ (lins[pos].v >>> 5) = asconQuad j := by
        have := congrArg (fun x => x >>> 5) hxor_eq
        rw [Nat.shiftRight_xor_distrib] at this; exact this.trans (asconPoly_quad j)
      have hlt32_parts : ∀ x, x < 32 → (x &&& 31) = x ∧ (x >>> 5) = 0 := by
        intro x hx; refine ⟨?_, by omega⟩
        apply Nat.eq_of_testBit_eq; intro bit; rw [Nat.testBit_and]
        by_cases h5 : bit < 5
        · have h31 : (31 : Nat).testBit bit = true := by
            have : (31 : Nat) = 2 ^ 5 - 1 := rfl
            rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
          simp [h31]
        · have h0 : x.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show x < 2 ^ 5 from hx) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
          simp [h0]
      rcases hcu with hubm | ⟨ka, hua⟩ | ⟨j1, hj1ne, huj1⟩ <;>
      rcases hcv with hvbm | ⟨kb, hvb⟩ | ⟨j2, hj2ne, hvj2⟩
      · rw [(hlt32_parts _ hubm).2, (hlt32_parts _ hvbm).2] at hquad_part
        exact False.elim (asconQuad_ne_zero j hquad_part.symm)
      · have hq : coordToQuad (1 <<< kb.val) = coordToQuad (inv j) := by
          rw [hctq_k kb, hctq_inv j, ← hquad_part, (hlt32_parts _ hubm).2, Nat.zero_xor, hvb, hnl_quad kb]
        have hinv_eq : inv j = 1 <<< kb.val :=
          (hctq_inj _ _ (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ kb.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) kb.isLt) (hinv_spec j) hq).symm
        rw [(hlt32_parts _ hubm).1, hvb, hnl_lin' kb] at hlin_part
        have hu_eq : lins[pos].u = asconLin j ^^^ shiftOf (T0 kb) (T1 kb) (cArr' kb).val := by
          rw [← hlin_part, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Or.inr (Or.inr (Or.inl ⟨kb, hinv_eq, (hbm_all32 _).mpr (hu_eq ▸ hubm)⟩))
      · rw [(hlt32_parts _ hubm).2, Nat.zero_xor, hvj2, asconPoly_quad j2] at hquad_part
        exact absurd (asconQuad_inj j2 j hquad_part) hj2ne
      · have hq : coordToQuad (1 <<< ka.val) = coordToQuad (inv j) := by
          rw [hctq_k ka, hctq_inv j, ← hquad_part, (hlt32_parts _ hvbm).2, Nat.xor_zero, hua, hnl_quad ka]
        have hinv_eq : inv j = 1 <<< ka.val :=
          (hctq_inj _ _ (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ ka.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) ka.isLt) (hinv_spec j) hq).symm
        rw [hua, hnl_lin' ka, (hlt32_parts _ hvbm).1] at hlin_part
        have hv_eq : lins[pos].v = asconLin j ^^^ shiftOf (T0 ka) (T1 ka) (cArr' ka).val := by
          rw [← hlin_part, Nat.xor_comm (shiftOf _ _ _), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Or.inr (Or.inr (Or.inl ⟨ka, hinv_eq, (hbm_all32 _).mpr (hv_eq ▸ hvbm)⟩))
      · have hq : coordToQuad ((1 <<< ka.val) ^^^ (1 <<< kb.val)) = coordToQuad (inv j) := by
          rw [hctq_xor, hctq_k ka, hctq_k kb, hctq_inv j, ← hquad_part, hua, hvb, hnl_quad ka, hnl_quad kb]
        have hinv_eq : inv j = (1 <<< ka.val) ^^^ (1 <<< kb.val) :=
          (hctq_inj _ _ (xor_lt_32 (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ ka.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) ka.isLt)
            (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ kb.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) kb.isLt)) (hinv_spec j) hq).symm
        rw [hua, hvb, hnl_lin' ka, hnl_lin' kb] at hlin_part
        by_cases hkab : ka = kb
        · subst hkab; rw [Nat.xor_self] at hinv_eq
          have hq0 := hctq_inv j; rw [hinv_eq, hctq_0] at hq0
          exact False.elim (asconQuad_ne_zero j hq0.symm)
        · have hxor_or : ∀ a b : Fin 5, a ≠ b → ((1 <<< a.val) ^^^ (1 <<< b.val)) = ((1 <<< a.val) ||| (1 <<< b.val)) := by decide +kernel
          by_cases hlt : ka.val < kb.val
          · exact Or.inr (Or.inl ⟨ka, kb, hlt, hinv_eq.trans (hxor_or ka kb hkab), hlin_part⟩)
          · exact Or.inr (Or.inl ⟨kb, ka, by omega,
              by rw [hinv_eq, Nat.xor_comm]; exact hxor_or kb ka (fun h => hkab h.symm),
              by rw [Nat.xor_comm]; exact hlin_part⟩)
      · have hq : coordToQuad ((1 <<< ka.val) ^^^ inv j2) = coordToQuad (inv j) := by
          rw [hctq_xor, hctq_k ka, hctq_inv j2, hctq_inv j, ← hquad_part, hua, hvj2, hnl_quad ka, asconPoly_quad j2]
        have hinv_eq : (1 <<< ka.val) ^^^ inv j2 = inv j :=
          hctq_inj _ _ (xor_lt_32 (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ ka.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) ka.isLt) (hinv_spec j2))
            (hinv_spec j) hq
        have hinv_eq' : inv j ^^^ inv j2 = 1 <<< ka.val := by rw [← hinv_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [hua, hvj2, hnl_lin' ka, asconPoly_lin j2] at hlin_part
        have hl' : asconLin j ^^^ asconLin j2 = shiftOf (T0 ka) (T1 ka) (cArr' ka).val := by rw [← hlin_part, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Or.inr (Or.inr (Or.inr ⟨ka, j2, hj2ne, hinv_eq', hl'⟩))
      · rw [huj1, asconPoly_quad j1, (hlt32_parts _ hvbm).2, Nat.xor_zero] at hquad_part
        exact absurd (asconQuad_inj j1 j hquad_part) hj1ne
      · have hq : coordToQuad (inv j1 ^^^ (1 <<< kb.val)) = coordToQuad (inv j) := by
          rw [hctq_xor, hctq_inv j1, hctq_k kb, hctq_inv j, ← hquad_part, huj1, hvb, asconPoly_quad j1, hnl_quad kb]
        have hinv_eq : inv j1 ^^^ (1 <<< kb.val) = inv j :=
          hctq_inj _ _ (xor_lt_32 (hinv_spec j1) (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact show 2 ^ kb.val < 2 ^ 5 from Nat.pow_lt_pow_right (by omega : 1 < 2) kb.isLt))
            (hinv_spec j) hq
        have hinv_eq' : inv j ^^^ inv j1 = 1 <<< kb.val := by rw [← hinv_eq, Nat.xor_comm (inv j1), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [huj1, hvb, asconPoly_lin j1, hnl_lin' kb] at hlin_part
        have hl' : asconLin j ^^^ asconLin j1 = shiftOf (T0 kb) (T1 kb) (cArr' kb).val := by rw [← hlin_part, Nat.xor_comm (asconLin j1), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Or.inr (Or.inr (Or.inr ⟨kb, j1, hj1ne, hinv_eq', hl'⟩))
      · have hq : coordToQuad (inv j1 ^^^ inv j2) = coordToQuad (inv j) := by
          rw [hctq_xor, hctq_inv j1, hctq_inv j2, hctq_inv j, ← hquad_part, huj1, hvj2, asconPoly_quad j1, asconPoly_quad j2]
        have hinv_eq : inv j1 ^^^ inv j2 = inv j := hctq_inj _ _ (xor_lt_32 (hinv_spec j1) (hinv_spec j2)) (hinv_spec j) hq
        rw [huj1, hvj2, asconPoly_lin j1, asconPoly_lin j2] at hlin_part
        by_cases hj12 : j1 = j2
        · subst hj12; rw [Nat.xor_self] at hinv_eq
          have hq0 := hctq_inv j; rw [← hinv_eq, hctq_0] at hq0
          exact False.elim (asconQuad_ne_zero j hq0.symm)
        · by_cases hlt : j1.val < j2.val
          · exact Or.inl ⟨j1, j2, hj1ne, hj2ne, hlt, hinv_eq, hlin_part⟩
          · exact Or.inl ⟨j2, j1, hj2ne, hj1ne, by omega, by rw [Nat.xor_comm]; exact hinv_eq, by rw [Nat.xor_comm]; exact hlin_part⟩)
  rw [hfalse] at hzh_raw; cases hzh_raw

set_option maxRecDepth 8192 in
theorem record : ¬ Crypto.Statements.CZ_rec_ascon_gates.Record 14 := by
  rintro ⟨c, hwf, hnl, hd, hsz, hcomp⟩
  -- 1. Unpack simulation soundness and match all 5 outputs to `asconPoly 0..4`
  have hsim := simWires_sound c.gates
  obtain ⟨hsim_sz, hsim_dep, hsim_lt, hsim_d0, hsim_ev⟩ := hsim
  have hwf' := hwf
  unfold MultiCircuit.IsWellFormed MultiCircuit.isWellFormedBool at hwf'
  simp only [Bool.and_eq_true, beq_iff_eq] at hwf'
  have hout_len : c.outputs.length = 5 := hwf'.1.1
  -- Depth of every output wire is ≤ 1
  have hout_dep : ∀ j : Fin 5, (simWires c.gates |>.getD (c.outputs.getD j.val 0) ⟨0, 0, false⟩).depth ≤ 1 := by
    intro j
    rw [hsim_dep]
    have hd' : c.outputs.foldl (fun best w => Nat.max best ((c.gates.foldl (fun (acc : Array Nat) g =>
        let base := Nat.max (acc.getD g.w1 0) (acc.getD g.w2 0)
        acc.push (if g.op.isLinear then base else base + 1)) (Array.replicate 5 0)).getD w 0)) 0 ≤ 1 := hd
    have hfold_max : ∀ (ws : List Nat) (b : Nat) (f : Nat → Nat),
        ∀ w ∈ ws, f w ≤ ws.foldl (fun best w => Nat.max best (f w)) b := by
      intro ws; induction ws with
      | nil => intro _ _ _ h; cases h
      | cons w ws ih =>
        intro b f u hu
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hu with rfl | hws
        · have hge : ∀ (zs : List Nat) (a : Nat), a ≤ zs.foldl (fun best z => Nat.max best (f z)) a := by
            intro zs; induction zs with
            | nil => intro a; exact Nat.le_refl _
            | cons z zs ihz => intro a; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ihz _)
          exact Nat.le_trans (Nat.le_max_right b (f u)) (hge ws _)
        · exact ih _ f u hws
    have hmem : c.outputs.getD j.val 0 ∈ c.outputs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem (by omega)
    exact Nat.le_trans (hfold_max c.outputs 0 (fun w => (c.gates.foldl (fun (acc : Array Nat) g =>
        let base := Nat.max (acc.getD g.w1 0) (acc.getD g.w2 0)
        acc.push (if g.op.isLinear then base else base + 1)) (Array.replicate 5 0)).getD w 0) _ hmem) hd'
  -- Every output wire evaluates to `asconPoly j` mod constants, so its `SimWire.poly = asconPoly j`!
  have hout_poly : ∀ j : Fin 5, (simWires c.gates |>.getD (c.outputs.getD j.val 0) ⟨0, 0, false⟩).poly = asconPoly j := by
    intro j
    let w := c.outputs.getD j.val 0
    have hlt1 := hsim_lt w
    have hlt2 := asconPoly_lt j
    apply poly_unique hlt1 hlt2 (c0 := xor (simWires c.gates |>.getD w ⟨0, 0, false⟩).cbit (j.val == 2))
    intro x
    have hev := hsim_ev x w (hout_dep j)
    have hbit : (MultiCircuit.evalWires x c.gates).getD w false = (Crypto.asconSBox x).getLsbD j.val := by
      have hc := hcomp x
      have htb := congrArg (fun n => n.testBit j.val) hc
      unfold MultiCircuit.evalNat at htb
      -- Use packBits bit extraction
      have hpb : ∀ (bs : List Bool) (k : Nat), (MultiCircuit.packBits bs).testBit k = bs.getD k false := by
        intro bs; induction bs with
        | nil => intro k; simp [MultiCircuit.packBits]
        | cons b bs ih =>
          intro k; cases k with
          | zero => simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_zero]; cases b <;> simp [Nat.testBit_zero]
          | succ k =>
            have hk := ih k
            simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_succ] at hk ⊢
            rw [Nat.testBit_succ]; cases b <;> simp [Nat.mul_add_div, hk]
      rw [hpb] at htb
      have hmap : (c.outputs.map (fun u => (MultiCircuit.evalWires x c.gates).getD u false)).getD j.val false =
          (MultiCircuit.evalWires x c.gates).getD w false := by
        simp [w, List.getD_eq_getElem?_getD, show j.val < c.outputs.length by omega]
      rw [hmap] at htb
      exact htb
    rw [hbit, ascon_matches_poly j x] at hev
    revert hev
    generalize (simWires c.gates |>.getD w ⟨0, 0, false⟩).cbit = c1
    generalize (j.val == 2) = c2
    generalize evalPoly (simWires c.gates |>.getD w ⟨0, 0, false⟩).poly x = p1
    generalize evalPoly (asconPoly j) x = p2
    cases c1 <;> cases c2 <;> cases p1 <;> cases p2 <;> decide

  let ex := extractGates c.gates
  obtain ⟨hex_sw, hex_nl_len, hex_lin_len, hex_qspan, hex_d0, hex_all, hex_nl_in, hex_lin_in⟩ := extractGates_inv c.gates
  let nls := ex.2.1
  let lins := ex.2.2

  -- 3. `nls` has length exactly 5, and its 5 quadratic parts are 5 distinct elements of `decomps` forming a basis of Q!
  have hnl_le5 : nls.length ≤ 5 := Nat.le_trans hex_nl_len hnl
  have hq_cov : ∀ j : Fin 5, inQuadSpan (nls.map (fun n => prodQ n.a n.b)) (asconQuad j) := by
    intro j
    have h1 := hex_qspan (c.outputs.getD j.val 0) (by rw [hex_sw]; exact hout_dep j)
    rw [hex_sw, hout_poly j] at h1
    have hqa : asconPoly j >>> 5 = asconQuad j := asconPoly_quad j
    rwa [hqa] at h1
  obtain ⟨hqs_len, hqs_nd, hqs_inQ⟩ := inQuadSpan_of_length_le_5 (by simpa using hnl_le5) hq_cov
  have hnls_len : nls.length = 5 := by simpa using hqs_len

  -- Total linear gates ≤ 9!
  have hlin_le9 : lins.length ≤ 9 := by
    have hpart : (c.gates.filter (fun g => !g.op.isLinear)).length +
                 (c.gates.filter (fun g => g.op.isLinear)).length = c.gates.length := by
      induction c.gates with
      | nil => simp
      | cons g gs ih =>
        by_cases h : g.op.isLinear = true <;> simp [h] <;> omega
    have hnl_eq5 : (c.gates.filter (fun g => !g.op.isLinear)).length = 5 := by
      have hnl_le' : nls.length ≤ (c.gates.filter (fun g => !g.op.isLinear)).length := hex_nl_len
      have h5 : 5 ≤ (c.gates.filter (fun g => !g.op.isLinear)).length := by omega
      have hnl' : (c.gates.filter (fun g => !g.op.isLinear)).length ≤ 5 := by
        simpa [MultiCircuit.nonLinearCount] using hnl
      omega
    have htot : c.gates.length ≤ 14 := by simpa [MultiCircuit.totalGates] using hsz
    have hlin_le' : lins.length ≤ (c.gates.filter (fun g => g.op.isLinear)).length := hex_lin_len
    omega

  -- Classify every `n ∈ nls` into a unique index `idx ∈ Fin 10` of `decomps`!
  have hnl_class : ∀ n ∈ nls, ∃ idx : Fin 10,
      prodQ n.a n.b = (decomps[idx.val]).quad ∧
      (n.a = (decomps[idx.val]).t0 ∨ n.a = (decomps[idx.val]).t1 ∨ n.a = (decomps[idx.val]).t2) ∧
      (n.b = (decomps[idx.val]).t0 ∨ n.b = (decomps[idx.val]).t1 ∨ n.b = (decomps[idx.val]).t2) ∧
      n.a ≠ n.b := by
    intro n hn
    obtain ⟨m, hm0, hmq⟩ := hqs_inQ (prodQ n.a n.b) (List.mem_map.mpr ⟨n, hn, rfl⟩)
    obtain ⟨idx, hmask, ha, hb, hne⟩ := prodQ_in_Q_classified ⟨n.a, n.ha⟩ ⟨n.b, n.hb⟩ m hm0 hmq
    refine ⟨idx, ?_, ha, hb, hne⟩
    rw [hmq, ← hmask, decomp_quad_eq idx]

  -- Associate to each `n ∈ nls` its `decompIdx : Nat` (< 10)
  let getIdx (n : NLInfo) : Nat :=
    match (List.finRange 10).find? (fun idx => (decomps[idx.val]).quad == prodQ n.a n.b) with
    | some idx => idx.val
    | none => 0
  have hgetIdx_spec : ∀ n ∈ nls,
      let idx := getIdx n
      idx < 10 ∧
      prodQ n.a n.b = (decomps[idx]!).quad ∧
      (n.a = (decomps[idx]!).t0 ∨ n.a = (decomps[idx]!).t1 ∨ n.a = (decomps[idx]!).t2) ∧
      (n.b = (decomps[idx]!).t0 ∨ n.b = (decomps[idx]!).t1 ∨ n.b = (decomps[idx]!).t2) ∧
      n.a ≠ n.b := by
    intro n hn
    obtain ⟨idx, hq, ha, hb, hne⟩ := hnl_class n hn
    have hq_inj : ∀ i j : Fin 10, (decomps[i.val]).quad = (decomps[j.val]).quad → i = j := by
      decide +kernel
    unfold getIdx
    cases hfind : (List.finRange 10).find? (fun k => (decomps[k.val]).quad == prodQ n.a n.b) with
    | none =>
      exact absurd (beq_iff_eq.mpr hq.symm) (List.find?_eq_none.mp hfind idx (List.mem_finRange idx))
    | some k =>
      have hk := by simpa using List.find?_some hfind
      have heq : k = idx := hq_inj k idx (hk.trans hq)
      subst heq
      have hbang : decomps[k.val]! = decomps[k.val] := getElem!_pos decomps k.val k.isLt
      exact ⟨k.isLt, by rw [hbang]; exact hq, by rw [hbang]; exact ha, by rw [hbang]; exact hb, hne⟩

  -- The 5 indices `nls.map getIdx` are pairwise distinct, so sorting them gives `i0 < i1 < i2 < i3 < i4 < 10`!
  have hidxs_nd : (nls.map getIdx).Nodup := by
    have hmap_eq : (nls.map getIdx).map (fun i => (decomps[i]!).quad) = nls.map (fun n => prodQ n.a n.b) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro n hn; exact (hgetIdx_spec n hn).2.1.symm
    have hnd_q : ((nls.map getIdx).map (fun i => (decomps[i]!).quad)).Nodup := by rw [hmap_eq]; exact hqs_nd
    exact nodup_of_map _ hnd_q
  let sortedIdxs := sortList (nls.map getIdx)
  have hsort_len : sortedIdxs.length = 5 := by simp [sortedIdxs, length_sortList, hnls_len]
  have hsort_pw : sortedIdxs.Pairwise (· < ·) := pairwise_sortList hidxs_nd
  match hseq : sortedIdxs with
  | [i0, i1, i2, i3, i4] =>
    have hi_ord : i0 < i1 ∧ i1 < i2 ∧ i2 < i3 ∧ i3 < i4 := by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsort_pw
      exact ⟨hsort_pw.1.1, hsort_pw.2.1.1, hsort_pw.2.2.1.1, hsort_pw.2.2.2.1⟩
    -- Recover the 5 `NLInfo` gates ordered by `i0 < i1 < i2 < i3 < i4`!
    have hfind_nl : ∀ idx ∈ [i0, i1, i2, i3, i4], ∃ n ∈ nls, getIdx n = idx := by
      intro idx hidx
      have hmem : idx ∈ nls.map getIdx := mem_sortList.mp (by change idx ∈ sortedIdxs; rw [hseq]; exact hidx)
      exact List.mem_map.mp hmem
    obtain ⟨n0, hn0, hi0_eq⟩ := hfind_nl i0 (by simp)
    obtain ⟨n1, hn1, hi1_eq⟩ := hfind_nl i1 (by simp)
    obtain ⟨n2, hn2, hi2_eq⟩ := hfind_nl i2 (by simp)
    obtain ⟨n3, hn3, hi3_eq⟩ := hfind_nl i3 (by simp)
    obtain ⟨n4, hn4, hi4_eq⟩ := hfind_nl i4 (by simp)
    let nlArr : Fin 5 → NLInfo
      | ⟨0, _⟩ => n0 | ⟨1, _⟩ => n1 | ⟨2, _⟩ => n2 | ⟨3, _⟩ => n3 | ⟨4, _⟩ => n4
    let idxArr : Fin 5 → Nat
      | ⟨0, _⟩ => i0 | ⟨1, _⟩ => i1 | ⟨2, _⟩ => i2 | ⟨3, _⟩ => i3 | ⟨4, _⟩ => i4
    have hnl_mem : ∀ k : Fin 5, nlArr k ∈ nls := by
      intro k; rcases k with ⟨k, hk⟩; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => assumption
    have hnl_idx : ∀ k : Fin 5, getIdx (nlArr k) = idxArr k := by
      intro k; rcases k with ⟨k, hk⟩; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => assumption
    have hidx_lt10 : ∀ k : Fin 5, idxArr k < 10 := by
      intro k; rw [← hnl_idx k]; exact (hgetIdx_spec (nlArr k) (hnl_mem k)).1
    -- Every `n ∈ nls` is one of `nlArr 0..4`!
    have hnls_eq : ∀ n ∈ nls, ∃ k : Fin 5, n = nlArr k := by
      intro n hn
      have hmem : getIdx n ∈ [i0, i1, i2, i3, i4] := by
        rw [← hseq, mem_sortList]; exact List.mem_map.mpr ⟨n, hn, rfl⟩
      have hinj_n : ∀ n' ∈ nls, getIdx n' = getIdx n → n' = n := by
        -- From `hidxs_nd`, `getIdx` is injective on `nls`!
        intro n' hn' heq
        obtain ⟨j1, hj1, rfl⟩ := List.getElem_of_mem hn'
        obtain ⟨j2, hj2, rfl⟩ := List.getElem_of_mem hn
        have hnd' := inj_getElem_of_nodup hidxs_nd
        have : j1 = j2 := hnd' j1 j2 (by simp [hj1]) (by simp [hj2]) (by simpa using heq)
        subst this; rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h
      · exact ⟨⟨0, by decide⟩, (hinj_n n0 hn0 (hi0_eq.trans h.symm)).symm⟩
      · exact ⟨⟨1, by decide⟩, (hinj_n n1 hn1 (hi1_eq.trans h.symm)).symm⟩
      · exact ⟨⟨2, by decide⟩, (hinj_n n2 hn2 (hi2_eq.trans h.symm)).symm⟩
      · exact ⟨⟨3, by decide⟩, (hinj_n n3 hn3 (hi3_eq.trans h.symm)).symm⟩
      · exact ⟨⟨4, by decide⟩, (hinj_n n4 hn4 (hi4_eq.trans h.symm)).symm⟩

    -- Check `isBasis5` for `(decomps[i0]!.mask, ..., decomps[i4]!.mask)`!
    let mArr : Fin 5 → Nat := fun k => (decomps[idxArr k]!).mask
    have hm_lt32 : ∀ k : Fin 5, mArr k < 32 := by
      intro k
      have hk := hidx_lt10 k
      have : ∀ i : Fin 10, (decomps[i.val]!).mask < 32 := by decide
      exact this ⟨idxArr k, hk⟩
    have hq_of_m : ∀ k : Fin 5, qOfMask (mArr k) = prodQ (nlArr k).a (nlArr k).b := by
      intro k
      have hsp := hgetIdx_spec (nlArr k) (hnl_mem k)
      rw [hnl_idx k] at hsp
      have hdk : qOfMask (decomps[idxArr k]!).mask = (decomps[idxArr k]!).quad := by
        have hbang : decomps[idxArr k]! = decomps[idxArr k]'(hidx_lt10 k) := getElem!_pos decomps (idxArr k) (hidx_lt10 k)
        rw [hbang]; exact decomp_quad_eq ⟨idxArr k, hidx_lt10 k⟩
      exact hdk.trans hsp.2.1.symm
    -- Every `1 <<< j.val` is in `span(mArr)`!
    have hm_span : ∀ j : Fin 5, ∃ s : Fin 32, maskSubset mArr s.val = 1 <<< j.val := by
      intro j
      obtain ⟨sub, hsub, hqeq⟩ := hq_cov j
      -- Express `sub` as a 5-bit mask `s` over `nlArr 0..4`!
      have hex_s : ∃ s : Fin 32, qOfMask (maskSubset mArr s.val) = xorList sub := by
        clear hqeq
        induction sub with
        | nil => exact ⟨⟨0, by decide⟩, by simp [maskSubset, qOfMask, xorList]⟩
        | cons q rest ih =>
          obtain ⟨s, hs⟩ := ih (fun x hx => hsub x (List.mem_cons_of_mem q hx))
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp (hsub q (List.mem_cons_self ..))
          obtain ⟨k, rfl⟩ := hnls_eq n hn
          have h1 : 1 <<< k.val < 32 := by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) k.isLt
          refine ⟨⟨(1 <<< k.val) ^^^ s.val, xor_lt_32 h1 s.isLt⟩, ?_⟩
          have hms_x : maskSubset mArr ((1 <<< k.val) ^^^ s.val) = mArr k ^^^ maskSubset mArr s.val := by
            rw [maskSubset_xor]
            congr 1
            exact maskSubset_bit mArr k
          rw [hms_x, qOfMask_xor, hq_of_m k, hs]
          have hxl : xorList (prodQ (nlArr k).a (nlArr k).b :: rest) = prodQ (nlArr k).a (nlArr k).b ^^^ xorList rest := by
            have hcons : ∀ (zs : List Nat) (a : Nat), zs.foldl (· ^^^ ·) a = a ^^^ xorList zs := by
              intro zs; induction zs with
              | nil => intro a; simp [xorList]
              | cons z zs ihz => intro a; simp only [List.foldl_cons, xorList] at ihz ⊢; rw [ihz (a ^^^ z), ihz (0 ^^^ z)]; simp [Nat.xor_assoc]
            unfold xorList; simp only [List.foldl_cons, Nat.zero_xor]; exact hcons rest _
          exact hxl.symm
      obtain ⟨s, hs⟩ := hex_s
      rw [hqeq] at hs
      have hms_lt : maskSubset mArr s.val < 32 := by
        unfold maskSubset
        have hi : ∀ (c : Bool) (k : Fin 5), (if c then mArr k else 0) < 32 := fun c k => by
          cases c with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hm_lt32 k
        exact xor_lt_32 (xor_lt_32 (xor_lt_32 (xor_lt_32 (hi _ ⟨0, by decide⟩) (hi _ ⟨1, by decide⟩))
          (hi _ ⟨2, by decide⟩)) (hi _ ⟨3, by decide⟩)) (hi _ ⟨4, by decide⟩)
      have hej : qOfMask (1 <<< j.val) = asconQuad j := qOfMask_bit j
      have hdiff0 : maskSubset mArr s.val ^^^ (1 <<< j.val) = 0 := by
        apply Classical.byContradiction; intro hnz
        have hlt : maskSubset mArr s.val ^^^ (1 <<< j.val) < 32 :=
          xor_lt_32 hms_lt (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) j.isLt)
        have h0 := asconQuad_indep ⟨_, hlt⟩ hnz
        rw [qOfMask_xor, hs, hej, Nat.xor_self] at h0
        exact h0 rfl
      exact ⟨s, nat_eq_of_xor_eq_zero hdiff0⟩

    have hbasis5 : isBasis5 (mArr ⟨0, by decide⟩) (mArr ⟨1, by decide⟩) (mArr ⟨2, by decide⟩)
        (mArr ⟨3, by decide⟩) (mArr ⟨4, by decide⟩) = true :=
      basis5_of_span ⟨hm_lt32 ⟨0, by decide⟩, hm_lt32 ⟨1, by decide⟩, hm_lt32 ⟨2, by decide⟩,
        hm_lt32 ⟨3, by decide⟩, hm_lt32 ⟨4, by decide⟩⟩ hm_span

    -- Map any quadratic part `q ∈ Q` uniquely to its 5-bit coordinate vector `invOfQ` in the basis `nlArr 0..4`!
    let inv : Fin 5 → Nat := fun j =>
      findInvRow (mArr ⟨0, by decide⟩) (mArr ⟨1, by decide⟩) (mArr ⟨2, by decide⟩)
        (mArr ⟨3, by decide⟩) (mArr ⟨4, by decide⟩) (1 <<< j.val)
    have hinv_spec : ∀ j : Fin 5,
        inv j < 32 ∧ maskSubset mArr (inv j) = 1 <<< j.val := by
      intro j
      obtain ⟨s, hs⟩ := hm_span j
      have hinv_eq : inv j = findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask (1 <<< j.val) := by
        rcases j with ⟨j, hj⟩; match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
      have heq := findInvRow_spec hbasis5 s.isLt hs
      rw [hinv_eq, heq]
      exact ⟨s.isLt, hs⟩
    -- Crucial coordinate isomorphism: `qOfMask (maskSubset mArr s)` is injective on `s < 32`,
    -- and maps `1 <<< k.val ↦ prodQ (nlArr k).a (nlArr k).b` and `inv j ↦ asconQuad j`!
    let coordToQuad (s : Nat) : Nat := qOfMask (maskSubset mArr s)
    have hctq_xor : ∀ s1 s2, coordToQuad (s1 ^^^ s2) = coordToQuad s1 ^^^ coordToQuad s2 := by
      intro s1 s2
      have hms_x := maskSubset_xor mArr s1 s2
      unfold coordToQuad; rw [hms_x, qOfMask_xor]
    have hctq_inj : ∀ s1 s2, s1 < 32 → s2 < 32 → coordToQuad s1 = coordToQuad s2 → s1 = s2 := by
      intro s1 s2 hs1 hs2 heq
      apply Classical.byContradiction; intro hne
      have hnz : s1 ^^^ s2 ≠ 0 := fun hz => hne (nat_eq_of_xor_eq_zero hz)
      have hlt : s1 ^^^ s2 < 32 := xor_lt_32 hs1 hs2
      have hms_nz : maskSubset mArr (s1 ^^^ s2) ≠ 0 := by
        unfold isBasis5 at hbasis5; rw [List.all_eq_true] at hbasis5
        have hmem := hbasis5 ((s1 ^^^ s2) - 1) (List.mem_range.mpr (by omega))
        have he1 : (s1 ^^^ s2) - 1 + 1 = s1 ^^^ s2 := by omega
        rw [he1, bne_iff_ne] at hmem; exact hmem
      have hms_lt : maskSubset mArr (s1 ^^^ s2) < 32 := by
        unfold maskSubset
        have hi : ∀ (c : Bool) (k : Fin 5), (if c then mArr k else 0) < 32 := fun c k => by
          cases c with | false => simp only [Bool.false_eq_true, ↓reduceIte]; decide | true => simp only [↓reduceIte]; exact hm_lt32 k
        exact xor_lt_32 (xor_lt_32 (xor_lt_32 (xor_lt_32 (hi _ ⟨0, by decide⟩) (hi _ ⟨1, by decide⟩))
          (hi _ ⟨2, by decide⟩)) (hi _ ⟨3, by decide⟩)) (hi _ ⟨4, by decide⟩)
      have hq0 := asconQuad_indep ⟨_, hms_lt⟩ hms_nz
      have : coordToQuad (s1 ^^^ s2) = 0 := by rw [hctq_xor, heq, Nat.xor_self]
      exact hq0 this
    have hctq_k : ∀ k : Fin 5, coordToQuad (1 <<< k.val) = prodQ (nlArr k).a (nlArr k).b := by
      intro k; unfold coordToQuad
      have : maskSubset mArr (1 <<< k.val) = mArr k := maskSubset_bit mArr k
      rw [this, hq_of_m k]
    have hctq_inv : ∀ j : Fin 5, coordToQuad (inv j) = asconQuad j := by
      intro j; unfold coordToQuad; rw [(hinv_spec j).2]; exact qOfMask_bit j
    have hctq_0 : coordToQuad 0 = 0 := by simp [coordToQuad, maskSubset, qOfMask]

    -- Construct `skipArr : Fin 5 → Fin 3` and `cArr : Fin 5 → Fin 4` cleanly!
    let skipOf (k : Fin 5) : Fin 3 :=
      let d := decomps[idxArr k]!
      if (nlArr k).a ≠ d.t0 ∧ (nlArr k).b ≠ d.t0 then ⟨0, by decide⟩
      else if (nlArr k).a ≠ d.t1 ∧ (nlArr k).b ≠ d.t1 then ⟨1, by decide⟩
      else ⟨2, by decide⟩
    let pcode : Nat :=
      (skipOf ⟨0, by decide⟩).val + 3 * ((skipOf ⟨1, by decide⟩).val +
      3 * ((skipOf ⟨2, by decide⟩).val + 3 * ((skipOf ⟨3, by decide⟩).val +
      3 * (skipOf ⟨4, by decide⟩).val)))
    have hpcode_lt : pcode < 243 := by
      have h0 := (skipOf ⟨0, by decide⟩).isLt; have h1 := (skipOf ⟨1, by decide⟩).isLt
      have h2 := (skipOf ⟨2, by decide⟩).isLt; have h3 := (skipOf ⟨3, by decide⟩).isLt
      have h4 := (skipOf ⟨4, by decide⟩).isLt
      omega
    have hdiv_skip :
        pcode % 3 = (skipOf ⟨0, by decide⟩).val ∧
        (pcode / 3) % 3 = (skipOf ⟨1, by decide⟩).val ∧
        (pcode / 9) % 3 = (skipOf ⟨2, by decide⟩).val ∧
        (pcode / 27) % 3 = (skipOf ⟨3, by decide⟩).val ∧
        (pcode / 81) % 3 = (skipOf ⟨4, by decide⟩).val := by
      have h0 := (skipOf ⟨0, by decide⟩).isLt; have h1 := (skipOf ⟨1, by decide⟩).isLt
      have h2 := (skipOf ⟨2, by decide⟩).isLt; have h3 := (skipOf ⟨3, by decide⟩).isLt
      have h4 := (skipOf ⟨4, by decide⟩).isLt
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩

    let A : Fin 5 → Nat := fun k => (pairOfSkip (decomps[idxArr k]!) (skipOf k).val).1
    let B : Fin 5 → Nat := fun k => (pairOfSkip (decomps[idxArr k]!) (skipOf k).val).2
    have hAB_eq : ∀ k : Fin 5,
        ((nlArr k).a = A k ∧ (nlArr k).b = B k) ∨ ((nlArr k).a = B k ∧ (nlArr k).b = A k) := by
      intro k
      have hsp := hgetIdx_spec (nlArr k) (hnl_mem k)
      rw [hnl_idx k] at hsp
      obtain ⟨_, _, ha, hb, hne⟩ := hsp
      have htri_ne : (decomps[idxArr k]!).t0 ≠ (decomps[idxArr k]!).t1 ∧
                     (decomps[idxArr k]!).t0 ≠ (decomps[idxArr k]!).t2 ∧
                     (decomps[idxArr k]!).t1 ≠ (decomps[idxArr k]!).t2 := by
        have : ∀ i : Fin 10, (decomps[i.val]!).t0 ≠ (decomps[i.val]!).t1 ∧
            (decomps[i.val]!).t0 ≠ (decomps[i.val]!).t2 ∧ (decomps[i.val]!).t1 ≠ (decomps[i.val]!).t2 := by decide
        exact this ⟨idxArr k, hidx_lt10 k⟩
      dsimp only [A, B, skipOf]
      rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
      · exact absurd (ha.trans hb.symm) hne
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1, htri_ne.2.1.symm, htri_ne.2.2, htri_ne.2.2.symm, pairOfSkip]
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1, htri_ne.2.1.symm, htri_ne.2.2, htri_ne.2.2.symm, pairOfSkip]
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1, htri_ne.2.1.symm, htri_ne.2.2, htri_ne.2.2.symm, pairOfSkip]
      · exact absurd (ha.trans hb.symm) hne
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1, htri_ne.2.1.symm, htri_ne.2.2, htri_ne.2.2.symm, pairOfSkip]
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1, htri_ne.2.1.symm, htri_ne.2.2, htri_ne.2.2.symm, pairOfSkip]
      · simp [ha, hb, htri_ne.1, htri_ne.1.symm, htri_ne.2.1.symm, htri_ne.2.2.symm, pairOfSkip]
      · exact absurd (ha.trans hb.symm) hne

    -- Linear part of `nlArr k` equals `shiftOf (A k) (B k) (cArr k).val`!
    let cArr (k : Fin 5) : Fin 4 :=
      let (ca', cb') := if (nlArr k).a = A k then ((nlArr k).ca, (nlArr k).cb) else ((nlArr k).cb, (nlArr k).ca)
      ⟨(if ca' then 1 else 0) + (if cb' then 2 else 0), by cases ca' <;> cases cb' <;> decide⟩
    have hnl_lin : ∀ k : Fin 5, ((nlArr k).poly &&& 31) = shiftOf (A k) (B k) (cArr k).val := by
      intro k
      have hlt_ab : A k < 32 ∧ B k < 32 := by
        rcases hAB_eq k with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨ha ▸ (nlArr k).ha, hb ▸ (nlArr k).hb⟩
        · exact ⟨hb ▸ (nlArr k).hb, ha ▸ (nlArr k).ha⟩
      have hpoly := (nlArr k).hpoly
      have hmask : ∀ (a b : Nat) (ca cb : Bool), a < 32 → b < 32 →
          (((prodPoly a b ^^^ (if ca then a else 0)) ^^^ (if cb then b else 0)) &&& 31) =
            (a &&& b) ^^^ (if ca then a else 0) ^^^ (if cb then b else 0) := by
        intro a b ca cb ha hb
        apply Nat.eq_of_testBit_eq; intro bit
        unfold prodPoly
        simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
        by_cases h5 : bit < 5
        · have h31 : (31 : Nat).testBit bit = true := by
            have : (31 : Nat) = 2 ^ 5 - 1 := rfl
            rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
          have hge : ¬ (5 ≤ bit) := by omega
          simp [h31, hge]
        · have h31 : (31 : Nat).testBit bit = false := by
            have : (31 : Nat) = 2 ^ 5 - 1 := rfl
            rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h5
          have ha0 : a.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show a < 2 ^ 5 from ha) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
          have hb0 : b.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show b < 2 ^ 5 from hb) (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega)))
          cases ca <;> cases cb <;> simp [h31, ha0, hb0]
      rw [hpoly, hmask _ _ _ _ (nlArr k).ha (nlArr k).hb]
      rcases hAB_eq k with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp only [cArr, ha, hb, ↓reduceIte, shiftOf]
        cases (nlArr k).ca <;> cases (nlArr k).cb <;>
          simp [show (0 : Nat).testBit 0 = false by decide, show (0 : Nat).testBit 1 = false by decide,
                show (1 : Nat).testBit 0 = true by decide, show (1 : Nat).testBit 1 = false by decide,
                show (2 : Nat).testBit 0 = false by decide, show (2 : Nat).testBit 1 = true by decide,
                show (3 : Nat).testBit 0 = true by decide, show (3 : Nat).testBit 1 = true by decide]
      · have hne' : B k ≠ A k := by
          have hsp := hgetIdx_spec (nlArr k) (hnl_mem k)
          rw [ha, hb] at hsp; exact hsp.2.2.2.2
        simp only [cArr, ha, hb, hne', ↓reduceIte, shiftOf]
        have hcomm : B k &&& A k = A k &&& B k := Nat.and_comm _ _
        rw [hcomm]
        cases (nlArr k).ca <;> cases (nlArr k).cb
        · simp [show (0 : Nat).testBit 0 = false by decide, show (0 : Nat).testBit 1 = false by decide]
        · simp [show (1 : Nat).testBit 0 = true by decide, show (1 : Nat).testBit 1 = false by decide]
        · simp [show (2 : Nat).testBit 0 = false by decide, show (2 : Nat).testBit 1 = true by decide]
        · simp only [show (3 : Nat).testBit 0 = true by decide, show (3 : Nat).testBit 1 = true by decide, ↓reduceIte]
          apply Nat.eq_of_testBit_eq; intro bit; simp only [Nat.testBit_xor]
          cases (A k &&& B k).testBit bit <;> cases (A k).testBit bit <;> cases (B k).testBit bit <;> rfl
    have hnl_quad : ∀ k : Fin 5, ((nlArr k).poly >>> 5) = prodQ (nlArr k).a (nlArr k).b := by
      intro k; rw [(nlArr k).hpoly]; exact prodPoly_quad (nlArr k).ha (nlArr k).hb _ _
    have hnl_poly_decomp : ∀ k : Fin 5, (nlArr k).poly =
        shiftOf (A k) (B k) (cArr k).val ||| (coordToQuad (1 <<< k.val) <<< 5) := by
      intro k; rw [hctq_k k, ← hnl_quad k, ← hnl_lin k]
      apply Nat.eq_of_testBit_eq; intro bit
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      by_cases h5 : bit < 5
      · have h31 : (31 : Nat).testBit bit = true := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h5
        have hge : ¬ (5 ≤ bit) := by omega
        simp [h31, hge]
      · have h31 : (31 : Nat).testBit bit = false := by
          have : (31 : Nat) = 2 ^ 5 - 1 := rfl
          rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h5
        have hge : 5 ≤ bit := by omega
        have heq : 5 + (bit - 5) = bit := by omega
        simp [h31, hge, heq]

    -- 4. Partition `lins` into depth-0 (`d0Lins`) and depth-1 (`d1Lins`)!
    let d0Lins := lins.filter (fun l => l.depth == 0)
    let d1Lins := lins.filter (fun l => l.depth != 0)
    have hlin_split : d0Lins.length + d1Lins.length = lins.length := by
      have hgen : ∀ ls : List LinInfo, (ls.filter (fun l => l.depth == 0)).length + (ls.filter (fun l => l.depth != 0)).length = ls.length := by
        intro ls; induction ls with
        | nil => simp
        | cons l ls ih =>
          by_cases h : l.depth = 0
          · simp [h]; omega
          · simp [h, bne_iff_ne.mpr h]; omega
      exact hgen lins

    -- Every `asconPoly j` MUST appear in `d1Lins.map (·.poly)`!
    have hascon_in_d1 : ∀ j : Fin 5, asconPoly j ∈ d1Lins.map (·.poly) := by
      intro j
      have h1 := hex_all (c.outputs.getD j.val 0) (by rw [hex_sw]; exact hout_dep j)
      rw [hex_sw, hout_poly j] at h1
      rcases h1 with hbm | ⟨n, hn, hnp⟩ | ⟨l, hl, hlp⟩
      · exfalso; have hbf : ∀ j' : Fin 5, baseBm.testBit (asconPoly j') = false := by decide
        rw [hbf j] at hbm; cases hbm
      · exfalso; rw [n.hpoly] at hnp
        exact no_free_output ⟨n.a, n.ha⟩ ⟨n.b, n.hb⟩ n.ca n.cb j hnp
      · refine List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, hlp⟩
        rw [bne_iff_ne]
        intro hl0
        -- If `l.depth = 0`, then `l.poly < 32`, impossible since `asconPoly j ≥ 32`!
        have hl32 : l.poly < 32 := by
          obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨h0, _⟩ := hex_lin_in idx hidx
          obtain ⟨hu, hv⟩ := h0 hl0
          have hbm32 : ∀ x, baseBm.testBit x = true → x < 32 := by
            intro x hx; apply Classical.byContradiction; intro hge
            have hlt : baseBm < 2 ^ 32 := by decide
            have h0 : baseBm.testBit x = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 32 ≤ x)))
            rw [h0] at hx; cases hx
          -- Simpler: use `l.poly = asconPoly j` directly? No, we need `l.depth ≠ 0` from `l.poly < 32`!
          -- Wait: every `l ∈ lins` with `l.depth = 0` came from `sw.depth = 0`, which had `sw.poly < 32`!
          -- Prove `∀ i < lins.length, lins[i].depth = 0 → lins[i].poly < 32` by induction from the end!
          have hall32 : ∀ k (hk : k ≤ lins.length), ∀ i (hi : i < lins.length),
              lins.length - i ≤ k → lins[i].depth = 0 → lins[i].poly < 32 := by
            intro k; induction k with
            | zero => intro _ i hi hle; omega
            | succ k ihk =>
              intro _ i hi hle hdi0
              obtain ⟨h0', _⟩ := hex_lin_in i hi
              obtain ⟨hu', hv'⟩ := h0' hdi0
              have hget32 : ∀ x, (baseBm.testBit x = true ∨ ∃ e ∈ lins.drop (i + 1), e.depth = 0 ∧ e.poly = x) → x < 32 := by
                intro x hx; rcases hx with hbx | ⟨e, he, he0, rfl⟩
                · exact hbm32 x hbx
                · obtain ⟨j', hj', heq⟩ := List.getElem_of_mem he
                  rw [List.getElem_drop] at heq; subst heq
                  exact ihk (by omega) (i + 1 + j') (by simp at hj'; omega) (by omega) he0
              have hu32 := hget32 _ hu'
              have hv32 := hget32 _ hv'
              have hpl := lins[i].hpoly
              cases hix : lins[i].isXor
              · simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl
                rcases hpl with h | h | h
                · rw [h]; decide
                · rw [h]; exact hu32
                · rw [h]; exact hv32
              · simp only [hix, ↓reduceIte] at hpl
                rw [hpl]; exact xor_lt_32 hu32 hv32
          exact hall32 lins.length (Nat.le_refl _) idx hidx (by omega) hl0
        rw [hlp] at hl32
        rcases j with ⟨j, hj⟩; match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [asconPoly, asconLin, asconQuad] at hl32

    have hascon_nd : ((List.finRange 5).map asconPoly).Nodup := by decide
    have hd1_ge5 : 5 ≤ d1Lins.length := by
      have hle := nodup_length_le_of_subset hascon_nd (fun y hy => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy; exact hascon_in_d1 j)
      simpa using hle
    have hd0_le4 : d0Lins.length ≤ 4 := by omega

    -- Every element of `pm = preMaskOf A B` MUST appear in `d0Lins.map (·.poly)`!
    let pm := preMaskOf A B
    have hpm_in_d0 : ∀ x, pm.testBit x = true → x ∈ d0Lins.map (·.poly) := by
      intro x hx
      have hfrom : ∃ k : Fin 5, (pop5 (A k) > 1 ∧ x = A k) ∨ (pop5 (B k) > 1 ∧ x = B k) := by
        unfold pm preMaskOf at hx
        have hfold_bit : ∀ (ks : List (Fin 5)) (acc : Nat),
            ((ks.foldl (fun m k =>
              let m1 := if pop5 (A k) > 1 then m ||| (1 <<< A k) else m
              if pop5 (B k) > 1 then m1 ||| (1 <<< B k) else m1) acc).testBit x = true) →
            acc.testBit x = true ∨ ∃ k ∈ ks, (pop5 (A k) > 1 ∧ x = A k) ∨ (pop5 (B k) > 1 ∧ x = B k) := by
          intro ks; induction ks with
          | nil => intro acc h; exact Or.inl h
          | cons k ks ih =>
            intro acc h
            rcases ih _ h with h1 | ⟨k', hk', hcond⟩
            · have htb_sh : ∀ y, (1 <<< y).testBit x = true → x = y := by
                intro y hy; rw [Nat.testBit_shiftLeft] at hy
                by_cases hxy : x = y
                · exact hxy
                · by_cases hle : y ≤ x
                  · cases hm : x - y with
                    | zero => omega
                    | succ m =>
                      have h1m : (1 : Nat).testBit (m + 1) = false := by simp [Nat.testBit_succ]
                      rw [hm, h1m] at hy; simp only [Bool.and_false] at hy; cases hy
                  · simp [hle] at hy
              by_cases hb : pop5 (B k) > 1
              · simp only [hb, ↓reduceIte, Nat.testBit_or] at h1
                rcases Bool.or_eq_true_iff.mp h1 with h1 | hxb
                · by_cases ha : pop5 (A k) > 1
                  · simp only [ha, ↓reduceIte, Nat.testBit_or] at h1
                    rcases Bool.or_eq_true_iff.mp h1 with hacc | hxa
                    · exact Or.inl hacc
                    · exact Or.inr ⟨k, List.mem_cons_self .., Or.inl ⟨ha, htb_sh _ hxa⟩⟩
                  · simp only [ha, ↓reduceIte] at h1; exact Or.inl h1
                · exact Or.inr ⟨k, List.mem_cons_self .., Or.inr ⟨hb, htb_sh _ hxb⟩⟩
              · simp only [hb, ↓reduceIte] at h1
                by_cases ha : pop5 (A k) > 1
                · simp only [ha, ↓reduceIte, Nat.testBit_or] at h1
                  rcases Bool.or_eq_true_iff.mp h1 with hacc | hxa
                  · exact Or.inl hacc
                  · exact Or.inr ⟨k, List.mem_cons_self .., Or.inl ⟨ha, htb_sh _ hxa⟩⟩
                · simp only [ha, ↓reduceIte] at h1; exact Or.inl h1
            · exact Or.inr ⟨k', List.mem_cons_of_mem _ hk', hcond⟩
        rcases hfold_bit (List.finRange 5) 0 hx with h0 | ⟨k, _, hc⟩
        · simp at h0
        · exact ⟨k, hc⟩
      obtain ⟨k, ⟨hpop, rfl⟩ | ⟨hpop, rfl⟩⟩ := hfrom
      · have hnotbm : baseBm.testBit (A k) = false := by
          have ha32 : A k < 32 := by rcases hAB_eq k with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h ▸ (nlArr k).ha | exact h ▸ (nlArr k).hb
          have : ∀ y : Fin 32, pop5 y.val > 1 → baseBm.testBit y.val = false := by decide
          exact this ⟨A k, ha32⟩ hpop
        obtain ⟨hna, hnb⟩ := hex_nl_in (nlArr k) (hnl_mem k)
        rcases hAB_eq k with ⟨ha, _⟩ | ⟨_, hb⟩
        · rw [ha] at hna
          rcases hna with hbm | ⟨l, hl, hl0, hlp⟩
          · rw [hnotbm] at hbm; cases hbm
          · exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, beq_iff_eq.mpr hl0⟩, hlp⟩
        · rw [hb] at hnb
          rcases hnb with hbm | ⟨l, hl, hl0, hlp⟩
          · rw [hnotbm] at hbm; cases hbm
          · exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, beq_iff_eq.mpr hl0⟩, hlp⟩
      · have hnotbm : baseBm.testBit (B k) = false := by
          have hb32 : B k < 32 := by rcases hAB_eq k with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h ▸ (nlArr k).hb | exact h ▸ (nlArr k).ha
          have : ∀ y : Fin 32, pop5 y.val > 1 → baseBm.testBit y.val = false := by decide
          exact this ⟨B k, hb32⟩ hpop
        obtain ⟨hna, hnb⟩ := hex_nl_in (nlArr k) (hnl_mem k)
        rcases hAB_eq k with ⟨_, hb⟩ | ⟨ha, _⟩
        · rw [hb] at hnb
          rcases hnb with hbm | ⟨l, hl, hl0, hlp⟩
          · rw [hnotbm] at hbm; cases hbm
          · exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, beq_iff_eq.mpr hl0⟩, hlp⟩
        · rw [ha] at hna
          rcases hna with hbm | ⟨l, hl, hl0, hlp⟩
          · rw [hnotbm] at hbm; cases hbm
          · exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, beq_iff_eq.mpr hl0⟩, hlp⟩

    have hpm_bits32 : ∀ x, pm.testBit x = true → x < 32 := by
      intro x hx
      have hpm_lt : pm < 2 ^ 32 := by
        unfold pm preMaskOf
        have hf : ∀ (ks : List (Fin 5)) (acc : Nat), acc < 2 ^ 32 →
            ks.foldl (fun m k =>
              let m1 := if pop5 (A k) > 1 then m ||| (1 <<< A k) else m
              if pop5 (B k) > 1 then m1 ||| (1 <<< B k) else m1) acc < 2 ^ 32 := by
          intro ks; induction ks with
          | nil => intro acc h; exact h
          | cons k ks ih =>
            intro acc h; simp only [List.foldl_cons]; apply ih
            have hA32 : A k < 32 := by rcases hAB_eq k with ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h ▸ (nlArr k).ha | exact h ▸ (nlArr k).hb
            have hB32 : B k < 32 := by rcases hAB_eq k with ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h ▸ (nlArr k).hb | exact h ▸ (nlArr k).ha
            have h1 : (if pop5 (A k) > 1 then acc ||| (1 <<< A k) else acc) < 2 ^ 32 := by
              split
              · exact Nat.or_lt_two_pow h (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) hA32)
              · exact h
            split
            · exact Nat.or_lt_two_pow h1 (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by omega : 1 < 2) hB32)
            · exact h1
        exact hf (List.finRange 5) 0 (by decide)
      apply Classical.byContradiction; intro hge
      have h0 : pm.testBit x = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hpm_lt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 32 ≤ x)))
      rw [h0] at hx; cases hx

    let pmList := (List.range 32).filter (fun x => pm.testBit x)
    have hpmList_len : pmList.length = pop32 pm := by
      unfold pmList pop32
      suffices ∀ (xs : List Nat) (acc : Nat), (xs.filter (fun x => pm.testBit x)).length + acc =
          xs.foldl (fun a i => if pm.testBit i then a + 1 else a) acc by
        simpa [Nat.add_zero] using this (List.range 32) 0
      intro xs; induction xs with
      | nil => intro acc; simp
      | cons x xs ih =>
        intro acc; cases h : pm.testBit x <;> simp [h]
        · exact ih acc
        · rw [← ih (acc + 1)]; omega
    have hpmList_nd : pmList.Nodup := nodup_filter _ List.nodup_range
    have hnp_le_d0 : pop32 pm ≤ d0Lins.length := by
      rw [← hpmList_len]
      have hle := nodup_length_le_of_subset hpmList_nd (fun x hx => hpm_in_d0 x (List.mem_filter.mp hx).2)
      simpa using hle

    -- 5. Membership in `allBases5` and refutation via our 3 fast kernel certificates!
    have hmem_b : (i0, i1, i2, i3, i4) ∈ allBases5 := by
      unfold allBases5
      rw [List.mem_flatMap]; refine ⟨i0, List.mem_range.mpr (hidx_lt10 ⟨0, by decide⟩), ?_⟩
      rw [List.mem_flatMap]; refine ⟨i1, List.mem_range.mpr (hidx_lt10 ⟨1, by decide⟩), ?_⟩
      simp only [show ¬ (i1 ≤ i0) by omega, ↓reduceIte]
      rw [List.mem_flatMap]; refine ⟨i2, List.mem_range.mpr (hidx_lt10 ⟨2, by decide⟩), ?_⟩
      simp only [show ¬ (i2 ≤ i1) by omega, ↓reduceIte]
      rw [List.mem_flatMap]; refine ⟨i3, List.mem_range.mpr (hidx_lt10 ⟨3, by decide⟩), ?_⟩
      simp only [show ¬ (i3 ≤ i2) by omega, ↓reduceIte]
      rw [List.mem_filterMap]; refine ⟨i4, List.mem_range.mpr (hidx_lt10 ⟨4, by decide⟩), ?_⟩
      simp only [show ¬ (i4 ≤ i3) by omega, ↓reduceIte]
      have : isBasis5 (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask
          (decomps[i3]!).mask (decomps[i4]!).mask = true := hbasis5
      simp [this]
    have hmem3 : ∀ s : Fin 3, s.val ∈ [0, 1, 2] := fun s => by
      rcases s with ⟨s, hs⟩; match s, hs with | 0, _ | 1, _ | 2, _ => simp
    -- 5a. Rule out the single diagonal basis `(0, 1, 2, 5, 6)` via `cert_diag_np5`!
    by_cases hdiag : (i0, i1, i2, i3, i4) = (0, 1, 2, 5, 6)
    · rcases Prod.mk.inj hdiag with ⟨rfl, h1⟩
      rcases Prod.mk.inj h1 with ⟨rfl, h2⟩
      rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
      rcases Prod.mk.inj h3 with ⟨rfl, rfl⟩
      have h0 := List.all_eq_true.mp cert_diag_np5 (skipOf ⟨0, by decide⟩).val (hmem3 _)
      have h1 := List.all_eq_true.mp h0 (skipOf ⟨1, by decide⟩).val (hmem3 _)
      have h2 := List.all_eq_true.mp h1 (skipOf ⟨2, by decide⟩).val (hmem3 _)
      have h3 := List.all_eq_true.mp h2 (skipOf ⟨3, by decide⟩).val (hmem3 _)
      have h4 := List.all_eq_true.mp h3 (skipOf ⟨4, by decide⟩).val (hmem3 _)
      dsimp only at h4
      have hpm_eq : pm =
          pairMask (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) |||
          pairMask (A ⟨1, by decide⟩) (B ⟨1, by decide⟩) |||
          pairMask (A ⟨2, by decide⟩) (B ⟨2, by decide⟩) |||
          pairMask (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) |||
          pairMask (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) := preMaskOf_eq_or A B
      have hge5 : pop32Byte pm ≥ 5 := by
        rw [hpm_eq]; exact of_decide_eq_true h4
      rw [pop32Byte_eq_pop32] at hge5
      omega
    · -- 5b. Non-diagonal basis: `cert_zero_helper` refutes ANY zero-helper or linear-helper circuit!
      have hzh_raw := List.all_eq_true.mp cert_zero_helper _ hmem_b
      dsimp only at hzh_raw
      have hne_b : ((i0, i1, i2, i3, i4) == (0, 1, 2, 5, 6)) = false := beq_false_of_ne hdiag
      simp only [hne_b, Bool.false_eq_true, ↓reduceIte] at hzh_raw
      let T0 : Fin 5 → Nat := fun k => (decomps[idxArr k]!).t0
      let T1 : Fin 5 → Nat := fun k => (decomps[idxArr k]!).t1
      have hinv_fn_eq : (fun j : Fin 5 => match j with
          | ⟨0, _⟩ => findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask 1
          | ⟨1, _⟩ => findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask 2
          | ⟨2, _⟩ => findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask 4
          | ⟨3, _⟩ => findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask 8
          | ⟨4, _⟩ => findInvRow (decomps[i0]!).mask (decomps[i1]!).mask (decomps[i2]!).mask (decomps[i3]!).mask (decomps[i4]!).mask 16) = inv := by
        funext j; rcases j with ⟨j, hj⟩; match j, hj with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
      have hT0_eq : (fun k : Fin 5 => match k with
          | ⟨0,_⟩ => (decomps[i0]!).t0 | ⟨1,_⟩ => (decomps[i1]!).t0 | ⟨2,_⟩ => (decomps[i2]!).t0
          | ⟨3,_⟩ => (decomps[i3]!).t0 | ⟨4,_⟩ => (decomps[i4]!).t0) = T0 := by
        funext k; rcases k with ⟨k, hk⟩; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
      have hT1_eq : (fun k : Fin 5 => match k with
          | ⟨0,_⟩ => (decomps[i0]!).t1 | ⟨1,_⟩ => (decomps[i1]!).t1 | ⟨2,_⟩ => (decomps[i2]!).t1
          | ⟨3,_⟩ => (decomps[i3]!).t1 | ⟨4,_⟩ => (decomps[i4]!).t1) = T1 := by
        funext k; rcases k with ⟨k, hk⟩; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
      rw [hinv_fn_eq, hT0_eq, hT1_eq] at hzh_raw
      -- Re-index `cArr` to canonical `(T0 k, T1 k)` via `shift_coset_eq`!
      have hc_ex : ∀ k : Fin 5, ∃ c' : Fin 4, shiftOf (T0 k) (T1 k) c'.val = shiftOf (A k) (B k) (cArr k).val := by
        intro k
        have hbang : decomps[idxArr k]! = decomps[idxArr k]'(hidx_lt10 k) := getElem!_pos decomps (idxArr k) (hidx_lt10 k)
        obtain ⟨c', hc'⟩ := shift_coset_eq ⟨idxArr k, hidx_lt10 k⟩ (skipOf k) (cArr k)
        refine ⟨c', ?_⟩
        dsimp only [T0, T1, A, B]; rw [hbang]; exact hc'.symm
      let cArr' : Fin 5 → Fin 4 := fun k => Classical.choose (hc_ex k)
      have hcArr'_eq : ∀ k : Fin 5, shiftOf (T0 k) (T1 k) (cArr' k).val = shiftOf (A k) (B k) (cArr k).val :=
        fun k => Classical.choose_spec (hc_ex k)
      have hno_lin_helper : (∀ l ∈ d1Lins, l.poly < 32 ∨ ∃ j : Fin 5, l.poly = asconPoly j) → False :=
        no_lin_helper_contradiction nls lins d0Lins d1Lins nlArr inv T0 T1 cArr' coordToQuad rfl rfl hnls_eq
          (fun k => by have : ∀ i : Fin 10, (decomps[i.val]!).t0 < 32 ∧ (decomps[i.val]!).t1 < 32 := by decide
                       exact this ⟨idxArr k, hidx_lt10 k⟩)
          (fun k => (hnl_lin k).trans (hcArr'_eq k).symm)
          hnl_quad (fun j => (hinv_spec j).1) hctq_xor hctq_inj hctq_k hctq_inv hctq_0 hascon_in_d1 hex_lin_in hzh_raw
      -- Now split on `d1Lins.length = 5` (0 helpers) vs `d1Lins.length ≥ 6` (≥ 1 helper, so `d0Lins.length ≤ 3`)!
      by_cases hd1_eq5 : d1Lins.length = 5
      · apply hno_lin_helper
        intro l hl
        have hmem := subset_of_length_eq hascon_nd
          (fun y hy => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy; exact hascon_in_d1 j)
          (by simp [hd1_eq5]) l.poly (List.mem_map.mpr ⟨l, hl, rfl⟩)
        obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem
        exact Or.inr ⟨j, hj.symm⟩
      · -- `d1Lins.length ≥ 6`, hence `d0Lins.length ≤ 3`, hence `pop32 pm ≤ 3`!
        have hd0_le3 : d0Lins.length ≤ 3 := by omega
        have hnp_le3 : pop32 pm ≤ 3 := Nat.le_trans hnp_le_d0 hd0_le3
        -- Unpack `cert_p3_quad` for `(i0..i4)` and `skipOf 0..4`!
        have hp3_b := List.all_eq_true.mp cert_p3_quad _ hmem_b
        have hp3_0 := List.all_eq_true.mp hp3_b (skipOf ⟨0, by decide⟩).val (hmem3 _)
        have hp3_1 := List.all_eq_true.mp hp3_0 (skipOf ⟨1, by decide⟩).val (hmem3 _)
        dsimp only at hp3_1
        have hpm_eq : pm =
            pairMask (A ⟨0, by decide⟩) (B ⟨0, by decide⟩) |||
            pairMask (A ⟨1, by decide⟩) (B ⟨1, by decide⟩) |||
            pairMask (A ⟨2, by decide⟩) (B ⟨2, by decide⟩) |||
            pairMask (A ⟨3, by decide⟩) (B ⟨3, by decide⟩) |||
            pairMask (A ⟨4, by decide⟩) (B ⟨4, by decide⟩) := preMaskOf_eq_or A B
        let pm0 := pairMask (A ⟨0, by decide⟩) (B ⟨0, by decide⟩)
        let pm1 := pm0 ||| pairMask (A ⟨1, by decide⟩) (B ⟨1, by decide⟩)
        let pm2 := pm1 ||| pairMask (A ⟨2, by decide⟩) (B ⟨2, by decide⟩)
        let pm3 := pm2 ||| pairMask (A ⟨3, by decide⟩) (B ⟨3, by decide⟩)
        have hle3 : pop32 pm3 ≤ 3 := by
          have : pop32 pm3 ≤ pop32 pm := by rw [hpm_eq]; exact pop32_mono_or _ _
          omega
        have hle2 : pop32 pm2 ≤ 3 := by
          have : pop32 pm2 ≤ pop32 pm3 := pop32_mono_or _ _
          omega
        have hle1 : pop32 pm1 ≤ 3 := by
          have : pop32 pm1 ≤ pop32 pm2 := pop32_mono_or _ _
          omega
        have hnot1 : ¬ (pop32Byte pm1 > 3) := by rw [pop32Byte_eq_pop32]; omega
        have hnot2 : ¬ (pop32Byte pm2 > 3) := by rw [pop32Byte_eq_pop32]; omega
        have hnot3 : ¬ (pop32Byte pm3 > 3) := by rw [pop32Byte_eq_pop32]; omega
        have hnot4 : ¬ (pop32Byte pm > 3) := by rw [pop32Byte_eq_pop32]; omega
        rw [if_neg hnot1] at hp3_1
        have hp3_2 := List.all_eq_true.mp hp3_1 (skipOf ⟨2, by decide⟩).val (hmem3 _)
        rw [if_neg hnot2] at hp3_2
        have hp3_3 := List.all_eq_true.mp hp3_2 (skipOf ⟨3, by decide⟩).val (hmem3 _)
        rw [if_neg hnot3] at hp3_3
        have hp3_4 := List.all_eq_true.mp hp3_3 (skipOf ⟨4, by decide⟩).val (hmem3 _)
        have hpm_raw : pairMask (pairOfSkip decomps[i0]! (skipOf ⟨0, by decide⟩).val).1 (pairOfSkip decomps[i0]! (skipOf ⟨0, by decide⟩).val).2 |||
            pairMask (pairOfSkip decomps[i1]! (skipOf ⟨1, by decide⟩).val).1 (pairOfSkip decomps[i1]! (skipOf ⟨1, by decide⟩).val).2 |||
            pairMask (pairOfSkip decomps[i2]! (skipOf ⟨2, by decide⟩).val).1 (pairOfSkip decomps[i2]! (skipOf ⟨2, by decide⟩).val).2 |||
            pairMask (pairOfSkip decomps[i3]! (skipOf ⟨3, by decide⟩).val).1 (pairOfSkip decomps[i3]! (skipOf ⟨3, by decide⟩).val).2 |||
            pairMask (pairOfSkip decomps[i4]! (skipOf ⟨4, by decide⟩).val).1 (pairOfSkip decomps[i4]! (skipOf ⟨4, by decide⟩).val).2 = pm := hpm_eq.symm
        rw [hpm_raw, if_neg hnot4] at hp3_4
        have hnp_eq3 : pop32 pm = 3 := by
          by_cases hlt3 : pop32Byte pm < 3
          · simp only [hlt3, ↓reduceIte] at hp3_4; cases hp3_4
          · rw [pop32Byte_eq_pop32] at hlt3; omega
        have hnot_lt3 : ¬ (pop32Byte pm < 3) := by rw [pop32Byte_eq_pop32]; omega
        simp only [hnot_lt3, ↓reduceIte] at hp3_4
        -- Therefore `d0Lins.length = 3` and `d1Lins.length = 6`!
        have hd0_eq3 : d0Lins.length = 3 := by omega
        have hd1_le6 : d1Lins.length ≤ 6 := by omega
        have hd0_sub : ∀ l ∈ d0Lins, pm.testBit l.poly = true := by
          intro l hl
          have hmem := subset_of_length_eq hpmList_nd
            (fun x hx => hpm_in_d0 x (List.mem_filter.mp hx).2)
            (by simp [hpmList_len, hnp_eq3, hd0_eq3])
            l.poly (List.mem_map.mpr ⟨l, hl, rfl⟩)
          exact (List.mem_filter.mp hmem).2
        -- Prove `d0ClosureOk pm = true` via `d0Closure_sound`!
        have hd0_ok : d0ClosureOk pm = true := by
          let fwd := (d0Lins.map (·.poly)).reverse
          apply d0Closure_sound pm hpm_bits32 fwd (by simp [fwd, hd0_eq3])
          · intro x hx; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
            exact Or.inl (hd0_sub l hl)
          · intro x hx; exact Or.inl (List.mem_reverse.mpr (hpm_in_d0 x hx))
          · intro i hi
            have hi' : i < d0Lins.length := by simpa [fwd] using hi
            let ridx := d0Lins.length - 1 - i
            have hridx : ridx < d0Lins.length := by omega
            have hfwd_eq : fwd[i] = d0Lins[ridx].poly := by simp [fwd, List.getElem_reverse, ridx]
            rw [hfwd_eq]
            have hex_pos : ∀ (ls : List LinInfo) (p : LinInfo → Bool) (r : Nat) (hr : r < (ls.filter p).length),
                ∃ pos, ∃ hpos : pos < ls.length, ls[pos] = (ls.filter p)[r] ∧
                  ∀ e ∈ ls.drop (pos + 1), p e = true → ∃ r' > r, ∃ hr' : r' < (ls.filter p).length, (ls.filter p)[r'] = e := by
              intro ls p; induction ls with
              | nil => intro r hr; simp at hr
              | cons a as iha =>
                intro r hr; by_cases hpa : p a = true
                · simp only [List.filter_cons, hpa, ↓reduceIte] at hr ⊢
                  cases r with
                  | zero =>
                    refine ⟨0, by simp, by simp, ?_⟩
                    intro e he hpe; have hmem : e ∈ as.filter p := List.mem_filter.mpr ⟨by simpa using he, hpe⟩
                    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
                    exact ⟨k + 1, by omega, by simp; omega, by simp⟩
                  | succ r =>
                    obtain ⟨pos, hpos, hpeq, hdrop⟩ := iha r (by simp at hr; omega)
                    refine ⟨pos + 1, by simp; omega, by simpa using hpeq, ?_⟩
                    intro e he hpe; obtain ⟨r', hr', hr'lt, hreq⟩ := hdrop e (by simpa using he) hpe
                    exact ⟨r' + 1, by omega, by simp; omega, by simpa using hreq⟩
                · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hr ⊢
                  obtain ⟨pos, hpos, hpeq, hdrop⟩ := iha r hr
                  exact ⟨pos + 1, by simp; omega, hpeq, fun e he hpe => hdrop e (by simpa using he) hpe⟩
            obtain ⟨pos, hpos, hpeq, hdrop⟩ := hex_pos lins (fun l => l.depth == 0) ridx hridx
            have hd0_pos : lins[pos].depth = 0 := by
              have : d0Lins[ridx] ∈ d0Lins := List.getElem_mem hridx
              rw [← hpeq] at this; exact beq_iff_eq.mp (List.mem_filter.mp this).2
            obtain ⟨h0_in, _⟩ := hex_lin_in pos hpos
            obtain ⟨hu_in, hv_in⟩ := h0_in hd0_pos
            have hlift : ∀ x, (baseBm.testBit x = true ∨ ∃ e ∈ lins.drop (pos + 1), e.depth = 0 ∧ e.poly = x) →
                x < 32 ∧ (baseBm.testBit x = true ∨ ∃ j, j < i ∧ fwd[j]? = some x) := by
              intro x hx; rcases hx with hbx | ⟨e, he, he0, rfl⟩
              · refine ⟨?_, Or.inl hbx⟩
                apply Classical.byContradiction; intro hge; have hlt : baseBm < 2 ^ 32 := by decide
                have h0 : baseBm.testBit x = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 32 ≤ x)))
                rw [h0] at hbx; cases hbx
              · obtain ⟨r', hr', hr'lt, hreq⟩ := hdrop e he (beq_iff_eq.mpr he0)
                have hr'lt' : r' < d0Lins.length := hr'lt
                let j := d0Lins.length - 1 - r'
                have hjlt : j < i := by omega
                have hjfwd : fwd[j]? = some e.poly := by
                  rw [List.getElem?_eq_getElem (by simp [fwd]; omega)]
                  have hidx : d0Lins.length - 1 - j = r' := by omega
                  simp only [fwd, List.getElem_reverse, List.length_map, List.getElem_map, hidx]
                  exact congrArg (fun x : LinInfo => some x.poly) hreq
                have he32 : e.poly < 32 := hpm_bits32 _ (hd0_sub e (by rw [← hreq]; exact List.getElem_mem hr'lt))
                exact ⟨he32, Or.inr ⟨j, hjlt, hjfwd⟩⟩
            obtain ⟨hu32, hu_f⟩ := hlift _ hu_in; obtain ⟨hv32, hv_f⟩ := hlift _ hv_in
            rw [← hpeq]; have hpl := lins[pos].hpoly
            cases hix : lins[pos].isXor
            · simp only [hix, Bool.false_eq_true, ↓reduceIte] at hpl
              rcases hpl with h0 | hu | hv
              · left; rw [h0]; decide
              · rw [hu]; right; exact ⟨lins[pos].u, 0, hu32, by decide, hu_f, Or.inl (by decide), by simp⟩
              · rw [hv]; right; exact ⟨lins[pos].v, 0, hv32, by decide, hv_f, Or.inl (by decide), by simp⟩
            · simp only [hix, ↓reduceIte] at hpl
              right; exact ⟨lins[pos].u, lins[pos].v, hu32, hv32, hu_f, hv_f, hpl.symm⟩
        simp only [hd0_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp3_4
        -- Extract the single extra wire `h` of `d1Lins`!
        obtain ⟨h, hh⟩ := subset_plus_one hascon_nd
          (fun y hy => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy; exact hascon_in_d1 j)
          (by simp [hd1_le6])
        by_cases hh_lin : h < 32
        · apply hno_lin_helper
          intro l hl
          rcases hh l.poly (List.mem_map.mpr ⟨l, hl, rfl⟩) with heq | hmem
          · exact Or.inl (heq ▸ hh_lin)
          · obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem; exact Or.inr ⟨j, hj.symm⟩
        · exact p3_quad_contradiction nls lins d0Lins d1Lins nlArr inv A B cArr coordToQuad pm h
            rfl rfl hnl_mem hnls_eq hnl_lin hnl_quad hq_cov (fun j => (hinv_spec j).1)
            hctq_xor hctq_inj hctq_k hctq_inv hctq_0 hascon_in_d1
            (fun i hi => (hex_lin_in i hi).2) hpm_bits32 hd0_sub hh hh_lin hp3_4
  | [] => simp at hsort_len
  | [_] => simp at hsort_len
  | [_, _] => simp at hsort_len
  | [_, _, _] => simp at hsort_len
  | [_, _, _, _] => simp at hsort_len
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at hsort_len

end Crypto.Claims.CZ_rec_ascon_gates_not_s14
