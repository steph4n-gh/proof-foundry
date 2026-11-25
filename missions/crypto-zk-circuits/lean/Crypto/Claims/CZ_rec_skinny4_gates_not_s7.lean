import Crypto.Core
import Crypto.Statements.CZ_rec_skinny4_gates

namespace Crypto.Claims.CZ_rec_skinny4_gates_not_s7

open Crypto Crypto.B2Op

/-!
  Exact optimality proof for the SKINNY 4-bit S-box over the full binary basis B2:
  `¬ Crypto.Statements.CZ_rec_skinny4_gates.Record 7`.
  Together with the 8-gate champion (`CZ_rec_skinny4_gates_s8`), this proves the exact
  minimum B2 circuit size of the SKINNY 4-bit S-box is 8 gates.

  Proof architecture:
  1. Normalize every 16-bit wire truth table `t < 65536` to `norm t` with bit 0 equal to 0.
     Under normalization, all 16 binary operations in `B2Op` collapse to `{0, a, b}` plus
     the 5 symmetric binary operations `ops5` (`^`, `&`, `a & ~b`, `~a & b`, `|`).
  2. Model normalized circuit reachability inductively (`Reach k w rem`) and prove:
     - Monotonicity in `w`, `rem`, and `k`;
     - Pigeonhole bound (`rem.length ≤ k` when `rem` is nodup and disjoint from `w`);
     - Dominant-move lemma (any target already producible from `w` can be scheduled first);
     - Order-symmetry breaking for independent consecutive helper gates.
  3. Prove soundness of the pruned decision procedure `noReach` with respect to `Reach`.
  4. Certify `noReach 7 false initW initRem = true` directly in the Lean 4 kernel
     via `decide +kernel` (standard axioms only).
-/

private def mask16 : Nat := 65535

private def norm16 (t : Nat) : Nat :=
  if t.testBit 0 then mask16 ^^^ t else t

private def isOps5 (a b v : Nat) : Prop :=
  v = (a ^^^ b) ∨
  v = (a &&& b) ∨
  v = (a &&& (mask16 ^^^ b)) ∨
  v = ((mask16 ^^^ a) &&& b) ∨
  v = (a ||| b)

private theorem testBit_mask16 (k : Nat) : mask16.testBit k = decide (k < 16) := by
  have h : mask16 = 2 ^ 16 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

private theorem testBit_lt_65536 {t k : Nat} (ht : t < 65536) (hk : 16 ≤ k) :
    t.testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have hpow : 65536 ≤ 2 ^ k := by
    have : (2 : Nat) ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  omega

private theorem lt_65536_of_testBit {t : Nat} (h : ∀ k, 16 ≤ k → t.testBit k = false) :
    t < 65536 := by
  cases Nat.lt_or_ge t 65536 with
  | inl hlt => exact hlt
  | inr hge =>
    exfalso
    have h1 : 2 ^ 16 ≤ t := by omega
    have hne : t ≠ 0 := by omega
    have hlog : 16 ≤ Nat.log2 t := by
      rw [Nat.le_log2 hne]
      exact h1
    have htb : t.testBit (Nat.log2 t) = true := Nat.testBit_log2 hne
    have hf := h (Nat.log2 t) hlog
    rw [htb] at hf
    cases hf

private theorem xor_lt_65536 {a b : Nat} (ha : a < 65536) (hb : b < 65536) :
    (a ^^^ b) < 65536 := by
  apply lt_65536_of_testBit
  intro k hk
  rw [Nat.testBit_xor, testBit_lt_65536 ha hk, testBit_lt_65536 hb hk]
  rfl

private theorem land_lt_65536 {a b : Nat} (ha : a < 65536) :
    (a &&& b) < 65536 := by
  apply lt_65536_of_testBit
  intro k hk
  rw [Nat.testBit_and, testBit_lt_65536 ha hk]
  rfl

private theorem land_lt_65536_right {a b : Nat} (hb : b < 65536) :
    (a &&& b) < 65536 := by
  apply lt_65536_of_testBit
  intro k hk
  rw [Nat.testBit_and, testBit_lt_65536 hb hk]
  simp

private theorem lor_lt_65536 {a b : Nat} (ha : a < 65536) (hb : b < 65536) :
    (a ||| b) < 65536 := by
  apply lt_65536_of_testBit
  intro k hk
  rw [Nat.testBit_or, testBit_lt_65536 ha hk, testBit_lt_65536 hb hk]
  rfl

private theorem isOps5_lt {a b v : Nat} (ha : a < 65536) (hb : b < 65536) (h : isOps5 a b v) :
    v < 65536 := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact xor_lt_65536 ha hb
  · exact land_lt_65536 ha
  · exact land_lt_65536 ha
  · exact land_lt_65536_right hb
  · exact lor_lt_65536 ha hb

private theorem isOps5_symm {a b v : Nat} (h : isOps5 a b v) : isOps5 b a v := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · left; exact Nat.xor_comm a b
  · right; left; exact Nat.and_comm a b
  · right; right; right; left; exact Nat.and_comm a (mask16 ^^^ b)
  · right; right; left; exact Nat.and_comm (mask16 ^^^ a) b
  · right; right; right; right; exact Nat.or_comm a b

private theorem isOps5_zero_left {b v : Nat} (hb : b < 65536) (h : isOps5 0 b v) :
    v = 0 ∨ v = b := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · right; exact Nat.zero_xor b
  · left; exact Nat.zero_and b
  · left; exact Nat.zero_and (mask16 ^^^ b)
  · right
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, testBit_mask16]
    by_cases hk : k < 16
    · simp [hk]
    · have hge : 16 ≤ k := by omega
      simp [hk, testBit_lt_65536 hb hge]
  · right; exact Nat.zero_or b

private theorem isOps5_self {a v : Nat} (ha : a < 65536) (h : isOps5 a a v) :
    v = 0 ∨ v = a := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · left; exact Nat.xor_self a
  · right; exact Nat.and_self a
  · left
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_mask16, Nat.zero_testBit]
    by_cases hk : k < 16
    · cases a.testBit k <;> simp [hk]
    · have hge : 16 ≤ k := by omega
      simp [hk, testBit_lt_65536 ha hge]
  · left
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_mask16, Nat.zero_testBit]
    by_cases hk : k < 16
    · cases a.testBit k <;> simp [hk]
    · have hge : 16 ≤ k := by omega
      simp [hk, testBit_lt_65536 ha hge]
  · right; exact Nat.or_self a

private theorem norm16_lt {t : Nat} (ht : t < 65536) : norm16 t < 65536 := by
  unfold norm16
  split
  · exact xor_lt_65536 (by decide) ht
  · exact ht

private theorem testBit_norm16_zero {t : Nat} : (norm16 t).testBit 0 = false := by
  unfold norm16
  cases h : t.testBit 0
  · simp [h]
  · simp only [↓reduceIte]
    rw [Nat.testBit_xor, testBit_mask16, h]
    rfl

private theorem testBit_norm16 {t k : Nat} (hk : k < 16) :
    (norm16 t).testBit k = xor (t.testBit k) (t.testBit 0) := by
  unfold norm16
  cases h : t.testBit 0
  · simp
  · simp [Nat.testBit_xor, testBit_mask16, hk]

private theorem evalOpTT_lt {op : B2Op} {t1 t2 : Nat} (h1 : t1 < 65536) (h2 : t2 < 65536) :
    evalOpTT mask16 op t1 t2 < 65536 := by
  apply lt_65536_of_testBit
  intro k hk
  have hlt : ¬ (k < 16) := by omega
  have hm : mask16.testBit k = false := by rw [testBit_mask16]; simp [hlt]
  have ht1 : t1.testBit k = false := testBit_lt_65536 h1 hk
  have ht2 : t2.testBit k = false := testBit_lt_65536 h2 hk
  unfold evalOpTT
  cases op with
  | mk b00 b01 b10 b11 =>
    cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
      simp [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hm, ht1, ht2]

private theorem testBit_evalOpTT_mask16 (op : B2Op) (t1 t2 k : Nat) (hk : k < 16) :
    (evalOpTT mask16 op t1 t2).testBit k = op.eval (t1.testBit k) (t2.testBit k) := by
  have hm : mask16.testBit k = true := by rw [testBit_mask16]; simp [hk]
  unfold evalOpTT
  cases op with
  | mk b00 b01 b10 b11 =>
    cases h1 : t1.testBit k <;> cases h2 : t2.testBit k <;>
      cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
      simp [B2Op.eval, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hm, h1, h2]

private theorem eval_norm_table (op : B2Op) (p1 p2 ba bb : Bool) :
    xor (op.eval (xor ba p1) (xor bb p2)) (op.eval p1 p2) =
    match ba, bb with
    | false, false => false
    | false, true  => xor (op.eval p1 (!p2)) (op.eval p1 p2)
    | true,  false => xor (op.eval (!p1) p2) (op.eval p1 p2)
    | true,  true  => xor (op.eval (!p1) (!p2)) (op.eval p1 p2) := by
  cases ba <;> cases bb <;> cases p1 <;> cases p2 <;>
    cases op with | mk b00 b01 b10 b11 => cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> rfl

private theorem norm16_evalOpTT_cases (op : B2Op) {t1 t2 : Nat} (h1 : t1 < 65536) (h2 : t2 < 65536) :
    let a := norm16 t1
    let b := norm16 t2
    let v := norm16 (evalOpTT mask16 op t1 t2)
    v = 0 ∨ v = a ∨ v = b ∨ isOps5 a b v := by
  intro a b v
  have ha : a < 65536 := norm16_lt h1
  have hb : b < 65536 := norm16_lt h2
  have hv : v < 65536 := norm16_lt (evalOpTT_lt h1 h2)
  have hbit : ∀ k, k < 16 →
      v.testBit k = xor (op.eval (xor (a.testBit k) (t1.testBit 0))
                                 (xor (b.testBit k) (t2.testBit 0)))
                        (op.eval (t1.testBit 0) (t2.testBit 0)) := by
    intro k hk
    dsimp only [v]
    rw [testBit_norm16 hk, testBit_evalOpTT_mask16 op t1 t2 k hk,
        testBit_evalOpTT_mask16 op t1 t2 0 (by decide)]
    have ha' : a.testBit k = xor (t1.testBit k) (t1.testBit 0) := testBit_norm16 hk
    have hb' : b.testBit k = xor (t2.testBit k) (t2.testBit 0) := testBit_norm16 hk
    rw [ha', hb']
    cases t1.testBit k <;> cases t1.testBit 0 <;> cases t2.testBit k <;> cases t2.testBit 0 <;> rfl
  let p1 := t1.testBit 0
  let p2 := t2.testBit 0
  let f01 := xor (op.eval p1 (!p2)) (op.eval p1 p2)
  let f10 := xor (op.eval (!p1) p2) (op.eval p1 p2)
  let f11 := xor (op.eval (!p1) (!p2)) (op.eval p1 p2)
  have hmatch : ∀ (target : Nat), target < 65536 →
      (∀ k, k < 16 → target.testBit k =
        match a.testBit k, b.testBit k with
        | false, false => false
        | false, true  => f01
        | true,  false => f10
        | true,  true  => f11) →
      v = target := by
    intro target htl htg
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 16
    · rw [hbit k hk, htg k hk]
      exact eval_norm_table op p1 p2 (a.testBit k) (b.testBit k)
    · have hge : 16 ≤ k := by omega
      rw [testBit_lt_65536 hv hge, testBit_lt_65536 htl hge]
  cases hf01 : f01 <;> cases hf10 : f10 <;> cases hf11 : f11
  · left
    apply hmatch 0 (by decide)
    intro k _
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]
  · right; right; right; right; left
    apply hmatch (a &&& b) (land_lt_65536 ha)
    intro k _
    rw [Nat.testBit_and]
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]
  · right; right; right; right; right; left
    apply hmatch (a &&& (mask16 ^^^ b)) (land_lt_65536 ha)
    intro k hk
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_mask16]
    cases a.testBit k <;> cases b.testBit k <;> simp [hk, hf01, hf10, hf11]
  · right; left
    apply hmatch a ha
    intro k _
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]
  · right; right; right; right; right; right; left
    apply hmatch ((mask16 ^^^ a) &&& b) (land_lt_65536_right hb)
    intro k hk
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_mask16]
    cases a.testBit k <;> cases b.testBit k <;> simp [hk, hf01, hf10, hf11]
  · right; right; left
    apply hmatch b hb
    intro k _
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]
  · right; right; right; left
    apply hmatch (a ^^^ b) (xor_lt_65536 ha hb)
    intro k _
    rw [Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]
  · right; right; right; right; right; right; right
    apply hmatch (a ||| b) (lor_lt_65536 ha hb)
    intro k _
    rw [Nat.testBit_or]
    cases a.testBit k <;> cases b.testBit k <;> simp [hf01, hf10, hf11]

/-! ## 2. Inductive Reachability Model & Core Structural Lemmas -/

private def StepFrom (w : List Nat) (v : Nat) : Prop :=
  ∃ a b, a ∈ w ∧ b ∈ w ∧ isOps5 a b v

private theorem StepFrom.mono {w w' : List Nat} {v : Nat}
    (hsub : ∀ x ∈ w, x ∈ w') (h : StepFrom w v) : StepFrom w' v := by
  rcases h with ⟨a, b, ha, hb, hop⟩
  exact ⟨a, b, hsub a ha, hsub b hb, hop⟩

private inductive Reach : Nat → List Nat → List Nat → Prop
  | done {k w rem} : (∀ t ∈ rem, t ∈ w) → Reach k w rem
  | step {k w rem v} : v ≠ 0 → v ∉ w → StepFrom w v → Reach k (v :: w) rem → Reach (k + 1) w rem

private theorem Reach.mono_k {k k' : Nat} {w rem : List Nat}
    (hle : k ≤ k') (h : Reach k w rem) : Reach k' w rem := by
  induction h generalizing k' with
  | done hsub => exact Reach.done hsub
  | step hv0 hvnot hv _ ih =>
    cases k' with
    | zero => omega
    | succ k'' =>
      exact Reach.step hv0 hvnot hv (ih (by omega))

private theorem Reach.mono_w {k : Nat} {w w' rem : List Nat}
    (hsub : ∀ x ∈ w, x ∈ w') (h : Reach k w rem) : Reach k w' rem := by
  induction h generalizing w' with
  | done hd => exact Reach.done (fun t ht => hsub t (hd t ht))
  | @step _ w0 _ v hv0 hvnot hv _ ih =>
    by_cases hmem : v ∈ w'
    · have hsub' : ∀ x ∈ v :: w0, x ∈ w' := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact hmem
        · exact hsub x hx'
      exact Reach.mono_k (Nat.le_succ _) (ih hsub')
    · have hsub' : ∀ x ∈ v :: w0, x ∈ v :: w' := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem v (hsub x hx')
      exact Reach.step hv0 hmem (StepFrom.mono hsub hv) (ih hsub')

private theorem Reach.mono_rem {k : Nat} {w rem rem' : List Nat}
    (hsub : ∀ t ∈ rem', t ∈ rem) (h : Reach k w rem) : Reach k w rem' := by
  induction h with
  | done hd => exact Reach.done (fun t ht => hd t (hsub t ht))
  | step hv0 hvnot hv _ ih => exact Reach.step hv0 hvnot hv (ih hsub)

private def eraseNat (t : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x == t then xs else x :: eraseNat t xs

private theorem mem_eraseNat_imp {t x : Nat} : ∀ {xs : List Nat}, x ∈ eraseNat t xs → x ∈ xs
  | [], h => by simp [eraseNat] at h
  | y :: ys, h => by
    simp only [eraseNat] at h
    split at h
    · exact List.mem_cons_of_mem y h
    · rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (mem_eraseNat_imp h')

private theorem not_mem_eraseNat_of_nodup {t : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → t ∉ eraseNat t xs
  | [], _ => by simp [eraseNat]
  | y :: ys, hnd => by
    have ⟨hny, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [eraseNat]
    by_cases heq : y = t
    · subst heq; simp [hny]
    · have hbeq : (y == t) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rintro (rfl | hmem)
      · exact heq rfl
      · exact not_mem_eraseNat_of_nodup hnd' hmem

private theorem nodup_eraseNat {t : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (eraseNat t xs).Nodup
  | [], _ => by simp [eraseNat]
  | y :: ys, hnd => by
    have ⟨hny, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [eraseNat]
    split
    · exact hnd'
    · exact List.nodup_cons.2 ⟨fun h => hny (mem_eraseNat_imp h), nodup_eraseNat hnd'⟩

private theorem length_eraseNat_of_mem {t : Nat} :
    ∀ {xs : List Nat}, t ∈ xs → (eraseNat t xs).length + 1 = xs.length
  | [], h => by cases h
  | y :: ys, h => by
    simp only [eraseNat]
    by_cases heq : y = t
    · subst heq; simp
    · have hbeq : (y == t) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.1 h with rfl | hmem
      · exact absurd rfl heq
      · have ih := length_eraseNat_of_mem hmem
        omega

private theorem Reach.pigeonhole :
    ∀ {k : Nat} {w rem : List Nat}, rem.Nodup → (∀ t ∈ rem, t ∉ w) → Reach k w rem →
      rem.length ≤ k
  | k, w, rem, _, hdisj, Reach.done hd => by
    cases rem with
    | nil => exact Nat.zero_le _
    | cons t ts =>
      exact absurd (hd t List.mem_cons_self) (hdisj t List.mem_cons_self)
  | _, w0, rem0, hnd, hdisj, Reach.step (k := k0) (v := v) _ _ _ hnext => by
    by_cases hvm : v ∈ rem0
    · have hrem' : Reach k0 (v :: w0) (eraseNat v rem0) :=
        Reach.mono_rem (fun t ht => mem_eraseNat_imp ht) hnext
      have hdisj' : ∀ t ∈ eraseNat v rem0, t ∉ v :: w0 := by
        intro t ht hmem
        rcases List.mem_cons.1 hmem with rfl | hmw
        · exact not_mem_eraseNat_of_nodup hnd ht
        · exact hdisj t (mem_eraseNat_imp ht) hmw
      have hle := Reach.pigeonhole (nodup_eraseNat hnd) hdisj' hrem'
      have hlen := length_eraseNat_of_mem hvm
      omega
    · have hdisj' : ∀ t ∈ rem0, t ∉ v :: w0 := by
        intro t ht hmem
        rcases List.mem_cons.1 hmem with rfl | hmw
        · exact hvm ht
        · exact hdisj t ht hmw
      have hle := Reach.pigeonhole hnd hdisj' hnext
      omega

private theorem Reach.remove_hit (t : Nat) :
    ∀ {k : Nat} {w rem : List Nat}, t ∈ rem → t ∉ w → Reach k w rem →
      ∃ k', k' + 1 = k ∧ Reach k' (t :: w) (eraseNat t rem)
  | _, _, _, ht, hnw, Reach.done hd => absurd (hd t ht) hnw
  | _, w, rem, ht, hnw, Reach.step (k := k0) (v := v) hv0 hvnot hv hnext => by
    by_cases hvt : v = t
    · subst hvt
      exact ⟨k0, rfl, Reach.mono_rem (fun x hx => mem_eraseNat_imp hx) hnext⟩
    · have hnw' : t ∉ v :: w := by
        intro hm
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact hvt rfl
        · exact hnw hm'
      rcases Reach.remove_hit t ht hnw' hnext with ⟨k1, hk1, hr1⟩
      have hswap : Reach k1 (v :: t :: w) (eraseNat t rem) := by
        apply Reach.mono_w _ hr1
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact List.mem_cons_of_mem v List.mem_cons_self
        · rcases List.mem_cons.1 hx' with rfl | hx''
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem v (List.mem_cons_of_mem t hx'')
      have hvnot' : v ∉ t :: w := by
        intro hm
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact hvt rfl
        · exact hvnot hm'
      have hv' : StepFrom (t :: w) v := StepFrom.mono (fun x hx => List.mem_cons_of_mem t hx) hv
      exact ⟨k1 + 1, by omega, Reach.step hv0 hvnot' hv' hswap⟩

/-! ## 3. Fast Pruned Decision Procedure & Soundness Proof -/

@[inline] private def bucket (v : Nat) : Nat := (v >>> 1) &&& 255

private def findXor (v : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (x, t) :: rest => if v == x then some t else findXor v rest

private def findAnd (v : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, t) :: rest =>
    if (a &&& v) == t || (a &&& (mask16 ^^^ v)) == t then some t else findAnd v rest

private def findDisj (v : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, t) :: rest =>
    if ((mask16 ^^^ a) &&& v) == t then some t else findDisj v rest

private def findOr (v : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, t) :: rest =>
    if (a ||| v) == t then some t else findOr v rest

private structure FilterData where
  xorMask : Nat
  xors    : List (Nat × Nat)
  ands    : List (Nat × Nat)
  disj    : List (Nat × Nat)
  ors     : List (Nat × Nat)

private def addFiltersW (t : Nat) : List Nat → FilterData → FilterData
  | [], acc => acc
  | a :: wrest, ⟨xm, xs, as, ds, os⟩ =>
    let atv := a &&& t
    let x := a ^^^ t
    let xm' := xm ||| (1 <<< bucket x)
    let xs' := (x, t) :: xs
    let as' := if atv == t then (a, t) :: as else as
    let ds' := if atv == 0 then (a, t) :: ds else ds
    let os' := if atv == a then (a, t) :: os else os
    addFiltersW t wrest ⟨xm', xs', as', ds', os'⟩

private def buildFiltersGo (w : List Nat) : List Nat → FilterData → FilterData
  | [], acc => acc
  | t :: rrest, acc => buildFiltersGo w rrest (addFiltersW t w acc)

private def buildFilters (w rem : List Nat) : FilterData :=
  buildFiltersGo w rem ⟨0, [], [], [], []⟩

private def ops5Match (a na b t : Nat) : Bool :=
  (a ^^^ b) == t ||
  (a &&& b) == t ||
  (a &&& (mask16 ^^^ b)) == t ||
  (na &&& b) == t ||
  (a ||| b) == t

private def can1With (w : List Nat) (v nv t : Nat) : Bool :=
  match w with
  | [] => false
  | a :: rest => ops5Match v nv a t || can1With rest v nv t

private def can1 (w : List Nat) (t : Nat) : Bool :=
  match w with
  | [] => false
  | a :: rest => can1With rest a (mask16 ^^^ a) t || can1 rest t

private def findHit (w : List Nat) : List Nat → Option (Nat × List Nat)
  | [] => none
  | t :: rest =>
    if can1 w t then some (t, rest)
    else match findHit w rest with
      | none => none
      | some (h, r) => some (h, t :: r)

private def pushUnique (minVal v : Nat) (w : List Nat) (acc : Nat × List Nat) : Nat × List Nat :=
  if v == 0 || v < minVal then acc
  else
    let b := bucket v
    let (m, seen) := acc
    if Nat.testBit m b then
      if w.elem v || seen.elem v then acc else (m, v :: seen)
    else
      (m ||| (1 <<< b), v :: seen)

private def initSeenMask : List Nat → Nat
  | [] => 0
  | a :: rest => (1 <<< bucket a) ||| initSeenMask rest

private def genOps5 (minVal a na b : Nat) (w : List Nat) (acc : Nat × List Nat) : Nat × List Nat :=
  let s1 := pushUnique minVal (a ^^^ b) w acc
  let s2 := pushUnique minVal (a &&& b) w s1
  let s3 := pushUnique minVal (a &&& (mask16 ^^^ b)) w s2
  let s4 := pushUnique minVal (na &&& b) w s3
  pushUnique minVal (a ||| b) w s4

private def genWith (minVal a na : Nat) (bs w : List Nat) (acc : Nat × List Nat) : Nat × List Nat :=
  match bs with
  | [] => acc
  | b :: rest => genWith minVal a na rest w (genOps5 minVal a na b w acc)

private def genNextGo (minVal : Nat) (cur w : List Nat) (acc : Nat × List Nat) : Nat × List Nat :=
  match cur with
  | [] => acc
  | a :: rest => genNextGo minVal rest w (genWith minVal a (mask16 ^^^ a) rest w acc)

private def genNextSym (prevHelper : Bool) (w : List Nat) : List Nat :=
  match prevHelper, w with
  | true, h :: tail =>
    let acc0 := (initSeenMask w, [])
    let acc1 := genWith 0 h (mask16 ^^^ h) tail w acc0
    (genNextGo h tail w acc1).2
  | _, _ =>
    (genNextGo 0 w w (initSeenMask w, [])).2

private def allPairsWith (a na : Nat) (f : Nat → Bool) : List Nat → Bool
  | [] => true
  | b :: brest =>
    f (a ^^^ b) &&
    f (a &&& b) &&
    f (a &&& (mask16 ^^^ b)) &&
    f (na &&& b) &&
    f (a ||| b) &&
    allPairsWith a na f brest

private def allPairsOps (f : Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: rest => allPairsWith a (mask16 ^^^ a) f rest && allPairsOps f rest

private def allPairsSym (prevHelper : Bool) (fAll fMin : Nat → Bool) (w : List Nat) : Bool :=
  match prevHelper, w with
  | true, h :: tail => allPairsWith h (mask16 ^^^ h) fAll tail && allPairsOps fMin tail
  | _, _ => allPairsOps fAll w

private def checkFilterFull (fd : FilterData) (v : Nat) : Option Nat :=
  match (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
  | some t => some t
  | none =>
    match (match fd.ands with | [] => none | as => findAnd v as) with
    | some t => some t
    | none =>
      match (match fd.disj with | [] => none | ds => findDisj v ds) with
      | some t => some t
      | none => match fd.ors with | [] => none | os => findOr v os

private def noReach : Nat → Bool → List Nat → List Nat → Bool
  | 0, _, _, rem => !rem.isEmpty
  | left + 1, prevH, w, rem =>
    if rem.isEmpty then false
    else if rem.length > left + 1 then true
    else
      match findHit w rem with
      | some (t, rem') => noReach left false (t :: w) rem'
      | none =>
        if rem.length == left + 1 then true
        else if rem.length == left then
          let fd := buildFilters w rem
          let cont (v t : Nat) : Bool :=
            match left with
            | 0 => true
            | left' + 1 => noReach left' false (t :: v :: w) (eraseNat t rem)
          let hMin := w.headD 0
          if fd.ands.isEmpty && fd.disj.isEmpty && fd.ors.isEmpty then
            let xm := fd.xorMask
            let xs := fd.xors
            let fAll (v : Nat) : Bool :=
              if Nat.testBit xm (bucket v) then
                match findXor v xs with
                | none => true
                | some t => cont v t
              else true
            let fMin (v : Nat) : Bool :=
              if v < hMin then true
              else if Nat.testBit xm (bucket v) then
                match findXor v xs with
                | none => true
                | some t => cont v t
              else true
            allPairsSym prevH fAll fMin w
          else
            let fAll (v : Nat) : Bool :=
              match checkFilterFull fd v with
              | none => true
              | some t => cont v t
            let fMin (v : Nat) : Bool :=
              if v < hMin then true
              else match checkFilterFull fd v with
              | none => true
              | some t => cont v t
            allPairsSym prevH fAll fMin w
        else
          (genNextSym prevH w).all (fun v => noReach left true (v :: w) rem)

/-! ### Soundness & Completeness of Helper Functions -/

private theorem ops5Match_of_isOps5 {a b t : Nat} (h : isOps5 a b t) :
    ops5Match a (mask16 ^^^ a) b t = true := by
  unfold ops5Match
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem can1With_of_mem {w : List Nat} {a b t : Nat}
    (hb : b ∈ w) (hop : isOps5 a b t) : can1With w a (mask16 ^^^ a) t = true := by
  induction w with
  | nil => cases hb
  | cons x xs ih =>
    simp only [can1With, Bool.or_eq_true]
    rcases List.mem_cons.1 hb with rfl | hb'
    · left; exact ops5Match_of_isOps5 hop
    · right; exact ih hb'

private theorem can1_of_step {w : List Nat} {t : Nat} (hw : ∀ x ∈ w, x < 65536)
    (ht0 : t ≠ 0) (htw : t ∉ w) (hs : StepFrom w t) : can1 w t = true := by
  rcases hs with ⟨a, b, ha, hb, hop⟩
  induction w with
  | nil => cases ha
  | cons x xs ih =>
    simp only [can1, Bool.or_eq_true]
    have hxlt : x < 65536 := hw x List.mem_cons_self
    have hw' : ∀ y ∈ xs, y < 65536 := fun y hy => hw y (List.mem_cons_of_mem x hy)
    have htw' : t ∉ xs := fun hm => htw (List.mem_cons_of_mem x hm)
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rcases isOps5_self hxlt hop with rfl | rfl
      · exact absurd rfl ht0
      · exact absurd List.mem_cons_self htw
    · left; exact can1With_of_mem hb' hop
    · left; exact can1With_of_mem ha' (isOps5_symm hop)
    · right; exact ih hw' htw' ha' hb'

-- Clean specification of `findHit`
private theorem findHit_spec {w : List Nat} :
    ∀ {rem t rem'}, findHit w rem = some (t, rem') →
      t ∈ rem ∧ can1 w t = true ∧ rem' = eraseNat t rem := by
  intro rem
  induction rem with
  | nil => intro t rem' h; simp [findHit] at h
  | cons x xs ih =>
    intro t rem' h
    simp only [findHit] at h
    cases hc : can1 w x
    · rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hrec : findHit w xs with
      | none => rw [hrec] at h; cases h
      | some p =>
        rcases p with ⟨h0, r0⟩
        rw [hrec] at h
        injection h with h1
        injection h1 with ht hr
        subst ht hr
        rcases ih hrec with ⟨hmem, hch0, her⟩
        have hne : x ≠ h0 := by intro heq; subst heq; rw [hc] at hch0; cases hch0
        have hbeq : (x == h0) = false := beq_false_of_ne hne
        exact ⟨List.mem_cons_of_mem x hmem, hch0, by simp [eraseNat, hbeq, her]⟩
    · rw [hc] at h
      simp only [↓reduceIte] at h
      injection h with h1
      injection h1 with hxt hxs
      subst hxt hxs
      exact ⟨List.mem_cons_self, hc, by simp [eraseNat]⟩

private theorem findHit_none {w : List Nat} :
    ∀ {rem}, findHit w rem = none → ∀ t ∈ rem, can1 w t = false := by
  intro rem
  induction rem with
  | nil => intro _ t ht; cases ht
  | cons x xs ih =>
    intro h t ht
    simp only [findHit] at h
    cases hc : can1 w x
    · rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hrec : findHit w xs with
      | none =>
        rcases List.mem_cons.1 ht with rfl | ht'
        · exact hc
        · exact ih hrec t ht'
      | some p => rw [hrec] at h; cases h
    · rw [hc] at h; simp at h

private theorem testBit_one_shl_self (k : Nat) : Nat.testBit (1 <<< k) k = true := by
  rw [Nat.testBit_shiftLeft]
  simp

private theorem testBit_or_mono_left {m1 m2 k : Nat} (h : Nat.testBit m1 k = true) :
    Nat.testBit (m1 ||| m2) k = true := by
  rw [Nat.testBit_or, h]; rfl

private theorem testBit_or_mono_right {m1 m2 k : Nat} (h : Nat.testBit m2 k = true) :
    Nat.testBit (m1 ||| m2) k = true := by
  rw [Nat.testBit_or, h]; simp

private theorem findXor_mem {v t : Nat} :
    ∀ {xs : List (Nat × Nat)}, findXor v xs = some t → (v, t) ∈ xs
  | [], h => by simp [findXor] at h
  | (x, t0) :: rest, h => by
    simp only [findXor] at h
    cases hbeq : (v == x)
    · rw [hbeq] at h; simp at h
      exact List.mem_cons_of_mem _ (findXor_mem h)
    · rw [hbeq] at h; simp at h
      have hvx : v = x := eq_of_beq hbeq
      subst hvx h
      exact List.mem_cons_self

private theorem findXor_isSome {v t : Nat} :
    ∀ {xs : List (Nat × Nat)}, (v, t) ∈ xs → (findXor v xs).isSome = true
  | [], h => by cases h
  | (x, t0) :: rest, h => by
    simp only [findXor]
    by_cases hvx : v = x
    · subst hvx; simp
    · have hbeq : (v == x) = false := beq_false_of_ne hvx
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.1 h with hhead | htail
      · injection hhead with h1 _; exact absurd h1 hvx
      · exact findXor_isSome htail

private theorem findAnd_mem {v t : Nat} :
    ∀ {as : List (Nat × Nat)}, findAnd v as = some t → ∃ a, (a, t) ∈ as
  | [], h => by simp [findAnd] at h
  | (a, t0) :: rest, h => by
    simp only [findAnd] at h
    split at h
    · injection h with ht; subst ht; exact ⟨a, List.mem_cons_self⟩
    · rcases findAnd_mem h with ⟨a', ha'⟩; exact ⟨a', List.mem_cons_of_mem _ ha'⟩

private theorem findAnd_isSome {v a t : Nat} :
    ∀ {as : List (Nat × Nat)}, (a, t) ∈ as →
      ((a &&& v) = t ∨ (a &&& (mask16 ^^^ v)) = t) → (findAnd v as).isSome = true
  | [], h, _ => by cases h
  | (a0, t0) :: rest, h, heq => by
    simp only [findAnd]
    split
    · rfl
    · rename_i hnot
      rcases List.mem_cons.1 h with hhead | htail
      · injection hhead with ha ht; subst ha ht
        exfalso; apply hnot
        rcases heq with h1 | h2
        · simp [h1]
        · simp [h2]
      · exact findAnd_isSome htail heq

private theorem findDisj_mem {v t : Nat} :
    ∀ {ds : List (Nat × Nat)}, findDisj v ds = some t → ∃ a, (a, t) ∈ ds
  | [], h => by simp [findDisj] at h
  | (a, t0) :: rest, h => by
    simp only [findDisj] at h
    split at h
    · injection h with ht; subst ht; exact ⟨a, List.mem_cons_self⟩
    · rcases findDisj_mem h with ⟨a', ha'⟩; exact ⟨a', List.mem_cons_of_mem _ ha'⟩

private theorem findDisj_isSome {v a t : Nat} :
    ∀ {ds : List (Nat × Nat)}, (a, t) ∈ ds →
      ((mask16 ^^^ a) &&& v) = t → (findDisj v ds).isSome = true
  | [], h, _ => by cases h
  | (a0, t0) :: rest, h, heq => by
    simp only [findDisj]
    split
    · rfl
    · rename_i hnot
      rcases List.mem_cons.1 h with hhead | htail
      · injection hhead with ha ht; subst ha ht
        exfalso; apply hnot; simp [heq]
      · exact findDisj_isSome htail heq

private theorem findOr_mem {v t : Nat} :
    ∀ {os : List (Nat × Nat)}, findOr v os = some t → ∃ a, (a, t) ∈ os
  | [], h => by simp [findOr] at h
  | (a, t0) :: rest, h => by
    simp only [findOr] at h
    split at h
    · injection h with ht; subst ht; exact ⟨a, List.mem_cons_self⟩
    · rcases findOr_mem h with ⟨a', ha'⟩; exact ⟨a', List.mem_cons_of_mem _ ha'⟩

private theorem findOr_isSome {v a t : Nat} :
    ∀ {os : List (Nat × Nat)}, (a, t) ∈ os →
      (a ||| v) = t → (findOr v os).isSome = true
  | [], h, _ => by cases h
  | (a0, t0) :: rest, h, heq => by
    simp only [findOr]
    split
    · rfl
    · rename_i hnot
      rcases List.mem_cons.1 h with hhead | htail
      · injection hhead with ha ht; subst ha ht
        exfalso; apply hnot; simp [heq]
      · exact findOr_isSome htail heq

private def FilterInv (rem : List Nat) (fd : FilterData) : Prop :=
  (∀ x t, (x, t) ∈ fd.xors → t ∈ rem ∧ Nat.testBit fd.xorMask (bucket x) = true) ∧
  (∀ a t, (a, t) ∈ fd.ands → t ∈ rem) ∧
  (∀ a t, (a, t) ∈ fd.disj → t ∈ rem) ∧
  (∀ a t, (a, t) ∈ fd.ors → t ∈ rem)

private theorem addFiltersW_inv (rem : List Nat) {t : Nat} (ht : t ∈ rem) :
    ∀ (ws : List Nat) (fd : FilterData), FilterInv rem fd → FilterInv rem (addFiltersW t ws fd)
  | [], fd, h => h
  | a :: wrest, ⟨xm, xs, as, ds, os⟩, ⟨hx, ha, hd, ho⟩ => by
    apply addFiltersW_inv rem ht wrest
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x t0 hm
      rcases List.mem_cons.1 hm with hhead | htail
      · injection hhead with h1 h2; subst h1 h2
        exact ⟨ht, testBit_or_mono_right (testBit_one_shl_self _)⟩
      · rcases hx x t0 htail with ⟨hmem, htb⟩
        exact ⟨hmem, testBit_or_mono_left htb⟩
    · intro a0 t0 hm
      dsimp only at hm
      split at hm
      · rcases List.mem_cons.1 hm with hhead | htail
        · injection hhead with _ h2; subst h2; exact ht
        · exact ha a0 t0 htail
      · exact ha a0 t0 hm
    · intro a0 t0 hm
      dsimp only at hm
      split at hm
      · rcases List.mem_cons.1 hm with hhead | htail
        · injection hhead with _ h2; subst h2; exact ht
        · exact hd a0 t0 htail
      · exact hd a0 t0 hm
    · intro a0 t0 hm
      dsimp only at hm
      split at hm
      · rcases List.mem_cons.1 hm with hhead | htail
        · injection hhead with _ h2; subst h2; exact ht
        · exact ho a0 t0 htail
      · exact ho a0 t0 hm

private theorem buildFiltersGo_inv (w rem : List Nat) :
    ∀ (rs : List Nat) (fd : FilterData),
      (∀ t ∈ rs, t ∈ rem) → FilterInv rem fd → FilterInv rem (buildFiltersGo w rs fd)
  | [], _, _, h => h
  | t :: rrest, fd, hsub, h =>
    buildFiltersGo_inv w rem rrest _ (fun x hx => hsub x (List.mem_cons_of_mem t hx))
      (addFiltersW_inv rem (hsub t List.mem_cons_self) w fd h)

private theorem buildFilters_inv (w rem : List Nat) : FilterInv rem (buildFilters w rem) := by
  apply buildFiltersGo_inv w rem rem ⟨0, [], [], [], []⟩ (fun _ h => h)
  exact ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h),
         fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

private theorem addFiltersW_mono {t : Nat} :
    ∀ (ws : List Nat) (fd : FilterData),
      (∀ p, p ∈ fd.xors → p ∈ (addFiltersW t ws fd).xors) ∧
      (∀ p, p ∈ fd.ands → p ∈ (addFiltersW t ws fd).ands) ∧
      (∀ p, p ∈ fd.disj → p ∈ (addFiltersW t ws fd).disj) ∧
      (∀ p, p ∈ fd.ors  → p ∈ (addFiltersW t ws fd).ors)
  | [], _ => ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | a :: wrest, ⟨xm, xs, as, ds, os⟩ => by
    have ih := addFiltersW_mono (t := t) wrest (addFiltersW t [a] ⟨xm, xs, as, ds, os⟩)
    simp only [addFiltersW] at ih ⊢
    refine ⟨fun p hp => ih.1 p (List.mem_cons_of_mem _ hp),
            fun p hp => ih.2.1 p (by
              split
              · exact List.mem_cons_of_mem _ hp
              · exact hp),
            fun p hp => ih.2.2.1 p (by
              split
              · exact List.mem_cons_of_mem _ hp
              · exact hp),
            fun p hp => ih.2.2.2 p (by
              split
              · exact List.mem_cons_of_mem _ hp
              · exact hp)⟩

private theorem buildFiltersGo_mono (w : List Nat) :
    ∀ (rs : List Nat) (fd : FilterData),
      (∀ p, p ∈ fd.xors → p ∈ (buildFiltersGo w rs fd).xors) ∧
      (∀ p, p ∈ fd.ands → p ∈ (buildFiltersGo w rs fd).ands) ∧
      (∀ p, p ∈ fd.disj → p ∈ (buildFiltersGo w rs fd).disj) ∧
      (∀ p, p ∈ fd.ors  → p ∈ (buildFiltersGo w rs fd).ors)
  | [], _ => ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | t :: rrest, fd => by
    have h1 := addFiltersW_mono (t := t) w fd
    have h2 := buildFiltersGo_mono w rrest (addFiltersW t w fd)
    exact ⟨fun p hp => h2.1 p (h1.1 p hp),
           fun p hp => h2.2.1 p (h1.2.1 p hp),
           fun p hp => h2.2.2.1 p (h1.2.2.1 p hp),
           fun p hp => h2.2.2.2 p (h1.2.2.2 p hp)⟩

private theorem addFiltersW_contains {t a : Nat} :
    ∀ (ws : List Nat) (fd : FilterData), a ∈ ws →
      (a ^^^ t, t) ∈ (addFiltersW t ws fd).xors ∧
      ((a &&& t) = t → (a, t) ∈ (addFiltersW t ws fd).ands) ∧
      ((a &&& t) = 0 → (a, t) ∈ (addFiltersW t ws fd).disj) ∧
      ((a &&& t) = a → (a, t) ∈ (addFiltersW t ws fd).ors)
  | [], _, h => by cases h
  | x :: wrest, ⟨xm, xs, as, ds, os⟩, h => by
    rcases List.mem_cons.1 h with rfl | htail
    · have hm := addFiltersW_mono (t := t) wrest (addFiltersW t [a] ⟨xm, xs, as, ds, os⟩)
      simp only [addFiltersW] at hm ⊢
      refine ⟨hm.1 _ List.mem_cons_self,
              fun heq => hm.2.1 _ (by simp [heq]),
              fun heq => hm.2.2.1 _ (by simp [heq]),
              fun heq => hm.2.2.2 _ (by simp [heq])⟩
    · exact addFiltersW_contains wrest _ htail

private theorem buildFilters_contains {w rem : List Nat} {a t : Nat}
    (ha : a ∈ w) (ht : t ∈ rem) :
    (a ^^^ t, t) ∈ (buildFilters w rem).xors ∧
    ((a &&& t) = t → (a, t) ∈ (buildFilters w rem).ands) ∧
    ((a &&& t) = 0 → (a, t) ∈ (buildFilters w rem).disj) ∧
    ((a &&& t) = a → (a, t) ∈ (buildFilters w rem).ors) := by
  have hgo : ∀ (rs : List Nat) (fd : FilterData), t ∈ rs →
      (a ^^^ t, t) ∈ (buildFiltersGo w rs fd).xors ∧
      ((a &&& t) = t → (a, t) ∈ (buildFiltersGo w rs fd).ands) ∧
      ((a &&& t) = 0 → (a, t) ∈ (buildFiltersGo w rs fd).disj) ∧
      ((a &&& t) = a → (a, t) ∈ (buildFiltersGo w rs fd).ors) := by
    intro rs
    induction rs with
    | nil => intro _ h; cases h
    | cons r rrest ih =>
      intro fd hm
      rcases List.mem_cons.1 hm with rfl | hm'
      · have hc := addFiltersW_contains (t := t) w fd ha
        have hm2 := buildFiltersGo_mono w rrest (addFiltersW t w fd)
        exact ⟨hm2.1 _ hc.1, fun h => hm2.2.1 _ (hc.2.1 h),
               fun h => hm2.2.2.1 _ (hc.2.2.1 h), fun h => hm2.2.2.2 _ (hc.2.2.2 h)⟩
      · exact ih _ hm'
  exact hgo rem ⟨0, [], [], [], []⟩ ht

private theorem bit_and_of_eq_and {a v t : Nat} (h : (a &&& v) = t) : (a &&& t) = t := by
  subst h
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and]
  cases a.testBit k <;> cases v.testBit k <;> rfl

private theorem bit_and_of_eq_notand {a v t : Nat} (ha : a < 65536)
    (h : ((mask16 ^^^ a) &&& v) = t) : (a &&& t) = 0 := by
  subst h
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_xor, testBit_mask16, Nat.zero_testBit]
  by_cases hk : k < 16
  · cases a.testBit k <;> cases v.testBit k <;> simp [hk]
  · have hge : 16 ≤ k := by omega
    simp [hk, testBit_lt_65536 ha hge]

private theorem bit_and_of_eq_or {a v t : Nat} (h : (a ||| v) = t) : (a &&& t) = a := by
  subst h
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit k <;> cases v.testBit k <;> rfl

private theorem bit_xor_cancel {a v t : Nat} (h : (a ^^^ v) = t) : (a ^^^ t) = v := by
  subst h
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor]
  cases a.testBit k <;> cases v.testBit k <;> rfl

private theorem checkFilterFull_mem {w rem : List Nat} {v t : Nat}
    (h : checkFilterFull (buildFilters w rem) v = some t) : t ∈ rem := by
  have hinv := buildFilters_inv w rem
  unfold checkFilterFull at h
  cases h1 : (if Nat.testBit (buildFilters w rem).xorMask (bucket v) then findXor v (buildFilters w rem).xors else none) with
  | some t1 =>
    rw [h1] at h; injection h with ht; subst ht
    split at h1
    · exact (hinv.1 v t1 (findXor_mem h1)).1
    · cases h1
  | none =>
    rw [h1] at h; dsimp only at h
    cases h2 : (match (buildFilters w rem).ands with | [] => none | as => findAnd v as) with
    | some t2 =>
      rw [h2] at h; injection h with ht; subst ht
      cases has : (buildFilters w rem).ands with
      | nil => rw [has] at h2; cases h2
      | cons x xs =>
        rw [has] at h2
        rcases findAnd_mem h2 with ⟨a, ha⟩
        exact hinv.2.1 a t2 (by rw [has]; exact ha)
    | none =>
      rw [h2] at h; dsimp only at h
      cases h3 : (match (buildFilters w rem).disj with | [] => none | ds => findDisj v ds) with
      | some t3 =>
        rw [h3] at h; injection h with ht; subst ht
        cases hds : (buildFilters w rem).disj with
        | nil => rw [hds] at h3; cases h3
        | cons x xs =>
          rw [hds] at h3
          rcases findDisj_mem h3 with ⟨a, ha⟩
          exact hinv.2.2.1 a t3 (by rw [hds]; exact ha)
      | none =>
        rw [h3] at h; dsimp only at h
        cases hos : (buildFilters w rem).ors with
        | nil => rw [hos] at h; cases h
        | cons x xs =>
          rw [hos] at h
          rcases findOr_mem h with ⟨a, ha⟩
          exact hinv.2.2.2 a t (by rw [hos]; exact ha)

private theorem checkFilterFull_isSome {w rem : List Nat} {a v t : Nat}
    (ha_lt : a < 65536) (ha : a ∈ w) (ht : t ∈ rem) (hop : isOps5 a v t) :
    (checkFilterFull (buildFilters w rem) v).isSome = true := by
  have hinv := buildFilters_inv w rem
  have hc := buildFilters_contains ha ht
  unfold checkFilterFull
  let fd := buildFilters w rem
  change (match (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
    | some t => some t
    | none =>
      match (match fd.ands with | [] => none | as => findAnd v as) with
      | some t => some t
      | none =>
        match (match fd.disj with | [] => none | ds => findDisj v ds) with
        | some t => some t
        | none => match fd.ors with | [] => none | os => findOr v os).isSome = true
  rcases hop with hxor | hand | handnot | hnotand | hor
  · have hxv : a ^^^ t = v := bit_xor_cancel hxor.symm
    have hmem : (v, t) ∈ fd.xors := by rw [← hxv]; exact hc.1
    have htb : Nat.testBit fd.xorMask (bucket v) = true := (hinv.1 v t hmem).2
    have hfx := findXor_isSome hmem
    rw [htb]; simp only [↓reduceIte]
    cases h : findXor v fd.xors with
    | none => rw [h] at hfx; cases hfx
    | some _ => rfl
  · have hat : (a &&& t) = t := bit_and_of_eq_and hand.symm
    have hmem : (a, t) ∈ fd.ands := hc.2.1 hat
    have hfa := findAnd_isSome hmem (Or.inl hand.symm)
    cases h1 : (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
    | some _ => rfl
    | none =>
      dsimp only
      cases has : fd.ands with
      | nil => rw [has] at hmem; cases hmem
      | cons _ _ =>
        rw [has] at hfa
        dsimp only
        cases h2 : findAnd v _ with
        | none => rw [h2] at hfa; cases hfa
        | some _ => rfl
  · have hat : (a &&& t) = t := bit_and_of_eq_and handnot.symm
    have hmem : (a, t) ∈ fd.ands := hc.2.1 hat
    have hfa := findAnd_isSome hmem (Or.inr handnot.symm)
    cases h1 : (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
    | some _ => rfl
    | none =>
      dsimp only
      cases has : fd.ands with
      | nil => rw [has] at hmem; cases hmem
      | cons _ _ =>
        rw [has] at hfa
        dsimp only
        cases h2 : findAnd v _ with
        | none => rw [h2] at hfa; cases hfa
        | some _ => rfl
  · have hat : (a &&& t) = 0 := bit_and_of_eq_notand ha_lt hnotand.symm
    have hmem : (a, t) ∈ fd.disj := hc.2.2.1 hat
    have hfd := findDisj_isSome hmem hnotand.symm
    cases h1 : (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
    | some _ => rfl
    | none =>
      dsimp only
      cases h2 : (match fd.ands with | [] => none | as => findAnd v as) with
      | some _ => rfl
      | none =>
        dsimp only
        cases hds : fd.disj with
        | nil => rw [hds] at hmem; cases hmem
        | cons _ _ =>
          rw [hds] at hfd
          dsimp only
          cases h3 : findDisj v _ with
          | none => rw [h3] at hfd; cases hfd
          | some _ => rfl
  · have hat : (a &&& t) = a := bit_and_of_eq_or hor.symm
    have hmem : (a, t) ∈ fd.ors := hc.2.2.2 hat
    have hfo := findOr_isSome hmem hor.symm
    cases h1 : (if Nat.testBit fd.xorMask (bucket v) then findXor v fd.xors else none) with
    | some _ => rfl
    | none =>
      dsimp only
      cases h2 : (match fd.ands with | [] => none | as => findAnd v as) with
      | some _ => rfl
      | none =>
        dsimp only
        cases h3 : (match fd.disj with | [] => none | ds => findDisj v ds) with
        | some _ => rfl
        | none =>
          dsimp only
          cases hos : fd.ors with
          | nil => rw [hos] at hmem; cases hmem
          | cons _ _ =>
            rw [hos] at hfo
            dsimp only
            cases h4 : findOr v _ with
            | none => rw [h4] at hfo; cases hfo
            | some _ => rfl

private theorem checkXorOnly_isSome {w rem : List Nat} {a v t : Nat}
    (ha_lt : a < 65536) (ha : a ∈ w) (ht : t ∈ rem) (hop : isOps5 a v t)
    (hemp : (buildFilters w rem).ands.isEmpty = true ∧
            (buildFilters w rem).disj.isEmpty = true ∧
            (buildFilters w rem).ors.isEmpty = true) :
    Nat.testBit (buildFilters w rem).xorMask (bucket v) = true ∧
    (findXor v (buildFilters w rem).xors).isSome = true := by
  have hinv := buildFilters_inv w rem
  have hc := buildFilters_contains ha ht
  let fd := buildFilters w rem
  rcases hemp with ⟨has, hds, hos⟩
  have hna : fd.ands = [] := List.isEmpty_iff.1 has
  have hnd : fd.disj = [] := List.isEmpty_iff.1 hds
  have hno : fd.ors  = [] := List.isEmpty_iff.1 hos
  rcases hop with hxor | hand | handnot | hnotand | hor
  · have hxv : a ^^^ t = v := bit_xor_cancel hxor.symm
    have hmem : (v, t) ∈ fd.xors := by rw [← hxv]; exact hc.1
    exact ⟨(hinv.1 v t hmem).2, findXor_isSome hmem⟩
  · have hm := hc.2.1 (bit_and_of_eq_and hand.symm); rw [hna] at hm; cases hm
  · have hm := hc.2.1 (bit_and_of_eq_and handnot.symm); rw [hna] at hm; cases hm
  · have hm := hc.2.2.1 (bit_and_of_eq_notand ha_lt hnotand.symm); rw [hnd] at hm; cases hm
  · have hm := hc.2.2.2 (bit_and_of_eq_or hor.symm); rw [hno] at hm; cases hm

/-! ### Completeness of `genNextSym` and `allPairsSym` -/

private theorem pushUnique_mem_of_mem {minVal v x : Nat} {w : List Nat} {acc : Nat × List Nat}
    (hx : x ∈ acc.2) : x ∈ (pushUnique minVal v w acc).2 := by
  unfold pushUnique
  split
  · exact hx
  · dsimp only
    split
    · split
      · exact hx
      · exact List.mem_cons_of_mem v hx
    · exact List.mem_cons_of_mem v hx

private theorem pushUnique_mem_self {minVal v : Nat} {w : List Nat} {acc : Nat × List Nat}
    (hv0 : v ≠ 0) (hvmin : ¬ (v < minVal)) (hvw : v ∉ w) :
    v ∈ (pushUnique minVal v w acc).2 := by
  unfold pushUnique
  have hcond : (v == 0 || v < minVal) = false := by
    simp [beq_false_of_ne hv0, hvmin]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · rename_i hel
      rw [Bool.or_eq_true] at hel
      rcases hel with hw' | hs'
      · exact absurd (List.mem_of_elem_eq_true hw') hvw
      · exact List.mem_of_elem_eq_true hs'
    · exact List.mem_cons_self
  · exact List.mem_cons_self

private theorem genOps5_mono {minVal a na b x : Nat} {w : List Nat} {acc : Nat × List Nat}
    (hx : x ∈ acc.2) : x ∈ (genOps5 minVal a na b w acc).2 := by
  unfold genOps5
  exact pushUnique_mem_of_mem (pushUnique_mem_of_mem (pushUnique_mem_of_mem
    (pushUnique_mem_of_mem (pushUnique_mem_of_mem hx))))

private theorem genOps5_mem {minVal a b v : Nat} {w : List Nat} {acc : Nat × List Nat}
    (hv0 : v ≠ 0) (hvmin : ¬ (v < minVal)) (hvw : v ∉ w) (hop : isOps5 a b v) :
    v ∈ (genOps5 minVal a (mask16 ^^^ a) b w acc).2 := by
  unfold genOps5
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · exact pushUnique_mem_of_mem (pushUnique_mem_of_mem (pushUnique_mem_of_mem
      (pushUnique_mem_of_mem (pushUnique_mem_self hv0 hvmin hvw))))
  · exact pushUnique_mem_of_mem (pushUnique_mem_of_mem (pushUnique_mem_of_mem
      (pushUnique_mem_self hv0 hvmin hvw)))
  · exact pushUnique_mem_of_mem (pushUnique_mem_of_mem
      (pushUnique_mem_self hv0 hvmin hvw))
  · exact pushUnique_mem_of_mem (pushUnique_mem_self hv0 hvmin hvw)
  · exact pushUnique_mem_self hv0 hvmin hvw

private theorem genWith_mono {minVal a na x : Nat} :
    ∀ (bs : List Nat) (w : List Nat) (acc : Nat × List Nat),
      x ∈ acc.2 → x ∈ (genWith minVal a na bs w acc).2
  | [], _, _, hx => hx
  | b :: rest, w, acc, hx => genWith_mono rest w _ (genOps5_mono hx)

private theorem genWith_mem {minVal a b v : Nat} :
    ∀ (bs : List Nat) (w : List Nat) (acc : Nat × List Nat),
      b ∈ bs → v ≠ 0 → ¬ (v < minVal) → v ∉ w → isOps5 a b v →
      v ∈ (genWith minVal a (mask16 ^^^ a) bs w acc).2
  | [], _, _, hb, _, _, _, _ => by cases hb
  | b0 :: rest, w, acc, hb, hv0, hvmin, hvw, hop => by
    simp only [genWith]
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact genWith_mono rest w _ (genOps5_mem hv0 hvmin hvw hop)
    · exact genWith_mem rest w _ hb' hv0 hvmin hvw hop

private theorem genNextGo_mono {minVal x : Nat} :
    ∀ (cur w : List Nat) (acc : Nat × List Nat),
      x ∈ acc.2 → x ∈ (genNextGo minVal cur w acc).2
  | [], _, _, hx => hx
  | a :: rest, w, acc, hx => genNextGo_mono rest w _ (genWith_mono rest w acc hx)

private theorem genNextGo_mem {minVal v : Nat} :
    ∀ (cur w : List Nat) (acc : Nat × List Nat),
      (∀ x ∈ cur, x < 65536) →
      (∀ x ∈ cur, x ∈ w) →
      v ≠ 0 → ¬ (v < minVal) → v ∉ w → StepFrom cur v →
      v ∈ (genNextGo minVal cur w acc).2
  | [], _, _, _, _, _, _, _, ⟨a, _, ha, _, _⟩ => by cases ha
  | x :: xs, w, acc, hlt, hsub, hv0, hvmin, hvw, ⟨a, b, ha, hb, hop⟩ => by
    simp only [genNextGo]
    have hxlt : x < 65536 := hlt x List.mem_cons_self
    have hlt' : ∀ y ∈ xs, y < 65536 := fun y hy => hlt y (List.mem_cons_of_mem x hy)
    have hsub' : ∀ y ∈ xs, y ∈ w := fun y hy => hsub y (List.mem_cons_of_mem x hy)
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rcases isOps5_self hxlt hop with rfl | rfl
      · exact absurd rfl hv0
      · exact absurd (hsub v List.mem_cons_self) hvw
    · exact genNextGo_mono xs w _ (genWith_mem xs w acc hb' hv0 hvmin hvw hop)
    · exact genNextGo_mono xs w _ (genWith_mem xs w acc ha' hv0 hvmin hvw (isOps5_symm hop))
    · exact genNextGo_mem xs w _ hlt' hsub' hv0 hvmin hvw ⟨a, b, ha', hb', hop⟩

private theorem allPairsWith_spec {a b v : Nat} {f : Nat → Bool} :
    ∀ {bs : List Nat}, allPairsWith a (mask16 ^^^ a) f bs = true →
      b ∈ bs → isOps5 a b v → f v = true
  | [], _, hb, _ => by cases hb
  | b0 :: rest, hall, hb, hop => by
    simp only [allPairsWith, Bool.and_eq_true] at hall
    rcases List.mem_cons.1 hb with rfl | hb'
    · rcases hop with rfl | rfl | rfl | rfl | rfl
      · exact hall.1.1.1.1.1
      · exact hall.1.1.1.1.2
      · exact hall.1.1.1.2
      · exact hall.1.1.2
      · exact hall.1.2
    · exact allPairsWith_spec hall.2 hb' hop

private theorem allPairsOps_spec {v : Nat} {f : Nat → Bool} :
    ∀ {cur : List Nat}, allPairsOps f cur = true →
      (∀ x ∈ cur, x < 65536) → v ≠ 0 → v ∉ cur → StepFrom cur v → f v = true
  | [], _, _, _, _, ⟨a, _, ha, _, _⟩ => by cases ha
  | x :: xs, hall, hlt, hv0, hvn, ⟨a, b, ha, hb, hop⟩ => by
    simp only [allPairsOps, Bool.and_eq_true] at hall
    have hxlt : x < 65536 := hlt x List.mem_cons_self
    have hlt' : ∀ y ∈ xs, y < 65536 := fun y hy => hlt y (List.mem_cons_of_mem x hy)
    have hvn' : v ∉ xs := fun hm => hvn (List.mem_cons_of_mem x hm)
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rcases isOps5_self hxlt hop with rfl | rfl
      · exact absurd rfl hv0
      · exact absurd List.mem_cons_self hvn
    · exact allPairsWith_spec hall.1 hb' hop
    · exact allPairsWith_spec hall.1 ha' (isOps5_symm hop)
    · exact allPairsOps_spec hall.2 hlt' hv0 hvn' ⟨a, b, ha', hb', hop⟩

private theorem stepFrom_cons_split {h v : Nat} {tail : List Nat}
    (hh : h < 65536) (hv0 : v ≠ 0) (hvn : v ∉ h :: tail) (hs : StepFrom (h :: tail) v) :
    (∃ b ∈ tail, isOps5 h b v) ∨ StepFrom tail v := by
  rcases hs with ⟨a, b, ha, hb, hop⟩
  rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
  · rcases isOps5_self hh hop with rfl | rfl
    · exact absurd rfl hv0
    · exact absurd List.mem_cons_self hvn
  · left; exact ⟨b, hb', hop⟩
  · left; exact ⟨a, ha', isOps5_symm hop⟩
  · right; exact ⟨a, b, ha', hb', hop⟩

/-! ### Main Soundness Theorem for `noReach` -/

private def SymInv (left : Nat) (prevH : Bool) (w rem : List Nat) : Prop :=
  match prevH, w with
  | true, h :: tail =>
      h ≠ 0 ∧ h ∉ tail ∧ StepFrom tail h ∧
      (∀ u, u < h → u ≠ 0 → u ∉ tail → StepFrom tail u → ¬ Reach left (u :: tail) rem)
  | _, _ => True

private theorem noReach_sound (left : Nat) :
    ∀ (prevH : Bool) (w rem : List Nat),
      noReach left prevH w rem = true →
      (∀ x ∈ w, x < 65536) →
      (∀ t ∈ rem, t < 65536 ∧ t ≠ 0) →
      rem.Nodup →
      (∀ t ∈ rem, t ∉ w) →
      SymInv left prevH w rem →
      ¬ Reach left w rem := by
  induction left using Nat.strongRecOn with
  | ind left ih =>
    intro prevH w rem hnr hw hrem hnd hdisj hsym hreach
    cases left with
    | zero =>
      simp only [noReach, Bool.not_eq_true'] at hnr
      have hlen := Reach.pigeonhole hnd hdisj hreach
      cases rem with
      | nil => simp at hnr
      | cons _ _ => simp at hlen
    | succ left0 =>
      simp only [noReach] at hnr
      cases hremEmpty : rem.isEmpty with
      | true => rw [hremEmpty] at hnr; simp at hnr
      | false =>
        rw [hremEmpty] at hnr
        simp only [Bool.false_eq_true, ↓reduceIte] at hnr
        by_cases hgt : rem.length > left0 + 1
        · have hlen := Reach.pigeonhole hnd hdisj hreach
          omega
        · simp only [hgt, ↓reduceIte] at hnr
          cases hfh : findHit w rem with
          | some p =>
            rcases p with ⟨t, rem'⟩
            rw [hfh] at hnr
            rcases findHit_spec hfh with ⟨htmem, _, hrem'eq⟩
            subst hrem'eq
            rcases Reach.remove_hit t htmem (hdisj t htmem) hreach with ⟨k', hk', hr'⟩
            have hk'eq : k' = left0 := by omega
            subst k'
            have hw' : ∀ x ∈ t :: w, x < 65536 := by
              intro x hx
              rcases List.mem_cons.1 hx with hxt | hx'
              · rw [hxt]; exact (hrem t htmem).1
              · exact hw x hx'
            have hrem' : ∀ x ∈ eraseNat t rem, x < 65536 ∧ x ≠ 0 :=
              fun x hx => hrem x (mem_eraseNat_imp hx)
            have hdisj' : ∀ x ∈ eraseNat t rem, x ∉ t :: w := by
              intro x hx hm
              rcases List.mem_cons.1 hm with hxt | hm'
              · rw [hxt] at hx; exact not_mem_eraseNat_of_nodup hnd hx
              · exact hdisj x (mem_eraseNat_imp hx) hm'
            exact ih left0 (Nat.lt_succ_self left0) false (t :: w) (eraseNat t rem)
              hnr hw' hrem' (nodup_eraseNat hnd) hdisj' trivial hr'
          | none =>
            rw [hfh] at hnr
            have hnohit : ∀ t ∈ rem, ¬ StepFrom w t := by
              intro t ht hs
              have hc := can1_of_step hw (hrem t ht).2 (hdisj t ht) hs
              have hf := findHit_none hfh t ht
              rw [hc] at hf; cases hf
            -- First step of `hreach` must exist because `rem` is nonempty and disjoint from `w`
            have hstep : ∀ (k : Nat), k = left0 + 1 → Reach k w rem →
                ∃ v, v ≠ 0 ∧ v ∉ w ∧ StepFrom w v ∧ Reach left0 (v :: w) rem := by
              intro k hk hr
              cases hr with
              | done hd =>
                cases rem with
                | nil => simp at hremEmpty
                | cons t _ => exact absurd (hd t List.mem_cons_self) (hdisj t List.mem_cons_self)
              | step hv0 hvnot hv hnext =>
                injection hk with hkeq; subst hkeq
                exact ⟨_, hv0, hvnot, hv, hnext⟩
            by_cases heq1 : rem.length = left0 + 1
            · rcases hstep (left0 + 1) rfl hreach with ⟨v, hv0, hvnot, hv, hnext⟩
              have hvnotrem : v ∉ rem := fun hm => hnohit v hm hv
              have hdisj' : ∀ t ∈ rem, t ∉ v :: w := by
                intro t ht hm
                rcases List.mem_cons.1 hm with rfl | hm'
                · exact hvnotrem ht
                · exact hdisj t ht hm'
              have hlen := Reach.pigeonhole hnd hdisj' hnext
              omega
            · have hbeq1 : (rem.length == left0 + 1) = false := beq_false_of_ne heq1
              simp only [hbeq1, Bool.false_eq_true, ↓reduceIte] at hnr
              -- Helper: symmetry-skipping contradiction for `prevH = true, w = h :: tail`
              have hskip : ∀ (v : Nat),
                  (match prevH, w with
                   | true, h :: tail => v < h ∧ StepFrom tail v
                   | _, _ => False) →
                  v ≠ 0 → v ∉ w → Reach left0 (v :: w) rem → False := by
                intro v hsk hv0 hvnot hnext
                cases prevH with
                | false => cases hsk
                | true =>
                  cases w with
                  | nil => cases hsk
                  | cons h tail =>
                    rcases hsk with ⟨hvlt, hvtail⟩
                    rcases hsym with ⟨hh0, hhtail, hsteph, hnoskip⟩
                    have hvntail : v ∉ tail := fun hm => hvnot (List.mem_cons_of_mem h hm)
                    have hswap : Reach left0 (h :: v :: tail) rem := by
                      apply Reach.mono_w _ hnext
                      intro x hx
                      rcases List.mem_cons.1 hx with rfl | hx'
                      · exact List.mem_cons_of_mem h List.mem_cons_self
                      · rcases List.mem_cons.1 hx' with rfl | hx''
                        · exact List.mem_cons_self
                        · exact List.mem_cons_of_mem h (List.mem_cons_of_mem v hx'')
                    have hhnv : h ∉ v :: tail := by
                      intro hm
                      rcases List.mem_cons.1 hm with rfl | hm'
                      · omega
                      · exact hhtail hm'
                    have hsteph' : StepFrom (v :: tail) h :=
                      StepFrom.mono (fun x hx => List.mem_cons_of_mem v hx) hsteph
                    have hreach_v : Reach (left0 + 1) (v :: tail) rem :=
                      Reach.step hh0 hhnv hsteph' hswap
                    exact hnoskip v hvlt hv0 hvntail hvtail hreach_v
              by_cases heq0 : rem.length = left0
              · have hbeq0 : (rem.length == left0) = true := beq_iff_eq.2 heq0
                simp only [hbeq0, ↓reduceIte] at hnr
                rcases hstep (left0 + 1) rfl hreach with ⟨v, hv0, hvnot, hv, hnext⟩
                -- Show `v` must unlock some target in `rem` on the next step
                have hvnotrem : v ∉ rem := fun hm => hnohit v hm hv
                have hdisj_v : ∀ t ∈ rem, t ∉ v :: w := by
                  intro t ht hm
                  rcases List.mem_cons.1 hm with rfl | hm'
                  · exact hvnotrem ht
                  · exact hdisj t ht hm'
                have hvlt : v < 65536 := by
                  rcases hv with ⟨a, b, ha, hb, hop⟩
                  exact isOps5_lt (hw a ha) (hw b hb) hop
                cases left0 with
                | zero =>
                  cases rem with
                  | nil => simp at hremEmpty
                  | cons _ _ => simp at heq0
                | succ left' =>
                  -- Extract next step `u` from `hnext : Reach (left' + 1) (v :: w) rem`
                  have hnext_unlock : ∃ t ∈ rem, ∃ a ∈ w, isOps5 a v t := by
                    cases hnext with
                    | done hd =>
                      cases rem with
                      | nil => simp at hremEmpty
                      | cons t _ => exact absurd (hd t List.mem_cons_self) (hdisj_v t List.mem_cons_self)
                    | step hu0 hunot hu hnext2 =>
                      rename_i u
                      by_cases hum : u ∈ rem
                      · rcases stepFrom_cons_split hvlt hu0 hunot hu with ⟨a, ha, hop⟩ | huw
                        · exact ⟨u, hum, a, ha, isOps5_symm hop⟩
                        · exact absurd huw (hnohit u hum)
                      · have hdisj_u : ∀ t ∈ rem, t ∉ u :: v :: w := by
                          intro t ht hm
                          rcases List.mem_cons.1 hm with rfl | hm'
                          · exact hum ht
                          · exact hdisj_v t ht hm'
                        have hlen := Reach.pigeonhole hnd hdisj_u hnext2
                        omega
                  rcases hnext_unlock with ⟨t0, ht0, a0, ha0, hop0⟩
                  -- Helper: apply IH once we know `t ∈ rem` and `noReach left' false (t :: v :: w) (eraseNat t rem) = true`
                  have hclose : ∀ t, t ∈ rem →
                      noReach left' false (t :: v :: w) (eraseNat t rem) = true → False := by
                    intro t ht hnr'
                    rcases Reach.remove_hit t ht (hdisj_v t ht) hnext with ⟨k', hk', hr'⟩
                    have hk'eq : k' = left' := by omega
                    subst k'
                    have hw' : ∀ x ∈ t :: v :: w, x < 65536 := by
                      intro x hx
                      rcases List.mem_cons.1 hx with hxt | hx'
                      · rw [hxt]; exact (hrem t ht).1
                      · rcases List.mem_cons.1 hx' with hxv | hx''
                        · rw [hxv]; exact hvlt
                        · exact hw x hx''
                    have hrem' : ∀ x ∈ eraseNat t rem, x < 65536 ∧ x ≠ 0 :=
                      fun x hx => hrem x (mem_eraseNat_imp hx)
                    have hdisj' : ∀ x ∈ eraseNat t rem, x ∉ t :: v :: w := by
                      intro x hx hm
                      rcases List.mem_cons.1 hm with hxt | hm'
                      · rw [hxt] at hx; exact not_mem_eraseNat_of_nodup hnd hx
                      · exact hdisj_v x (mem_eraseNat_imp hx) hm'
                    exact ih left' (by omega) false (t :: v :: w) (eraseNat t rem)
                      hnr' hw' hrem' (nodup_eraseNat hnd) hdisj' trivial hr'
                  -- Helper: extract `fAll v = true` from `allPairsSym prevH fAll fMin w = true`
                  -- whenever `fMin` agrees with `fAll` for `v ≥ w.headD 0`
                  have hall_v : ∀ (fAll fMin : Nat → Bool),
                      allPairsSym prevH fAll fMin w = true →
                      (∀ u, ¬ (u < w.headD 0) → fMin u = fAll u) →
                      fAll v = true := by
                    intro fAll fMin hall hagree
                    cases prevH with
                    | false =>
                      simp only [allPairsSym] at hall
                      exact allPairsOps_spec hall hw hv0 hvnot hv
                    | true =>
                      cases w with
                      | nil =>
                        rcases hv with ⟨a, _, ha, _, _⟩; cases ha
                      | cons h tail =>
                        simp only [allPairsSym, Bool.and_eq_true] at hall
                        rcases stepFrom_cons_split (hw h List.mem_cons_self) hv0 hvnot hv with
                          ⟨b, hb, hop⟩ | hvtail
                        · exact allPairsWith_spec hall.1 hb hop
                        · by_cases hvlt_h : v < h
                          · exact absurd (hskip v ⟨hvlt_h, hvtail⟩ hv0 hvnot hnext) id
                          · have hfmin := allPairsOps_spec hall.2
                              (fun x hx => hw x (List.mem_cons_of_mem h hx))
                              hv0 (fun hm => hvnot (List.mem_cons_of_mem h hm)) hvtail
                            rw [hagree v hvlt_h] at hfmin
                            exact hfmin
                  -- Split on the fast-path `if fd.ands.isEmpty && fd.disj.isEmpty && fd.ors.isEmpty`
                  dsimp only at hnr
                  split at hnr
                  · rename_i hemp
                    simp only [Bool.and_eq_true] at hemp
                    have hf := hall_v _ _ hnr (fun u hu => by simp only [hu, ↓reduceIte])
                    have ⟨htb, hfx⟩ := checkXorOnly_isSome (hw a0 ha0) ha0 ht0 hop0
                      ⟨hemp.1.1, hemp.1.2, hemp.2⟩
                    simp only [htb, ↓reduceIte] at hf
                    cases hres : findXor v (buildFilters w rem).xors with
                    | none => rw [hres] at hfx; cases hfx
                    | some t =>
                      rw [hres] at hf
                      have htmem : t ∈ rem := ((buildFilters_inv w rem).1 v t (findXor_mem hres)).1
                      exact hclose t htmem hf
                  · have hf := hall_v _ _ hnr (fun u hu => by simp only [hu, ↓reduceIte])
                    have hcf := checkFilterFull_isSome (hw a0 ha0) ha0 ht0 hop0
                    cases hres : checkFilterFull (buildFilters w rem) v with
                    | none => rw [hres] at hcf; cases hcf
                    | some t =>
                      rw [hres] at hf
                      exact hclose t (checkFilterFull_mem hres) hf
              · have hbeq0 : (rem.length == left0) = false := beq_false_of_ne heq0
                simp only [hbeq0, Bool.false_eq_true, ↓reduceIte] at hnr
                -- General recursive step: prove `∀ v, v ≠ 0 → v ∉ w → StepFrom w v → ¬ Reach left0 (v :: w) rem`
                -- by strong induction on `v`!
                have hall_v : ∀ (v : Nat), v ≠ 0 → v ∉ w → StepFrom w v → ¬ Reach left0 (v :: w) rem := by
                  intro v
                  induction v using Nat.strongRecOn with
                  | ind v ihv =>
                    intro hv0 hvnot hv hnext
                    -- Either `v` was skipped by symmetry breaking, or `v ∈ genNextSym prevH w`
                    have hmem_gen : v ∈ genNextSym prevH w := by
                      cases prevH with
                      | false =>
                        simp only [genNextSym]
                        exact genNextGo_mem w w _ hw (fun _ h => h) hv0 (Nat.not_lt_zero v) hvnot hv
                      | true =>
                        cases w with
                        | nil => rcases hv with ⟨a, _, ha, _, _⟩; cases ha
                        | cons h tail =>
                          simp only [genNextSym]
                          rcases stepFrom_cons_split (hw h List.mem_cons_self) hv0 hvnot hv with
                            ⟨b, hb, hop⟩ | hvtail
                          · exact genNextGo_mono tail (h :: tail) _
                              (genWith_mem tail (h :: tail) _ hb hv0 (Nat.not_lt_zero v) hvnot hop)
                          · by_cases hvlt_h : v < h
                            · exact absurd (hskip v ⟨hvlt_h, hvtail⟩ hv0 hvnot hnext) id
                            · exact genNextGo_mem tail (h :: tail) _
                                (fun x hx => hw x (List.mem_cons_of_mem h hx))
                                (fun x hx => List.mem_cons_of_mem h hx)
                                hv0 hvlt_h hvnot hvtail
                    have hnr_v : noReach left0 true (v :: w) rem = true :=
                      List.all_eq_true.1 hnr v hmem_gen
                    have hvlt : v < 65536 := by
                      rcases hv with ⟨a, b, ha, hb, hop⟩
                      exact isOps5_lt (hw a ha) (hw b hb) hop
                    have hw' : ∀ x ∈ v :: w, x < 65536 := by
                      intro x hx
                      rcases List.mem_cons.1 hx with rfl | hx'
                      · exact hvlt
                      · exact hw x hx'
                    have hvnotrem : v ∉ rem := fun hm => hnohit v hm hv
                    have hdisj' : ∀ t ∈ rem, t ∉ v :: w := by
                      intro t ht hm
                      rcases List.mem_cons.1 hm with rfl | hm'
                      · exact hvnotrem ht
                      · exact hdisj t ht hm'
                    have hsym' : SymInv left0 true (v :: w) rem :=
                      ⟨hv0, hvnot, hv, fun u hult hu0 hunot hu => ihv u hult hu0 hunot hu⟩
                    exact ih left0 (Nat.lt_succ_self left0) true (v :: w) rem
                      hnr_v hw' hrem hnd hdisj' hsym' hnext
                rcases hstep (left0 + 1) rfl hreach with ⟨v, hv0, hvnot, hv, hnext⟩
                exact hall_v v hv0 hvnot hv hnext

/-! ## 4. Connecting `MultiCircuit.Computes skinny4SBox` to `Reach 7 initW initRem` -/

private def initW : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
private def initRem : List Nat := [0xcd94, 0xe1e2, 0x03fc, 0x555a]

private theorem array_getD_push' {α : Type} (arr : Array α) (v d : α) (w : Nat) :
    (arr.push v).getD w d =
      if w < arr.size then arr.getD w d else if w = arr.size then v else d := by
  by_cases hw : w < arr.size
  · have hw1 : w < arr.size + 1 := by omega
    simp [Array.getD, hw, hw1, Array.getElem_push_lt]
  · by_cases hweq : w = arr.size
    · subst hweq
      simp [Array.getD]
    · have hnot : ¬ (w < arr.size + 1) := by omega
      simp [Array.getD, hw, hweq, hnot]

private theorem evalWiresTT4_matches (x : BitVec 4) :
    ∀ (gates : List B2Gate) (accB : Array Bool) (accT : Array Nat),
      accB.size = accT.size →
      (∀ w, accB.getD w false = (accT.getD w 0).testBit x.toNat) →
      let rB := gates.foldl (fun acc g => acc.push (g.op.eval (acc.getD g.w1 false) (acc.getD g.w2 false))) accB
      let rT := gates.foldl (fun acc g => acc.push (evalOpTT mask16 g.op (acc.getD g.w1 0) (acc.getD g.w2 0))) accT
      rB.size = rT.size ∧ ∀ w, rB.getD w false = (rT.getD w 0).testBit x.toNat
  | [], accB, accT, hsz, hinv => ⟨hsz, hinv⟩
  | g :: gs, accB, accT, hsz, hinv => by
    apply evalWiresTT4_matches x gs
    · simp [Array.size_push, hsz]
    · intro w
      rw [array_getD_push', array_getD_push', ← hsz]
      by_cases hw : w < accB.size
      · simp [hw, hinv w]
      · by_cases hweq : w = accB.size
        · simp [hweq, testBit_evalOpTT_mask16 g.op _ _ x.toNat x.isLt, hinv g.w1, hinv g.w2]
        · simp [hw, hweq]

private theorem testBit_packBits' : ∀ (bits : List Bool) (j : Nat),
    (MultiCircuit.packBits bits).testBit j = bits.getD j false
  | [], j => by simp [MultiCircuit.packBits]
  | b :: bs, 0 => by
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_zero]
    cases b <;> simp [Nat.testBit_zero]
  | b :: bs, j + 1 => by
    have ih := testBit_packBits' bs j
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_succ] at ih ⊢
    rw [Nat.testBit_succ]
    cases b <;> simp [Nat.mul_add_div, ih]

private theorem evalWiresTT4_lt :
    ∀ (gates : List B2Gate) (acc : Array Nat),
      (∀ i, acc.getD i 0 < 65536) →
      ∀ i, (gates.foldl (fun acc g => acc.push (evalOpTT mask16 g.op (acc.getD g.w1 0) (acc.getD g.w2 0))) acc).getD i 0 < 65536
  | [], acc, h, i => h i
  | g :: gs, acc, h, i => by
    apply evalWiresTT4_lt gs
    intro k
    rw [array_getD_push']
    by_cases hk : k < acc.size
    · simp only [hk, ↓reduceIte]; exact h k
    · by_cases hkeq : k = acc.size
      · simp only [hkeq, Nat.lt_irrefl, ↓reduceIte]; exact evalOpTT_lt (h g.w1) (h g.w2)
      · simp only [hk, hkeq, ↓reduceIte]; decide

private theorem reach_of_gates :
    ∀ (gs : List B2Gate) (acc : Array Nat) (w rem : List Nat),
      (∀ x ∈ w, x < 65536) →
      (∀ i, acc.getD i 0 < 65536) →
      (∀ i, norm16 (acc.getD i 0) = 0 ∨ norm16 (acc.getD i 0) ∈ w) →
      (∀ t ∈ rem, t ≠ 0 ∧ ∃ i,
        norm16 ((gs.foldl (fun acc g => acc.push (evalOpTT mask16 g.op (acc.getD g.w1 0) (acc.getD g.w2 0))) acc).getD i 0) = t) →
      Reach gs.length w rem
  | [], acc, w, rem, _, _, hinv, hrem => by
    apply Reach.done
    intro t ht
    rcases hrem t ht with ⟨ht0, i, hi⟩
    simp only [List.foldl_nil] at hi
    rcases hinv i with h0 | hmem
    · rw [h0] at hi; exact absurd hi.symm ht0
    · rw [← hi]; exact hmem
  | g :: gs, acc, w, rem, hw, hacc_lt, hinv, hrem => by
    let t1 := acc.getD g.w1 0
    let t2 := acc.getD g.w2 0
    let out := evalOpTT mask16 g.op t1 t2
    let v := norm16 out
    let acc' := acc.push out
    have hacc'_lt : ∀ i, acc'.getD i 0 < 65536 := by
      intro i
      dsimp only [acc']
      rw [array_getD_push']
      by_cases hi : i < acc.size
      · simp only [hi, ↓reduceIte]; exact hacc_lt i
      · by_cases hieq : i = acc.size
        · simp only [hieq, Nat.lt_irrefl, ↓reduceIte]; exact evalOpTT_lt (hacc_lt g.w1) (hacc_lt g.w2)
        · simp only [hi, hieq, ↓reduceIte]; decide
    by_cases hvskip : v = 0 ∨ v ∈ w
    · have hinv' : ∀ i, norm16 (acc'.getD i 0) = 0 ∨ norm16 (acc'.getD i 0) ∈ w := by
        intro i
        dsimp only [acc']
        rw [array_getD_push']
        by_cases hi : i < acc.size
        · simp only [hi, ↓reduceIte]; exact hinv i
        · by_cases hieq : i = acc.size
          · simp only [hieq, Nat.lt_irrefl, ↓reduceIte]; exact hvskip
          · simp only [hi, hieq, ↓reduceIte]; left; decide
      have hr := reach_of_gates gs acc' w rem hw hacc'_lt hinv' hrem
      exact Reach.mono_k (Nat.le_succ _) hr
    · have hv0 : v ≠ 0 := fun h => hvskip (Or.inl h)
      have hvw : v ∉ w := fun h => hvskip (Or.inr h)
      have hcases := norm16_evalOpTT_cases g.op (hacc_lt g.w1) (hacc_lt g.w2)
      dsimp only at hcases
      have hstep : StepFrom w v := by
        rcases hcases with h0 | ha | hb | hop
        · exact absurd h0 hv0
        · rcases hinv g.w1 with h10 | h1w
          · rw [h10] at ha; exact absurd ha hv0
          · rw [← ha] at h1w; exact absurd h1w hvw
        · rcases hinv g.w2 with h20 | h2w
          · rw [h20] at hb; exact absurd hb hv0
          · rw [← hb] at h2w; exact absurd h2w hvw
        · rcases hinv g.w1 with h10 | h1w
          · rw [h10] at hop
            rcases isOps5_zero_left (norm16_lt (hacc_lt g.w2)) hop with h0 | hb
            · exact absurd h0 hv0
            · rcases hinv g.w2 with h20 | h2w
              · rw [h20] at hb; exact absurd hb hv0
              · rw [← hb] at h2w; exact absurd h2w hvw
          · rcases hinv g.w2 with h20 | h2w
            · rw [h20] at hop
              rcases isOps5_zero_left (norm16_lt (hacc_lt g.w1)) (isOps5_symm hop) with h0 | ha
              · exact absurd h0 hv0
              · rw [← ha] at h1w; exact absurd h1w hvw
            · exact ⟨norm16 t1, norm16 t2, h1w, h2w, hop⟩
      have hw' : ∀ x ∈ v :: w, x < 65536 := by
        intro x hx
        rcases List.mem_cons.1 hx with hxv | hx'
        · rw [hxv]; exact norm16_lt (evalOpTT_lt (hacc_lt g.w1) (hacc_lt g.w2))
        · exact hw x hx'
      have hinv' : ∀ i, norm16 (acc'.getD i 0) = 0 ∨ norm16 (acc'.getD i 0) ∈ v :: w := by
        intro i
        dsimp only [acc']
        rw [array_getD_push']
        by_cases hi : i < acc.size
        · simp only [hi, ↓reduceIte]
          rcases hinv i with h0 | hm
          · exact Or.inl h0
          · exact Or.inr (List.mem_cons_of_mem v hm)
        · by_cases hieq : i = acc.size
          · simp only [hieq, Nat.lt_irrefl, ↓reduceIte]; exact Or.inr List.mem_cons_self
          · simp only [hi, hieq, ↓reduceIte]; left; decide
      have hr := reach_of_gates gs acc' (v :: w) rem hw' hacc'_lt hinv' hrem
      exact Reach.step hv0 hvw hstep hr

private def initArr : Array Nat := #[0xaaaa, 0xcccc, 0xf0f0, 0xff00]

private theorem initArr_matches (x : BitVec 4) (w : Nat) :
    (Array.ofFn (fun i : Fin 4 => x.getLsbD i.val)).getD w false =
    (initArr.getD w 0).testBit x.toNat := by
  have hx : x.toNat < 16 := x.isLt
  have hcheck : ∀ (k : Fin 16) (j : Fin 4),
      (BitVec.ofNat 4 k.val).getLsbD j.val = (initArr.getD j.val 0).testBit k.val := by
    decide
  by_cases hw : w < 4
  · have hbv : BitVec.ofNat 4 x.toNat = x := BitVec.eq_of_toNat_eq (by simp)
    have h := hcheck ⟨x.toNat, hx⟩ ⟨w, hw⟩
    rw [hbv] at h
    have h1 : (Array.ofFn (fun i : Fin 4 => x.getLsbD i.val)).getD w false = x.getLsbD w := by
      simp [Array.getD, hw]
    rw [h1]
    exact h
  · have hsz : initArr.size = 4 := rfl
    simp [Array.getD, hw, hsz]

private theorem skinny4_outputs_norm :
    norm16 (sboxBitTT skinny4SBox 0) = 0xcd94 ∧
    norm16 (sboxBitTT skinny4SBox 1) = 0xe1e2 ∧
    norm16 (sboxBitTT skinny4SBox 2) = 0x03fc ∧
    norm16 (sboxBitTT skinny4SBox 3) = 0x555a := by
  decide +kernel

private theorem sboxBitTT_skinny4_testBit (j : Fin 4) (k : Fin 16) :
    (sboxBitTT skinny4SBox j.val).testBit k.val =
    ((skinny4SBox (BitVec.ofNat 4 k.val)).toNat).testBit j.val := by
  revert j k
  decide +kernel

private theorem sboxBitTT_skinny4_lt (j : Fin 4) :
    sboxBitTT skinny4SBox j.val < 65536 := by
  revert j
  decide +kernel

private theorem circuit_implies_reach {c : MultiCircuit 4 4}
    (hwf : c.IsWellFormed) (hsz : c.totalGates ≤ 7) (hcomp : c.Computes skinny4SBox) :
    Reach 7 initW initRem := by
  have houtlen : c.outputs.length = 4 := by
    unfold MultiCircuit.IsWellFormed MultiCircuit.isWellFormedBool at hwf
    simp only [Bool.and_eq_true, beq_iff_eq] at hwf
    exact hwf.1.1
  let final := c.gates.foldl
    (fun acc g => acc.push (evalOpTT mask16 g.op (acc.getD g.w1 0) (acc.getD g.w2 0))) initArr
  have hinit_lt : ∀ i, initArr.getD i 0 < 65536 := by
    intro i
    by_cases hi : i < 4
    · match i with
      | 0 => decide
      | 1 => decide
      | 2 => decide
      | 3 => decide
    · have hsz4 : initArr.size = 4 := rfl
      simp [Array.getD, hi, hsz4]
  have hfinal_lt : ∀ i, final.getD i 0 < 65536 := evalWiresTT4_lt c.gates initArr hinit_lt
  have hout_eq : ∀ (j : Fin 4), final.getD (c.outputs.getD j.val 0) 0 = sboxBitTT skinny4SBox j.val := by
    intro j
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 16
    · let x : BitVec 4 := BitVec.ofNat 4 k
      have hxval : x.toNat = k := by simp [x, Nat.mod_eq_of_lt hk]
      have hinitSz : (Array.ofFn (fun i : Fin 4 => x.getLsbD i.val)).size = initArr.size := rfl
      have hm := (evalWiresTT4_matches x c.gates _ initArr hinitSz (initArr_matches x)).2
      have h1 := hm (c.outputs.getD j.val 0)
      rw [hxval] at h1
      rw [← h1]
      have hcomp_x := hcomp x
      have htb := congrArg (fun n => n.testBit j.val) hcomp_x
      unfold MultiCircuit.evalNat at htb
      rw [testBit_packBits'] at htb
      have hj' : j.val < c.outputs.length := by omega
      have hmap : (c.outputs.map (fun w => (MultiCircuit.evalWires x c.gates).getD w false)).getD j.val false =
          (MultiCircuit.evalWires x c.gates).getD (c.outputs.getD j.val 0) false := by
        simp [List.getD_eq_getElem?_getD, hj']
      rw [hmap] at htb
      unfold MultiCircuit.evalWires at htb
      rw [htb]
      exact (sboxBitTT_skinny4_testBit j ⟨k, hk⟩).symm
    · have hge : 16 ≤ k := by omega
      rw [testBit_lt_65536 (hfinal_lt _) hge, testBit_lt_65536 (sboxBitTT_skinny4_lt j) hge]
  have hinit_inv : ∀ i, norm16 (initArr.getD i 0) = 0 ∨ norm16 (initArr.getD i 0) ∈ initW := by
    intro i
    by_cases hi : i < 4
    · match i with
      | 0 => right; decide
      | 1 => right; decide
      | 2 => right; decide
      | 3 => right; decide
    · have hsz4 : initArr.size = 4 := rfl
      left; simp [Array.getD, hi, hsz4]; decide
  have hw_lt : ∀ x ∈ initW, x < 65536 := by decide
  have hrem_in : ∀ t ∈ initRem, t ≠ 0 ∧ ∃ i, norm16 (final.getD i 0) = t := by
    rcases skinny4_outputs_norm with ⟨h0, h1, h2, h3⟩
    intro t ht
    simp only [initRem, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide, c.outputs.getD 0 0, by rw [hout_eq ⟨0, by decide⟩, h0]⟩
    · exact ⟨by decide, c.outputs.getD 1 0, by rw [hout_eq ⟨1, by decide⟩, h1]⟩
    · exact ⟨by decide, c.outputs.getD 2 0, by rw [hout_eq ⟨2, by decide⟩, h2]⟩
    · exact ⟨by decide, c.outputs.getD 3 0, by rw [hout_eq ⟨3, by decide⟩, h3]⟩
  have hreach_len := reach_of_gates c.gates initArr initW initRem hw_lt hinit_lt hinit_inv hrem_in
  exact Reach.mono_k hsz hreach_len

set_option maxRecDepth 8192 in
private theorem noReach_7_true : noReach 7 false initW initRem = true := by
  decide +kernel

theorem record : ¬ Crypto.Statements.CZ_rec_skinny4_gates.Record 7 := by
  rintro ⟨c, hwf, hsz, hcomp⟩
  have hreach : Reach 7 initW initRem := circuit_implies_reach hwf hsz hcomp
  exact noReach_sound 7 false initW initRem noReach_7_true
    (by decide) (by decide) (by decide) (by decide) trivial hreach

end Crypto.Claims.CZ_rec_skinny4_gates_not_s7
