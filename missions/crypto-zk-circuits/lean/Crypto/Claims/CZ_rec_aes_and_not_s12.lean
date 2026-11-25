import Crypto.Core
import Crypto.Statements.CZ_rec_aes_and

namespace Crypto.Claims.CZ_rec_aes_and_not_s12

open Crypto

/-!
  Formal Lean 4 proof of `¬ Crypto.Statements.CZ_rec_aes_and.Record 12`, certifying that
  every well-formed B2 circuit computing the FIPS-197 AES 8-bit S-box requires at least
  13 non-linear (degree-2) gates — exceeding the literature lower bound of 12.

  Proof outline:
  1. Define the `d`-th order finite difference `cubeSum f x0 vs` of any Boolean function
     `f : BitVec 8 → Bool` over a list `vs` of direction vectors. Prove symmetry (`cubeSum_swap`),
     shear invariance (`cubeSum_shear`), linearity, and vanishing on affine functions for `d ≥ 2`.
  2. Prove Schnorr's multiplicative complexity degree bound (`cubeSum_evalWires_eq_false`):
     for any gate list `gates` with `k` non-linear gates and any wire `w`, every cube sum of
     dimension `d ≥ k + 2` vanishes (`cubeSum (wire w) x0 vs = false`).
     The induction step splits on the first non-linear gate `g`: its first input computes an
     affine function `L(x) = c ^^ dot a x`; shearing `vs` reduces to two `(d - 1)`-dimensional
     subcubes on which `L` is constant, where `g` collapses to the linear gate `specializeLeft g.op b`.
  3. Define the degree-7 ANF vector `deg7Vec f : BitVec 8` whose `j`-th bit is `cubeSum f 0 (basisWithout j)`
     (a 7-dimensional cube sum). Every wire produced after the first 5 non-linear gates has `deg7Vec = 0`,
     linear gates act linearly on `deg7Vec`, and each remaining non-linear gate contributes at most one
     generator to the GF(2) subspace containing all output `deg7Vec`s.
  4. If `c.nonLinearCount ≤ 12`, at most `12 - 5 = 7` non-linear gates remain after the first 5, so
     all 8 output `deg7Vec`s lie in a GF(2) subspace of size `≤ 2^7 = 128`.
     Meanwhile, the 8 degree-7 ANF vectors of `Crypto.aesSBox` span all `2^8 = 256` elements of
     `BitVec 8` (explicitly certified via the inverse GF(2) basis masks). Contradiction (`256 ≤ 128`).
-/

/-! ## 1. BitVec 8 & Affine Boolean Function Helpers -/

private theorem bv_xor_comm (a b : BitVec 8) : a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bv_xor_assoc (a b c : BitVec 8) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bv_xor_self (a : BitVec 8) : a ^^^ a = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem bv_xor_zero (a : BitVec 8) : a ^^^ 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem bv_zero_xor (a : BitVec 8) : 0 ^^^ a = a := by
  rw [bv_xor_comm, bv_xor_zero]

private theorem bv_xor_cancel (a b : BitVec 8) : (a ^^^ b) ^^^ b = a := by
  rw [bv_xor_assoc, bv_xor_self, bv_xor_zero]

private def dot8 (a x : BitVec 8) : Bool :=
  (List.range 8).foldl (fun acc i => xor acc (a.getLsbD i && x.getLsbD i)) false

private theorem dot8_xor_right (a x y : BitVec 8) :
    dot8 a (x ^^^ y) = xor (dot8 a x) (dot8 a y) := by
  unfold dot8
  have haux : ∀ (l : List Nat) (acc1 acc2 : Bool),
      l.foldl (fun acc i => xor acc (a.getLsbD i && (x ^^^ y).getLsbD i)) (xor acc1 acc2) =
      xor (l.foldl (fun acc i => xor acc (a.getLsbD i && x.getLsbD i)) acc1)
          (l.foldl (fun acc i => xor acc (a.getLsbD i && y.getLsbD i)) acc2) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons i is ih =>
      intro acc1 acc2
      simp only [List.foldl_cons]
      have hstep : xor (xor acc1 acc2) (a.getLsbD i && (x ^^^ y).getLsbD i) =
          xor (xor acc1 (a.getLsbD i && x.getLsbD i)) (xor acc2 (a.getLsbD i && y.getLsbD i)) := by
        rw [BitVec.getLsbD_xor]
        cases acc1 <;> cases acc2 <;> cases a.getLsbD i <;> cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
      rw [hstep, ih]
  exact haux (List.range 8) false false

private theorem dot8_xor_left (a b x : BitVec 8) :
    dot8 (a ^^^ b) x = xor (dot8 a x) (dot8 b x) := by
  have hcomm : ∀ u v : BitVec 8, dot8 u v = dot8 v u := by
    intro u v
    unfold dot8
    have haux : ∀ (l : List Nat) (acc : Bool),
        l.foldl (fun acc i => xor acc (u.getLsbD i && v.getLsbD i)) acc =
        l.foldl (fun acc i => xor acc (v.getLsbD i && u.getLsbD i)) acc := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons i is ih =>
        intro acc
        simp only [List.foldl_cons, Bool.and_comm (u.getLsbD i) (v.getLsbD i)]
        exact ih _
    exact haux (List.range 8) false
  rw [hcomm (a ^^^ b) x, dot8_xor_right, hcomm x a, hcomm x b]

private theorem dot8_zero_left (x : BitVec 8) : dot8 0 x = false := by
  unfold dot8
  have haux : ∀ (l : List Nat),
      l.foldl (fun acc i => xor acc ((0 : BitVec 8).getLsbD i && x.getLsbD i)) false = false := by
    intro l
    induction l with
    | nil => rfl
    | cons i is ih =>
      simp only [List.foldl_cons]
      have hb : ((0 : BitVec 8).getLsbD i && x.getLsbD i) = false := by simp
      rw [hb, Bool.xor_false]
      exact ih
  exact haux (List.range 8)

private theorem dot8_unit_left (w : Nat) (hw : w < 8) (x : BitVec 8) :
    dot8 (BitVec.ofNat 8 1 <<< w) x = x.getLsbD w := by
  have hcheck : ∀ (w' : Fin 8) (x' : BitVec 8),
      dot8 (BitVec.ofNat 8 1 <<< w'.val) x' = x'.getLsbD w'.val := by
    decide +kernel
  exact hcheck ⟨w, hw⟩ x

private theorem linear_op_decomp (op : B2Op) (h : op.isLinear = true) (a b : Bool) :
    op.eval a b = xor (xor op.b00 (xor op.b00 op.b10 && a)) (xor op.b00 op.b01 && b) := by
  cases op with
  | mk b00 b01 b10 b11 =>
    cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> cases a <;> cases b <;>
      simp [B2Op.isLinear, B2Op.eval] at h ⊢

private def specializeLeft (op : B2Op) (b0 : Bool) : B2Op :=
  if b0 then ⟨op.b10, op.b11, op.b10, op.b11⟩ else ⟨op.b00, op.b01, op.b00, op.b01⟩

private theorem specializeLeft_isLinear (op : B2Op) (b0 : Bool) :
    (specializeLeft op b0).isLinear = true := by
  cases op with
  | mk b00 b01 b10 b11 =>
    cases b0 <;> cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> rfl

private theorem specializeLeft_eval (op : B2Op) (b0 a b : Bool) (ha : a = b0) :
    (specializeLeft op b0).eval a b = op.eval a b := by
  subst ha
  cases op with
  | mk b00 b01 b10 b11 =>
    cases a <;> cases b <;> rfl

private def IsAffine (f : BitVec 8 → Bool) : Prop :=
  ∃ (a : BitVec 8) (c : Bool), ∀ x : BitVec 8, f x = xor c (dot8 a x)

private theorem isAffine_const (c : Bool) : IsAffine (fun _ => c) :=
  ⟨0, c, fun x => by rw [dot8_zero_left]; simp⟩

private theorem isAffine_linear_op {op : B2Op} (hop : op.isLinear = true)
    {f1 f2 : BitVec 8 → Bool} (h1 : IsAffine f1) (h2 : IsAffine f2) :
    IsAffine (fun x => op.eval (f1 x) (f2 x)) := by
  rcases h1 with ⟨a1, c1, hf1⟩
  rcases h2 with ⟨a2, c2, hf2⟩
  let k1 := xor op.b00 op.b10
  let k2 := xor op.b00 op.b01
  refine ⟨(if k1 then a1 else 0) ^^^ (if k2 then a2 else 0),
    xor (xor op.b00 (k1 && c1)) (k2 && c2), ?_⟩
  intro x
  dsimp only
  rw [linear_op_decomp op hop, hf1 x, hf2 x, dot8_xor_left]
  change xor (xor op.b00 (k1 && xor c1 (dot8 a1 x))) (k2 && xor c2 (dot8 a2 x)) = _
  cases k1 <;> cases k2 <;> simp only [Bool.false_eq_true, ↓reduceIte, dot8_zero_left,
    Bool.false_and, Bool.true_and] <;>
    cases op.b00 <;> cases c1 <;> cases c2 <;> cases dot8 a1 x <;> cases dot8 a2 x <;> rfl

private theorem array_getD_push {α : Type} (arr : Array α) (v d : α) (w : Nat) :
    (arr.push v).getD w d =
      if w < arr.size then arr.getD w d else if w = arr.size then v else d := by
  by_cases hw : w < arr.size
  · have hw1 : w < arr.size + 1 := by omega
    simp [Array.getD, hw, hw1, Array.getElem_push_lt]
  · by_cases hweq : w = arr.size
    · subst hweq; simp [Array.getD]
    · have hnot : ¬ (w < arr.size + 1) := by omega
      simp [Array.getD, hw, hweq, hnot]

private def evalWiresFrom (init : BitVec 8 → Array Bool) (gates : List B2Gate) (x : BitVec 8) : Array Bool :=
  gates.foldl (fun acc g =>
    acc.push (g.op.eval (acc.getD g.w1 false) (acc.getD g.w2 false))) (init x)

private theorem evalWires_eq_evalWiresFrom (gates : List B2Gate) (x : BitVec 8) :
    MultiCircuit.evalWires x gates =
    evalWiresFrom (fun y => Array.ofFn (fun i : Fin 8 => y.getLsbD i.val)) gates x := rfl

private theorem evalWiresFrom_append (init : BitVec 8 → Array Bool) (g1 g2 : List B2Gate) (x : BitVec 8) :
    evalWiresFrom init (g1 ++ g2) x = evalWiresFrom (evalWiresFrom init g1) g2 x := by
  unfold evalWiresFrom
  exact List.foldl_append

private theorem evalWiresFrom_size (init : BitVec 8 → Array Bool) (gates : List B2Gate) (x : BitVec 8) :
    (evalWiresFrom init gates x).size = (init x).size + gates.length := by
  unfold evalWiresFrom
  induction gates generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h := ih (fun y => (init y).push (g.op.eval ((init y).getD g.w1 false) ((init y).getD g.w2 false)))
    simp only [Array.size_push] at h
    omega

private theorem evalWires_linear_isAffine (gates : List B2Gate)
    (hlin : ∀ g ∈ gates, g.op.isLinear = true) (w : Nat) :
    IsAffine (fun x => (MultiCircuit.evalWires x gates).getD w false) := by
  have hstep : ∀ (gs : List B2Gate) (init : BitVec 8 → Array Bool) (sz : Nat),
      (∀ x, (init x).size = sz) →
      (∀ u, IsAffine (fun x => (init x).getD u false)) →
      (∀ g ∈ gs, g.op.isLinear = true) →
      ∀ u, IsAffine (fun x => (evalWiresFrom init gs x).getD u false) := by
    intro gs
    induction gs with
    | nil =>
      intro init _ _ haff _ u
      exact haff u
    | cons g gs' ih =>
      intro init sz hsz haff hlin' u
      let init' : BitVec 8 → Array Bool :=
        fun x => (init x).push (g.op.eval ((init x).getD g.w1 false) ((init x).getD g.w2 false))
      have hsz' : ∀ x, (init' x).size = sz + 1 := fun x => by simp [init', Array.size_push, hsz x]
      have hg_lin : g.op.isLinear = true := hlin' g List.mem_cons_self
      have hnew : IsAffine (fun x => g.op.eval ((init x).getD g.w1 false) ((init x).getD g.w2 false)) :=
        isAffine_linear_op hg_lin (haff g.w1) (haff g.w2)
      have haff' : ∀ v, IsAffine (fun x => (init' x).getD v false) := by
        intro v
        by_cases hv : v < sz
        · have heq : (fun x => (init' x).getD v false) = (fun x => (init x).getD v false) := by
            funext x; dsimp only [init']; rw [array_getD_push, hsz x]; simp [hv]
          rw [heq]; exact haff v
        · by_cases hveq : v = sz
          · have heq : (fun x => (init' x).getD v false) =
                (fun x => g.op.eval ((init x).getD g.w1 false) ((init x).getD g.w2 false)) := by
              funext x; dsimp only [init']; rw [array_getD_push, hsz x]; simp [hveq]
            rw [heq]; exact hnew
          · have heq : (fun x => (init' x).getD v false) = (fun _ => false) := by
              funext x; dsimp only [init']; rw [array_getD_push, hsz x]; simp [hv, hveq]
            rw [heq]; exact isAffine_const false
      exact ih init' (sz + 1) hsz' haff' (fun g' hg' => hlin' g' (List.mem_cons_of_mem g hg')) u
  apply hstep gates (fun y => Array.ofFn (fun i : Fin 8 => y.getLsbD i.val)) 8
  · intro x; simp
  · intro u
    by_cases hu : u < 8
    · refine ⟨BitVec.ofNat 8 1 <<< u, false, ?_⟩
      intro x
      dsimp only
      rw [dot8_unit_left u hu x]
      simp [Array.getD, hu]
    · refine ⟨0, false, ?_⟩
      intro x
      dsimp only
      rw [dot8_zero_left]
      simp [Array.getD, hu]
  · exact hlin

/-! ## 2. Higher-Order Cube Sums & Schnorr's Multiplicative Complexity Bound -/

private def cubeSum (f : BitVec 8 → Bool) (x0 : BitVec 8) : List (BitVec 8) → Bool
  | [] => f x0
  | v :: vs => xor (cubeSum f x0 vs) (cubeSum f (x0 ^^^ v) vs)

private def InCube (x0 : BitVec 8) : List (BitVec 8) → BitVec 8 → Prop
  | [], x => x = x0
  | v :: vs, x => InCube x0 vs x ∨ InCube (x0 ^^^ v) vs x

private theorem cubeSum_congr {f g : BitVec 8 → Bool} {x0 : BitVec 8} :
    ∀ {vs : List (BitVec 8)}, (∀ x, InCube x0 vs x → f x = g x) →
      cubeSum f x0 vs = cubeSum g x0 vs
  | [], h => h x0 rfl
  | v :: vs, h => by
    simp only [cubeSum]
    rw [cubeSum_congr (fun x hx => h x (Or.inl hx)),
        cubeSum_congr (fun x hx => h x (Or.inr hx))]

private theorem cubeSum_xor (f g : BitVec 8 → Bool) (x0 : BitVec 8) :
    ∀ vs : List (BitVec 8),
      cubeSum (fun x => xor (f x) (g x)) x0 vs = xor (cubeSum f x0 vs) (cubeSum g x0 vs)
  | [] => rfl
  | v :: vs => by
    simp only [cubeSum, cubeSum_xor f g x0 vs, cubeSum_xor f g (x0 ^^^ v) vs]
    cases cubeSum f x0 vs <;> cases cubeSum g x0 vs <;>
      cases cubeSum f (x0 ^^^ v) vs <;> cases cubeSum g (x0 ^^^ v) vs <;> rfl

private theorem cubeSum_const (c : Bool) (x0 : BitVec 8) (v : BitVec 8) (vs : List (BitVec 8)) :
    cubeSum (fun _ => c) x0 (v :: vs) = false := by
  have hconst : ∀ (u1 u2 : BitVec 8) (ws : List (BitVec 8)),
      cubeSum (fun _ => c) u1 ws = cubeSum (fun _ => c) u2 ws := by
    intro u1 u2 ws
    induction ws generalizing u1 u2 with
    | nil => rfl
    | cons w ws' ih =>
      simp only [cubeSum]
      rw [ih u1 u2, ih (u1 ^^^ w) (u2 ^^^ w)]
  simp only [cubeSum]
  rw [hconst x0 (x0 ^^^ v) vs]
  cases cubeSum (fun _ => c) (x0 ^^^ v) vs <;> rfl

private theorem cubeSum_affine {f : BitVec 8 → Bool} (haff : IsAffine f) (x0 v1 v2 : BitVec 8)
    (vs : List (BitVec 8)) : cubeSum f x0 (v1 :: v2 :: vs) = false := by
  rcases haff with ⟨a, c, hf⟩
  have h1 : ∀ u : BitVec 8, xor (f u) (f (u ^^^ v1)) = dot8 a v1 := by
    intro u
    rw [hf u, hf (u ^^^ v1), dot8_xor_right]
    cases c <;> cases dot8 a u <;> cases dot8 a v1 <;> rfl
  have hstep : ∀ (u : BitVec 8) (ws : List (BitVec 8)),
      cubeSum f u (v1 :: ws) = cubeSum (fun x => xor (f x) (f (x ^^^ v1))) u ws := by
    intro u ws
    induction ws generalizing u with
    | nil => rfl
    | cons w ws' ih =>
      simp only [cubeSum] at ih ⊢
      rw [← ih u, ← ih (u ^^^ w)]
      have ha : (u ^^^ w) ^^^ v1 = (u ^^^ v1) ^^^ w := by
        rw [bv_xor_assoc, bv_xor_comm w v1, ← bv_xor_assoc]
      rw [ha]
      cases cubeSum f u ws' <;> cases cubeSum f (u ^^^ w) ws' <;>
        cases cubeSum f (u ^^^ v1) ws' <;> cases cubeSum f ((u ^^^ v1) ^^^ w) ws' <;> rfl
  rw [hstep x0 (v2 :: vs)]
  have hcongr : cubeSum (fun x => xor (f x) (f (x ^^^ v1))) x0 (v2 :: vs) =
      cubeSum (fun _ => dot8 a v1) x0 (v2 :: vs) :=
    cubeSum_congr (fun x _ => h1 x)
  rw [hcongr]
  exact cubeSum_const (dot8 a v1) x0 v2 vs

private theorem cubeSum_swap (f : BitVec 8 → Bool) (x0 a b : BitVec 8) (vs : List (BitVec 8)) :
    cubeSum f x0 (a :: b :: vs) = cubeSum f x0 (b :: a :: vs) := by
  simp only [cubeSum]
  have h : (x0 ^^^ a) ^^^ b = (x0 ^^^ b) ^^^ a := by
    rw [bv_xor_assoc, bv_xor_comm a b, ← bv_xor_assoc]
  rw [h]
  cases cubeSum f x0 vs <;> cases cubeSum f (x0 ^^^ b) vs <;>
    cases cubeSum f (x0 ^^^ a) vs <;> cases cubeSum f ((x0 ^^^ b) ^^^ a) vs <;> rfl

private theorem cubeSum_shear (f : BitVec 8 → Bool) (x0 a b : BitVec 8) (vs : List (BitVec 8)) :
    cubeSum f x0 (a :: b :: vs) = cubeSum f x0 (a :: (b ^^^ a) :: vs) := by
  simp only [cubeSum]
  have h1 : (x0 ^^^ a) ^^^ (b ^^^ a) = x0 ^^^ b := by
    rw [bv_xor_assoc, bv_xor_comm a (b ^^^ a), bv_xor_cancel]
  have h2 : (x0 ^^^ a) ^^^ b = x0 ^^^ (b ^^^ a) := by
    rw [bv_xor_assoc, bv_xor_comm a b]
  rw [h1, h2]
  cases cubeSum f x0 vs <;> cases cubeSum f (x0 ^^^ (b ^^^ a)) vs <;>
    cases cubeSum f (x0 ^^^ a) vs <;> cases cubeSum f (x0 ^^^ b) vs <;> rfl

private theorem cubeSum_move_head (f : BitVec 8 → Bool) (x0 : BitVec 8) :
    ∀ (p q : List (BitVec 8)) (v : BitVec 8),
      cubeSum f x0 (p ++ v :: q) = cubeSum f x0 (v :: (p ++ q))
  | [], _, _ => rfl
  | u :: ps, q, v => by
    simp only [List.cons_append]
    have h1 : cubeSum f x0 (u :: (ps ++ v :: q)) = cubeSum f x0 (u :: v :: (ps ++ q)) := by
      change xor (cubeSum f x0 (ps ++ v :: q)) (cubeSum f (x0 ^^^ u) (ps ++ v :: q)) =
             xor (cubeSum f x0 (v :: (ps ++ q))) (cubeSum f (x0 ^^^ u) (v :: (ps ++ q)))
      rw [cubeSum_move_head f x0 ps q v, cubeSum_move_head f (x0 ^^^ u) ps q v]
    rw [h1, cubeSum_swap]

private def shearTail (a v0 : BitVec 8) : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | w :: ws => (if dot8 a w then w ^^^ v0 else w) :: shearTail a v0 ws

private theorem shearTail_length (a v0 : BitVec 8) :
    ∀ ws : List (BitVec 8), (shearTail a v0 ws).length = ws.length
  | [] => rfl
  | w :: ws => by simp [shearTail, shearTail_length a v0 ws]

private theorem shearTail_orth (a v0 : BitVec 8) (hv0 : dot8 a v0 = true) :
    ∀ ws : List (BitVec 8), ∀ w ∈ shearTail a v0 ws, dot8 a w = false
  | [], _, hw => absurd hw List.not_mem_nil
  | u :: ws, w, hw => by
    simp only [shearTail] at hw
    rcases List.mem_cons.1 hw with rfl | hw'
    · cases hu : dot8 a u
      · simp [hu]
      · simp [dot8_xor_right, hu, hv0]
    · exact shearTail_orth a v0 hv0 ws w hw'

private theorem cubeSum_shearTail (f : BitVec 8 → Bool) (a v0 : BitVec 8) :
    ∀ (x0 : BitVec 8) (ws : List (BitVec 8)),
      cubeSum f x0 (v0 :: ws) = cubeSum f x0 (v0 :: shearTail a v0 ws)
  | _, [] => rfl
  | x0, u :: ws => by
    simp only [shearTail]
    have htail : ∀ (y0 : BitVec 8) (u' : BitVec 8),
        cubeSum f y0 (v0 :: u' :: ws) = cubeSum f y0 (v0 :: u' :: shearTail a v0 ws) := by
      intro y0 u'
      rw [cubeSum_swap f y0 v0 u' ws, cubeSum_swap f y0 v0 u' (shearTail a v0 ws)]
      change xor (cubeSum f y0 (v0 :: ws)) (cubeSum f (y0 ^^^ u') (v0 :: ws)) =
             xor (cubeSum f y0 (v0 :: shearTail a v0 ws)) (cubeSum f (y0 ^^^ u') (v0 :: shearTail a v0 ws))
      rw [cubeSum_shearTail f a v0 y0 ws, cubeSum_shearTail f a v0 (y0 ^^^ u') ws]
    cases dot8 a u
    · exact htail x0 u
    · rw [cubeSum_shear f x0 v0 u ws]
      exact htail x0 (u ^^^ v0)

private theorem inCube_dot8_const (a x0 : BitVec 8) :
    ∀ (vs : List (BitVec 8)), (∀ v ∈ vs, dot8 a v = false) →
      ∀ x, InCube x0 vs x → dot8 a x = dot8 a x0
  | [], _, x, hx => by rw [hx]
  | v :: vs, horth, x, hx => by
    have hv0 : dot8 a v = false := horth v List.mem_cons_self
    have hrest : ∀ u ∈ vs, dot8 a u = false := fun u hu => horth u (List.mem_cons_of_mem v hu)
    rcases hx with h1 | h2
    · exact inCube_dot8_const a x0 vs hrest x h1
    · rw [inCube_dot8_const a (x0 ^^^ v) vs hrest x h2, dot8_xor_right, hv0, Bool.xor_false]

private def nlCount (gates : List B2Gate) : Nat :=
  (gates.filter (fun g => !g.op.isLinear)).length

private theorem nlCount_append (g1 g2 : List B2Gate) :
    nlCount (g1 ++ g2) = nlCount g1 + nlCount g2 := by
  unfold nlCount
  rw [List.filter_append, List.length_append]

private theorem split_first_nl :
    ∀ (gates : List B2Gate), 0 < nlCount gates →
      ∃ (pre suf : List B2Gate) (g : B2Gate),
        gates = pre ++ g :: suf ∧
        (∀ h ∈ pre, h.op.isLinear = true) ∧
        g.op.isLinear = false ∧
        nlCount suf + 1 = nlCount gates
  | [], h => by simp [nlCount] at h
  | g :: gs, h => by
    cases hg : g.op.isLinear
    · refine ⟨[], gs, g, rfl, fun _ hm => absurd hm List.not_mem_nil, hg, ?_⟩
      unfold nlCount
      simp [hg]
    · have hpos : 0 < nlCount gs := by
        unfold nlCount at h ⊢
        simp [hg] at h ⊢
        exact h
      rcases split_first_nl gs hpos with ⟨pre, suf, g0, rfl, hpre, hg0, hcnt⟩
      refine ⟨g :: pre, suf, g0, rfl, ?_, hg0, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact hg
        · exact hpre x hx'
      · unfold nlCount at hcnt ⊢
        simp [hg] at hcnt ⊢
        exact hcnt

private theorem split_by_bool {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) ∨ ∃ (pre suf : List α) (v : α), l = pre ++ v :: suf ∧ p v = true
  | [] => Or.inl (fun _ hm => absurd hm List.not_mem_nil)
  | x :: xs => by
    cases hx : p x
    · rcases split_by_bool p xs with hall | ⟨pre, suf, v, rfl, hv⟩
      · left
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact hx
        · exact hall y hy'
      · right
        exact ⟨x :: pre, suf, v, rfl, hv⟩
    · right
      exact ⟨[], xs, x, rfl, hx⟩

private theorem evalWires_specialize_eq (pre suf : List B2Gate) (g : B2Gate) (b0 : Bool) (x : BitVec 8)
    (hval : (MultiCircuit.evalWires x pre).getD g.w1 false = b0) :
    MultiCircuit.evalWires x (pre ++ ⟨specializeLeft g.op b0, g.w1, g.w2⟩ :: suf) =
    MultiCircuit.evalWires x (pre ++ g :: suf) := by
  rw [evalWires_eq_evalWiresFrom, evalWires_eq_evalWiresFrom,
      evalWiresFrom_append, evalWiresFrom_append]
  unfold evalWiresFrom
  simp only [List.foldl_cons]
  let arr := MultiCircuit.evalWires x pre
  have h1 : (specializeLeft g.op b0).eval (arr.getD g.w1 false) (arr.getD g.w2 false) =
      g.op.eval (arr.getD g.w1 false) (arr.getD g.w2 false) :=
    specializeLeft_eval g.op b0 _ _ hval
  change List.foldl _ (arr.push ((specializeLeft g.op b0).eval (arr.getD g.w1 false) (arr.getD g.w2 false))) suf =
         List.foldl _ (arr.push (g.op.eval (arr.getD g.w1 false) (arr.getD g.w2 false))) suf
  rw [h1]

/-- Schnorr's multiplicative complexity degree bound via cube sums:
    any wire computed with `k` non-linear gates has vanishing cube sums of dimension `≥ k + 2`. -/
private theorem schnorr_cubeSum :
    ∀ (k : Nat) (gates : List B2Gate) (w : Nat) (x0 : BitVec 8) (vs : List (BitVec 8)),
      nlCount gates ≤ k →
      k + 2 ≤ vs.length →
      cubeSum (fun x => (MultiCircuit.evalWires x gates).getD w false) x0 vs = false
  | 0, gates, w, x0, vs, hnl, hlen => by
    have hlin : ∀ g ∈ gates, g.op.isLinear = true := by
      intro g hg
      cases hgl : g.op.isLinear
      · exfalso
        have hmem : g ∈ gates.filter (fun g => !g.op.isLinear) :=
          List.mem_filter.2 ⟨hg, by simp [hgl]⟩
        have hpos : 0 < (gates.filter (fun g => !g.op.isLinear)).length := by
          cases hf : gates.filter (fun g => !g.op.isLinear) with
          | nil => rw [hf] at hmem; exact absurd hmem List.not_mem_nil
          | cons _ _ => simp
        unfold nlCount at hnl
        omega
      · rfl
    cases vs with
    | nil => simp at hlen
    | cons v1 vs1 =>
      cases vs1 with
      | nil => simp at hlen
      | cons v2 vs2 =>
        exact cubeSum_affine (evalWires_linear_isAffine gates hlin w) x0 v1 v2 vs2
  | k + 1, gates, w, x0, vs, hnl, hlen => by
    cases Nat.eq_zero_or_pos (nlCount gates) with
    | inl h0 =>
      exact schnorr_cubeSum 0 gates w x0 vs (by omega) (by omega)
    | inr hpos =>
      rcases split_first_nl gates hpos with ⟨pre, suf, g, rfl, hpre, hg_nl, hcnt⟩
      have haff_w1 : IsAffine (fun x => (MultiCircuit.evalWires x pre).getD g.w1 false) :=
        evalWires_linear_isAffine pre hpre g.w1
      rcases haff_w1 with ⟨a, c, hw1⟩
      dsimp only at hw1
      have hnl_spec : ∀ b0 : Bool,
          nlCount (pre ++ ⟨specializeLeft g.op b0, g.w1, g.w2⟩ :: suf) ≤ k := by
        intro b0
        rw [nlCount_append]
        have hpre0 : nlCount pre = 0 := by
          unfold nlCount
          simp
          exact hpre
        have hcons : nlCount (⟨specializeLeft g.op b0, g.w1, g.w2⟩ :: suf) = nlCount suf := by
          unfold nlCount
          simp [specializeLeft_isLinear]
        omega
      rcases split_by_bool (fun v => dot8 a v) vs with horth | ⟨p, q, v0, rfl, hv0⟩
      · -- `L(x)` is constant `= b0` on the entire cube `x0 + span(vs)`
        let b0 := xor c (dot8 a x0)
        let gates' := pre ++ ⟨specializeLeft g.op b0, g.w1, g.w2⟩ :: suf
        have heq : cubeSum (fun x => (MultiCircuit.evalWires x (pre ++ g :: suf)).getD w false) x0 vs =
            cubeSum (fun x => (MultiCircuit.evalWires x gates').getD w false) x0 vs := by
          apply cubeSum_congr
          intro x hx
          have hx_w1 : (MultiCircuit.evalWires x pre).getD g.w1 false = b0 := by
            rw [hw1 x, inCube_dot8_const a x0 vs horth x hx]
          rw [evalWires_specialize_eq pre suf g b0 x hx_w1]
        rw [heq]
        exact schnorr_cubeSum k gates' w x0 vs (hnl_spec b0) (by omega)
      · -- Move `v0` to head and shear the tail `pq` so every tail vector is orthogonal to `a`
        let pq := p ++ q
        let tail := shearTail a v0 pq
        have htail_len : k + 2 ≤ tail.length := by
          rw [shearTail_length]
          simp only [pq, List.length_append, List.length_cons] at hlen ⊢
          omega
        have htail_orth : ∀ u ∈ tail, dot8 a u = false := shearTail_orth a v0 hv0 pq
        rw [cubeSum_move_head _ x0 p q v0, cubeSum_shearTail _ a v0 x0 pq]
        simp only [cubeSum]
        let b0 := xor c (dot8 a x0)
        let b1 := xor c (dot8 a (x0 ^^^ v0))
        let g0 := pre ++ ⟨specializeLeft g.op b0, g.w1, g.w2⟩ :: suf
        let g1 := pre ++ ⟨specializeLeft g.op b1, g.w1, g.w2⟩ :: suf
        have heq0 : cubeSum (fun x => (MultiCircuit.evalWires x (pre ++ g :: suf)).getD w false) x0 tail =
            cubeSum (fun x => (MultiCircuit.evalWires x g0).getD w false) x0 tail := by
          apply cubeSum_congr
          intro x hx
          have hx_w1 : (MultiCircuit.evalWires x pre).getD g.w1 false = b0 := by
            rw [hw1 x, inCube_dot8_const a x0 tail htail_orth x hx]
          rw [evalWires_specialize_eq pre suf g b0 x hx_w1]
        have heq1 : cubeSum (fun x => (MultiCircuit.evalWires x (pre ++ g :: suf)).getD w false) (x0 ^^^ v0) tail =
            cubeSum (fun x => (MultiCircuit.evalWires x g1).getD w false) (x0 ^^^ v0) tail := by
          apply cubeSum_congr
          intro x hx
          have hx_w1 : (MultiCircuit.evalWires x pre).getD g.w1 false = b1 := by
            rw [hw1 x, inCube_dot8_const a (x0 ^^^ v0) tail htail_orth x hx]
          rw [evalWires_specialize_eq pre suf g b1 x hx_w1]
        rw [heq0, heq1,
            schnorr_cubeSum k g0 w x0 tail (hnl_spec b0) htail_len,
            schnorr_cubeSum k g1 w (x0 ^^^ v0) tail (hnl_spec b1) htail_len]
        rfl

/-! ## 3. Degree-7 ANF Vector & GF(2) Subspace Span Bound -/

private def basisWithout (j : Nat) : List (BitVec 8) :=
  ((List.range 8).filter (fun i => i != j)).map (fun i => BitVec.ofNat 8 1 <<< i)

private theorem basisWithout_length (j : Nat) (hj : j < 8) : (basisWithout j).length = 7 := by
  have hcheck : ∀ j' : Fin 8, (basisWithout j'.val).length = 7 := by decide +kernel
  exact hcheck ⟨j, hj⟩

private def deg7Vec (f : BitVec 8 → Bool) : BitVec 8 :=
  (List.range 8).foldl (fun acc j =>
    if cubeSum f 0 (basisWithout j) then acc ||| (BitVec.ofNat 8 1 <<< j) else acc) 0

private theorem deg7Vec_getLsbD (f : BitVec 8 → Bool) (j : Nat) (hj : j < 8) :
    (deg7Vec f).getLsbD j = cubeSum f 0 (basisWithout j) := by
  unfold deg7Vec
  have hstep : ∀ (k : Nat) (acc : BitVec 8), k ≤ 8 →
      ((List.range k).foldl (fun acc i =>
        if cubeSum f 0 (basisWithout i) then acc ||| (BitVec.ofNat 8 1 <<< i) else acc) acc).getLsbD j =
      if j < k then (acc.getLsbD j || cubeSum f 0 (basisWithout j)) else acc.getLsbD j := by
    intro k
    induction k with
    | zero => intro acc _; simp
    | succ k' ih =>
      intro acc hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hk8 : k' < 8 := by omega
      have hunit : ∀ m, (BitVec.ofNat 8 1 <<< k').getLsbD m = decide (m = k') := by
        intro m
        have hc : ∀ (k0 : Fin 8) (m0 : Nat), m0 < 8 →
            (BitVec.ofNat 8 1 <<< k0.val).getLsbD m0 = decide (m0 = k0.val) := by
          intro k0 m0 hm0
          have hc2 : ∀ (a b : Fin 8), (BitVec.ofNat 8 1 <<< a.val).getLsbD b.val = decide (b.val = a.val) := by
            decide +kernel
          exact hc2 k0 ⟨m0, hm0⟩
        by_cases hm8 : m < 8
        · exact hc ⟨k', hk8⟩ m hm8
        · have hne : m ≠ k' := by omega
          simp [BitVec.getLsbD_shiftLeft, hm8, hne]
      by_cases hjlt : j < k'
      · have hjlt' : j < k' + 1 := by omega
        have hjne : j ≠ k' := by omega
        cases hcb : cubeSum f 0 (basisWithout k')
        · simp only [Bool.false_eq_true, ↓reduceIte, ih acc (by omega), hjlt, hjlt']
        · simp only [↓reduceIte, BitVec.getLsbD_or, hunit j, hjne, decide_false, Bool.or_false,
            ih acc (by omega), hjlt, hjlt']
      · by_cases hjeq : j = k'
        · subst hjeq
          have hjlt' : j < j + 1 := Nat.lt_succ_self j
          cases hcb : cubeSum f 0 (basisWithout j)
          · simp only [Bool.false_eq_true, ↓reduceIte, ih acc (by omega), hjlt, hjlt', Bool.or_false]
          · simp only [↓reduceIte, BitVec.getLsbD_or, hunit j, decide_true, Bool.or_true, hjlt']
        · have hnot' : ¬ (j < k' + 1) := by omega
          cases hcb : cubeSum f 0 (basisWithout k')
          · simp only [Bool.false_eq_true, ↓reduceIte, ih acc (by omega), hjlt, hnot']
          · simp only [↓reduceIte, BitVec.getLsbD_or, hunit j, hjeq, decide_false, Bool.or_false,
              ih acc (by omega), hjlt, hnot']
  rw [hstep 8 0 (Nat.le_refl 8)]
  simp [hj]

private theorem deg7Vec_eq_zero_of_all_false {f : BitVec 8 → Bool}
    (h : ∀ j, j < 8 → cubeSum f 0 (basisWithout j) = false) : deg7Vec f = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [deg7Vec_getLsbD f j hj, h j hj]
  simp

private theorem deg7Vec_linear_op {op : B2Op} (hop : op.isLinear = true) (f1 f2 : BitVec 8 → Bool) :
    deg7Vec (fun x => op.eval (f1 x) (f2 x)) =
    (if xor op.b00 op.b10 then deg7Vec f1 else 0) ^^^ (if xor op.b00 op.b01 then deg7Vec f2 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [deg7Vec_getLsbD _ j hj, BitVec.getLsbD_xor]
  have h7 : (basisWithout j).length = 7 := basisWithout_length j hj
  cases hbw : basisWithout j with
  | nil => rw [hbw] at h7; simp at h7
  | cons v vs =>
    have hfun : (fun x => op.eval (f1 x) (f2 x)) =
        (fun x => xor (xor op.b00 (xor op.b00 op.b10 && f1 x)) (xor op.b00 op.b01 && f2 x)) := by
      funext x; exact linear_op_decomp op hop (f1 x) (f2 x)
    rw [hfun, cubeSum_xor, cubeSum_xor, cubeSum_const op.b00 0 v vs, Bool.false_xor]
    have hmul : ∀ (k : Bool) (g : BitVec 8 → Bool),
        cubeSum (fun x => k && g x) 0 (v :: vs) = (if k then deg7Vec g else 0).getLsbD j := by
      intro k g
      cases k
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [cubeSum_const false 0 v vs]; simp
      · simp only [Bool.true_and, ↓reduceIte]
        rw [deg7Vec_getLsbD g j hj, hbw]
    rw [hmul, hmul]

private def InSpan (gens : List (BitVec 8)) (v : BitVec 8) : Prop :=
  ∃ m : List Bool, m.length = gens.length ∧
    (List.zip gens m).foldl (fun acc pr => if pr.2 then acc ^^^ pr.1 else acc) 0 = v

private def xorComb (gens : List (BitVec 8)) (m : List Bool) : BitVec 8 :=
  (List.zip gens m).foldl (fun acc pr => if pr.2 then acc ^^^ pr.1 else acc) 0

private theorem xorComb_nil : xorComb [] [] = 0 := rfl

private theorem xorComb_cons (g : BitVec 8) (gs : List (BitVec 8)) (b : Bool) (bs : List Bool) :
    xorComb (g :: gs) (b :: bs) = (if b then g else 0) ^^^ xorComb gs bs := by
  unfold xorComb
  have haux : ∀ (l : List (BitVec 8 × Bool)) (a : BitVec 8),
      l.foldl (fun acc pr => if pr.2 then acc ^^^ pr.1 else acc) a =
      a ^^^ l.foldl (fun acc pr => if pr.2 then acc ^^^ pr.1 else acc) 0 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons pr ps ih =>
      intro a
      simp only [List.foldl_cons]
      cases pr.2
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih a
      · simp only [↓reduceIte, bv_zero_xor]
        rw [ih (a ^^^ pr.1), ih pr.1, bv_xor_assoc]
  simp only [List.zip_cons_cons, List.foldl_cons]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bv_zero_xor]
  · simp only [↓reduceIte, bv_zero_xor]
    exact haux (List.zip gs bs) g

private theorem inSpan_zero (gens : List (BitVec 8)) : InSpan gens 0 := by
  refine ⟨List.replicate gens.length false, List.length_replicate, ?_⟩
  change xorComb gens (List.replicate gens.length false) = 0
  induction gens with
  | nil => rfl
  | cons g gs ih =>
    rw [List.length_cons, List.replicate_succ, xorComb_cons]
    simp [ih]

private theorem inSpan_xor {gens : List (BitVec 8)} {a b : BitVec 8}
    (ha : InSpan gens a) (hb : InSpan gens b) : InSpan gens (a ^^^ b) := by
  rcases ha with ⟨m1, h1, rfl⟩
  rcases hb with ⟨m2, h2, rfl⟩
  refine ⟨List.zipWith xor m1 m2, by simp [h1, h2], ?_⟩
  change xorComb gens (List.zipWith xor m1 m2) = xorComb gens m1 ^^^ xorComb gens m2
  induction gens generalizing m1 m2 with
  | nil =>
    cases m1 <;> cases m2 <;> simp [xorComb] at h1 h2 ⊢
  | cons g gs ih =>
    cases m1 with
    | nil => simp at h1
    | cons b1 bs1 =>
      cases m2 with
      | nil => simp at h2
      | cons b2 bs2 =>
        simp only [List.length_cons, Nat.succ.injEq] at h1 h2
        simp only [List.zipWith_cons_cons, xorComb_cons, ih bs1 h1 bs2 h2]
        apply BitVec.eq_of_getLsbD_eq
        intro i _
        cases b1 <;> cases b2 <;>
          simp [BitVec.getLsbD_xor] <;>
          cases g.getLsbD i <;> cases (xorComb gs bs1).getLsbD i <;> cases (xorComb gs bs2).getLsbD i <;> rfl

private theorem inSpan_cons_of_mem {g : BitVec 8} {gens : List (BitVec 8)} {v : BitVec 8}
    (hv : InSpan gens v) : InSpan (g :: gens) v := by
  rcases hv with ⟨m, hm, rfl⟩
  refine ⟨false :: m, by simp [hm], ?_⟩
  change xorComb (g :: gens) (false :: m) = xorComb gens m
  rw [xorComb_cons]; simp

private theorem inSpan_cons_self (g : BitVec 8) (gens : List (BitVec 8)) : InSpan (g :: gens) g := by
  rcases inSpan_zero gens with ⟨m, hm, h0⟩
  change xorComb gens m = 0 at h0
  refine ⟨true :: m, by simp [hm], ?_⟩
  change xorComb (g :: gens) (true :: m) = g
  rw [xorComb_cons]
  simp only [↓reduceIte]
  rw [h0, bv_xor_zero]

private theorem split_after_k_nl :
    ∀ (k : Nat) (gates : List B2Gate),
      ∃ (pre suf : List B2Gate),
        gates = pre ++ suf ∧ nlCount pre ≤ k ∧ nlCount suf ≤ nlCount gates - k
  | 0, gates => ⟨[], gates, rfl, Nat.zero_le 0, by simp⟩
  | k + 1, [] => ⟨[], [], rfl, Nat.zero_le _, by simp [nlCount]⟩
  | k + 1, g :: gs => by
    cases hg : g.op.isLinear
    · rcases split_after_k_nl k gs with ⟨pre, suf, rfl, hpre, hsuf⟩
      refine ⟨g :: pre, suf, rfl, ?_, ?_⟩
      · unfold nlCount at hpre ⊢; simp [hg]; omega
      · unfold nlCount at hsuf ⊢; simp [hg] at hsuf ⊢; omega
    · rcases split_after_k_nl (k + 1) gs with ⟨pre, suf, rfl, hpre, hsuf⟩
      refine ⟨g :: pre, suf, rfl, ?_, ?_⟩
      · unfold nlCount at hpre ⊢; simp [hg]; exact hpre
      · simp only [nlCount, List.filter_cons, hg, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        exact hsuf

private theorem deg7Vec_wires_inSpan_suffix (init : BitVec 8 → Array Bool) (sz : Nat)
    (hsz : ∀ x, (init x).size = sz)
    (hinit : ∀ w, deg7Vec (fun x => (init x).getD w false) = 0)
    (suf : List B2Gate) :
    ∃ gens : List (BitVec 8),
      gens.length ≤ nlCount suf ∧
      ∀ w, InSpan gens (deg7Vec (fun x => (evalWiresFrom init suf x).getD w false)) := by
  have hgo : ∀ (gs : List B2Gate) (cur : BitVec 8 → Array Bool) (s : Nat) (acc : List (BitVec 8)),
      (∀ x, (cur x).size = s) →
      (∀ w, InSpan acc (deg7Vec (fun x => (cur x).getD w false))) →
      ∃ gens : List (BitVec 8),
        gens.length ≤ acc.length + nlCount gs ∧
        ∀ w, InSpan gens (deg7Vec (fun x => (evalWiresFrom cur gs x).getD w false)) := by
    intro gs
    induction gs with
    | nil =>
      intro cur _ acc _ hacc
      exact ⟨acc, by simp [nlCount], hacc⟩
    | cons g gs' ih =>
      intro cur s acc hs hacc
      let cur' : BitVec 8 → Array Bool :=
        fun x => (cur x).push (g.op.eval ((cur x).getD g.w1 false) ((cur x).getD g.w2 false))
      have hs' : ∀ x, (cur' x).size = s + 1 := fun x => by simp [cur', Array.size_push, hs x]
      cases hg : g.op.isLinear
      · -- Non-linear gate: add its deg7Vec to `acc`
        let d := deg7Vec (fun x => g.op.eval ((cur x).getD g.w1 false) ((cur x).getD g.w2 false))
        have hacc' : ∀ w, InSpan (d :: acc) (deg7Vec (fun x => (cur' x).getD w false)) := by
          intro w
          by_cases hw : w < s
          · have heq : (fun x => (cur' x).getD w false) = (fun x => (cur x).getD w false) := by
              funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hw]
            rw [heq]; exact inSpan_cons_of_mem (hacc w)
          · by_cases hweq : w = s
            · have heq : (fun x => (cur' x).getD w false) =
                  (fun x => g.op.eval ((cur x).getD g.w1 false) ((cur x).getD g.w2 false)) := by
                funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hweq]
              rw [heq]; exact inSpan_cons_self d acc
            · have heq : (fun x => (cur' x).getD w false) = (fun _ => false) := by
                funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hw, hweq]
              rw [heq]
              have h0 : deg7Vec (fun _ => false) = 0 := by
                apply deg7Vec_eq_zero_of_all_false
                intro j hj
                have h7 := basisWithout_length j hj
                cases hbw : basisWithout j with
                | nil => rw [hbw] at h7; simp at h7
                | cons v vs => exact cubeSum_const false 0 v vs
              rw [h0]; exact inSpan_zero _
        rcases ih cur' (s + 1) (d :: acc) hs' hacc' with ⟨gens, hlen, hsp⟩
        refine ⟨gens, ?_, hsp⟩
        simp only [List.length_cons] at hlen
        have hnl : nlCount (g :: gs') = nlCount gs' + 1 := by unfold nlCount; simp [hg]
        omega
      · -- Linear gate: deg7Vec stays in `InSpan acc`
        have hnew : InSpan acc (deg7Vec (fun x => g.op.eval ((cur x).getD g.w1 false) ((cur x).getD g.w2 false))) := by
          rw [deg7Vec_linear_op hg]
          apply inSpan_xor
          · cases xor g.op.b00 g.op.b10
            · exact inSpan_zero acc
            · exact hacc g.w1
          · cases xor g.op.b00 g.op.b01
            · exact inSpan_zero acc
            · exact hacc g.w2
        have hacc' : ∀ w, InSpan acc (deg7Vec (fun x => (cur' x).getD w false)) := by
          intro w
          by_cases hw : w < s
          · have heq : (fun x => (cur' x).getD w false) = (fun x => (cur x).getD w false) := by
              funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hw]
            rw [heq]; exact hacc w
          · by_cases hweq : w = s
            · have heq : (fun x => (cur' x).getD w false) =
                  (fun x => g.op.eval ((cur x).getD g.w1 false) ((cur x).getD g.w2 false)) := by
                funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hweq]
              rw [heq]; exact hnew
            · have heq : (fun x => (cur' x).getD w false) = (fun _ => false) := by
                funext x; dsimp only [cur']; rw [array_getD_push, hs x]; simp [hw, hweq]
              rw [heq]
              have h0 : deg7Vec (fun _ => false) = 0 := by
                apply deg7Vec_eq_zero_of_all_false
                intro j hj
                have h7 := basisWithout_length j hj
                cases hbw : basisWithout j with
                | nil => rw [hbw] at h7; simp at h7
                | cons v vs => exact cubeSum_const false 0 v vs
              rw [h0]; exact inSpan_zero _
        rcases ih cur' (s + 1) acc hs' hacc' with ⟨gens, hlen, hsp⟩
        refine ⟨gens, ?_, hsp⟩
        have hnl : nlCount (g :: gs') = nlCount gs' := by unfold nlCount; simp [hg]
        omega
  rcases hgo suf init sz [] hsz (fun w => by rw [hinit w]; exact inSpan_zero []) with ⟨gens, hlen, hsp⟩
  exact ⟨gens, by simpa using hlen, hsp⟩

/-! ## 4. AES S-Box Full-Rank Degree-7 ANF Certificate & Counting Contradiction -/

private def aesBit (b : Nat) (x : BitVec 8) : Bool :=
  (aesSBox x).getLsbD b

private def aesDeg7List : List (BitVec 8) :=
  (List.range 8).map (fun b => deg7Vec (aesBit b))

private def unitMasks : List (BitVec 8) :=
  [0xc6#8, 0x63#8, 0xe3#8, 0xa3#8, 0x83#8, 0xc1#8, 0xb2#8, 0x0b#8]

private def xorByByte (vecs : List (BitVec 8)) (mask : BitVec 8) : BitVec 8 :=
  (List.range 8).foldl (fun acc b =>
    if mask.getLsbD b then acc ^^^ vecs.getD b 0 else acc) 0

private theorem aesDeg7_span_units :
    (List.range 8).all (fun j =>
      xorByByte aesDeg7List (unitMasks.getD j 0) == (BitVec.ofNat 8 1 <<< j)) = true := by
  decide +kernel

private theorem inSpan_xorByByte {gens : List (BitVec 8)} {vecs : List (BitVec 8)}
    (hvecs : ∀ b, b < 8 → InSpan gens (vecs.getD b 0)) (mask : BitVec 8) :
    InSpan gens (xorByByte vecs mask) := by
  unfold xorByByte
  have haux : ∀ (k : Nat) (acc : BitVec 8), k ≤ 8 → InSpan gens acc →
      InSpan gens ((List.range k).foldl (fun acc b =>
        if mask.getLsbD b then acc ^^^ vecs.getD b 0 else acc) acc) := by
    intro k
    induction k with
    | zero => intro acc _ hacc; exact hacc
    | succ k' ih =>
      intro acc hk hacc
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hprev := ih acc (by omega) hacc
      cases mask.getLsbD k'
      · exact hprev
      · exact inSpan_xor hprev (hvecs k' (by omega))
  exact haux 8 0 (Nat.le_refl 8) (inSpan_zero gens)

private theorem all_bv8_inSpan_of_units {gens : List (BitVec 8)}
    (hunits : ∀ j, j < 8 → InSpan gens (BitVec.ofNat 8 1 <<< j)) (v : BitVec 8) :
    InSpan gens v := by
  have hdecomp : v = xorByByte ((List.range 8).map (fun j => BitVec.ofNat 8 1 <<< j)) v := by
    have hcheck : ∀ v' : BitVec 8,
        v' = xorByByte ((List.range 8).map (fun j => BitVec.ofNat 8 1 <<< j)) v' := by
      decide +kernel
    exact hcheck v
  rw [hdecomp]
  apply inSpan_xorByByte
  intro b hb
  have hget : ((List.range 8).map (fun j => BitVec.ofNat 8 1 <<< j)).getD b 0 =
      BitVec.ofNat 8 1 <<< b := by
    have hcheck : ∀ b' : Fin 8,
        ((List.range 8).map (fun j => BitVec.ofNat 8 1 <<< j)).getD b'.val 0 =
        BitVec.ofNat 8 1 <<< b'.val := by
      decide +kernel
    exact hcheck ⟨b, hb⟩
  rw [hget]
  exact hunits b hb

private def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).map (false :: ·) ++ (allMasks n).map (true :: ·)

private theorem allMasks_length : ∀ n, (allMasks n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [allMasks, List.length_append, List.length_map, allMasks_length n, Nat.pow_succ]
    omega

private theorem mem_allMasks : ∀ (n : Nat) (m : List Bool), m.length = n → m ∈ allMasks n
  | 0, [], _ => List.mem_cons_self
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, b :: bs, h => by
    simp only [List.length_cons, Nat.succ.injEq] at h
    have ih := mem_allMasks n bs h
    cases b
    · exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨bs, ih, rfl⟩))
    · exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨bs, ih, rfl⟩))

private theorem mem_split {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l → ∃ p q : List α, l = p ++ x :: q
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨[], ys, rfl⟩
    · rcases mem_split h' with ⟨p, q, rfl⟩
      exact ⟨y :: p, q, rfl⟩

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

private theorem testBit_packBits : ∀ (bits : List Bool) (j : Nat),
    Nat.testBit (MultiCircuit.packBits bits) j = bits.getD j false
  | [], _ => by simp [MultiCircuit.packBits]
  | b :: bs, 0 => by
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_zero]
    cases b <;> simp [Nat.testBit_zero]
  | b :: bs, j + 1 => by
    have ih := testBit_packBits bs j
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_succ] at ih ⊢
    rw [Nat.testBit_succ]
    cases b <;> simp [Nat.mul_add_div, ih]

/-! ## 5. Main Theorem: `¬ Record 12` -/

theorem record : ¬ Crypto.Statements.CZ_rec_aes_and.Record 12 := by
  intro ⟨c, hwf, hnl, hcomp⟩
  have hout_len : c.outputs.length = 8 := by
    unfold MultiCircuit.IsWellFormed MultiCircuit.isWellFormedBool at hwf
    simp only [Bool.and_eq_true, beq_iff_eq] at hwf
    exact hwf.1.1
  -- Split `c.gates` into `pre ++ suf` with `nlCount pre ≤ 5` and `nlCount suf ≤ 7`
  rcases split_after_k_nl 5 c.gates with ⟨pre, suf, hgates, hpre_nl, hsuf_nl⟩
  have hnl_c : nlCount c.gates ≤ 12 := hnl
  have hsuf_le7 : nlCount suf ≤ 7 := by omega
  -- Every wire after `pre` has `deg7Vec = 0` by Schnorr's theorem
  have hpre_deg7 : ∀ w, deg7Vec (fun x => (MultiCircuit.evalWires x pre).getD w false) = 0 := by
    intro w
    apply deg7Vec_eq_zero_of_all_false
    intro j hj
    exact schnorr_cubeSum 5 pre w 0 (basisWithout j) hpre_nl (by rw [basisWithout_length j hj]; decide)
  -- Walk `suf` to get a generating set `gens` of size `≤ 7` spanning all output `deg7Vec`s
  have hpre_sz : ∀ x : BitVec 8, (MultiCircuit.evalWires x pre).size = 8 + pre.length := fun x => by
    rw [evalWires_eq_evalWiresFrom, evalWiresFrom_size]
    simp
  rcases deg7Vec_wires_inSpan_suffix (fun x => MultiCircuit.evalWires x pre) (8 + pre.length)
      hpre_sz hpre_deg7 suf with ⟨gens, hgens_len, hgens_span⟩
  have hgens_le7 : gens.length ≤ 7 := by omega
  -- Match each output bit `b < 8` of `c` with `aesBit b`
  have hout_eq : ∀ b, b < 8 →
      (fun x : BitVec 8 => (MultiCircuit.evalWires x c.gates).getD (c.outputs.getD b 0) false) = aesBit b := by
    intro b hb
    funext x
    have hcx : c.evalNat x = (aesSBox x).toNat := hcomp x
    have htb := congrArg (fun n => Nat.testBit n b) hcx
    unfold MultiCircuit.evalNat at htb
    rw [testBit_packBits] at htb
    have hb' : b < c.outputs.length := by omega
    have hmap : (c.outputs.map (fun w => (MultiCircuit.evalWires x c.gates).getD w false)).getD b false =
        (MultiCircuit.evalWires x c.gates).getD (c.outputs.getD b 0) false := by
      simp [List.getD_eq_getElem?_getD, hb']
    rw [hmap] at htb
    exact htb
  -- Therefore every `aesDeg7List.getD b 0` lies in `InSpan gens`
  have haes_inSpan : ∀ b, b < 8 → InSpan gens (aesDeg7List.getD b 0) := by
    intro b hb
    have hget : aesDeg7List.getD b 0 = deg7Vec (aesBit b) := by
      unfold aesDeg7List
      simp [List.getD_eq_getElem?_getD, hb]
    rw [hget, ← hout_eq b hb, hgates]
    have hfrom : (fun x => (MultiCircuit.evalWires x (pre ++ suf)).getD (c.outputs.getD b 0) false) =
        (fun x => (evalWiresFrom (fun y => MultiCircuit.evalWires y pre) suf x).getD (c.outputs.getD b 0) false) := by
      funext x
      rw [evalWires_eq_evalWiresFrom, evalWiresFrom_append]
      rfl
    rw [hfrom]
    exact hgens_span (c.outputs.getD b 0)
  -- Hence every unit vector `1 <<< j` (`j < 8`), and therefore every `v : BitVec 8`, lies in `InSpan gens`
  have hunits : ∀ j, j < 8 → InSpan gens (BitVec.ofNat 8 1 <<< j) := by
    intro j hj
    have heq := List.all_eq_true.1 aesDeg7_span_units j (List.mem_range.2 hj)
    simp only [beq_iff_eq] at heq
    rw [← heq]
    exact inSpan_xorByByte haes_inSpan (unitMasks.getD j 0)
  have hall : ∀ v : BitVec 8, InSpan gens v := all_bv8_inSpan_of_units hunits
  -- Counting contradiction: `256 ≤ |(allMasks gens.length).map (xorComb gens)| = 2^(gens.length) ≤ 128`
  let all256 : List (BitVec 8) := (List.range 256).map (BitVec.ofNat 8)
  let image : List (BitVec 8) := (allMasks gens.length).map (xorComb gens)
  have hall256_nd : all256.Nodup := by
    have hcheck : all256.Nodup ↔ true = true := by
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      unfold all256
      have hinj : ∀ a ∈ List.range 256, ∀ b ∈ List.range 256,
          BitVec.ofNat 8 a = BitVec.ofNat 8 b → a = b := by
        intro a ha b hb heq
        have ha' : a < 256 := List.mem_range.1 ha
        have hb' : b < 256 := List.mem_range.1 hb
        have hn := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat] at hn
        rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hn
        exact hn
      have hmap : ∀ (l : List Nat), l.Nodup →
          (∀ a ∈ l, ∀ b ∈ l, BitVec.ofNat 8 a = BitVec.ofNat 8 b → a = b) →
          (l.map (BitVec.ofNat 8)).Nodup := by
        intro l
        induction l with
        | nil => intro _ _; exact List.nodup_nil
        | cons x xs ih =>
          intro hnd' hinj'
          have ⟨hx, hxs⟩ := List.nodup_cons.1 hnd'
          apply List.nodup_cons.2
          refine ⟨?_, ih hxs (fun a ha b hb => hinj' a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
          intro hm
          rcases List.mem_map.1 hm with ⟨y, hy, hyx⟩
          have hxy := hinj' y (List.mem_cons_of_mem x hy) x List.mem_cons_self hyx
          subst hxy; exact hx hy
      exact hmap (List.range 256) List.nodup_range hinj
    exact hcheck.2 rfl
  have hsub : ∀ v ∈ all256, v ∈ image := by
    intro v _
    rcases hall v with ⟨m, hm, hv⟩
    exact List.mem_map.2 ⟨m, mem_allMasks gens.length m hm, hv⟩
  have hle := nodup_length_le_of_subset all256 image hall256_nd hsub
  have hlen1 : all256.length = 256 := by simp [all256]
  have hlen2 : image.length = 2 ^ gens.length := by
    simp only [image, List.length_map, allMasks_length]
  have hpow : 2 ^ gens.length ≤ 128 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hgens_le7
    omega
  omega

end Crypto.Claims.CZ_rec_aes_and_not_s12
