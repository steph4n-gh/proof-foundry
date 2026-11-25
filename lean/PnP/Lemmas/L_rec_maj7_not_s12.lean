import PnP.Core
import PnP.Statements.L_rec_maj7

namespace PnP.Lemmas.L_rec_maj7_not_s12

open PnP
open PnP.Statements.L_rec_maj7

/-!
  B2 circuit lower bound `¬ PnP.Statements.L_rec_maj7.Record 12`, certifying
  that every well-formed B2 circuit computing 7-bit Majority (`MAJ_7 = thresh 7 4`)
  requires at least 13 gates (beating both `bound_floor = 11` and `literature_lower_bound = 12`).

  Proof chain:
  `MAJ_7` (size ≤ 12) → restrict fan-out ≥ 2 input to `false` → `TH_4^6` (size ≤ 10)
                      → restrict fan-out ≥ 2 input to `true`  → `MAJ_5`  (size ≤ 8)
                      → restrict fan-out ≥ 2 input to `true`  → `TH_2^4` (size ≤ 6)
                      → restrict fan-out ≥ 2 input to `false` → 4-gate `MAJ_3` lift to `OR_3` (impossible).
-/

/-! ## 1. General Well-Formedness, `evalWires` Semantics, & Target Functions -/

private def GatesWF (n : Nat) (gs : List B2Gate) : Prop :=
  ∀ (i : Nat) (g : B2Gate), gs[i]? = some g → g.w1 < n + i ∧ g.w2 < n + i

private def WF (n : Nat) (c : B2Circuit n) : Prop :=
  c.outputWire < n + c.gates.length ∧ GatesWF n c.gates

private def ComputesUpToNeg {n : Nat} (c : B2Circuit n) (f : BoolFn n) : Prop :=
  ∃ flip : Bool, ∀ x : BoolVec n, c.eval x = xor (f x) flip

private def th24 : BoolFn 4 := thresh 4 2

private def or3 : BoolFn 3 :=
  fun x => x ⟨0, by decide⟩ || x ⟨1, by decide⟩ || x ⟨2, by decide⟩

private def evalWiresFrom (init : Array Bool) (gs : List B2Gate) : Array Bool :=
  gs.foldl (fun acc g =>
    let v1 := acc.getD g.w1 false
    let v2 := acc.getD g.w2 false
    acc.push (g.op.eval v1 v2)
  ) init

private theorem evalWires_eq_from {n : Nat} (x : BoolVec n) (gs : List B2Gate) :
    B2Circuit.evalWires x gs = evalWiresFrom (Array.ofFn (fun i : Fin n => x i)) gs := rfl

private theorem evalWiresFrom_size (init : Array Bool) (gs : List B2Gate) :
    (evalWiresFrom init gs).size = init.size + gs.length := by
  induction gs generalizing init with
  | nil => simp [evalWiresFrom]
  | cons g gs ih =>
    simp only [evalWiresFrom, List.foldl_cons] at ih ⊢
    rw [ih, Array.size_push, List.length_cons]
    omega

private theorem array_getD_push_lt (a : Array Bool) (v : Bool) (k : Nat) (hk : k < a.size) :
    (a.push v).getD k false = a.getD k false := by
  simp [Array.getD, Array.size_push, hk, Array.getElem_push_lt, Nat.lt_succ_of_lt hk]

private theorem array_getD_push_eq (a : Array Bool) (v : Bool) :
    (a.push v).getD a.size false = v := by
  simp [Array.getD, Array.size_push, Array.getElem_push_eq]

private theorem evalWiresFrom_prefix (init : Array Bool) (gs : List B2Gate)
    (k : Nat) (hk : k < init.size) :
    (evalWiresFrom init gs).getD k false = init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (evalWiresFrom (init.push _) gs).getD k false = init.getD k false
    rw [ih _ (by rw [Array.size_push]; omega)]
    exact array_getD_push_lt init _ k hk

private theorem evalWiresFrom_append (init : Array Bool) (g1 g2 : List B2Gate) :
    evalWiresFrom init (g1 ++ g2) = evalWiresFrom (evalWiresFrom init g1) g2 := by
  simp [evalWiresFrom, List.foldl_append]

private theorem evalWires_size {n : Nat} (x : BoolVec n) (gs : List B2Gate) :
    (B2Circuit.evalWires x gs).size = n + gs.length := by
  rw [evalWires_eq_from, evalWiresFrom_size, Array.size_ofFn]

private theorem evalWires_input {n : Nat} (x : BoolVec n) (gs : List B2Gate) (i : Fin n) :
    (B2Circuit.evalWires x gs).getD i.val false = x i := by
  rw [evalWires_eq_from, evalWiresFrom_prefix _ gs i.val (by rw [Array.size_ofFn]; exact i.isLt)]
  simp [Array.getD, i.isLt]

private theorem evalWires_gate {n : Nat} (x : BoolVec n) (gs : List B2Gate)
    (k : Nat) (g : B2Gate) (hk : gs[k]? = some g)
    (hwf : GatesWF n gs) :
    (B2Circuit.evalWires x gs).getD (n + k) false =
      g.op.eval ((B2Circuit.evalWires x gs).getD g.w1 false)
                ((B2Circuit.evalWires x gs).getD g.w2 false) := by
  have hklt : k < gs.length := by
    by_cases hlt : k < gs.length
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hk; cases hk
  have hsplit : gs = gs.take k ++ g :: gs.drop (k + 1) := by
    have hget : gs[k] = g := by
      have := List.getElem?_eq_getElem hklt
      rw [hk] at this
      exact Option.some.inj this.symm
    conv => lhs; rw [← List.take_append_drop k gs]
    congr 1
    rw [List.drop_eq_getElem_cons hklt, hget]
  have htakelen : (gs.take k).length = k := List.length_take_of_le (by omega)
  have hgw := hwf k g hk
  let pre := evalWiresFrom (Array.ofFn (fun i : Fin n => x i)) (gs.take k)
  have hpre_sz : pre.size = n + k := by
    dsimp only [pre]; rw [evalWiresFrom_size, Array.size_ofFn, htakelen]
  let pushed := pre.push (g.op.eval (pre.getD g.w1 false) (pre.getD g.w2 false))
  have hpushed_sz : pushed.size = n + k + 1 := by
    dsimp only [pushed]; rw [Array.size_push, hpre_sz]
  have hfull : B2Circuit.evalWires x gs = evalWiresFrom pushed (gs.drop (k + 1)) := by
    rw [evalWires_eq_from]
    conv => lhs; rw [hsplit]
    rw [evalWiresFrom_append]
    rfl
  rw [hfull]
  rw [evalWiresFrom_prefix pushed _ (n + k) (by omega)]
  rw [evalWiresFrom_prefix pushed _ g.w1 (by omega)]
  rw [evalWiresFrom_prefix pushed _ g.w2 (by omega)]
  dsimp only [pushed]
  rw [← hpre_sz, array_getD_push_eq]
  rw [array_getD_push_lt pre _ g.w1 (by omega)]
  rw [array_getD_push_lt pre _ g.w2 (by omega)]

/-! ## 2. B2Op Normalization & WireRef Compiler (`compileAux`) -/

private def b2NegOut (op : B2Op) : B2Op :=
  ⟨!op.b00, !op.b01, !op.b10, !op.b11⟩

private def b2SwapIn (op : B2Op) : B2Op :=
  ⟨op.b00, op.b10, op.b01, op.b11⟩

private theorem eval_b2SwapIn (op : B2Op) (a b : Bool) :
    (b2SwapIn op).eval a b = op.eval b a := by
  cases a <;> cases b <;> rfl

private def b2Adjust (op : B2Op) (f1 f2 swap : Bool) : B2Op :=
  let e (a b : Bool) : Bool :=
    let a' := if swap then b else a
    let b' := if swap then a else b
    op.eval (xor a' f1) (xor b' f2)
  ⟨e false false, e false true, e true false, e true true⟩

private theorem eval_b2Adjust (op : B2Op) (f1 f2 swap a b : Bool) :
    (b2Adjust op f1 f2 swap).eval a b =
      op.eval (xor (if swap then b else a) f1) (xor (if swap then a else b) f2) := by
  cases a <;> cases b <;> rfl

private theorem eval_b2NegOut (op : B2Op) (a b : Bool) :
    (b2NegOut op).eval a b = !(op.eval a b) := by
  cases a <;> cases b <;> rfl

private def opOfNat5 (k : Nat) : B2Op :=
  match k with
  | 0 => B2Op.opAnd
  | 1 => B2Op.opAndNot
  | 2 => B2Op.opNotAnd
  | 3 => B2Op.opOr
  | _ => B2Op.opXor

private def opToNat5 (op : B2Op) : Nat :=
  if op == B2Op.opAnd then 0
  else if op == B2Op.opAndNot then 1
  else if op == B2Op.opNotAnd then 2
  else if op == B2Op.opOr then 3
  else 4

private def isNorm5 (op : B2Op) : Bool :=
  op == B2Op.opAnd || op == B2Op.opAndNot || op == B2Op.opNotAnd ||
  op == B2Op.opOr || op == B2Op.opXor

private theorem opToNat5_lt (op : B2Op) : opToNat5 op < 5 := by
  unfold opToNat5
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split <;> decide

private theorem opOfNat5_toNat5 (op : B2Op) (h : (isNorm5 op) = true) :
    opOfNat5 (opToNat5 op) = op := by
  rcases op with ⟨b00, b01, b10, b11⟩
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
    simp_all [isNorm5, opOfNat5, opToNat5,
      B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor]

private theorem isNorm5_swapIn (op : B2Op) (h : (isNorm5 op) = true) :
    (isNorm5 (b2SwapIn op)) = true := by
  rcases op with ⟨b00, b01, b10, b11⟩
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
    simp_all [isNorm5, b2SwapIn,
      B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor]

private theorem isNorm5_of_genuine (op : B2Op)
    (hb00 : op.b00 = false)
    (hdep1 : !(op.b00 == op.b10 && op.b01 == op.b11))
    (hdep2 : !(op.b00 == op.b01 && op.b10 == op.b11)) :
    (isNorm5 op) = true := by
  rcases op with ⟨b00, b01, b10, b11⟩
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
    simp_all [isNorm5, B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor]

private theorem eval_norm5_false (op : B2Op) (h : (isNorm5 op) = true) :
    op.eval false false = false := by
  rcases op with ⟨b00, b01, b10, b11⟩
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
    simp_all [isNorm5, B2Op.eval, B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor]

private inductive WireRef where
  | const (b : Bool)
  | wire (w : Nat) (flip : Bool)
  deriving Repr, DecidableEq

private def evalRef (arr : Array Bool) : WireRef → Bool
  | .const b => b
  | .wire w flip => xor (arr.getD w false) flip

private def WireRef.wf (bound : Nat) : WireRef → Prop
  | .const _ => True
  | .wire w _ => w < bound

private def compileGate (n' : Nat) (outLen : Nat) (r1 r2 : WireRef) (op : B2Op) :
    Option B2Gate × WireRef :=
  match r1, r2 with
  | .const b1, .const b2 => (none, .const (op.eval b1 b2))
  | .const b1, .wire u f2 =>
    let v0 := op.eval b1 f2
    let v1 := op.eval b1 (!f2)
    if v0 == v1 then (none, .const v0) else (none, .wire u v0)
  | .wire u f1, .const b2 =>
    let v0 := op.eval f1 b2
    let v1 := op.eval (!f1) b2
    if v0 == v1 then (none, .const v0) else (none, .wire u v0)
  | .wire u1 f1, .wire u2 f2 =>
    if u1 == u2 then
      let v0 := op.eval f1 f2
      let v1 := op.eval (!f1) (!f2)
      if v0 == v1 then (none, .const v0) else (none, .wire u1 v0)
    else
      let swap := decide (u2 < u1)
      let a := if swap then u2 else u1
      let b := if swap then u1 else u2
      let op' := b2Adjust op f1 f2 swap
      if op'.b00 == op'.b10 && op'.b01 == op'.b11 then
        if op'.b00 == op'.b01 then (none, .const op'.b00)
        else (none, .wire b op'.b00)
      else if op'.b00 == op'.b01 && op'.b10 == op'.b11 then
        (none, .wire a op'.b00)
      else
        let p := op'.b00
        let opN := if p then (b2NegOut op') else op'
        (some ⟨opN, a, b⟩, .wire (n' + outLen) p)

private theorem compileGate_spec (n' outLen : Nat) (r1 r2 : WireRef) (op : B2Op)
    (hr1 : r1.wf (n' + outLen)) (hr2 : r2.wf (n' + outLen))
    (arr : Array Bool) (hsz : arr.size = n' + outLen) :
    let res := compileGate n' outLen r1 r2 op
    match res.1 with
    | none =>
      res.2.wf (n' + outLen) ∧
      evalRef arr res.2 = op.eval (evalRef arr r1) (evalRef arr r2)
    | some g =>
      g.w1 < g.w2 ∧ g.w2 < n' + outLen ∧ (isNorm5 g.op) = true ∧
      res.2.wf (n' + outLen + 1) ∧
      evalRef (arr.push (g.op.eval (arr.getD g.w1 false) (arr.getD g.w2 false))) res.2 =
        op.eval (evalRef arr r1) (evalRef arr r2) := by
  cases r1 with
  | const b1 =>
    cases r2 with
    | const b2 => exact ⟨trivial, rfl⟩
    | wire u f2 =>
      dsimp only [compileGate]
      by_cases hv : (op.eval b1 f2 == op.eval b1 (!f2)) = true
      · simp only [hv, ↓reduceIte]
        have heq : op.eval b1 f2 = op.eval b1 (!f2) := beq_iff_eq.1 hv
        refine ⟨trivial, ?_⟩
        dsimp only [evalRef]
        cases arr.getD u false <;> cases f2 <;> simp_all
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        have hne : op.eval b1 f2 ≠ op.eval b1 (!f2) := fun h => hv (beq_iff_eq.2 h)
        refine ⟨hr2, ?_⟩
        dsimp only [evalRef]
        cases arr.getD u false <;> cases f2 <;> cases h1 : op.eval b1 false <;> cases h2 : op.eval b1 true <;>
          simp_all
  | wire u1 f1 =>
    cases r2 with
    | const b2 =>
      dsimp only [compileGate]
      by_cases hv : (op.eval f1 b2 == op.eval (!f1) b2) = true
      · simp only [hv, ↓reduceIte]
        have heq : op.eval f1 b2 = op.eval (!f1) b2 := beq_iff_eq.1 hv
        refine ⟨trivial, ?_⟩
        dsimp only [evalRef]
        cases arr.getD u1 false <;> cases f1 <;> simp_all
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        have hne : op.eval f1 b2 ≠ op.eval (!f1) b2 := fun h => hv (beq_iff_eq.2 h)
        refine ⟨hr1, ?_⟩
        dsimp only [evalRef]
        cases arr.getD u1 false <;> cases f1 <;> cases h1 : op.eval false b2 <;> cases h2 : op.eval true b2 <;>
          simp_all
    | wire u2 f2 =>
      dsimp only [compileGate]
      by_cases hu : (u1 == u2) = true
      · simp only [hu, ↓reduceIte]
        have heq : u1 = u2 := beq_iff_eq.1 hu
        subst heq
        by_cases hv : (op.eval f1 f2 == op.eval (!f1) (!f2)) = true
        · simp only [hv, ↓reduceIte]
          have hveq : op.eval f1 f2 = op.eval (!f1) (!f2) := beq_iff_eq.1 hv
          refine ⟨trivial, ?_⟩
          dsimp only [evalRef]
          cases arr.getD u1 false <;> cases f1 <;> cases f2 <;> simp_all
        · simp only [hv, Bool.false_eq_true, ↓reduceIte]
          have hvne : op.eval f1 f2 ≠ op.eval (!f1) (!f2) := fun h => hv (beq_iff_eq.2 h)
          refine ⟨hr1, ?_⟩
          dsimp only [evalRef]
          rcases op with ⟨b00, b01, b10, b11⟩
          cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
            cases arr.getD u1 false <;> cases f1 <;> cases f2 <;> simp_all [B2Op.eval]
      · simp only [hu, Bool.false_eq_true, ↓reduceIte]
        have hune : u1 ≠ u2 := fun h => hu (beq_iff_eq.2 h)
        generalize hswap : decide (u2 < u1) = swap
        generalize ha : (if swap = true then u2 else u1) = a
        generalize hb : (if swap = true then u1 else u2) = b
        generalize hop' : b2Adjust op f1 f2 swap = op'
        have hab : a < b ∧ b < n' + outLen := by
          subst ha hb hswap
          by_cases hlt : u2 < u1
          · have hdt : decide (u2 < u1) = true := decide_eq_true hlt
            simp only [hdt, ↓reduceIte]; exact ⟨hlt, hr1⟩
          · have hdf : decide (u2 < u1) = false := decide_eq_false hlt
            simp only [hdf, Bool.false_eq_true, ↓reduceIte]; exact ⟨by omega, hr2⟩
        have heval_adj : op'.eval (arr.getD a false) (arr.getD b false) =
            op.eval (xor (arr.getD u1 false) f1) (xor (arr.getD u2 false) f2) := by
          subst hop' ha hb hswap
          rw [eval_b2Adjust]
          by_cases hlt : u2 < u1 <;> simp [hlt]
        by_cases hd1 : (op'.b00 == op'.b10 && op'.b01 == op'.b11) = true
        · simp only [hd1, ↓reduceIte]
          by_cases hc : (op'.b00 == op'.b01) = true
          · simp only [hc, ↓reduceIte]
            refine ⟨trivial, ?_⟩
            dsimp only [evalRef]
            rw [← heval_adj]
            rcases op' with ⟨c00, c01, c10, c11⟩
            cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;>
              cases arr.getD a false <;> cases arr.getD b false <;> simp_all [B2Op.eval]
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            refine ⟨hab.2, ?_⟩
            dsimp only [evalRef]
            rw [← heval_adj]
            rcases op' with ⟨c00, c01, c10, c11⟩
            cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;>
              cases arr.getD a false <;> cases arr.getD b false <;> simp_all [B2Op.eval]
        · simp only [hd1, Bool.false_eq_true, ↓reduceIte]
          by_cases hd2 : (op'.b00 == op'.b01 && op'.b10 == op'.b11) = true
          · simp only [hd2, ↓reduceIte]
            refine ⟨Nat.lt_trans hab.1 hab.2, ?_⟩
            dsimp only [evalRef]
            rw [← heval_adj]
            rcases op' with ⟨c00, c01, c10, c11⟩
            cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;>
              cases arr.getD a false <;> cases arr.getD b false <;> simp_all [B2Op.eval]
          · simp only [hd2, Bool.false_eq_true, ↓reduceIte]
            refine ⟨hab.1, hab.2, ?_, ?_, ?_⟩
            · cases hp : op'.b00
              · simp only [Bool.false_eq_true, ↓reduceIte]
                apply isNorm5_of_genuine op' hp
                · simp [hd1]
                · simp [hd2]
              · simp only [↓reduceIte]
                apply isNorm5_of_genuine (b2NegOut op')
                · simp [b2NegOut, hp]
                · rcases op' with ⟨c00, c01, c10, c11⟩
                  cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;> simp_all [b2NegOut]
                · rcases op' with ⟨c00, c01, c10, c11⟩
                  cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;> simp_all [b2NegOut]
            · change n' + outLen < n' + outLen + 1; omega
            · dsimp only [evalRef]
              rw [← hsz, array_getD_push_eq]
              cases hp : op'.b00
              · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
                exact heval_adj
              · simp only [↓reduceIte, eval_b2NegOut, Bool.xor_true, Bool.not_not]
                exact heval_adj

-- Notice: whenever compileGate returns `some g'`, `r1` and `r2` were `.wire u1 f1` and `.wire u2 f2`,
-- and `g'.op.eval a b = xor (op.eval (xor a' f1) (xor b' f2)) p` for ALL booleans `a, b`!
private theorem compileGate_some_props (n' outLen : Nat) (r1 r2 : WireRef) (op : B2Op)
    (g' : B2Gate) (ref : WireRef) (h : compileGate n' outLen r1 r2 op = (some g', ref)) :
    ∃ (u1 u2 : Nat) (f1 f2 p : Bool),
      r1 = .wire u1 f1 ∧ r2 = .wire u2 f2 ∧ u1 ≠ u2 ∧
      ref = .wire (n' + outLen) p ∧
      ((u1 < u2 ∧ g'.w1 = u1 ∧ g'.w2 = u2 ∧
          ∀ a b : Bool, xor (g'.op.eval a b) p = op.eval (xor a f1) (xor b f2)) ∨
       (u2 < u1 ∧ g'.w1 = u2 ∧ g'.w2 = u1 ∧
          ∀ a b : Bool, xor (g'.op.eval a b) p = op.eval (xor b f1) (xor a f2))) := by
  cases r1 with
  | const b1 =>
    cases r2 with
    | const b2 => simp [compileGate] at h
    | wire u f2 =>
      dsimp only [compileGate] at h
      split at h <;> cases h
  | wire u1 f1 =>
    cases r2 with
    | const b2 =>
      dsimp only [compileGate] at h
      split at h <;> cases h
    | wire u2 f2 =>
      dsimp only [compileGate] at h
      by_cases hu : (u1 == u2) = true
      · simp only [hu, ↓reduceIte] at h
        split at h <;> cases h
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
        have hune : u1 ≠ u2 := fun heq => hu (beq_iff_eq.2 heq)
        let swap := decide (u2 < u1)
        let a := if swap then u2 else u1
        let b := if swap then u1 else u2
        let op' := b2Adjust op f1 f2 swap
        change (if (op'.b00 == op'.b10 && op'.b01 == op'.b11) = true then
            if (op'.b00 == op'.b01) = true then (none, WireRef.const op'.b00) else (none, WireRef.wire b op'.b00)
          else if (op'.b00 == op'.b01 && op'.b10 == op'.b11) = true then (none, WireRef.wire a op'.b00)
          else (some { op := if op'.b00 = true then b2NegOut op' else op', w1 := a, w2 := b },
                WireRef.wire (n' + outLen) op'.b00)) = (some g', ref) at h
        by_cases hd1 : (op'.b00 == op'.b10 && op'.b01 == op'.b11) = true
        · simp only [hd1, ↓reduceIte] at h
          split at h <;> cases h
        · simp only [hd1, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hd2 : (op'.b00 == op'.b01 && op'.b10 == op'.b11) = true
          · simp only [hd2, ↓reduceIte] at h; cases h
          · simp only [hd2, Bool.false_eq_true, ↓reduceIte] at h
            cases h
            refine ⟨u1, u2, f1, f2, op'.b00, rfl, rfl, hune, rfl, ?_⟩
            have heval : ∀ x y : Bool,
                xor ((if op'.b00 then (b2NegOut op') else op').eval x y) op'.b00 = op'.eval x y := by
              intro x y
              cases hp : op'.b00
              · simp
              · simp [eval_b2NegOut]
            by_cases hlt : u2 < u1
            · right
              have hsw : swap = true := by simp [swap, hlt]
              refine ⟨hlt, by simp [a, hsw], by simp [b, hsw], ?_⟩
              intro x y
              rw [heval x y]
              dsimp only [op']
              rw [eval_b2Adjust, hsw]
              simp
            · left
              have hsw : swap = false := by simp [swap, hlt]
              refine ⟨by omega, by simp [a, hsw], by simp [b, hsw], ?_⟩
              intro x y
              rw [heval x y]
              dsimp only [op']
              rw [eval_b2Adjust, hsw]
              simp

private def compileAux (n' : Nat) :
    List B2Gate → List WireRef → List Bool → List B2Gate → List B2Gate × List WireRef × List Bool
  | out, wmap, dropped, [] => (out, wmap, dropped)
  | out, wmap, dropped, g :: gs =>
    let r1 := wmap.getD g.w1 (.const false)
    let r2 := wmap.getD g.w2 (.const false)
    let (mg, ref) := compileGate n' out.length r1 r2 g.op
    match mg with
    | none => compileAux n' out (wmap ++ [ref]) (dropped ++ [true]) gs
    | some g' => compileAux n' (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false]) gs

private def IsNormGates (n : Nat) (gs : List B2Gate) : Prop :=
  ∀ (i : Nat) (g : B2Gate), gs[i]? = some g →
    g.w1 < g.w2 ∧ g.w2 < n + i ∧ (isNorm5 g.op) = true

private theorem isNormGates_wf {n : Nat} {gs : List B2Gate} (h : IsNormGates n gs) :
    GatesWF n gs := by
  intro i g hgi
  obtain ⟨h1, h2, _⟩ := h i g hgi
  exact ⟨by omega, h2⟩

private theorem list_getD_append_lt {α : Type} (l1 l2 : List α) (d : α) (k : Nat) (hk : k < l1.length) :
    (l1 ++ l2).getD k d = l1.getD k d := by
  simp only [List.getD, List.getElem?_append_left hk]

private theorem list_getD_append_eq {α : Type} (l1 : List α) (v d : α) :
    (l1 ++ [v]).getD l1.length d = v := by
  simp [List.getD]

private theorem wireRef_wf_mono {b1 b2 : Nat} (h : b1 ≤ b2) {r : WireRef} (hr : r.wf b1) :
    r.wf b2 := by
  cases r with
  | const _ => trivial
  | wire w _ => dsimp only [WireRef.wf] at hr ⊢; omega

private theorem countFalse_append (l1 l2 : List Bool) :
    (l1 ++ l2).count false = l1.count false + l2.count false := by
  simp [List.count_append]

private theorem compileAux_inv (n n' : Nat) (x : BoolVec n) (x' : BoolVec n') :
    ∀ (pre gs : List B2Gate) (out : List B2Gate) (wmap : List WireRef) (dropped : List Bool),
      GatesWF n (pre ++ gs) →
      IsNormGates n' out →
      wmap.length = n + pre.length →
      dropped.length = pre.length →
      out.length = dropped.count false →
      (∀ k, k < wmap.length → (wmap.getD k (.const false)).wf (n' + out.length)) →
      (∀ k, k < wmap.length →
        evalRef (B2Circuit.evalWires x' out) (wmap.getD k (.const false)) =
          (B2Circuit.evalWires x pre).getD k false) →
      let res := compileAux n' out wmap dropped gs
      let out' := res.1
      let wmap' := res.2.1
      let dropped' := res.2.2
      IsNormGates n' out' ∧
      wmap'.length = n + (pre ++ gs).length ∧
      dropped'.length = (pre ++ gs).length ∧
      out'.length = dropped'.count false ∧
      (∀ k, k < wmap.length → wmap'.getD k (.const false) = wmap.getD k (.const false)) ∧
      (∀ k, k < dropped.length → dropped'.getD k false = dropped.getD k false) ∧
      (∀ k, k < wmap'.length → (wmap'.getD k (.const false)).wf (n' + out'.length)) ∧
      (∀ k, k < wmap'.length →
        evalRef (B2Circuit.evalWires x' out') (wmap'.getD k (.const false)) =
          (B2Circuit.evalWires x (pre ++ gs)).getD k false)
  | pre, [], out, wmap, dropped, _, hnorm, hwlen, hdlen, houtlen, hwwf, hweval => by
    dsimp only [compileAux]
    rw [List.append_nil]
    exact ⟨hnorm, hwlen, hdlen, houtlen, fun _ _ => rfl, fun _ _ => rfl, hwwf, hweval⟩
  | pre, g :: gs, out, wmap, dropped, hwf, hnorm, hwlen, hdlen, houtlen, hwwf, hweval => by
    have hg_at : (pre ++ g :: gs)[pre.length]? = some g := by simp
    have hgw := hwf pre.length g hg_at
    have hr1_wf : (wmap.getD g.w1 (.const false)).wf (n' + out.length) := hwwf g.w1 (by omega)
    have hr2_wf : (wmap.getD g.w2 (.const false)).wf (n' + out.length) := hwwf g.w2 (by omega)
    have hspec := compileGate_spec n' out.length (wmap.getD g.w1 (.const false))
      (wmap.getD g.w2 (.const false)) g.op hr1_wf hr2_wf (B2Circuit.evalWires x' out)
      (evalWires_size x' out)
    have hpre_step : pre ++ g :: gs = (pre ++ [g]) ++ gs := by simp [List.append_assoc]
    have hstep_val : ∀ k, k < n + pre.length →
        (B2Circuit.evalWires x (pre ++ [g])).getD k false = (B2Circuit.evalWires x pre).getD k false := by
      intro k hk
      rw [evalWires_eq_from, evalWiresFrom_append]
      exact evalWiresFrom_prefix _ [g] k (by rw [evalWiresFrom_size, Array.size_ofFn]; exact hk)
    have hnew_val : (B2Circuit.evalWires x (pre ++ [g])).getD (n + pre.length) false =
        g.op.eval ((B2Circuit.evalWires x pre).getD g.w1 false)
                  ((B2Circuit.evalWires x pre).getD g.w2 false) := by
      rw [evalWires_eq_from, evalWiresFrom_append]
      change (evalWiresFrom (B2Circuit.evalWires x pre) [g]).getD (n + pre.length) false = _
      unfold evalWiresFrom
      simp only [List.foldl_cons, List.foldl_nil]
      rw [← evalWires_size x pre, array_getD_push_eq]
    have hwf_next : GatesWF n ((pre ++ [g]) ++ gs) := hpre_step ▸ hwf
    simp only [compileAux]
    cases hcg : compileGate n' out.length (wmap.getD g.w1 (.const false))
        (wmap.getD g.w2 (.const false)) g.op with
    | mk mg ref =>
      rw [hcg] at hspec
      cases mg with
      | none =>
        rcases hspec with ⟨href_wf, href_eval⟩
        have hih := compileAux_inv n n' x x' (pre ++ [g]) gs out (wmap ++ [ref]) (dropped ++ [true])
          hwf_next hnorm
          (by simp [hwlen]; omega)
          (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen])
          (by
            intro k hk
            simp only [List.length_append, List.length_singleton] at hk
            by_cases hlt : k < wmap.length
            · rw [list_getD_append_lt _ _ _ k hlt]; exact hwwf k hlt
            · have heq : k = wmap.length := by omega
              subst heq; rw [list_getD_append_eq]; exact href_wf)
          (by
            intro k hk
            simp only [List.length_append, List.length_singleton] at hk
            by_cases hlt : k < wmap.length
            · rw [list_getD_append_lt _ _ _ k hlt, hweval k hlt, hstep_val k (by omega)]
            · have heq : k = wmap.length := by omega
              subst heq; rw [list_getD_append_eq, href_eval, hwlen, hnew_val,
                hweval g.w1 (by omega), hweval g.w2 (by omega)])
        rcases hih with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
        rw [← hpre_step] at a2 a3 a8
        refine ⟨a1, a2, a3, a4, ?_, ?_, a7, a8⟩
        · intro k hk
          rw [a5 k (by simp; omega), list_getD_append_lt _ _ _ k hk]
        · intro k hk
          rw [a6 k (by simp; omega), list_getD_append_lt _ _ _ k hk]
      | some g' =>
        rcases hspec with ⟨hg1, hg2, hgnorm, href_wf, href_eval⟩
        have hnorm' : IsNormGates n' (out ++ [g']) := by
          intro i gi hgi
          by_cases hlt : i < out.length
          · rw [List.getElem?_append_left hlt] at hgi
            exact hnorm i gi hgi
          · have heq : i = out.length := by
              have : i < (out ++ [g']).length := by
                by_cases hlt2 : i < (out ++ [g']).length
                · exact hlt2
                · rw [List.getElem?_eq_none (by omega)] at hgi; cases hgi
              simp at this; omega
            subst heq
            simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem?_cons_zero] at hgi
            cases hgi
            exact ⟨hg1, hg2, hgnorm⟩
        have hout_push : B2Circuit.evalWires x' (out ++ [g']) =
            (B2Circuit.evalWires x' out).push
              (g'.op.eval ((B2Circuit.evalWires x' out).getD g'.w1 false)
                          ((B2Circuit.evalWires x' out).getD g'.w2 false)) := by
          rw [evalWires_eq_from, evalWiresFrom_append]
          rfl
        have hih := compileAux_inv n n' x x' (pre ++ [g]) gs (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false])
          hwf_next hnorm'
          (by simp [hwlen]; omega)
          (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen])
          (by
            intro k hk
            simp only [List.length_append, List.length_singleton] at hk ⊢
            by_cases hlt : k < wmap.length
            · rw [list_getD_append_lt _ _ _ k hlt]
              exact wireRef_wf_mono (by omega) (hwwf k hlt)
            · have heq : k = wmap.length := by omega
              subst heq; rw [list_getD_append_eq]
              exact wireRef_wf_mono (by omega) href_wf)
          (by
            intro k hk
            simp only [List.length_append, List.length_singleton] at hk
            by_cases hlt : k < wmap.length
            · rw [list_getD_append_lt _ _ _ k hlt, hout_push]
              have hwf_k := hwwf k hlt
              have hev_eq : ∀ v : Bool, evalRef ((B2Circuit.evalWires x' out).push v) (wmap.getD k (.const false)) =
                            evalRef (B2Circuit.evalWires x' out) (wmap.getD k (.const false)) := by
                intro v
                cases hwk : wmap.getD k (.const false) with
                | const b => rfl
                | wire w fl =>
                  rw [hwk] at hwf_k
                  dsimp only [evalRef]
                  rw [array_getD_push_lt _ v w (by rw [evalWires_size]; exact hwf_k)]
              rw [hev_eq _, hweval k hlt, hstep_val k (by omega)]
            · have heq : k = wmap.length := by omega
              subst heq
              rw [list_getD_append_eq, hout_push, href_eval, hwlen, hnew_val,
                hweval g.w1 (by omega), hweval g.w2 (by omega)])
        rcases hih with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
        rw [← hpre_step] at a2 a3 a8
        refine ⟨a1, a2, a3, a4, ?_, ?_, a7, a8⟩
        · intro k hk
          rw [a5 k (by simp; omega), list_getD_append_lt _ _ _ k hk]
        · intro k hk
          rw [a6 k (by simp; omega), list_getD_append_lt _ _ _ k hk]

-- Helper: step-level properties of compileAux (independent of x, x')
private theorem compileAux_step_props (n n' : Nat) :
    ∀ (pre gs : List B2Gate) (out : List B2Gate) (wmap : List WireRef) (dropped : List Bool),
      GatesWF n (pre ++ gs) →
      wmap.length = n + pre.length →
      dropped.length = pre.length →
      out.length = dropped.count false →
      (∀ i g, pre[i]? = some g →
        (∀ b, wmap.getD g.w1 (.const false) = .const b → dropped.getD i false = true) ∧
        (∀ b, wmap.getD g.w2 (.const false) = .const b → dropped.getD i false = true)) →
      let res := compileAux n' out wmap dropped gs
      let out' := res.1
      let wmap' := res.2.1
      let dropped' := res.2.2
      (∀ k, k < wmap.length → wmap'.getD k (.const false) = wmap.getD k (.const false)) ∧
      (∀ k, k < dropped.length → dropped'.getD k false = dropped.getD k false) ∧
      (∀ i g, (pre ++ gs)[i]? = some g →
        (∀ b, wmap'.getD g.w1 (.const false) = .const b → dropped'.getD i false = true) ∧
        (∀ b, wmap'.getD g.w2 (.const false) = .const b → dropped'.getD i false = true))
  | pre, [], out, wmap, dropped, _, _, _, _, hprev => by
    dsimp only [compileAux]
    rw [List.append_nil]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, hprev⟩
  | pre, g :: gs, out, wmap, dropped, hwf, hwlen, hdlen, houtlen, hprev => by
    have hg_at : (pre ++ g :: gs)[pre.length]? = some g := by simp
    have hgw := hwf pre.length g hg_at
    have hpre_step : pre ++ g :: gs = (pre ++ [g]) ++ gs := by simp [List.append_assoc]
    have hwf_next : GatesWF n ((pre ++ [g]) ++ gs) := hpre_step ▸ hwf
    simp only [compileAux]
    cases hcg : compileGate n' out.length (wmap.getD g.w1 (.const false))
        (wmap.getD g.w2 (.const false)) g.op with
    | mk mg ref =>
      cases mg with
      | none =>
        have hprev' : ∀ i gi, (pre ++ [g])[i]? = some gi →
            (∀ b, (wmap ++ [ref]).getD gi.w1 (.const false) = .const b → (dropped ++ [true]).getD i false = true) ∧
            (∀ b, (wmap ++ [ref]).getD gi.w2 (.const false) = .const b → (dropped ++ [true]).getD i false = true) := by
          intro i gi hgi
          by_cases hlt : i < pre.length
          · rw [List.getElem?_append_left hlt] at hgi
            have hgi_wf := hwf i gi (by rw [List.getElem?_append_left hlt]; exact hgi)
            rw [list_getD_append_lt _ _ _ gi.w1 (by omega),
                list_getD_append_lt _ _ _ gi.w2 (by omega),
                list_getD_append_lt _ _ _ i (by omega)]
            exact hprev i gi hgi
          · have heq : i = pre.length := by
              by_cases hle : i < (pre ++ [g]).length
              · simp at hle; omega
              · rw [List.getElem?_eq_none (by omega)] at hgi; cases hgi
            subst heq
            rw [← hdlen, list_getD_append_eq]
            exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        have hih := compileAux_step_props n n' (pre ++ [g]) gs out (wmap ++ [ref]) (dropped ++ [true])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) hprev'
        rcases hih with ⟨a1, a2, a3⟩
        rw [← hpre_step] at a3
        exact ⟨fun k hk => by rw [a1 k (by simp; omega), list_getD_append_lt _ _ _ k hk],
               fun k hk => by rw [a2 k (by simp; omega), list_getD_append_lt _ _ _ k hk], a3⟩
      | some g' =>
        have hnc := compileGate_some_props n' out.length _ _ _ g' ref hcg
        rcases hnc with ⟨u1, u2, f1, f2, p, hr1, hr2, _, _, _⟩
        have hprev' : ∀ i gi, (pre ++ [g])[i]? = some gi →
            (∀ b, (wmap ++ [ref]).getD gi.w1 (.const false) = .const b → (dropped ++ [false]).getD i false = true) ∧
            (∀ b, (wmap ++ [ref]).getD gi.w2 (.const false) = .const b → (dropped ++ [false]).getD i false = true) := by
          intro i gi hgi
          by_cases hlt : i < pre.length
          · rw [List.getElem?_append_left hlt] at hgi
            have hgi_wf := hwf i gi (by rw [List.getElem?_append_left hlt]; exact hgi)
            rw [list_getD_append_lt _ _ _ gi.w1 (by omega),
                list_getD_append_lt _ _ _ gi.w2 (by omega),
                list_getD_append_lt _ _ _ i (by omega)]
            exact hprev i gi hgi
          · have heq : i = pre.length := by
              by_cases hle : i < (pre ++ [g]).length
              · simp at hle; omega
              · rw [List.getElem?_eq_none (by omega)] at hgi; cases hgi
            subst heq
            simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem?_cons_zero, Option.some.injEq] at hgi
            subst hgi
            rw [list_getD_append_lt _ _ _ g.w1 (by omega),
                list_getD_append_lt _ _ _ g.w2 (by omega), hr1, hr2]
            constructor
            · intro _ h; cases h
            · intro _ h; cases h
        have hih := compileAux_step_props n n' (pre ++ [g]) gs (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) hprev'
        rcases hih with ⟨a1, a2, a3⟩
        rw [← hpre_step] at a3
        exact ⟨fun k hk => by rw [a1 k (by simp; omega), list_getD_append_lt _ _ _ k hk],
               fun k hk => by rw [a2 k (by simp; omega), list_getD_append_lt _ _ _ k hk], a3⟩

private theorem count_false_le_len (l : List Bool) : l.count false ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons b bs ih => cases b <;> simp <;> omega

private theorem count_false_le_of_one_true (l : List Bool) (i : Nat) (hi : i < l.length)
    (ht : l.getD i false = true) : l.count false + 1 ≤ l.length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at ht
      subst ht
      have := count_false_le_len bs
      simp; omega
    | succ i' =>
      simp only [List.getD_cons_succ] at ht
      have := ih i' (by simp at hi; omega) ht
      cases b <;> simp <;> omega

private theorem count_false_le_of_two_true (l : List Bool) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j)
    (hti : l.getD i false = true) (htj : l.getD j false = true) :
    l.count false + 2 ≤ l.length := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j' =>
        simp only [List.getD_cons_zero] at hti
        simp only [List.getD_cons_succ] at htj
        subst hti
        have := count_false_le_of_one_true bs j' (by simp at hj; omega) htj
        simp; omega
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getD_cons_succ] at hti
        simp only [List.getD_cons_zero] at htj
        subst htj
        have := count_false_le_of_one_true bs i' (by simp at hi; omega) hti
        simp; omega
      | succ j' =>
        simp only [List.getD_cons_succ] at hti htj
        have := ih i' j' (by simp at hi; omega) (by simp at hj; omega) (by omega) hti htj
        cases b <;> simp <;> omega

private theorem count_false_le_of_three_true (l : List Bool) (i j k : Nat)
    (hi : i < l.length) (hj : j < l.length) (hk : k < l.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hti : l.getD i false = true) (htj : l.getD j false = true) (htk : l.getD k false = true) :
    l.count false + 3 ≤ l.length := by
  induction l generalizing i j k with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j' =>
        cases k with
        | zero => exact absurd rfl hik
        | succ k' =>
          simp only [List.getD_cons_zero] at hti
          simp only [List.getD_cons_succ] at htj htk
          subst hti
          have := count_false_le_of_two_true bs j' k' (by simp at hj; omega) (by simp at hk; omega) (by omega) htj htk
          simp; omega
    | succ i' =>
      cases j with
      | zero =>
        cases k with
        | zero => exact absurd rfl hjk
        | succ k' =>
          simp only [List.getD_cons_zero] at htj
          simp only [List.getD_cons_succ] at hti htk
          subst htj
          have := count_false_le_of_two_true bs i' k' (by simp at hi; omega) (by simp at hk; omega) (by omega) hti htk
          simp; omega
      | succ j' =>
        cases k with
        | zero =>
          simp only [List.getD_cons_zero] at htk
          simp only [List.getD_cons_succ] at hti htj
          subst htk
          have := count_false_le_of_two_true bs i' j' (by simp at hi; omega) (by simp at hj; omega) (by omega) hti htj
          simp; omega
        | succ k' =>
          simp only [List.getD_cons_succ] at hti htj htk
          have := ih i' j' k' (by simp at hi; omega) (by simp at hj; omega) (by simp at hk; omega)
            (by omega) (by omega) (by omega) hti htj htk
          cases b <;> simp <;> omega

/-! ## 3. Unused-Gate Deletion & Minimal Normalized Circuits -/

private def IsNonTrivial {n : Nat} (f : BoolFn n) : Prop :=
  (∀ b : Bool, ∃ x : BoolVec n, f x ≠ b) ∧
  (∀ (i : Fin n) (b : Bool), ∃ x : BoolVec n, f x ≠ xor (x i) b)

private def UsedAfter (n : Nat) (gs : List B2Gate) (w : Nat) : Prop :=
  ∃ (j : Nat) (g : B2Gate), gs[j]? = some g ∧ (g.w1 = w ∨ g.w2 = w)

private def remapDel (cut w : Nat) : Nat :=
  if w < cut then w else w - 1

private def deleteGate (n : Nat) (c : B2Circuit n) (k : Nat) : B2Circuit n :=
  let cut := n + k
  let remapG (g : B2Gate) : B2Gate := ⟨g.op, remapDel cut g.w1, remapDel cut g.w2⟩
  ⟨c.gates.take k ++ (c.gates.drop (k + 1)).map remapG, remapDel cut c.outputWire⟩

private theorem deleteGate_props {n : Nat} (c : B2Circuit n) (k : Nat)
    (hwf : WF n c) (hk : k < c.gates.length)
    (hout : c.outputWire ≠ n + k)
    (hunused : ∀ (j : Nat) (g : B2Gate), c.gates[j]? = some g → g.w1 ≠ n + k ∧ g.w2 ≠ n + k) :
    let c' := deleteGate n c k
    WF n c' ∧ c'.size + 1 = c.size ∧ ∀ x : BoolVec n, c'.eval x = c.eval x := by
  let cut := n + k
  let c' := deleteGate n c k
  have htakelen : (c.gates.take k).length = k := List.length_take_of_le (by omega)
  have hdroplen : (c.gates.drop (k + 1)).length = c.gates.length - (k + 1) := List.length_drop
  have hlen' : c'.gates.length + 1 = c.gates.length := by
    dsimp only [c', deleteGate]
    rw [List.length_append, List.length_map, htakelen, hdroplen]
    omega
  have hwf' : WF n c' := by
    constructor
    · change remapDel cut c.outputWire < n + c'.gates.length
      dsimp only [remapDel, cut]
      have h1 := hwf.1
      split <;> omega
    · intro i g hgi
      dsimp only [c', deleteGate] at hgi
      by_cases hlt : i < k
      · rw [List.getElem?_append_left (by rw [htakelen]; exact hlt),
            List.getElem?_take_of_lt hlt] at hgi
        exact hwf.2 i g hgi
      · rw [List.getElem?_append_right (by rw [htakelen]; omega), htakelen,
            List.getElem?_map, List.getElem?_drop] at hgi
        cases horig : c.gates[k + 1 + (i - k)]? with
        | none => rw [horig] at hgi; cases hgi
        | some g0 =>
          rw [horig] at hgi; simp only [Option.map_some, Option.some.injEq] at hgi
          subst hgi
          have h0 := hwf.2 (k + 1 + (i - k)) g0 horig
          have hu := hunused (k + 1 + (i - k)) g0 horig
          dsimp only [remapDel]
          constructor <;> split <;> omega
  have heval_w : ∀ (x : BoolVec n) (w : Nat), w < n + c.gates.length → w ≠ n + k →
      (B2Circuit.evalWires x c'.gates).getD (remapDel cut w) false =
        (B2Circuit.evalWires x c.gates).getD w false := by
    intro x w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hne
      by_cases hlt : w < n
      · have hrm : remapDel cut w = w := by dsimp only [remapDel, cut]; split <;> omega
        rw [hrm]
        exact (evalWires_input x c'.gates ⟨w, hlt⟩).trans (evalWires_input x c.gates ⟨w, hlt⟩).symm
      · let i := w - n
        have hwi : w = n + i := by omega
        have hilt : i < c.gates.length := by omega
        have hgi : c.gates[i]? = some (c.gates[i]) := List.getElem?_eq_getElem hilt
        have hgwf := hwf.2 i (c.gates[i]) hgi
        have hu := hunused i (c.gates[i]) hgi
        rw [hwi, evalWires_gate x c.gates i (c.gates[i]) hgi hwf.2]
        by_cases hik : i < k
        · have hrm : remapDel cut (n + i) = n + i := by dsimp only [remapDel, cut]; split <;> omega
          have hgi' : c'.gates[i]? = some (c.gates[i]) := by
            dsimp only [c', deleteGate]
            rw [List.getElem?_append_left (by rw [htakelen]; exact hik), List.getElem?_take_of_lt hik]
            exact hgi
          rw [hrm, evalWires_gate x c'.gates i (c.gates[i]) hgi' hwf'.2]
          have h1 := ih (c.gates[i]).w1 (by omega) (by omega) hu.1
          have h2 := ih (c.gates[i]).w2 (by omega) (by omega) hu.2
          have hrm1 : remapDel cut (c.gates[i]).w1 = (c.gates[i]).w1 := by
            dsimp only [remapDel, cut]; split <;> omega
          have hrm2 : remapDel cut (c.gates[i]).w2 = (c.gates[i]).w2 := by
            dsimp only [remapDel, cut]; split <;> omega
          rw [hrm1] at h1; rw [hrm2] at h2
          rw [h1, h2]
        · have hik' : k < i := by omega
          have hrm : remapDel cut (n + i) = n + (i - 1) := by dsimp only [remapDel, cut]; split <;> omega
          have hgi' : c'.gates[i - 1]? = some ⟨(c.gates[i]).op, remapDel cut (c.gates[i]).w1, remapDel cut (c.gates[i]).w2⟩ := by
            dsimp only [c', deleteGate]
            rw [List.getElem?_append_right (by rw [htakelen]; omega), htakelen,
                List.getElem?_map, List.getElem?_drop]
            have hidx : k + 1 + (i - 1 - k) = i := by omega
            rw [hidx, hgi]; rfl
          rw [hrm, evalWires_gate x c'.gates (i - 1) _ hgi' hwf'.2]
          have h1 := ih (c.gates[i]).w1 (by omega) (by omega) hu.1
          have h2 := ih (c.gates[i]).w2 (by omega) (by omega) hu.2
          rw [h1, h2]
  refine ⟨hwf', hlen', fun x => ?_⟩
  exact heval_w x c.outputWire hwf.1 hout

private def idMap (n : Nat) : List WireRef :=
  (List.range n).map (fun i => .wire i false)

private theorem idMap_length (n : Nat) : (idMap n).length = n := by
  simp [idMap]

private theorem idMap_getD (n k : Nat) (hk : k < n) :
    (idMap n).getD k (.const false) = .wire k false := by
  simp [idMap, List.getD, List.getElem?_map, List.getElem?_range hk]

-- Normalize any WF circuit computing a non-trivial function f up to negation
private theorem normalize_circuit {n : Nat} {f : BoolFn n} (hf : IsNonTrivial f)
    (c : B2Circuit n) (hwf : WF n c) (hcomp : ComputesUpToNeg c f) :
    ∃ c' : B2Circuit n, WF n c' ∧ IsNormGates n c'.gates ∧ c'.size ≤ c.size ∧ ComputesUpToNeg c' f := by
  let res := compileAux n [] (idMap n) [] c.gates
  let out := res.1
  let wmap := res.2.1
  let dropped := res.2.2
  have hprops : ∀ x : BoolVec n,
      IsNormGates n out ∧ wmap.length = n + c.gates.length ∧
      dropped.length = c.gates.length ∧ out.length = dropped.count false ∧
      (∀ k, k < wmap.length → (wmap.getD k (.const false)).wf (n + out.length)) ∧
      (∀ k, k < wmap.length →
        evalRef (B2Circuit.evalWires x out) (wmap.getD k (.const false)) =
          (B2Circuit.evalWires x c.gates).getD k false) := by
    intro x
    have h := compileAux_inv n n x x [] c.gates [] (idMap n) []
      hwf.2 (fun _ _ h => by cases h)
      (by simp [idMap_length]) rfl rfl
      (by intro k hk; rw [idMap_length] at hk; rw [idMap_getD n k hk]; exact hk)
      (by
        intro k hk; rw [idMap_length] at hk; rw [idMap_getD n k hk]
        dsimp only [evalRef]
        rw [evalWires_input x [] ⟨k, hk⟩, Bool.xor_false])
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  obtain ⟨hnorm, hwlen, hdlen, houtlen, hwwf, _⟩ := hprops (fun _ => false)
  have hout_wf := hwf.1
  rcases hcomp with ⟨flip, hflip⟩
  cases houtref : wmap.getD c.outputWire (.const false) with
  | const b =>
    exfalso
    obtain ⟨x0, hx0⟩ := hf.1 (xor b flip)
    have hev := (hprops x0).2.2.2.2.2 c.outputWire (by omega)
    rw [houtref] at hev
    have hc := hflip x0
    dsimp only [B2Circuit.eval] at hc
    rw [← hev] at hc
    dsimp only [evalRef] at hc
    cases b <;> cases flip <;> cases hf0 : f x0 <;> rw [hf0] at hc hx0 <;> simp at hc hx0
  | wire w p =>
    have hw_lt : w < n + out.length := by
      have := hwwf c.outputWire (by omega)
      rw [houtref] at this
      exact this
    refine ⟨⟨out, w⟩, ⟨hw_lt, isNormGates_wf hnorm⟩, hnorm, ?_, xor flip p, ?_⟩
    · change out.length ≤ c.gates.length
      have := count_false_le_len dropped
      omega
    · intro x
      have hev := (hprops x).2.2.2.2.2 c.outputWire (by omega)
      rw [houtref] at hev
      have hc := hflip x
      dsimp only [B2Circuit.eval, evalRef] at hc hev ⊢
      rw [← hev] at hc
      cases hv : (B2Circuit.evalWires x out).getD w false <;> rw [hv] at hc <;>
        cases p <;> cases hfx : f x <;> rw [hfx] at hc <;> cases flip <;> simp at hc ⊢

-- Existence of a minimal normalized circuit with no unused non-output gates and outputWire = n + size - 1
private theorem exists_minimal_norm {n : Nat} {f : BoolFn n} (hf : IsNonTrivial f)
    {S : Nat} (hex : ∃ c : B2Circuit n, WF n c ∧ c.size ≤ S ∧ ComputesUpToNeg c f) :
    ∃ c : B2Circuit n,
      WF n c ∧ IsNormGates n c.gates ∧ c.size ≤ S ∧ 1 ≤ c.size ∧
      c.outputWire = n + (c.size - 1) ∧
      ComputesUpToNeg c f ∧
      (∀ c' : B2Circuit n, WF n c' → ComputesUpToNeg c' f → c.size ≤ c'.size) ∧
      (∀ k, k + 1 < c.size → UsedAfter n c.gates (n + k)) := by
  -- Find minimal size m <= S via strong induction on S
  have hmin : ∃ m, m ≤ S ∧
      (∃ c : B2Circuit n, WF n c ∧ c.size = m ∧ ComputesUpToNeg c f) ∧
      (∀ c' : B2Circuit n, WF n c' → ComputesUpToNeg c' f → m ≤ c'.size) := by
    induction S with
    | zero =>
      rcases hex with ⟨c, hwf, hsz, hcomp⟩
      exact ⟨0, Nat.le_refl 0, ⟨c, hwf, by omega, hcomp⟩, fun _ _ _ => Nat.zero_le _⟩
    | succ S' ih =>
      by_cases hle : ∃ c : B2Circuit n, WF n c ∧ c.size ≤ S' ∧ ComputesUpToNeg c f
      · obtain ⟨m, hm, hc, hbest⟩ := ih hle
        exact ⟨m, by omega, hc, hbest⟩
      · rcases hex with ⟨c, hwf, hsz, hcomp⟩
        have heq : c.size = S' + 1 := by
          by_cases hlt : c.size ≤ S'
          · exact absurd ⟨c, hwf, hlt, hcomp⟩ hle
          · omega
        refine ⟨S' + 1, Nat.le_refl _, ⟨c, hwf, heq, hcomp⟩, ?_⟩
        intro c' hwf' hcomp'
        by_cases hlt : c'.size ≤ S'
        · exact absurd ⟨c', hwf', hlt, hcomp'⟩ hle
        · omega
  obtain ⟨m, hmS, ⟨c0, hwf0, hsz0, hcomp0⟩, hbest⟩ := hmin
  obtain ⟨c, hwf, hnorm, hle, hcomp⟩ := normalize_circuit hf c0 hwf0 hcomp0
  have hsz : c.size = m := by
    have := hbest c hwf hcomp
    omega
  have hpos : 1 ≤ c.size := by
    cases hgs : c.gates with
    | nil =>
      exfalso
      have hout : c.outputWire < n := by have := hwf.1; rw [hgs] at this; simp at this; exact this
      rcases hcomp with ⟨flip, hflip⟩
      obtain ⟨x0, hx0⟩ := hf.2 ⟨c.outputWire, hout⟩ flip
      have hc := hflip x0
      dsimp only [B2Circuit.eval] at hc
      rw [hgs, evalWires_input x0 [] ⟨c.outputWire, hout⟩] at hc
      cases x0 ⟨c.outputWire, hout⟩ <;> cases flip <;> cases f x0 <;> simp_all
    | cons _ _ => simp [B2Circuit.size, hgs]
  have hunused_contra : ∀ k, k < c.gates.length → c.outputWire ≠ n + k →
      ¬ (∀ (j : Nat) (g : B2Gate), c.gates[j]? = some g → g.w1 ≠ n + k ∧ g.w2 ≠ n + k) := by
    intro k hk hne hall
    obtain ⟨hwf', hlen', heval'⟩ := deleteGate_props c k hwf hk hne hall
    have hcomp' : ComputesUpToNeg (deleteGate n c k) f := by
      rcases hcomp with ⟨flip, hflip⟩
      exact ⟨flip, fun x => (heval' x).trans (hflip x)⟩
    have hge := hbest (deleteGate n c k) hwf' hcomp'
    omega
  have hout_eq : c.outputWire = n + (c.size - 1) := by
    by_cases heq : c.outputWire = n + (c.size - 1)
    · exact heq
    · exfalso
      apply hunused_contra (c.size - 1) (by dsimp only [B2Circuit.size] at hpos ⊢; omega) heq
      intro j g hgj
      have hgw := hwf.2 j g hgj
      have hjlt : j < c.gates.length := by
        by_cases hlt : j < c.gates.length
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hgj; cases hgj
      dsimp only [B2Circuit.size]
      omega
  have hused : ∀ k, k + 1 < c.size → UsedAfter n c.gates (n + k) := by
    intro k hk
    have hnot := hunused_contra k (by dsimp only [B2Circuit.size] at hk; omega) (by rw [hout_eq]; omega)
    -- Use finite decidability over j < c.gates.length
    have hex : (List.range c.gates.length).any (fun j =>
        match c.gates[j]? with
        | none => false
        | some g => (g.w1 == n + k) || (g.w2 == n + k)) = true := by
      cases ha : (List.range c.gates.length).any (fun j =>
          match c.gates[j]? with
          | none => false
          | some g => (g.w1 == n + k) || (g.w2 == n + k))
      · exfalso
        apply hnot
        intro j g hgj
        have hjlt : j < c.gates.length := by
          by_cases hlt : j < c.gates.length
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hgj; cases hgj
        have hfalse := List.any_eq_false.1 ha j (List.mem_range.2 hjlt)
        rw [hgj] at hfalse
        dsimp only at hfalse
        constructor
        · intro h1; rw [h1] at hfalse; simp at hfalse
        · intro h2; rw [h2] at hfalse; simp at hfalse
      · rfl
    rcases List.any_eq_true.1 hex with ⟨j, _, hmatch⟩
    cases hgj : c.gates[j]? with
    | none => rw [hgj] at hmatch; cases hmatch
    | some g =>
      rw [hgj] at hmatch
      rcases Bool.or_eq_true_iff.1 hmatch with h1 | h2
      · exact ⟨j, g, hgj, Or.inl (beq_iff_eq.1 h1)⟩
      · exact ⟨j, g, hgj, Or.inr (beq_iff_eq.1 h2)⟩
  refine ⟨c, hwf, hnorm, by omega, hpos, hout_eq, hcomp, ?_, hused⟩
  intro c' hwf' hcomp'
  rw [hsz]
  exact hbest c' hwf' hcomp'

/-! ## 4. Input Restriction Helper & 3-Cofactor Fan-Out Lemma -/

private def insertBit {n : Nat} (x : BoolVec n) (idx : Fin (n + 1)) (val : Bool) : BoolVec (n + 1) :=
  fun i =>
    if h : i.val < idx.val then x ⟨i.val, by omega⟩
    else if h2 : i.val = idx.val then val
    else x ⟨i.val - 1, by omega⟩

private def restrictMap (n : Nat) (idx : Fin (n + 1)) (val : Bool) : List WireRef :=
  (List.range (n + 1)).map fun i =>
    if i < idx.val then .wire i false
    else if i == idx.val then .const val
    else .wire (i - 1) false

private theorem restrictMap_length (n : Nat) (idx : Fin (n + 1)) (val : Bool) :
    (restrictMap n idx val).length = n + 1 := by
  simp [restrictMap]

private theorem restrictMap_getD (n : Nat) (idx : Fin (n + 1)) (val : Bool) (i : Nat) (hi : i < n + 1) :
    (restrictMap n idx val).getD i (.const false) =
      (if i < idx.val then .wire i false else if i == idx.val then .const val else .wire (i - 1) false) := by
  simp [restrictMap, List.getD, List.getElem?_map, List.getElem?_range hi]

private theorem restrictMap_eval {n : Nat} (x : BoolVec n) (idx : Fin (n + 1)) (val : Bool)
    (k : Nat) (hk : k < n + 1) :
    evalRef (B2Circuit.evalWires x []) ((restrictMap n idx val).getD k (.const false)) =
      insertBit x idx val ⟨k, hk⟩ := by
  rw [restrictMap_getD n idx val k hk]
  dsimp only [insertBit]
  by_cases hlt : k < idx.val
  · simp only [hlt, ↓reduceIte, ↓reduceDIte, evalRef]
    rw [evalWires_input x [] ⟨k, by omega⟩, Bool.xor_false]
  · simp only [hlt, ↓reduceIte, ↓reduceDIte]
    by_cases heq : k = idx.val
    · simp [heq, evalRef]
    · have hbf : (k == idx.val) = false := beq_false_of_ne heq
      simp only [hbf, Bool.false_eq_true, heq, ↓reduceIte, ↓reduceDIte, evalRef]
      rw [evalWires_input x [] ⟨k - 1, by omega⟩, Bool.xor_false]

private theorem restrict_circuit {n : Nat} {f : BoolFn (n + 1)} {f' : BoolFn n}
    (hf' : IsNonTrivial f')
    (c : B2Circuit (n + 1)) (hwf : WF (n + 1) c) (hcomp : ComputesUpToNeg c f)
    (idx : Fin (n + 1)) (val : Bool)
    (hres : ∀ x : BoolVec n, f (insertBit x idx val) = f' x)
    (i1 i2 : Nat) (hi1 : i1 < c.gates.length) (hi2 : i2 < c.gates.length) (hne : i1 ≠ i2)
    (g1 g2 : B2Gate) (hg1 : c.gates[i1]? = some g1) (hg2 : c.gates[i2]? = some g2)
    (hr1 : g1.w1 = idx.val ∨ g1.w2 = idx.val)
    (hr2 : g2.w1 = idx.val ∨ g2.w2 = idx.val) :
    ∃ c' : B2Circuit n, WF n c' ∧ IsNormGates n c'.gates ∧ c'.size + 2 ≤ c.size ∧ ComputesUpToNeg c' f' := by
  let rmap := restrictMap n idx val
  let res := compileAux n [] rmap [] c.gates
  let out := res.1
  let wmap := res.2.1
  let dropped := res.2.2
  have hstep := compileAux_step_props (n + 1) n [] c.gates [] rmap []
    hwf.2 (by simp [rmap, restrictMap_length]) rfl rfl (fun _ _ h => by cases h)
  have hidx_const : wmap.getD idx.val (.const false) = .const val := by
    rw [hstep.1 idx.val (by rw [restrictMap_length]; exact idx.isLt)]
    rw [restrictMap_getD n idx val idx.val idx.isLt]
    have hnl : ¬ (idx.val < idx.val) := Nat.lt_irrefl _
    simp [hnl]
  have hd1 : dropped.getD i1 false = true := by
    rcases hr1 with h | h
    · exact (hstep.2.2 i1 g1 hg1).1 val (h ▸ hidx_const)
    · exact (hstep.2.2 i1 g1 hg1).2 val (h ▸ hidx_const)
  have hd2 : dropped.getD i2 false = true := by
    rcases hr2 with h | h
    · exact (hstep.2.2 i2 g2 hg2).1 val (h ▸ hidx_const)
    · exact (hstep.2.2 i2 g2 hg2).2 val (h ▸ hidx_const)
  have hprops : ∀ x : BoolVec n,
      IsNormGates n out ∧ wmap.length = (n + 1) + c.gates.length ∧
      dropped.length = c.gates.length ∧ out.length = dropped.count false ∧
      (∀ k, k < wmap.length → (wmap.getD k (.const false)).wf (n + out.length)) ∧
      (∀ k, k < wmap.length →
        evalRef (B2Circuit.evalWires x out) (wmap.getD k (.const false)) =
          (B2Circuit.evalWires (insertBit x idx val) c.gates).getD k false) := by
    intro x
    have h := compileAux_inv (n + 1) n (insertBit x idx val) x [] c.gates [] rmap []
      hwf.2 (fun _ _ h => by cases h)
      (by simp [rmap, restrictMap_length]) rfl rfl
      (by
        intro k hk; rw [restrictMap_length] at hk; rw [restrictMap_getD n idx val k hk]
        by_cases hlt : k < idx.val
        · simp only [hlt, ↓reduceIte, WireRef.wf]; omega
        · by_cases heq : k = idx.val
          · simp [hlt, heq, WireRef.wf]
          · have hbf : (k == idx.val) = false := beq_false_of_ne heq
            simp only [hlt, hbf, Bool.false_eq_true, ↓reduceIte, WireRef.wf]; omega)
      (by
        intro k hk; rw [restrictMap_length] at hk
        rw [restrictMap_eval x idx val k hk]
        exact (evalWires_input (insertBit x idx val) [] ⟨k, hk⟩).symm)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  obtain ⟨hnorm, hwlen, hdlen, houtlen, hwwf, _⟩ := hprops (fun _ => false)
  have hout_wf := hwf.1
  have hcnt := count_false_le_of_two_true dropped i1 i2 (by omega) (by omega) hne hd1 hd2
  rcases hcomp with ⟨flip, hflip⟩
  cases houtref : wmap.getD c.outputWire (.const false) with
  | const b =>
    exfalso
    obtain ⟨x0, hx0⟩ := hf'.1 (xor b flip)
    have hev := (hprops x0).2.2.2.2.2 c.outputWire (by omega)
    rw [houtref] at hev
    have hc := hflip (insertBit x0 idx val)
    rw [hres x0] at hc
    dsimp only [B2Circuit.eval] at hc
    rw [← hev] at hc
    dsimp only [evalRef] at hc
    cases b <;> cases flip <;> cases hf0 : f' x0 <;> rw [hf0] at hc hx0 <;> simp at hc hx0
  | wire w p =>
    have hw_lt : w < n + out.length := by
      have := hwwf c.outputWire (by omega); rw [houtref] at this; exact this
    refine ⟨⟨out, w⟩, ⟨hw_lt, isNormGates_wf hnorm⟩, hnorm, by dsimp only [B2Circuit.size]; omega, xor flip p, ?_⟩
    intro x
    have hev := (hprops x).2.2.2.2.2 c.outputWire (by omega)
    rw [houtref] at hev
    have hc := hflip (insertBit x idx val)
    rw [hres x] at hc
    dsimp only [B2Circuit.eval, evalRef] at hc hev ⊢
    rw [← hev] at hc
    cases hv : (B2Circuit.evalWires x out).getD w false <;> rw [hv] at hc <;>
      cases p <;> cases hfx : f' x <;> rw [hfx] at hc <;> cases flip <;> simp at hc ⊢

-- 3-cofactor fan-out lemma: if gate 0 reads two distinct inputs i1, i2, and f has 3 distinct cofactors
-- on (i1, i2), then at least one of i1, i2 is read by some later gate j >= 1!
private def setTwo {n : Nat} (x : BoolVec n) (i1 i2 : Fin n) (v1 v2 : Bool) : BoolVec n :=
  fun k => if k = i1 then v1 else if k = i2 then v2 else x k

private theorem fanout_ge_2_of_three_cofactors {n : Nat} {f : BoolFn n}
    (c : B2Circuit n) (hwf : WF n c) (hpos : 1 ≤ c.size)
    (hout : c.outputWire = n + (c.size - 1))
    (hcomp : ComputesUpToNeg c f)
    (g0 : B2Gate) (hg0 : c.gates[0]? = some g0)
    (i1 i2 : Fin n) (hw1 : g0.w1 = i1.val) (hw2 : g0.w2 = i2.val) (hne : i1 ≠ i2)
    (hcof : ∀ b1 b2 b3 : Bool,
      (b1 = b2 → ∃ x : BoolVec n, f (setTwo x i1 i2 false false) ≠ f (setTwo x i1 i2 false true)) ∧
      (b1 = b3 → ∃ x : BoolVec n, f (setTwo x i1 i2 false false) ≠ f (setTwo x i1 i2 true true)) ∧
      (b2 = b3 → ∃ x : BoolVec n, f (setTwo x i1 i2 false true) ≠ f (setTwo x i1 i2 true true))) :
    ∃ (j : Nat) (gj : B2Gate), 1 ≤ j ∧ j < c.gates.length ∧ c.gates[j]? = some gj ∧
      (gj.w1 = i1.val ∨ gj.w2 = i1.val ∨ gj.w1 = i2.val ∨ gj.w2 = i2.val) := by
  have hdec : (List.range c.gates.length).any (fun j =>
      if j == 0 then false
      else match c.gates[j]? with
      | none => false
      | some g => (g.w1 == i1.val) || (g.w2 == i1.val) || (g.w1 == i2.val) || (g.w2 == i2.val)) = true := by
    cases ha : (List.range c.gates.length).any (fun j =>
        if j == 0 then false
        else match c.gates[j]? with
        | none => false
        | some g => (g.w1 == i1.val) || (g.w2 == i1.val) || (g.w1 == i2.val) || (g.w2 == i2.val))
    · exfalso
      have hno : ∀ j g, 1 ≤ j → c.gates[j]? = some g →
          g.w1 ≠ i1.val ∧ g.w2 ≠ i1.val ∧ g.w1 ≠ i2.val ∧ g.w2 ≠ i2.val := by
        intro j g hj hgj
        have hjlt : j < c.gates.length := by
          by_cases hlt : j < c.gates.length
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hgj; cases hgj
        have hf := List.any_eq_false.1 ha j (List.mem_range.2 hjlt)
        have hj0 : (j == 0) = false := by cases j with | zero => omega | succ _ => rfl
        simp only [hj0, Bool.false_eq_true, ↓reduceIte, hgj] at hf
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [h] at hf
      -- For any x, if two pairs (a1, a2) and (b1, b2) give the same g0.op.eval, then c.eval agrees!
      have hsame : ∀ (x : BoolVec n) (a1 a2 b1 b2 : Bool),
          g0.op.eval a1 a2 = g0.op.eval b1 b2 →
          c.eval (setTwo x i1 i2 a1 a2) = c.eval (setTwo x i1 i2 b1 b2) := by
        intro x a1 a2 b1 b2 heq0
        let xa := setTwo x i1 i2 a1 a2
        let xb := setTwo x i1 i2 b1 b2
        have hw_eq : ∀ w, w < n + c.gates.length → w ≠ i1.val → w ≠ i2.val →
            (B2Circuit.evalWires xa c.gates).getD w false =
            (B2Circuit.evalWires xb c.gates).getD w false := by
          intro w
          induction w using Nat.strongRecOn with
          | ind w ih =>
            intro hw h1 h2
            by_cases hlt : w < n
            · rw [evalWires_input xa c.gates ⟨w, hlt⟩, evalWires_input xb c.gates ⟨w, hlt⟩]
              dsimp only [xa, xb, setTwo]
              have hne1 : (⟨w, hlt⟩ : Fin n) ≠ i1 := fun h => h1 (congrArg Fin.val h)
              have hne2 : (⟨w, hlt⟩ : Fin n) ≠ i2 := fun h => h2 (congrArg Fin.val h)
              simp [hne1, hne2]
            · let j := w - n
              have hwj : w = n + j := by omega
              have hjlt : j < c.gates.length := by omega
              have hgj : c.gates[j]? = some (c.gates[j]) := List.getElem?_eq_getElem hjlt
              rw [hwj, evalWires_gate xa c.gates j _ hgj hwf.2,
                  evalWires_gate xb c.gates j _ hgj hwf.2]
              by_cases hj0 : j = 0
              · have hgj0 : c.gates[j] = g0 := by
                  have h' : c.gates[0]? = some (c.gates[j]) := hj0 ▸ hgj
                  rw [hg0] at h'; exact Option.some.inj h'.symm
                rw [hgj0, hw1, hw2, evalWires_input xa _ i1, evalWires_input xa _ i2,
                    evalWires_input xb _ i1, evalWires_input xb _ i2]
                dsimp only [xa, xb, setTwo]
                have h21 : i2 ≠ i1 := Ne.symm hne
                simp [h21, heq0]
              · have hgw := hwf.2 j _ hgj
                have hno_j := hno j _ (by omega) hgj
                rw [ih _ (by omega) (by omega) hno_j.1 hno_j.2.2.1,
                    ih _ (by omega) (by omega) hno_j.2.1 hno_j.2.2.2]
        dsimp only [B2Circuit.eval]
        exact hw_eq c.outputWire hwf.1 (by rw [hout]; omega) (by rw [hout]; omega)
      -- Pigeonhole on the 3 booleans g0.op.eval (0,0), (0,1), (1,1)
      let v1 := g0.op.eval false false
      let v2 := g0.op.eval false true
      let v3 := g0.op.eval true true
      rcases hcomp with ⟨flip, hflip⟩
      have hxor_inj : ∀ a b : Bool, xor a flip = xor b flip → a = b := by
        intro a b hab; cases a <;> cases b <;> cases flip <;> simp at hab ⊢
      have htri := hcof v1 v2 v3
      cases hv1 : v1 <;> cases hv2 : v2 <;> cases hv3 : v3
      · obtain ⟨x, hx⟩ := htri.1 (by rw [hv1, hv2])
        have hs := hsame x false false false true (by dsimp only [v1, v2] at hv1 hv2; rw [hv1, hv2])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.1 (by rw [hv1, hv2])
        have hs := hsame x false false false true (by dsimp only [v1, v2] at hv1 hv2; rw [hv1, hv2])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.2.1 (by rw [hv1, hv3])
        have hs := hsame x false false true true (by dsimp only [v1, v3] at hv1 hv3; rw [hv1, hv3])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.2.2 (by rw [hv2, hv3])
        have hs := hsame x false true true true (by dsimp only [v2, v3] at hv2 hv3; rw [hv2, hv3])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.2.2 (by rw [hv2, hv3])
        have hs := hsame x false true true true (by dsimp only [v2, v3] at hv2 hv3; rw [hv2, hv3])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.2.1 (by rw [hv1, hv3])
        have hs := hsame x false false true true (by dsimp only [v1, v3] at hv1 hv3; rw [hv1, hv3])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.1 (by rw [hv1, hv2])
        have hs := hsame x false false false true (by dsimp only [v1, v2] at hv1 hv2; rw [hv1, hv2])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
      · obtain ⟨x, hx⟩ := htri.1 (by rw [hv1, hv2])
        have hs := hsame x false false false true (by dsimp only [v1, v2] at hv1 hv2; rw [hv1, hv2])
        rw [hflip, hflip] at hs; exact hx (hxor_inj _ _ hs)
    · rfl
  rcases List.any_eq_true.1 hdec with ⟨j, hjmem, hcond⟩
  have hjlt : j < c.gates.length := List.mem_range.1 hjmem
  cases j with
  | zero => simp at hcond
  | succ j' =>
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, beq_iff_eq, ↓reduceIte] at hcond
    cases hgj : c.gates[j' + 1]? with
    | none => rw [hgj] at hcond; cases hcond
    | some gj =>
      rw [hgj] at hcond
      refine ⟨j' + 1, gj, by omega, hjlt, hgj, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hcond
      rcases hcond with ((h | h) | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

/-! ## 5. 3-Bit Truth Table (`TT3`), Canonical Sorting, & Kernel Checks -/

private structure TT3 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
  b7 : Bool
  deriving DecidableEq, BEq

private def TT3.zero : TT3 := ⟨false,false,false,false,false,false,false,false⟩
private def TT3.one  : TT3 := ⟨true,true,true,true,true,true,true,true⟩
private def TT3.x0   : TT3 := ⟨false,true,false,true,false,true,false,true⟩
private def TT3.x1   : TT3 := ⟨false,false,true,true,false,false,true,true⟩
private def TT3.x2   : TT3 := ⟨false,false,false,false,true,true,true,true⟩
private def TT3.maj3 : TT3 := ⟨false,false,false,true,false,true,true,true⟩
private def TT3.or3  : TT3 := ⟨false,true,true,true,true,true,true,true⟩

private def TT3.not (a : TT3) : TT3 :=
  ⟨!a.b0, !a.b1, !a.b2, !a.b3, !a.b4, !a.b5, !a.b6, !a.b7⟩

private def TT3.evalOp5 (op : Nat) (a b : TT3) : TT3 :=
  match op with
  | 0 => ⟨a.b0 && b.b0, a.b1 && b.b1, a.b2 && b.b2, a.b3 && b.b3,
          a.b4 && b.b4, a.b5 && b.b5, a.b6 && b.b6, a.b7 && b.b7⟩
  | 1 => ⟨a.b0 && !b.b0, a.b1 && !b.b1, a.b2 && !b.b2, a.b3 && !b.b3,
          a.b4 && !b.b4, a.b5 && !b.b5, a.b6 && !b.b6, a.b7 && !b.b7⟩
  | 2 => ⟨!a.b0 && b.b0, !a.b1 && b.b1, !a.b2 && b.b2, !a.b3 && b.b3,
          !a.b4 && b.b4, !a.b5 && b.b5, !a.b6 && b.b6, !a.b7 && b.b7⟩
  | 3 => ⟨a.b0 || b.b0, a.b1 || b.b1, a.b2 || b.b2, a.b3 || b.b3,
          a.b4 || b.b4, a.b5 || b.b5, a.b6 || b.b6, a.b7 || b.b7⟩
  | _ => ⟨xor a.b0 b.b0, xor a.b1 b.b1, xor a.b2 b.b2, xor a.b3 b.b3,
          xor a.b4 b.b4, xor a.b5 b.b5, xor a.b6 b.b6, xor a.b7 b.b7⟩

private def vec3 (b0 b1 b2 : Bool) : BoolVec 3 :=
  fun i => match i with | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2

private def tt3Of (f : BoolFn 3) : TT3 :=
  ⟨f (vec3 false false false), f (vec3 true false false),
   f (vec3 false true false),  f (vec3 true true false),
   f (vec3 false false true),  f (vec3 true false true),
   f (vec3 false true true),   f (vec3 true true true)⟩

private theorem tt3Of_x0 : tt3Of (fun x => x ⟨0, by decide⟩) = TT3.x0 := rfl
private theorem tt3Of_x1 : tt3Of (fun x => x ⟨1, by decide⟩) = TT3.x1 := rfl
private theorem tt3Of_x2 : tt3Of (fun x => x ⟨2, by decide⟩) = TT3.x2 := rfl
private theorem tt3Of_maj3 : tt3Of PnP.maj3 = TT3.maj3 := rfl
private theorem tt3Of_or3 : tt3Of or3 = TT3.or3 := rfl

private theorem tt3Of_not (f : BoolFn 3) : tt3Of (fun x => !(f x)) = (tt3Of f).not := rfl

private theorem tt3Of_op (op : B2Op) (hop : (isNorm5 op) = true) (f g : BoolFn 3) :
    tt3Of (fun x => op.eval (f x) (g x)) = TT3.evalOp5 (opToNat5 op) (tt3Of f) (tt3Of g) := by
  have heq := opOfNat5_toNat5 op hop
  have hlt := opToNat5_lt op
  have e0 : ∀ a b : Bool, (opOfNat5 0).eval a b = (a && b) := by decide
  have e1 : ∀ a b : Bool, (opOfNat5 1).eval a b = (a && !b) := by decide
  have e2 : ∀ a b : Bool, (opOfNat5 2).eval a b = (!a && b) := by decide
  have e3 : ∀ a b : Bool, (opOfNat5 3).eval a b = (a || b) := by decide
  have e4 : ∀ a b : Bool, (opOfNat5 4).eval a b = xor a b := by decide
  match hk : opToNat5 op with
  | 0 => rw [hk] at heq; rw [← heq]; simp only [tt3Of, TT3.evalOp5, e0]
  | 1 => rw [hk] at heq; rw [← heq]; simp only [tt3Of, TT3.evalOp5, e1]
  | 2 => rw [hk] at heq; rw [← heq]; simp only [tt3Of, TT3.evalOp5, e2]
  | 3 => rw [hk] at heq; rw [← heq]; simp only [tt3Of, TT3.evalOp5, e3]
  | 4 => rw [hk] at heq; rw [← heq]; simp only [tt3Of, TT3.evalOp5, e4]
  | k + 5 => omega

private def getW3 (w0 w1 w2 w3 w4 w5 : TT3) (idx : Nat) : TT3 :=
  match idx with
  | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3 | 4 => w4 | _ => w5

private def pairsUpTo (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun b => (List.range b).map fun a => (a, b)

private theorem mem_pairsUpTo (n a b : Nat) (hab : a < b) (hb : b < n) :
    (a, b) ∈ pairsUpTo n := by
  unfold pairsUpTo
  rw [List.mem_flatMap]
  refine ⟨b, List.mem_range.2 hb, ?_⟩
  rw [List.mem_map]
  exact ⟨a, List.mem_range.2 hab, rfl⟩

private def pairLe (p q : Nat × Nat) : Bool :=
  p.2 < q.2 || (p.2 == q.2 && p.1 <= q.1)

private def allTopos3 : List (Nat × Nat × Nat × Nat) :=
  (pairsUpTo 4).flatMap fun (a1, b1) =>
    if !pairLe (0, 1) (a1, b1) then [] else
    (pairsUpTo 5).filterMap fun (a2, b2) =>
      if !pairLe (a1, b1) (a2, b2) then none else
      let used3 := a1 == 3 || b1 == 3 || a2 == 3 || b2 == 3
      let used4 := a2 == 4 || b2 == 4
      if used3 && used4 then some (a1, b1, a2, b2) else none

private def checkTopo3 (a1 b1 a2 b2 : Nat) : Bool :=
  let allOps := [0, 1, 2, 3, 4]
  allOps.all fun o0 =>
    let w3 := TT3.evalOp5 o0 TT3.x0 TT3.x1
    allOps.all fun o1 =>
      let w4 := TT3.evalOp5 o1 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero a1)
                               (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero b1)
      allOps.all fun o2 =>
        let w5 := TT3.evalOp5 o2 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero a2)
                                 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero b2)
        w5 != TT3.maj3

private theorem no_maj3_3_check :
    allTopos3.all (fun (a1, b1, a2, b2) => checkTopo3 a1 b1 a2 b2) = true := by
  decide +kernel

-- 2-gate and 1-gate normalized circuits cannot compute maj3 either
private theorem no_maj3_1_check :
    [0, 1, 2, 3, 4].all (fun o0 => TT3.evalOp5 o0 TT3.x0 TT3.x1 != TT3.maj3) = true := by
  decide +kernel

private theorem no_maj3_2_check :
    (pairsUpTo 4).all (fun (a1, b1) =>
      [0, 1, 2, 3, 4].all fun o0 =>
        let w3 := TT3.evalOp5 o0 TT3.x0 TT3.x1
        [0, 1, 2, 3, 4].all fun o1 =>
          TT3.evalOp5 o1 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero a1)
                         (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero b1) != TT3.maj3) = true := by
  decide +kernel

-- Perturbation checker for 4-gate MAJ3 circuits (using fast Bool slots instead of Nat bitmasks)
private structure Mask8 where
  s0a : Bool
  s0b : Bool
  s1a : Bool
  s1b : Bool
  s2a : Bool
  s2b : Bool
  s3a : Bool
  s3b : Bool
  deriving DecidableEq, BEq

private def Mask8.empty : Mask8 := ⟨false,false,false,false,false,false,false,false⟩

private def Mask8.setBit (m : Mask8) (k : Nat) : Mask8 :=
  match k with
  | 0 => { m with s0a := true }
  | 1 => { m with s0b := true }
  | 2 => { m with s1a := true }
  | 3 => { m with s1b := true }
  | 4 => { m with s2a := true }
  | 5 => { m with s2b := true }
  | 6 => { m with s3a := true }
  | _ => { m with s3b := true }

private def Mask8.disjoint (a b : Mask8) : Bool :=
  !(a.s0a && b.s0a) && !(a.s0b && b.s0b) &&
  !(a.s1a && b.s1a) && !(a.s1b && b.s1b) &&
  !(a.s2a && b.s2a) && !(a.s2b && b.s2b) &&
  !(a.s3a && b.s3a) && !(a.s3b && b.s3b)

private def submasks8 : List Nat → List Mask8
  | [] => [Mask8.empty]
  | b :: bs =>
    let rest := submasks8 bs
    rest ++ rest.map (fun m => m.setBit b)

private def evalPert4 (a1 b1 a2 b2 a3 b3 o0 o1 o2 o3 : Nat)
    (x2 : Nat) (m0 : Mask8) (g0Mode : Nat) (u : Nat) (m1 : Mask8) (uMode : Nat) : TT3 :=
  let g0v := match g0Mode with
    | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero x2).not
  let pick (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
    if b0 then g0v
    else if b1 then
      match uMode with
      | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 u).not
    else cur
  let v0a := pick m0.s0a m1.s0a TT3.x0 TT3.zero TT3.zero TT3.zero
  let v0b := pick m0.s0b m1.s0b TT3.x1 TT3.zero TT3.zero TT3.zero
  let w3 := TT3.evalOp5 o0 v0a v0b
  let v1a := pick m0.s1a m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero a1) w3 TT3.zero TT3.zero
  let v1b := pick m0.s1b m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero b1) w3 TT3.zero TT3.zero
  let w4 := TT3.evalOp5 o1 v1a v1b
  let v2a := pick m0.s2a m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero a2) w3 w4 TT3.zero
  let v2b := pick m0.s2b m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero b2) w3 w4 TT3.zero
  let w5 := TT3.evalOp5 o2 v2a v2b
  let v3a := pick m0.s3a m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 a3) w3 w4 w5
  let v3b := pick m0.s3b m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 b3) w3 w4 w5
  TT3.evalOp5 o3 v3a v3b

private def slotsOf4 (a1 b1 a2 b2 a3 b3 w : Nat) : List Nat :=
  (if 0 == w then [0] else []) ++ (if 1 == w then [1] else []) ++
  (if a1 == w then [2] else []) ++ (if b1 == w then [3] else []) ++
  (if a2 == w then [4] else []) ++ (if b2 == w then [5] else []) ++
  (if a3 == w then [6] else []) ++ (if b3 == w then [7] else [])

private def checkLiftOne (a1 b1 a2 b2 a3 b3 o0 o1 o2 o3 : Nat) : Bool :=
  [0, 1, 2].all fun x2 =>
    let sm0 := submasks8 (slotsOf4 a1 b1 a2 b2 a3 b3 x2)
    sm0.all fun m0 =>
      [0, 1, 2].all fun g0Mode =>
        let outA := evalPert4 a1 b1 a2 b2 a3 b3 o0 o1 o2 o3 x2 m0 g0Mode 0 Mask8.empty 0
        (outA != TT3.or3 && outA != TT3.or3.not) &&
        [0, 1, 2, 3, 4, 5].all fun u =>
          let sm1 := submasks8 (slotsOf4 a1 b1 a2 b2 a3 b3 u)
          sm1.all fun m1 =>
            if m1 == Mask8.empty || (u == x2 && !(m0.disjoint m1)) then true
            else [0, 1, 2].all fun uMode =>
              evalPert4 a1 b1 a2 b2 a3 b3 o0 o1 o2 o3 x2 m0 g0Mode u m1 uMode != TT3.or3

private def allTopos4 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (pairsUpTo 4).flatMap fun (a1, b1) =>
    if !pairLe (0, 1) (a1, b1) then [] else
    (pairsUpTo 5).flatMap fun (a2, b2) =>
      if !pairLe (a1, b1) (a2, b2) then [] else
      (pairsUpTo 6).filterMap fun (a3, b3) =>
        if !pairLe (a2, b2) (a3, b3) then none else
        let used2 := a1 == 2 || b1 == 2 || a2 == 2 || b2 == 2 || a3 == 2 || b3 == 2
        let used3 := a1 == 3 || b1 == 3 || a2 == 3 || b2 == 3 || a3 == 3 || b3 == 3
        let used4 := a2 == 4 || b2 == 4 || a3 == 4 || b3 == 4
        let used5 := a3 == 5 || b3 == 5
        if used2 && used3 && used4 && used5 then some (a1, b1, a2, b2, a3, b3) else none

private def checkTopo4 (a1 b1 a2 b2 a3 b3 : Nat) : Bool :=
  let allOps := [0, 1, 2, 3, 4]
  allOps.all fun o0 =>
    let w3 := TT3.evalOp5 o0 TT3.x0 TT3.x1
    allOps.all fun o1 =>
      let w4 := TT3.evalOp5 o1 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero a1)
                               (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero b1)
      allOps.all fun o2 =>
        let w5 := TT3.evalOp5 o2 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero a2)
                                 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero b2)
        allOps.all fun o3 =>
          let w6 := TT3.evalOp5 o3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 a3)
                                   (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 b3)
          if w6 == TT3.maj3 then checkLiftOne a1 b1 a2 b2 a3 b3 o0 o1 o2 o3
          else true

private theorem no_maj3_4_lift_check :
    allTopos4.all (fun (a1, b1, a2, b2, a3, b3) => checkTopo4 a1 b1 a2 b2 a3 b3) = true := by
  decide +kernel

/-! ## 6. Canonicalizing 3-Bit Circuits (`S_3` + Adjacent-Swap Bubble Sort) & `maj3_lb` -/

-- Every normalized circuit outputs `false` on the all-false input!
private theorem evalWires_allFalse_norm {n : Nat} (gs : List B2Gate) (hnorm : IsNormGates n gs) :
    ∀ w, w < n + gs.length → (B2Circuit.evalWires (fun _ : Fin n => false) gs).getD w false = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · exact evalWires_input (fun _ => false) gs ⟨w, hlt⟩
    · let i := w - n
      have hwi : w = n + i := by omega
      have hilt : i < gs.length := by omega
      have hgi : gs[i]? = some (gs[i]) := List.getElem?_eq_getElem hilt
      obtain ⟨h1, h2, hop⟩ := hnorm i (gs[i]) hgi
      rw [hwi, evalWires_gate _ gs i _ hgi (isNormGates_wf hnorm)]
      rw [ih (gs[i]).w1 (by omega) (by omega), ih (gs[i]).w2 (by omega) (by omega)]
      exact eval_norm5_false _ hop

-- S_3 permutation on 3-bit inputs sending a pair (a, b) with a < b < 3 to (0, 1)
private def perm3For (a b : Nat) : Fin 3 → Fin 3 :=
  if a == 0 && b == 1 then id
  else if a == 0 && b == 2 then
    fun i => match i with | ⟨0, _⟩ => ⟨0, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨1, by decide⟩
  else
    fun i => match i with | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨0, by decide⟩

private def perm3Inv (a b : Nat) : Fin 3 → Fin 3 :=
  if a == 0 && b == 1 then id
  else if a == 0 && b == 2 then
    fun i => match i with | ⟨0, _⟩ => ⟨0, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨1, by decide⟩
  else
    fun i => match i with | ⟨0, _⟩ => ⟨2, by decide⟩ | ⟨1, _⟩ => ⟨0, by decide⟩ | ⟨2, _⟩ => ⟨1, by decide⟩

private def permWire3 (p : Fin 3 → Fin 3) (w : Nat) : Nat :=
  if h : w < 3 then (p ⟨w, h⟩).val else w

private def permGate3 (p : Fin 3 → Fin 3) (g : B2Gate) : B2Gate :=
  let u1 := permWire3 p g.w1
  let u2 := permWire3 p g.w2
  if u2 < u1 then ⟨(b2SwapIn g.op), u2, u1⟩ else ⟨g.op, u1, u2⟩

private theorem perm3_props (a b : Nat) (hab : a < b) (hb : b < 3) :
    (∀ i : Fin 3, perm3Inv a b (perm3For a b i) = i) ∧
    (∀ i : Fin 3, perm3For a b (perm3Inv a b i) = i) ∧
    permWire3 (perm3Inv a b) a = 0 ∧ permWire3 (perm3Inv a b) b = 1 ∧
    (∀ x : BoolVec 3, PnP.maj3 (fun i => x (perm3Inv a b i)) = PnP.maj3 x) ∧
    (∀ x : BoolVec 3, or3 (fun i => x (perm3Inv a b i)) = or3 x) := by
  have hvec : ∀ x : BoolVec 3, x = vec3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) := by
    intro x; funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  have hcases : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨fun i => rfl, fun i => rfl, rfl, rfl, fun x => rfl, fun x => rfl⟩
  · refine ⟨?_, ?_, by decide, by decide, ?_, ?_⟩
    · intro i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    · intro i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    · intro x; rw [hvec x]
      cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩ <;> decide
    · intro x; rw [hvec x]
      cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩ <;> decide
  · refine ⟨?_, ?_, by decide, by decide, ?_, ?_⟩
    · intro i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    · intro i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    · intro x; rw [hvec x]
      cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩ <;> decide
    · intro x; rw [hvec x]
      cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩ <;> decide

-- Adjacent swap of two gates k and k+1 in a 3-bit normalized circuit
private def swapIdx (p q w : Nat) : Nat :=
  if w == p then q else if w == q then p else w

private def remapGateSwap (p q : Nat) (g : B2Gate) : B2Gate :=
  let u1 := swapIdx p q g.w1
  let u2 := swapIdx p q g.w2
  if u2 < u1 then ⟨(b2SwapIn g.op), u2, u1⟩ else ⟨g.op, u1, u2⟩

private theorem swapIdx_invol (p q w : Nat) : swapIdx p q (swapIdx p q w) = w := by
  unfold swapIdx
  by_cases h1 : w = p
  · subst h1; by_cases h2 : w = q <;> simp [h2]
  · by_cases h2 : w = q
    · subst h2; simp [h1]
    · have hb1 : (w == p) = false := beq_false_of_ne h1
      have hb2 : (w == q) = false := beq_false_of_ne h2
      simp [hb1, hb2]

private theorem eval_permGate3 (p inv : Fin 3 → Fin 3)
    (hpinv : ∀ i, inv (p i) = i) (hinvp : ∀ i, p (inv i) = i)
    (gs : List B2Gate) (hnorm : IsNormGates 3 gs) :
    let gs' := gs.map (permGate3 inv)
    IsNormGates 3 gs' ∧
    ∀ (x : BoolVec 3) (w : Nat), w < 3 + gs.length →
      (B2Circuit.evalWires x gs').getD (permWire3 inv w) false =
        (B2Circuit.evalWires (fun i => x (inv i)) gs).getD w false := by
  let gs' := gs.map (permGate3 inv)
  have hnorm' : IsNormGates 3 gs' := by
    intro i g hgi
    dsimp only [gs'] at hgi
    rw [List.getElem?_map] at hgi
    cases h0 : gs[i]? with
    | none => rw [h0] at hgi; cases hgi
    | some g0 =>
      rw [h0] at hgi; simp only [Option.map_some, Option.some.injEq] at hgi
      subst hgi
      obtain ⟨h1, h2, hop⟩ := hnorm i g0 h0
      have hne : permWire3 inv g0.w1 ≠ permWire3 inv g0.w2 := by
        intro heq
        unfold permWire3 at heq
        by_cases ha : g0.w1 < 3 <;> by_cases hb : g0.w2 < 3
        · simp only [ha, hb, ↓reduceDIte] at heq
          have hfin : inv ⟨g0.w1, ha⟩ = inv ⟨g0.w2, hb⟩ := Fin.ext heq
          have hfin2 := congrArg p hfin
          rw [hinvp, hinvp] at hfin2
          have hval : g0.w1 = g0.w2 := congrArg Fin.val hfin2
          omega
        · simp only [ha, hb, ↓reduceDIte] at heq
          have := (inv ⟨g0.w1, ha⟩).isLt; omega
        · simp only [ha, hb, ↓reduceDIte] at heq
          have := (inv ⟨g0.w2, hb⟩).isLt; omega
        · simp only [ha, hb, ↓reduceDIte] at heq; omega
      have hlt1 : permWire3 inv g0.w1 < 3 + i := by
        unfold permWire3; split
        · rename_i h; have := (inv ⟨g0.w1, h⟩).isLt; omega
        · omega
      have hlt2 : permWire3 inv g0.w2 < 3 + i := by
        unfold permWire3; split
        · rename_i h; have := (inv ⟨g0.w2, h⟩).isLt; omega
        · omega
      dsimp only [permGate3]
      split
      · dsimp only; exact ⟨‹_›, hlt1, isNorm5_swapIn _ hop⟩
      · dsimp only; exact ⟨by omega, hlt2, hop⟩
  refine ⟨hnorm', ?_⟩
  intro x w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < 3
    · have hpw : permWire3 inv w = (inv ⟨w, hlt⟩).val := by simp [permWire3, hlt]
      rw [hpw, evalWires_input x gs' (inv ⟨w, hlt⟩), evalWires_input _ gs ⟨w, hlt⟩]
    · have hpw : permWire3 inv w = w := by simp [permWire3, hlt]
      let i := w - 3
      have hwi : w = 3 + i := by omega
      have hilt : i < gs.length := by omega
      have hgi : gs[i]? = some (gs[i]) := List.getElem?_eq_getElem hilt
      have hgi' : gs'[i]? = some (permGate3 inv (gs[i])) := by
        dsimp only [gs']; rw [List.getElem?_map, hgi]; rfl
      obtain ⟨h1, h2, _⟩ := hnorm i (gs[i]) hgi
      rw [hpw, hwi, evalWires_gate x gs' i _ hgi' (isNormGates_wf hnorm'),
          evalWires_gate _ gs i _ hgi (isNormGates_wf hnorm)]
      have ih1 := ih (gs[i]).w1 (by omega) (by omega)
      have ih2 := ih (gs[i]).w2 (by omega) (by omega)
      dsimp only [permGate3]
      split
      · rw [eval_b2SwapIn, ih1, ih2]
      · rw [ih1, ih2]

-- Proving `maj3_lb`: no well-formed 3-bit circuit of size <= 3 computes `maj3` up to negation!
private theorem maj3_nonTrivial : IsNonTrivial PnP.maj3 := by
  constructor
  · intro b
    cases b
    · exact ⟨vec3 true true true, by decide⟩
    · exact ⟨vec3 false false false, by decide⟩
  · intro i b
    have h : ∀ (i : Fin 3) (b : Bool),
        (PnP.maj3 (fun _ => false) != xor false b) ||
        (PnP.maj3 (fun j => decide (j = i)) != xor true b) = true := by decide
    rcases Bool.or_eq_true_iff.1 (h i b) with h1 | h2
    · exact ⟨fun _ => false, by simpa using h1⟩
    · exact ⟨fun j => decide (j = i), by simpa using h2⟩

private theorem th24_nonTrivial : IsNonTrivial th24 := by
  constructor
  · intro b
    cases b
    · exact ⟨fun _ => true, by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  · intro i b
    have h : ∀ (i : Fin 4) (b : Bool),
        (th24 (fun _ => false) != xor false b) ||
        (th24 (fun j => decide (j = i)) != xor true b) = true := by decide
    rcases Bool.or_eq_true_iff.1 (h i b) with h1 | h2
    · exact ⟨fun _ => false, by simpa using h1⟩
    · exact ⟨fun j => decide (j = i), by simpa using h2⟩

private theorem maj3_lb (c : B2Circuit 3) (hwf : WF 3 c) (hcomp : ComputesUpToNeg c PnP.maj3) :
    4 ≤ c.size := by
  by_cases hge : 4 ≤ c.size
  · exact hge
  · exfalso
    have hle3 : c.size ≤ 3 := by omega
    obtain ⟨cm, hwfM, hnormM, hszM, hposM, houtM, hcompM, hminM, husedM⟩ :=
      exists_minimal_norm maj3_nonTrivial ⟨c, hwf, hle3, hcomp⟩
    -- Permute inputs so gate 0 reads (0, 1)
    have hg0_ex : ∃ g0, cm.gates[0]? = some g0 := by
      cases h : cm.gates with
      | nil => simp [B2Circuit.size, h] at hposM
      | cons g0 _ => exact ⟨g0, rfl⟩
    obtain ⟨g0, hg0⟩ := hg0_ex
    obtain ⟨hg0_1, hg0_2, _⟩ := hnormM 0 g0 hg0
    let p := perm3For g0.w1 g0.w2
    let inv := perm3Inv g0.w1 g0.w2
    obtain ⟨hpinv, hinvp, hp0, hp1, hmajP, _⟩ := perm3_props g0.w1 g0.w2 hg0_1 hg0_2
    let gs := cm.gates.map (permGate3 inv)
    obtain ⟨hnormP, hevalP⟩ := eval_permGate3 p inv hpinv hinvp cm.gates hnormM
    have hlen_gs : gs.length = cm.gates.length := List.length_map _
    -- Gate 0 of gs reads (0, 1)
    have hgs0 : gs[0]? = some ⟨g0.op, 0, 1⟩ := by
      dsimp only [gs]; rw [List.getElem?_map, hg0]
      simp only [Option.map_some, Option.some.injEq]
      dsimp only [permGate3]; rw [hp0, hp1]; simp
    -- Since gs is normalized, gs computes maj3 with flip = false!
    have hev_out : ∀ x : BoolVec 3, (B2Circuit.evalWires x gs).getD (3 + (gs.length - 1)) false = PnP.maj3 x := by
      rcases hcompM with ⟨flip, hflip⟩
      have hfl : flip = false := by
        have h0 := hevalP (fun _ => false) cm.outputWire hwfM.1
        have hpw : permWire3 inv cm.outputWire = cm.outputWire := by
          simp only [permWire3]; split
          · omega
          · rfl
        rw [hpw] at h0
        have hnorm0 := evalWires_allFalse_norm gs hnormP cm.outputWire (by rw [hlen_gs]; exact hwfM.1)
        have hf0 := hflip (fun i => (fun _ => false) (inv i))
        dsimp only [B2Circuit.eval] at hf0
        rw [← h0, hnorm0] at hf0
        have hmaj0 : PnP.maj3 (fun _ => false) = false := by decide
        rw [hmaj0] at hf0
        cases flip
        · rfl
        · simp at hf0
      subst hfl
      intro x
      have h0 := hevalP x cm.outputWire hwfM.1
      have hpw : permWire3 inv cm.outputWire = cm.outputWire := by
        simp only [permWire3]; split
        · omega
        · rfl
      rw [hpw, houtM, B2Circuit.size, ← hlen_gs] at h0
      rw [h0]
      have hf := hflip (fun i => x (inv i))
      rw [hmajP x, Bool.xor_false] at hf
      dsimp only [B2Circuit.eval] at hf
      rw [houtM, B2Circuit.size, ← hlen_gs] at hf
      exact hf
    -- Case split on gs.length = 1, 2, 3!
    have hgs_cases : gs.length = 1 ∨ gs.length = 2 ∨ gs.length = 3 := by
      dsimp only [B2Circuit.size] at hszM hposM; omega
    rcases hgs_cases with h1 | h2 | h3
    · -- Size 1: gs = [⟨g0.op, 0, 1⟩]
      have hop0 : (isNorm5 g0.op) = true := (hnormP 0 _ hgs0).2.2
      have htt : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 3 false) = TT3.maj3 := by
        rw [← tt3Of_maj3]; exact congrArg tt3Of (funext fun x => by have := hev_out x; rw [h1] at this; exact this)
      have hgate0 : ∀ x : BoolVec 3, (B2Circuit.evalWires x gs).getD 3 false =
          g0.op.eval (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) := by
        intro x
        have := evalWires_gate x gs 0 ⟨g0.op, 0, 1⟩ hgs0 (isNormGates_wf hnormP)
        rw [evalWires_input x gs (⟨0, by decide⟩ : Fin 3), evalWires_input x gs (⟨1, by decide⟩ : Fin 3)] at this
        exact this
      have htt2 : TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1 = TT3.maj3 := by
        rw [← tt3Of_x0, ← tt3Of_x1, ← tt3Of_op g0.op hop0]
        simpa [hgate0] using htt
      have hchk := List.all_eq_true.1 no_maj3_1_check (opToNat5 g0.op)
        (by have := opToNat5_lt g0.op; match h : opToNat5 g0.op with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | _ + 5 => omega)
      rw [htt2] at hchk; exact absurd hchk (by decide)
    · -- Size 2: gs = [⟨g0.op, 0, 1⟩, g1]
      have hgs_ex : ∃ ga gb, gs = [ga, gb] := by
        match gs, h2 with | [ga, gb], _ => exact ⟨ga, gb, rfl⟩
      obtain ⟨ga, gb, h⟩ := hgs_ex
      rw [h] at hgs0; simp only [List.getElem?_cons_zero, Option.some.injEq] at hgs0
      subst hgs0
      have hop0 : (isNorm5 g0.op) = true := (hnormP 0 ⟨g0.op, 0, 1⟩ (by change gs[0]? = _; rw [h]; rfl)).2.2
      obtain ⟨hb1, hb2, hop1⟩ := hnormP 1 gb (by change gs[1]? = _; rw [h]; rfl)
      have hw3 : ∀ x : BoolVec 3, (B2Circuit.evalWires x gs).getD 3 false =
          g0.op.eval (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) := by
        intro x
        have := evalWires_gate x gs 0 ⟨g0.op, 0, 1⟩ (by rw [h]; rfl) (isNormGates_wf hnormP)
        rw [evalWires_input x gs (⟨0, by decide⟩ : Fin 3), evalWires_input x gs (⟨1, by decide⟩ : Fin 3)] at this
        exact this
      have htt3 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 3 false) =
          TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1 := by
        rw [← tt3Of_x0, ← tt3Of_x1, ← tt3Of_op g0.op hop0]
        exact congrArg tt3Of (funext hw3)
      have hgetW : ∀ idx, idx < 4 →
          tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
            getW3 TT3.x0 TT3.x1 TT3.x2 (TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1) TT3.zero TT3.zero idx := by
        intro idx hidx
        match idx with
        | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
               rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
        | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
               rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
        | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
               rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
        | 3 => exact htt3
      have hw4 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 4 false) = TT3.maj3 := by
        rw [← tt3Of_maj3]; exact congrArg tt3Of (funext fun x => by have := hev_out x; rw [h2] at this; exact this)
      have htt4 : TT3.evalOp5 (opToNat5 gb.op)
          (getW3 TT3.x0 TT3.x1 TT3.x2 (TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1) TT3.zero TT3.zero gb.w1)
          (getW3 TT3.x0 TT3.x1 TT3.x2 (TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1) TT3.zero TT3.zero gb.w2) = TT3.maj3 := by
        rw [← hgetW gb.w1 (by omega), ← hgetW gb.w2 (by omega), ← tt3Of_op gb.op hop1]
        have hstep : (fun x : BoolVec 3 => gb.op.eval ((B2Circuit.evalWires x gs).getD gb.w1 false)
            ((B2Circuit.evalWires x gs).getD gb.w2 false)) =
            (fun x : BoolVec 3 => (B2Circuit.evalWires x gs).getD 4 false) := by
          funext x; exact (evalWires_gate x gs 1 gb (by change gs[1]? = _; rw [h]; rfl) (isNormGates_wf hnormP)).symm
        rw [hstep, hw4]
      have hchk := List.all_eq_true.1 no_maj3_2_check (gb.w1, gb.w2) (mem_pairsUpTo 4 gb.w1 gb.w2 hb1 hb2)
      have hchk0 := List.all_eq_true.1 hchk (opToNat5 g0.op)
        (by have := opToNat5_lt g0.op; match h : opToNat5 g0.op with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | _ + 5 => omega)
      have hchk1 := List.all_eq_true.1 hchk0 (opToNat5 gb.op)
        (by have := opToNat5_lt gb.op; match h : opToNat5 gb.op with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | _ + 5 => omega)
      rw [htt4] at hchk1; exact absurd hchk1 (by decide)
    · -- Size 3: gs = [⟨g0.op, 0, 1⟩, g1, g2]
      have hgs_ex : ∃ ga g1 g2, gs = [ga, g1, g2] := by
        match gs, h3 with | [ga, g1, g2], _ => exact ⟨ga, g1, g2, rfl⟩
      obtain ⟨ga, g1, g2, h⟩ := hgs_ex
      rw [h] at hgs0; simp only [List.getElem?_cons_zero, Option.some.injEq] at hgs0
      subst hgs0
      obtain ⟨_, _, hop0⟩ := hnormP 0 _ (by change gs[0]? = _; rw [h]; rfl)
      obtain ⟨ha1, hb1, hop1⟩ := hnormP 1 g1 (by change gs[1]? = _; rw [h]; rfl)
      obtain ⟨ha2, hb2, hop2⟩ := hnormP 2 g2 (by change gs[2]? = _; rw [h]; rfl)
      have hg2_uses_4 : g2.w1 = 4 ∨ g2.w2 = 4 := by
        have hu1 := husedM 1 (by dsimp only [B2Circuit.size]; omega)
        rcases hu1 with ⟨j, gj, hgj, hreads⟩
        have hjlt : j < 3 := by
          by_cases hlt : j < 3
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hgj; cases hgj
        have hgjwf := hwfM.2 j gj hgj
        have hj2 : j = 2 := by
          rcases hreads with h1 | h2 <;> omega
        subst hj2
        have hgs2 : gs[2]? = some (permGate3 inv gj) := by dsimp only [gs]; rw [List.getElem?_map, hgj]; rfl
        rw [h] at hgs2; simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgs2
        rw [hgs2]
        dsimp only [permGate3]
        have hp4 : permWire3 inv 4 = 4 := by simp [permWire3]
        rcases hreads with h1 | h2
        · rw [h1, hp4]; split
          · exact Or.inr rfl
          · exact Or.inl rfl
        · rw [h2, hp4]; split
          · exact Or.inl rfl
          · exact Or.inr rfl
      have hg2_w2_eq4 : g2.w2 = 4 := by rcases hg2_uses_4 with h1 | h2 <;> omega
      have hused3 : g1.w1 == 3 || g1.w2 == 3 || g2.w1 == 3 || g2.w2 == 3 := by
        have hu0 := husedM 0 (by dsimp only [B2Circuit.size]; omega)
        rcases hu0 with ⟨j, gj, hgj, hreads⟩
        have hjlt : j < 3 := by
          by_cases hlt : j < 3
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hgj; cases hgj
        have hgjwf := hwfM.2 j gj hgj
        have hj12 : j = 1 ∨ j = 2 := by rcases hreads with h1 | h2 <;> omega
        have hp3 : permWire3 inv 3 = 3 := by simp [permWire3]
        rcases hj12 with rfl | rfl
        · have hgs1 : gs[1]? = some (permGate3 inv gj) := by dsimp only [gs]; rw [List.getElem?_map, hgj]; rfl
          rw [h] at hgs1; simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgs1
          rw [hgs1]; dsimp only [permGate3]
          by_cases hlt : permWire3 inv gj.w2 < permWire3 inv gj.w1
          · simp only [hlt, ↓reduceIte]; rcases hreads with h1 | h1 <;> simp [h1, hp3]
          · simp only [hlt, ↓reduceIte]; rcases hreads with h1 | h1 <;> simp [h1, hp3]
        · have hgs2 : gs[2]? = some (permGate3 inv gj) := by dsimp only [gs]; rw [List.getElem?_map, hgj]; rfl
          rw [h] at hgs2; simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgs2
          rw [hgs2]; dsimp only [permGate3]
          by_cases hlt : permWire3 inv gj.w2 < permWire3 inv gj.w1
          · simp only [hlt, ↓reduceIte]; rcases hreads with h1 | h1 <;> simp [h1, hp3]
          · simp only [hlt, ↓reduceIte]; rcases hreads with h1 | h1 <;> simp [h1, hp3]
      have hmemT3 : (g1.w1, g1.w2, g2.w1, g2.w2) ∈ allTopos3 := by
        unfold allTopos3
        rw [List.mem_flatMap]
        refine ⟨(g1.w1, g1.w2), mem_pairsUpTo 4 g1.w1 g1.w2 ha1 hb1, ?_⟩
        have hle01 : pairLe (0, 1) (g1.w1, g1.w2) = true := by
          unfold pairLe; by_cases hlt : 1 < g1.w2 <;> simp [hlt] <;> omega
        simp only [hle01, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_filterMap]
        refine ⟨(g2.w1, g2.w2), mem_pairsUpTo 5 g2.w1 g2.w2 ha2 hb2, ?_⟩
        have hle12 : pairLe (g1.w1, g1.w2) (g2.w1, g2.w2) = true := by
          unfold pairLe; have : g1.w2 < g2.w2 := by omega
          simp [this]
        have hu4 : (g2.w1 == 4 || g2.w2 == 4) = true := by simp [hg2_w2_eq4]
        simp [hle12, hused3, hu4]
      have hw3 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 3 false) =
          TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1 := by
        rw [← tt3Of_x0, ← tt3Of_x1, ← tt3Of_op g0.op hop0]
        exact congrArg tt3Of (funext fun x => by
          have := evalWires_gate x gs 0 ⟨g0.op, 0, 1⟩ (by rw [h]; rfl) (isNormGates_wf hnormP)
          rw [evalWires_input x gs (⟨0, by decide⟩ : Fin 3), evalWires_input x gs (⟨1, by decide⟩ : Fin 3)] at this
          exact this)
      let t3 := TT3.evalOp5 (opToNat5 g0.op) TT3.x0 TT3.x1
      have hget3 : ∀ idx, idx < 4 →
          tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
            getW3 TT3.x0 TT3.x1 TT3.x2 t3 TT3.zero TT3.zero idx := by
        intro idx hidx
        match idx with
        | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
               rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
        | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
               rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
        | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
               rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
        | 3 => exact hw3
      let t4 := TT3.evalOp5 (opToNat5 g1.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 t3 TT3.zero TT3.zero g1.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 t3 TT3.zero TT3.zero g1.w2)
      have hw4 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 4 false) = t4 := by
        dsimp only [t4]
        rw [← hget3 g1.w1 (by omega), ← hget3 g1.w2 (by omega), ← tt3Of_op g1.op hop1]
        exact congrArg tt3Of (funext fun x => evalWires_gate x gs 1 g1 (by rw [h]; rfl) (isNormGates_wf hnormP))
      have hget4 : ∀ idx, idx < 5 →
          tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
            getW3 TT3.x0 TT3.x1 TT3.x2 t3 t4 TT3.zero idx := by
        intro idx hidx
        match idx with
        | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
               rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
        | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
               rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
        | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
               rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
        | 3 => exact hw3
        | 4 => exact hw4
      have hw5_maj : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 5 false) = TT3.maj3 := by
        rw [← tt3Of_maj3]; exact congrArg tt3Of (funext fun x => by have := hev_out x; rw [h3] at this; exact this)
      have htt5 : TT3.evalOp5 (opToNat5 g2.op)
          (getW3 TT3.x0 TT3.x1 TT3.x2 t3 t4 TT3.zero g2.w1)
          (getW3 TT3.x0 TT3.x1 TT3.x2 t3 t4 TT3.zero g2.w2) = TT3.maj3 := by
        rw [← hget4 g2.w1 (by omega), ← hget4 g2.w2 (by omega), ← tt3Of_op g2.op hop2]
        have hstep : (fun x : BoolVec 3 => g2.op.eval ((B2Circuit.evalWires x gs).getD g2.w1 false)
            ((B2Circuit.evalWires x gs).getD g2.w2 false)) =
            (fun x : BoolVec 3 => (B2Circuit.evalWires x gs).getD 5 false) := by
          funext x; exact (evalWires_gate x gs 2 g2 (by change gs[2]? = _; rw [h]; rfl) (isNormGates_wf hnormP)).symm
        rw [hstep, hw5_maj]
      have hchk := List.all_eq_true.1 no_maj3_3_check (g1.w1, g1.w2, g2.w1, g2.w2) hmemT3
      unfold checkTopo3 at hchk
      have hmem5 : ∀ k, k < 5 → k ∈ [0, 1, 2, 3, 4] := by
        intro k hk; match k with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
      have h0 := List.all_eq_true.1 hchk (opToNat5 g0.op) (hmem5 _ (opToNat5_lt _))
      have h1 := List.all_eq_true.1 h0 (opToNat5 g1.op) (hmem5 _ (opToNat5_lt _))
      have h2 := List.all_eq_true.1 h1 (opToNat5 g2.op) (hmem5 _ (opToNat5_lt _))
      simp only [t3, t4] at htt5
      rw [htt5] at h2; exact absurd h2 (by decide)

/-! ## 7. 4-Gate `MAJ_3` Perturbed Evaluation, Topological Sort, & `th24_lb` -/

-- Abstract specification of a 4-gate normalized circuit + 2-gate perturbation
private def MaskValid (a0 b0 a1 b1 a2 b2 a3 b3 w : Nat) (m : Mask8) : Prop :=
  (m.s0a = true → a0 = w) ∧ (m.s0b = true → b0 = w) ∧
  (m.s1a = true → a1 = w) ∧ (m.s1b = true → b1 = w) ∧
  (m.s2a = true → a2 = w) ∧ (m.s2b = true → b2 = w) ∧
  (m.s3a = true → a3 = w) ∧ (m.s3b = true → b3 = w)

private theorem mem_submasks8_of_valid (a1 b1 a2 b2 a3 b3 w : Nat) (m : Mask8)
    (hv : MaskValid 0 1 a1 b1 a2 b2 a3 b3 w m) :
    m ∈ submasks8 (slotsOf4 a1 b1 a2 b2 a3 b3 w) := by
  have hgen : ∀ (l : List Nat) (cur : Mask8), cur ∈ submasks8 l →
      ∀ b, (b ∈ l → cur.setBit b ∈ submasks8 l) := by
    intro l
    induction l with
    | nil => intro _ _ _ hb; cases hb
    | cons x xs ih =>
      intro cur hcur b hb
      simp only [submasks8, List.mem_append, List.mem_map] at hcur ⊢
      rcases List.mem_cons.1 hb with rfl | hb'
      · rcases hcur with h1 | ⟨m', hm', rfl⟩
        · exact Or.inr ⟨cur, h1, rfl⟩
        · right; refine ⟨m', hm', ?_⟩
          cases m'; match b with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | _ + 7 => rfl
      · rcases hcur with h1 | ⟨m', hm', rfl⟩
        · exact Or.inl (ih cur h1 b hb')
        · right; refine ⟨m'.setBit b, ih m' hm' b hb', ?_⟩
          cases m'
          match x, b with
          | 0, 0 => rfl | 0, 1 => rfl | 0, 2 => rfl | 0, 3 => rfl | 0, 4 => rfl | 0, 5 => rfl | 0, 6 => rfl | 0, _+7 => rfl
          | 1, 0 => rfl | 1, 1 => rfl | 1, 2 => rfl | 1, 3 => rfl | 1, 4 => rfl | 1, 5 => rfl | 1, 6 => rfl | 1, _+7 => rfl
          | 2, 0 => rfl | 2, 1 => rfl | 2, 2 => rfl | 2, 3 => rfl | 2, 4 => rfl | 2, 5 => rfl | 2, 6 => rfl | 2, _+7 => rfl
          | 3, 0 => rfl | 3, 1 => rfl | 3, 2 => rfl | 3, 3 => rfl | 3, 4 => rfl | 3, 5 => rfl | 3, 6 => rfl | 3, _+7 => rfl
          | 4, 0 => rfl | 4, 1 => rfl | 4, 2 => rfl | 4, 3 => rfl | 4, 4 => rfl | 4, 5 => rfl | 4, 6 => rfl | 4, _+7 => rfl
          | 5, 0 => rfl | 5, 1 => rfl | 5, 2 => rfl | 5, 3 => rfl | 5, 4 => rfl | 5, 5 => rfl | 5, 6 => rfl | 5, _+7 => rfl
          | 6, 0 => rfl | 6, 1 => rfl | 6, 2 => rfl | 6, 3 => rfl | 6, 4 => rfl | 6, 5 => rfl | 6, 6 => rfl | 6, _+7 => rfl
          | _+7, 0 => rfl | _+7, 1 => rfl | _+7, 2 => rfl | _+7, 3 => rfl | _+7, 4 => rfl | _+7, 5 => rfl | _+7, 6 => rfl | _+7, _+7 => rfl
  have hempty : ∀ l, Mask8.empty ∈ submasks8 l := by
    intro l; induction l with | nil => exact List.mem_cons_self | cons _ _ ih => exact List.mem_append.2 (Or.inl ih)
  let L := slotsOf4 a1 b1 a2 b2 a3 b3 w
  have hstep : ∀ (b : Bool) (k : Nat) (cur : Mask8), cur ∈ submasks8 L → (b = true → k ∈ L) →
      (if b then cur.setBit k else cur) ∈ submasks8 L := by
    intro b k cur hc hk; cases b
    · exact hc
    · exact hgen L cur hc k (hk rfl)
  have hmem_slot : ∀ (k lhs : Nat), lhs = w →
      (k = 0 ∧ lhs = 0) ∨ (k = 1 ∧ lhs = 1) ∨ (k = 2 ∧ lhs = a1) ∨ (k = 3 ∧ lhs = b1) ∨
      (k = 4 ∧ lhs = a2) ∨ (k = 5 ∧ lhs = b2) ∨ (k = 6 ∧ lhs = a3) ∨ (k = 7 ∧ lhs = b3) → k ∈ L := by
    intro k lhs hlw hcase
    dsimp only [L, slotsOf4]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hlw]
  rcases m with ⟨s0a, s0b, s1a, s1b, s2a, s2b, s3a, s3b⟩
  have h0 : Mask8.empty ∈ submasks8 L := hempty L
  have h1 := hstep s0a 0 _ h0 (fun h => hmem_slot 0 0 (hv.1 h) (Or.inl ⟨rfl, rfl⟩))
  have h2 := hstep s0b 1 _ h1 (fun h => hmem_slot 1 1 (hv.2.1 h) (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h3 := hstep s1a 2 _ h2 (fun h => hmem_slot 2 a1 (hv.2.2.1 h) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have h4 := hstep s1b 3 _ h3 (fun h => hmem_slot 3 b1 (hv.2.2.2.1 h) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  have h5 := hstep s2a 4 _ h4 (fun h => hmem_slot 4 a2 (hv.2.2.2.2.1 h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  have h6 := hstep s2b 5 _ h5 (fun h => hmem_slot 5 b2 (hv.2.2.2.2.2.1 h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  have h7 := hstep s3a 6 _ h6 (fun h => hmem_slot 6 a3 (hv.2.2.2.2.2.2.1 h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  have h8 := hstep s3b 7 _ h7 (fun h => hmem_slot 7 b3 (hv.2.2.2.2.2.2.2 h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))))
  -- Direct case split on the 8 booleans without wildcards:
  have hfinal : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
      (let t0 := if b0 then Mask8.empty.setBit 0 else Mask8.empty
       let t1 := if b1 then t0.setBit 1 else t0
       let t2 := if b2 then t1.setBit 2 else t1
       let t3 := if b3 then t2.setBit 3 else t2
       let t4 := if b4 then t3.setBit 4 else t3
       let t5 := if b5 then t4.setBit 5 else t4
       let t6 := if b6 then t5.setBit 6 else t5
       if b7 then t6.setBit 7 else t6) = Mask8.mk b0 b1 b2 b3 b4 b5 b6 b7 := by
    decide
  rw [← hfinal s0a s0b s1a s1b s2a s2b s3a s3b]
  exact h8

-- Clean general 4-gate perturbed circuit bundle (before sorting g1, g2, g3!)
private structure FourGateLift where
  g0 : B2Gate
  g1 : B2Gate
  g2 : B2Gate
  g3 : B2Gate
  x2 : Nat
  g0Mode : Nat
  u : Nat
  uMode : Nat
  m0 : Mask8
  m1 : Mask8
  outFlip : Bool -- true iff Case A where g_p was output gate flipping final output

private def FourGateLift.evalBase (L : FourGateLift) : TT3 :=
  let w3 := TT3.evalOp5 (opToNat5 L.g0.op)
    (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1)
    (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2)
  let w4 := TT3.evalOp5 (opToNat5 L.g1.op)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w1)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w2)
  let w5 := TT3.evalOp5 (opToNat5 L.g2.op)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2)
  TT3.evalOp5 (opToNat5 L.g3.op)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1)
    (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2)

private def FourGateLift.evalPert (L : FourGateLift) : TT3 :=
  let g0v := match L.g0Mode with
    | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.x2).not
  let pick (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
    if b0 then g0v
    else if b1 then
      match L.uMode with
      | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.u).not
    else cur
  let v0a := pick L.m0.s0a L.m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1) TT3.zero TT3.zero TT3.zero
  let v0b := pick L.m0.s0b L.m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) TT3.zero TT3.zero TT3.zero
  let w3 := TT3.evalOp5 (opToNat5 L.g0.op) v0a v0b
  let v1a := pick L.m0.s1a L.m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w1) w3 TT3.zero TT3.zero
  let v1b := pick L.m0.s1b L.m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w2) w3 TT3.zero TT3.zero
  let w4 := TT3.evalOp5 (opToNat5 L.g1.op) v1a v1b
  let v2a := pick L.m0.s2a L.m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1) w3 w4 TT3.zero
  let v2b := pick L.m0.s2b L.m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2) w3 w4 TT3.zero
  let w5 := TT3.evalOp5 (opToNat5 L.g2.op) v2a v2b
  let v3a := pick L.m0.s3a L.m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1) w3 w4 w5
  let v3b := pick L.m0.s3b L.m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2) w3 w4 w5
  let raw := TT3.evalOp5 (opToNat5 L.g3.op) v3a v3b
  if L.outFlip then raw.not else raw

private def FourGateLift.valid (L : FourGateLift) : Prop :=
  IsNormGates 3 [L.g0, L.g1, L.g2, L.g3] ∧
  L.x2 < 3 ∧ L.g0Mode < 3 ∧ L.u < 6 ∧ L.uMode < 3 ∧
  MaskValid L.g0.w1 L.g0.w2 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 L.x2 L.m0 ∧
  MaskValid L.g0.w1 L.g0.w2 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 L.u L.m1 ∧
  L.m0.disjoint L.m1 = true ∧
  (L.outFlip = true → L.m1 = Mask8.empty) ∧
  L.evalBase = TT3.maj3 ∧
  L.evalPert = TT3.or3

-- Any valid FourGateLift MUST use wires 2, 3, 4, 5 (otherwise maj3 would be computed by <= 3 gates!)
private theorem fourGateLift_uses_all (L : FourGateLift) (hv : L.valid) :
    (L.g0.w1 == 2 || L.g0.w2 == 2 || L.g1.w1 == 2 || L.g1.w2 == 2 || L.g2.w1 == 2 || L.g2.w2 == 2 || L.g3.w1 == 2 || L.g3.w2 == 2) = true ∧
    (L.g1.w1 == 3 || L.g1.w2 == 3 || L.g2.w1 == 3 || L.g2.w2 == 3 || L.g3.w1 == 3 || L.g3.w2 == 3) = true ∧
    (L.g2.w1 == 4 || L.g2.w2 == 4 || L.g3.w1 == 4 || L.g3.w2 == 4) = true ∧
    (L.g3.w1 == 5 || L.g3.w2 == 5) = true := by
  let gs := [L.g0, L.g1, L.g2, L.g3]
  have hnorm := hv.1
  have hbase : ∀ x : BoolVec 3, (B2Circuit.evalWires x gs).getD 6 false = PnP.maj3 x := by
    -- Relate evalWires to L.evalBase via tt3Of
    have h0 := hnorm 0 L.g0 rfl
    have h1 := hnorm 1 L.g1 rfl
    have h2 := hnorm 2 L.g2 rfl
    have h3 := hnorm 3 L.g3 rfl
    have ht3 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 3 false) =
        TT3.evalOp5 (opToNat5 L.g0.op)
          (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1)
          (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) := by
      have hg : ∀ idx, idx < 3 → tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
          getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero idx := by
        intro idx hi; match idx with
        | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
               rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
        | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
               rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
        | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
               rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
      rw [← hg L.g0.w1 (by omega), ← hg L.g0.w2 (by omega), ← tt3Of_op L.g0.op h0.2.2]
      exact congrArg tt3Of (funext fun x => evalWires_gate x gs 0 L.g0 rfl (isNormGates_wf hnorm))
    let w3 := TT3.evalOp5 (opToNat5 L.g0.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2)
    have hget3 : ∀ idx, idx < 4 → tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
        getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero idx := by
      intro idx hi; match idx with
      | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
             rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
      | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
             rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
      | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
             rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
      | 3 => exact ht3
    let w4 := TT3.evalOp5 (opToNat5 L.g1.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w2)
    have ht4 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 4 false) = w4 := by
      dsimp only [w4]
      rw [← hget3 L.g1.w1 (by omega), ← hget3 L.g1.w2 (by omega), ← tt3Of_op L.g1.op h1.2.2]
      exact congrArg tt3Of (funext fun x => evalWires_gate x gs 1 L.g1 rfl (isNormGates_wf hnorm))
    have hget4 : ∀ idx, idx < 5 → tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
        getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero idx := by
      intro idx hi; match idx with
      | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
             rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
      | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
             rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
      | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
             rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
      | 3 => exact ht3
      | 4 => exact ht4
    let w5 := TT3.evalOp5 (opToNat5 L.g2.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2)
    have ht5 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 5 false) = w5 := by
      dsimp only [w5]
      rw [← hget4 L.g2.w1 (by omega), ← hget4 L.g2.w2 (by omega), ← tt3Of_op L.g2.op h2.2.2]
      exact congrArg tt3Of (funext fun x => evalWires_gate x gs 2 L.g2 rfl (isNormGates_wf hnorm))
    have hget5 : ∀ idx, idx < 6 → tt3Of (fun x => (B2Circuit.evalWires x gs).getD idx false) =
        getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 idx := by
      intro idx hi; match idx with
      | 0 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 0 false) = TT3.x0
             rw [← tt3Of_x0]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨0, by decide⟩)
      | 1 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 1 false) = TT3.x1
             rw [← tt3Of_x1]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨1, by decide⟩)
      | 2 => change tt3Of (fun x => (B2Circuit.evalWires x gs).getD 2 false) = TT3.x2
             rw [← tt3Of_x2]; exact congrArg tt3Of (funext fun x => evalWires_input x gs ⟨2, by decide⟩)
      | 3 => exact ht3
      | 4 => exact ht4
      | 5 => exact ht5
    have ht6 : tt3Of (fun x => (B2Circuit.evalWires x gs).getD 6 false) = TT3.maj3 := by
      rw [← hv.2.2.2.2.2.2.2.2.2.1]
      dsimp only [FourGateLift.evalBase]
      rw [← hget5 L.g3.w1 (by omega), ← hget5 L.g3.w2 (by omega), ← tt3Of_op L.g3.op h3.2.2]
      exact congrArg tt3Of (funext fun x => evalWires_gate x gs 3 L.g3 rfl (isNormGates_wf hnorm))
    intro x
    have hx : x = vec3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    rw [hx]
    cases x ⟨0, by decide⟩ <;> cases x ⟨1, by decide⟩ <;> cases x ⟨2, by decide⟩
    · exact congrArg TT3.b0 ht6
    · exact congrArg TT3.b4 ht6
    · exact congrArg TT3.b2 ht6
    · exact congrArg TT3.b6 ht6
    · exact congrArg TT3.b1 ht6
    · exact congrArg TT3.b5 ht6
    · exact congrArg TT3.b3 ht6
    · exact congrArg TT3.b7 ht6
  have hwfC : WF 3 ⟨gs, 6⟩ := ⟨by simp [gs], isNormGates_wf hnorm⟩
  have hcompC : ComputesUpToNeg ⟨gs, 6⟩ PnP.maj3 :=
    ⟨false, fun x => by dsimp only [B2Circuit.eval]; rw [hbase x, Bool.xor_false]⟩
  have hdel_contra : ∀ k, k < 3 → (∀ (j : Nat) (g : B2Gate), gs[j]? = some g → g.w1 ≠ 3 + k ∧ g.w2 ≠ 3 + k) → False := by
    intro k hk hall
    obtain ⟨hwf', hlen', hev'⟩ := deleteGate_props ⟨gs, 6⟩ k hwfC (by simp [gs]; omega) (by dsimp only; omega) hall
    have hcomp' : ComputesUpToNeg (deleteGate 3 ⟨gs, 6⟩ k) PnP.maj3 :=
      ⟨false, fun x => by rw [hev' x]; dsimp only [B2Circuit.eval]; rw [hbase x, Bool.xor_false]⟩
    have hlb' := maj3_lb (deleteGate 3 ⟨gs, 6⟩ k) hwf' hcomp'
    dsimp only [B2Circuit.size, gs] at hlen' hlb'
    simp at hlen'
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Wire 2 must be used (maj3 depends on x2!)
    cases hu : (L.g0.w1 == 2 || L.g0.w2 == 2 || L.g1.w1 == 2 || L.g1.w2 == 2 ||
        L.g2.w1 == 2 || L.g2.w2 == 2 || L.g3.w1 == 2 || L.g3.w2 == 2)
    · exfalso
      have hne2 : ∀ (j : Nat) (g : B2Gate), gs[j]? = some g → g.w1 ≠ 2 ∧ g.w2 ≠ 2 := by
        intro j g hgj
        match j with
        | 0 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
        | 1 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
        | 2 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
        | 3 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
        | _ + 4 => simp [gs] at hgj
      have heq_w : ∀ w, w < 7 → w ≠ 2 →
          (B2Circuit.evalWires (vec3 true false false) gs).getD w false =
          (B2Circuit.evalWires (vec3 true false true) gs).getD w false := by
        intro w
        induction w using Nat.strongRecOn with
        | ind w ih =>
          intro hw h2
          by_cases hlt : w < 3
          · rw [evalWires_input _ gs ⟨w, hlt⟩, evalWires_input _ gs ⟨w, hlt⟩]
            match w, hlt with | 0, _ => rfl | 1, _ => rfl | 2, _ => exact absurd rfl h2
          · let j := w - 3
            have hwj : w = 3 + j := by omega
            have hjlt : j < 4 := by omega
            have hgj : gs[j]? = some (gs[j]) := List.getElem?_eq_getElem (by simp [gs]; exact hjlt)
            have hgw := (isNormGates_wf hnorm) j _ hgj
            have hn2 := hne2 j _ hgj
            rw [hwj, evalWires_gate _ gs j _ hgj (isNormGates_wf hnorm),
                evalWires_gate _ gs j _ hgj (isNormGates_wf hnorm),
                ih _ (by omega) (by omega) hn2.1, ih _ (by omega) (by omega) hn2.2]
      have h6 := heq_w 6 (by decide) (by decide)
      rw [hbase, hbase] at h6
      exact absurd h6 (by decide)
    · rfl
  · cases hu : (L.g1.w1 == 3 || L.g1.w2 == 3 || L.g2.w1 == 3 || L.g2.w2 == 3 || L.g3.w1 == 3 || L.g3.w2 == 3)
    · exfalso; apply hdel_contra 0 (by decide)
      intro j g hgj
      match j with
      | 0 => simp [gs] at hgj; subst hgj; have := hnorm 0 L.g0 rfl; omega
      | 1 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | 2 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | 3 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | _ + 4 => simp [gs] at hgj
    · rfl
  · cases hu : (L.g2.w1 == 4 || L.g2.w2 == 4 || L.g3.w1 == 4 || L.g3.w2 == 4)
    · exfalso; apply hdel_contra 1 (by decide)
      intro j g hgj
      match j with
      | 0 => simp [gs] at hgj; subst hgj; have := hnorm 0 L.g0 rfl; omega
      | 1 => simp [gs] at hgj; subst hgj; have := hnorm 1 L.g1 rfl; omega
      | 2 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | 3 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | _ + 4 => simp [gs] at hgj
    · rfl
  · cases hu : (L.g3.w1 == 5 || L.g3.w2 == 5)
    · exfalso; apply hdel_contra 2 (by decide)
      intro j g hgj
      match j with
      | 0 => simp [gs] at hgj; subst hgj; have := hnorm 0 L.g0 rfl; omega
      | 1 => simp [gs] at hgj; subst hgj; have := hnorm 1 L.g1 rfl; omega
      | 2 => simp [gs] at hgj; subst hgj; have := hnorm 2 L.g2 rfl; omega
      | 3 => simp [gs] at hgj; subst hgj; constructor <;> intro h <;> simp [h] at hu
      | _ + 4 => simp [gs] at hgj
    · rfl

-- Any valid FourGateLift with g0=(0,1) AND sorted (g1 <= g2 <= g3) contradicts `no_maj3_4_lift_check`!
private theorem fourGateLift_sorted_false (L : FourGateLift) (hv : L.valid)
    (hg0 : L.g0.w1 = 0 ∧ L.g0.w2 = 1)
    (hs12 : pairLe (L.g1.w1, L.g1.w2) (L.g2.w1, L.g2.w2) = true)
    (hs23 : pairLe (L.g2.w1, L.g2.w2) (L.g3.w1, L.g3.w2) = true) : False := by
  obtain ⟨hu2, hu3, hu4, hu5⟩ := fourGateLift_uses_all L hv
  have hnorm := hv.1
  obtain ⟨h1a, h1b, _⟩ := hnorm 1 L.g1 rfl
  obtain ⟨h2a, h2b, _⟩ := hnorm 2 L.g2 rfl
  obtain ⟨h3a, h3b, _⟩ := hnorm 3 L.g3 rfl
  have hu2' : (L.g1.w1 == 2 || L.g1.w2 == 2 || L.g2.w1 == 2 || L.g2.w2 == 2 || L.g3.w1 == 2 || L.g3.w2 == 2) = true := by
    rw [hg0.1, hg0.2] at hu2; exact hu2
  have hmemT : (L.g1.w1, L.g1.w2, L.g2.w1, L.g2.w2, L.g3.w1, L.g3.w2) ∈ allTopos4 := by
    unfold allTopos4
    rw [List.mem_flatMap]
    refine ⟨(L.g1.w1, L.g1.w2), mem_pairsUpTo 4 _ _ h1a h1b, ?_⟩
    have h01 : pairLe (0, 1) (L.g1.w1, L.g1.w2) = true := by
      unfold pairLe; by_cases hlt : 1 < L.g1.w2 <;> simp [hlt] <;> omega
    simp only [h01, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
    refine ⟨(L.g2.w1, L.g2.w2), mem_pairsUpTo 5 _ _ h2a h2b, ?_⟩
    simp only [hs12, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_filterMap]
    refine ⟨(L.g3.w1, L.g3.w2), mem_pairsUpTo 6 _ _ h3a h3b, ?_⟩
    simp [hs23, hu2', hu3, hu4, hu5]
  have hchk := List.all_eq_true.1 no_maj3_4_lift_check _ hmemT
  unfold checkTopo4 at hchk
  have hmem5 : ∀ k, k < 5 → k ∈ [0, 1, 2, 3, 4] := by
    intro k hk; match k with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  have h0 := List.all_eq_true.1 hchk (opToNat5 L.g0.op) (hmem5 _ (opToNat5_lt _))
  have h1 := List.all_eq_true.1 h0 (opToNat5 L.g1.op) (hmem5 _ (opToNat5_lt _))
  have h2 := List.all_eq_true.1 h1 (opToNat5 L.g2.op) (hmem5 _ (opToNat5_lt _))
  have h3 := List.all_eq_true.1 h2 (opToNat5 L.g3.op) (hmem5 _ (opToNat5_lt _))
  have hbase : L.evalBase = TT3.maj3 := hv.2.2.2.2.2.2.2.2.2.1
  dsimp only [FourGateLift.evalBase] at hbase
  rw [hg0.1, hg0.2] at hbase
  have h0x : getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero 0 = TT3.x0 := rfl
  have h1x : getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero 1 = TT3.x1 := rfl
  rw [h0x, h1x] at hbase
  change (if _ == TT3.maj3 then checkLiftOne _ _ _ _ _ _ _ _ _ _ else true) = true at h3
  rw [hbase] at h3
  have hm_eq : (TT3.maj3 == TT3.maj3) = true := rfl
  simp only [hm_eq, ↓reduceIte] at h3
  unfold checkLiftOne at h3
  have hmem3 : ∀ k, k < 3 → k ∈ [0, 1, 2] := by
    intro k hk; match k with | 0 => decide | 1 => decide | 2 => decide
  have hmem6 : ∀ k, k < 6 → k ∈ [0, 1, 2, 3, 4, 5] := by
    intro k hk; match k with | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide | 5 => decide
  have hx2_chk := List.all_eq_true.1 h3 L.x2 (hmem3 _ hv.2.1)
  have hm0_valid : MaskValid 0 1 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 L.x2 L.m0 := by
    have := hv.2.2.2.2.2.1; rw [hg0.1, hg0.2] at this; exact this
  have hm0_chk := List.all_eq_true.1 hx2_chk L.m0 (mem_submasks8_of_valid _ _ _ _ _ _ _ _ hm0_valid)
  have hg0m_chk := List.all_eq_true.1 hm0_chk L.g0Mode (hmem3 _ hv.2.2.1)
  rcases Bool.and_eq_true_iff.1 hg0m_chk with ⟨hCaseA, hCaseB⟩
  have hpert : L.evalPert = TT3.or3 := hv.2.2.2.2.2.2.2.2.2.2
  unfold FourGateLift.evalPert at hpert
  rw [hg0.1, hg0.2] at hpert
  by_cases hm1_emp : L.m1 = Mask8.empty
  · -- Case A: m1 = empty (covers both outFlip = true and outFlip = false!)
    rw [hm1_emp] at hpert
    have heqA : evalPert4 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2
        (opToNat5 L.g0.op) (opToNat5 L.g1.op) (opToNat5 L.g2.op) (opToNat5 L.g3.op)
        L.x2 L.m0 L.g0Mode 0 Mask8.empty 0 =
        (if L.outFlip then TT3.or3.not else TT3.or3) := by
      cases hfl : L.outFlip
      · rw [hfl] at hpert; exact hpert
      · rw [hfl] at hpert
        have hnot_inv : ∀ a : TT3, a.not = TT3.or3 → a = TT3.or3.not := by
          intro a ha
          have hnn : a.not.not = a := by rcases a with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩; simp [TT3.not]
          rw [← hnn, ha]
        exact hnot_inv _ hpert
    cases hfl : L.outFlip <;> (rw [hfl] at heqA; rw [heqA] at hCaseA; exact absurd hCaseA (by decide))
  · -- Case B: m1 != empty (hence outFlip = false!)
    have hfl : L.outFlip = false := by
      cases hf : L.outFlip
      · rfl
      · exact absurd (hv.2.2.2.2.2.2.2.2.1 hf) hm1_emp
    rw [hfl] at hpert
    simp only [Bool.false_eq_true, ↓reduceIte] at hpert
    have hu_chk := List.all_eq_true.1 hCaseB L.u (hmem6 _ hv.2.2.2.1)
    have hm1_valid : MaskValid 0 1 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 L.u L.m1 := by
      have := hv.2.2.2.2.2.2.1; rw [hg0.1, hg0.2] at this; exact this
    have hm1_chk := List.all_eq_true.1 hu_chk L.m1 (mem_submasks8_of_valid _ _ _ _ _ _ _ _ hm1_valid)
    have hne_emp : (L.m1 == Mask8.empty) = false := by
      cases hm : (L.m1 == Mask8.empty)
      · rfl
      · exfalso; apply hm1_emp
        have hbeq : ∀ a : Mask8, (a == Mask8.empty) = true → a = Mask8.empty := by
          intro a ha
          rcases a with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
          revert ha
          cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
            cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide
        exact hbeq L.m1 hm
    have hdisj : L.m0.disjoint L.m1 = true := hv.2.2.2.2.2.2.2.1
    simp only [hne_emp, hdisj, Bool.not_true, Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hm1_chk
    have hum_chk := List.all_eq_true.1 hm1_chk L.uMode (hmem3 _ hv.2.2.2.2.1)
    change evalPert4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = TT3.or3 at hpert
    rw [hpert] at hum_chk; exact absurd hum_chk (by decide)

-- Swap g1 and g2 in a FourGateLift when g2.w2 < 4 (so g2 does NOT read wire 4!)
private def swapMask12 (m : Mask8) (sw3 : Bool) : Mask8 :=
  ⟨m.s0a, m.s0b, m.s2a, m.s2b, m.s1a, m.s1b,
   if sw3 then m.s3b else m.s3a, if sw3 then m.s3a else m.s3b⟩

private def FourGateLift.swap12 (L : FourGateLift) : FourGateLift :=
  let sw3 := decide (swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1)
  { L with
    g1 := L.g2
    g2 := L.g1
    g3 := remapGateSwap 4 5 L.g3
    u := swapIdx 4 5 L.u
    m0 := swapMask12 L.m0 sw3
    m1 := swapMask12 L.m1 sw3 }

private theorem swap12_valid (L : FourGateLift) (hv : L.valid) (h12 : pairLe (L.g1.w1, L.g1.w2) (L.g2.w1, L.g2.w2) = false) :
    L.swap12.valid ∧ pairLe (L.swap12.g1.w1, L.swap12.g1.w2) (L.swap12.g2.w1, L.swap12.g2.w2) = true := by
  have hnorm := hv.1
  obtain ⟨h0a, h0b, hop0⟩ := hnorm 0 L.g0 rfl
  obtain ⟨h1a, h1b, hop1⟩ := hnorm 1 L.g1 rfl
  obtain ⟨h2a, h2b, hop2⟩ := hnorm 2 L.g2 rfl
  obtain ⟨h3a, h3b, hop3⟩ := hnorm 3 L.g3 rfl
  have hg2_lt4 : L.g2.w2 < 4 := by
    unfold pairLe at h12
    by_cases hlt : L.g1.w2 < L.g2.w2
    · simp [hlt] at h12
    · omega
  have hpair_sw : pairLe (L.g2.w1, L.g2.w2) (L.g1.w1, L.g1.w2) = true := by
    unfold pairLe at h12 ⊢
    by_cases hlt : L.g2.w2 < L.g1.w2
    · simp [hlt]
    · by_cases heq : L.g2.w2 = L.g1.w2
      · simp [heq] at h12 ⊢; omega
      · have : L.g1.w2 < L.g2.w2 := by omega
        simp [this] at h12
  -- Key: sw3 = true iff g3.w1 = 4 ∧ g3.w2 = 5!
  let sw3 := decide (swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1)
  have hsw_spec : ∀ x, x < 6 → swapIdx 4 5 x < 6 := by
    intro x hx; unfold swapIdx; by_cases h4 : x = 4 <;> by_cases h5 : x = 5 <;> simp [h4, h5] <;> omega
  have hg3_norm : (remapGateSwap 4 5 L.g3).w1 < (remapGateSwap 4 5 L.g3).w2 ∧
      (remapGateSwap 4 5 L.g3).w2 < 6 ∧ (isNorm5 (remapGateSwap 4 5 L.g3).op) = true := by
    dsimp only [remapGateSwap]
    have hne : swapIdx 4 5 L.g3.w1 ≠ swapIdx 4 5 L.g3.w2 := fun h => by
      have := congrArg (swapIdx 4 5) h; rw [swapIdx_invol, swapIdx_invol] at this; omega
    split
    · dsimp only; exact ⟨‹_›, hsw_spec _ (by omega), isNorm5_swapIn _ hop3⟩
    · dsimp only; exact ⟨by omega, hsw_spec _ h3b, hop3⟩
  have hnorm' : IsNormGates 3 [L.g0, L.g2, L.g1, remapGateSwap 4 5 L.g3] := by
    intro i g hgi
    match i with
    | 0 => simp at hgi; subst hgi; exact ⟨h0a, h0b, hop0⟩
    | 1 => simp at hgi; subst hgi; exact ⟨h2a, hg2_lt4, hop2⟩
    | 2 => simp at hgi; subst hgi; exact ⟨h1a, by omega, hop1⟩
    | 3 => simp at hgi; subst hgi; exact hg3_norm
    | _ + 4 => simp at hgi
  have hsw_op : ∀ a b : TT3,
      TT3.evalOp5 (opToNat5 (remapGateSwap 4 5 L.g3).op)
        (if sw3 then b else a) (if sw3 then a else b) =
      TT3.evalOp5 (opToNat5 L.g3.op) a b := by
    intro a b
    dsimp only [remapGateSwap, sw3]
    by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
    · simp only [hlt, decide_true, ↓reduceIte]
      have h5 := opOfNat5_toNat5 L.g3.op hop3
      have h5s := opOfNat5_toNat5 (b2SwapIn L.g3.op) (isNorm5_swapIn _ hop3)
      rcases L.g3.op with ⟨c00, c01, c10, c11⟩
      cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;>
        simp_all [isNorm5, b2SwapIn, opToNat5, TT3.evalOp5,
          B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor] <;>
        rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ <;> rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩ <;>
        simp [Bool.and_comm, Bool.or_comm, Bool.xor_comm]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hget_swap : ∀ (w0 w1 w2 w3 w4 w5 : TT3) (idx : Nat), idx < 6 →
      getW3 w0 w1 w2 w3 w5 w4 (swapIdx 4 5 idx) = getW3 w0 w1 w2 w3 w4 w5 idx := by
    intro w0 w1 w2 w3 w4 w5 idx hidx
    match idx with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl
  have hget_lt4 : ∀ (w0 w1 w2 w3 a b c d : TT3) (idx : Nat), idx < 4 →
      getW3 w0 w1 w2 w3 a b idx = getW3 w0 w1 w2 w3 c d idx := by
    intro _ _ _ _ _ _ _ _ idx hidx
    match idx with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  have hbase' : L.swap12.evalBase = L.evalBase := by
    dsimp only [FourGateLift.evalBase, FourGateLift.swap12]
    let w3 := TT3.evalOp5 (opToNat5 L.g0.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2)
    let w4 := TT3.evalOp5 (opToNat5 L.g1.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w2)
    let w5 := TT3.evalOp5 (opToNat5 L.g2.op)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g2.w1)
      (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g2.w2)
    have hw5eq : TT3.evalOp5 (opToNat5 L.g2.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2) = w5 := by
      dsimp only [w5]
      rw [hget_lt4 _ _ _ _ w4 TT3.zero TT3.zero TT3.zero L.g2.w1 (by omega),
          hget_lt4 _ _ _ _ w4 TT3.zero TT3.zero TT3.zero L.g2.w2 hg2_lt4]
    have hw4eq : TT3.evalOp5 (opToNat5 L.g1.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w2) = w4 := by
      dsimp only [w4]
      rw [hget_lt4 _ _ _ _ w5 TT3.zero TT3.zero TT3.zero L.g1.w1 (by omega),
          hget_lt4 _ _ _ _ w5 TT3.zero TT3.zero TT3.zero L.g1.w2 h1b]
    change TT3.evalOp5 (opToNat5 (remapGateSwap 4 5 L.g3).op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5
          (TT3.evalOp5 (opToNat5 L.g1.op) (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w1)
            (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w2)) (remapGateSwap 4 5 L.g3).w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5
          (TT3.evalOp5 (opToNat5 L.g1.op) (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w1)
            (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w2)) (remapGateSwap 4 5 L.g3).w2) =
      TT3.evalOp5 (opToNat5 L.g3.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4
          (TT3.evalOp5 (opToNat5 L.g2.op) (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1)
            (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2)) L.g3.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4
          (TT3.evalOp5 (opToNat5 L.g2.op) (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1)
            (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2)) L.g3.w2)
    rw [hw4eq, hw5eq]
    have ha : getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w1 =
        if sw3 then getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2
        else getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1 := by
      dsimp only [remapGateSwap, sw3]
      by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
      · simp only [hlt, decide_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ h3b
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ (by omega)
    have hb : getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w2 =
        if sw3 then getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1
        else getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2 := by
      dsimp only [remapGateSwap, sw3]
      by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
      · simp only [hlt, decide_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ (by omega)
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ h3b
    rw [ha, hb, hsw_op]
  -- Similarly evalPert is preserved!
  have hpert' : L.swap12.evalPert = L.evalPert := by
    have hm1v := hv.2.2.2.2.2.2.1
    -- Note: if L.m1.s2a or L.m1.s2b is true, then L.u = L.g2.w1 or L.g2.w2 < 4, so swapIdx 4 5 L.u = L.u < 4!
    -- Similarly if L.m1.s1a or L.m1.s1b is true, L.u < 4!
    have hsw_u_lt4 : ∀ x, x < 4 → swapIdx 4 5 x = x := by
      intro x hx; unfold swapIdx; have h4 : (x == 4) = false := beq_false_of_ne (by omega)
      have h5 : (x == 5) = false := beq_false_of_ne (by omega); simp [h4, h5]
    dsimp only [FourGateLift.evalPert, FourGateLift.swap12, swapMask12]
    let g0v := match L.g0Mode with
      | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.x2).not
    let pickL (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
      if b0 then g0v
      else if b1 then
        match L.uMode with
        | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.u).not
      else cur
    let pickR (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
      if b0 then g0v
      else if b1 then
        match L.uMode with
        | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 (swapIdx 4 5 L.u)).not
      else cur
    have hpick_lt4 : ∀ b0 b1 cur w3 a b c d, (b1 = true → L.u < 4) →
        pickR b0 b1 cur w3 a b = pickL b0 b1 cur w3 c d := by
      intro b0 b1 cur w3 a b c d hu4
      dsimp only [pickR, pickL]
      cases b0
      · cases b1
        · rfl
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hlt := hu4 rfl
          rw [hsw_u_lt4 L.u hlt, hget_lt4 _ _ _ _ a b c d L.u hlt]
      · rfl
    have hpick_sw : ∀ b0 b1 cur w3 w4 w5,
        pickR b0 b1 cur w3 w5 w4 = pickL b0 b1 cur w3 w4 w5 := by
      intro b0 b1 cur w3 w4 w5
      dsimp only [pickR, pickL]
      cases b0
      · cases b1
        · rfl
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hget_swap _ _ _ _ _ _ L.u hv.2.2.2.1]
      · rfl
    -- Step 0: w3 is identical
    have hw3_eq : TT3.evalOp5 (opToNat5 L.g0.op)
        (pickR L.m0.s0a L.m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1) TT3.zero TT3.zero TT3.zero)
        (pickR L.m0.s0b L.m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) TT3.zero TT3.zero TT3.zero) =
      TT3.evalOp5 (opToNat5 L.g0.op)
        (pickL L.m0.s0a L.m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1) TT3.zero TT3.zero TT3.zero)
        (pickL L.m0.s0b L.m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) TT3.zero TT3.zero TT3.zero) := by
      rw [hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.1 h; omega),
          hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.2.1 h; omega)]
    let w3 := TT3.evalOp5 (opToNat5 L.g0.op)
      (pickL L.m0.s0a L.m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1) TT3.zero TT3.zero TT3.zero)
      (pickL L.m0.s0b L.m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) TT3.zero TT3.zero TT3.zero)
    let w4 := TT3.evalOp5 (opToNat5 L.g1.op)
      (pickL L.m0.s1a L.m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w1) w3 TT3.zero TT3.zero)
      (pickL L.m0.s1b L.m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g1.w2) w3 TT3.zero TT3.zero)
    let w5 := TT3.evalOp5 (opToNat5 L.g2.op)
      (pickL L.m0.s2a L.m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w1) w3 w4 TT3.zero)
      (pickL L.m0.s2b L.m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero L.g2.w2) w3 w4 TT3.zero)
    have hw5_eq : TT3.evalOp5 (opToNat5 L.g2.op)
        (pickR L.m0.s2a L.m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g2.w1) w3 TT3.zero TT3.zero)
        (pickR L.m0.s2b L.m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero L.g2.w2) w3 TT3.zero TT3.zero) = w5 := by
      dsimp only [w5]
      rw [hget_lt4 _ _ _ _ TT3.zero TT3.zero w4 TT3.zero L.g2.w1 (by omega),
          hget_lt4 _ _ _ _ TT3.zero TT3.zero w4 TT3.zero L.g2.w2 hg2_lt4,
          hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.2.2.2.2.1 h; omega),
          hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.2.2.2.2.2.1 h; omega)]
    have hw4_eq : TT3.evalOp5 (opToNat5 L.g1.op)
        (pickR L.m0.s1a L.m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w1) w3 w5 TT3.zero)
        (pickR L.m0.s1b L.m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 TT3.zero L.g1.w2) w3 w5 TT3.zero) = w4 := by
      dsimp only [w4]
      rw [hget_lt4 _ _ _ _ w5 TT3.zero TT3.zero TT3.zero L.g1.w1 (by omega),
          hget_lt4 _ _ _ _ w5 TT3.zero TT3.zero TT3.zero L.g1.w2 h1b,
          hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.2.2.1 h; omega),
          hpick_lt4 _ _ _ _ _ _ _ _ (fun h => by have := hm1v.2.2.2.1 h; omega)]
    -- Now gate 3!
    have hraw : TT3.evalOp5 (opToNat5 (remapGateSwap 4 5 L.g3).op)
        (pickR (if sw3 then L.m0.s3b else L.m0.s3a) (if sw3 then L.m1.s3b else L.m1.s3a)
          (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w1) w3 w5 w4)
        (pickR (if sw3 then L.m0.s3a else L.m0.s3b) (if sw3 then L.m1.s3a else L.m1.s3b)
          (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w2) w3 w5 w4) =
      TT3.evalOp5 (opToNat5 L.g3.op)
        (pickL L.m0.s3a L.m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1) w3 w4 w5)
        (pickL L.m0.s3b L.m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2) w3 w4 w5) := by
      rw [hpick_sw, hpick_sw]
      have ha : getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w1 =
          if sw3 then getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2
          else getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1 := by
        dsimp only [remapGateSwap, sw3]
        by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
        · simp only [hlt, decide_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ h3b
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ (by omega)
      have hb : getW3 TT3.x0 TT3.x1 TT3.x2 w3 w5 w4 (remapGateSwap 4 5 L.g3).w2 =
          if sw3 then getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1
          else getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2 := by
        dsimp only [remapGateSwap, sw3]
        by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
        · simp only [hlt, decide_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ (by omega)
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hget_swap _ _ _ _ _ _ _ h3b
      rw [ha, hb]
      cases hsw : sw3
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have := hsw_op (pickL L.m0.s3a L.m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1) w3 w4 w5)
                       (pickL L.m0.s3b L.m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2) w3 w4 w5)
        rw [hsw] at this; exact this
      · simp only [↓reduceIte]
        have := hsw_op (pickL L.m0.s3a L.m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1) w3 w4 w5)
                       (pickL L.m0.s3b L.m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2) w3 w4 w5)
        rw [hsw] at this; exact this
    -- Assemble into L.swap12.evalPert = L.evalPert
    change (if L.outFlip then
      (TT3.evalOp5 (opToNat5 (remapGateSwap 4 5 L.g3).op)
        (pickR (if sw3 then L.m0.s3b else L.m0.s3a) (if sw3 then L.m1.s3b else L.m1.s3a)
          (getW3 TT3.x0 TT3.x1 TT3.x2 _ _ _ (remapGateSwap 4 5 L.g3).w1) _ _ _)
        (pickR (if sw3 then L.m0.s3a else L.m0.s3b) (if sw3 then L.m1.s3a else L.m1.s3b)
          (getW3 TT3.x0 TT3.x1 TT3.x2 _ _ _ (remapGateSwap 4 5 L.g3).w2) _ _ _)).not else _) =
           (if L.outFlip then
      (TT3.evalOp5 (opToNat5 L.g3.op)
        (pickL L.m0.s3a L.m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w1) w3 w4 w5)
        (pickL L.m0.s3b L.m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.g3.w2) w3 w4 w5)).not else _)
    rw [hw3_eq, hw5_eq, hw4_eq, hraw]
  have hmv_map : ∀ (w : Nat) (m : Mask8),
      MaskValid L.g0.w1 L.g0.w2 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 w m →
      MaskValid L.g0.w1 L.g0.w2 L.g2.w1 L.g2.w2 L.g1.w1 L.g1.w2
        (remapGateSwap 4 5 L.g3).w1 (remapGateSwap 4 5 L.g3).w2 (swapIdx 4 5 w) (swapMask12 m sw3) := by
    intro w m hm
    have hsw_lt4 : ∀ y, y < 4 → swapIdx 4 5 y = y := by
      intro y hy; unfold swapIdx; have h4 : (y == 4) = false := beq_false_of_ne (by omega)
      have h5 : (y == 5) = false := beq_false_of_ne (by omega); simp [h4, h5]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; have := hm.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; have := hm.2.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; have := hm.2.2.2.2.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; have := hm.2.2.2.2.2.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; have := hm.2.2.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; have := hm.2.2.2.1 h; rw [← this, hsw_lt4 _ (by omega)]
    · intro h; dsimp only [remapGateSwap, swapMask12, sw3] at h ⊢
      by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
      · simp only [hlt, decide_true, ↓reduceIte] at h ⊢; rw [hm.2.2.2.2.2.2.2 h]
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [hm.2.2.2.2.2.2.1 h]
    · intro h; dsimp only [remapGateSwap, swapMask12, sw3] at h ⊢
      by_cases hlt : swapIdx 4 5 L.g3.w2 < swapIdx 4 5 L.g3.w1
      · simp only [hlt, decide_true, ↓reduceIte] at h ⊢; rw [hm.2.2.2.2.2.2.1 h]
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [hm.2.2.2.2.2.2.2 h]
  have hx2_sw : swapIdx 4 5 L.x2 = L.x2 := by
    unfold swapIdx; have h4 : (L.x2 == 4) = false := beq_false_of_ne (by have := hv.2.1; omega)
    have h5 : (L.x2 == 5) = false := beq_false_of_ne (by have := hv.2.1; omega); simp [h4, h5]
  refine ⟨⟨hnorm', hv.2.1, hv.2.2.1, hsw_spec _ hv.2.2.2.1, hv.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpair_sw⟩
  · have := hmv_map L.x2 L.m0 hv.2.2.2.2.2.1; rwa [hx2_sw] at this
  · exact hmv_map L.u L.m1 hv.2.2.2.2.2.2.1
  · have hd := hv.2.2.2.2.2.2.2.1
    have hdisj_sw : ∀ (m0 m1 : Mask8) (sw : Bool), m0.disjoint m1 = true →
        (swapMask12 m0 sw).disjoint (swapMask12 m1 sw) = true := by
      intro m0 m1 sw hm
      simp only [Mask8.disjoint, swapMask12, Bool.and_eq_true] at hm ⊢
      cases sw <;> simp_all
    exact hdisj_sw L.m0 L.m1 sw3 hd
  · intro hfl; have h1 := hv.2.2.2.2.2.2.2.2.1 hfl; dsimp only [FourGateLift.swap12]; rw [h1]
    have hemp_sw : ∀ sw : Bool, swapMask12 Mask8.empty sw = Mask8.empty := by decide
    exact hemp_sw sw3
  · rw [hbase', hv.2.2.2.2.2.2.2.2.2.1]
  · rw [hpert', hv.2.2.2.2.2.2.2.2.2.2]

-- Notice: in ANY valid FourGateLift, g3 MUST read wire 5 (from fourGateLift_uses_all!), so g3.w2 = 5!
-- Since g2.w2 <= 4 < 5 = g3.w2, `pairLe (g2.w1, g2.w2) (g3.w1, g3.w2) = true` AUTOMATICALLY!
-- So AT MOST ONE swap (`swap12`) sorts ANY FourGateLift with g0=(0,1)!!
private theorem fourGateLift_g0_01_false (L : FourGateLift) (hv : L.valid)
    (hg0 : L.g0.w1 = 0 ∧ L.g0.w2 = 1) : False := by
  have hs23 : ∀ (L' : FourGateLift), L'.valid → pairLe (L'.g2.w1, L'.g2.w2) (L'.g3.w1, L'.g3.w2) = true := by
    intro L' hv'
    obtain ⟨_, _, _, hu5⟩ := fourGateLift_uses_all L' hv'
    obtain ⟨_, h2b, _⟩ := hv'.1 2 L'.g2 rfl
    obtain ⟨h3a, h3b, _⟩ := hv'.1 3 L'.g3 rfl
    have hg3w2 : L'.g3.w2 = 5 := by
      rcases Bool.or_eq_true_iff.1 hu5 with h1 | h2
      · have := beq_iff_eq.1 h1; omega
      · exact beq_iff_eq.1 h2
    unfold pairLe
    have : L'.g2.w2 < L'.g3.w2 := by omega
    simp [this]
  cases h12 : pairLe (L.g1.w1, L.g1.w2) (L.g2.w1, L.g2.w2)
  · obtain ⟨hv', h12'⟩ := swap12_valid L hv h12
    exact fourGateLift_sorted_false L.swap12 hv' hg0 h12' (hs23 L.swap12 hv')
  · exact fourGateLift_sorted_false L hv hg0 h12 (hs23 L hv)

-- S_3 permutation on FourGateLift to bring g0 to (0, 1)!
private theorem fourGateLift_false (L : FourGateLift) (hv : L.valid) : False := by
  obtain ⟨h0a, h0b, _⟩ := hv.1 0 L.g0 rfl
  let p := perm3For L.g0.w1 L.g0.w2
  let inv := perm3Inv L.g0.w1 L.g0.w2
  obtain ⟨hpinv, hinvp, hp0, hp1, hmajP, horP⟩ := perm3_props L.g0.w1 L.g0.w2 h0a h0b
  -- Permute TT3 via perm3Inv: tt3Of (f ∘ inv)
  let permTT3 (t : TT3) : TT3 :=
    let evalT (x : BoolVec 3) : Bool :=
      match x ⟨0, by decide⟩, x ⟨1, by decide⟩, x ⟨2, by decide⟩ with
      | false, false, false => t.b0 | true, false, false => t.b1
      | false, true, false  => t.b2 | true, true, false  => t.b3
      | false, false, true  => t.b4 | true, false, true  => t.b5
      | false, true, true   => t.b6 | true, true, true   => t.b7
    tt3Of (fun x => evalT (fun i => x (inv i)))
  have hperm_op : ∀ (op : Nat) (a b : TT3),
      permTT3 (TT3.evalOp5 op a b) = TT3.evalOp5 op (permTT3 a) (permTT3 b) := by
    intro op a b
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    all_goals
      dsimp only [permTT3, inv]; rw [ha, hb]; dsimp only [perm3Inv]
      match op with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _ + 4 => rfl
  have hperm_not : ∀ (a : TT3), permTT3 a.not = (permTT3 a).not := by
    intro a
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> (dsimp only [permTT3, inv]; rw [ha, hb]; dsimp only [perm3Inv]; rfl)
  have hperm_zero : permTT3 TT3.zero = TT3.zero := by
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> (dsimp only [permTT3, inv]; rw [ha, hb]; dsimp only [perm3Inv]; rfl)
  have hperm_one : permTT3 TT3.one = TT3.one := by
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> (dsimp only [permTT3, inv]; rw [ha, hb]; dsimp only [perm3Inv]; rfl)
  have hperm_maj3 : permTT3 TT3.maj3 = TT3.maj3 := by
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> (dsimp only [permTT3, inv]; rw [ha, hb]; decide)
  have hperm_or3 : permTT3 TT3.or3 = TT3.or3 := by
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> (dsimp only [permTT3, inv]; rw [ha, hb]; decide)
  have hperm_inp : ∀ (w3 w4 w5 : TT3) (idx : Nat), idx < 6 →
      getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permWire3 inv idx) =
      permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 idx) := by
    intro w3 w4 w5 idx hidx
    have hcases : (L.g0.w1 = 0 ∧ L.g0.w2 = 1) ∨ (L.g0.w1 = 0 ∧ L.g0.w2 = 2) ∨ (L.g0.w1 = 1 ∧ L.g0.w2 = 2) := by omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    all_goals
      match idx with
      | 0 => dsimp only [permTT3, permWire3, inv, getW3]; rw [ha, hb]; dsimp only [perm3Inv]; rfl
      | 1 => dsimp only [permTT3, permWire3, inv, getW3]; rw [ha, hb]; dsimp only [perm3Inv]; rfl
      | 2 => dsimp only [permTT3, permWire3, inv, getW3]; rw [ha, hb]; dsimp only [perm3Inv]; rfl
      | 3 => rfl
      | 4 => rfl
      | 5 => rfl
  let swG (g : B2Gate) : Bool := decide (permWire3 inv g.w2 < permWire3 inv g.w1)
  let permMask (m : Mask8) : Mask8 :=
    ⟨if swG L.g0 then m.s0b else m.s0a, if swG L.g0 then m.s0a else m.s0b,
     if swG L.g1 then m.s1b else m.s1a, if swG L.g1 then m.s1a else m.s1b,
     if swG L.g2 then m.s2b else m.s2a, if swG L.g2 then m.s2a else m.s2b,
     if swG L.g3 then m.s3b else m.s3a, if swG L.g3 then m.s3a else m.s3b⟩
  let L' : FourGateLift :=
    { g0 := permGate3 inv L.g0
      g1 := permGate3 inv L.g1
      g2 := permGate3 inv L.g2
      g3 := permGate3 inv L.g3
      x2 := permWire3 inv L.x2
      g0Mode := L.g0Mode
      u := permWire3 inv L.u
      uMode := L.uMode
      m0 := permMask L.m0
      m1 := permMask L.m1
      outFlip := L.outFlip }
  have hg0' : L'.g0.w1 = 0 ∧ L'.g0.w2 = 1 := by
    dsimp only [L', permGate3]; rw [hp0, hp1]; simp
  have hnorm' : IsNormGates 3 [L'.g0, L'.g1, L'.g2, L'.g3] := by
    exact (eval_permGate3 p inv hpinv hinvp [L.g0, L.g1, L.g2, L.g3] hv.1).1
  have hsw_op : ∀ (g : B2Gate), (isNorm5 g.op) = true → ∀ a b : TT3,
      TT3.evalOp5 (opToNat5 (permGate3 inv g).op)
        (if swG g then b else a) (if swG g then a else b) =
      TT3.evalOp5 (opToNat5 g.op) a b := by
    intro g hop a b
    dsimp only [permGate3, swG]
    by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
    · simp only [hlt, decide_true, ↓reduceIte]
      rcases g.op with ⟨c00, c01, c10, c11⟩
      cases c00 <;> cases c01 <;> cases c10 <;> cases c11 <;>
        simp_all [isNorm5, b2SwapIn, opToNat5, TT3.evalOp5,
          B2Op.opAnd, B2Op.opAndNot, B2Op.opNotAnd, B2Op.opOr, B2Op.opXor] <;>
        rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ <;> rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩ <;>
        simp [Bool.and_comm, Bool.or_comm, Bool.xor_comm]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hgate_step : ∀ (g : B2Gate) (w3 w4 w5 : TT3),
      (isNorm5 g.op) = true → g.w1 < 6 → g.w2 < 6 →
      TT3.evalOp5 (opToNat5 (permGate3 inv g).op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w2) =
      permTT3 (TT3.evalOp5 (opToNat5 g.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2)) := by
    intro g w3 w4 w5 hop hw1 hw2
    rw [hperm_op]
    have h1 : getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w1 =
        if swG g then permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2)
        else permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1) := by
      dsimp only [permGate3, swG]
      by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
      · simp only [hlt, decide_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w2 hw2
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w1 hw1
    have h2 : getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w2 =
        if swG g then permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1)
        else permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2) := by
      dsimp only [permGate3, swG]
      by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
      · simp only [hlt, decide_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w1 hw1
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w2 hw2
    rw [h1, h2, hsw_op g hop]
  have hbase' : L'.evalBase = TT3.maj3 := by
    obtain ⟨h0a, h0b, hop0⟩ := hv.1 0 L.g0 rfl
    obtain ⟨h1a, h1b, hop1⟩ := hv.1 1 L.g1 rfl
    obtain ⟨h2a, h2b, hop2⟩ := hv.1 2 L.g2 rfl
    obtain ⟨h3a, h3b, hop3⟩ := hv.1 3 L.g3 rfl
    have heq : L'.evalBase = permTT3 L.evalBase := by
      dsimp only [FourGateLift.evalBase, L']
      conv => lhs; rw [← hperm_zero]
      rw [hgate_step L.g0 _ _ _ hop0 (by omega) (by omega),
          hgate_step L.g1 _ _ _ hop1 (by omega) (by omega),
          hgate_step L.g2 _ _ _ hop2 (by omega) (by omega),
          hgate_step L.g3 _ _ _ hop3 (by omega) (by omega)]
    rw [heq, hv.2.2.2.2.2.2.2.2.2.1, hperm_maj3]
  have hpert' : L'.evalPert = TT3.or3 := by
    obtain ⟨h0a, h0b, hop0⟩ := hv.1 0 L.g0 rfl
    obtain ⟨h1a, h1b, hop1⟩ := hv.1 1 L.g1 rfl
    obtain ⟨h2a, h2b, hop2⟩ := hv.1 2 L.g2 rfl
    obtain ⟨h3a, h3b, hop3⟩ := hv.1 3 L.g3 rfl
    let g0v := match L.g0Mode with
      | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.x2).not
    let g0v' := match L.g0Mode with
      | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero (permWire3 inv L.x2)).not
    have hg0v_eq : g0v' = permTT3 g0v := by
      dsimp only [g0v, g0v']
      match L.g0Mode with
      | 0 => exact hperm_zero.symm
      | 1 => exact hperm_one.symm
      | _ + 2 =>
        change (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero (permWire3 inv L.x2)).not =
               permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.x2).not
        rw [hperm_not]; congr 1
        conv => lhs; rw [← hperm_zero]
        exact hperm_inp TT3.zero TT3.zero TT3.zero L.x2 (by have := hv.2.1; omega)
    let pickL (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
      if b0 then g0v else if b1 then
        match L.uMode with | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.u).not
      else cur
    let pickR (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
      if b0 then g0v' else if b1 then
        match L.uMode with | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 (permWire3 inv L.u)).not
      else cur
    have hpick_eq : ∀ b0 b1 cur w3 w4 w5,
        pickR b0 b1 (permTT3 cur) (permTT3 w3) (permTT3 w4) (permTT3 w5) =
        permTT3 (pickL b0 b1 cur w3 w4 w5) := by
      intro b0 b1 cur w3 w4 w5
      dsimp only [pickR, pickL]
      cases b0
      · cases b1
        · rfl
        · simp only [Bool.false_eq_true, ↓reduceIte]
          match L.uMode with
          | 0 => exact hperm_zero.symm
          | 1 => exact hperm_one.symm
          | _ + 2 =>
            change (getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permWire3 inv L.u)).not =
                   permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.u).not
            rw [hperm_not]; congr 1; exact hperm_inp w3 w4 w5 L.u hv.2.2.2.1
      · exact hg0v_eq
    have hpert_step : ∀ (g : B2Gate) (b0a b0b b1a b1b : Bool) (w3 w4 w5 : TT3),
        (isNorm5 g.op) = true → g.w1 < 6 → g.w2 < 6 →
        TT3.evalOp5 (opToNat5 (permGate3 inv g).op)
          (pickR (if swG g then b0b else b0a) (if swG g then b1b else b1a)
            (getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w1)
            (permTT3 w3) (permTT3 w4) (permTT3 w5))
          (pickR (if swG g then b0a else b0b) (if swG g then b1a else b1b)
            (getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w2)
            (permTT3 w3) (permTT3 w4) (permTT3 w5)) =
        permTT3 (TT3.evalOp5 (opToNat5 g.op)
          (pickL b0a b1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1) w3 w4 w5)
          (pickL b0b b1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2) w3 w4 w5)) := by
      intro g b0a b0b b1a b1b w3 w4 w5 hop hw1 hw2
      rw [hperm_op]
      have h1 : getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w1 =
          if swG g then permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2)
          else permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1) := by
        dsimp only [permGate3, swG]
        by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
        · simp only [hlt, decide_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w2 hw2
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w1 hw1
      have h2 : getW3 TT3.x0 TT3.x1 TT3.x2 (permTT3 w3) (permTT3 w4) (permTT3 w5) (permGate3 inv g).w2 =
          if swG g then permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1)
          else permTT3 (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2) := by
        dsimp only [permGate3, swG]
        by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
        · simp only [hlt, decide_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w1 hw1
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hperm_inp w3 w4 w5 g.w2 hw2
      rw [h1, h2]
      cases hsw : swG g
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hpick_eq, hpick_eq]
        have := hsw_op g hop (permTT3 (pickL b0a b1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1) w3 w4 w5))
                             (permTT3 (pickL b0b b1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2) w3 w4 w5))
        rw [hsw] at this; exact this
      · simp only [↓reduceIte]
        rw [hpick_eq, hpick_eq]
        have := hsw_op g hop (permTT3 (pickL b0a b1a (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w1) w3 w4 w5))
                             (permTT3 (pickL b0b b1b (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 g.w2) w3 w4 w5))
        rw [hsw] at this; exact this
    have heq : L'.evalPert = permTT3 L.evalPert := by
      let lw3 := TT3.evalOp5 (opToNat5 L.g0.op)
        (pickL L.m0.s0a L.m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w1) TT3.zero TT3.zero TT3.zero)
        (pickL L.m0.s0b L.m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero L.g0.w2) TT3.zero TT3.zero TT3.zero)
      let lw4 := TT3.evalOp5 (opToNat5 L.g1.op)
        (pickL L.m0.s1a L.m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 lw3 TT3.zero TT3.zero L.g1.w1) lw3 TT3.zero TT3.zero)
        (pickL L.m0.s1b L.m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 lw3 TT3.zero TT3.zero L.g1.w2) lw3 TT3.zero TT3.zero)
      let lw5 := TT3.evalOp5 (opToNat5 L.g2.op)
        (pickL L.m0.s2a L.m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 lw3 lw4 TT3.zero L.g2.w1) lw3 lw4 TT3.zero)
        (pickL L.m0.s2b L.m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 lw3 lw4 TT3.zero L.g2.w2) lw3 lw4 TT3.zero)
      have hs0 := hpert_step L.g0 L.m0.s0a L.m0.s0b L.m1.s0a L.m1.s0b TT3.zero TT3.zero TT3.zero hop0 (by omega) (by omega)
      have hs1 := hpert_step L.g1 L.m0.s1a L.m0.s1b L.m1.s1a L.m1.s1b lw3 TT3.zero TT3.zero hop1 (by omega) (by omega)
      have hs2 := hpert_step L.g2 L.m0.s2a L.m0.s2b L.m1.s2a L.m1.s2b lw3 lw4 TT3.zero hop2 (by omega) (by omega)
      have hs3 := hpert_step L.g3 L.m0.s3a L.m0.s3b L.m1.s3a L.m1.s3b lw3 lw4 lw5 hop3 (by omega) (by omega)
      rw [hperm_zero] at hs0 hs1 hs2
      dsimp only [pickR, pickL, g0v', g0v] at hs0 hs1 hs2 hs3
      dsimp only [FourGateLift.evalPert, L', permMask]
      cases L.outFlip
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hs0, hs1, hs2, hs3]
      · simp only [↓reduceIte]
        rw [hperm_not]; congr 1
        rw [hs0, hs1, hs2, hs3]
    rw [heq, hv.2.2.2.2.2.2.2.2.2.2, hperm_or3]
  have hmv_perm : ∀ (w : Nat) (m : Mask8),
      MaskValid L.g0.w1 L.g0.w2 L.g1.w1 L.g1.w2 L.g2.w1 L.g2.w2 L.g3.w1 L.g3.w2 w m →
      MaskValid L'.g0.w1 L'.g0.w2 L'.g1.w1 L'.g1.w2 L'.g2.w1 L'.g2.w2 L'.g3.w1 L'.g3.w2 (permWire3 inv w) (permMask m) := by
    intro w m hm
    have hside : ∀ (g : B2Gate) (ba bb : Bool), (ba = true → g.w1 = w) → (bb = true → g.w2 = w) →
        ((if swG g then bb else ba) = true → (permGate3 inv g).w1 = permWire3 inv w) ∧
        ((if swG g then ba else bb) = true → (permGate3 inv g).w2 = permWire3 inv w) := by
      intro g ba bb ha hb
      dsimp only [permGate3, swG]
      by_cases hlt : permWire3 inv g.w2 < permWire3 inv g.w1
      · simp only [hlt, decide_true, ↓reduceIte]
        exact ⟨fun h => by rw [hb h], fun h => by rw [ha h]⟩
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun h => by rw [ha h], fun h => by rw [hb h]⟩
    obtain ⟨a0, b0⟩ := hside L.g0 m.s0a m.s0b hm.1 hm.2.1
    obtain ⟨a1, b1⟩ := hside L.g1 m.s1a m.s1b hm.2.2.1 hm.2.2.2.1
    obtain ⟨a2, b2⟩ := hside L.g2 m.s2a m.s2b hm.2.2.2.2.1 hm.2.2.2.2.2.1
    obtain ⟨a3, b3⟩ := hside L.g3 m.s3a m.s3b hm.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.2
    exact ⟨a0, b0, a1, b1, a2, b2, a3, b3⟩
  have hpw3 : ∀ k, k < 3 → permWire3 inv k < 3 := by
    intro k hk; unfold permWire3; simp only [hk, ↓reduceDIte]; exact (inv ⟨k, hk⟩).isLt
  have hpw6 : ∀ k, k < 6 → permWire3 inv k < 6 := by
    intro k hk; unfold permWire3; split
    · rename_i h; have := (inv ⟨k, h⟩).isLt; omega
    · omega
  have hv' : L'.valid := by
    refine ⟨hnorm', hpw3 _ hv.2.1, hv.2.2.1, hpw6 _ hv.2.2.2.1, hv.2.2.2.2.1,
      hmv_perm L.x2 L.m0 hv.2.2.2.2.2.1, hmv_perm L.u L.m1 hv.2.2.2.2.2.2.1, ?_, ?_, hbase', hpert'⟩
    · have hd := hv.2.2.2.2.2.2.2.1
      have hdisj_p : ∀ (m0 m1 : Mask8) (s0 s1 s2 s3 : Bool), m0.disjoint m1 = true →
          (Mask8.mk (if s0 then m0.s0b else m0.s0a) (if s0 then m0.s0a else m0.s0b)
                    (if s1 then m0.s1b else m0.s1a) (if s1 then m0.s1a else m0.s1b)
                    (if s2 then m0.s2b else m0.s2a) (if s2 then m0.s2a else m0.s2b)
                    (if s3 then m0.s3b else m0.s3a) (if s3 then m0.s3a else m0.s3b)).disjoint
          (Mask8.mk (if s0 then m1.s0b else m1.s0a) (if s0 then m1.s0a else m1.s0b)
                    (if s1 then m1.s1b else m1.s1a) (if s1 then m1.s1a else m1.s1b)
                    (if s2 then m1.s2b else m1.s2a) (if s2 then m1.s2a else m1.s2b)
                    (if s3 then m1.s3b else m1.s3a) (if s3 then m1.s3a else m1.s3b)) = true := by
        intro m0 m1 s0 s1 s2 s3 hm
        simp only [Mask8.disjoint, Bool.and_eq_true] at hm ⊢
        cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> simp_all
      exact hdisj_p L.m0 L.m1 (swG L.g0) (swG L.g1) (swG L.g2) (swG L.g3) hd
    · intro hfl; have h1 := hv.2.2.2.2.2.2.2.2.1 hfl; dsimp only [L']; rw [h1]
      have hemp_p : ∀ s0 s1 s2 s3 : Bool,
          Mask8.mk (if s0 then Mask8.empty.s0b else Mask8.empty.s0a) (if s0 then Mask8.empty.s0a else Mask8.empty.s0b)
                   (if s1 then Mask8.empty.s1b else Mask8.empty.s1a) (if s1 then Mask8.empty.s1a else Mask8.empty.s1b)
                   (if s2 then Mask8.empty.s2b else Mask8.empty.s2a) (if s2 then Mask8.empty.s2a else Mask8.empty.s2b)
                   (if s3 then Mask8.empty.s3b else Mask8.empty.s3a) (if s3 then Mask8.empty.s3a else Mask8.empty.s3b) =
          Mask8.empty := by decide
      exact hemp_p (swG L.g0) (swG L.g1) (swG L.g2) (swG L.g3)
  exact fourGateLift_g0_01_false L' hv' hg0'

/-! ## 8. Middle Reduction (`th24_lb`: `C_{B2}(TH_2^4) ≥ 7`) & Main Theorem (`¬ Record 8`) -/

private theorem th24_insert_false (idx : Fin 4) (x : BoolVec 3) :
    th24 (insertBit x idx false) = PnP.maj3 x := by
  have hx : x = vec3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) := by
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  have h : ∀ (idx : Fin 4) (a b c : Bool),
      th24 (insertBit (vec3 a b c) idx false) = PnP.maj3 (vec3 a b c) := by decide
  rw [hx]; exact h idx _ _ _

private theorem th24_insert_true (idx : Fin 4) (x : BoolVec 3) :
    th24 (insertBit x idx true) = or3 x := by
  have hx : x = vec3 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) := by
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  have h : ∀ (idx : Fin 4) (a b c : Bool),
      th24 (insertBit (vec3 a b c) idx true) = or3 (vec3 a b c) := by decide
  rw [hx]; exact h idx _ _ _

private theorem maj5_insert_true (idx : Fin 5) (x : BoolVec 4) :
    PnP.maj5 (insertBit x idx true) = th24 x := by
  let v4 (a b c d : Bool) : BoolVec 4 :=
    fun i => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d
  have hx : x = v4 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) := by
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  have h : ∀ (idx : Fin 5) (a b c d : Bool),
      PnP.maj5 (insertBit (v4 a b c d) idx true) = th24 (v4 a b c d) := by decide
  rw [hx]; exact h idx _ _ _ _

private theorem th24_three_cofactors (i1 i2 : Fin 4) (hne : i1 ≠ i2) :
    ∀ b1 b2 b3 : Bool,
      (b1 = b2 → ∃ x : BoolVec 4, th24 (setTwo x i1 i2 false false) ≠ th24 (setTwo x i1 i2 false true)) ∧
      (b1 = b3 → ∃ x : BoolVec 4, th24 (setTwo x i1 i2 false false) ≠ th24 (setTwo x i1 i2 true true)) ∧
      (b2 = b3 → ∃ x : BoolVec 4, th24 (setTwo x i1 i2 false true) ≠ th24 (setTwo x i1 i2 true true)) := by
  intro _ _ _
  have h1 : ∀ a b : Fin 4, a ≠ b →
      (List.finRange 4).any (fun j1 =>
        decide (j1 ≠ a ∧ j1 ≠ b) &&
        decide (th24 (setTwo (fun k => decide (k = j1)) a b false false) ≠
                th24 (setTwo (fun k => decide (k = j1)) a b false true))) = true := by
    decide
  have h2 : ∀ a b : Fin 4, a ≠ b →
      th24 (setTwo (fun _ => false) a b false false) ≠ th24 (setTwo (fun _ => false) a b true true) := by
    decide
  have h3 : ∀ a b : Fin 4, a ≠ b →
      th24 (setTwo (fun _ => false) a b false true) ≠ th24 (setTwo (fun _ => false) a b true true) := by
    decide
  refine ⟨fun _ => ?_, fun _ => ⟨fun _ => false, h2 i1 i2 hne⟩, fun _ => ⟨fun _ => false, h3 i1 i2 hne⟩⟩
  rcases List.any_eq_true.1 (h1 i1 i2 hne) with ⟨j1, _, h1'⟩
  exact ⟨fun k => decide (k = j1), of_decide_eq_true (Bool.and_eq_true_iff.1 h1').2⟩

private theorem maj5_three_cofactors (i1 i2 : Fin 5) (hne : i1 ≠ i2) :
    ∀ b1 b2 b3 : Bool,
      (b1 = b2 → ∃ x : BoolVec 5, PnP.maj5 (setTwo x i1 i2 false false) ≠ PnP.maj5 (setTwo x i1 i2 false true)) ∧
      (b1 = b3 → ∃ x : BoolVec 5, PnP.maj5 (setTwo x i1 i2 false false) ≠ PnP.maj5 (setTwo x i1 i2 true true)) ∧
      (b2 = b3 → ∃ x : BoolVec 5, PnP.maj5 (setTwo x i1 i2 false true) ≠ PnP.maj5 (setTwo x i1 i2 true true)) := by
  intro _ _ _
  -- Simply prove via finite decision over all 20 distinct pairs (i1, i2) : Fin 5!
  have h1 : ∀ a b : Fin 5, a ≠ b →
      (List.finRange 5).any (fun j1 =>
        (List.finRange 5).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (PnP.maj5 (setTwo (fun k => decide (k = j1 || k = j2)) a b false false) ≠
                  PnP.maj5 (setTwo (fun k => decide (k = j1 || k = j2)) a b false true)))) = true := by
    decide
  have h2 : ∀ a b : Fin 5, a ≠ b →
      (List.finRange 5).any (fun j1 =>
        decide (j1 ≠ a ∧ j1 ≠ b) &&
        decide (PnP.maj5 (setTwo (fun k => decide (k = j1)) a b false false) ≠
                PnP.maj5 (setTwo (fun k => decide (k = j1)) a b true true))) = true := by
    decide
  have h3 : ∀ a b : Fin 5, a ≠ b →
      (List.finRange 5).any (fun j1 =>
        decide (j1 ≠ a ∧ j1 ≠ b) &&
        decide (PnP.maj5 (setTwo (fun k => decide (k = j1)) a b false true) ≠
                PnP.maj5 (setTwo (fun k => decide (k = j1)) a b true true))) = true := by
    decide
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · rcases List.any_eq_true.1 (h1 i1 i2 hne) with ⟨j1, _, h1'⟩
    rcases List.any_eq_true.1 h1' with ⟨j2, _, h1''⟩
    exact ⟨fun k => decide (k = j1 || k = j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h1'').2⟩
  · rcases List.any_eq_true.1 (h2 i1 i2 hne) with ⟨j1, _, h2'⟩
    exact ⟨fun k => decide (k = j1), of_decide_eq_true (Bool.and_eq_true_iff.1 h2').2⟩
  · rcases List.any_eq_true.1 (h3 i1 i2 hne) with ⟨j1, _, h3'⟩
    exact ⟨fun k => decide (k = j1), of_decide_eq_true (Bool.and_eq_true_iff.1 h3').2⟩

private theorem maj5_nonTrivial : IsNonTrivial PnP.maj5 := by
  constructor
  · intro b; cases b
    · exact ⟨fun _ => true, by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  · intro i b
    have h : ∀ (i : Fin 5) (b : Bool),
        (PnP.maj5 (fun _ => false) != xor false b) ||
        (PnP.maj5 (fun j => decide (j = i)) != xor true b) = true := by decide
    rcases Bool.or_eq_true_iff.1 (h i b) with h1 | h2
    · exact ⟨fun _ => false, by simpa using h1⟩
    · exact ⟨fun j => decide (j = i), by simpa using h2⟩

-- Helper: extract the exact 2-gate perturbation FourGateLift from a 6-gate circuit for th24!
private def KeptInv (n' : Nat) (gs out : List B2Gate) (wmap : List WireRef) (dropped : List Bool) : Prop :=
  ∀ k g, gs[k]? = some g → dropped.getD k false = false →
    ∃ (oi : Nat) (g' : B2Gate) (u1 u2 : Nat) (f1 f2 p : Bool),
      oi = (dropped.take k).count false ∧
      out[oi]? = some g' ∧
      wmap.getD g.w1 (.const false) = .wire u1 f1 ∧
      wmap.getD g.w2 (.const false) = .wire u2 f2 ∧
      wmap.getD (4 + k) (.const false) = .wire (n' + oi) p ∧
      ((u1 < u2 ∧ g'.w1 = u1 ∧ g'.w2 = u2 ∧
          ∀ a b : Bool, xor (g'.op.eval a b) p = g.op.eval (xor a f1) (xor b f2)) ∨
       (u2 < u1 ∧ g'.w1 = u2 ∧ g'.w2 = u1 ∧
          ∀ a b : Bool, xor (g'.op.eval a b) p = g.op.eval (xor b f1) (xor a f2)))

private theorem compileAux_kept_spec (n' : Nat) :
    ∀ (pre gs : List B2Gate) (out : List B2Gate) (wmap : List WireRef) (dropped : List Bool),
      GatesWF 4 (pre ++ gs) →
      wmap.length = 4 + pre.length →
      dropped.length = pre.length →
      out.length = dropped.count false →
      KeptInv n' pre out wmap dropped →
      let res := compileAux n' out wmap dropped gs
      KeptInv n' (pre ++ gs) res.1 res.2.1 res.2.2
  | pre, [], out, wmap, dropped, _, _, _, _, hprev => by
    simp only [compileAux, List.append_nil]; exact hprev
  | pre, g0 :: gs, out, wmap, dropped, hwf, hwlen, hdlen, houtlen, hprev => by
    have hpre_step : pre ++ g0 :: gs = (pre ++ [g0]) ++ gs := by simp [List.append_assoc]
    have hwf_next : GatesWF 4 ((pre ++ [g0]) ++ gs) := hpre_step ▸ hwf
    have hg0_wf := hwf pre.length g0 (by simp)
    simp only [compileAux]
    cases hcg : compileGate n' out.length (wmap.getD g0.w1 (.const false))
        (wmap.getD g0.w2 (.const false)) g0.op with
    | mk mg ref =>
      cases mg with
      | none =>
        have hprev' : KeptInv n' (pre ++ [g0]) out (wmap ++ [ref]) (dropped ++ [true]) := by
          intro k g hkg hdk
          by_cases hlt : k < pre.length
          · rw [List.getElem?_append_left hlt] at hkg
            rw [list_getD_append_lt _ _ _ k (by omega)] at hdk
            obtain ⟨oi, g', u1, u2, f1, f2, p, hoi, houti, hw1, hw2, hwk, hsym⟩ := hprev k g hkg hdk
            have hgw := hwf k g (by rw [List.getElem?_append_left hlt]; exact hkg)
            refine ⟨oi, g', u1, u2, f1, f2, p, ?_, houti, ?_, ?_, ?_, hsym⟩
            · rw [List.take_append_of_le_length (by omega)]; exact hoi
            · rw [list_getD_append_lt _ _ _ g.w1 (by omega)]; exact hw1
            · rw [list_getD_append_lt _ _ _ g.w2 (by omega)]; exact hw2
            · rw [list_getD_append_lt _ _ _ (4 + k) (by omega)]; exact hwk
          · have heq : k = pre.length := by
              by_cases hle : k < (pre ++ [g0]).length
              · simp at hle; omega
              · rw [List.getElem?_eq_none (by omega)] at hkg; cases hkg
            subst heq
            rw [← hdlen, list_getD_append_eq] at hdk; cases hdk
        have hih := compileAux_kept_spec n' (pre ++ [g0]) gs out (wmap ++ [ref]) (dropped ++ [true])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) hprev'
        rwa [← hpre_step] at hih
      | some g' =>
        obtain ⟨u1, u2, f1, f2, p, hr1, hr2, _, href, hsym⟩ := compileGate_some_props n' out.length _ _ _ g' ref hcg
        have hprev' : KeptInv n' (pre ++ [g0]) (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false]) := by
          intro k g hkg hdk
          by_cases hlt : k < pre.length
          · rw [List.getElem?_append_left hlt] at hkg
            rw [list_getD_append_lt _ _ _ k (by omega)] at hdk
            obtain ⟨oi, g'', u1', u2', f1', f2', p', hoi, houti, hw1, hw2, hwk, hsym'⟩ := hprev k g hkg hdk
            have hgw := hwf k g (by rw [List.getElem?_append_left hlt]; exact hkg)
            have hoi_lt : oi < out.length := by
              by_cases h : oi < out.length
              · exact h
              · rw [List.getElem?_eq_none (by omega)] at houti; cases houti
            refine ⟨oi, g'', u1', u2', f1', f2', p', ?_, ?_, ?_, ?_, ?_, hsym'⟩
            · rw [List.take_append_of_le_length (by omega)]; exact hoi
            · rw [List.getElem?_append_left hoi_lt]; exact houti
            · rw [list_getD_append_lt _ _ _ g.w1 (by omega)]; exact hw1
            · rw [list_getD_append_lt _ _ _ g.w2 (by omega)]; exact hw2
            · rw [list_getD_append_lt _ _ _ (4 + k) (by omega)]; exact hwk
          · have heq : k = pre.length := by
              by_cases hle : k < (pre ++ [g0]).length
              · simp at hle; omega
              · rw [List.getElem?_eq_none (by omega)] at hkg; cases hkg
            subst heq
            simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem?_cons_zero, Option.some.injEq] at hkg
            subst hkg
            refine ⟨out.length, g', u1, u2, f1, f2, p, ?_, by simp, ?_, ?_, ?_, hsym⟩
            · rw [← hdlen, List.take_append_of_le_length (Nat.le_refl _), List.take_length, houtlen]
            · rw [list_getD_append_lt _ _ _ g0.w1 (by omega)]; exact hr1
            · rw [list_getD_append_lt _ _ _ g0.w2 (by omega)]; exact hr2
            · rw [← hwlen, list_getD_append_eq, href]
        have hih := compileAux_kept_spec n' (pre ++ [g0]) gs (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) hprev'
        rwa [← hpre_step] at hih

-- Exact output wireRef at step k of compileAux
private theorem compileAux_ref_eq (n' : Nat) :
    ∀ (pre gs : List B2Gate) (out : List B2Gate) (wmap : List WireRef) (dropped : List Bool),
      GatesWF 4 (pre ++ gs) →
      wmap.length = 4 + pre.length →
      dropped.length = pre.length →
      out.length = dropped.count false →
      (∀ k g, pre[k]? = some g →
        wmap.getD (4 + k) (.const false) =
          (compileGate n' ((dropped.take k).count false)
            (wmap.getD g.w1 (.const false)) (wmap.getD g.w2 (.const false)) g.op).2) →
      let res := compileAux n' out wmap dropped gs
      let wmap' := res.2.1
      let dropped' := res.2.2
      ∀ k g, (pre ++ gs)[k]? = some g →
        wmap'.getD (4 + k) (.const false) =
          (compileGate n' ((dropped'.take k).count false)
            (wmap'.getD g.w1 (.const false)) (wmap'.getD g.w2 (.const false)) g.op).2
  | pre, [], out, wmap, dropped, _, _, _, _, hprev => by
    simp only [compileAux, List.append_nil]; exact hprev
  | pre, g0 :: gs, out, wmap, dropped, hwf, hwlen, hdlen, houtlen, hprev => by
    have hpre_step : pre ++ g0 :: gs = (pre ++ [g0]) ++ gs := by simp [List.append_assoc]
    have hwf_next : GatesWF 4 ((pre ++ [g0]) ++ gs) := hpre_step ▸ hwf
    have hg0_wf := hwf pre.length g0 (by simp)
    simp only [compileAux]
    cases hcg : compileGate n' out.length (wmap.getD g0.w1 (.const false))
        (wmap.getD g0.w2 (.const false)) g0.op with
    | mk mg ref =>
      have hstep_prev : ∀ (b : Bool),
          ∀ k g, (pre ++ [g0])[k]? = some g →
            (wmap ++ [ref]).getD (4 + k) (.const false) =
              (compileGate n' (((dropped ++ [b]).take k).count false)
                ((wmap ++ [ref]).getD g.w1 (.const false))
                ((wmap ++ [ref]).getD g.w2 (.const false)) g.op).2 := by
        intro b k g hkg
        by_cases hlt : k < pre.length
        · rw [List.getElem?_append_left hlt] at hkg
          have hgw := hwf k g (by rw [List.getElem?_append_left hlt]; exact hkg)
          rw [list_getD_append_lt _ _ _ (4 + k) (by omega),
              list_getD_append_lt _ _ _ g.w1 (by omega),
              list_getD_append_lt _ _ _ g.w2 (by omega),
              List.take_append_of_le_length (by omega)]
          exact hprev k g hkg
        · have heq : k = pre.length := by
            by_cases hle : k < (pre ++ [g0]).length
            · simp at hle; omega
            · rw [List.getElem?_eq_none (by omega)] at hkg; cases hkg
          subst heq
          simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.some.injEq] at hkg
          subst hkg
          rw [← hwlen, list_getD_append_eq,
              list_getD_append_lt _ _ _ g0.w1 (by omega),
              list_getD_append_lt _ _ _ g0.w2 (by omega),
              ← hdlen, List.take_append_of_le_length (Nat.le_refl _),
              List.take_length, ← houtlen, hcg]
      cases mg with
      | none =>
        have hih := compileAux_ref_eq n' (pre ++ [g0]) gs out (wmap ++ [ref]) (dropped ++ [true])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) (hstep_prev true)
        rwa [← hpre_step] at hih
      | some g' =>
        have hih := compileAux_ref_eq n' (pre ++ [g0]) gs (out ++ [g']) (wmap ++ [ref]) (dropped ++ [false])
          hwf_next (by simp [hwlen]; omega) (by simp [hdlen])
          (by rw [countFalse_append]; simp [houtlen]) (hstep_prev false)
        rwa [← hpre_step] at hih

-- Classify any 1-bit Boolean function f : Bool → Bool as (changed, mode)
private theorem bool_fn_classify (f : Bool → Bool) :
    ∃ (changed : Bool) (mode : Nat), mode < 3 ∧
      (changed = false → ∀ b, f b = b) ∧
      (changed = true → ∀ b, f b = match mode with | 0 => false | 1 => true | _ => !b) := by
  cases h0 : f false <;> cases h1 : f true
  · exact ⟨true, 0, by decide, (fun h => by cases h), (fun _ b => by cases b <;> assumption)⟩
  · exact ⟨false, 0, by decide, (fun _ b => by cases b <;> assumption), (fun h => by cases h)⟩
  · exact ⟨true, 2, by decide, (fun h => by cases h), (fun _ b => by cases b <;> assumption)⟩
  · exact ⟨true, 1, by decide, (fun h => by cases h), (fun _ b => by cases b <;> assumption)⟩

private theorem th24_lb (c : B2Circuit 4) (hwf : WF 4 c) (hcomp : ComputesUpToNeg c th24) :
    7 ≤ c.size := by
  by_cases hge : 7 ≤ c.size
  · exact hge
  · exfalso
    have hle6 : c.size ≤ 6 := by omega
    obtain ⟨cm, hwfM, hnormM, hszM, hposM, houtM, hcompM, _, husedM⟩ :=
      exists_minimal_norm th24_nonTrivial ⟨c, hwf, hle6, hcomp⟩
    -- Gate 0 reads two distinct inputs i1 < i2 < 4
    have hg0_ex : ∃ g0, cm.gates[0]? = some g0 := by
      cases h : cm.gates with
      | nil => simp [B2Circuit.size, h] at hposM
      | cons g0 _ => exact ⟨g0, rfl⟩
    obtain ⟨g0, hg0⟩ := hg0_ex
    obtain ⟨hg0_1, hg0_2, _⟩ := hnormM 0 g0 hg0
    let fi1 : Fin 4 := ⟨g0.w1, by omega⟩
    let fi2 : Fin 4 := ⟨g0.w2, hg0_2⟩
    have hne12 : fi1 ≠ fi2 := fun h => by have := congrArg Fin.val h; dsimp only [fi1, fi2] at this; omega
    obtain ⟨p, gp, hp1, hplt, hgp, hgp_reads⟩ :=
      fanout_ge_2_of_three_cofactors cm hwfM hposM houtM hcompM g0 hg0 fi1 fi2 rfl rfl hne12
        (th24_three_cofactors fi1 fi2 hne12)
    -- Pick v in {fi1, fi2} read by gp, and partner wp = the other of {fi1, fi2}
    have hv_ex : ∃ (v wp : Fin 4), v ≠ wp ∧
        (g0.w1 = v.val ∨ g0.w2 = v.val) ∧ (g0.w1 = wp.val ∨ g0.w2 = wp.val) ∧
        (gp.w1 = v.val ∨ gp.w2 = v.val) := by
      rcases hgp_reads with h | h | h | h
      · exact ⟨fi1, fi2, hne12, Or.inl rfl, Or.inr rfl, Or.inl h⟩
      · exact ⟨fi1, fi2, hne12, Or.inl rfl, Or.inr rfl, Or.inr h⟩
      · exact ⟨fi2, fi1, Ne.symm hne12, Or.inr rfl, Or.inl rfl, Or.inl h⟩
      · exact ⟨fi2, fi1, Ne.symm hne12, Or.inr rfl, Or.inl rfl, Or.inr h⟩
    obtain ⟨v, wp, hvne, hg0_v, hg0_wp, hgp_v⟩ := hv_ex
    -- Restrict x_v := false via compileAux!
    let rmap := restrictMap 3 v false
    let res := compileAux 3 [] rmap [] cm.gates
    let out := res.1
    let wmap := res.2.1
    let dropped := res.2.2
    have hstep := compileAux_step_props 4 3 [] cm.gates [] rmap []
      hwfM.2 (by simp [rmap, restrictMap_length]) rfl rfl (fun _ _ h => by cases h)
    have hkept := compileAux_kept_spec 3 [] cm.gates [] rmap []
      hwfM.2 (by simp [rmap, restrictMap_length]) rfl rfl (fun _ _ h => by cases h)
    have href := compileAux_ref_eq 3 [] cm.gates [] rmap []
      hwfM.2 (by simp [rmap, restrictMap_length]) rfl rfl (fun _ _ h => by cases h)
    have hprops : ∀ x : BoolVec 3,
        IsNormGates 3 out ∧ wmap.length = 4 + cm.gates.length ∧
        dropped.length = cm.gates.length ∧ out.length = dropped.count false ∧
        (∀ k, k < wmap.length → (wmap.getD k (.const false)).wf (3 + out.length)) ∧
        (∀ k, k < wmap.length →
          evalRef (B2Circuit.evalWires x out) (wmap.getD k (.const false)) =
            (B2Circuit.evalWires (insertBit x v false) cm.gates).getD k false) := by
      intro x
      have h := compileAux_inv 4 3 (insertBit x v false) x [] cm.gates [] rmap []
        hwfM.2 (fun _ _ h => by cases h)
        (by simp [rmap, restrictMap_length]) rfl rfl
        (by
          intro k hk; rw [restrictMap_length] at hk; rw [restrictMap_getD 3 v false k hk]
          by_cases hlt : k < v.val
          · simp only [hlt, ↓reduceIte, WireRef.wf]; omega
          · by_cases heq : k = v.val
            · simp [hlt, heq, WireRef.wf]
            · have hbf : (k == v.val) = false := beq_false_of_ne heq
              simp only [hlt, hbf, Bool.false_eq_true, ↓reduceIte, WireRef.wf]; omega)
        (by
          intro k hk; rw [restrictMap_length] at hk
          rw [restrictMap_eval x v false k hk]
          exact (evalWires_input (insertBit x v false) [] ⟨k, hk⟩).symm)
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
    obtain ⟨hnormO, hwlen, hdlen, houtlen, hwwf, _⟩ := hprops (fun _ => false)
    have hv_const : wmap.getD v.val (.const false) = .const false := by
      rw [hstep.1 v.val (by rw [restrictMap_length]; exact v.isLt)]
      rw [restrictMap_getD 3 v false v.val v.isLt]
      have hnl : ¬ (v.val < v.val) := Nat.lt_irrefl _
      simp [hnl]
    let remapIn (k : Nat) : Nat := if k < v.val then k else k - 1
    have hmap_in : ∀ k, k < 4 → k ≠ v.val →
        wmap.getD k (.const false) = .wire (remapIn k) false ∧ remapIn k < 3 := by
      intro k hk hne
      rw [hstep.1 k (by rw [restrictMap_length]; exact hk), restrictMap_getD 3 v false k hk]
      dsimp only [remapIn]
      by_cases hlt : k < v.val
      · rw [if_pos hlt, if_pos hlt]; exact ⟨rfl, by omega⟩
      · have hbf : (k == v.val) = false := beq_false_of_ne hne
        rw [if_neg hlt, if_neg hlt, hbf]; exact ⟨rfl, by omega⟩
    have hd0 : dropped.getD 0 false = true := by
      rcases hg0_v with h | h
      · exact (hstep.2.2 0 g0 hg0).1 false (h ▸ hv_const)
      · exact (hstep.2.2 0 g0 hg0).2 false (h ▸ hv_const)
    have hdp : dropped.getD p false = true := by
      rcases hgp_v with h | h
      · exact (hstep.2.2 p gp hgp).1 false (h ▸ hv_const)
      · exact (hstep.2.2 p gp hgp).2 false (h ▸ hv_const)
    -- out computes maj3 up to negation, so by maj3_lb, out.length >= 4!
    have hout_wf := hwfM.1
    rcases hcompM with ⟨flip, hflip⟩
    have hout_not_const : ∀ b, wmap.getD cm.outputWire (.const false) ≠ .const b := by
      intro b hb
      obtain ⟨x0, hx0⟩ := maj3_nonTrivial.1 (xor b flip)
      have hev := (hprops x0).2.2.2.2.2 cm.outputWire (by omega)
      rw [hb] at hev
      have hc := hflip (insertBit x0 v false)
      rw [th24_insert_false v x0] at hc
      dsimp only [B2Circuit.eval, evalRef] at hc hev
      rw [← hev] at hc
      cases b <;> cases flip <;> cases hm : PnP.maj3 x0 <;> rw [hm] at hc hx0 <;> simp at hc hx0
    have hout_ge4 : 4 ≤ out.length := by
      cases houtref : wmap.getD cm.outputWire (.const false) with
      | const b => exact absurd houtref (hout_not_const b)
      | wire w pf =>
        have hw_lt : w < 3 + out.length := by
          have := hwwf cm.outputWire (by omega); rw [houtref] at this; exact this
        have hcompO : ComputesUpToNeg ⟨out, w⟩ PnP.maj3 := by
          refine ⟨xor flip pf, fun x => ?_⟩
          have hev := (hprops x).2.2.2.2.2 cm.outputWire (by omega)
          rw [houtref] at hev
          have hc := hflip (insertBit x v false)
          rw [th24_insert_false v x] at hc
          dsimp only [B2Circuit.eval, evalRef] at hc hev ⊢
          rw [← hev] at hc
          cases hv : (B2Circuit.evalWires x out).getD w false <;> rw [hv] at hc <;>
            cases pf <;> cases hm : PnP.maj3 x <;> rw [hm] at hc <;> cases flip <;> simp at hc ⊢
        exact maj3_lb ⟨out, w⟩ ⟨hw_lt, isNormGates_wf hnormO⟩ hcompO
    have hcnt2 := count_false_le_of_two_true dropped 0 p (by omega) (by omega) (by omega) hd0 hdp
    have hcm6 : cm.gates.length = 6 := by dsimp only [B2Circuit.size] at hszM; omega
    have hout4 : out.length = 4 := by omega
    have hout9 : cm.outputWire = 9 := by rw [houtM, B2Circuit.size, hcm6]
    -- No third gate q != 0, q != p can be dropped!
    have hno_third : ∀ q, q < 6 → q ≠ 0 → q ≠ p → dropped.getD q false = false := by
      intro q hq hq0 hqp
      cases hdq : dropped.getD q false
      · rfl
      · exfalso
        have h3 := count_false_le_of_three_true dropped 0 p q (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) hd0 hdp hdq
        omega
    -- Step 1: Neither wire (4 + p) nor wire 4 can map to .const in wmap!
    have hwp_not_const : ∀ bp, wmap.getD (4 + p) (.const false) ≠ .const bp := by
      intro bp hbp
      by_cases hp5 : p = 5
      · have h9 : 4 + p = cm.outputWire := by omega
        rw [h9] at hbp
        exact hout_not_const bp hbp
      · obtain ⟨r, gr, hgr, hr_reads⟩ := husedM p (by dsimp only [B2Circuit.size]; omega)
        have hrlt : r < 6 := by
          by_cases hlt : r < 6
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hgr; cases hgr
        have hrgt : p < r := by
          have hgw := hwfM.2 r gr hgr
          rcases hr_reads with h | h <;> omega
        have hdr : dropped.getD r false = true := by
          rcases hr_reads with h | h
          · exact (hstep.2.2 r gr hgr).1 bp (h ▸ hbp)
          · exact (hstep.2.2 r gr hgr).2 bp (h ▸ hbp)
        have := hno_third r hrlt (by omega) (by omega)
        rw [hdr] at this; cases this
    have hw4_not_const : ∀ b, wmap.getD 4 (.const false) ≠ .const b := by
      intro b hb
      obtain ⟨q, gq, hgq, hq_reads⟩ := husedM 0 (by dsimp only [B2Circuit.size]; omega)
      have hqlt : q < 6 := by
        by_cases hlt : q < 6
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hgq; cases hgq
      have hq0 : q ≠ 0 := by
        have hgw := hwfM.2 q gq hgq
        rcases hq_reads with h | h <;> omega
      by_cases hqp : q = p
      · subst hqp
        rw [hgp] at hgq; cases hgq
        have hboth := href q gp hgp
        rcases hgp_v with hv1 | hv2 <;> rcases hq_reads with h41 | h42
        · rw [hv1] at h41; omega
        · rw [hv1, h42, hv_const, hb] at hboth
          exact hwp_not_const (gp.op.eval false b) hboth
        · rw [h41, hv2, hv_const, hb] at hboth
          exact hwp_not_const (gp.op.eval b false) hboth
        · rw [hv2] at h42; omega
      · have hdq : dropped.getD q false = true := by
          rcases hq_reads with h | h
          · exact (hstep.2.2 q gq hgq).1 b (h ▸ hb)
          · exact (hstep.2.2 q gq hgq).2 b (h ▸ hb)
        have := hno_third q hqlt hq0 hqp
        rw [hdq] at this; cases this
    -- Step 2: Determine exact shape of wmap[4] = .wire x2 f0 and wmap[4+p] = .wire u_p fp!
    let x2 := remapIn wp.val
    have hx2_lt : x2 < 3 := (hmap_in wp.val wp.isLt (fun h => hvne (Fin.ext h.symm))).2
    have hwp_map : wmap.getD wp.val (.const false) = .wire x2 false :=
      (hmap_in wp.val wp.isLt (fun h => hvne (Fin.ext h.symm))).1
    have hw4_ex : ∃ f0 : Bool, wmap.getD 4 (.const false) = .wire x2 f0 := by
      have h0ref := href 0 g0 hg0
      rcases hg0_v with hv1 | hv2 <;> rcases hg0_wp with hw1 | hw2
      · rw [hv1] at hw1; exact absurd (Fin.ext hw1) hvne
      · rw [hv1, hw2, hv_const, hwp_map] at h0ref
        dsimp only [compileGate] at h0ref
        split at h0ref
        · exact absurd h0ref (hw4_not_const _)
        · exact ⟨_, h0ref⟩
      · rw [hw1, hv2, hv_const, hwp_map] at h0ref
        dsimp only [compileGate] at h0ref
        split at h0ref
        · exact absurd h0ref (hw4_not_const _)
        · exact ⟨_, h0ref⟩
      · rw [hv2] at hw2; exact absurd (Fin.ext hw2) hvne
    obtain ⟨f0, hw4_eq⟩ := hw4_ex
    -- Every wire w < 10 with w != v.val and w != 4 + p is mapped to a .wire in wmap
    -- First characterize dropped explicitly from p in {1..5}:
    have hdropped_eq : dropped = [true, decide (p = 1), decide (p = 2), decide (p = 3), decide (p = 4), decide (p = 5)] := by
      have hdrop_len6 : dropped.length = 6 := by omega
      have hdrop_ex : ∃ d0 d1 d2 d3 d4 d5, dropped = [d0, d1, d2, d3, d4, d5] := by
        match dropped, hdrop_len6 with | [d0, d1, d2, d3, d4, d5], _ => exact ⟨d0, d1, d2, d3, d4, d5, rfl⟩
      obtain ⟨d0, d1, d2, d3, d4, d5, hdl⟩ := hdrop_ex
      have hget : ∀ i, i < 6 → dropped.getD i false = (if i = 0 ∨ i = p then true else false) := by
        intro i hi
        by_cases h0 : i = 0
        · subst h0; simp only [true_or, ↓reduceIte]; exact hd0
        · by_cases hp : i = p
          · subst hp; simp only [or_true, ↓reduceIte]; exact hdp
          · simp only [h0, hp, or_self, ↓reduceIte]; exact hno_third i hi h0 hp
      have e0 := hget 0 (by decide); have e1 := hget 1 (by decide); have e2 := hget 2 (by decide)
      have e3 := hget 3 (by decide); have e4 := hget 4 (by decide); have e5 := hget 5 (by decide)
      rw [hdl] at e0 e1 e2 e3 e4 e5 ⊢
      simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4 e5
      have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
      rcases hp_cases with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [List.cons.injEq, and_true]; simp at e0 e1 e2 e3 e4 e5; exact ⟨e0, e1, e2, e3, e4, e5⟩)
    -- Now examine gp's other wire w_other < 4 + p (w_other != v.val)
    obtain ⟨hgp_1, hgp_2, _⟩ := hnormM p gp hgp
    let w_other := if gp.w1 = v.val then gp.w2 else gp.w1
    have hw_other_props : w_other < 4 + p ∧ w_other ≠ v.val ∧
        ((gp.w1 = v.val ∧ gp.w2 = w_other) ∨ (gp.w1 = w_other ∧ gp.w2 = v.val)) := by
      dsimp only [w_other]
      rcases hgp_v with h1 | h2
      · rw [if_pos h1]; exact ⟨hgp_2, by omega, Or.inl ⟨h1, rfl⟩⟩
      · have hne : gp.w1 ≠ v.val := by omega
        rw [if_neg hne]; exact ⟨by omega, hne, Or.inr ⟨rfl, h2⟩⟩
    have hw_other_wire : ∃ (u_p : Nat) (fu : Bool),
        wmap.getD w_other (.const false) = .wire u_p fu ∧ (p < 5 → u_p < 6) ∧ u_p < 7 := by
      by_cases hlt4 : w_other < 4
      · obtain ⟨hm, hlt3⟩ := hmap_in w_other hlt4 hw_other_props.2.1
        exact ⟨remapIn w_other, false, hm, fun _ => by omega, by omega⟩
      · by_cases heq4 : w_other = 4
        · exact ⟨x2, f0, heq4 ▸ hw4_eq, fun _ => by omega, by omega⟩
        · let j := w_other - 4
          have hj_eq : w_other = 4 + j := by omega
          have hj_lt : j < p := by omega
          have hj_pos : 0 < j := by omega
          have hgj_ex : ∃ gj, cm.gates[j]? = some gj := ⟨cm.gates[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨gj, hgj⟩ := hgj_ex
          have hdj : dropped.getD j false = false := hno_third j (by omega) (by omega) (by omega)
          obtain ⟨oi, _, _, _, _, _, pj, hoi, _, _, _, hwk, _⟩ := hkept j gj hgj hdj
          have hoi_lt3 : p < 5 → oi < 3 := by
            intro hp5
            rw [hoi]; change (dropped.take j).count false < 3; rw [hdropped_eq]
            have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
            have hj_cases : j = 1 ∨ j = 2 ∨ j = 3 := by omega
            rcases hp_cases with rfl | rfl | rfl | rfl <;>
              rcases hj_cases with hjv | hjv | hjv <;> (try rw [hjv] at hj_lt ⊢) <;> first | omega | decide
          have hoi_lt4 : oi < 4 := by
            rw [hoi]; change (dropped.take j).count false < 4; rw [hdropped_eq]
            have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
            have hj_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
            rcases hp_cases with rfl | rfl | rfl | rfl | rfl <;>
              rcases hj_cases with hjv | hjv | hjv | hjv <;> (try rw [hjv] at hj_lt ⊢) <;> first | omega | decide
          exact ⟨3 + oi, pj, hj_eq ▸ hwk, fun hp5 => by have := hoi_lt3 hp5; omega, by omega⟩
    obtain ⟨u_p, fu, hw_other_map, hup_lt6, hup_lt7⟩ := hw_other_wire
    have hwp_ex : ∃ fp : Bool, wmap.getD (4 + p) (.const false) = .wire u_p fp := by
      have hpref := href p gp hgp
      rcases hw_other_props.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hv_const, hw_other_map] at hpref
        dsimp only [compileGate] at hpref
        split at hpref
        · exact absurd hpref (hwp_not_const _)
        · exact ⟨_, hpref⟩
      · rw [h1, h2, hv_const, hw_other_map] at hpref
        dsimp only [compileGate] at hpref
        split at hpref
        · exact absurd hpref (hwp_not_const _)
        · exact ⟨_, hpref⟩
    obtain ⟨fp, hwp_eq⟩ := hwp_ex
    -- Step 3: Unpack out = [o0, o1, o2, o3] and prove wmap[9] = .wire 6 flip!
    have hout_cons : ∃ o0 o1 o2 o3, out = [o0, o1, o2, o3] := by
      match out, hout4 with | [o0, o1, o2, o3], _ => exact ⟨o0, o1, o2, o3, rfl⟩
    obtain ⟨o0, o1, o2, o3, hout_eq⟩ := hout_cons
    -- Define the 4 kept gate indices k0 < k1 < k2 < k3 in {1..5} \ {p}
    let k0 := if p == 1 then 2 else 1
    let k1 := if p <= 2 then 3 else 2
    let k2 := if p <= 3 then 4 else 3
    let k3 := if p <= 4 then 5 else 4
    have hk_props :
        (k0 < 6 ∧ k0 ≠ 0 ∧ k0 ≠ p ∧ (dropped.take k0).count false = 0) ∧
        (k1 < 6 ∧ k1 ≠ 0 ∧ k1 ≠ p ∧ (dropped.take k1).count false = 1) ∧
        (k2 < 6 ∧ k2 ≠ 0 ∧ k2 ≠ p ∧ (dropped.take k2).count false = 2) ∧
        (k3 < 6 ∧ k3 ≠ 0 ∧ k3 ≠ p ∧ (dropped.take k3).count false = 3) := by
      dsimp only [k0, k1, k2, k3]
      rw [hdropped_eq]
      have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
      rcases hp_cases with rfl | rfl | rfl | rfl | rfl <;> decide
    -- Extract kept gate specs for i = 0, 1, 2, 3
    have hget_kept : ∀ (ki oi : Nat) (o : B2Gate),
        ki < 6 → ki ≠ 0 → ki ≠ p → (dropped.take ki).count false = oi → out[oi]? = some o →
        ∃ (gk : B2Gate) (srcA srcB : Nat) (fA fB pk : Bool),
          cm.gates[ki]? = some gk ∧
          wmap.getD srcA (.const false) = .wire o.w1 fA ∧
          wmap.getD srcB (.const false) = .wire o.w2 fB ∧
          wmap.getD (4 + ki) (.const false) = .wire (3 + oi) pk ∧
          srcA < 4 + ki ∧ srcB < 4 + ki ∧
          ((gk.w1 = srcA ∧ gk.w2 = srcB) ∨ (gk.w1 = srcB ∧ gk.w2 = srcA)) ∧
          ∀ a b : Bool, xor (o.op.eval (xor a fA) (xor b fB)) pk = gk.op.eval
            (if gk.w1 = srcA ∧ gk.w2 = srcB then a else b)
            (if gk.w1 = srcA ∧ gk.w2 = srcB then b else a) := by
      intro ki oi o hki hki0 hkip hcnt hoi
      have hgk : cm.gates[ki]? = some (cm.gates[ki]'(by omega)) := List.getElem?_eq_getElem (by omega)
      have hdk : dropped.getD ki false = false := hno_third ki hki hki0 hkip
      obtain ⟨oi', g', u1, u2, f1, f2, pk, hoi', hg', hw1, hw2, hwk, hsym⟩ := hkept ki _ hgk hdk
      have hoieq : oi' = oi := by rw [hoi', hcnt]
      subst hoieq
      rw [hoi] at hg'; cases hg'
      have hgw := hwfM.2 ki _ hgk
      rcases hsym with ⟨hlt, heq1, heq2, hev⟩ | ⟨hlt, heq1, heq2, hev⟩
      · refine ⟨cm.gates[ki]'(by omega), (cm.gates[ki]'(by omega)).w1, (cm.gates[ki]'(by omega)).w2,
          f1, f2, pk, hgk, heq1 ▸ hw1, heq2 ▸ hw2, hwk, hgw.1, hgw.2, Or.inl ⟨rfl, rfl⟩, fun a b => ?_⟩
        simp only [and_self, ↓reduceIte]
        have := hev (xor a f1) (xor b f2)
        simpa [Bool.xor_assoc] using this
      · refine ⟨cm.gates[ki]'(by omega), (cm.gates[ki]'(by omega)).w2, (cm.gates[ki]'(by omega)).w1,
          f2, f1, pk, hgk, heq1 ▸ hw2, heq2 ▸ hw1, hwk, hgw.2, hgw.1, Or.inr ⟨rfl, rfl⟩, fun a b => ?_⟩
        have hne_w : (cm.gates[ki]'(by omega)).w1 ≠ (cm.gates[ki]'(by omega)).w2 := by
          intro heq; rw [heq] at hw1; rw [hw1] at hw2; cases hw2; omega
        have hcond : ¬ ((cm.gates[ki]'(by omega)).w1 = (cm.gates[ki]'(by omega)).w2 ∧
                        (cm.gates[ki]'(by omega)).w2 = (cm.gates[ki]'(by omega)).w1) := fun h => hne_w h.1
        simp only [hcond, ↓reduceIte]
        have := hev (xor a f2) (xor b f1)
        simpa [Bool.xor_assoc] using this
    obtain ⟨gk0, s0a, s0b, f0a, f0b, pk0, hgk0, hs0a, hs0b, hwk0, hs0a_lt, hs0b_lt, hpr0, hev0⟩ :=
      hget_kept k0 0 o0 hk_props.1.1 hk_props.1.2.1 hk_props.1.2.2.1 hk_props.1.2.2.2 (by rw [hout_eq]; rfl)
    obtain ⟨gk1, s1a, s1b, f1a, f1b, pk1, hgk1, hs1a, hs1b, hwk1, hs1a_lt, hs1b_lt, hpr1, hev1⟩ :=
      hget_kept k1 1 o1 hk_props.2.1.1 hk_props.2.1.2.1 hk_props.2.1.2.2.1 hk_props.2.1.2.2.2 (by rw [hout_eq]; rfl)
    obtain ⟨gk2, s2a, s2b, f2a, f2b, pk2, hgk2, hs2a, hs2b, hwk2, hs2a_lt, hs2b_lt, hpr2, hev2⟩ :=
      hget_kept k2 2 o2 hk_props.2.2.1.1 hk_props.2.2.1.2.1 hk_props.2.2.1.2.2.1 hk_props.2.2.1.2.2.2 (by rw [hout_eq]; rfl)
    obtain ⟨gk3, s3a, s3b, f3a, f3b, pk3, hgk3, hs3a, hs3b, hwk3, hs3a_lt, hs3b_lt, hpr3, hev3⟩ :=
      hget_kept k3 3 o3 hk_props.2.2.2.1 hk_props.2.2.2.2.1 hk_props.2.2.2.2.2.1 hk_props.2.2.2.2.2.2 (by rw [hout_eq]; rfl)
    -- Prove wmap[9] = .wire 6 pf (and if p = 5, u_p = 6!)
    have hw9_eq : ∃ pf : Bool, wmap.getD 9 (.const false) = .wire 6 pf ∧ (p = 5 → u_p = 6 ∧ fp = pf) := by
      by_cases hp5 : p = 5
      · have h9 : 4 + p = 9 := by omega
        have hw9 : wmap.getD 9 (.const false) = .wire u_p fp := h9 ▸ hwp_eq
        have hu6 : u_p = 6 := by
          by_cases hlt6 : u_p < 6
          · exfalso
            have hcompO : ComputesUpToNeg ⟨out, u_p⟩ PnP.maj3 := by
              refine ⟨xor flip fp, fun x => ?_⟩
              have hev := (hprops x).2.2.2.2.2 9 (by omega)
              rw [hw9] at hev
              have hc := hflip (insertBit x v false)
              rw [th24_insert_false v x] at hc
              dsimp only [B2Circuit.eval, evalRef] at hc hev ⊢
              rw [hout9, ← hev] at hc
              cases hv : (B2Circuit.evalWires x out).getD u_p false <;> rw [hv] at hc <;>
                cases fp <;> cases hm : PnP.maj3 x <;> rw [hm] at hc <;> cases flip <;> simp at hc ⊢
            have hwfO : WF 3 ⟨out, u_p⟩ := ⟨by change u_p < 3 + out.length; omega, isNormGates_wf hnormO⟩
            obtain ⟨hwf', hlen', hev'⟩ := deleteGate_props ⟨out, u_p⟩ 3 hwfO (by change 3 < out.length; omega) (by change u_p ≠ 3 + 3; omega)
              (fun j g hgj => by
                have hgw := (isNormGates_wf hnormO) j g hgj
                have hjlt : j < 4 := by
                  by_cases hlt : j < 4
                  · exact hlt
                  · rw [List.getElem?_eq_none (by change out.length ≤ j; omega)] at hgj; cases hgj
                omega)
            have hcomp' : ComputesUpToNeg (deleteGate 3 ⟨out, u_p⟩ 3) PnP.maj3 := by
              rcases hcompO with ⟨fl, hfl⟩; exact ⟨fl, fun x => (hev' x).trans (hfl x)⟩
            have hlb := maj3_lb (deleteGate 3 ⟨out, u_p⟩ 3) hwf' hcomp'
            dsimp only [B2Circuit.size] at hlen' hlb; omega
          · omega
        exact ⟨fp, hu6 ▸ hw9, fun _ => ⟨hu6, rfl⟩⟩
      · have hk3_5 : k3 = 5 := by dsimp only [k3]; split <;> omega
        have h9 : 4 + k3 = 9 := by omega
        exact ⟨pk3, h9 ▸ hwk3, fun h => absurd h hp5⟩
    obtain ⟨pf, hw9_map, hp5_u6⟩ := hw9_eq
    -- Prove pf = flip (by evaluating at all-false!)
    have hpf_eq : pf = flip := by
      have hev := (hprops (fun _ => false)).2.2.2.2.2 9 (by omega)
      rw [hw9_map] at hev
      have hc := hflip (insertBit (fun _ => false) v false)
      rw [th24_insert_false v (fun _ => false)] at hc
      dsimp only [B2Circuit.eval, evalRef] at hc hev
      rw [hout9, ← hev] at hc
      have hnorm0 := evalWires_allFalse_norm out hnormO 6 (by omega)
      have hmaj0 : PnP.maj3 (fun _ => false) = false := by decide
      rw [hnorm0, hmaj0] at hc
      cases pf <;> cases flip <;> simp at hc ⊢
    subst hpf_eq
    -- Base circuit computes maj3 with flip = false!
    have hbase_eval : ∀ x : BoolVec 3, (B2Circuit.evalWires x out).getD 6 false = PnP.maj3 x := by
      intro x
      have hev := (hprops x).2.2.2.2.2 9 (by omega)
      rw [hw9_map] at hev
      have hc := hflip (insertBit x v false)
      rw [th24_insert_false v x] at hc
      dsimp only [B2Circuit.eval, evalRef] at hc hev
      rw [hout9, ← hev] at hc
      cases hv : (B2Circuit.evalWires x out).getD 6 false <;> rw [hv] at hc <;>
        cases pf <;> cases hm : PnP.maj3 x <;> rw [hm] at hc <;> simp at hc ⊢
    -- Step 4: Classify g0 and gp at x_v = true!
    let evalT (x : BoolVec 3) (w : Nat) : Bool :=
      (B2Circuit.evalWires (insertBit x v true) cm.gates).getD w false
    have hevalT_in : ∀ (x : BoolVec 3) (k : Nat) (hk : k < 4),
        evalT x k = if h : k = v.val then true else x ⟨remapIn k, (hmap_in k hk h).2⟩ := by
      intro x k hk
      dsimp only [evalT]
      rw [evalWires_input (insertBit x v true) cm.gates ⟨k, hk⟩]
      dsimp only [insertBit, remapIn]
      by_cases hlt : k < v.val
      · have hne : k ≠ v.val := by omega
        simp [hlt, hne]
      · by_cases heq : k = v.val
        · simp [hlt, heq]
        · simp [hlt, heq]
    let h0_fn : Bool → Bool := fun b =>
      xor (g0.op.eval (if g0.w1 = v.val then true else b) (if g0.w2 = v.val then true else b)) f0
    have hevalT_4 : ∀ x : BoolVec 3, xor (evalT x 4) f0 = h0_fn (x ⟨x2, hx2_lt⟩) := by
      intro x
      dsimp only [evalT, h0_fn]
      rw [evalWires_gate _ cm.gates 0 g0 hg0 hwfM.2]
      rcases hg0_v with hv1 | hv2 <;> rcases hg0_wp with hw1 | hw2
      · rw [hv1] at hw1; exact absurd (Fin.ext hw1) hvne
      · have hne : g0.w2 ≠ v.val := by rw [hw2]; exact fun h => hvne (Fin.ext h.symm)
        simp only [hv1, hne, ↓reduceIte]
        have e1 := hevalT_in x v.val v.isLt
        have e2 := hevalT_in x wp.val wp.isLt
        have hne_wp : wp.val ≠ v.val := fun h => hvne (Fin.ext h.symm)
        simp only [↓reduceIte, hne_wp, ↓reduceDIte] at e1 e2
        dsimp only [evalT] at e1 e2
        rw [hw2, e1, e2]
      · have hne : g0.w1 ≠ v.val := by rw [hw1]; exact fun h => hvne (Fin.ext h.symm)
        simp only [hv2, hne, ↓reduceIte]
        have e1 := hevalT_in x v.val v.isLt
        have e2 := hevalT_in x wp.val wp.isLt
        have hne_wp : wp.val ≠ v.val := fun h => hvne (Fin.ext h.symm)
        simp only [↓reduceIte, hne_wp, ↓reduceDIte] at e1 e2
        dsimp only [evalT] at e1 e2
        rw [hw1, e1, e2]
      · rw [hv2] at hw2; exact absurd (Fin.ext hw2) hvne
    obtain ⟨g0Ch, g0Mode, hg0Mode_lt, hg0_unch, hg0_ch⟩ := bool_fn_classify h0_fn
    let hp_fn : Bool → Bool :=
      if w_other = 4 then
        fun b => xor (gp.op.eval (if gp.w1 = v.val then true else xor (h0_fn b) f0)
                                 (if gp.w2 = v.val then true else xor (h0_fn b) f0)) fp
      else
        fun b => xor (gp.op.eval (if gp.w1 = v.val then true else xor b fu)
                                 (if gp.w2 = v.val then true else xor b fu)) fp
    obtain ⟨gpCh, gpMode, hgpMode_lt, hgp_unch, hgp_ch⟩ := bool_fn_classify hp_fn
    -- Step 5: Construct the FourGateLift L!
    let pLt5 : Bool := decide (p < 5)
    let m0 : Mask8 :=
      ⟨g0Ch && (s0a == 4), g0Ch && (s0b == 4),
       g0Ch && (s1a == 4), g0Ch && (s1b == 4),
       g0Ch && (s2a == 4), g0Ch && (s2b == 4),
       g0Ch && (s3a == 4), g0Ch && (s3b == 4)⟩
    let m1 : Mask8 :=
      ⟨pLt5 && gpCh && (s0a == 4 + p), pLt5 && gpCh && (s0b == 4 + p),
       pLt5 && gpCh && (s1a == 4 + p), pLt5 && gpCh && (s1b == 4 + p),
       pLt5 && gpCh && (s2a == 4 + p), pLt5 && gpCh && (s2b == 4 + p),
       pLt5 && gpCh && (s3a == 4 + p), pLt5 && gpCh && (s3b == 4 + p)⟩
    let L : FourGateLift :=
      { g0 := o0, g1 := o1, g2 := o2, g3 := o3
        x2 := x2, g0Mode := g0Mode
        u := if p < 5 then u_p else 0
        uMode := if p < 5 then gpMode else 0
        m0 := m0, m1 := m1
        outFlip := if p = 5 then gpCh else false }
    -- Prove L.evalBase = TT3.maj3
    have hL_norm : IsNormGates 3 [o0, o1, o2, o3] := hout_eq ▸ hnormO
    have hL_base : L.evalBase = TT3.maj3 := by
      have ho0 := hL_norm 0 o0 rfl; have ho1 := hL_norm 1 o1 rfl
      have ho2 := hL_norm 2 o2 rfl; have ho3 := hL_norm 3 o3 rfl
      have ht_in : ∀ idx, idx < 3 → tt3Of (fun x => (B2Circuit.evalWires x out).getD idx false) =
          getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero idx := by
        intro idx hidx; match idx with
        | 0 => change tt3Of (fun x => (B2Circuit.evalWires x out).getD 0 false) = TT3.x0
               rw [← tt3Of_x0]; congr; funext x; exact evalWires_input x out ⟨0, by decide⟩
        | 1 => change tt3Of (fun x => (B2Circuit.evalWires x out).getD 1 false) = TT3.x1
               rw [← tt3Of_x1]; congr; funext x; exact evalWires_input x out ⟨1, by decide⟩
        | 2 => change tt3Of (fun x => (B2Circuit.evalWires x out).getD 2 false) = TT3.x2
               rw [← tt3Of_x2]; congr; funext x; exact evalWires_input x out ⟨2, by decide⟩
      let w3 := TT3.evalOp5 (opToNat5 o0.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero o0.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero o0.w2)
      have ht3 : tt3Of (fun x => (B2Circuit.evalWires x out).getD 3 false) = w3 := by
        dsimp only [w3]; rw [← ht_in o0.w1 (by omega), ← ht_in o0.w2 (by omega), ← tt3Of_op o0.op ho0.2.2]
        congr; funext x; exact evalWires_gate x out 0 o0 (by rw [hout_eq]; rfl) (isNormGates_wf hnormO)
      have hget3 : ∀ idx, idx < 4 → tt3Of (fun x => (B2Circuit.evalWires x out).getD idx false) =
          getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero idx := by
        intro idx hi; match idx with
        | 0 => exact ht_in 0 (by decide) | 1 => exact ht_in 1 (by decide) | 2 => exact ht_in 2 (by decide)
        | 3 => exact ht3
      let w4 := TT3.evalOp5 (opToNat5 o1.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero o1.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 TT3.zero TT3.zero o1.w2)
      have ht4 : tt3Of (fun x => (B2Circuit.evalWires x out).getD 4 false) = w4 := by
        dsimp only [w4]; rw [← hget3 o1.w1 (by omega), ← hget3 o1.w2 (by omega), ← tt3Of_op o1.op ho1.2.2]
        congr; funext x; exact evalWires_gate x out 1 o1 (by rw [hout_eq]; rfl) (isNormGates_wf hnormO)
      have hget4 : ∀ idx, idx < 5 → tt3Of (fun x => (B2Circuit.evalWires x out).getD idx false) =
          getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero idx := by
        intro idx hi; match idx with
        | 0 => exact ht_in 0 (by decide) | 1 => exact ht_in 1 (by decide) | 2 => exact ht_in 2 (by decide)
        | 3 => exact ht3 | 4 => exact ht4
      let w5 := TT3.evalOp5 (opToNat5 o2.op)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero o2.w1)
        (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 TT3.zero o2.w2)
      have ht5 : tt3Of (fun x => (B2Circuit.evalWires x out).getD 5 false) = w5 := by
        dsimp only [w5]; rw [← hget4 o2.w1 (by omega), ← hget4 o2.w2 (by omega), ← tt3Of_op o2.op ho2.2.2]
        congr; funext x; exact evalWires_gate x out 2 o2 (by rw [hout_eq]; rfl) (isNormGates_wf hnormO)
      have hget5 : ∀ idx, idx < 6 → tt3Of (fun x => (B2Circuit.evalWires x out).getD idx false) =
          getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 idx := by
        intro idx hi; match idx with
        | 0 => exact ht_in 0 (by decide) | 1 => exact ht_in 1 (by decide) | 2 => exact ht_in 2 (by decide)
        | 3 => exact ht3 | 4 => exact ht4 | 5 => exact ht5
      have ht6 : tt3Of (fun x => (B2Circuit.evalWires x out).getD 6 false) = L.evalBase := by
        dsimp only [FourGateLift.evalBase, L]
        rw [← hget5 o3.w1 (by omega), ← hget5 o3.w2 (by omega), ← tt3Of_op o3.op ho3.2.2]
        congr; funext x; exact evalWires_gate x out 3 o3 (by rw [hout_eq]; rfl) (isNormGates_wf hnormO)
      rw [← ht6, ← tt3Of_maj3]
      congr; funext x; exact hbase_eval x
    -- Prove L.evalPert = TT3.or3!
    have hL_pert : L.evalPert = TT3.or3 := by
      have ho0 := hL_norm 0 o0 rfl; have ho1 := hL_norm 1 o1 rfl
      have ho2 := hL_norm 2 o2 rfl; have ho3 := hL_norm 3 o3 rfl
      -- Compute the 4 intermediate TT3s of L.evalPert
      let g0v := match g0Mode with
        | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero x2).not
      let pick (b0 b1 : Bool) (cur : TT3) (w3 w4 w5 : TT3) : TT3 :=
        if b0 then g0v
        else if b1 then
          match L.uMode with
          | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 L.u).not
        else cur
      let pw3 := TT3.evalOp5 (opToNat5 o0.op)
        (pick m0.s0a m1.s0a (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero o0.w1) TT3.zero TT3.zero TT3.zero)
        (pick m0.s0b m1.s0b (getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero o0.w2) TT3.zero TT3.zero TT3.zero)
      let pw4 := TT3.evalOp5 (opToNat5 o1.op)
        (pick m0.s1a m1.s1a (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 TT3.zero TT3.zero o1.w1) pw3 TT3.zero TT3.zero)
        (pick m0.s1b m1.s1b (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 TT3.zero TT3.zero o1.w2) pw3 TT3.zero TT3.zero)
      let pw5 := TT3.evalOp5 (opToNat5 o2.op)
        (pick m0.s2a m1.s2a (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 TT3.zero o2.w1) pw3 pw4 TT3.zero)
        (pick m0.s2b m1.s2b (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 TT3.zero o2.w2) pw3 pw4 TT3.zero)
      let pw6 := TT3.evalOp5 (opToNat5 o3.op)
        (pick m0.s3a m1.s3a (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 pw5 o3.w1) pw3 pw4 pw5)
        (pick m0.s3b m1.s3b (getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 pw5 o3.w2) pw3 pw4 pw5)
      -- Helper: TT3 of x[idx] for idx < 3
      have htt_x : ∀ (idx : Nat) (hidx : idx < 3),
          tt3Of (fun x => x ⟨idx, hidx⟩) = getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero idx := by
        intro idx hidx; match idx with | 0 => exact tt3Of_x0 | 1 => exact tt3Of_x1 | 2 => exact tt3Of_x2
      have htt_x_any : ∀ (w3 w4 w5 : TT3) (idx : Nat) (hidx : idx < 3),
          tt3Of (fun x => x ⟨idx, hidx⟩) = getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 idx := by
        intro w3 w4 w5 idx hidx; match idx with | 0 => exact tt3Of_x0 | 1 => exact tt3Of_x1 | 2 => exact tt3Of_x2
      -- Helper: TT3 of xor (evalT x 4) f0
      have htt_4 : tt3Of (fun x => xor (evalT x 4) f0) =
          if g0Ch then g0v else getW3 TT3.x0 TT3.x1 TT3.x2 TT3.zero TT3.zero TT3.zero x2 := by
        have hfn : (fun x => xor (evalT x 4) f0) = (fun x => h0_fn (x ⟨x2, hx2_lt⟩)) := funext hevalT_4
        rw [hfn]
        cases hch : g0Ch
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hu := hg0_unch hch
          simpa [hu] using htt_x x2 hx2_lt
        · simp only [↓reduceIte]
          have hc := hg0_ch hch
          dsimp only [g0v]
          match hm : g0Mode with
          | 0 => simp [hc, hm]; rfl
          | 1 => simp [hc, hm]; rfl
          | 2 => simp [hc, hm]; rw [tt3Of_not, htt_x x2 hx2_lt]
          | _ + 3 => omega
      -- Helper: TT3 of any wire w < 4 (w != v)
      have htt_in : ∀ (w : Nat) (hw4 : w < 4) (hwv : w ≠ v.val) (w3 w4 w5 : TT3),
          tt3Of (fun x => xor (evalT x w) false) = getW3 TT3.x0 TT3.x1 TT3.x2 w3 w4 w5 (remapIn w) := by
        intro w hw4 hwv w3 w4 w5
        have hfn : (fun x => xor (evalT x w) false) = (fun x => x ⟨remapIn w, (hmap_in w hw4 hwv).2⟩) := by
          funext x; rw [Bool.xor_false, hevalT_in x w hw4]; simp [hwv]
        rw [hfn]; exact htt_x_any w3 w4 w5 (remapIn w) (hmap_in w hw4 hwv).2
      -- Define a uniform wire-value helper `valAt step w`:
      -- By strong induction on w < 10 (w != v.val), prove that for all w < 10 (w != v.val):
      --   * w < 4 => tt3Of (xor (evalT · w) false) = getW3 ... (remapIn w)
      --   * w = 4 => tt3Of (xor (evalT · 4) f0) = if g0Ch then g0v else getW3 ... x2
      --   * w = 4 + k0 => tt3Of (xor (evalT · (4+k0)) pk0) = pw3
      --   * w = 4 + k1 => tt3Of (xor (evalT · (4+k1)) pk1) = pw4
      --   * w = 4 + k2 => tt3Of (xor (evalT · (4+k2)) pk2) = pw5
      --   * w = 4 + k3 => tt3Of (xor (evalT · (4+k3)) pk3) = pw6
      --   * w = 4 + p (when p < 5) => tt3Of (xor (evalT · (4+p)) fp) =
      --       if gpCh then (match gpMode with | 0 => TT3.zero | 1 => TT3.one | _ => (getW3 x0 x1 x2 pw3 pw4 pw5 u_p).not)
      --       else getW3 x0 x1 x2 pw3 pw4 pw5 u_p
      --   * w = 4 + p (when p = 5) => tt3Of (xor (evalT · 9) fp) = if gpCh then pw6.not else pw6
      let wireTT (idx : Nat) : TT3 :=
        match idx with
        | 0 => TT3.x0 | 1 => TT3.x1 | 2 => TT3.x2
        | 3 => pw3 | 4 => pw4 | 5 => pw5 | _ => pw6
      have hwireTT_getW3 : ∀ (idx : Nat) (a b c : TT3),
          (idx < 3 → getW3 TT3.x0 TT3.x1 TT3.x2 a b c idx = wireTT idx) ∧
          (idx < 4 → getW3 TT3.x0 TT3.x1 TT3.x2 pw3 b c idx = wireTT idx) ∧
          (idx < 5 → getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 c idx = wireTT idx) ∧
          (idx < 6 → getW3 TT3.x0 TT3.x1 TT3.x2 pw3 pw4 pw5 idx = wireTT idx) := by
        intro idx a b c
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
        · match idx with | 0 => rfl | 1 => rfl | 2 => rfl
        · match idx with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
        · match idx with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
        · match idx with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl
      -- Prove the main invariant by strong induction on w < 10!
      have hinv : ∀ w, w < 10 → w ≠ v.val →
          ∀ (uw : Nat) (fw : Bool), wmap.getD w (.const false) = .wire uw fw →
          (w ≠ 4 ∧ w ≠ 4 + p → tt3Of (fun x => xor (evalT x w) fw) = wireTT uw) ∧
          (w = 4 + p → p < 5 →
            tt3Of (fun x => xor (evalT x w) fw) =
              if gpCh then (match gpMode with | 0 => TT3.zero | 1 => TT3.one | _ => (wireTT u_p).not)
              else wireTT u_p) ∧
          (w = 4 + p → p = 5 →
            tt3Of (fun x => xor (evalT x w) fw) =
              if gpCh then (match gpMode with | 0 => TT3.zero | 1 => TT3.one | _ => pw6.not)
              else pw6) := by
        intro w
        induction w using Nat.strongRecOn with
        | ind w ih =>
          intro hw10 hwv uw fw hwm
          -- Helper to compute TT3 of any wire s < w with wmap[s] = .wire us fs!
          have hpick_src : ∀ (s : Nat) (us : Nat) (fs : Bool) (oi : Nat) (w3a w4a w5a : TT3),
              s < w → wmap.getD s (.const false) = .wire us fs → us < 3 + oi →
              (oi = 0 ∨ (oi = 1 ∧ w3a = pw3) ∨ (oi = 2 ∧ w3a = pw3 ∧ w4a = pw4) ∨ (oi = 3 ∧ w3a = pw3 ∧ w4a = pw4 ∧ w5a = pw5)) →
              tt3Of (fun x => xor (evalT x s) fs) =
                pick (g0Ch && (s == 4)) (pLt5 && gpCh && (s == 4 + p))
                  (getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a us) w3a w4a w5a := by
            intro s us fs oi w3a w4a w5a hsw hsm hus hoi
            have hsv : s ≠ v.val := by
              intro h; subst h; rw [hv_const] at hsm; cases hsm
            have hget_us : getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a us = wireTT us := by
              rcases hoi with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
              · exact (hwireTT_getW3 us w3a w4a w5a).1 hus
              · exact (hwireTT_getW3 us TT3.zero w4a w5a).2.1 hus
              · exact (hwireTT_getW3 us TT3.zero TT3.zero w5a).2.2.1 hus
              · exact (hwireTT_getW3 us TT3.zero TT3.zero TT3.zero).2.2.2 hus
            by_cases hs4 : s = 4
            · subst hs4
              rw [hw4_eq] at hsm; cases hsm
              have hne4p : (4 == 4 + p) = false := beq_false_of_ne (by omega)
              dsimp only [pick]
              simp only [beq_self_eq_true, Bool.and_true, hne4p, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
              rw [htt_4, hget_us]
              cases g0Ch
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact (hwireTT_getW3 x2 TT3.zero TT3.zero TT3.zero).1 hx2_lt
              · rfl
            · by_cases hsp : s = 4 + p
              · subst hsp
                have hp5 : p < 5 := by omega
                have hplt5 : pLt5 = true := by simp [pLt5, hp5]
                rw [hwp_eq] at hsm; cases hsm
                have hne4 : (4 + p == 4) = false := beq_false_of_ne (by omega)
                dsimp only [pick]
                simp only [hne4, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hplt5, Bool.true_and, beq_self_eq_true, Bool.and_true]
                have hget_u : getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a L.u = wireTT u_p := by
                  have hLu : L.u = u_p := by simp [L, hp5]
                  rw [hLu]; exact hget_us
                have hihp := (ih (4 + p) hsw (by omega) hsv u_p fp hwp_eq).2.1 rfl hp5
                rw [hihp, hget_us]
                cases gpCh
                · rfl
                · simp only [↓reduceIte]
                  have hLum : L.uMode = gpMode := by simp [L, hp5]
                  rw [hLum]
                  match gpMode with
                  | 0 => rfl
                  | 1 => rfl
                  | _ + 2 =>
                    change (wireTT u_p).not = (getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a L.u).not
                    rw [hget_u]
              · have hne4 : (s == 4) = false := beq_false_of_ne hs4
                have hnep : (s == 4 + p) = false := beq_false_of_ne hsp
                dsimp only [pick]
                simp only [hne4, hnep, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                rw [hget_us]
                exact (ih s hsw (by omega) hsv us fs hsm).1 ⟨hs4, hsp⟩
          -- Now prove the 3 clauses for w!
          refine ⟨fun ⟨hne4, hnep⟩ => ?_, fun heqp hp5 => ?_, fun heqp hp5 => ?_⟩
          · -- Clause 1: w != 4 and w != 4 + p
            by_cases hlt4 : w < 4
            · obtain ⟨hm, hlt3⟩ := hmap_in w hlt4 hwv
              rw [hm] at hwm; cases hwm
              rw [htt_in w hlt4 hwv TT3.zero TT3.zero TT3.zero]
              exact (hwireTT_getW3 (remapIn w) TT3.zero TT3.zero TT3.zero).1 hlt3
            · -- w = 4 + ki for one of k0, k1, k2, k3!
              have hcases : w = 4 + k0 ∨ w = 4 + k1 ∨ w = 4 + k2 ∨ w = 4 + k3 := by
                have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
                rcases hp_cases with rfl | rfl | rfl | rfl | rfl <;> (dsimp only [k0, k1, k2, k3]; simp; omega)
              -- Uniform step for a kept gate (oi, o, ki, gk, sA, sB, fA, fB, pk):
              have hkept_step : ∀ (oi ki : Nat) (o gk : B2Gate) (sA sB : Nat) (fA fB pk : Bool)
                  (w3a w4a w5a : TT3),
                  w = 4 + ki → ki < 6 → (isNorm5 o.op) = true → o.w1 < o.w2 → o.w2 < 3 + oi →
                  cm.gates[ki]? = some gk →
                  wmap.getD sA (.const false) = .wire o.w1 fA →
                  wmap.getD sB (.const false) = .wire o.w2 fB →
                  wmap.getD (4 + ki) (.const false) = .wire (3 + oi) pk →
                  sA < 4 + ki → sB < 4 + ki →
                  ((gk.w1 = sA ∧ gk.w2 = sB) ∨ (gk.w1 = sB ∧ gk.w2 = sA)) →
                  (∀ a b : Bool, xor (o.op.eval (xor a fA) (xor b fB)) pk = gk.op.eval
                    (if gk.w1 = sA ∧ gk.w2 = sB then a else b)
                    (if gk.w1 = sA ∧ gk.w2 = sB then b else a)) →
                  (oi = 0 ∨ (oi = 1 ∧ w3a = pw3) ∨ (oi = 2 ∧ w3a = pw3 ∧ w4a = pw4) ∨ (oi = 3 ∧ w3a = pw3 ∧ w4a = pw4 ∧ w5a = pw5)) →
                  tt3Of (fun x => xor (evalT x w) fw) =
                    TT3.evalOp5 (opToNat5 o.op)
                      (pick (g0Ch && (sA == 4)) (pLt5 && gpCh && (sA == 4 + p))
                        (getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a o.w1) w3a w4a w5a)
                      (pick (g0Ch && (sB == 4)) (pLt5 && gpCh && (sB == 4 + p))
                        (getW3 TT3.x0 TT3.x1 TT3.x2 w3a w4a w5a o.w2) w3a w4a w5a) := by
                intro oi ki o gk sA sB fA fB pk w3a w4a w5a hwki hki hop ho12 ho2w hgk hsA hsB hwk hsAlt hsBlt hpair hevg hoi
                subst hwki
                rw [hwk] at hwm; cases hwm
                rw [← hpick_src sA o.w1 fA oi w3a w4a w5a hsAlt hsA (by omega) hoi,
                    ← hpick_src sB o.w2 fB oi w3a w4a w5a hsBlt hsB ho2w hoi,
                    ← tt3Of_op o.op hop]
                congr; funext x
                have hgate := evalWires_gate (insertBit x v true) cm.gates ki gk hgk hwfM.2
                change xor ((B2Circuit.evalWires (insertBit x v true) cm.gates).getD (4 + ki) false) fw = _
                rw [hgate]
                have hev_x := hevg (evalT x sA) (evalT x sB)
                have hflip_eq : o.op.eval (xor (evalT x sA) fA) (xor (evalT x sB) fB) =
                    xor (gk.op.eval (if gk.w1 = sA ∧ gk.w2 = sB then evalT x sA else evalT x sB)
                                    (if gk.w1 = sA ∧ gk.w2 = sB then evalT x sB else evalT x sA)) fw := by
                  rw [← hev_x, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
                rw [hflip_eq]
                rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · simp only [h1, h2, and_self, ↓reduceIte]; rfl
                · have hne : ¬ (sB = sA ∧ sA = sB) := by
                    intro ⟨ha, _⟩
                    rw [ha] at hsB; rw [hsA] at hsB
                    have : o.w1 = o.w2 := by injection hsB
                    omega
                  simp only [h1, h2, hne, ↓reduceIte]; rfl
              rcases hcases with hw0 | hw1 | hw2 | hw3
              · rw [hw0] at hwm; rw [hwk0] at hwm; cases hwm
                exact hkept_step 0 k0 o0 gk0 s0a s0b f0a f0b pk0 TT3.zero TT3.zero TT3.zero
                  hw0 hk_props.1.1 ho0.2.2 ho0.1 ho0.2.1 hgk0 hs0a hs0b hwk0 hs0a_lt hs0b_lt hpr0 hev0 (Or.inl rfl)
              · rw [hw1] at hwm; rw [hwk1] at hwm; cases hwm
                exact hkept_step 1 k1 o1 gk1 s1a s1b f1a f1b pk1 pw3 TT3.zero TT3.zero
                  hw1 hk_props.2.1.1 ho1.2.2 ho1.1 ho1.2.1 hgk1 hs1a hs1b hwk1 hs1a_lt hs1b_lt hpr1 hev1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
              · rw [hw2] at hwm; rw [hwk2] at hwm; cases hwm
                exact hkept_step 2 k2 o2 gk2 s2a s2b f2a f2b pk2 pw3 pw4 TT3.zero
                  hw2 hk_props.2.2.1.1 ho2.2.2 ho2.1 ho2.2.1 hgk2 hs2a hs2b hwk2 hs2a_lt hs2b_lt hpr2 hev2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
              · rw [hw3] at hwm; rw [hwk3] at hwm; cases hwm
                exact hkept_step 3 k3 o3 gk3 s3a s3b f3a f3b pk3 pw3 pw4 pw5
                  hw3 hk_props.2.2.2.1 ho3.2.2 ho3.1 ho3.2.1 hgk3 hs3a hs3b hwk3 hs3a_lt hs3b_lt hpr3 hev3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
          · -- Clause 2: w = 4 + p and p < 5
            subst heqp
            rw [hwp_eq] at hwm; cases hwm
            have hstep_p : ∀ x : BoolVec 3, xor (evalT x (4 + p)) fp =
                hp_fn (if w_other = 4 then x ⟨x2, hx2_lt⟩ else xor (evalT x w_other) fu) := by
              intro x
              dsimp only [evalT, hp_fn]
              rw [evalWires_gate (insertBit x v true) cm.gates p gp hgp hwfM.2]
              have e_v := hevalT_in x v.val v.isLt
              simp only [↓reduceDIte] at e_v
              dsimp only [evalT] at e_v
              by_cases hw4 : w_other = 4
              · simp only [hw4, ↓reduceIte]
                have h4x := hevalT_4 x
                have h4eq : evalT x 4 = xor (h0_fn (x ⟨x2, hx2_lt⟩)) f0 := by
                  rw [← h4x, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
                dsimp only [evalT] at h4eq
                have hne4v : (4 : Nat) ≠ v.val := by omega
                rcases hw_other_props.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · simp only [h1, h2, hw4, hne4v, ↓reduceIte, e_v, h4eq]
                · simp only [h1, h2, hw4, hne4v, ↓reduceIte, e_v, h4eq]
              · simp only [hw4, ↓reduceIte]
                have hxor : xor (xor (evalT x w_other) fu) fu = evalT x w_other := by
                  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
                dsimp only [evalT] at hxor
                have hnewv : w_other ≠ v.val := hw_other_props.2.1
                rcases hw_other_props.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · simp only [h1, h2, hnewv, ↓reduceIte, e_v, hxor]
                · simp only [h1, h2, hnewv, ↓reduceIte, e_v, hxor]
            have hbase_arg : tt3Of (fun x => if w_other = 4 then x ⟨x2, hx2_lt⟩ else xor (evalT x w_other) fu) = wireTT u_p := by
              by_cases hw4 : w_other = 4
              · simp only [hw4, ↓reduceIte]
                rw [hw4, hw4_eq] at hw_other_map; cases hw_other_map
                rw [htt_x x2 hx2_lt]; exact (hwireTT_getW3 x2 TT3.zero TT3.zero TT3.zero).1 hx2_lt
              · simp only [hw4, ↓reduceIte]
                exact (ih w_other hw_other_props.1 (by omega) hw_other_props.2.1 u_p fu hw_other_map).1 ⟨hw4, by omega⟩
            have hfn_p : (fun x => xor (evalT x (4 + p)) fp) =
                (fun x => hp_fn (if w_other = 4 then x ⟨x2, hx2_lt⟩ else xor (evalT x w_other) fu)) := funext hstep_p
            rw [hfn_p]
            by_cases hch : gpCh = true
            · simp only [hch, ↓reduceIte]
              have hc := hgp_ch hch
              match hm : gpMode with
              | 0 => simp [hc, hm]; rfl
              | 1 => simp [hc, hm]; rfl
              | 2 => simp [hc, hm]; rw [tt3Of_not, hbase_arg]
              | _ + 3 => omega
            · have hchf : gpCh = false := Bool.eq_false_iff.2 hch
              simp only [hchf, Bool.false_eq_true, ↓reduceIte]
              simpa [hgp_unch hchf] using hbase_arg
          · -- Clause 3: w = 4 + p and p = 5
            subst heqp
            obtain ⟨hu6, hfp_eq⟩ := hp5_u6 hp5
            rw [hwp_eq] at hwm; cases hwm
            have hw_ne4 : w_other ≠ 4 := by
              intro h; rw [h, hw4_eq] at hw_other_map; cases hw_other_map; omega
            have hstep_p : ∀ x : BoolVec 3, xor (evalT x (4 + p)) fp = hp_fn (xor (evalT x w_other) fu) := by
              intro x
              dsimp only [evalT, hp_fn]
              simp only [hw_ne4, ↓reduceIte]
              rw [evalWires_gate (insertBit x v true) cm.gates p gp hgp hwfM.2]
              have e_v := hevalT_in x v.val v.isLt
              simp only [↓reduceDIte] at e_v
              dsimp only [evalT] at e_v
              have hxor : xor (xor (evalT x w_other) fu) fu = evalT x w_other := by
                rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
              dsimp only [evalT] at hxor
              have hnewv : w_other ≠ v.val := hw_other_props.2.1
              rcases hw_other_props.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · simp only [h1, h2, hnewv, ↓reduceIte, e_v, hxor]
              · simp only [h1, h2, hnewv, ↓reduceIte, e_v, hxor]
            have hbase_arg : tt3Of (fun x => xor (evalT x w_other) fu) = pw6 := by
              have h1 := (ih w_other hw_other_props.1 (by omega) hw_other_props.2.1 u_p fu hw_other_map).1 ⟨hw_ne4, by omega⟩
              rw [hu6] at h1; exact h1
            have hfn_p : (fun x => xor (evalT x (4 + p)) fp) = (fun x => hp_fn (xor (evalT x w_other) fu)) := funext hstep_p
            rw [hfn_p]
            by_cases hch : gpCh = true
            · simp only [hch, ↓reduceIte]
              have hc := hgp_ch hch
              match hm : gpMode with
              | 0 => simp [hc, hm]; rfl
              | 1 => simp [hc, hm]; rfl
              | 2 => simp [hc, hm]; rw [tt3Of_not, hbase_arg]
              | _ + 3 => omega
            · have hchf : gpCh = false := Bool.eq_false_iff.2 hch
              simp only [hchf, Bool.false_eq_true, ↓reduceIte]
              simpa [hgp_unch hchf] using hbase_arg
      -- Now read off wire 9 = cm.outputWire!
      have hor3_9 : tt3Of (fun x => xor (evalT x 9) pf) = TT3.or3 := by
        rw [← tt3Of_or3]; congr; funext x
        have hc := hflip (insertBit x v true)
        rw [th24_insert_true v x] at hc
        dsimp only [B2Circuit.eval, evalT] at hc ⊢
        rw [hout9] at hc
        rw [hc, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      have h9v : (9 : Nat) ≠ v.val := by omega
      have hinv9 := hinv 9 (by decide) h9v 6 pf hw9_map
      change (if L.outFlip then pw6.not else pw6) = TT3.or3
      by_cases hp5 : p = 5
      · have h9p : (9 : Nat) = 4 + p := by omega
        have hres9 := hinv9.2.2 h9p hp5
        rw [hor3_9] at hres9
        dsimp only [L]
        simp only [hp5, ↓reduceIte]
        by_cases hch : gpCh = true
        · simp only [hch, ↓reduceIte] at hres9 ⊢
          match hm : gpMode with
          | 0 => cases hres9
          | 1 => cases hres9
          | 2 => exact hres9.symm
          | _ + 3 => omega
        · have hchf : gpCh = false := Bool.eq_false_iff.2 hch
          simp only [hchf, Bool.false_eq_true, ↓reduceIte] at hres9 ⊢; exact hres9.symm
      · have hres9 := hinv9.1 ⟨by decide, by omega⟩
        rw [hor3_9] at hres9
        dsimp only [L]
        simp only [hp5, ↓reduceIte]
        exact hres9.symm
    -- Step 6: Verify L.valid and apply fourGateLift_false!
    have hvalid : L.valid := by
      have hm0_val : MaskValid o0.w1 o0.w2 o1.w1 o1.w2 o2.w1 o2.w2 o3.w1 o3.w2 x2 m0 := by
        have h1 : ∀ (s w : Nat) (f : Bool), wmap.getD s (.const false) = .wire w f →
            (g0Ch && (s == 4)) = true → w = x2 := by
          intro s w f hsm hb
          have hs4 : s = 4 := beq_iff_eq.1 (Bool.and_eq_true_iff.1 hb).2
          subst hs4; rw [hw4_eq] at hsm; cases hsm; rfl
        exact ⟨h1 s0a o0.w1 f0a hs0a, h1 s0b o0.w2 f0b hs0b,
               h1 s1a o1.w1 f1a hs1a, h1 s1b o1.w2 f1b hs1b,
               h1 s2a o2.w1 f2a hs2a, h1 s2b o2.w2 f2b hs2b,
               h1 s3a o3.w1 f3a hs3a, h1 s3b o3.w2 f3b hs3b⟩
      have hm1_val : MaskValid o0.w1 o0.w2 o1.w1 o1.w2 o2.w1 o2.w2 o3.w1 o3.w2 L.u m1 := by
        have h1 : ∀ (s w : Nat) (f : Bool), wmap.getD s (.const false) = .wire w f →
            (pLt5 && gpCh && (s == 4 + p)) = true → w = L.u := by
          intro s w f hsm hb
          have h12 := Bool.and_eq_true_iff.1 hb
          have hlt5 : p < 5 := of_decide_eq_true (Bool.and_eq_true_iff.1 h12.1).1
          have hsp : s = 4 + p := beq_iff_eq.1 h12.2
          subst hsp; rw [hwp_eq] at hsm; cases hsm; simp [L, hlt5]
        exact ⟨h1 s0a o0.w1 f0a hs0a, h1 s0b o0.w2 f0b hs0b,
               h1 s1a o1.w1 f1a hs1a, h1 s1b o1.w2 f1b hs1b,
               h1 s2a o2.w1 f2a hs2a, h1 s2b o2.w2 f2b hs2b,
               h1 s3a o3.w1 f3a hs3a, h1 s3b o3.w2 f3b hs3b⟩
      have hdisj : m0.disjoint m1 = true := by
        have hslot : ∀ s : Nat, (!((g0Ch && (s == 4)) && (pLt5 && gpCh && (s == 4 + p)))) = true := by
          intro s
          by_cases h4 : s = 4
          · subst h4; have hne : (4 == 4 + p) = false := beq_false_of_ne (by omega); simp [hne]
          · have hne : (s == 4) = false := beq_false_of_ne h4; simp [hne]
        dsimp only [Mask8.disjoint, m0, m1]
        rw [hslot s0a, hslot s0b, hslot s1a, hslot s1b, hslot s2a, hslot s2b, hslot s3a, hslot s3b]
        rfl
      have houtfl : L.outFlip = true → m1 = Mask8.empty := by
        intro hfl
        dsimp only [L] at hfl
        by_cases hp5 : p = 5
        · have hlt5f : pLt5 = false := by simp [pLt5, hp5]
          dsimp only [m1, Mask8.empty]; simp [hlt5f]
        · simp [hp5] at hfl
      refine ⟨hL_norm, hx2_lt, hg0Mode_lt, ?_, ?_, hm0_val, hm1_val, hdisj, houtfl, hL_base, hL_pert⟩
      · dsimp only [L]; split
        · exact hup_lt6 ‹_›
        · decide
      · dsimp only [L]; split
        · exact hgpMode_lt
        · decide
    exact fourGateLift_false L hvalid

/-! ## 9. Cascading Gate Elimination: `MAJ_5 ≥ 9` → `TH_4^6 ≥ 11` → `MAJ_7 ≥ 13` (`¬ Record 12`) -/

private theorem maj5_lb (c : B2Circuit 5) (hwf : WF 5 c) (hcomp : ComputesUpToNeg c PnP.maj5) :
    9 ≤ c.size := by
  by_cases hge : 9 ≤ c.size
  · exact hge
  · exfalso
    have hle8 : c.size ≤ 8 := by omega
    obtain ⟨cm, hwfM, hnormM, hszM, hposM, houtM, hcompM, _, _⟩ :=
      exists_minimal_norm maj5_nonTrivial ⟨c, hwf, hle8, hcomp⟩
    have hg0_ex : ∃ g0, cm.gates[0]? = some g0 := by
      cases h : cm.gates with
      | nil => simp [B2Circuit.size, h] at hposM
      | cons g0 _ => exact ⟨g0, rfl⟩
    obtain ⟨g0, hg0⟩ := hg0_ex
    obtain ⟨hg0_1, hg0_2, _⟩ := hnormM 0 g0 hg0
    let fi1 : Fin 5 := ⟨g0.w1, by omega⟩
    let fi2 : Fin 5 := ⟨g0.w2, hg0_2⟩
    have hne12 : fi1 ≠ fi2 := fun h => by have := congrArg Fin.val h; dsimp only [fi1, fi2] at this; omega
    obtain ⟨j, gj, hj1, hjlt, hgj, hgj_reads⟩ :=
      fanout_ge_2_of_three_cofactors cm hwfM hposM houtM hcompM g0 hg0 fi1 fi2 rfl rfl hne12
        (maj5_three_cofactors fi1 fi2 hne12)
    have hres_ex : ∃ c' : B2Circuit 4, WF 4 c' ∧ IsNormGates 4 c'.gates ∧ c'.size + 2 ≤ cm.size ∧ ComputesUpToNeg c' th24 := by
      rcases hgj_reads with h | h | h | h
      · exact restrict_circuit th24_nonTrivial cm hwfM hcompM fi1 true (maj5_insert_true fi1)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inl h)
      · exact restrict_circuit th24_nonTrivial cm hwfM hcompM fi1 true (maj5_insert_true fi1)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inr h)
      · exact restrict_circuit th24_nonTrivial cm hwfM hcompM fi2 true (maj5_insert_true fi2)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inl h)
      · exact restrict_circuit th24_nonTrivial cm hwfM hcompM fi2 true (maj5_insert_true fi2)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inr h)
    obtain ⟨c4, hwf4, _, hsz4, hcomp4⟩ := hres_ex
    have hlb := th24_lb c4 hwf4 hcomp4
    omega

private def th64 : BoolFn 6 := PnP.thresh 6 4
private def maj7 : BoolFn 7 := PnP.thresh 7 4

private def b2n (b : Bool) : Nat := if b then 1 else 0
private theorem b2n_true : b2n true = 1 := rfl
private theorem b2n_false : b2n false = 0 := rfl

private theorem if_add_one (c : Bool) (a : Nat) :
    (if c = true then a + 1 else a) = a + b2n c := by
  cases c <;> simp [b2n]

private theorem finRange_5 : List.finRange 5 = [⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩] := rfl
private theorem finRange_6 : List.finRange 6 = [⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩] := rfl
private theorem finRange_7 : List.finRange 7 = [⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩] := rfl

private theorem th64_insert_true (idx : Fin 6) (x : BoolVec 5) :
    th64 (insertBit x idx true) = PnP.maj5 x := by
  unfold th64 PnP.maj5 PnP.thresh
  have hhw : PnP.hammingWeight (insertBit x idx true) = PnP.hammingWeight x + 1 := by
    unfold PnP.hammingWeight
    rw [finRange_6, finRange_5]
    rcases idx with ⟨iv, hiv⟩
    match iv, hiv with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
      simp only [List.foldl_cons, List.foldl_nil, if_add_one]
      dsimp only [insertBit]
      simp only [Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte, b2n_true]
      try omega
  rw [hhw]
  by_cases h : 3 ≤ PnP.hammingWeight x
  · have h4 : 4 ≤ PnP.hammingWeight x + 1 := by omega
    simp [h, h4]
  · have h4 : ¬ (4 ≤ PnP.hammingWeight x + 1) := by omega
    simp [h, h4]

private theorem maj7_insert_false (idx : Fin 7) (x : BoolVec 6) :
    maj7 (insertBit x idx false) = th64 x := by
  unfold maj7 th64 PnP.thresh
  have hhw : PnP.hammingWeight (insertBit x idx false) = PnP.hammingWeight x := by
    unfold PnP.hammingWeight
    rw [finRange_7, finRange_6]
    rcases idx with ⟨iv, hiv⟩
    match iv, hiv with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
      simp only [List.foldl_cons, List.foldl_nil, if_add_one]
      dsimp only [insertBit]
      simp only [Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte, b2n_false]
      try omega
  rw [hhw]

private theorem th64_nonTrivial : IsNonTrivial th64 := by
  constructor
  · intro b; cases b
    · exact ⟨fun _ => true, by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  · intro i b
    have h : ∀ (i : Fin 6) (b : Bool),
        (th64 (fun _ => false) != xor false b) ||
        (th64 (fun j => decide (j = i)) != xor true b) = true := by decide
    rcases Bool.or_eq_true_iff.1 (h i b) with h1 | h2
    · exact ⟨fun _ => false, by simpa using h1⟩
    · exact ⟨fun j => decide (j = i), by simpa using h2⟩

private theorem maj7_nonTrivial : IsNonTrivial maj7 := by
  constructor
  · intro b; cases b
    · exact ⟨fun _ => true, by decide⟩
    · exact ⟨fun _ => false, by decide⟩
  · intro i b
    have h : ∀ (i : Fin 7) (b : Bool),
        (maj7 (fun _ => false) != xor false b) ||
        (maj7 (fun j => decide (j = i)) != xor true b) = true := by decide
    rcases Bool.or_eq_true_iff.1 (h i b) with h1 | h2
    · exact ⟨fun _ => false, by simpa using h1⟩
    · exact ⟨fun j => decide (j = i), by simpa using h2⟩

private theorem th64_three_cofactors (i1 i2 : Fin 6) (hne : i1 ≠ i2) :
    ∀ b1 b2 b3 : Bool,
      (b1 = b2 → ∃ x : BoolVec 6, th64 (setTwo x i1 i2 false false) ≠ th64 (setTwo x i1 i2 false true)) ∧
      (b1 = b3 → ∃ x : BoolVec 6, th64 (setTwo x i1 i2 false false) ≠ th64 (setTwo x i1 i2 true true)) ∧
      (b2 = b3 → ∃ x : BoolVec 6, th64 (setTwo x i1 i2 false true) ≠ th64 (setTwo x i1 i2 true true)) := by
  intro _ _ _
  have h1 : ∀ a b : Fin 6, a ≠ b →
      (List.finRange 6).any (fun j1 =>
        decide (j1 ≠ a ∧ j1 ≠ b) &&
        decide (th64 (setTwo (fun k => decide (k ≠ a ∧ k ≠ b ∧ k ≠ j1)) a b false false) ≠
                th64 (setTwo (fun k => decide (k ≠ a ∧ k ≠ b ∧ k ≠ j1)) a b false true))) = true := by
    decide
  have h2 : ∀ a b : Fin 6, a ≠ b →
      (List.finRange 6).any (fun j1 =>
        (List.finRange 6).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (th64 (setTwo (fun k => decide (k = j1 || k = j2)) a b false false) ≠
                  th64 (setTwo (fun k => decide (k = j1 || k = j2)) a b true true)))) = true := by
    decide
  have h3 : ∀ a b : Fin 6, a ≠ b →
      (List.finRange 6).any (fun j1 =>
        (List.finRange 6).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (th64 (setTwo (fun k => decide (k = j1 || k = j2)) a b false true) ≠
                  th64 (setTwo (fun k => decide (k = j1 || k = j2)) a b true true)))) = true := by
    decide
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · rcases List.any_eq_true.1 (h1 i1 i2 hne) with ⟨j1, _, h1'⟩
    exact ⟨fun k => decide (k ≠ i1 ∧ k ≠ i2 ∧ k ≠ j1), of_decide_eq_true (Bool.and_eq_true_iff.1 h1').2⟩
  · rcases List.any_eq_true.1 (h2 i1 i2 hne) with ⟨j1, _, h2'⟩
    rcases List.any_eq_true.1 h2' with ⟨j2, _, h2''⟩
    exact ⟨fun k => decide (k = j1 || k = j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h2'').2⟩
  · rcases List.any_eq_true.1 (h3 i1 i2 hne) with ⟨j1, _, h3'⟩
    rcases List.any_eq_true.1 h3' with ⟨j2, _, h3''⟩
    exact ⟨fun k => decide (k = j1 || k = j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h3'').2⟩

private theorem maj7_three_cofactors (i1 i2 : Fin 7) (hne : i1 ≠ i2) :
    ∀ b1 b2 b3 : Bool,
      (b1 = b2 → ∃ x : BoolVec 7, maj7 (setTwo x i1 i2 false false) ≠ maj7 (setTwo x i1 i2 false true)) ∧
      (b1 = b3 → ∃ x : BoolVec 7, maj7 (setTwo x i1 i2 false false) ≠ maj7 (setTwo x i1 i2 true true)) ∧
      (b2 = b3 → ∃ x : BoolVec 7, maj7 (setTwo x i1 i2 false true) ≠ maj7 (setTwo x i1 i2 true true)) := by
  intro _ _ _
  have h1 : ∀ a b : Fin 7, a ≠ b →
      (List.finRange 7).any (fun j1 =>
        (List.finRange 7).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (maj7 (setTwo (fun k => decide (k ≠ a ∧ k ≠ b ∧ k ≠ j1 ∧ k ≠ j2)) a b false false) ≠
                  maj7 (setTwo (fun k => decide (k ≠ a ∧ k ≠ b ∧ k ≠ j1 ∧ k ≠ j2)) a b false true)))) = true := by
    decide
  have h2 : ∀ a b : Fin 7, a ≠ b →
      (List.finRange 7).any (fun j1 =>
        (List.finRange 7).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (maj7 (setTwo (fun k => decide (k = j1 || k = j2)) a b false false) ≠
                  maj7 (setTwo (fun k => decide (k = j1 || k = j2)) a b true true)))) = true := by
    decide
  have h3 : ∀ a b : Fin 7, a ≠ b →
      (List.finRange 7).any (fun j1 =>
        (List.finRange 7).any (fun j2 =>
          decide (j1 ≠ j2 ∧ j1 ≠ a ∧ j1 ≠ b ∧ j2 ≠ a ∧ j2 ≠ b) &&
          decide (maj7 (setTwo (fun k => decide (k = j1 || k = j2)) a b false true) ≠
                  maj7 (setTwo (fun k => decide (k = j1 || k = j2)) a b true true)))) = true := by
    decide
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · rcases List.any_eq_true.1 (h1 i1 i2 hne) with ⟨j1, _, h1'⟩
    rcases List.any_eq_true.1 h1' with ⟨j2, _, h1''⟩
    exact ⟨fun k => decide (k ≠ i1 ∧ k ≠ i2 ∧ k ≠ j1 ∧ k ≠ j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h1'').2⟩
  · rcases List.any_eq_true.1 (h2 i1 i2 hne) with ⟨j1, _, h2'⟩
    rcases List.any_eq_true.1 h2' with ⟨j2, _, h2''⟩
    exact ⟨fun k => decide (k = j1 || k = j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h2'').2⟩
  · rcases List.any_eq_true.1 (h3 i1 i2 hne) with ⟨j1, _, h3'⟩
    rcases List.any_eq_true.1 h3' with ⟨j2, _, h3''⟩
    exact ⟨fun k => decide (k = j1 || k = j2), of_decide_eq_true (Bool.and_eq_true_iff.1 h3'').2⟩

private theorem th64_lb (c : B2Circuit 6) (hwf : WF 6 c) (hcomp : ComputesUpToNeg c th64) :
    11 ≤ c.size := by
  by_cases hge : 11 ≤ c.size
  · exact hge
  · exfalso
    have hle10 : c.size ≤ 10 := by omega
    obtain ⟨cm, hwfM, hnormM, hszM, hposM, houtM, hcompM, _, _⟩ :=
      exists_minimal_norm th64_nonTrivial ⟨c, hwf, hle10, hcomp⟩
    have hg0_ex : ∃ g0, cm.gates[0]? = some g0 := by
      cases h : cm.gates with
      | nil => simp [B2Circuit.size, h] at hposM
      | cons g0 _ => exact ⟨g0, rfl⟩
    obtain ⟨g0, hg0⟩ := hg0_ex
    obtain ⟨hg0_1, hg0_2, _⟩ := hnormM 0 g0 hg0
    let fi1 : Fin 6 := ⟨g0.w1, by omega⟩
    let fi2 : Fin 6 := ⟨g0.w2, hg0_2⟩
    have hne12 : fi1 ≠ fi2 := fun h => by have := congrArg Fin.val h; dsimp only [fi1, fi2] at this; omega
    obtain ⟨j, gj, hj1, hjlt, hgj, hgj_reads⟩ :=
      fanout_ge_2_of_three_cofactors cm hwfM hposM houtM hcompM g0 hg0 fi1 fi2 rfl rfl hne12
        (th64_three_cofactors fi1 fi2 hne12)
    have hres_ex : ∃ c' : B2Circuit 5, WF 5 c' ∧ IsNormGates 5 c'.gates ∧ c'.size + 2 ≤ cm.size ∧ ComputesUpToNeg c' PnP.maj5 := by
      rcases hgj_reads with h | h | h | h
      · exact restrict_circuit maj5_nonTrivial cm hwfM hcompM fi1 true (th64_insert_true fi1)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inl h)
      · exact restrict_circuit maj5_nonTrivial cm hwfM hcompM fi1 true (th64_insert_true fi1)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inr h)
      · exact restrict_circuit maj5_nonTrivial cm hwfM hcompM fi2 true (th64_insert_true fi2)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inl h)
      · exact restrict_circuit maj5_nonTrivial cm hwfM hcompM fi2 true (th64_insert_true fi2)
          0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inr h)
    obtain ⟨c5, hwf5, _, hsz5, hcomp5⟩ := hres_ex
    have hlb := maj5_lb c5 hwf5 hcomp5
    omega

theorem record : ¬ PnP.Statements.L_rec_maj7.Record 12 := by
  rintro ⟨c, hwf, hsz, hcomp⟩
  have hwf7 : WF 7 c := hwf
  have hcomp7 : ComputesUpToNeg c maj7 := ⟨false, fun x => by rw [hcomp x, Bool.xor_false]; rfl⟩
  obtain ⟨cm, hwfM, hnormM, hszM, hposM, houtM, hcompM, _, _⟩ :=
    exists_minimal_norm maj7_nonTrivial ⟨c, hwf7, hsz, hcomp7⟩
  have hg0_ex : ∃ g0, cm.gates[0]? = some g0 := by
    cases h : cm.gates with
    | nil => simp [B2Circuit.size, h] at hposM
    | cons g0 _ => exact ⟨g0, rfl⟩
  obtain ⟨g0, hg0⟩ := hg0_ex
  obtain ⟨hg0_1, hg0_2, _⟩ := hnormM 0 g0 hg0
  let fi1 : Fin 7 := ⟨g0.w1, by omega⟩
  let fi2 : Fin 7 := ⟨g0.w2, hg0_2⟩
  have hne12 : fi1 ≠ fi2 := fun h => by have := congrArg Fin.val h; dsimp only [fi1, fi2] at this; omega
  obtain ⟨j, gj, hj1, hjlt, hgj, hgj_reads⟩ :=
    fanout_ge_2_of_three_cofactors cm hwfM hposM houtM hcompM g0 hg0 fi1 fi2 rfl rfl hne12
      (maj7_three_cofactors fi1 fi2 hne12)
  have hres_ex : ∃ c' : B2Circuit 6, WF 6 c' ∧ IsNormGates 6 c'.gates ∧ c'.size + 2 ≤ cm.size ∧ ComputesUpToNeg c' th64 := by
    rcases hgj_reads with h | h | h | h
    · exact restrict_circuit th64_nonTrivial cm hwfM hcompM fi1 false (maj7_insert_false fi1)
        0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inl h)
    · exact restrict_circuit th64_nonTrivial cm hwfM hcompM fi1 false (maj7_insert_false fi1)
        0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inl rfl) (Or.inr h)
    · exact restrict_circuit th64_nonTrivial cm hwfM hcompM fi2 false (maj7_insert_false fi2)
        0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inl h)
    · exact restrict_circuit th64_nonTrivial cm hwfM hcompM fi2 false (maj7_insert_false fi2)
        0 j (by dsimp only [B2Circuit.size] at hposM; omega) hjlt (by omega) g0 gj hg0 hgj (Or.inr rfl) (Or.inr h)
  obtain ⟨c6, hwf6, _, hsz6, hcomp6⟩ := hres_ex
  have hlb := th64_lb c6 hwf6 hcomp6
  omega

end PnP.Lemmas.L_rec_maj7_not_s12
