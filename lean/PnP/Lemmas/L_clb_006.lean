import PnP.Core

namespace PnP.Lemmas.L_clb_006

private def pushGate (a : Array Bool) (g : B2Gate) : Array Bool :=
  a.push (g.op.eval (a.getD g.w1 false) (a.getD g.w2 false))

private theorem readPush (a : Array Bool) (b : Bool) (w : Nat) :
    (a.push b).getD w false = if w = a.size then b else a.getD w false := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

private theorem wireSize {n : Nat} (x : BoolVec n) (gs : List B2Gate) :
    (B2Circuit.evalWires x gs).size = n + gs.length := by
  suffices ∀ a : Array Bool, (gs.foldl pushGate a).size = a.size + gs.length by
    change (gs.foldl pushGate (Array.ofFn x)).size = n + gs.length
    simpa only [Array.size_ofFn] using this (Array.ofFn x)
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro a
    rw [List.foldl_cons, ih]
    simp only [pushGate, Array.size_push, List.length_cons]
    omega

private theorem readPreserved {n : Nat} (x : BoolVec n) (gs added : List B2Gate)
    (w : Nat) (hw : w < n + gs.length) :
    (B2Circuit.evalWires x (gs ++ added)).getD w false =
      (B2Circuit.evalWires x gs).getD w false := by
  have preserves (a : Array Bool) (ha : w < a.size) :
      (added.foldl pushGate a).getD w false = a.getD w false := by
    induction added generalizing a with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      · simp only [pushGate, readPush, Nat.ne_of_lt ha, ite_false]
      · simp only [pushGate, Array.size_push]
        omega
  change (List.foldl pushGate (Array.ofFn x) (gs ++ added)).getD w false = _
  rw [List.foldl_append]
  exact preserves (B2Circuit.evalWires x gs) (by simpa only [wireSize] using hw)

private def lastWire (n : Nat) (gs : List B2Gate) : Nat := n + gs.length - 1

private theorem readSnoc {n : Nat} (x : BoolVec n) (gs : List B2Gate) (g : B2Gate)
    (w : Nat) :
    let a := B2Circuit.evalWires x gs
    (B2Circuit.evalWires x (gs ++ [g])).getD w false =
      if w = n + gs.length then g.op.eval (a.getD g.w1 false) (a.getD g.w2 false)
      else a.getD w false := by
  change (List.foldl pushGate (Array.ofFn x) (gs ++ [g])).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [pushGate, readPush]
  change (if w = (B2Circuit.evalWires x gs).size then _ else _) = _
  rw [wireSize]
  rfl

private theorem readLast {n : Nat} (x : BoolVec n) (gs : List B2Gate) (g : B2Gate) :
    let a := B2Circuit.evalWires x gs
    (B2Circuit.evalWires x (gs ++ [g])).getD (lastWire n (gs ++ [g])) false =
      g.op.eval (a.getD g.w1 false) (a.getD g.w2 false) := by
  have h : lastWire n (gs ++ [g]) = n + gs.length := by
    simp [lastWire]
  simp only [h, readSnoc, ite_true]

private def input {n : Nat} (x : BoolVec n) (w : Nat) : Bool :=
  (Array.ofFn x).getD w false

private theorem readInput {n : Nat} (x : BoolVec n) (gs : List B2Gate)
    (w : Nat) (h : w < n) :
    (B2Circuit.evalWires x gs).getD w false = input x w :=
  readPreserved x [] gs w (by simpa using h)

private def edge {n : Nat} (x : BoolVec n) (w : Nat) : Bool :=
  input x w && input x ((w + 1) % n)

private theorem cyclicEq {n : Nat} (x : BoolVec n) (hn : 0 < n) :
    cyclicAdj n x = (List.range n).any (edge x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [cyclicAdj, dite_eq_left hn, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨i.val, i.isLt, ?_⟩
    simpa [edge, input, i.isLt, Nat.mod_lt _ hn] using hi
  · rintro ⟨w, hw, he⟩
    refine ⟨⟨w, hw⟩, List.mem_finRange _, ?_⟩
    simpa [edge, input, hw, Nat.mod_lt _ hn] using he

private def andGate (a b : Nat) : B2Gate := ⟨B2Op.opAnd, a, b⟩
private def orGate (a b : Nat) : B2Gate := ⟨B2Op.opOr, a, b⟩

private theorem evalAnd (a b : Bool) : B2Op.opAnd.eval a b = (a && b) := by
  cases a <;> cases b <;> rfl

private theorem evalOr (a b : Bool) : B2Op.opOr.eval a b = (a || b) := by
  cases a <;> cases b <;> rfl

private theorem andU2 (a b : Nat) : (andGate a b).op.isU2 = true := rfl
private theorem orU2 (a b : Nat) : (orGate a b).op.isU2 = true := rfl

-- The pair centered at i + 1 covers edges i and i + 1.
private def appendPair (n i : Nat) (gs : List B2Gate) : List B2Gate :=
  gs ++ [orGate i ((i + 2) % n)] ++ [andGate (i + 1) (n + gs.length)]

private theorem pairSize (n i : Nat) (gs : List B2Gate) :
    (appendPair n i gs).length = gs.length + 2 := by
  simp [appendPair]

private theorem pairU2 (n i : Nat) (gs : List B2Gate)
    (h : gs.all (fun g => g.op.isU2) = true) :
    (appendPair n i gs).all (fun g => g.op.isU2) = true := by
  simp [appendPair, h, andU2, orU2]

private theorem pairEval {n : Nat} (x : BoolVec n) (i : Nat)
    (gs : List B2Gate) (hi : i + 2 ≤ n) :
    (B2Circuit.evalWires x (appendPair n i gs)).getD
        (lastWire n (appendPair n i gs)) false =
      (edge x i || edge x (i + 1)) := by
  have hleft : i < n := by omega
  have hcenter : i + 1 < n := by omega
  have hright : (i + 2) % n < n := Nat.mod_lt _ (by omega)
  unfold appendPair
  rw [readLast]
  simp only [andGate, evalAnd, readInput x _ _ hcenter, readSnoc,
    ite_true, orGate, evalOr, readInput x _ _ hleft, readInput x _ _ hright]
  simp only [edge, Nat.mod_eq_of_lt hcenter, Bool.and_or_distrib_left]
  rw [Bool.and_comm (input x (i + 1)) (input x i)]

-- Index k represents k + 1 pairs. Each additional pair contributes two
-- gates for the pair itself and one gate to OR it into the preceding result.
private def pairs (n : Nat) : Nat → List B2Gate
  | 0 => appendPair n 0 []
  | k + 1 =>
    let gs := pairs n k
    let next := appendPair n (2 * (k + 1)) gs
    next ++ [orGate (lastWire n gs) (lastWire n next)]

private theorem pairsSize (n k : Nat) : (pairs n k).length = 3 * k + 2 := by
  induction k with
  | zero => simp [pairs, pairSize]
  | succ k ih =>
    simp only [pairs, List.length_append, List.length_cons, List.length_nil, pairSize, ih]
    omega

private theorem pairsU2 (n k : Nat) : (pairs n k).all (fun g => g.op.isU2) = true := by
  induction k with
  | zero => exact pairU2 _ _ _ rfl
  | succ k ih =>
    simp [pairs, pairU2 _ _ _ ih, orU2]

private theorem pairsEval {n : Nat} (x : BoolVec n) (k : Nat) (hk : 2 * (k + 1) ≤ n) :
    (B2Circuit.evalWires x (pairs n k)).getD (lastWire n (pairs n k)) false =
      (List.range (2 * (k + 1))).any (edge x) := by
  induction k with
  | zero =>
    simpa [pairs, show List.range 2 = [0, 1] by decide] using pairEval x 0 [] (by omega)
  | succ k ih =>
    let gs := pairs n k
    let i := 2 * (k + 1)
    let next := appendPair n i gs
    have hprev : lastWire n gs < n + gs.length := by
      simp only [lastWire, gs, pairsSize]
      omega
    have hread := readPreserved x gs ([orGate i ((i + 2) % n)] ++
      [andGate (i + 1) (n + gs.length)]) (lastWire n gs) hprev
    have hprev' : (B2Circuit.evalWires x next).getD (lastWire n gs) false =
        (List.range i).any (edge x) := by
      have hnext : next = gs ++ ([orGate i ((i + 2) % n)] ++
          [andGate (i + 1) (n + gs.length)]) := List.append_assoc _ _ _
      rw [hnext, hread]
      exact ih (by omega)
    change (B2Circuit.evalWires x (next ++ [orGate (lastWire n gs) (lastWire n next)])).getD
      (lastWire n (next ++ [orGate (lastWire n gs) (lastWire n next)])) false = _
    rw [readLast]
    simp only [orGate, evalOr, hprev', show 2 * (k + 1 + 1) = i + 1 + 1 by omega]
    rw [pairEval x i gs (by omega), List.range_succ, List.range_succ]
    simp

theorem cyclicAdj_upper_bound (n : Nat) (hn : 5 ≤ n) :
    ∃ c : B2Circuit n, c.isU2 = true ∧ c.size ≤ n + (n + 1) / 2 - 1 ∧
      c.Computes (cyclicAdj n) := by
  let k := n / 2 - 1
  let i := 2 * (k + 1)
  let gs := pairs n k
  have hi : i ≤ n := by omega
  have hlen : gs.length = 3 * k + 2 := pairsSize n k
  have hparity : n = i ∨ n = i + 1 := by omega
  rcases hparity with he | ho
  · refine ⟨⟨gs, lastWire n gs⟩, pairsU2 _ _, ?_, ?_⟩
    · change gs.length ≤ _
      omega
    · intro x
      change (B2Circuit.evalWires x gs).getD (lastWire n gs) false = cyclicAdj n x
      rw [cyclicEq x (by omega), congrArg List.range he]
      exact pairsEval x k hi
  · let extra := andGate i ((i + 1) % n)
    let next := gs ++ [extra]
    let gates := next ++ [orGate (lastWire n gs) (lastWire n next)]
    refine ⟨⟨gates, lastWire n gates⟩, ?_, ?_, ?_⟩
    · simp [B2Circuit.isU2, gates, next, extra, gs, pairsU2, andU2, orU2]
    · change gates.length ≤ _
      simp only [gates, next, List.length_append, List.length_cons, List.length_nil, hlen]
      omega
    · intro x
      have hprev : lastWire n gs < n + gs.length := by
        simp only [lastWire, hlen]
        omega
      have hread := readPreserved x gs [extra] (lastWire n gs) hprev
      change (B2Circuit.evalWires x gates).getD (lastWire n gates) false = cyclicAdj n x
      rw [cyclicEq x (by omega)]
      simp only [gates, readLast, orGate, evalOr]
      rw [show (B2Circuit.evalWires x next).getD (lastWire n gs) false = _ from hread,
        pairsEval x k hi]
      simp only [next, readLast, extra, andGate, evalAnd,
        readInput x gs _ (show i < n by omega),
        readInput x gs _ (Nat.mod_lt _ (show 0 < n by omega))]
      rw [show List.range n = List.range i ++ [i] by rw [ho, List.range_succ]]
      simp [edge, i]

end PnP.Lemmas.L_clb_006
