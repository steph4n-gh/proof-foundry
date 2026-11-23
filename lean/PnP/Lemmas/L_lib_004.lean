import PnP.Core

namespace PnP.Lemmas.L_lib_004

def snocVec {n : Nat} (x : BoolVec n) (b : Bool) : BoolVec (n + 1) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else b

private inductive WireRef where
  | wire (w : Nat)
  | fixed (b : Bool)

private def WireRef.index : WireRef → Nat
  | .wire w => w
  | .fixed _ => 0

private def WireRef.value : WireRef → Bool → Bool
  | .wire _, b => b
  | .fixed v, _ => v

private def WireRef.read (a : Array Bool) (r : WireRef) : Bool :=
  r.value (a.getD r.index false)

private def WireRef.valid (m : Nat) : WireRef → Prop
  | .wire w => w < m
  | .fixed _ => True

private def pushGate (a : Array Bool) (g : B2Gate) : Array Bool :=
  a.push (g.op.eval (a.getD g.w1 false) (a.getD g.w2 false))

private theorem readPush (a : Array α) (b : α) (w : Nat) (fallback : α) :
    (a.push b).getD w fallback = if w = a.size then b else a.getD w fallback := by
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

private def specialize (op : B2Op) (p q : WireRef) : B2Gate :=
  ⟨⟨op.eval (p.value false) (q.value false), op.eval (p.value false) (q.value true),
    op.eval (p.value true) (q.value false), op.eval (p.value true) (q.value true)⟩,
    p.index, q.index⟩

private theorem evalSpecialize (op : B2Op) (p q : WireRef) (a : Array Bool) :
    (specialize op p q).op.eval (a.getD p.index false) (a.getD q.index false) =
      op.eval (p.read a) (q.read a) := by
  unfold WireRef.read
  generalize a.getD p.index false = u, a.getD q.index false = v
  cases u <;> cases v <;> rfl

private def constantOp (op : B2Op) : Prop :=
  op.b01 = op.b00 ∧ op.b10 = op.b00 ∧ op.b11 = op.b00

private instance (op : B2Op) : Decidable (constantOp op) := by
  unfold constantOp
  infer_instance

private theorem evalConstant (op : B2Op) (h : constantOp op) (a b : Bool) :
    op.eval a b = op.b00 := by
  cases a <;> cases b
  · rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

private def wireRefAt (refs : Array WireRef) (w : Nat) : WireRef :=
  refs.getD w (.fixed false)

-- Each source wire, including each unavailable operand, has a translation.
-- Constant truth tables update the translation without emitting a gate.
private theorem compile {n : Nat} (gs built : List B2Gate) (refs : Array WireRef)
    (old : BoolVec n → Array Bool)
    (hsize : ∀ x, (old x).size = refs.size)
    (hvalid : ∀ w, (wireRefAt refs w).valid (n + built.length))
    (hread : ∀ x w, (wireRefAt refs w).read (B2Circuit.evalWires x built) = (old x).getD w false) :
    ∃ qs : List B2Gate, qs.length ≤ built.length + gs.length ∧
      ∃ rs : Array WireRef, ∀ x w,
        (wireRefAt rs w).read (B2Circuit.evalWires x qs) =
          (gs.foldl pushGate (old x)).getD w false := by
  induction gs generalizing built refs old with
  | nil => exact ⟨built, by simp, refs, hread⟩
  | cons g gs ih =>
    let p := wireRefAt refs g.w1
    let q := wireRefAt refs g.w2
    let gate := specialize g.op p q
    let old' := fun x => pushGate (old x) g
    have hval (x : BoolVec n) :
        (let a := B2Circuit.evalWires x built
         gate.op.eval (a.getD gate.w1 false) (a.getD gate.w2 false)) =
        g.op.eval ((old x).getD g.w1 false) ((old x).getD g.w2 false) := by
      calc
        _ = g.op.eval (p.read (B2Circuit.evalWires x built))
            (q.read (B2Circuit.evalWires x built)) := evalSpecialize g.op p q _
        _ = _ := by rw [hread x g.w1, hread x g.w2]
    by_cases hconstant : constantOp gate.op
    · let rs := refs.push (.fixed gate.op.b00)
      have hv (w : Nat) : (wireRefAt rs w).valid (n + built.length) := by
        simp only [rs, wireRefAt, readPush]
        split
        · trivial
        · exact hvalid w
      have hr (x : BoolVec n) (w : Nat) :
          (wireRefAt rs w).read (B2Circuit.evalWires x built) = (old' x).getD w false := by
        simp only [rs, wireRefAt, old', pushGate, readPush, hsize]
        split
        · simpa only [WireRef.read, WireRef.value, evalConstant gate.op hconstant] using hval x
        · exact hread x w
      obtain ⟨qs, hlen, rs', heval⟩ :=
        ih built rs old' (by intro x; simp [old', pushGate, rs, hsize]) hv hr
      exact ⟨qs, by simp only [List.length_cons]; omega, rs', heval⟩
    · let rs := refs.push (.wire (n + built.length))
      let built' := built ++ [gate]
      have hv (w : Nat) : (wireRefAt rs w).valid (n + built'.length) := by
        simp only [rs, wireRefAt, readPush]
        split
        · simp [WireRef.valid, built']
        · change (wireRefAt refs w).valid (n + built'.length)
          have hv := hvalid w
          cases h : wireRefAt refs w <;> simp [h, WireRef.valid, built'] at hv ⊢
          omega
      have hr (x : BoolVec n) (w : Nat) :
          (wireRefAt rs w).read (B2Circuit.evalWires x built') = (old' x).getD w false := by
        have hstep : B2Circuit.evalWires x built' =
            pushGate (B2Circuit.evalWires x built) gate := by
          simp [built', B2Circuit.evalWires, List.foldl_append, pushGate]
        simp only [rs, wireRefAt, old', hstep, pushGate, readPush, hsize]
        split
        · simpa only [WireRef.read, WireRef.value, WireRef.index, readPush, wireSize, ite_true]
            using hval x
        · have he := hread x w
          have hv := hvalid w
          change (wireRefAt refs w).read (pushGate (B2Circuit.evalWires x built) gate) =
            (old x).getD w false
          cases h : wireRefAt refs w with
          | fixed _ =>
            rw [h] at he
            exact he
          | wire j =>
            rw [h] at he hv
            have hj : j ≠ n + built.length := Nat.ne_of_lt hv
            simpa only [pushGate, WireRef.read, WireRef.value, WireRef.index, readPush,
              wireSize, hj, ite_false] using he
      obtain ⟨qs, hlen, rs', heval⟩ :=
        ih built' rs old' (by intro x; simp [old', pushGate, rs, hsize]) hv hr
      refine ⟨qs, ?_, rs', heval⟩
      simpa [built', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen

private def initialRefs (n : Nat) (b : Bool) : Array WireRef :=
  (Array.ofFn (fun i : Fin n => WireRef.wire i.val)).push (.fixed b)

private theorem initialRead {n : Nat} (x : BoolVec n) (b : Bool) (w : Nat) :
    (wireRefAt (initialRefs n b) w).read (B2Circuit.evalWires x []) =
      (Array.ofFn (snocVec x b)).getD w false := by
  simp only [initialRefs, wireRefAt, readPush, Array.size_ofFn]
  by_cases h : w = n
  · subst w
    simp [WireRef.read, WireRef.value, snocVec]
  · by_cases hl : w < n
    · have hs : w < n + 1 := by omega
      simp [h, hl, hs, WireRef.read, WireRef.value, WireRef.index,
        B2Circuit.evalWires, snocVec]
    · have hs : ¬ w < n + 1 := by omega
      simp [h, hl, hs, WireRef.read, WireRef.value]

private def constantCircuit (n : Nat) (b : Bool) : B2Circuit n :=
  ⟨if b then [⟨⟨true, true, true, true⟩, 0, 0⟩] else [], n⟩

private theorem constantEval {n : Nat} (b : Bool) (x : BoolVec n) :
    (constantCircuit n b).eval x = b := by
  cases b with
  | false => simp [constantCircuit, B2Circuit.eval, B2Circuit.evalWires]
  | true =>
    simp only [constantCircuit, B2Circuit.eval, B2Circuit.evalWires, ite_true,
      List.foldl_cons, List.foldl_nil, readPush, Array.size_ofFn]
    cases (Array.ofFn x).getD 0 false <;> rfl

/-- Restriction costs at most one extra gate, and only for a gate-free
    circuit whose output is the input fixed to true. -/
theorem b2_restrict_size_bound {n : Nat} (c : B2Circuit (n + 1)) (b : Bool) :
    ∃ c' : B2Circuit n,
      c'.size ≤ c.size + (if c.size = 0 ∧ c.outputWire = n ∧ b = true then 1 else 0) ∧
      ∀ x : BoolVec n, c'.eval x = c.eval (snocVec x b) := by
  obtain ⟨gs, out⟩ := c
  cases gs with
  | nil =>
    by_cases ho : out = n
    · subst out
      refine ⟨constantCircuit n b, ?_, ?_⟩
      · cases b <;> simp [constantCircuit, B2Circuit.size]
      · intro x
        rw [constantEval]
        simp [B2Circuit.eval, B2Circuit.evalWires, snocVec]
    · refine ⟨⟨[], out⟩, by simp [B2Circuit.size], ?_⟩
      intro x
      by_cases hl : out < n
      · have hs : out < n + 1 := by omega
        simp [B2Circuit.eval, B2Circuit.evalWires, snocVec, hl, hs]
      · have hs : ¬ out < n + 1 := by omega
        simp [B2Circuit.eval, B2Circuit.evalWires, hl, hs]
  | cons g gs =>
    have hv (w : Nat) : (wireRefAt (initialRefs n b) w).valid n := by
      simp only [wireRefAt, initialRefs, readPush, Array.size_ofFn]
      by_cases h : w = n
      · simp [h, WireRef.valid]
      · by_cases hl : w < n <;> simp [h, hl, WireRef.valid]
    obtain ⟨qs, hlen, refs, heval⟩ := compile (g :: gs) [] (initialRefs n b)
      (fun x => Array.ofFn (snocVec x b)) (by intro x; simp [initialRefs]) (by simpa using hv)
      (fun x w => initialRead x b w)
    cases hr : wireRefAt refs out with
    | fixed a =>
      refine ⟨constantCircuit n a, ?_, ?_⟩
      · cases a <;> simp [B2Circuit.size, constantCircuit]
      · intro x
        rw [constantEval]
        have h := heval x out
        rw [hr] at h
        exact h
    | wire w =>
      refine ⟨⟨qs, w⟩, ?_, ?_⟩
      · simpa [B2Circuit.size] using hlen
      · intro x
        have h := heval x out
        rw [hr] at h
        exact h

theorem b2_restrict_size_le {n : Nat} (c : B2Circuit (n + 1)) (b : Bool)
    (h : 0 < c.size ∨ c.outputWire ≠ n ∨ b = false) :
    ∃ c' : B2Circuit n, c'.size ≤ c.size ∧
      ∀ x : BoolVec n, c'.eval x = c.eval (snocVec x b) := by
  have he : ¬ (c.size = 0 ∧ c.outputWire = n ∧ b = true) := by
    rintro ⟨hs, ho, hb⟩
    rcases h with hp | hne | hf
    · omega
    · exact hne ho
    · simp [hb] at hf
  simpa [he] using b2_restrict_size_bound c b

/-- The extra gate is necessary when the circuit only outputs the input fixed to true. -/
theorem b2_restrict_zero_gate_exception (n : Nat) :
    ¬ ∃ c' : B2Circuit n, c'.size ≤ 0 ∧
      ∀ x : BoolVec n, c'.eval x = (⟨[], n⟩ : B2Circuit (n + 1)).eval (snocVec x true) := by
  rintro ⟨⟨gs, out⟩, hsize, heval⟩
  cases gs with
  | cons g gs => simp [B2Circuit.size] at hsize
  | nil =>
    have h := heval (fun _ => false)
    by_cases ho : out < n <;> simp [B2Circuit.eval, B2Circuit.evalWires, snocVec, ho] at h

end PnP.Lemmas.L_lib_004
