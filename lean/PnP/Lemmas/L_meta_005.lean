import PnP.Statements.L_meta_005

namespace PnP.Lemmas.L_meta_005

private def xor2Circuit : PnP.B2Circuit 2 where
  gates :=
    [ { op := PnP.B2Op.opAndNot, w1 := 0, w2 := 1 }
    , { op := PnP.B2Op.opNotAnd, w1 := 0, w2 := 1 }
    , { op := PnP.B2Op.opOr,     w1 := 2, w2 := 3 }
    ]
  outputWire := 4

private def vec2 (a b : Bool) : PnP.BoolVec 2
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

private theorem vec2_eta (x : PnP.BoolVec 2) : x = vec2 (x 0) (x 1) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

private theorem upper_bound :
    ∃ c : PnP.B2Circuit 2, c.isU2 = true ∧ c.size = 3 ∧ c.Computes PnP.xor2 := by
  refine ⟨xor2Circuit, by decide, by decide, ?_⟩
  intro x
  rw [vec2_eta x]
  revert x
  have h : ∀ a b : Bool, xor2Circuit.eval (vec2 a b) = PnP.xor2 (vec2 a b) := by decide
  intro x
  exact h (x 0) (x 1)

private abbrev TT := Bool × Bool × Bool × Bool

private def ttF : TT := (false, false, false, false)
private def ttX0 : TT := (false, false, true, true)
private def ttX1 : TT := (false, true, false, true)
private def ttXor : TT := (false, true, true, false)
private def ttXnor : TT := (true, false, false, true)

private def applyOpTT (op : PnP.B2Op) (t1 t2 : TT) : TT :=
  (op.eval t1.1 t2.1, op.eval t1.2.1 t2.2.1, op.eval t1.2.2.1 t2.2.2.1, op.eval t1.2.2.2 t2.2.2.2)

private def baseTT : Fin 3 → TT
  | ⟨0, _⟩ => ttF
  | ⟨1, _⟩ => ttX0
  | ⟨2, _⟩ => ttX1

private def extTT (g0 : TT) : Fin 4 → TT
  | ⟨0, _⟩ => ttF
  | ⟨1, _⟩ => ttX0
  | ⟨2, _⟩ => ttX1
  | ⟨3, _⟩ => g0

private theorem step1_no_parity :
    ∀ b00 b01 b10 b11 : Bool,
      let op : PnP.B2Op := ⟨b00, b01, b10, b11⟩
      op.isU2 = true →
      ∀ i j : Fin 3,
        applyOpTT op (baseTT i) (baseTT j) ≠ ttXor ∧
        applyOpTT op (baseTT i) (baseTT j) ≠ ttXnor := by
  decide +kernel

private theorem step2_no_xor :
    ∀ g00 g01 g10 g11 : Bool,
      let g0 : TT := (g00, g01, g10, g11)
      g0 ≠ ttXor → g0 ≠ ttXnor →
      ∀ b00 b01 b10 b11 : Bool,
        let op : PnP.B2Op := ⟨b00, b01, b10, b11⟩
        op.isU2 = true →
        ∀ i j : Fin 4,
          applyOpTT op (extTT g0 i) (extTT g0 j) ≠ ttXor := by
  decide +kernel

private def toTT (f : PnP.BoolVec 2 → Bool) : TT :=
  (f (vec2 false false), f (vec2 false true), f (vec2 true false), f (vec2 true true))

private theorem getD_arr2 (w : Nat) :
    ∃ i : Fin 3, toTT (fun x => (#[x 0, x 1] : Array Bool).getD w false) = baseTT i := by
  match w with
  | 0 => exact ⟨1, rfl⟩
  | 1 => exact ⟨2, rfl⟩
  | k + 2 =>
    refine ⟨0, ?_⟩
    simp [toTT, baseTT, ttF, Array.getD]; omega

private theorem getD_arr3 (v0 : PnP.BoolVec 2 → Bool) (w : Nat) :
    ∃ i : Fin 4, toTT (fun x => (#[x 0, x 1, v0 x] : Array Bool).getD w false) = extTT (toTT v0) i := by
  match w with
  | 0 => exact ⟨1, rfl⟩
  | 1 => exact ⟨2, rfl⟩
  | 2 => exact ⟨3, rfl⟩
  | k + 3 =>
    refine ⟨0, ?_⟩
    simp [toTT, extTT, ttF, Array.getD]; omega

private theorem getD_arr4 (v0 v1 : PnP.BoolVec 2 → Bool) (w : Nat) :
    (∃ i : Fin 4, toTT (fun x => (#[x 0, x 1, v0 x, v1 x] : Array Bool).getD w false) = extTT (toTT v0) i) ∨
    toTT (fun x => (#[x 0, x 1, v0 x, v1 x] : Array Bool).getD w false) = toTT v1 := by
  match w with
  | 0 => exact Or.inl ⟨1, rfl⟩
  | 1 => exact Or.inl ⟨2, rfl⟩
  | 2 => exact Or.inl ⟨3, rfl⟩
  | 3 => exact Or.inr rfl
  | k + 4 =>
    refine Or.inl ⟨0, ?_⟩
    simp [toTT, extTT, ttF, Array.getD]; omega

private theorem arr_ofFn2 (x : PnP.BoolVec 2) :
    Array.ofFn (fun i : Fin 2 => x i) = #[x 0, x 1] := by
  rfl

private theorem lower_bound :
    ∀ c : PnP.B2Circuit 2, c.isU2 = true → c.Computes PnP.xor2 → 3 ≤ c.size := by
  intro c hu2 hcomp
  have htt : toTT c.eval = ttXor := by
    unfold toTT ttXor
    rw [hcomp (vec2 false false), hcomp (vec2 false true), hcomp (vec2 true false), hcomp (vec2 true true)]
    rfl
  cases hgates : c.gates with
  | nil =>
    have heval : c.eval = fun x => (#[x 0, x 1] : Array Bool).getD c.outputWire false := by
      funext x
      simp [PnP.B2Circuit.eval, PnP.B2Circuit.evalWires, hgates, arr_ofFn2]
    rw [heval] at htt
    rcases getD_arr2 c.outputWire with ⟨i, hi⟩
    rw [hi] at htt
    match i with
    | ⟨0, _⟩ => simp [baseTT, ttF, ttXor] at htt
    | ⟨1, _⟩ => simp [baseTT, ttX0, ttXor] at htt
    | ⟨2, _⟩ => simp [baseTT, ttX1, ttXor] at htt
  | cons g0 rest =>
    cases rest with
    | nil =>
      have hg0u2 : g0.op.isU2 = true := by
        simpa [PnP.B2Circuit.isU2, hgates] using hu2
      let v0 : PnP.BoolVec 2 → Bool := fun x =>
        g0.op.eval ((#[x 0, x 1] : Array Bool).getD g0.w1 false)
                   ((#[x 0, x 1] : Array Bool).getD g0.w2 false)
      have heval : c.eval = fun x => (#[x 0, x 1, v0 x] : Array Bool).getD c.outputWire false := by
        funext x
        simp [PnP.B2Circuit.eval, PnP.B2Circuit.evalWires, hgates, arr_ofFn2, v0]
      rcases getD_arr2 g0.w1 with ⟨i1, hi1⟩
      rcases getD_arr2 g0.w2 with ⟨i2, hi2⟩
      have hv0_tt : toTT v0 = applyOpTT g0.op (baseTT i1) (baseTT i2) := by
        rw [← hi1, ← hi2]; rfl
      have hne := step1_no_parity g0.op.b00 g0.op.b01 g0.op.b10 g0.op.b11 hg0u2 i1 i2
      rw [← hv0_tt] at hne
      rw [heval] at htt
      rcases getD_arr3 v0 c.outputWire with ⟨i, hi⟩
      rw [hi] at htt
      match i with
      | ⟨0, _⟩ => simp [extTT, ttF, ttXor] at htt
      | ⟨1, _⟩ => simp [extTT, ttX0, ttXor] at htt
      | ⟨2, _⟩ => simp [extTT, ttX1, ttXor] at htt
      | ⟨3, _⟩ => exact absurd htt hne.1
    | cons g1 rest2 =>
      cases rest2 with
      | nil =>
        have hu2' : g0.op.isU2 = true ∧ g1.op.isU2 = true := by
          simpa [PnP.B2Circuit.isU2, hgates] using hu2
        let v0 : PnP.BoolVec 2 → Bool := fun x =>
          g0.op.eval ((#[x 0, x 1] : Array Bool).getD g0.w1 false)
                     ((#[x 0, x 1] : Array Bool).getD g0.w2 false)
        let v1 : PnP.BoolVec 2 → Bool := fun x =>
          g1.op.eval ((#[x 0, x 1, v0 x] : Array Bool).getD g1.w1 false)
                     ((#[x 0, x 1, v0 x] : Array Bool).getD g1.w2 false)
        have heval : c.eval = fun x => (#[x 0, x 1, v0 x, v1 x] : Array Bool).getD c.outputWire false := by
          funext x
          simp [PnP.B2Circuit.eval, PnP.B2Circuit.evalWires, hgates, arr_ofFn2, v0, v1]
        rcases getD_arr2 g0.w1 with ⟨i1, hi1⟩
        rcases getD_arr2 g0.w2 with ⟨i2, hi2⟩
        have hv0_tt : toTT v0 = applyOpTT g0.op (baseTT i1) (baseTT i2) := by
          rw [← hi1, ← hi2]; rfl
        have hne0 := step1_no_parity g0.op.b00 g0.op.b01 g0.op.b10 g0.op.b11 hu2'.1 i1 i2
        rw [← hv0_tt] at hne0
        rcases getD_arr3 v0 g1.w1 with ⟨j1, hj1⟩
        rcases getD_arr3 v0 g1.w2 with ⟨j2, hj2⟩
        have hv1_tt : toTT v1 = applyOpTT g1.op (extTT (toTT v0) j1) (extTT (toTT v0) j2) := by
          rw [← hj1, ← hj2]; rfl
        have hne1 : toTT v1 ≠ ttXor := by
          rw [hv1_tt]
          exact step2_no_xor (toTT v0).1 (toTT v0).2.1 (toTT v0).2.2.1 (toTT v0).2.2.2
            hne0.1 hne0.2 g1.op.b00 g1.op.b01 g1.op.b10 g1.op.b11 hu2'.2 j1 j2
        rw [heval] at htt
        rcases getD_arr4 v0 v1 c.outputWire with ⟨i, hi⟩ | hv1eq
        · rw [hi] at htt
          match i with
          | ⟨0, _⟩ => simp [extTT, ttF, ttXor] at htt
          | ⟨1, _⟩ => simp [extTT, ttX0, ttXor] at htt
          | ⟨2, _⟩ => simp [extTT, ttX1, ttXor] at htt
          | ⟨3, _⟩ => exact absurd htt hne0.1
        · rw [hv1eq] at htt
          exact absurd htt hne1
      | cons _ _ =>
        simp [PnP.B2Circuit.size, hgates]

theorem xor2_exact_u2_size_three : PnP.Statements.L_meta_005.Claim :=
  ⟨upper_bound, lower_bound⟩

end PnP.Lemmas.L_meta_005
