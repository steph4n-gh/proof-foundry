import PnP.Core
import PnP.Statements.L_rec_maj7

namespace PnP.Lemmas.L_rec_maj7_s16

open PnP

/-- 16-gate well-formed B2 circuit for 7-bit Majority (MAJ7), matching the best known
    frontier (16 gates):
    - Gates 0..8 compute `A = MAJ5(x0..x4)` via parity/all-equal cancellation (9 gates).
    - Gates 9..10 compute the mid-band indicator `E = (2 ≤ x0+..+x4 ≤ 3)` in 2 extra gates
      as `(w10 ∧ ¬w11) ⊕ w13`.
    - Gates 11..15 combine with `(x5, x6)` as `A ⊕ (E ∧ (A ⊕ x5) ∧ (A ⊕ x6))` (5 gates). -/
private def circuit : B2Circuit 7 where
  gates :=
    [ { op := B2Op.opXor,    w1 := 0,  w2 := 1  } -- w7  = x0 ⊕ x1
    , { op := B2Op.opXor,    w1 := 0,  w2 := 2  } -- w8  = x0 ⊕ x2
    , { op := B2Op.opXor,    w1 := 2,  w2 := 7  } -- w9  = x0 ⊕ x1 ⊕ x2
    , { op := B2Op.opXor,    w1 := 4,  w2 := 9  } -- w10 = x4 ⊕ w9
    , { op := B2Op.opXor,    w1 := 3,  w2 := 4  } -- w11 = x3 ⊕ x4
    , { op := B2Op.opOr,     w1 := 10, w2 := 11 } -- w12 = w10 ∨ w11
    , { op := B2Op.opOr,     w1 := 7,  w2 := 8  } -- w13 = w7 ∨ w8
    , { op := B2Op.opAnd,    w1 := 12, w2 := 13 } -- w14 = w12 ∧ w13
    , { op := B2Op.opXor,    w1 := 9,  w2 := 14 } -- w15 = A = MAJ5(x0..x4)
    , { op := B2Op.opAndNot, w1 := 10, w2 := 11 } -- w16 = w10 ∧ ¬w11
    , { op := B2Op.opXor,    w1 := 16, w2 := 13 } -- w17 = E = (2 ≤ sum(x0..x4) ≤ 3)
    , { op := B2Op.opXor,    w1 := 15, w2 := 5  } -- w18 = A ⊕ x5
    , { op := B2Op.opXor,    w1 := 15, w2 := 6  } -- w19 = A ⊕ x6
    , { op := B2Op.opAnd,    w1 := 18, w2 := 19 } -- w20 = (A ⊕ x5) ∧ (A ⊕ x6)
    , { op := B2Op.opAnd,    w1 := 17, w2 := 20 } -- w21 = E ∧ w20
    , { op := B2Op.opXor,    w1 := 15, w2 := 21 } -- w22 = MAJ7(x0..x6)
    ]
  outputWire := 22

private def vec7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : BoolVec 7
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6

private theorem vec7_eta (x : BoolVec 7) :
    x = vec7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl

private theorem circuit_wf : PnP.Statements.L_rec_maj7.IsWellFormed circuit := by
  refine ⟨by decide, ?_⟩
  intro i g h
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h
  | 8, h | 9, h | 10, h | 11, h | 12, h | 13, h | 14, h | 15, h =>
    simp [circuit] at h; subst h; decide
  | _ + 16, h => simp [circuit] at h

private theorem circuit_check :
    ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      circuit.eval (vec7 b0 b1 b2 b3 b4 b5 b6) = thresh 7 4 (vec7 b0 b1 b2 b3 b4 b5 b6) := by
  decide +kernel

private theorem circuit_computes : circuit.Computes (thresh 7 4) := by
  intro x
  rw [vec7_eta x]
  exact circuit_check (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem record : PnP.Statements.L_rec_maj7.Record 16 :=
  ⟨circuit, circuit_wf, by decide, circuit_computes⟩

end PnP.Lemmas.L_rec_maj7_s16
