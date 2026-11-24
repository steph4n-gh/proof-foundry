import PnP.Core
import PnP.Statements.L_rec_mod3_6

namespace PnP.Lemmas.L_rec_mod3_6_s12

open PnP

/-- `¬a ∨ b` (implication `a → b`) in full B2. -/
private def opImp : B2Op := ⟨true, true, false, true⟩

/-- 12-gate well-formed B2 circuit for `mod3Eq0 6` (strictly beating the 13-gate catalog frontier):
    - Splits the 6 bits into two 3-bit blocks `(x0, x1, x2)` and `(x3, x4, x5)`.
    - For each 3-bit block, `d = (a ⊕ b) ∨ (a ⊕ c)` indicates `sum ≢ 0 (mod 3)`, while
      `s = a ⊕ b ⊕ c` distinguishes residue 1 (`s = true`) from residue 2 (`s = false`) when `d = true`.
    - Total sum is `0 (mod 3)` iff `(d1 = d2) ∧ (¬d1 ∨ (s1 ⊕ s2))`. -/
private def circuit : B2Circuit 6 where
  gates :=
    [ { op := B2Op.opXor,  w1 := 0,  w2 := 1  } -- w6  = x0 ⊕ x1
    , { op := B2Op.opXor,  w1 := 0,  w2 := 2  } -- w7  = x0 ⊕ x2
    , { op := B2Op.opOr,   w1 := 6,  w2 := 7  } -- w8  = d1 = ¬(x0 = x1 = x2)
    , { op := B2Op.opXor,  w1 := 3,  w2 := 4  } -- w9  = x3 ⊕ x4
    , { op := B2Op.opXor,  w1 := 3,  w2 := 5  } -- w10 = x3 ⊕ x5
    , { op := B2Op.opOr,   w1 := 9,  w2 := 10 } -- w11 = d2 = ¬(x3 = x4 = x5)
    , { op := B2Op.opXor,  w1 := 6,  w2 := 2  } -- w12 = s1 = x0 ⊕ x1 ⊕ x2
    , { op := B2Op.opXor,  w1 := 9,  w2 := 5  } -- w13 = s2 = x3 ⊕ x4 ⊕ x5
    , { op := B2Op.opXor,  w1 := 12, w2 := 13 } -- w14 = s1 ⊕ s2
    , { op := B2Op.opXnor, w1 := 8,  w2 := 11 } -- w15 = (d1 == d2)
    , { op := opImp,       w1 := 8,  w2 := 14 } -- w16 = ¬d1 ∨ (s1 ⊕ s2)
    , { op := B2Op.opAnd,  w1 := 15, w2 := 16 } -- w17 = (d1 == d2) ∧ (¬d1 ∨ (s1 ⊕ s2))
    ]
  outputWire := 17

private def vec6 (b0 b1 b2 b3 b4 b5 : Bool) : BoolVec 6
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5

private theorem vec6_eta (x : BoolVec 6) :
    x = vec6 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl

private theorem circuit_wf : PnP.Statements.L_rec_mod3_6.IsWellFormed circuit := by
  refine ⟨by decide, ?_⟩
  intro i g h
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h
  | 6, h | 7, h | 8, h | 9, h | 10, h | 11, h =>
    simp [circuit] at h; subst h; decide
  | _ + 12, h => simp [circuit] at h

private theorem circuit_check :
    ∀ b0 b1 b2 b3 b4 b5 : Bool,
      circuit.eval (vec6 b0 b1 b2 b3 b4 b5) = mod3Eq0 6 (vec6 b0 b1 b2 b3 b4 b5) := by
  decide +kernel

private theorem circuit_computes : circuit.Computes (mod3Eq0 6) := by
  intro x
  rw [vec6_eta x]
  exact circuit_check (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem record : PnP.Statements.L_rec_mod3_6.Record 12 :=
  ⟨circuit, circuit_wf, by decide, circuit_computes⟩

end PnP.Lemmas.L_rec_mod3_6_s12
