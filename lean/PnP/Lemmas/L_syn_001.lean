import PnP.Statements.L_syn_001

namespace PnP.Lemmas.L_syn_001

private def mod3Circuit : PnP.B2Circuit 4 where
  gates :=
    [ { op := PnP.B2Op.opXor,  w1 := 0, w2 := 1 }  -- wire 4: x0 ⊕ x1
    , { op := PnP.B2Op.opXor,  w1 := 2, w2 := 3 }  -- wire 5: x2 ⊕ x3
    , { op := PnP.B2Op.opOr,   w1 := 0, w2 := 1 }  -- wire 6: x0 ∨ x1
    , { op := PnP.B2Op.opOr,   w1 := 2, w2 := 3 }  -- wire 7: x2 ∨ x3
    , { op := PnP.B2Op.opXor,  w1 := 4, w2 := 5 }  -- wire 8: (x0 ⊕ x1) ⊕ (x2 ⊕ x3)
    , { op := PnP.B2Op.opXnor, w1 := 6, w2 := 7 }  -- wire 9: (x0 ∨ x1) == (x2 ∨ x3)
    , { op := PnP.B2Op.opXnor, w1 := 6, w2 := 8 }  -- wire 10: (x0 ∨ x1) == parity
    , { op := PnP.B2Op.opAnd,  w1 := 9, w2 := 10 } -- wire 11: mod3Eq0 4
    ]
  outputWire := 11

private def vec4 (b0 b1 b2 b3 : Bool) : PnP.BoolVec 4
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3

private theorem vec4_eta (x : PnP.BoolVec 4) : x = vec4 (x 0) (x 1) (x 2) (x 3) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

private theorem mod3_check :
    ∀ b0 b1 b2 b3 : Bool, mod3Circuit.eval (vec4 b0 b1 b2 b3) = PnP.mod3Eq0 4 (vec4 b0 b1 b2 b3) := by
  decide

theorem mod3_4_le_8 : PnP.Statements.L_syn_001.Claim := by
  refine ⟨mod3Circuit, by decide, ?_⟩
  intro x
  rw [vec4_eta x]
  exact mod3_check (x 0) (x 1) (x 2) (x 3)

end PnP.Lemmas.L_syn_001
