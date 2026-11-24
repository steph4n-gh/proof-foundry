import PnP.Statements.L_syn_003

namespace PnP.Lemmas.L_syn_003

/-- 7-gate shared-wire B2 DAG circuit computing `mod3Eq0 4`. -/
private def mod3Circuit7 : PnP.B2Circuit 4 where
  gates :=
    [ { op := PnP.B2Op.opNor,    w1 := 0, w2 := 1 }  -- wire 4: ¬(x0 ∨ x1)
    , { op := PnP.B2Op.opXnor,   w1 := 3, w2 := 4 }  -- wire 5: x3 ↔ ¬(x0 ∨ x1)
    , { op := PnP.B2Op.opXor,    w1 := 2, w2 := 3 }  -- wire 6: x2 ⊕ x3
    , { op := PnP.B2Op.opAndNot, w1 := 5, w2 := 6 }  -- wire 7: w5 ∧ ¬w6
    , { op := PnP.B2Op.opNand,   w1 := 0, w2 := 1 }  -- wire 8: ¬(x0 ∧ x1)
    , { op := PnP.B2Op.opXor,    w1 := 6, w2 := 8 }  -- wire 9: w6 ⊕ w8
    , { op := PnP.B2Op.opNotAnd, w1 := 7, w2 := 9 }  -- wire 10: ¬w7 ∧ w9 = mod3Eq0 4
    ]
  outputWire := 10

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

private theorem mod3_check7 :
    ∀ b0 b1 b2 b3 : Bool, mod3Circuit7.eval (vec4 b0 b1 b2 b3) = PnP.mod3Eq0 4 (vec4 b0 b1 b2 b3) := by
  decide

theorem mod3_4_le_7_contest : PnP.Statements.L_syn_003.Claim := by
  refine ⟨mod3Circuit7, by decide, ?_⟩
  intro x
  rw [vec4_eta x]
  exact mod3_check7 (x 0) (x 1) (x 2) (x 3)

end PnP.Lemmas.L_syn_003
