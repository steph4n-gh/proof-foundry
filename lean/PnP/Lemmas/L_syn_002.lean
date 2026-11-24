import PnP.Statements.L_syn_002

namespace PnP.Lemmas.L_syn_002

private def maj5Circuit9 : PnP.B2Circuit 5 where
  gates :=
    [ { op := PnP.B2Op.opXor, w1 := 0,  w2 := 1  } -- wire 5: x0 ⊕ x1
    , { op := PnP.B2Op.opXor, w1 := 0,  w2 := 2  } -- wire 6: x0 ⊕ x2
    , { op := PnP.B2Op.opXor, w1 := 2,  w2 := 5  } -- wire 7: x0 ⊕ x1 ⊕ x2
    , { op := PnP.B2Op.opXor, w1 := 4,  w2 := 7  } -- wire 8: x4 ⊕ x0 ⊕ x1 ⊕ x2
    , { op := PnP.B2Op.opXor, w1 := 3,  w2 := 4  } -- wire 9: x3 ⊕ x4
    , { op := PnP.B2Op.opOr,  w1 := 8,  w2 := 9  } -- wire 10: w8 ∨ w9
    , { op := PnP.B2Op.opOr,  w1 := 5,  w2 := 6  } -- wire 11: w5 ∨ w6
    , { op := PnP.B2Op.opAnd, w1 := 10, w2 := 11 } -- wire 12: w10 ∧ w11
    , { op := PnP.B2Op.opXor, w1 := 7,  w2 := 12 } -- wire 13: w7 ⊕ w12 = MAJ5
    ]
  outputWire := 13

private def vec5 (b0 b1 b2 b3 b4 : Bool) : PnP.BoolVec 5
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4

private theorem vec5_eta (x : PnP.BoolVec 5) : x = vec5 (x 0) (x 1) (x 2) (x 3) (x 4) := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

private theorem maj5_check :
    ∀ b0 b1 b2 b3 b4 : Bool,
      maj5Circuit9.eval (vec5 b0 b1 b2 b3 b4) = PnP.maj5 (vec5 b0 b1 b2 b3 b4) := by
  decide +kernel

theorem maj5_ge_10_contest : ¬ PnP.Statements.L_syn_002.Claim := by
  intro hclaim
  have hcomp : maj5Circuit9.Computes PnP.maj5 := by
    intro x
    rw [vec5_eta x]
    exact maj5_check (x 0) (x 1) (x 2) (x 3) (x 4)
  have hge10 := hclaim maj5Circuit9 hcomp
  exact absurd hge10 (by decide)

end PnP.Lemmas.L_syn_002
