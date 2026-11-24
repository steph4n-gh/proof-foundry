import PnP.Statements.L_rec_005

namespace PnP.Lemmas.L_rec_005_s10

private def opImp : PnP.B2Op := ⟨true, true, false, true⟩ -- a → b

-- Exact 10-gate well-formed B2 circuit for MOD3=0 on 5 bits:
-- Encodes (x0+x1+x2) mod 3 using (nz1, p1) in 4 gates and (x3+x4) mod 3 using (nz2, p2) in 2 gates,
-- then tests (nz1 == nz2) ∧ (nz1 → (p1 ⊕ p2)) in 4 gates.
private def mod3Circuit10 : PnP.B2Circuit 5 where
  gates :=
    [ { op := PnP.B2Op.opXor,  w1 := 0, w2 := 1  } -- wire 5: a = x0 ⊕ x1
    , { op := PnP.B2Op.opXor,  w1 := 1, w2 := 2  } -- wire 6: b = x1 ⊕ x2
    , { op := PnP.B2Op.opOr,   w1 := 5, w2 := 6  } -- wire 7: nz1 = a ∨ b ((x0+x1+x2) % 3 ≠ 0)
    , { op := PnP.B2Op.opXor,  w1 := 5, w2 := 2  } -- wire 8: p1 = x0 ⊕ x1 ⊕ x2
    , { op := PnP.B2Op.opOr,   w1 := 3, w2 := 4  } -- wire 9: nz2 = x3 ∨ x4 ((x3+x4) % 3 ≠ 0)
    , { op := PnP.B2Op.opXor,  w1 := 3, w2 := 4  } -- wire 10: p2 = x3 ⊕ x4
    , { op := PnP.B2Op.opXnor, w1 := 7, w2 := 9  } -- wire 11: nz1 == nz2
    , { op := PnP.B2Op.opXor,  w1 := 8, w2 := 10 } -- wire 12: p1 ⊕ p2
    , { op := opImp,           w1 := 7, w2 := 12 } -- wire 13: nz1 → (p1 ⊕ p2)
    , { op := PnP.B2Op.opAnd,  w1 := 11, w2 := 13 } -- wire 14: mod3Eq0 5
    ]
  outputWire := 14

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

private theorem mod3_check :
    ∀ b0 b1 b2 b3 b4 : Bool,
      mod3Circuit10.eval (vec5 b0 b1 b2 b3 b4) = PnP.mod3Eq0 5 (vec5 b0 b1 b2 b3 b4) := by
  decide +kernel

private theorem mod3_wf : PnP.Statements.L_rec_005.IsWellFormed mod3Circuit10 := by
  refine ⟨by decide, ?_⟩
  intro i g hg
  match i with
  | 0 => simp [mod3Circuit10] at hg; subst hg; decide
  | 1 => simp [mod3Circuit10] at hg; subst hg; decide
  | 2 => simp [mod3Circuit10] at hg; subst hg; decide
  | 3 => simp [mod3Circuit10] at hg; subst hg; decide
  | 4 => simp [mod3Circuit10] at hg; subst hg; decide
  | 5 => simp [mod3Circuit10] at hg; subst hg; decide
  | 6 => simp [mod3Circuit10] at hg; subst hg; decide
  | 7 => simp [mod3Circuit10] at hg; subst hg; decide
  | 8 => simp [mod3Circuit10] at hg; subst hg; decide
  | 9 => simp [mod3Circuit10] at hg; subst hg; decide
  | _ + 10 => simp [mod3Circuit10] at hg

theorem record : PnP.Statements.L_rec_005.Record 10 := by
  refine ⟨mod3Circuit10, mod3_wf, by decide, ?_⟩
  intro x
  rw [vec5_eta x]
  exact mod3_check (x 0) (x 1) (x 2) (x 3) (x 4)

end PnP.Lemmas.L_rec_005_s10
