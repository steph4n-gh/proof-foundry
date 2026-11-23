import PnP.Core

namespace PnP.Lemmas.L_lib_002
open PnP

theorem unused_input_invariant {n : Nat} (c : Circuit n) (i : Fin n)
    (hu : c.usesInput i = false) (x : BoolVec n) :
    c.eval (flipBit x i) = c.eval x := by
  induction c with
  | input j =>
    have hj : j ≠ i := by simpa [Circuit.usesInput] using hu
    simp [Circuit.eval, flipBit, hj]
  | const b => rfl
  | not c ih =>
    simp only [Circuit.usesInput] at hu
    simp [Circuit.eval, ih hu]
  | and a b iha ihb =>
    simp only [Circuit.usesInput, Bool.or_eq_false_iff] at hu
    simp [Circuit.eval, iha hu.1, ihb hu.2]
  | or a b iha ihb =>
    simp only [Circuit.usesInput, Bool.or_eq_false_iff] at hu
    simp [Circuit.eval, iha hu.1, ihb hu.2]
  | xor a b iha ihb =>
    simp only [Circuit.usesInput, Bool.or_eq_false_iff] at hu
    simp [Circuit.eval, iha hu.1, ihb hu.2]

end PnP.Lemmas.L_lib_002
