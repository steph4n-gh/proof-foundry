import PnP.Core

/-
  L-lib-000: Smoke-check lemma verifying the PnP.Core foundation compiles
  and the Lean kernel enforces zero-sorry standard axioms.
-/
namespace PnP.Lemmas.L_lib_000

theorem flipBit_involutive {n : Nat} (x : BoolVec n) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  funext j
  simp only [flipBit]
  split
  · next h => subst h; simp
  · rfl

end PnP.Lemmas.L_lib_000
