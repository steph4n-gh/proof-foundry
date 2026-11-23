import Erdos.Core
import Erdos.Statements.E_erd128_003

namespace Erdos.Claims.E_erd128_003

open Erdos

/-- Balanced blow-up C5[2] on 10 vertices: vertex u belongs to part u.val / 2 ∈ Z/5Z,
    with edges between adjacent parts modulo 5. -/
private def c5BlowupAdj (u v : Fin 10) : Bool :=
  let pu := u.val / 2
  let pv := v.val / 2
  ((pu + 1) % 5 == pv) || ((pv + 1) % 5 == pu)

private theorem c5Blowup_symm : ∀ u v : Fin 10, c5BlowupAdj u v = c5BlowupAdj v u := by
  decide

private theorem c5Blowup_loopless : ∀ v : Fin 10, c5BlowupAdj v v = false := by
  decide

private def c5Blowup : SimpleGraph 10 where
  adj := c5BlowupAdj
  symm := c5Blowup_symm
  loopless := c5Blowup_loopless

private theorem c5Blowup_triangleFree : ¬ HasTriangle c5Blowup := by
  unfold HasTriangle
  decide

/-- 5-vertex witness subset {0, 1, 2, 6, 7} spans exactly 2 edges (0-2 and 1-2),
    giving 50 * 2 = 100 = 10^2. -/
private def witnessHalf (v : Fin 10) : Bool :=
  v.val == 0 || v.val == 1 || v.val == 2 || v.val == 6 || v.val == 7

private theorem c5Blowup_hasSparseHalf : HasSparseHalf c5Blowup :=
  ⟨witnessHalf, by decide, by decide⟩

/-- Parameterize any vertex subset S : Fin 10 → Bool by its 10 indicator bits. -/
private def bits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool :=
  fun v => match v.val with
    | 0 => b0
    | 1 => b1
    | 2 => b2
    | 3 => b3
    | 4 => b4
    | 5 => b5
    | 6 => b6
    | 7 => b7
    | 8 => b8
    | _ => b9

private theorem bits_eq (S : Fin 10 → Bool) :
    S = bits (S ⟨0, by decide⟩) (S ⟨1, by decide⟩) (S ⟨2, by decide⟩) (S ⟨3, by decide⟩)
             (S ⟨4, by decide⟩) (S ⟨5, by decide⟩) (S ⟨6, by decide⟩) (S ⟨7, by decide⟩)
             (S ⟨8, by decide⟩) (S ⟨9, by decide⟩) := by
  funext v
  rcases v with ⟨k, hk⟩
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

private theorem all_halves_ge_two :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      5 ≤ subsetSize (bits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) →
      100 ≤ 50 * inducedEdgeCount c5Blowup (bits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) := by
  decide

private theorem c5Blowup_lower :
    ∀ S : Fin 10 → Bool, 5 ≤ subsetSize S → 100 ≤ 50 * inducedEdgeCount c5Blowup S := by
  intro S hS
  rw [bits_eq S] at hS ⊢
  exact all_halves_ge_two _ _ _ _ _ _ _ _ _ _ hS

theorem erdos128_n10_sharpness : Erdos.Statements.E_erd128_003.Claim :=
  ⟨c5Blowup, c5Blowup_triangleFree, c5Blowup_hasSparseHalf, c5Blowup_lower⟩

end Erdos.Claims.E_erd128_003
