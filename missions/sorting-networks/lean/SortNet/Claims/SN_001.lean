import SortNet.Statements.SN_001

namespace SortNet.Claims.SN_001

private def thresh (t x : Nat) : Bool :=
  decide (t ≤ x)

private theorem thresh_min (t a b : Nat) :
    thresh t (Nat.min a b) = (thresh t a && thresh t b) := by
  unfold thresh Nat.min
  by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;> simp [hta, htb] <;> omega

private theorem thresh_max (t a b : Nat) :
    thresh t (Nat.max a b) = (thresh t a || thresh t b) := by
  unfold thresh Nat.max
  by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;> simp [hta, htb] <;> omega

private theorem applyComp_thresh {n : Nat} (t : Nat) (c : Fin n × Fin n) (v : Fin n → Nat) :
    (fun k => thresh t (SortNet.applyCompNat c v k)) =
      SortNet.applyCompBool c (fun k => thresh t (v k)) := by
  funext k
  unfold SortNet.applyCompNat SortNet.applyCompBool
  dsimp only
  split
  · split
    · exact thresh_min t _ _
    · split
      · exact thresh_max t _ _
      · rfl
  · split
    · exact thresh_min t _ _
    · split
      · exact thresh_max t _ _
      · rfl

private theorem eval_thresh {n : Nat} (t : Nat) (net : SortNet.Net n) (v : Fin n → Nat) :
    (fun k => thresh t (SortNet.evalNat net v k)) =
      SortNet.evalBool net (fun k => thresh t (v k)) := by
  unfold SortNet.evalNat SortNet.evalBool
  induction net generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (SortNet.applyCompNat c v), applyComp_thresh]

theorem zero_one_principle : SortNet.Statements.SN_001.Claim := by
  intro n net hbool v i j hij
  let t := SortNet.evalNat net v i
  have hsorted := hbool (fun k => thresh t (v k))
  have heq := eval_thresh t net v
  have hti : SortNet.evalBool net (fun k => thresh t (v k)) i = true := by
    rw [← heq]
    exact decide_eq_true (Nat.le_refl t)
  have htj : SortNet.evalBool net (fun k => thresh t (v k)) j = true :=
    hsorted i j hij hti
  rw [← heq] at htj
  exact of_decide_eq_true htj

end SortNet.Claims.SN_001
