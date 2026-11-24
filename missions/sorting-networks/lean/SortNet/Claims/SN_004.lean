import SortNet.Statements.SN_004

namespace SortNet.Claims.SN_004

/-- Optimal 8-wire Batcher/Green sorting network: 19 comparators, parallel depth 6. -/
private def network : SortNet.Net 8 :=
  [(0, 1), (2, 3), (4, 5), (6, 7),
   (0, 2), (1, 3), (4, 6), (5, 7),
   (1, 2), (5, 6), (0, 4), (3, 7),
   (1, 5), (2, 6),
   (2, 4), (3, 5),
   (1, 2), (3, 4), (5, 6)]

private def circuit (x0 x1 x2 x3 x4 x5 x6 x7 : Bool) : List Bool :=
  let a0 := x0 && x1
  let a1 := x0 || x1
  let a2 := x2 && x3
  let a3 := x2 || x3
  let a4 := x4 && x5
  let a5 := x4 || x5
  let a6 := x6 && x7
  let a7 := x6 || x7

  let b0 := a0 && a2
  let b2 := a0 || a2
  let b1 := a1 && a3
  let b3 := a1 || a3
  let b4 := a4 && a6
  let b6 := a4 || a6
  let b5 := a5 && a7
  let b7 := a5 || a7

  let c1 := b1 && b2
  let c2 := b1 || b2
  let c5 := b5 && b6
  let c6 := b5 || b6
  let c0 := b0 && b4
  let c4 := b0 || b4
  let c3 := b3 && b7
  let c7 := b3 || b7

  let d1 := c1 && c5
  let d5 := c1 || c5
  let d2 := c2 && c6
  let d6 := c2 || c6

  let e2 := d2 && c4
  let e4 := d2 || c4
  let e3 := c3 && d5
  let e5 := c3 || d5

  let f1 := d1 && e2
  let f2 := d1 || e2
  let f3 := e3 && e4
  let f4 := e3 || e4
  let f5 := e5 && d6
  let f6 := e5 || d6
  [c0, f1, f2, f3, f4, f5, f6, c7]

private def ordered : List Bool → Bool
  | [] => true
  | false :: xs => ordered xs
  | true :: xs => xs.all id

private theorem ordered_pairwise (xs : List Bool) (h : ordered xs = true) :
    xs.Pairwise (· ≤ ·) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    cases x with
    | false => exact .cons (fun y _ => Bool.false_le y) (ih h)
    | true =>
      have allTrue := List.all_eq_true.mp (show xs.all id = true from h)
      apply List.pairwise_of_forall_mem_list
      intro a _ b hb
      have : b = true := by
        rcases List.mem_cons.mp hb with h | h
        · exact h
        · exact allTrue b h
      simp [this]

private theorem certificate : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : Bool,
    ordered (circuit x0 x1 x2 x3 x4 x5 x6 x7) = true := by
  decide +kernel

theorem optimal_8_sorter : SortNet.Statements.SN_004.Claim := by
  refine ⟨network, by decide, by decide, ?_⟩
  intro v
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ (certificate (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7))
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_004
