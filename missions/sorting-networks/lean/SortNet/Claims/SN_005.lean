import SortNet.Statements.SN_005

namespace SortNet.Claims.SN_005

/-- Optimal 9-wire sorting network (Floyd's 25-comparator benchmark). -/
private def network : SortNet.Net 9 :=
  [(0, 1), (3, 4), (6, 7),
   (1, 2), (4, 5), (7, 8),
   (0, 1), (3, 4), (6, 7),
   (0, 3), (3, 6), (0, 3),
   (1, 4), (4, 7), (1, 4),
   (2, 5), (5, 8), (2, 5),
   (1, 3), (5, 7), (2, 6),
   (4, 6), (2, 4), (2, 3), (5, 6)]

private def circuit (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Bool) : List Bool :=
  -- Sort triples (0,1,2), (3,4,5), (6,7,8)
  let a0 := x0 && x1; let a1 := x0 || x1
  let a3 := x3 && x4; let a4 := x3 || x4
  let a6 := x6 && x7; let a7 := x6 || x7

  let b1 := a1 && x2; let b2 := a1 || x2
  let b4 := a4 && x5; let b5 := a4 || x5
  let b7 := a7 && x8; let b8 := a7 || x8

  let c0 := a0 && b1; let c1 := a0 || b1
  let c3 := a3 && b4; let c4 := a3 || b4
  let c6 := a6 && b7; let c7 := a6 || b7

  -- Sort columns (0,3,6), (1,4,7), (2,5,8)
  let d0 := c0 && c3; let d3 := c0 || c3
  let e3 := d3 && c6; let e6 := d3 || c6
  let f0 := d0 && e3; let f3 := d0 || e3

  let d1 := c1 && c4; let d4 := c1 || c4
  let e4 := d4 && c7; let e7 := d4 || c7
  let f1 := d1 && e4; let f4 := d1 || e4

  let d2 := b2 && b5; let d5 := b2 || b5
  let e5 := d5 && b8; let e8 := d5 || b8
  let f2 := d2 && e5; let f5 := d2 || e5

  -- Final 7 comparators: (1,3), (5,7), (2,6), (4,6), (2,4), (2,3), (5,6)
  let g1 := f1 && f3; let g3 := f1 || f3
  let g5 := f5 && e7; let g7 := f5 || e7
  let g2 := f2 && e6; let g6 := f2 || e6

  let h4 := f4 && g6; let h6 := f4 || g6
  let i2 := g2 && h4; let i4 := g2 || h4
  let j2 := i2 && g3; let j3 := i2 || g3
  let j5 := g5 && h6; let j6 := g5 || h6
  [f0, g1, j2, j3, i4, j5, j6, g7, e8]

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

private theorem certificate : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 : Bool,
    ordered (circuit x0 x1 x2 x3 x4 x5 x6 x7 x8) = true := by
  decide +kernel

theorem optimal_9_sorter : SortNet.Statements.SN_005.Claim := by
  refine ⟨network, by decide, ?_⟩
  intro v
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ (certificate (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_005
