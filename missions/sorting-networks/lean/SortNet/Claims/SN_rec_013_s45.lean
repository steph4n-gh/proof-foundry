import SortNet.Statements.SN_rec_013

namespace SortNet.Claims.SN_rec_013_s45

-- Dobbelaere's catalog, https://bertdobbelaere.github.io/sorting_networks.html#N13L45D10
private def network : SortNet.Net 13 :=
  [(0, 12), (1, 10), (2, 9), (3, 7), (5, 11), (6, 8),
   (1, 6), (2, 3), (4, 11), (7, 9), (8, 10),
   (0, 4), (1, 2), (3, 6), (7, 8), (9, 10), (11, 12),
   (4, 6), (5, 9), (8, 11), (10, 12),
   (0, 5), (3, 8), (4, 7), (6, 11), (9, 10),
   (0, 1), (2, 5), (6, 9), (7, 8), (10, 11),
   (1, 3), (2, 4), (5, 6), (9, 10),
   (1, 2), (3, 4), (5, 7), (6, 8),
   (2, 3), (4, 5), (6, 7), (8, 9),
   (3, 4), (5, 6)]

-- Letters a through j denote successive layers. Each suffix is a wire index.
private def circuit (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Bool) : List Bool :=
  let a0 := x0 && x12
  let a12 := x0 || x12
  let a1 := x1 && x10
  let a10 := x1 || x10
  let a2 := x2 && x9
  let a9 := x2 || x9
  let a3 := x3 && x7
  let a7 := x3 || x7
  let a5 := x5 && x11
  let a11 := x5 || x11
  let a6 := x6 && x8
  let a8 := x6 || x8

  let b1 := a1 && a6
  let b6 := a1 || a6
  let b2 := a2 && a3
  let b3 := a2 || a3
  let b4 := x4 && a11
  let b11 := x4 || a11
  let b7 := a7 && a9
  let b9 := a7 || a9
  let b8 := a8 && a10
  let b10 := a8 || a10

  let c0 := a0 && b4
  let c4 := a0 || b4
  let c1 := b1 && b2
  let c2 := b1 || b2
  let c3 := b3 && b6
  let c6 := b3 || b6
  let c7 := b7 && b8
  let c8 := b7 || b8
  let c9 := b9 && b10
  let c10 := b9 || b10
  let c11 := b11 && a12
  let c12 := b11 || a12

  let d4 := c4 && c6
  let d6 := c4 || c6
  let d5 := a5 && c9
  let d9 := a5 || c9
  let d8 := c8 && c11
  let d11 := c8 || c11
  let d10 := c10 && c12
  let d12 := c10 || c12

  let e0 := c0 && d5
  let e5 := c0 || d5
  let e3 := c3 && d8
  let e8 := c3 || d8
  let e4 := d4 && c7
  let e7 := d4 || c7
  let e6 := d6 && d11
  let e11 := d6 || d11
  let e9 := d9 && d10
  let e10 := d9 || d10

  let f0 := e0 && c1
  let f1 := e0 || c1
  let f2 := c2 && e5
  let f5 := c2 || e5
  let f6 := e6 && e9
  let f9 := e6 || e9
  let f7 := e7 && e8
  let f8 := e7 || e8
  let f10 := e10 && e11
  let f11 := e10 || e11

  let g1 := f1 && e3
  let g3 := f1 || e3
  let g2 := f2 && e4
  let g4 := f2 || e4
  let g5 := f5 && f6
  let g6 := f5 || f6
  let g9 := f9 && f10
  let g10 := f9 || f10

  let h1 := g1 && g2
  let h2 := g1 || g2
  let h3 := g3 && g4
  let h4 := g3 || g4
  let h5 := g5 && f7
  let h7 := g5 || f7
  let h6 := g6 && f8
  let h8 := g6 || f8

  let i2 := h2 && h3
  let i3 := h2 || h3
  let i4 := h4 && h5
  let i5 := h4 || h5
  let i6 := h6 && h7
  let i7 := h6 || h7
  let i8 := h8 && g9
  let i9 := h8 || g9

  let j3 := i3 && i4
  let j4 := i3 || i4
  let j5 := i5 && i6
  let j6 := i5 || i6
  [f0, h1, i2, j3, j4, j5, j6, i7, i8, i9, g10, f11, d12]

-- Once the first true wire is reached, all remaining wires must be true.
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

set_option maxHeartbeats 0 in
private theorem certificate : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Bool,
    ordered (circuit x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem record : SortNet.Statements.SN_rec_013.Record 45 := by
  refine ⟨network, by decide, ?_⟩
  intro v
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ (certificate (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
      (v 7) (v 8) (v 9) (v 10) (v 11) (v 12))
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_rec_013_s45
