import SortNet.Statements.SN_rec_014

namespace SortNet.Claims.SN_rec_014_s51

-- Dobbelaere catalog, https://bertdobbelaere.github.io/sorting_networks.html#N14L51D10
private def network : SortNet.Net 14 := [
  (0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11),
  (12, 13), (0, 2), (1, 3), (4, 8), (5, 9), (10, 12),
  (11, 13), (0, 4), (1, 2), (3, 7), (5, 8), (6, 10),
  (9, 13), (11, 12), (0, 6), (1, 5), (3, 9), (4, 10),
  (7, 13), (8, 12), (2, 10), (3, 11), (4, 6), (7, 9),
  (1, 3), (2, 8), (5, 11), (6, 7), (10, 12), (1, 4),
  (2, 6), (3, 5), (7, 11), (8, 10), (9, 12), (2, 4),
  (3, 6), (5, 8), (7, 10), (9, 11), (3, 4), (5, 6),
  (7, 8), (9, 10), (6, 7)
]

private def circuit (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Bool) : List Bool :=
  let t0a := x0 && x1
  let t0b := x0 || x1
  let t1a := x2 && x3
  let t1b := x2 || x3
  let t2a := x4 && x5
  let t2b := x4 || x5
  let t3a := x6 && x7
  let t3b := x6 || x7
  let t4a := x8 && x9
  let t4b := x8 || x9
  let t5a := x10 && x11
  let t5b := x10 || x11
  let t6a := x12 && x13
  let t6b := x12 || x13
  let t7a := t0a && t1a
  let t7b := t0a || t1a
  let t8a := t0b && t1b
  let t8b := t0b || t1b
  let t9a := t2a && t4a
  let t9b := t2a || t4a
  let t10a := t2b && t4b
  let t10b := t2b || t4b
  let t11a := t5a && t6a
  let t11b := t5a || t6a
  let t12a := t5b && t6b
  let t12b := t5b || t6b
  let t13a := t7a && t9a
  let t13b := t7a || t9a
  let t14a := t8a && t7b
  let t14b := t8a || t7b
  let t15a := t8b && t3b
  let t15b := t8b || t3b
  let t16a := t10a && t9b
  let t16b := t10a || t9b
  let t17a := t3a && t11a
  let t17b := t3a || t11a
  let t18a := t10b && t12b
  let t18b := t10b || t12b
  let t19a := t12a && t11b
  let t19b := t12a || t11b
  let t20a := t13a && t17a
  let t20b := t13a || t17a
  let t21a := t14a && t16a
  let t21b := t14a || t16a
  let t22a := t15a && t18a
  let t22b := t15a || t18a
  let t23a := t13b && t17b
  let t23b := t13b || t17b
  let t24a := t15b && t18b
  let t24b := t15b || t18b
  let t25a := t16b && t19b
  let t25b := t16b || t19b
  let t26a := t14b && t23b
  let t26b := t14b || t23b
  let t27a := t22a && t19a
  let t27b := t22a || t19a
  let t28a := t23a && t20b
  let t28b := t23a || t20b
  let t29a := t24a && t22b
  let t29b := t24a || t22b
  let t30a := t21a && t27a
  let t30b := t21a || t27a
  let t31a := t26a && t25a
  let t31b := t26a || t25a
  let t32a := t21b && t27b
  let t32b := t21b || t27b
  let t33a := t28b && t29a
  let t33b := t28b || t29a
  let t34a := t26b && t25b
  let t34b := t26b || t25b
  let t35a := t30a && t28a
  let t35b := t30a || t28a
  let t36a := t31a && t33a
  let t36b := t31a || t33a
  let t37a := t30b && t32a
  let t37b := t30b || t32a
  let t38a := t33b && t32b
  let t38b := t33b || t32b
  let t39a := t31b && t34a
  let t39b := t31b || t34a
  let t40a := t29b && t34b
  let t40b := t29b || t34b
  let t41a := t36a && t35b
  let t41b := t36a || t35b
  let t42a := t37a && t36b
  let t42b := t37a || t36b
  let t43a := t37b && t39a
  let t43b := t37b || t39a
  let t44a := t38a && t39b
  let t44b := t38a || t39b
  let t45a := t40a && t38b
  let t45b := t40a || t38b
  let t46a := t42a && t41b
  let t46b := t42a || t41b
  let t47a := t43a && t42b
  let t47b := t43a || t42b
  let t48a := t44a && t43b
  let t48b := t44a || t43b
  let t49a := t45a && t44b
  let t49b := t45a || t44b
  let t50a := t47b && t48a
  let t50b := t47b || t48a
  [t20a, t35a, t41a, t46a, t46b, t47a, t50a, t50b, t48b, t49a, t49b, t45b, t40b, t24b]

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
private theorem certificate : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Bool,
    ordered (circuit x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem record : SortNet.Statements.SN_rec_014.Record 51 := by
  refine ⟨network, by decide, ?_⟩
  intro v
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ (certificate (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13))
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_rec_014_s51
