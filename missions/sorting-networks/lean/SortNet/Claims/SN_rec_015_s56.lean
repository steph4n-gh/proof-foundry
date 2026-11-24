import SortNet.Statements.SN_rec_015

namespace SortNet.Claims.SN_rec_015_s56

-- Dobbelaere catalog, https://bertdobbelaere.github.io/sorting_networks.html#N15L56D10
private def network : SortNet.Net 15 := [
  (1, 2), (3, 10), (4, 14), (5, 8), (6, 13), (7, 12),
  (9, 11), (0, 14), (1, 5), (2, 8), (3, 7), (6, 9),
  (10, 12), (11, 13), (0, 7), (1, 6), (2, 9), (4, 10),
  (5, 11), (8, 13), (12, 14), (0, 6), (2, 4), (3, 5),
  (7, 11), (8, 10), (9, 12), (13, 14), (0, 3), (1, 2),
  (4, 7), (5, 9), (6, 8), (10, 11), (12, 13), (0, 1),
  (2, 3), (4, 6), (7, 9), (10, 12), (11, 13), (1, 2),
  (3, 5), (8, 10), (11, 12), (3, 4), (5, 6), (7, 8),
  (9, 10), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11),
  (5, 6), (7, 8)
]

private def pLo (p : Fin 3) : Bool := p.val == 2
private def pHi (p : Fin 3) : Bool := p.val != 0

private def pair3 (a b : Bool) : Fin 3 :=
  if a then (if b then ⟨2, by omega⟩ else ⟨1, by omega⟩)
  else (if b then ⟨1, by omega⟩ else ⟨0, by omega⟩)

private theorem pLo_pair3 (a b : Bool) : pLo (pair3 a b) = (a && b) := by
  cases a <;> cases b <;> rfl

private theorem pHi_pair3 (a b : Bool) : pHi (pair3 a b) = (a || b) := by
  cases a <;> cases b <;> rfl

private def circuitAfter (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : Bool) : List Bool :=
  let t0a := w0 && w14
  let t0b := w0 || w14
  let t1a := w1 && w5
  let t1b := w1 || w5
  let t2a := w2 && w8
  let t2b := w2 || w8
  let t3a := w3 && w7
  let t3b := w3 || w7
  let t4a := w6 && w9
  let t4b := w6 || w9
  let t5a := w10 && w12
  let t5b := w10 || w12
  let t6a := w11 && w13
  let t6b := w11 || w13
  let t7a := t0a && t3b
  let t7b := t0a || t3b
  let t8a := t1a && t4a
  let t8b := t1a || t4a
  let t9a := t2a && t4b
  let t9b := t2a || t4b
  let t10a := w4 && t5a
  let t10b := w4 || t5a
  let t11a := t1b && t6a
  let t11b := t1b || t6a
  let t12a := t2b && t6b
  let t12b := t2b || t6b
  let t13a := t5b && t0b
  let t13b := t5b || t0b
  let t14a := t7a && t8b
  let t14b := t7a || t8b
  let t15a := t9a && t10a
  let t15b := t9a || t10a
  let t16a := t3a && t11a
  let t16b := t3a || t11a
  let t17a := t7b && t11b
  let t17b := t7b || t11b
  let t18a := t12a && t10b
  let t18b := t12a || t10b
  let t19a := t9b && t13a
  let t19b := t9b || t13a
  let t20a := t12b && t13b
  let t20b := t12b || t13b
  let t21a := t14a && t16a
  let t21b := t14a || t16a
  let t22a := t8a && t15a
  let t22b := t8a || t15a
  let t23a := t15b && t17a
  let t23b := t15b || t17a
  let t24a := t16b && t19a
  let t24b := t16b || t19a
  let t25a := t14b && t18a
  let t25b := t14b || t18a
  let t26a := t18b && t17b
  let t26b := t18b || t17b
  let t27a := t19b && t20a
  let t27b := t19b || t20a
  let t28a := t21a && t22a
  let t28b := t21a || t22a
  let t29a := t22b && t21b
  let t29b := t22b || t21b
  let t30a := t23a && t25a
  let t30b := t23a || t25a
  let t31a := t23b && t24b
  let t31b := t23b || t24b
  let t32a := t26a && t27a
  let t32b := t26a || t27a
  let t33a := t26b && t27b
  let t33b := t26b || t27b
  let t34a := t28b && t29a
  let t34b := t28b || t29a
  let t35a := t29b && t24a
  let t35b := t29b || t24a
  let t36a := t25b && t32a
  let t36b := t25b || t32a
  let t37a := t33a && t32b
  let t37b := t33a || t32b
  let t38a := t35a && t30a
  let t38b := t35a || t30a
  let t39a := t35b && t30b
  let t39b := t35b || t30b
  let t40a := t31a && t36a
  let t40b := t31a || t36a
  let t41a := t31b && t36b
  let t41b := t31b || t36b
  let t42a := t34b && t38a
  let t42b := t34b || t38a
  let t43a := t38b && t39a
  let t43b := t38b || t39a
  let t44a := t39b && t40a
  let t44b := t39b || t40a
  let t45a := t40b && t41a
  let t45b := t40b || t41a
  let t46a := t41b && t37a
  let t46b := t41b || t37a
  let t47a := t43b && t44a
  let t47b := t43b || t44a
  let t48a := t44b && t45a
  let t48b := t44b || t45a
  [t28a, t34a, t42a, t42b, t43a, t47a, t47b, t48a, t48b, t45b, t46a, t46b, t37b, t33b, t20b]

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
private theorem certificate : ∀ (x0 : Bool) (p0 p1 p2 p3 p4 p5 p6 : Fin 3),
    ordered (circuitAfter x0 (pLo p0) (pHi p0) (pLo p1) (pLo p2) (pLo p3) (pLo p4) (pLo p5) (pHi p3) (pLo p6) (pHi p1) (pHi p6) (pHi p5) (pHi p4) (pHi p2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem record : SortNet.Statements.SN_rec_015.Record 56 := by
  refine ⟨network, by decide, ?_⟩
  intro v
  have hcert := certificate (v 0) (pair3 (v 1) (v 2)) (pair3 (v 3) (v 10)) (pair3 (v 4) (v 14)) (pair3 (v 5) (v 8)) (pair3 (v 6) (v 13)) (pair3 (v 7) (v 12)) (pair3 (v 9) (v 11))
  simp only [pLo_pair3, pHi_pair3] at hcert
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ hcert
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_rec_015_s56
