import SortNet.Statements.SN_rec_d17

namespace SortNet.Claims.SN_rec_d17_s10

-- 17-wire, 74-comparator, depth-10 sorting network (matching open world record D(17) = 10).
-- Layers 1..3 form two disjoint 8-wire Green-3 hypercubes on {0..7} and {9..16},
-- leaving only 20 * 20 * 2 = 800 reachable states for fast Lean 4 kernel verification.
private def prefixNet : SortNet.Net 17 := [
  (0, 1), (2, 3), (4, 5), (6, 7), (9, 10), (11, 12), (13, 14), (15, 16),
  (0, 2), (1, 3), (4, 6), (5, 7), (9, 11), (10, 12), (13, 15), (14, 16),
  (0, 4), (1, 5), (2, 6), (3, 7), (9, 13), (10, 14), (11, 15), (12, 16)
]

private def suffixNet : SortNet.Net 17 := [
  (0, 9), (1, 10), (2, 11), (3, 12), (4, 13), (5, 14), (6, 15), (7, 16),
  (1, 15), (2, 14), (4, 9), (5, 10), (6, 11), (8, 13), (1, 4), (3, 13),
  (5, 9), (6, 8), (7, 12), (10, 11), (14, 15), (2, 5), (3, 10), (4, 6),
  (7, 14), (8, 9), (11, 13), (12, 15), (1, 4), (3, 6), (5, 8), (7, 11),
  (9, 10), (12, 14), (13, 15), (0, 1), (2, 4), (3, 5), (6, 8), (7, 9),
  (10, 11), (12, 13), (15, 16), (1, 2), (3, 4), (5, 6), (7, 8), (9, 10),
  (11, 12), (13, 14)
]

private def network : SortNet.Net 17 := prefixNet ++ suffixNet

private def g2_0 (k : Fin 6) : Bool := (#v[false, false, false, false, false, true])[k]
private def g2_1 (k : Fin 6) : Bool := (#v[false, false, false, true, true, true])[k]
private def g2_2 (k : Fin 6) : Bool := (#v[false, false, true, false, true, true])[k]
private def g2_3 (k : Fin 6) : Bool := (#v[false, true, true, true, true, true])[k]

private def enc4 (b0 b1 b2 b3 : Bool) : Fin 6 :=
  match b0, b1, b2, b3 with
  | false, false, false, false => ⟨0, by decide⟩
  | true, false, false, false => ⟨1, by decide⟩
  | false, true, false, false => ⟨1, by decide⟩
  | true, true, false, false => ⟨2, by decide⟩
  | false, false, true, false => ⟨1, by decide⟩
  | true, false, true, false => ⟨3, by decide⟩
  | false, true, true, false => ⟨3, by decide⟩
  | true, true, true, false => ⟨4, by decide⟩
  | false, false, false, true => ⟨1, by decide⟩
  | true, false, false, true => ⟨3, by decide⟩
  | false, true, false, true => ⟨3, by decide⟩
  | true, true, false, true => ⟨4, by decide⟩
  | false, false, true, true => ⟨2, by decide⟩
  | true, false, true, true => ⟨4, by decide⟩
  | false, true, true, true => ⟨4, by decide⟩
  | true, true, true, true => ⟨5, by decide⟩

private theorem g2_0_spec (b0 b1 b2 b3 : Bool) : g2_0 (enc4 b0 b1 b2 b3) = ((b0 && b1) && (b2 && b3)) := by
  revert b0 b1 b2 b3; decide +kernel
private theorem g2_1_spec (b0 b1 b2 b3 : Bool) : g2_1 (enc4 b0 b1 b2 b3) = ((b0 || b1) && (b2 || b3)) := by
  revert b0 b1 b2 b3; decide +kernel
private theorem g2_2_spec (b0 b1 b2 b3 : Bool) : g2_2 (enc4 b0 b1 b2 b3) = ((b0 && b1) || (b2 && b3)) := by
  revert b0 b1 b2 b3; decide +kernel
private theorem g2_3_spec (b0 b1 b2 b3 : Bool) : g2_3 (enc4 b0 b1 b2 b3) = ((b0 || b1) || (b2 || b3)) := by
  revert b0 b1 b2 b3; decide +kernel

private def g3_0 (k : Fin 20) : Bool := (#v[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true])[k]
private def g3_1 (k : Fin 20) : Bool := (#v[false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true])[k]
private def g3_2 (k : Fin 20) : Bool := (#v[false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, true, true, true])[k]
private def g3_3 (k : Fin 20) : Bool := (#v[false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true])[k]
private def g3_4 (k : Fin 20) : Bool := (#v[false, false, false, false, false, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true])[k]
private def g3_5 (k : Fin 20) : Bool := (#v[false, false, false, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true])[k]
private def g3_6 (k : Fin 20) : Bool := (#v[false, false, true, false, true, true, false, true, false, true, true, true, true, true, false, true, true, true, true, true])[k]
private def g3_7 (k : Fin 20) : Bool := (#v[false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true])[k]

private def enc8 (u v : Fin 6) : Fin 20 :=
  match u.val, v.val with
  | 0, 0 => ⟨0, by decide⟩
  | 0, 1 => ⟨1, by decide⟩
  | 0, 2 => ⟨2, by decide⟩
  | 0, 3 => ⟨3, by decide⟩
  | 0, 4 => ⟨4, by decide⟩
  | 0, 5 => ⟨5, by decide⟩
  | 1, 0 => ⟨1, by decide⟩
  | 1, 1 => ⟨6, by decide⟩
  | 1, 2 => ⟨7, by decide⟩
  | 1, 3 => ⟨8, by decide⟩
  | 1, 4 => ⟨9, by decide⟩
  | 1, 5 => ⟨10, by decide⟩
  | 2, 0 => ⟨2, by decide⟩
  | 2, 1 => ⟨7, by decide⟩
  | 2, 2 => ⟨11, by decide⟩
  | 2, 3 => ⟨9, by decide⟩
  | 2, 4 => ⟨12, by decide⟩
  | 2, 5 => ⟨13, by decide⟩
  | 3, 0 => ⟨3, by decide⟩
  | 3, 1 => ⟨8, by decide⟩
  | 3, 2 => ⟨9, by decide⟩
  | 3, 3 => ⟨14, by decide⟩
  | 3, 4 => ⟨15, by decide⟩
  | 3, 5 => ⟨16, by decide⟩
  | 4, 0 => ⟨4, by decide⟩
  | 4, 1 => ⟨9, by decide⟩
  | 4, 2 => ⟨12, by decide⟩
  | 4, 3 => ⟨15, by decide⟩
  | 4, 4 => ⟨17, by decide⟩
  | 4, 5 => ⟨18, by decide⟩
  | 5, 0 => ⟨5, by decide⟩
  | 5, 1 => ⟨10, by decide⟩
  | 5, 2 => ⟨13, by decide⟩
  | 5, 3 => ⟨16, by decide⟩
  | 5, 4 => ⟨18, by decide⟩
  | 5, 5 => ⟨19, by decide⟩
  | _, _ => ⟨0, by decide⟩

private theorem g3_0_spec (u v : Fin 6) : g3_0 (enc8 u v) = (g2_0 u && g2_0 v) := by
  revert u v; decide +kernel
private theorem g3_1_spec (u v : Fin 6) : g3_1 (enc8 u v) = (g2_1 u && g2_1 v) := by
  revert u v; decide +kernel
private theorem g3_2_spec (u v : Fin 6) : g3_2 (enc8 u v) = (g2_2 u && g2_2 v) := by
  revert u v; decide +kernel
private theorem g3_3_spec (u v : Fin 6) : g3_3 (enc8 u v) = (g2_3 u && g2_3 v) := by
  revert u v; decide +kernel
private theorem g3_4_spec (u v : Fin 6) : g3_4 (enc8 u v) = (g2_0 u || g2_0 v) := by
  revert u v; decide +kernel
private theorem g3_5_spec (u v : Fin 6) : g3_5 (enc8 u v) = (g2_1 u || g2_1 v) := by
  revert u v; decide +kernel
private theorem g3_6_spec (u v : Fin 6) : g3_6 (enc8 u v) = (g2_2 u || g2_2 v) := by
  revert u v; decide +kernel
private theorem g3_7_spec (u v : Fin 6) : g3_7 (enc8 u v) = (g2_3 u || g2_3 v) := by
  revert u v; decide +kernel

private def circuitAfterL3 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : Bool) : List Bool :=
  let t0a := w0 && w9
  let t0b := w0 || w9
  let t1a := w1 && w10
  let t1b := w1 || w10
  let t2a := w2 && w11
  let t2b := w2 || w11
  let t3a := w3 && w12
  let t3b := w3 || w12
  let t4a := w4 && w13
  let t4b := w4 || w13
  let t5a := w5 && w14
  let t5b := w5 || w14
  let t6a := w6 && w15
  let t6b := w6 || w15
  let t7a := w7 && w16
  let t7b := w7 || w16
  let t8a := t1a && t6b
  let t8b := t1a || t6b
  let t9a := t2a && t5b
  let t9b := t2a || t5b
  let t10a := t4a && t0b
  let t10b := t4a || t0b
  let t11a := t5a && t1b
  let t11b := t5a || t1b
  let t12a := t6a && t2b
  let t12b := t6a || t2b
  let t13a := w8 && t4b
  let t13b := w8 || t4b
  let t14a := t8a && t10a
  let t14b := t8a || t10a
  let t15a := t3a && t13b
  let t15b := t3a || t13b
  let t16a := t11a && t10b
  let t16b := t11a || t10b
  let t17a := t12a && t13a
  let t17b := t12a || t13a
  let t18a := t7a && t3b
  let t18b := t7a || t3b
  let t19a := t11b && t12b
  let t19b := t11b || t12b
  let t20a := t9b && t8b
  let t20b := t9b || t8b
  let t21a := t9a && t16a
  let t21b := t9a || t16a
  let t22a := t15a && t19a
  let t22b := t15a || t19a
  let t23a := t14b && t17a
  let t23b := t14b || t17a
  let t24a := t18a && t20a
  let t24b := t18a || t20a
  let t25a := t17b && t16b
  let t25b := t17b || t16b
  let t26a := t19b && t15b
  let t26b := t19b || t15b
  let t27a := t18b && t20b
  let t27b := t18b || t20b
  let t28a := t14a && t23a
  let t28b := t14a || t23a
  let t29a := t22a && t23b
  let t29b := t22a || t23b
  let t30a := t21b && t25a
  let t30b := t21b || t25a
  let t31a := t24a && t26a
  let t31b := t24a || t26a
  let t32a := t25b && t22b
  let t32b := t25b || t22b
  let t33a := t27a && t24b
  let t33b := t27a || t24b
  let t34a := t26b && t27b
  let t34b := t26b || t27b
  let t35a := t0a && t28a
  let t35b := t0a || t28a
  let t36a := t21a && t28b
  let t36b := t21a || t28b
  let t37a := t29a && t30a
  let t37b := t29a || t30a
  let t38a := t29b && t30b
  let t38b := t29b || t30b
  let t39a := t31a && t32a
  let t39b := t31a || t32a
  let t40a := t32b && t31b
  let t40b := t32b || t31b
  let t41a := t33a && t34a
  let t41b := t33a || t34a
  let t42a := t34b && t7b
  let t42b := t34b || t7b
  let t43a := t35b && t36a
  let t43b := t35b || t36a
  let t44a := t37a && t36b
  let t44b := t37a || t36b
  let t45a := t37b && t38a
  let t45b := t37b || t38a
  let t46a := t39a && t38b
  let t46b := t39a || t38b
  let t47a := t39b && t40a
  let t47b := t39b || t40a
  let t48a := t40b && t41a
  let t48b := t40b || t41a
  let t49a := t41b && t33b
  let t49b := t41b || t33b
  [t35a, t43a, t43b, t44a, t44b, t45a, t45b, t46a, t46b, t47a, t47b, t48a, t48b, t49a, t49b, t42a, t42b]

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
private theorem certificate : ∀ (k1 k2 : Fin 20) (mid : Bool),
    ordered (circuitAfterL3
      (g3_0 k1) (g3_1 k1) (g3_2 k1) (g3_3 k1) (g3_4 k1) (g3_5 k1) (g3_6 k1) (g3_7 k1)
      mid
      (g3_0 k2) (g3_1 k2) (g3_2 k2) (g3_3 k2) (g3_4 k2) (g3_5 k2) (g3_6 k2) (g3_7 k2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem eval_suffix_eq (w : Fin 17 → Bool) :
    List.ofFn (SortNet.evalBool suffixNet w) =
    circuitAfterL3 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8)
      (w 9) (w 10) (w 11) (w 12) (w 13) (w 14) (w 15) (w 16) := rfl

set_option maxRecDepth 8192 in
theorem record : SortNet.Statements.SN_rec_d17.Record 10 := by
  refine ⟨network, by decide, ?_⟩
  intro v
  have hsplit : SortNet.evalBool network v = SortNet.evalBool suffixNet (SortNet.evalBool prefixNet v) := by
    unfold network SortNet.evalBool
    exact List.foldl_append
  have hcert := certificate
    (enc8 (enc4 (v 0) (v 1) (v 2) (v 3)) (enc4 (v 4) (v 5) (v 6) (v 7)))
    (enc8 (enc4 (v 9) (v 10) (v 11) (v 12)) (enc4 (v 13) (v 14) (v 15) (v 16))) (v 8)
  simp only [g3_0_spec, g3_1_spec, g3_2_spec, g3_3_spec, g3_4_spec, g3_5_spec, g3_6_spec, g3_7_spec,
             g2_0_spec, g2_1_spec, g2_2_spec, g2_3_spec] at hcert
  have hord : ordered (List.ofFn (SortNet.evalBool network v)) = true := by
    rw [hsplit, eval_suffix_eq]
    exact hcert
  have sorted : (List.ofFn (SortNet.evalBool network v)).Pairwise (· ≤ ·) :=
    ordered_pairwise _ hord
  intro i j hij hi
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · exact Fin.ext heq ▸ hi
  · have h := sorted.rel_getElem_of_lt (by simp) (by simp) hlt
    simp only [List.getElem_ofFn] at h
    exact Bool.eq_true_of_true_le (hi ▸ h)

end SortNet.Claims.SN_rec_d17_s10
