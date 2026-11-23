import Erdos.Core

namespace Erdos.Claims.E_tur_001

/-- Count edges from each list entry to entries later in the list. -/
private def forwardEdges {n : Nat} (G : SimpleGraph n) : List (Fin n) → Nat
  | [] => 0
  | u :: rest => rest.countP (G.adj u) + forwardEdges G rest

private theorem forwardEdges_insert {n : Nat} (G : SimpleGraph n) (v : Fin n)
    (before after : List (Fin n)) :
    forwardEdges G (before ++ v :: after) =
      forwardEdges G (before ++ after) + (before ++ after).countP (G.adj v) := by
  induction before with
  | nil => simp [forwardEdges, Nat.add_comm]
  | cons u before ih =>
      simp only [List.cons_append, forwardEdges, List.countP_append, List.countP_cons, ih]
      rw [G.symm u v]
      ac_rfl

private theorem adjacent_counts_le_length {n : Nat} (G : SimpleGraph n)
    (htf : ¬ HasTriangle G) {u v : Fin n} (huv : G.adj u v = true)
    (vertices : List (Fin n)) :
    vertices.countP (G.adj u) + vertices.countP (G.adj v) ≤ vertices.length := by
  rw [List.length_eq_countP_add_countP (G.adj u)]
  apply Nat.add_le_add_left
  apply List.countP_mono_left
  intro w _ hvw
  cases huw : G.adj u w
  · rfl
  · exact (htf ⟨u, v, w, huv, hvw, huw⟩).elim

private theorem forwardEdges_bound {n : Nat} (G : SimpleGraph n) (htf : ¬ HasTriangle G)
    (vertices : List (Fin n)) :
    4 * forwardEdges G vertices ≤ vertices.length * vertices.length := by
  induction hlen : vertices.length using Nat.strongRecOn generalizing vertices with
  | ind k ih =>
      cases vertices with
      | nil => simp [forwardEdges]
      | cons u rest =>
          by_cases empty : rest.countP (G.adj u) = 0
          · rw [forwardEdges, empty, Nat.zero_add]
            have shorter : rest.length < k := by
              simp only [List.length_cons] at hlen
              omega
            exact Nat.le_trans (ih _ shorter rest rfl)
              (Nat.mul_le_mul (Nat.le_of_lt shorter) (Nat.le_of_lt shorter))
          · obtain ⟨v, hv, huv⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero empty)
            obtain ⟨before, after, rfl⟩ := List.append_of_mem hv
            let remaining := before ++ after
            have length_eq : (u :: (before ++ v :: after)).length = remaining.length + 2 := by
              simp only [remaining, List.length_cons, List.length_append]
              omega
            have shorter : remaining.length < k := by omega
            have bound := ih _ shorter remaining rfl
            have incident := adjacent_counts_le_length G htf huv remaining
            have degree_u : (before ++ v :: after).countP (G.adj u) =
                remaining.countP (G.adj u) + 1 := by
              simp only [remaining, List.countP_append, List.countP_cons_of_pos huv, Nat.add_assoc]
            rw [← hlen, length_eq, forwardEdges, forwardEdges_insert, degree_u]
            change 4 * (remaining.countP (G.adj u) + 1 +
              (forwardEdges G remaining + remaining.countP (G.adj v))) ≤
                (remaining.length + 2) * (remaining.length + 2)
            simp only [Nat.mul_add, Nat.add_mul]
            omega

private theorem sum_upper_rows {n : Nat} (G : SimpleGraph n) (vertices : List (Fin n))
    (increasing : vertices.Pairwise (fun u v => u.val < v.val)) :
    (vertices.map (fun u =>
      (vertices.filter (fun v => decide (u.val < v.val) && G.adj u v)).length)).sum =
      forwardEdges G vertices := by
  induction vertices with
  | nil => rfl
  | cons u rest ih =>
      obtain ⟨head_lt, tail_increasing⟩ := List.pairwise_cons.mp increasing
      have headRow :
          (rest.filter (fun v => decide (u.val < v.val) && G.adj u v)) =
            rest.filter (G.adj u) := by
        apply List.filter_congr
        intro v hv
        simp [head_lt v hv]
      have tailRows :
          (rest.map (fun v =>
            ((u :: rest).filter (fun w => decide (v.val < w.val) && G.adj v w)).length)) =
          rest.map (fun v =>
            (rest.filter (fun w => decide (v.val < w.val) && G.adj v w)).length) := by
        apply List.map_congr_left
        intro v hv
        simp [Nat.not_lt_of_ge (Nat.le_of_lt (head_lt v hv))]
      simp only [List.map_cons, List.sum_cons, forwardEdges, List.countP_eq_length_filter]
      rw [tailRows, ih tail_increasing]
      simp [headRow]

theorem mantel_theorem (n : Nat) (G : SimpleGraph n) (htf : ¬ HasTriangle G) :
    4 * edgeCount G ≤ n * n := by
  unfold edgeCount
  rw [← List.foldl_map, ← List.sum_eq_foldl_nat, sum_upper_rows G _ (List.pairwise_lt_finRange n)]
  simpa using forwardEdges_bound G htf (List.finRange n)

end Erdos.Claims.E_tur_001
