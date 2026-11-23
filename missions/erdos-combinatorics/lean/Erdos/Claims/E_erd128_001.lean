import Erdos.Core

namespace Erdos.Claims.E_erd128_001

private theorem independent_inducedEdgeCount {n : Nat} (G : SimpleGraph n)
    (S : Fin n → Bool) (h : ∀ u v, S u = true → S v = true → G.adj u v = false) :
    inducedEdgeCount G S = 0 := by
  have emptyRow (u : Fin n) (hu : S u = true) :
      (List.finRange n).filter (fun v => decide (u.val < v.val) && S v && G.adj u v) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v _
    cases hv : S v <;> simp [hv, h u v hu]
  let step (acc : Nat) (u : Fin n) :=
    if S u then
      acc + ((List.finRange n).filter (fun v => decide (u.val < v.val) && S v && G.adj u v)).length
    else acc
  have zeroStep (u : Fin n) : step 0 u = 0 := by
    cases hu : S u <;> simp [step, hu, emptyRow u]
  change (List.finRange n).foldl step 0 = 0
  suffices ∀ vertices : List (Fin n), vertices.foldl step 0 = 0 from this _
  intro vertices
  induction vertices with
  | nil => rfl
  | cons u rest ih => simpa only [List.foldl_cons, zeroStep] using ih

theorem bipartite_has_sparse_half (n : Nat) (G : SimpleGraph n) (hb : IsBipartite G) :
    HasSparseHalf G := by
  obtain ⟨color, proper⟩ := hb
  have partition : n = subsetSize color + subsetSize (fun v => !color v) := by
    simpa [subsetSize, List.countP_eq_length_filter] using
      (List.length_eq_countP_add_countP color (l := List.finRange n))
  have colorClass (c : Bool) (size : n / 2 ≤ subsetSize (fun v => color v == c)) :
      HasSparseHalf G := by
    refine ⟨fun v => color v == c, size, ?_⟩
    rw [independent_inducedEdgeCount]
    · simp
    · intro u v hu hv
      simp only [beq_iff_eq] at hu hv
      cases h : G.adj u v
      · rfl
      · exact False.elim (proper u v h (hu.trans hv.symm))
  by_cases h : n / 2 ≤ subsetSize color
  · exact colorClass true (by simpa using h)
  · exact colorClass false (by simpa using (show n / 2 ≤ subsetSize (fun v => !color v) by omega))

end Erdos.Claims.E_erd128_001
