import PnP.Statements.L_rec_php4

namespace PnP.Lemmas.L_rec_php4_s85

private inductive PTree where
  | leaf (c : PnP.Clause)
  | step (v : Nat) (r : PnP.Clause) (t1 t2 : PTree)

private def PTree.clause : PTree → PnP.Clause
  | .leaf c => c
  | .step _ r _ _ => r

private def PTree.size : PTree → Nat
  | .leaf _ => 1
  | .step _ _ t1 t2 => 1 + t1.size + t2.size

private def checkRes (c1 c2 r : PnP.Clause) (v : Nat) : Bool :=
  c1.contains ⟨v, true⟩ &&
  c2.contains ⟨v, false⟩ &&
  c1.all (fun l => decide (l = ⟨v, true⟩) || r.contains l) &&
  c2.all (fun l => decide (l = ⟨v, false⟩) || r.contains l) &&
  r.all (fun l => (c1.contains l && decide (l ≠ ⟨v, true⟩)) || (c2.contains l && decide (l ≠ ⟨v, false⟩)))

private theorem checkRes_sound {c1 c2 r : PnP.Clause} {v : Nat}
    (h : checkRes c1 c2 r v = true) : PnP.IsResolvent c1 c2 r v := by
  simp only [checkRes, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro l hl hne
    rcases h3 l hl with heq | hr
    · exact absurd heq hne
    · exact hr
  · intro l hl hne
    rcases h4 l hl with heq | hr
    · exact absurd heq hne
    · exact hr
  · intro l hl
    exact h5 l hl

private def checkTree (φ : PnP.CNF) : PTree → Bool
  | .leaf c => φ.contains c
  | .step v r t1 t2 => checkRes t1.clause t2.clause r v && checkTree φ t1 && checkTree φ t2

private def toProof (φ : PnP.CNF) : (t : PTree) → checkTree φ t = true → PnP.ResProof φ t.clause
  | .leaf c, h => .leaf (List.contains_iff_mem.mp h)
  | .step v r t1 t2, h =>
    have h1 : checkRes t1.clause t2.clause r v = true := by
      simp only [checkTree, Bool.and_eq_true] at h; exact h.1.1
    have h2 : checkTree φ t1 = true := by
      simp only [checkTree, Bool.and_eq_true] at h; exact h.1.2
    have h3 : checkTree φ t2 = true := by
      simp only [checkTree, Bool.and_eq_true] at h; exact h.2
    .step (toProof φ t1 h2) (toProof φ t2 h3) (checkRes_sound h1)

private theorem toProof_size (φ : PnP.CNF) :
    ∀ (t : PTree) (h : checkTree φ t = true), (toProof φ t h).size = t.size
  | .leaf _, _ => rfl
  | .step _ _ t1 t2, h => by
    simp only [toProof, PnP.ResProof.size, PTree.size]
    rw [toProof_size φ t1, toProof_size φ t2]

-- Exact minimum-size (85-node) tree-like resolution refutation of PHP(4,3).
private def proofTree : PTree :=
  (.step 0 []
    (.step 1 [⟨0, true⟩]
      (.step 2 [⟨0, true⟩, ⟨1, true⟩]
        (.leaf [⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩])
        (.step 5 [⟨2, false⟩]
          (.step 8 [⟨2, false⟩, ⟨5, true⟩]
            (.step 9 [⟨2, false⟩, ⟨5, true⟩, ⟨8, true⟩]
              (.step 10 [⟨9, true⟩, ⟨2, false⟩, ⟨5, true⟩, ⟨8, true⟩]
                (.step 11 [⟨9, true⟩, ⟨10, true⟩, ⟨2, false⟩]
                  (.leaf [⟨9, true⟩, ⟨10, true⟩, ⟨11, true⟩])
                  (.leaf [⟨2, false⟩, ⟨11, false⟩]))
                (.step 3 [⟨5, true⟩, ⟨10, false⟩, ⟨8, true⟩]
                  (.step 4 [⟨3, true⟩, ⟨5, true⟩, ⟨10, false⟩]
                    (.leaf [⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩])
                    (.leaf [⟨4, false⟩, ⟨10, false⟩]))
                  (.step 6 [⟨8, true⟩, ⟨10, false⟩, ⟨3, false⟩]
                    (.step 7 [⟨6, true⟩, ⟨8, true⟩, ⟨10, false⟩]
                      (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                      (.leaf [⟨7, false⟩, ⟨10, false⟩]))
                    (.leaf [⟨3, false⟩, ⟨6, false⟩]))))
              (.step 3 [⟨5, true⟩, ⟨8, true⟩, ⟨9, false⟩]
                (.step 4 [⟨3, true⟩, ⟨5, true⟩, ⟨8, true⟩, ⟨9, false⟩]
                  (.leaf [⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩])
                  (.step 6 [⟨8, true⟩, ⟨4, false⟩, ⟨9, false⟩]
                    (.step 7 [⟨6, true⟩, ⟨8, true⟩, ⟨4, false⟩]
                      (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                      (.leaf [⟨4, false⟩, ⟨7, false⟩]))
                    (.leaf [⟨6, false⟩, ⟨9, false⟩])))
                (.leaf [⟨3, false⟩, ⟨9, false⟩])))
            (.leaf [⟨2, false⟩, ⟨8, false⟩]))
          (.leaf [⟨2, false⟩, ⟨5, false⟩])))
      (.step 4 [⟨1, false⟩]
        (.step 7 [⟨4, true⟩, ⟨1, false⟩]
          (.step 9 [⟨4, true⟩, ⟨7, true⟩, ⟨1, false⟩]
            (.step 10 [⟨9, true⟩, ⟨4, true⟩, ⟨7, true⟩, ⟨1, false⟩]
              (.step 11 [⟨9, true⟩, ⟨10, true⟩, ⟨4, true⟩, ⟨7, true⟩]
                (.leaf [⟨9, true⟩, ⟨10, true⟩, ⟨11, true⟩])
                (.step 3 [⟨4, true⟩, ⟨11, false⟩, ⟨7, true⟩]
                  (.step 5 [⟨3, true⟩, ⟨4, true⟩, ⟨11, false⟩]
                    (.leaf [⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩])
                    (.leaf [⟨5, false⟩, ⟨11, false⟩]))
                  (.step 6 [⟨7, true⟩, ⟨11, false⟩, ⟨3, false⟩]
                    (.step 8 [⟨6, true⟩, ⟨7, true⟩, ⟨11, false⟩]
                      (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                      (.leaf [⟨8, false⟩, ⟨11, false⟩]))
                    (.leaf [⟨3, false⟩, ⟨6, false⟩]))))
              (.leaf [⟨1, false⟩, ⟨10, false⟩]))
            (.step 3 [⟨4, true⟩, ⟨7, true⟩, ⟨9, false⟩]
              (.step 5 [⟨3, true⟩, ⟨4, true⟩, ⟨7, true⟩, ⟨9, false⟩]
                (.leaf [⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩])
                (.step 6 [⟨7, true⟩, ⟨5, false⟩, ⟨9, false⟩]
                  (.step 8 [⟨6, true⟩, ⟨7, true⟩, ⟨5, false⟩]
                    (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                    (.leaf [⟨5, false⟩, ⟨8, false⟩]))
                  (.leaf [⟨6, false⟩, ⟨9, false⟩])))
              (.leaf [⟨3, false⟩, ⟨9, false⟩])))
          (.leaf [⟨1, false⟩, ⟨7, false⟩]))
        (.leaf [⟨1, false⟩, ⟨4, false⟩])))
    (.step 3 [⟨0, false⟩]
      (.step 6 [⟨3, true⟩, ⟨0, false⟩]
        (.step 9 [⟨3, true⟩, ⟨6, true⟩, ⟨0, false⟩]
          (.step 4 [⟨3, true⟩, ⟨6, true⟩, ⟨9, true⟩]
            (.step 5 [⟨3, true⟩, ⟨4, true⟩, ⟨6, true⟩, ⟨9, true⟩]
              (.leaf [⟨3, true⟩, ⟨4, true⟩, ⟨5, true⟩])
              (.step 7 [⟨6, true⟩, ⟨5, false⟩, ⟨9, true⟩]
                (.step 8 [⟨6, true⟩, ⟨7, true⟩, ⟨5, false⟩]
                  (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                  (.leaf [⟨5, false⟩, ⟨8, false⟩]))
                (.step 10 [⟨9, true⟩, ⟨5, false⟩, ⟨7, false⟩]
                  (.step 11 [⟨9, true⟩, ⟨10, true⟩, ⟨5, false⟩]
                    (.leaf [⟨9, true⟩, ⟨10, true⟩, ⟨11, true⟩])
                    (.leaf [⟨5, false⟩, ⟨11, false⟩]))
                  (.leaf [⟨7, false⟩, ⟨10, false⟩]))))
            (.step 7 [⟨6, true⟩, ⟨9, true⟩, ⟨4, false⟩]
              (.step 8 [⟨6, true⟩, ⟨7, true⟩, ⟨9, true⟩, ⟨4, false⟩]
                (.leaf [⟨6, true⟩, ⟨7, true⟩, ⟨8, true⟩])
                (.step 10 [⟨9, true⟩, ⟨8, false⟩, ⟨4, false⟩]
                  (.step 11 [⟨9, true⟩, ⟨10, true⟩, ⟨8, false⟩]
                    (.leaf [⟨9, true⟩, ⟨10, true⟩, ⟨11, true⟩])
                    (.leaf [⟨8, false⟩, ⟨11, false⟩]))
                  (.leaf [⟨4, false⟩, ⟨10, false⟩])))
              (.leaf [⟨4, false⟩, ⟨7, false⟩])))
          (.leaf [⟨0, false⟩, ⟨9, false⟩]))
        (.leaf [⟨0, false⟩, ⟨6, false⟩]))
      (.leaf [⟨0, false⟩, ⟨3, false⟩])))

private theorem proofTree_ok : checkTree (PnP.PHP 4 3) proofTree = true := by
  decide +kernel

theorem record : PnP.Statements.L_rec_php4.Record 85 := by
  have hsz : (toProof (PnP.PHP 4 3) proofTree proofTree_ok).size = 85 :=
    toProof_size (PnP.PHP 4 3) proofTree proofTree_ok
  exact ⟨toProof (PnP.PHP 4 3) proofTree proofTree_ok, Nat.le_of_eq hsz⟩

end PnP.Lemmas.L_rec_php4_s85
