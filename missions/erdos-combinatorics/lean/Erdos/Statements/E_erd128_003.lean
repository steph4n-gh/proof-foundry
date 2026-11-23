import Erdos.Core

namespace Erdos.Statements.E_erd128_003

/--
  Frozen Wave 4 Statement (Erdős #128 Exact Sharpness at n = 10):
  There exists a triangle-free graph G on 10 vertices that satisfies HasSparseHalf G
  AND whose every induced vertex subset S of size ≥ 5 spans at least 2 edges
  (50 * e(S) ≥ 100 = n²), proving exact tightness of the 1/50 density threshold
  (achieved e.g. by the balanced blow-up C5[2] or the Petersen graph).
-/
def Claim : Prop :=
  ∃ G : Erdos.SimpleGraph 10,
    ¬ Erdos.HasTriangle G ∧
    Erdos.HasSparseHalf G ∧
    ∀ S : Fin 10 → Bool, 5 ≤ Erdos.subsetSize S → 100 ≤ 50 * Erdos.inducedEdgeCount G S

end Erdos.Statements.E_erd128_003
