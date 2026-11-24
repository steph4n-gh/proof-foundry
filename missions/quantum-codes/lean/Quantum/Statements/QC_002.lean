import Quantum.Core

namespace Quantum.Statements.QC_002

/-- Foundation Milestone: The `[[15, 7, 3]]` Hamming CSS code (weight-8 stabilizers, high rate). -/
def Claim : Prop :=
  ∃ (hx hz lx lz : List (BitVec 15)), Quantum.IsCSSCode 15 7 3 8 hx hz lx lz

end Quantum.Statements.QC_002
