import Quantum.Core

namespace Quantum.Statements.QC_001

/-- Foundation Milestone: The Steane `[[7, 1, 3]]` CSS code (weight-4 stabilizers). -/
def Claim : Prop :=
  ∃ (hx hz lx lz : List (BitVec 7)), Quantum.IsCSSCode 7 1 3 4 hx hz lx lz

end Quantum.Statements.QC_001
