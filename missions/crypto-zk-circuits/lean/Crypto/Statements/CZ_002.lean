import Crypto.Core

namespace Crypto.Statements.CZ_002

/--
  Foundation Milestone: ISO/IEC 29192-2 PRESENT 4-bit S-box with exact multiplicative
  complexity ≤ 4 non-linear gates (matches the known multiplicative optimum MC(PRESENT) = 4).
-/
def Claim : Prop :=
  ∃ c : Crypto.MultiCircuit 4 4,
    c.IsWellFormed ∧ c.nonLinearCount ≤ 4 ∧ c.Computes Crypto.presentSBox

end Crypto.Statements.CZ_002
