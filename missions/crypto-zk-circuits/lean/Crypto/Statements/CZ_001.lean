import Crypto.Core

namespace Crypto.Statements.CZ_001

/--
  Foundation Milestone: NIST SP 800-232 Ascon 5-bit S-box with exact 5 non-linear (AND) gates
  and multiplicative depth 1 (optimal non-linear depth for degree-2 S-boxes in FHE/MPC/masking).
-/
def Claim : Prop :=
  ∃ c : Crypto.MultiCircuit 5 5,
    c.IsWellFormed ∧ c.nonLinearCount ≤ 5 ∧ c.andDepth ≤ 1 ∧ c.Computes Crypto.asconSBox

end Crypto.Statements.CZ_001
