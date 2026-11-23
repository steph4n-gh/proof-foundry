import PnP.Core

namespace PnP.Statements.L_meta_005

/-- Frozen Statement: Exact U2 circuit complexity of 2-bit XOR is 3 (without XOR/XNOR gates). -/
def Claim : Prop :=
  (∃ c : PnP.B2Circuit 2, c.isU2 = true ∧ c.size = 3 ∧ c.Computes PnP.xor2) ∧
  (∀ c : PnP.B2Circuit 2, c.isU2 = true → c.Computes PnP.xor2 → 3 ≤ c.size)

end PnP.Statements.L_meta_005
