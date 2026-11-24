import Quantum.Core
import Quantum.Statements.QC_001

namespace Quantum.Claims.QC_001

open Quantum

/-- Steane `[[7, 1, 3]]` CSS code: self-dual `[7, 4, 3]` Hamming parity checks (weight 4). -/
def steaneH : List (BitVec 7) := [0x55#7, 0x66#7, 0x78#7]
def steaneL : List (BitVec 7) := [0x7F#7]

theorem steane_7_1_3 : Quantum.Statements.QC_001.Claim := by
  refine ⟨steaneH, steaneH, steaneL, steaneL, ?_⟩
  exact isCSSCode_of_check (basisX := []) (masksX := []) (basisZ := []) (masksZ := []) (by decide +kernel)

end Quantum.Claims.QC_001
