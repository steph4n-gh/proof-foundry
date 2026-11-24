import Quantum.Core
import Quantum.Statements.QC_002

namespace Quantum.Claims.QC_002

open Quantum

/-- `[15, 11, 3]` Hamming parity-check matrix rows (each weight 8, mutually orthogonal mod 2). -/
def hamming15H : List (BitVec 15) :=
  [0x5555#15, 0x6666#15, 0x7878#15, 0x7f80#15]

/-- 7 canonical logical X operators in `H^⊥` for the `[[15, 7, 3]]` Hamming CSS code. -/
def hamming15LX : List (BitVec 15) :=
  [0x0007#15, 0x0019#15, 0x002a#15, 0x004b#15, 0x0181#15, 0x0282#15, 0x0888#15]

/-- Symplectic dual logical Z operators in `H^⊥` satisfying `⟨LX[i], LZ[j]⟩ = δ_{ij}` mod 2. -/
def hamming15LZ : List (BitVec 15) :=
  [0x0337#15, 0x093d#15, 0x0a3e#15, 0x0bc0#15, 0x0055#15, 0x0066#15, 0x0078#15]

theorem hamming_15_7_3 : Quantum.Statements.QC_002.Claim := by
  refine ⟨hamming15H, hamming15H, hamming15LX, hamming15LZ, ?_⟩
  exact isCSSCode_of_check (basisX := []) (masksX := []) (basisZ := []) (masksZ := []) (by decide +kernel)

end Quantum.Claims.QC_002
