import Crypto.Core
import Crypto.Statements.CZ_rec_skinny4_gates

namespace Crypto.Claims.CZ_rec_skinny4_gates_s8

open Crypto Crypto.B2Op

/-- Optimal 8-gate (4 NOR + 4 XOR) well-formed B2 circuit for the SKINNY 4-bit S-box.
    Input wires: w0=x0 (LSB), w1=x1, w2=x2, w3=x3 (MSB). -/
def skinny4Circuit8 : MultiCircuit 4 4 where
  gates := [
    ⟨opNor, 3, 2⟩,   -- w4:  ~(x3 | x2)
    ⟨opXor, 0, 4⟩,   -- w5:  y3 = x0 ^ ~(x3 | x2)
    ⟨opNor, 2, 1⟩,   -- w6:  ~(x2 | x1)
    ⟨opXor, 3, 6⟩,   -- w7:  y2 = x3 ^ ~(x2 | x1)
    ⟨opNor, 1, 5⟩,   -- w8:  ~(x1 | y3)
    ⟨opXor, 2, 8⟩,   -- w9:  y1 = x2 ^ ~(x1 | y3)
    ⟨opNor, 5, 7⟩,   -- w10: ~(y3 | y2)
    ⟨opXor, 1, 10⟩   -- w11: y0 = x1 ^ ~(y3 | y2)
  ]
  outputs := [11, 9, 7, 5]

theorem record : Crypto.Statements.CZ_rec_skinny4_gates.Record 8 := by
  refine ⟨skinny4Circuit8, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_rec_skinny4_gates_s8
