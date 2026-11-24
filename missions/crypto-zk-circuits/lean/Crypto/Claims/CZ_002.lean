import Crypto.Core
import Crypto.Statements.CZ_002

namespace Crypto.Claims.CZ_002

open Crypto Crypto.B2Op

/-- 14-gate, 4-AND well-formed B2 circuit for the ISO/IEC 29192-2 PRESENT 4-bit S-box.
    Input wires: w0=x0 (LSB), w1=x1, w2=x2, w3=x3 (MSB). -/
def presentCircuit : MultiCircuit 4 4 where
  gates := [
    ⟨opXor,    1, 2⟩,   -- w4:  u3 = x1 ^ x2
    ⟨opAnd,    1, 2⟩,   -- w5:  q0 = x1 & x2            [AND #1]
    ⟨opAnd,    4, 3⟩,   -- w6:  q1 = u3 & x3            [AND #2]
    ⟨opXor,    2, 3⟩,   -- w7:  x2 ^ x3
    ⟨opXor,    0, 5⟩,   -- w8:  x0 ^ q0
    ⟨opXor,    7, 8⟩,   -- w9:  y0 = x0 ^ x2 ^ x3 ^ q0
    ⟨opXnor,   8, 6⟩,   -- w10: u1 = ~(x0 ^ q0 ^ q1)
    ⟨opAnd,    10, 0⟩,  -- w11: q2 = u1 & x0            [AND #3]
    ⟨opXor,    9, 4⟩,   -- w12: y0 ^ u3
    ⟨opXnor,   12, 11⟩, -- w13: y3 = ~(y0 ^ u3 ^ q2)
    ⟨opXor,    13, 10⟩, -- w14: y1 = y3 ^ u1
    ⟨opAndNot, 10, 12⟩, -- w15: q3 = u1 & ~(y0 ^ u3)    [AND #4]
    ⟨opXor,    0, 4⟩,   -- w16: x0 ^ u3
    ⟨opXor,    15, 16⟩  -- w17: y2 = q3 ^ x0 ^ u3
  ]
  outputs := [9, 14, 17, 13]

theorem present_four_and : Crypto.Statements.CZ_002.Claim := by
  refine ⟨presentCircuit, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_002
