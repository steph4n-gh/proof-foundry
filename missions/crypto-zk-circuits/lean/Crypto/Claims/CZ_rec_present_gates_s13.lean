import Crypto.Core
import Crypto.Statements.CZ_rec_present_gates

namespace Crypto.Claims.CZ_rec_present_gates_s13

open Crypto Crypto.B2Op

/-- 13-gate, 4-NL well-formed B2 circuit for the ISO/IEC 29192-2 PRESENT 4-bit S-box,
    improving the 14-gate literature record by absorbing linear terms into `opNotAnd` and `opOr`
    and resynthesizing the remaining linear layer in 9 gates.
    Input wires: w0=x0 (LSB), w1=x1, w2=x2, w3=x3 (MSB). -/
def presentCircuit13 : MultiCircuit 4 4 where
  gates := [
    ⟨opNotAnd, 1, 2⟩,   -- w4:  q0' = (~x1) & x2          [NL #1]
    ⟨opXor,    1, 2⟩,   -- w5:  u3  = x1 ^ x2
    ⟨opNotAnd, 5, 3⟩,   -- w6:  q1' = (~u3) & x3          [NL #2]
    ⟨opXor,    1, 6⟩,   -- w7:  x1 ^ q1'
    ⟨opXor,    3, 4⟩,   -- w8:  x3 ^ q0'
    ⟨opXor,    0, 8⟩,   -- w9:  y0  = x0 ^ x3 ^ q0'
    ⟨opXor,    5, 9⟩,   -- w10: w12 = u3 ^ y0
    ⟨opXnor,   7, 10⟩,  -- w11: u1  = ~(w7 ^ w10)
    ⟨opAnd,    11, 0⟩,  -- w12: q2  = u1 & x0             [NL #3]
    ⟨opXor,    7, 12⟩,  -- w13: y1  = w7 ^ q2
    ⟨opXnor,   10, 12⟩, -- w14: y3  = ~(w10 ^ q2)
    ⟨opOr,     11, 10⟩, -- w15: q3' = u1 | w10            [NL #4]
    ⟨opXor,    8, 15⟩   -- w16: y2  = w8 ^ q3'
  ]
  outputs := [9, 13, 16, 14]

theorem record : Crypto.Statements.CZ_rec_present_gates.Record 13 := by
  refine ⟨presentCircuit13, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_rec_present_gates_s13
