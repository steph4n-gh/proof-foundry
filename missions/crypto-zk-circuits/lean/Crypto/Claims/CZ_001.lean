import Crypto.Core
import Crypto.Statements.CZ_001

namespace Crypto.Claims.CZ_001

open Crypto Crypto.B2Op

/-- 16-gate, 5-AND, depth-1 well-formed B2 circuit for the NIST SP 800-232 Ascon 5-bit S-box.
    Input wires: w0=x4 (LSB), w1=x3, w2=x2, w3=x1, w4=x0 (MSB). -/
def asconCircuit : MultiCircuit 5 5 where
  gates := [
    ⟨opXor,    4, 0⟩,   -- w5:  a0 = x0 ^ x4
    ⟨opXor,    0, 1⟩,   -- w6:  a4 = x4 ^ x3
    ⟨opXor,    2, 3⟩,   -- w7:  a2 = x2 ^ x1
    ⟨opNotAnd, 5, 3⟩,   -- w8:  t0 = (~a0) & x1   [AND #1]
    ⟨opNotAnd, 3, 7⟩,   -- w9:  t1 = (~x1) & a2   [AND #2]
    ⟨opNotAnd, 7, 1⟩,   -- w10: t2 = (~a2) & x3   [AND #3]
    ⟨opNotAnd, 1, 6⟩,   -- w11: t3 = (~x3) & a4   [AND #4]
    ⟨opNotAnd, 6, 5⟩,   -- w12: t4 = (~a4) & a0   [AND #5]
    ⟨opXor,    5, 9⟩,   -- w13: b0 = a0 ^ t1
    ⟨opXor,    3, 10⟩,  -- w14: b1 = x1 ^ t2
    ⟨opXnor,   7, 11⟩,  -- w15: b2 = ~(a2 ^ t3)
    ⟨opXor,    1, 12⟩,  -- w16: b3 = x3 ^ t4
    ⟨opXor,    6, 8⟩,   -- w17: b4 = a4 ^ t0
    ⟨opXor,    14, 13⟩, -- w18: c1 = b1 ^ b0
    ⟨opXor,    13, 17⟩, -- w19: c0 = b0 ^ b4
    ⟨opXnor,   16, 15⟩  -- w20: c3 = b3 ^ (~b2)
  ]
  outputs := [17, 20, 15, 18, 19]

theorem ascon_five_and_depth_one : Crypto.Statements.CZ_001.Claim := by
  refine ⟨asconCircuit, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_001
