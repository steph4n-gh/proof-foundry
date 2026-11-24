import Crypto.Core
import Crypto.Statements.CZ_rec_ascon_gates

namespace Crypto.Claims.CZ_rec_ascon_gates_s15

open Crypto Crypto.B2Op

/-- Verified 15-gate, 5-AND, depth-1 full-B2 circuit for the NIST SP 800-232 Ascon 5-bit S-box
    (matches literature_best = 15; beats 16-gate incumbent by 1 gate).
    Uses an alternative decomposable quadratic basis `(x0∧¬x1, x1∧¬(x2⊕x3), (x0⊕x1)∨x4, x2∧¬x3, x3∧¬(x0⊕x4))`
    so the post-linear layer collapses to 7 XOR/XNOR gates with output complement folded into `opXnor`. -/
def asconCircuit15 : MultiCircuit 5 5 where
  gates := [
    ⟨opXor,    0,  1⟩, -- w5  = x0 ⊕ x1
    ⟨opXor,    2,  3⟩, -- w6  = x2 ⊕ x3
    ⟨opXor,    0,  4⟩, -- w7  = x0 ⊕ x4
    ⟨opAndNot, 0,  1⟩, -- w8  = t0 = x0 ∧ ¬x1
    ⟨opAndNot, 1,  6⟩, -- w9  = t1 = x1 ∧ ¬(x2 ⊕ x3)
    ⟨opOr,     5,  4⟩, -- w10 = t2 = (x0 ⊕ x1) ∨ x4
    ⟨opAndNot, 2,  3⟩, -- w11 = t3 = x2 ∧ ¬x3
    ⟨opAndNot, 3,  7⟩, -- w12 = t4 = x3 ∧ ¬(x0 ⊕ x4)
    ⟨opXor,    12, 5⟩, -- w13 = t4 ⊕ w5 = y0
    ⟨opXor,    10, 6⟩, -- w14 = t2 ⊕ w6 = y1
    ⟨opXnor,   8,  6⟩, -- w15 = ¬(t0 ⊕ w6) = y2
    ⟨opXor,    11, 7⟩, -- w16 = t3 ⊕ w7
    ⟨opXor,    13, 16⟩,-- w17 = y0 ⊕ w16 = y4
    ⟨opXor,    9,  16⟩,-- w18 = t1 ⊕ w16
    ⟨opXor,    3,  18⟩ -- w19 = x3 ⊕ w18 = y3
  ]
  outputs := [13, 14, 15, 19, 17]

theorem record : Crypto.Statements.CZ_rec_ascon_gates.Record 15 := by
  refine ⟨asconCircuit15, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_rec_ascon_gates_s15
