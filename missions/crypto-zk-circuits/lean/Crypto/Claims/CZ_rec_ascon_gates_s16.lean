import Crypto.Core
import Crypto.Statements.CZ_rec_ascon_gates

namespace Crypto.Claims.CZ_rec_ascon_gates_s16

open Crypto Crypto.B2Op

/-- Verified 16-gate, 5-AND, depth-1 B2 circuit for the NIST SP 800-232 Ascon 5-bit S-box. -/
def asconCircuit16 : MultiCircuit 5 5 where
  gates := [
    ⟨opXor,    4, 0⟩,
    ⟨opXor,    0, 1⟩,
    ⟨opXor,    2, 3⟩,
    ⟨opNotAnd, 5, 3⟩,
    ⟨opNotAnd, 3, 7⟩,
    ⟨opNotAnd, 7, 1⟩,
    ⟨opNotAnd, 1, 6⟩,
    ⟨opNotAnd, 6, 5⟩,
    ⟨opXor,    5, 9⟩,
    ⟨opXor,    3, 10⟩,
    ⟨opXnor,   7, 11⟩,
    ⟨opXor,    1, 12⟩,
    ⟨opXor,    6, 8⟩,
    ⟨opXor,    14, 13⟩,
    ⟨opXor,    13, 17⟩,
    ⟨opXnor,   16, 15⟩
  ]
  outputs := [17, 20, 15, 18, 19]

theorem record : Crypto.Statements.CZ_rec_ascon_gates.Record 16 := by
  refine ⟨asconCircuit16, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_rec_ascon_gates_s16
