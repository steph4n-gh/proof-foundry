import Crypto.Core
import Crypto.Statements.CZ_rec_aes_total

namespace Crypto.Claims.CZ_rec_aes_total_s107

open Crypto Crypto.B2Op

/-- 107-gate, AND-depth-4 (36 non-linear B2 gates) well-formed B2 circuit for the FIPS-197 AES 8-bit S-box.
    Obtained by GF(2^8) Frobenius + multiplicative scaling (x -> 0x1e * x^(2^2)) of the polynomial-Y
    tower-field inverter core, combined with exact RNBP SLP synthesis of the 8->18 top linear layer (18 XORs)
    and Transposition-Principle exact RNBP SLP synthesis of the 18->8 bottom linear layer (25 XOR/XNORs,
    with 0x63 affine constant folded into bottom XNOR gates at zero extra cost). -/
def aesCircuit107 : MultiCircuit 8 8 where
  gates := [
    ⟨opXor, 4, 5⟩,
    ⟨opXor, 1, 3⟩,
    ⟨opXor, 6, 9⟩,
    ⟨opXor, 2, 10⟩,
    ⟨opXor, 0, 11⟩,
    ⟨opXor, 4, 10⟩,
    ⟨opXor, 7, 13⟩,
    ⟨opXor, 5, 14⟩,
    ⟨opXor, 6, 14⟩,
    ⟨opXor, 1, 12⟩,
    ⟨opXor, 5, 10⟩,
    ⟨opXor, 11, 15⟩,
    ⟨opXor, 7, 17⟩,
    ⟨opXor, 16, 19⟩,
    ⟨opXor, 0, 16⟩,
    ⟨opXor, 17, 18⟩,
    ⟨opXor, 8, 20⟩,
    ⟨opXor, 12, 21⟩,
    ⟨opOr, 12, 23⟩,
    ⟨opOr, 25, 24⟩,
    ⟨opOr, 21, 14⟩,
    ⟨opOr, 0, 18⟩,
    ⟨opOr, 22, 8⟩,
    ⟨opNotAnd, 16, 13⟩,
    ⟨opOr, 11, 17⟩,
    ⟨opNotAnd, 15, 20⟩,
    ⟨opOr, 19, 7⟩,
    ⟨opXor, 27, 11⟩,
    ⟨opXor, 29, 25⟩,
    ⟨opXor, 26, 33⟩,
    ⟨opXor, 30, 34⟩,
    ⟨opXor, 28, 32⟩,
    ⟨opXor, 37, 39⟩,
    ⟨opXor, 31, 32⟩,
    ⟨opXor, 38, 41⟩,
    ⟨opXor, 33, 36⟩,
    ⟨opXor, 41, 43⟩,
    ⟨opXor, 38, 43⟩,
    ⟨opXor, 34, 35⟩,
    ⟨opXor, 39, 46⟩,
    ⟨opXor, 37, 46⟩,
    ⟨opXor, 45, 48⟩,
    ⟨opAnd, 40, 44⟩,
    ⟨opOr, 47, 42⟩,
    ⟨opAnd, 48, 45⟩,
    ⟨opXor, 52, 51⟩,
    ⟨opXor, 52, 50⟩,
    ⟨opXor, 54, 49⟩,
    ⟨opXor, 55, 53⟩,
    ⟨opAnd, 44, 53⟩,
    ⟨opAnd, 42, 55⟩,
    ⟨opAnd, 45, 56⟩,
    ⟨opAnd, 40, 53⟩,
    ⟨opAnd, 47, 55⟩,
    ⟨opAnd, 48, 56⟩,
    ⟨opXor, 59, 57⟩,
    ⟨opXor, 59, 58⟩,
    ⟨opXor, 57, 58⟩,
    ⟨opXor, 62, 60⟩,
    ⟨opXor, 62, 61⟩,
    ⟨opXor, 60, 61⟩,
    ⟨opXor, 63, 66⟩,
    ⟨opXor, 64, 67⟩,
    ⟨opXor, 65, 68⟩,
    ⟨opAnd, 12, 63⟩,
    ⟨opAnd, 25, 64⟩,
    ⟨opAnd, 21, 65⟩,
    ⟨opAnd, 0, 66⟩,
    ⟨opAnd, 22, 67⟩,
    ⟨opAnd, 16, 68⟩,
    ⟨opAnd, 11, 69⟩,
    ⟨opAnd, 15, 70⟩,
    ⟨opAnd, 19, 71⟩,
    ⟨opAnd, 23, 63⟩,
    ⟨opAnd, 24, 64⟩,
    ⟨opAnd, 14, 65⟩,
    ⟨opAnd, 18, 66⟩,
    ⟨opAnd, 8, 67⟩,
    ⟨opAnd, 13, 68⟩,
    ⟨opAnd, 17, 69⟩,
    ⟨opAnd, 20, 70⟩,
    ⟨opAnd, 7, 71⟩,
    ⟨opXnor, 79, 80⟩,
    ⟨opXor, 75, 90⟩,
    ⟨opXor, 91, 76⟩,
    ⟨opXnor, 87, 89⟩,
    ⟨opXor, 83, 93⟩,
    ⟨opXnor, 81, 94⟩,
    ⟨opXor, 86, 92⟩,
    ⟨opXor, 96, 93⟩,
    ⟨opXor, 97, 85⟩,
    ⟨opXor, 77, 76⟩,
    ⟨opXor, 82, 94⟩,
    ⟨opXor, 74, 98⟩,
    ⟨opXor, 101, 99⟩,
    ⟨opXor, 73, 102⟩,
    ⟨opXnor, 92, 100⟩,
    ⟨opXor, 84, 95⟩,
    ⟨opXor, 105, 85⟩,
    ⟨opXor, 78, 80⟩,
    ⟨opXor, 107, 99⟩,
    ⟨opXor, 108, 103⟩,
    ⟨opXor, 88, 92⟩,
    ⟨opXor, 110, 89⟩,
    ⟨opXor, 111, 95⟩,
    ⟨opXor, 72, 90⟩,
    ⟨opXor, 113, 102⟩
  ]
  outputs := [104, 100, 106, 109, 98, 112, 114, 103]

set_option maxRecDepth 8192 in
theorem record : Crypto.Statements.CZ_rec_aes_total.Record 107 := by
  refine ⟨aesCircuit107, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact computes_of_checkSBox (by decide +kernel)

end Crypto.Claims.CZ_rec_aes_total_s107
