import Codes.Core

namespace Codes.Statements.EC_001

/-- Frozen Statement: the Hamming [7,4,3] code — there is a binary code of length 7 with
    16 codewords and minimum distance 3 (so `A(7,3) ≥ 16`; with EC-002 this is exact). -/
def Claim : Prop :=
  ∃ C : List (BitVec 7), C.length = 16 ∧ Codes.IsBinaryCode 7 3 C

end Codes.Statements.EC_001
