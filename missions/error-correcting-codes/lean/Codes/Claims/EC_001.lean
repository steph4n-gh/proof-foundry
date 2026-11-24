import Codes.Statements.EC_001

namespace Codes.Claims.EC_001

private def hammingCode : List (BitVec 7) :=
  [0x00#7, 0x0B#7, 0x15#7, 0x1E#7,
   0x26#7, 0x2D#7, 0x33#7, 0x38#7,
   0x47#7, 0x4C#7, 0x52#7, 0x59#7,
   0x61#7, 0x6A#7, 0x74#7, 0x7F#7]

theorem hamming_7_4_3 : Codes.Statements.EC_001.Claim :=
  ⟨hammingCode, by decide, Codes.isBinaryCode_of_checkDist (by decide) (by decide +kernel)⟩

end Codes.Claims.EC_001
