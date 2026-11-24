import Quantum.Core
import Quantum.Statements.QC_rec_n16_d4_w6

namespace Quantum.Claims.QC_rec_n16_d4_w6_s4

open Quantum

/-- Z_8 generalized bicycle `[[16, 4, 4]]` CSS code (`a = 1 + x^2`, `b = 1 + x + x^3 + x^4`):
    all 6 X-checks and 6 Z-checks have uniform weight 6 (≤ 6), matching `literature_best = 4`. -/
def hx16 : List (BitVec 16) :=
  [0x1b05#16, 0x360a#16, 0x6c14#16, 0xd828#16, 0xb150#16, 0x63a0#16]

def hz16 : List (BitVec 16) :=
  [0x41b1#16, 0x8263#16, 0x5c6#16, 0xa8d#16, 0x141b#16, 0x2836#16]

def lx16 : List (BitVec 16) :=
  [0x55#16, 0xaa#16, 0x11c#16, 0x238#16]

def lz16 : List (BitVec 16) :=
  [0x2d6#16, 0x16b#16, 0xaa#16, 0x55#16]

def basisX16 : List (Nat × BitVec 16) :=
  [(0, 0xc641#16), (1, 0x8d82#16), (2, 0xdd44#16), (3, 0xbb88#16), (4, 0xb150#16), (5, 0x63a0#16)]

def masksX16 : List (List Bool) :=
  [
    [true, false, true, false, true, false],
    [false, true, false, true, false, true],
    [false, false, true, false, true, false],
    [false, false, false, true, false, true],
    [false, false, false, false, true, false],
    [false, false, false, false, false, true] ]

def basisZ16 : List (Nat × BitVec 16) :=
  [(0, 0x6c41#16), (1, 0xd882#16), (2, 0xdd44#16), (3, 0xbb88#16), (4, 0x1b50#16), (5, 0x36a0#16)]

def masksZ16 : List (List Bool) :=
  [
    [true, false, true, false, false, true],
    [true, true, true, true, true, false],
    [true, true, false, true, true, false],
    [false, true, true, false, true, true],
    [false, false, true, true, true, false],
    [false, false, false, true, true, true] ]

theorem record : Quantum.Statements.QC_rec_n16_d4_w6.Record 4 := by
  refine ⟨4, hx16, hz16, lx16, lz16, Nat.le_refl 4, ?_⟩
  exact isCSSCode_of_check (basisX := basisX16) (masksX := masksX16) (basisZ := basisZ16) (masksZ := masksZ16) (by decide +kernel)

end Quantum.Claims.QC_rec_n16_d4_w6_s4
