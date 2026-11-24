import Quantum.Core
import Quantum.Statements.QC_rec_n16_d4_w6

namespace Quantum.Claims.QC_rec_n16_d4_w6_s2

open Quantum

/-- Rotated 4×4 toric CSS code `[[16, 2, 4]]`: all 7 X-checks and 7 Z-checks have weight 4 (≤ 6). -/
def hx16 : List (BitVec 16) :=
  [0x33#16, 0xcc#16, 0x660#16, 0x990#16, 0x3300#16, 0xcc00#16, 0x6006#16]

def hz16 : List (BitVec 16) :=
  [0x66#16, 0x99#16, 0x330#16, 0xcc0#16, 0x6600#16, 0x9900#16, 0x3003#16]

def lx16 : List (BitVec 16) := [0xf#16, 0x1111#16]
def lz16 : List (BitVec 16) := [0x1111#16, 0xf#16]

def basisX16 : List (Nat × BitVec 16) :=
  [(0, 0x9009#16), (1, 0x60ca#16), (2, 0xcc#16), (4, 0x3a90#16), (5, 0xca60#16), (8, 0x3300#16), (10, 0xcc00#16)]

def masksX16 : List (List Bool) :=
  [ [true, true, true, true, true, true, true],
    [false, true, false, false, false, false, true],
    [false, true, false, false, false, false, false],
    [false, false, false, true, true, false, false],
    [false, false, true, false, false, true, false],
    [false, false, false, false, true, false, false],
    [false, false, false, false, false, true, false] ]

def basisZ16 : List (Nat × BitVec 16) :=
  [(0, 0xfca9#16), (1, 0xccaa#16), (2, 0xc00c#16), (4, 0xfc30#16), (6, 0xcc0#16), (8, 0x9900#16), (9, 0x6600#16)]

def masksZ16 : List (List Bool) :=
  [ [false, true, true, false, true, true, false],
    [false, true, true, false, true, true, true],
    [true, true, true, true, true, true, true],
    [false, false, true, false, true, true, false],
    [false, false, false, true, false, false, false],
    [false, false, false, false, false, true, false],
    [false, false, false, false, true, false, false] ]

theorem record : Quantum.Statements.QC_rec_n16_d4_w6.Record 2 := by
  refine ⟨2, hx16, hz16, lx16, lz16, Nat.le_refl 2, ?_⟩
  exact isCSSCode_of_check (basisX := basisX16) (masksX := masksX16) (basisZ := basisZ16) (masksZ := masksZ16) (by decide +kernel)

end Quantum.Claims.QC_rec_n16_d4_w6_s2
