import Quantum.Core
import Quantum.Statements.QC_rec_n18_d4_w6

namespace Quantum.Claims.QC_rec_n18_d4_w6_s4

open Quantum

/-- Generalized bicycle `[[18, 4, 4]]` CSS code over `Z_9` with `A(x) = 1 + x + x^2`, `B(x) = 1 + x^2 + x^4`
    (7 independent weight-6 X-checks and 7 independent weight-6 Z-checks; matches `literature_best = 4`). -/
def hx18 : List (BitVec 18) :=
  [0x02a07#18, 0x0540e#18, 0x0a81c#18, 0x15038#18, 0x2a070#18, 0x142e0#18, 0x285c0#18]

def hz18 : List (BitVec 18) :=
  [0x302a1#18, 0x20742#18, 0x00e85#18, 0x01d0a#18, 0x03815#18, 0x0702a#18, 0x0e054#18]

def lx18 : List (BitVec 18) :=
  [0x000db#18, 0x0016d#18, 0x00251#18, 0x00479#18]

def lz18 : List (BitVec 18) :=
  [0x0016d#18, 0x005d8#18, 0x00503#18, 0x00381#18]

def basisX18 : List (Nat × BitVec 18) :=
  [(13, 0x025b0#18), (14, 0x046d6#18), (15, 0x0821b#18), (16, 0x10436#18), (17, 0x207db#18), (12, 0x012d8#18), (11, 0x00fb7#18)]

def masksX18 : List (List Bool) :=
  [
    [false, false, false, false, true, false, true],
    [false, true, false, true, false, true, false],
    [true, false, true, false, false, false, false],
    [false, true, false, true, false, false, false],
    [true, false, true, false, false, false, true],
    [false, false, false, true, false, true, false],
    [true, false, false, false, true, false, true] ]

def basisZ18 : List (Nat × BitVec 18) :=
  [(17, 0x20742#18), (16, 0x105e3#18), (11, 0x00e85#18), (12, 0x0138f#18), (13, 0x0251f#18), (14, 0x046ba#18), (15, 0x083f1#18)]

def masksZ18 : List (List Bool) :=
  [
    [false, true, false, false, false, false, false],
    [true, true, false, false, false, false, false],
    [false, false, true, false, false, false, false],
    [false, false, true, true, false, false, false],
    [false, false, false, true, true, false, false],
    [false, false, true, false, true, true, false],
    [false, false, true, true, false, true, true] ]

theorem record : Quantum.Statements.QC_rec_n18_d4_w6.Record 4 := by
  refine ⟨4, hx18, hz18, lx18, lz18, Nat.le_refl 4, ?_⟩
  exact isCSSCode_of_check (basisX := basisX18) (masksX := masksX18) (basisZ := basisZ18) (masksZ := masksZ18) (by decide +kernel)

end Quantum.Claims.QC_rec_n18_d4_w6_s4
