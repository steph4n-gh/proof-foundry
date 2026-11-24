import Quantum.Core
import Quantum.Statements.QC_rec_n15_d3_w4

namespace Quantum.Claims.QC_rec_n15_d3_w4_s3

open Quantum

/-- Non-degenerate `[[15, 3, 3]]` CSS code with exact check weight 4:
    `hx` is the augmented vertex-edge incidence matrix of `K_{3,3}` (6 weight-4 checks),
    and `hz` consists of 6 orthogonal weight-4 checks in `hx^⊥` with all 15 columns distinct. -/
def hx15 : List (BitVec 15) :=
  [0x01c1#15, 0x0e02#15, 0x7004#15, 0x1248#15, 0x2490#15, 0x4920#15]

def hz15 : List (BitVec 15) :=
  [0x00d8#15, 0x0243#15, 0x0c30#15, 0x2406#15, 0x4105#15, 0x5028#15]

def lx15 : List (BitVec 15) :=
  [0x0007#15, 0x02c0#15, 0x0452#15]

def lz15 : List (BitVec 15) :=
  [0x0121#15, 0x045b#15, 0x0533#15]

theorem record : Quantum.Statements.QC_rec_n15_d3_w4.Record 3 := by
  refine ⟨3, hx15, hz15, lx15, lz15, Nat.le_refl 3, ?_⟩
  exact isCSSCode_of_check (basisX := []) (masksX := []) (basisZ := []) (masksZ := []) (by decide +kernel)

end Quantum.Claims.QC_rec_n15_d3_w4_s3
