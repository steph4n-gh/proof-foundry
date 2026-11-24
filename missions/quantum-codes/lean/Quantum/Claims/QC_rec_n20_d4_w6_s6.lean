import Quantum.Statements.QC_rec_n20_d4_w6

namespace Quantum.Claims.QC_rec_n20_d4_w6_s6

open Quantum

-- Non-degenerate [[20, 6, 4]] CSS code with check weights all <= 6 (hx all weight 6, hz all weight 6).
-- Constructed from an odd-in-A [20, 13, 4] weight-6 check matrix H_X and a dual odd-in-A [20, 13, 4] weight-6 check matrix H_Z.
private def hx : List (BitVec 20) :=
  [327793#20, 656258#20, 793604#20, 843784#20, 205968#20, 608544#20, 692800#20]

private def hz : List (BitVec 20) :=
  [540884#20, 346160#20, 37913#20, 156418#20, 401925#20, 529000#20, 539650#20]

private def lx : List (BitVec 20) :=
  [77#20, 184#20, 1343#20, 2327#20, 4362#20, 65557#20]

private def lz : List (BitVec 20) :=
  [1334#20, 6387#20, 6912#20, 3030#20, 5491#20, 5936#20]

theorem record : Quantum.Statements.QC_rec_n20_d4_w6.Record 6 := by
  refine ⟨6, hx, hz, lx, lz, Nat.le_refl 6, ?_⟩
  exact isCSSCode_of_check (basisX := []) (masksX := []) (basisZ := []) (masksZ := []) (by decide +kernel)

end Quantum.Claims.QC_rec_n20_d4_w6_s6
