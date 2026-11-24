import MatMul.Core

namespace MatMul.Statements.MM_rec_3x3x3_hw

/-- All linear-form coefficients lie in {-1, 0, 1} (no integer multiplications in pre/post-additions;
    keeps numerical stability tight for FP16/BF16/FP32 block-recursive GEMM). -/
def IsUnitCoeff (s : SchemeInt 3 3 3) : Prop :=
  ∀ t ∈ s,
    (∀ i, t.left i = -1 ∨ t.left i = 0 ∨ t.left i = 1) ∧
    (∀ j, t.right j = -1 ∨ t.right j = 0 ∨ t.right j = 1) ∧
    (∀ k, t.output k = -1 ∨ t.output k = 0 ∨ t.output k = 1)

def nnz {n : Nat} (v : Fin n → Int) : Nat :=
  (List.finRange n).foldl (fun acc i => if v i == 0 then acc else acc + 1) 0

/-- Direct (pre-CSE) addition count of a 3×3×3 scheme: input form additions + output accumulation additions. -/
def schemeAdditions (s : SchemeInt 3 3 3) : Nat :=
  s.foldl (fun acc t => acc + (nnz t.left - 1) + (nnz t.right - 1)) 0 +
  (List.finRange 9).foldl (fun acc k => acc + ((s.filter (fun t => t.output k != 0)).length - 1)) 0

/--
  King of the Hill Frozen Record Statement (Hardware-Friendly 3×3×3 Scheme):
  Minimize direct addition count among rank ≤ 23 schemes with unit coefficients {-1, 0, 1}.
  Directly determines the crossover size where fast block-recursive GEMM beats schoolbook on CPUs/GPUs!
-/
def Record (score : Nat) : Prop :=
  ∃ S : SchemeInt 3 3 3,
    S.length ≤ 23 ∧ IsUnitCoeff S ∧ schemeAdditions S ≤ score ∧ IsMatMulSchemeInt S

theorem Record_mono {a b : Nat} (h : a ≤ b) : Record a → Record b :=
  fun ⟨S, hlen, hunit, hadd, valid⟩ => ⟨S, hlen, hunit, Nat.le_trans hadd h, valid⟩

end MatMul.Statements.MM_rec_3x3x3_hw
