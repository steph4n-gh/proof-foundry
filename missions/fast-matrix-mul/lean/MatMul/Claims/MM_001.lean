import MatMul.Statements.MM_001

namespace MatMul.Claims.MM_001

private def term (left right output : Vector Int 4) : Term Int 2 2 2 :=
  ⟨left.get, right.get, output.get⟩

-- Each row gives one product's left, right, and output weights in row-major order.
private def strassen : SchemeInt 2 2 2 := [
  term #v[1, 0, 0, 1]  #v[1, 0, 0, 1]  #v[1, 0, 0, 1],
  term #v[0, 0, 1, 1]  #v[1, 0, 0, 0]  #v[0, 0, 1, -1],
  term #v[1, 0, 0, 0]  #v[0, 1, 0, -1] #v[0, 1, 0, 1],
  term #v[0, 0, 0, 1]  #v[-1, 0, 1, 0] #v[1, 0, 1, 0],
  term #v[1, 1, 0, 0]  #v[0, 0, 0, 1]  #v[-1, 1, 0, 0],
  term #v[-1, 0, 1, 0] #v[1, 1, 0, 0]  #v[0, 0, 0, 1],
  term #v[0, 1, 0, -1] #v[0, 0, 1, 1]  #v[1, 0, 0, 0]]

theorem strassen_int : MatMul.Statements.MM_001.Claim := by
  refine ⟨strassen, by decide, ?_⟩
  unfold IsMatMulSchemeInt
  decide +kernel

end MatMul.Claims.MM_001
