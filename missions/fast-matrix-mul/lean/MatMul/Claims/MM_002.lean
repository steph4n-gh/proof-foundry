import MatMul.Statements.MM_002

namespace MatMul.Claims.MM_002

private def vec4 (b0 b1 b2 b3 : Bool) : Fin 4 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3

private def strassen : MatMul.SchemeF2 2 2 2 :=
  [ { left := vec4 true  false false true,  right := vec4 true  false false true,  output := vec4 true  false false true  }
  , { left := vec4 false false true  true,  right := vec4 true  false false false, output := vec4 false false true  true  }
  , { left := vec4 true  false false false, right := vec4 false true  false true,  output := vec4 false true  false true  }
  , { left := vec4 false false false true,  right := vec4 true  false true  false, output := vec4 true  false true  false }
  , { left := vec4 true  true  false false, right := vec4 false false false true,  output := vec4 true  true  false false }
  , { left := vec4 true  false true  false, right := vec4 true  true  false false, output := vec4 false false false true  }
  , { left := vec4 false true  false true,  right := vec4 false false true  true,  output := vec4 true  false false false }
  ]

theorem strassen_f2 : MatMul.Statements.MM_002.Claim :=
  ⟨strassen, by decide, by unfold IsMatMulSchemeF2; decide⟩

end MatMul.Claims.MM_002
