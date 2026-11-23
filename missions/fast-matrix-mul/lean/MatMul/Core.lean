namespace MatMul

/-- One multiplication of a linear form in A by a linear form in B.
    The third factor distributes the product to entries of C. All indices
    are row-major: (row, column) is stored at row * numberOfColumns + column. -/
structure Term (α : Type) (m n p : Nat) where
  left   : Fin (m * n) → α
  right  : Fin (n * p) → α
  output : Fin (m * p) → α

abbrev SchemeInt (m n p : Nat) := List (Term Int m n p)
abbrev SchemeF2 (m n p : Nat) := List (Term Bool m n p)

/-- In A[i,j] B[k,l], j must equal k and the output must be C[i,l]. -/
def contributes {m n p : Nat} (a : Fin (m * n)) (b : Fin (n * p)) (c : Fin (m * p)) : Bool :=
  a.val % n == b.val / p && c.val == a.val / n * p + b.val % p

/-- The integer coefficient of A[a] B[b] in output c, summed over rank-one terms. -/
def coeffInt {m n p} (s : SchemeInt m n p) (a : Fin (m * n)) (b : Fin (n * p))
    (c : Fin (m * p)) : Int :=
  -- For each input pair, reuse its nonzero weights across all output entries.
  let active := s.filterMap fun t =>
    let k := t.left a * t.right b
    if k == 0 then none else some (k, t.output)
  active.foldl (fun acc (k, output) => acc + k * output c) 0

/-- The same coefficient in GF(2), with AND for multiplication and XOR for addition. -/
def coeffF2 {m n p} (s : SchemeF2 m n p) (a : Fin (m * n)) (b : Fin (n * p))
    (c : Fin (m * p)) : Bool :=
  let active := s.filter fun t => t.left a && t.right b
  active.foldl (fun acc t => acc ^^ t.output c) false

def IsMatMulSchemeInt {m n p} (s : SchemeInt m n p) : Prop :=
  ∀ a b c, coeffInt s a b c = (if contributes a b c then 1 else 0)

def IsMatMulSchemeF2 {m n p} (s : SchemeF2 m n p) : Prop :=
  ∀ a b c, coeffF2 s a b c = contributes a b c

end MatMul
