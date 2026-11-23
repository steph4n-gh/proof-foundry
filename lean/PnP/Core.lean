/-
  PnP.Core — Pure Lean 4 complexity, circuit, SAT, and proof-complexity foundations.
  Zero external dependencies: compiles in ~1s for fast live checker verification.
-/
namespace PnP

/-! ## 1. Boolean Functions & Monotonicity -/

abbrev BoolVec (n : Nat) := Fin n → Bool
abbrev BoolFn (n : Nat) := BoolVec n → Bool

def flipBit {n : Nat} (x : BoolVec n) (i : Fin n) : BoolVec n :=
  fun j => if j = i then !x i else x j

def BitLe (x y : BoolVec n) : Prop :=
  ∀ i : Fin n, x i = true → y i = true

def Monotone {n : Nat} (f : BoolFn n) : Prop :=
  ∀ x y : BoolVec n, BitLe x y → f x = true → f y = true

def DependsOn {n : Nat} (f : BoolFn n) (i : Fin n) : Prop :=
  ∃ x : BoolVec n, f x ≠ f (flipBit x i)

def parityFn : (n : Nat) → BoolFn n
  | 0, _ => false
  | n + 1, x => xor (x ⟨0, Nat.zero_lt_succ n⟩) (parityFn n (fun i => x i.succ))

def xor2 : BoolFn 2 :=
  fun x => xor (x ⟨0, by decide⟩) (x ⟨1, by decide⟩)

def and2 : BoolFn 2 :=
  fun x => x ⟨0, by decide⟩ && x ⟨1, by decide⟩

def or2 : BoolFn 2 :=
  fun x => x ⟨0, by decide⟩ || x ⟨1, by decide⟩

def maj3 : BoolFn 3 :=
  fun x =>
    let a := x ⟨0, by decide⟩
    let b := x ⟨1, by decide⟩
    let c := x ⟨2, by decide⟩
    (a && b) || (b && c) || (a && c)

/-! ## 2. Boolean Circuits (Formula Basis & Shared-Wire DAG Basis) -/

inductive Circuit (n : Nat) where
  | input (i : Fin n)
  | const (b : Bool)
  | not (c : Circuit n)
  | and (a b : Circuit n)
  | or (a b : Circuit n)
  | xor (a b : Circuit n)
  deriving Repr, DecidableEq

namespace Circuit

def eval {n : Nat} : Circuit n → BoolVec n → Bool
  | .input i, x => x i
  | .const b, _ => b
  | .not c, x => !(c.eval x)
  | .and a b, x => a.eval x && b.eval x
  | .or a b, x => a.eval x || b.eval x
  | .xor a b, x => Bool.xor (a.eval x) (b.eval x)

def gateCount {n : Nat} : Circuit n → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => 1 + c.gateCount
  | .and a b => 1 + a.gateCount + b.gateCount
  | .or a b => 1 + a.gateCount + b.gateCount
  | .xor a b => 1 + a.gateCount + b.gateCount

def binaryGateCount {n : Nat} : Circuit n → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => c.binaryGateCount
  | .and a b => 1 + a.binaryGateCount + b.binaryGateCount
  | .or a b => 1 + a.binaryGateCount + b.binaryGateCount
  | .xor a b => 1 + a.binaryGateCount + b.binaryGateCount

def depth {n : Nat} : Circuit n → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => 1 + c.depth
  | .and a b => 1 + Nat.max a.depth b.depth
  | .or a b => 1 + Nat.max a.depth b.depth
  | .xor a b => 1 + Nat.max a.depth b.depth

def isMonotone {n : Nat} : Circuit n → Bool
  | .input _ => true
  | .const _ => true
  | .not _ => false
  | .and a b => a.isMonotone && b.isMonotone
  | .or a b => a.isMonotone && b.isMonotone
  | .xor _ _ => false

def usesInput {n : Nat} : Circuit n → Fin n → Bool
  | .input j, i => decide (j = i)
  | .const _, _ => false
  | .not c, i => c.usesInput i
  | .and a b, i => a.usesInput i || b.usesInput i
  | .or a b, i => a.usesInput i || b.usesInput i
  | .xor a b, i => a.usesInput i || b.usesInput i

def Computes {n : Nat} (c : Circuit n) (f : BoolFn n) : Prop :=
  ∀ x : BoolVec n, c.eval x = f x

end Circuit

/-- Shared-wire DAG gates over full binary basis {NOT, AND, OR, XOR, CONST}. -/
inductive WireOp where
  | const (b : Bool)
  | not (w : Nat)
  | and (w1 w2 : Nat)
  | or (w1 w2 : Nat)
  | xor (w1 w2 : Nat)
  deriving Repr, DecidableEq

structure DAGCircuit (n : Nat) where
  gates : List WireOp
  outputWire : Nat
  deriving Repr, DecidableEq

namespace DAGCircuit

def evalWires {n : Nat} (x : BoolVec n) (gates : List WireOp) : Array Bool :=
  let init : Array Bool := Array.ofFn (fun i : Fin n => x i)
  gates.foldl (fun acc op =>
    let get (w : Nat) : Bool := acc.getD w false
    let v := match op with
      | .const b => b
      | .not w => !(get w)
      | .and w1 w2 => get w1 && get w2
      | .or w1 w2 => get w1 || get w2
      | .xor w1 w2 => Bool.xor (get w1) (get w2)
    acc.push v
  ) init

def eval {n : Nat} (c : DAGCircuit n) (x : BoolVec n) : Bool :=
  (evalWires x c.gates).getD c.outputWire false

def size {n : Nat} (c : DAGCircuit n) : Nat := c.gates.length

def Computes {n : Nat} (c : DAGCircuit n) (f : BoolFn n) : Prop :=
  ∀ x : BoolVec n, c.eval x = f x

end DAGCircuit

/-! ## 3. CNF, SAT, and Resolution Proof Complexity -/

structure Literal where
  var : Nat
  pos : Bool
  deriving Repr, DecidableEq

abbrev Clause := List Literal
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Literal) : Bool :=
  if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLit a)

def evalCNF (a : Assignment) (φ : CNF) : Bool :=
  φ.all (evalClause a)

def Satisfiable (φ : CNF) : Prop :=
  ∃ a : Assignment, evalCNF a φ = true

def Unsatisfiable (φ : CNF) : Prop :=
  ∀ a : Assignment, evalCNF a φ = false

def Is3CNF (φ : CNF) : Prop :=
  ∀ c ∈ φ, c.length ≤ 3

def IsHornClause (c : Clause) : Bool :=
  (c.filter (fun l => l.pos)).length ≤ 1

def IsHornCNF (φ : CNF) : Bool :=
  φ.all IsHornClause

/-- Resolution rule: if c1 contains +v and c2 contains -v, any clause containing all other literals is a resolvent. -/
def IsResolvent (c1 c2 r : Clause) (v : Nat) : Prop :=
  ⟨v, true⟩ ∈ c1 ∧
  ⟨v, false⟩ ∈ c2 ∧
  (∀ l ∈ c1, l ≠ ⟨v, true⟩ → l ∈ r) ∧
  (∀ l ∈ c2, l ≠ ⟨v, false⟩ → l ∈ r) ∧
  (∀ l ∈ r, (l ∈ c1 ∧ l ≠ ⟨v, true⟩) ∨ (l ∈ c2 ∧ l ≠ ⟨v, false⟩))

inductive ResDerivable (φ : CNF) : Clause → Prop where
  | axiomClause {c : Clause} (h : c ∈ φ) : ResDerivable φ c
  | resolve {c1 c2 r : Clause} {v : Nat}
      (h1 : ResDerivable φ c1)
      (h2 : ResDerivable φ c2)
      (hr : IsResolvent c1 c2 r v) : ResDerivable φ r

inductive ResProof (φ : CNF) : Clause → Type where
  | leaf {c : Clause} (h : c ∈ φ) : ResProof φ c
  | step {c1 c2 r : Clause} {v : Nat}
      (p1 : ResProof φ c1)
      (p2 : ResProof φ c2)
      (hr : IsResolvent c1 c2 r v) : ResProof φ r

def ResProof.size {φ : CNF} {c : Clause} : ResProof φ c → Nat
  | .leaf _ => 1
  | .step p1 p2 _ => 1 + p1.size + p2.size

def ResProof.width {φ : CNF} {c : Clause} : ResProof φ c → Nat
  | .leaf (c := c) _ => c.length
  | .step (r := r) p1 p2 _ => Nat.max r.length (Nat.max p1.width p2.width)

/-- Pigeonhole principle PHP(m, n): m pigeons into n holes. Variable index = p * n + h. -/
def phpVar (n p h : Nat) : Nat := p * n + h

def phpPigeonClause (n p : Nat) : Clause :=
  (List.range n).map (fun h => ⟨phpVar n p h, true⟩)

def phpHoleClauses (m n : Nat) : CNF :=
  (List.range n).flatMap (fun h =>
    (List.range m).flatMap (fun p1 =>
      (List.range m).filterMap (fun p2 =>
        if p1 < p2 then
          some [⟨phpVar n p1 h, false⟩, ⟨phpVar n p2 h, false⟩]
        else
          none)))

def PHP (m n : Nat) : CNF :=
  (List.range m).map (phpPigeonClause n) ++ phpHoleClauses m n

/-! ## 4. Asymptotic Growth Bounds -/

def PolyBounded (f : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n : Nat, f n ≤ c * (n + 1) ^ k + c

abbrev Language := List Bool → Bool

-- Note: Concrete step-counted machine models for P, NP, and poly-time reductions
-- belong in a dedicated machine-semantics module (no ungrounded cost-function stubs).

/-! ## 5. Full Binary Basis (B2 / U2) Shared-Wire DAG Circuits & Frontier Functions -/

/-- Any of the 16 binary Boolean operations specified by its 2×2 truth table. -/
structure B2Op where
  b00 : Bool
  b01 : Bool
  b10 : Bool
  b11 : Bool
  deriving Repr, DecidableEq

namespace B2Op

def eval (op : B2Op) (a b : Bool) : Bool :=
  match a, b with
  | false, false => op.b00
  | false, true  => op.b01
  | true,  false => op.b10
  | true,  true  => op.b11

def isXorOrXnor (op : B2Op) : Bool :=
  (op.b00 == op.b11) && (op.b01 == op.b10) && (op.b00 != op.b01)

/-- U2 is the full binary basis minus XOR and XNOR. -/
def isU2 (op : B2Op) : Bool := !op.isXorOrXnor

def opAnd  : B2Op := ⟨false, false, false, true⟩
def opOr   : B2Op := ⟨false, true, true, true⟩
def opXor  : B2Op := ⟨false, true, true, false⟩
def opXnor : B2Op := ⟨true, false, false, true⟩
def opNand : B2Op := ⟨true, true, true, false⟩
def opNor  : B2Op := ⟨true, false, false, false⟩
def opAndNot : B2Op := ⟨false, false, true, false⟩  -- a ∧ ¬b
def opNotAnd : B2Op := ⟨false, true, false, false⟩  -- ¬a ∧ b

end B2Op

structure B2Gate where
  op : B2Op
  w1 : Nat
  w2 : Nat
  deriving Repr, DecidableEq

/-- Shared-wire DAG circuit over the full binary basis B2.
    Wires 0 .. n-1 are inputs x 0 .. x (n-1); gate k writes wire n + k. -/
structure B2Circuit (n : Nat) where
  gates : List B2Gate
  outputWire : Nat
  deriving Repr, DecidableEq

namespace B2Circuit

def evalWires {n : Nat} (x : BoolVec n) (gates : List B2Gate) : Array Bool :=
  let init : Array Bool := Array.ofFn (fun i : Fin n => x i)
  gates.foldl (fun acc g =>
    let v1 := acc.getD g.w1 false
    let v2 := acc.getD g.w2 false
    acc.push (g.op.eval v1 v2)
  ) init

def eval {n : Nat} (c : B2Circuit n) (x : BoolVec n) : Bool :=
  (evalWires x c.gates).getD c.outputWire false

def size {n : Nat} (c : B2Circuit n) : Nat := c.gates.length

def isU2 {n : Nat} (c : B2Circuit n) : Bool :=
  c.gates.all (fun g => g.op.isU2)

def Computes {n : Nat} (c : B2Circuit n) (f : BoolFn n) : Prop :=
  ∀ x : BoolVec n, c.eval x = f x

end B2Circuit

/-- Hamming weight of an n-bit Boolean vector. -/
def hammingWeight {n : Nat} (x : BoolVec n) : Nat :=
  (List.finRange n).foldl (fun acc i => if x i then acc + 1 else acc) 0

/-- Threshold function: true iff at least k input bits are true. -/
def thresh (n k : Nat) : BoolFn n :=
  fun x => decide (k ≤ hammingWeight x)

/-- 5-bit Majority (threshold 3 of 5). -/
def maj5 : BoolFn 5 := thresh 5 3

/-- MOD3=0 function: true iff Hamming weight is divisible by 3. -/
def mod3Eq0 (n : Nat) : BoolFn n :=
  fun x => decide (hammingWeight x % 3 = 0)

/-- Cyclic-adjacent-ones on an n-ring: true iff some i and (i+1) mod n are both true. -/
def cyclicAdj (n : Nat) : BoolFn n :=
  fun x =>
    (List.finRange n).any (fun i =>
      if h : n > 0 then
        x i && x ⟨(i.val + 1) % n, Nat.mod_lt _ h⟩
      else false)

/-- Restrict a CNF by assigning variable v := val. -/
def restrictClause (v : Nat) (val : Bool) (c : Clause) : Option Clause :=
  if c.any (fun l => l.var == v && l.pos == val) then
    none
  else
    some (c.filter (fun l => l.var != v))

def restrictCNF (v : Nat) (val : Bool) (φ : CNF) : CNF :=
  φ.filterMap (restrictClause v val)

end PnP
