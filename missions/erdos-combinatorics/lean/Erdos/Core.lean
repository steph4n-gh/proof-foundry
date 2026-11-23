/-
  Erdos.Core — Pure Lean 4.36.0 foundations for Ramsey theory, Turán / extremal graph theory,
  Schur additive combinatorics, Erdős Problem #128 (Sparse Halves), and Erdős Problem #156
  (Minimal Maximal Sidon Sets). Zero Mathlib: ~1s kernel checks.
-/
namespace Erdos

/-! ## 1. Simple Graphs, Cliques, Independent Sets, Ramsey & Turán -/

/-- Simple undirected graph on Fin n represented as a symmetric, irreflexive Bool adjacency matrix. -/
structure SimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ v, adj v v = false

/-- Count of unordered edges (u < v with adj u v = true). -/
def edgeCount {n : Nat} (G : SimpleGraph n) : Nat :=
  (List.finRange n).foldl (fun acc u =>
    acc + ((List.finRange n).filter (fun v => decide (u.val < v.val) && G.adj u v)).length
  ) 0

/-- Number of edges inside an induced vertex subset S : Fin n → Bool. -/
def inducedEdgeCount {n : Nat} (G : SimpleGraph n) (S : Fin n → Bool) : Nat :=
  (List.finRange n).foldl (fun acc u =>
    if S u then
      acc + ((List.finRange n).filter (fun v => decide (u.val < v.val) && S v && G.adj u v)).length
    else acc
  ) 0

/-- Cardinality of a vertex subset S : Fin n → Bool. -/
def subsetSize {n : Nat} (S : Fin n → Bool) : Nat :=
  ((List.finRange n).filter S).length

/-- Graph contains a triangle (K3). -/
def HasTriangle {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c : Fin n, G.adj a b = true ∧ G.adj b c = true ∧ G.adj a c = true

/-- Graph contains a 4-clique (K4). -/
def HasK4 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c d : Fin n,
    G.adj a b = true ∧ G.adj a c = true ∧ G.adj a d = true ∧
    G.adj b c = true ∧ G.adj b d = true ∧ G.adj c d = true

/-- Graph contains a 3-element independent set (no edges among 3 distinct vertices). -/
def HasIndep3 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c : Fin n,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.adj a b = false ∧ G.adj b c = false ∧ G.adj a c = false

/-- Graph is bipartite (2-colorable). -/
def IsBipartite {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ col : Fin n → Bool, ∀ u v : Fin n, G.adj u v = true → col u ≠ col v

/-- Ramsey property R(3, 3) holds at N. -/
def Ramsey33At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasTriangle G ∨ HasIndep3 G

/-- Ramsey property R(3, 4) holds at N. -/
def Ramsey34At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasIndep3 G ∨ HasK4 G

/-- Graph contains a 4-element independent set (no edges among 4 distinct vertices). -/
def HasIndep4 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ a b c d : Fin n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.adj a b = false ∧ G.adj a c = false ∧ G.adj a d = false ∧
    G.adj b c = false ∧ G.adj b d = false ∧ G.adj c d = false

/-- Graph contains a 5-element independent set (no edges among 5 distinct vertices). -/
def HasIndep5 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ v0 v1 v2 v3 v4 : Fin n,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧
    v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
    G.adj v0 v1 = false ∧ G.adj v0 v2 = false ∧ G.adj v0 v3 = false ∧ G.adj v0 v4 = false ∧
    G.adj v1 v2 = false ∧ G.adj v1 v3 = false ∧ G.adj v1 v4 = false ∧
    G.adj v2 v3 = false ∧ G.adj v2 v4 = false ∧ G.adj v3 v4 = false

/-- Graph contains a 6-element independent set (no edges among 6 distinct vertices). -/
def HasIndep6 {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ v0 v1 v2 v3 v4 v5 : Fin n,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧ v0 ≠ v5 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v1 ≠ v5 ∧
    v2 ≠ v3 ∧ v2 ≠ v4 ∧ v2 ≠ v5 ∧
    v3 ≠ v4 ∧ v3 ≠ v5 ∧ v4 ≠ v5 ∧
    G.adj v0 v1 = false ∧ G.adj v0 v2 = false ∧ G.adj v0 v3 = false ∧ G.adj v0 v4 = false ∧ G.adj v0 v5 = false ∧
    G.adj v1 v2 = false ∧ G.adj v1 v3 = false ∧ G.adj v1 v4 = false ∧ G.adj v1 v5 = false ∧
    G.adj v2 v3 = false ∧ G.adj v2 v4 = false ∧ G.adj v2 v5 = false ∧
    G.adj v3 v4 = false ∧ G.adj v3 v5 = false ∧ G.adj v4 v5 = false

/-- Ramsey property R(4, 4) holds at N. -/
def Ramsey44At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasK4 G ∨ HasIndep4 G

/-- Ramsey property R(3, 5) holds at N (triangle or 5-independent set). -/
def Ramsey35At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasTriangle G ∨ HasIndep5 G

/-- Ramsey property R(3, 6) holds at N (triangle or 6-independent set). -/
def Ramsey36At (n : Nat) : Prop :=
  ∀ G : SimpleGraph n, HasTriangle G ∨ HasIndep6 G

/-! ## 2. Erdős Problem #128 ($250 Sparse-Halves Conjecture, erdosproblems.com/128) -/

/-- A graph G on n vertices satisfies the Erdős #128 sparse-half property if some subset S
    of size ≥ n / 2 spans at most n^2 / 50 edges (i.e. 50 * e(S) ≤ n * n). -/
def HasSparseHalf {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ S : Fin n → Bool, n / 2 ≤ subsetSize S ∧ 50 * inducedEdgeCount G S ≤ n * n

/-! ## 3. Schur Additive Combinatorics -/

/-- A k-coloring of {1, ..., n} (Fin n → Fin k where i represents i+1) is sum-free
    if no x, y, z with (x+1) + (y+1) = (z+1) share the same color. -/
def IsSumFreeColoring (n k : Nat) (col : Fin n → Fin k) : Prop :=
  ∀ x y z : Fin n, (x.val + 1) + (y.val + 1) = (z.val + 1) →
    ¬ (col x = col y ∧ col y = col z)

/-- Schur number property: every k-coloring of {1..n} contains a monochromatic x + y = z. -/
def SchurForced (n k : Nat) : Prop :=
  ∀ col : Fin n → Fin k, ¬ IsSumFreeColoring n k col

/-- A k-coloring of {1..n} is 3-AP-free if no arithmetic progression a < b < c (a + c = 2b) is monochromatic. -/
def IsAPFree3 (n k : Nat) (col : Fin n → Fin k) : Prop :=
  ∀ x y z : Fin n, x.val < y.val → x.val + z.val = 2 * y.val →
    ¬ (col x = col y ∧ col y = col z)

/-- Van der Waerden 3-AP forcing: every k-coloring of {1..n} contains a monochromatic 3-term arithmetic progression. -/
def VanDerWaerden3 (n k : Nat) : Prop :=
  ∀ col : Fin n → Fin k, ¬ IsAPFree3 n k col

/-! ## 4. Erdős Problem #156 (Smallest Maximal Sidon Sets, erdosproblems.com/156) -/

/-- A list of positive integers A is a Sidon (B2) set if all unordered pairwise sums a + b (a ≤ b)
    uniquely determine the pair {a, b}. -/
def IsSidon (A : List Nat) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Every element of A lies in {1, ..., N}. -/
def SubsetOfRange (N : Nat) (A : List Nat) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- A is a maximal Sidon subset of {1, ..., N}: it is Sidon, contained in {1..N},
    and adding any x ∈ {1..N} \ A destroys the Sidon property. -/
def IsMaximalSidon (N : Nat) (A : List Nat) : Prop :=
  A.Nodup ∧ SubsetOfRange N A ∧ IsSidon A ∧
  ∀ x : Nat, 1 ≤ x → x ≤ N → x ∉ A → ¬ IsSidon (x :: A)

end Erdos
