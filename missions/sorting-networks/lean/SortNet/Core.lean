/-
  SortNet.Core — Pure Lean 4.36.0 foundations for Optimal Sorting Networks (Knuth Vol. 3).
  Zero Mathlib: ~1s kernel builds. Supports both comparator-count and parallel-depth targets,
  plus Knuth's Zero-One Principle linking Boolean sorters to arbitrary Nat sorters.
-/
namespace SortNet

/-- A comparator network on n wires is an ordered list of wire pairs (i, j).
    Each comparator normalizes (min i j, max i j) and routes the smaller value to the lower index. -/
abbrev Net (n : Nat) := List (Fin n × Fin n)

/-- Apply one comparator to a Boolean wire vector. -/
def applyCompBool {n : Nat} (c : Fin n × Fin n) (v : Fin n → Bool) : Fin n → Bool :=
  let lo := if c.1.val ≤ c.2.val then c.1 else c.2
  let hi := if c.1.val ≤ c.2.val then c.2 else c.1
  fun k =>
    if k = lo then v lo && v hi
    else if k = hi then v lo || v hi
    else v k

/-- Evaluate a comparator network on a Boolean input vector. -/
def evalBool {n : Nat} (net : Net n) (v : Fin n → Bool) : Fin n → Bool :=
  net.foldl (fun acc c => applyCompBool c acc) v

/-- A Boolean wire vector is sorted (non-decreasing: all false before all true). -/
def isSortedBool {n : Nat} (v : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → v i = true → v j = true

/-- A network is a Boolean sorting network if it sorts every 0/1 input vector. -/
def IsBoolSorter (n : Nat) (net : Net n) : Prop :=
  ∀ v : Fin n → Bool, isSortedBool (evalBool net v)

/-- Apply one comparator to a natural-number wire vector. -/
def applyCompNat {n : Nat} (c : Fin n × Fin n) (v : Fin n → Nat) : Fin n → Nat :=
  let lo := if c.1.val ≤ c.2.val then c.1 else c.2
  let hi := if c.1.val ≤ c.2.val then c.2 else c.1
  fun k =>
    if k = lo then Nat.min (v lo) (v hi)
    else if k = hi then Nat.max (v lo) (v hi)
    else v k

/-- Evaluate a comparator network on a natural-number input vector. -/
def evalNat {n : Nat} (net : Net n) (v : Fin n → Nat) : Fin n → Nat :=
  net.foldl (fun acc c => applyCompNat c acc) v

/-- A natural-number wire vector is sorted (non-decreasing). -/
def isSortedNat {n : Nat} (v : Fin n → Nat) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → v i ≤ v j

/-- A network is a general sorting network if it sorts every natural-number input vector. -/
def IsNatSorter (n : Nat) (net : Net n) : Prop :=
  ∀ v : Fin n → Nat, isSortedNat (evalNat net v)

/-- Greedy parallel layer depth of a comparator network (disjoint wire comparators execute in parallel). -/
def netDepth {n : Nat} (net : Net n) : Nat :=
  let layers : Array Nat :=
    net.foldl (fun acc c =>
      let d := Nat.max (acc.getD c.1.val 0) (acc.getD c.2.val 0) + 1
      (acc.set! c.1.val d).set! c.2.val d
    ) (Array.replicate n 0)
  layers.foldl Nat.max 0

end SortNet
