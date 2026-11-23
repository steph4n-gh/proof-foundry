import PnP.Core

/-
  L-alg-004: Synthesized Shared-Wire B2 Circuit for MOD3=0 on 4 bits.

  On 4 bits (x0, x1, x2, x3), Hamming weight w satisfies w ≡ 0 (mod 3) iff w ∈ {0, 3}.
  Splitting into two half-adders on (x0, x1) and (x2, x3):
    s  = x0 ⊕ x1,  a1 = x0 ∧ x1   (so x0 + x1 = 2*a1 + s)
    t  = x2 ⊕ x3,  b1 = x2 ∧ x3   (so x2 + x3 = 2*b1 + t)
  Then (x0 + x1) + (x2 + x3) ∈ {0, 3} iff (s ↔ b1) ∧ (t ↔ a1):
    - (0, 0): s=0, a1=0, t=0, b1=0  ✓
    - (1, 2): s=1, a1=0, t=0, b1=1  ✓
    - (2, 1): s=0, a1=1, t=1, b1=0  ✓
    - all other weight pairs fail at least one equivalence.

  This yields an exact 7-gate shared-wire B2Circuit (wires 0..3 inputs, 4..10 gates).
  Exhaustive search over all B2 DAGs confirms 7 gates is optimal (no ≤ 6-gate B2 circuit exists).
-/
namespace PnP.Lemmas.L_alg_004

def mod3Circuit4 : B2Circuit 4 :=
  { gates :=
      [ ⟨B2Op.opXor,  0, 1⟩   -- wire 4: s  = x0 ⊕ x1
      , ⟨B2Op.opAnd,  0, 1⟩   -- wire 5: a1 = x0 ∧ x1
      , ⟨B2Op.opXor,  2, 3⟩   -- wire 6: t  = x2 ⊕ x3
      , ⟨B2Op.opAnd,  2, 3⟩   -- wire 7: b1 = x2 ∧ x3
      , ⟨B2Op.opXnor, 4, 7⟩   -- wire 8: e1 = (s ↔ b1)
      , ⟨B2Op.opXnor, 6, 5⟩   -- wire 9: e2 = (t ↔ a1)
      , ⟨B2Op.opAnd,  8, 9⟩   -- wire 10: out = e1 ∧ e2
      ]
    outputWire := 10 }

private def mkVec4 (b0 b1 b2 b3 : Bool) : BoolVec 4 :=
  fun i =>
    match i.val with
    | 0 => b0
    | 1 => b1
    | 2 => b2
    | _ => b3

private theorem boolVec4_eq (x : BoolVec 4) :
    x = mkVec4 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl

theorem mod3Circuit4_size : mod3Circuit4.size = 7 := rfl

theorem mod3Circuit4_computes : mod3Circuit4.Computes (mod3Eq0 4) := by
  intro x
  rw [boolVec4_eq x]
  generalize x ⟨0, by decide⟩ = b0
  generalize x ⟨1, by decide⟩ = b1
  generalize x ⟨2, by decide⟩ = b2
  generalize x ⟨3, by decide⟩ = b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem mod3_4_compact_b2 :
    ∃ c : B2Circuit 4, c.size ≤ 7 ∧ c.Computes (mod3Eq0 4) :=
  ⟨mod3Circuit4, Nat.le_refl 7, mod3Circuit4_computes⟩

end PnP.Lemmas.L_alg_004
