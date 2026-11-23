import PnP.Core

/-
  L-bar-003: Formal Relativization Barrier Metatheorem (Baker–Gill–Solovay abstraction).

  Any proof technique that relativizes — i.e., yields a uniform theorem valid relative
  to every oracle O — cannot resolve `P^empty = NP^empty` whenever there exists an
  oracle A making `P^A = NP^A` and an oracle B making `P^B ≠ NP^B`.
-/
namespace PnP.Lemmas.L_bar_003

abbrev Oracle := List Bool → Bool

def emptyOracle : Oracle := fun _ => false

/-- Primary relativization barrier metatheorem:
    if oracle-parameterized classes collapse under some oracle A and separate under
    some oracle B, then neither a universal separation nor a universal collapse holds. -/
theorem relativization_barrier_meta
    (P_O NP_O : Oracle → Prop)
    (hEq : ∃ A, P_O A = NP_O A)
    (hNeq : ∃ B, P_O B ≠ NP_O B) :
    (¬ ∀ O, P_O O ≠ NP_O O) ∧ (¬ ∀ O, P_O O = NP_O O) := by
  constructor
  · intro hAllNeq
    rcases hEq with ⟨A, hA⟩
    exact hAllNeq A hA
  · intro hAllEq
    rcases hNeq with ⟨B, hB⟩
    exact hB (hAllEq B)

/-- Possible verdicts of a proof resolving P vs NP relative to an oracle. -/
inductive Verdict where
  | collapse
  | separation
  deriving Repr, DecidableEq

/-- The proposition asserted by a verdict relative to oracle `O`. -/
def Verdict.holds (P_O NP_O : Oracle → Prop) (O : Oracle) : Verdict → Prop
  | .collapse => P_O O = NP_O O
  | .separation => P_O O ≠ NP_O O

/-- A relativizing proof technique is one whose verdict holds uniformly across all oracles. -/
structure RelativizingProof (P_O NP_O : Oracle → Prop) where
  verdict : Verdict
  uniform : ∀ O : Oracle, verdict.holds P_O NP_O O

/-- Any relativizing proof automatically resolves the unrelativized (empty-oracle) question. -/
theorem RelativizingProof.resolves_empty
    {P_O NP_O : Oracle → Prop}
    (π : RelativizingProof P_O NP_O) :
    π.verdict.holds P_O NP_O emptyOracle :=
  π.uniform emptyOracle

/-- Strengthened obstruction: under Baker–Gill–Solovay witness oracles `A` and `B`,
    no relativizing proof exists at all. -/
theorem no_relativizing_proof
    (P_O NP_O : Oracle → Prop)
    (hEq : ∃ A, P_O A = NP_O A)
    (hNeq : ∃ B, P_O B ≠ NP_O B) :
    ¬ Nonempty (RelativizingProof P_O NP_O) := by
  intro ⟨π⟩
  have hMeta := relativization_barrier_meta P_O NP_O hEq hNeq
  cases h : π.verdict with
  | collapse =>
      apply hMeta.2
      intro O
      have hO := π.uniform O
      rw [h] at hO
      exact hO
  | separation =>
      apply hMeta.1
      intro O
      have hO := π.uniform O
      rw [h] at hO
      exact hO

/-- Corollary: no relativizing proof can resolve `P_O emptyOracle` vs `NP_O emptyOracle`. -/
theorem no_relativizing_resolution_of_empty
    (P_O NP_O : Oracle → Prop)
    (hEq : ∃ A, P_O A = NP_O A)
    (hNeq : ∃ B, P_O B ≠ NP_O B) :
    ¬ ∃ π : RelativizingProof P_O NP_O,
        π.verdict.holds P_O NP_O emptyOracle := by
  intro ⟨π, _⟩
  exact no_relativizing_proof P_O NP_O hEq hNeq ⟨π⟩

/-- Concrete witness oracle model proving the BGS hypotheses are non-vacuously satisfiable. -/
def toyP (_ : Oracle) : Prop := True
def toyNP (O : Oracle) : Prop := O [] = true

theorem toy_model_bgs_witnesses :
    (∃ A, toyP A = toyNP A) ∧ (∃ B, toyP B ≠ toyNP B) := by
  constructor
  · refine ⟨fun _ => true, ?_⟩
    simp [toyP, toyNP]
  · refine ⟨emptyOracle, ?_⟩
    intro hEq
    dsimp [toyP, toyNP, emptyOracle] at hEq
    have hTrue : (false = true) := hEq ▸ trivial
    exact Bool.false_ne_true hTrue

theorem toy_model_no_relativizing_proof :
    ¬ Nonempty (RelativizingProof toyP toyNP) :=
  no_relativizing_proof toyP toyNP toy_model_bgs_witnesses.1 toy_model_bgs_witnesses.2

end PnP.Lemmas.L_bar_003
