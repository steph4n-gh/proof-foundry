import Lean
import PFFormal.StateMachine

/-!
# Axiom audit

`#assert_standard_axioms` collects every axiom that each named theorem transitively depends on.
It reports an error, which fails `lake build`, if any of them falls outside the standard set
`propext`, `Classical.choice`, `Quot.sound`. A `sorry` adds `sorryAx` and `native_decide` adds
`Lean.ofReduceBool`, so the build fails on either.

`#assert_standard_axioms_in PF` applies the same check to every theorem in the `PF` namespace,
including the helper lemmas, so a new or renamed lemma cannot skip the audit.

Each audited theorem logs an `AXIOMS <name>: [...]` line, which
`formal/verify_state_machine_equiv.mjs` parses.
-/

open Lean Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def auditAxioms (ref : Syntax) (n : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| Lean.collectAxioms n
  let bad := axs.filter (fun a => !standardAxioms.contains a)
  if !bad.isEmpty then
    throwErrorAt ref m!"{n} depends on non-standard axioms {bad.toList}"
  logInfoAt ref m!"AXIOMS {n}: {axs.toList}"

/-- Check the axioms of each named theorem. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    auditAxioms id n

/-- Check the axioms of every theorem whose name starts with the given namespace. -/
elab "#assert_standard_axioms_in " ns:ident : command => do
  let env ← getEnv
  let pre := ns.getId
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if pre.isPrefixOf n && !n.isInternal && ci matches .thmInfo _ then acc.push n else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwErrorAt ns m!"no theorems found in namespace {pre}"
  for n in names do
    auditAxioms ns n
  logInfoAt ns m!"AUDITED {names.size} theorems in {pre}"

/-! ## Requested theorems -/

-- 1. Monotone best record (single step, and over any replay list).
#assert_standard_axioms PF.koth_monotone_best PF.koth_monotone_best_replay
-- 2. Monotone refuted bound.
#assert_standard_axioms PF.koth_monotone_refuted PF.koth_monotone_refuted_replay
-- 3. Exact anti-farming telescoping identities.
#assert_standard_axioms PF.koth_anti_farming_ledger PF.koth_anti_farming_record_points
  PF.koth_anti_farming_bound_points PF.koth_anti_farming_record_points_replay
-- 4. Contradiction is sticky.
#assert_standard_axioms PF.koth_contradiction_sticky_step PF.koth_contradiction_sticky
  PF.koth_contradiction_reachable PF.koth_contradiction_replay
-- 5. Crossing record and bound contradict in both orders.
#assert_standard_axioms PF.koth_contradiction_order_independent
-- 6. A closed hunt is exactly optimal and refuses further attempts.
#assert_standard_axioms PF.koth_closed_exact_optimal PF.koth_closed_denies
-- 7. Standard-claim contradiction is sticky.
#assert_standard_axioms PF.claim_contradiction_sticky_step PF.claim_contradiction_sticky
-- 8. Proof and refutation contradict in either order.
#assert_standard_axioms PF.claim_order_independent_contradiction
-- 9. Barriers never overwrite a verdict.
#assert_standard_axioms PF.barrier_never_overwrites_verdict
-- 10. Seat–claim bijection.
#assert_standard_axioms PF.seat_claim_bijection_release PF.seat_claim_bijection_releaseClaim
  PF.seat_claim_bijection_assign PF.seat_claim_bijection_preserved PF.Bij.iff PF.Bij.single_owner
-- 11. Trust seal and rung conquest.
#assert_standard_axioms PF.trust_seal_and_conquered_sound PF.trust_seal_contradiction_iff
  PF.conquered_false_of_bad_seal PF.conquered_record_default PF.conquered_replay_default

/-! ## Every theorem in the development -/

#assert_standard_axioms_in PF
