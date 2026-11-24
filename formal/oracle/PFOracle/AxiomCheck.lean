import Lean.Elab.Command
import Lean.Util.CollectAxioms
import PFOracle.MathOracle

open Lean Elab Command PFOracle

run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let theorems := [
    ``dyadicAdd_sound, ``dyadicSub_sound, ``dyadicMul_sound, ``dyadicEq_iff, ``dyadicSign_sound,
    ``exactDot_sound, ``orient2d_sign_exact, ``tdiv_error,
    ``fixed128Exp_early_exit_exact, ``fixed128Sin_early_exit_exact,
    ``fixed128Exp_term_error, ``fixed128Sin_square_error, ``fixed128Sin_term_error,
    ``fixed128Exp_rounding_error, ``fixed128Sin_rounding_error,
    ``expTaylor_remainder_bound, ``sinTaylor_remainder_bound, ``expTaylor_tail_lt_ulp,
    ``sinTaylor_tail_lt_ulp, ``oracle_bound_decimal, ``oracle_bound_lt_decimal,
    ``fixed128Exp_total_error_bound, ``fixed128Sin_total_error_bound,
    ``fixed128Exp_series_enclosure, ``fixed128Sin_series_enclosure,
    ``ceilScore_spec, ``ceilScore_eq_ceil, ``ceilScore_decision_robustness]
  for theoremName in theorems do
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{theoremName} uses a nonstandard axiom {axiomName}"
    logInfo m!"{theoremName} axioms {axioms.toList}"
