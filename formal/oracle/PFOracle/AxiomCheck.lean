import Lean.Elab.Command
import Lean.Util.CollectAxioms
import PFOracle.BF16Oracle
import PFOracle.BF16Rounding

open Lean Elab Command PFOracle

run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let theorems := [
    ``dyadicAdd_sound, ``dyadicSub_sound, ``dyadicMul_sound, ``dyadicEq_iff, ``dyadicSign_sound,
    ``roundShiftEven_err_le_half, ``roundShiftEven_nearest, ``roundShiftEven_tie_even, ``roundShiftEven_mono,
    ``bf16LatticeIndex_zero, ``bf16UlpDist_zero_pm, ``bf16UlpDist_symm, ``bf16UlpDist_triangle,
    ``bf16ToF32_roundtrip, ``bf16ToF32_nan_canonical, ``f32BitsToBf16RNE_eq_roundShiftEven,
    ``f32BitsToBf16RNE_value_spec,
    ``bf16LatticeIndex_strict_mono, ``bf16LatticeIndex_eq_iff, ``bf16UlpDist_zero_iff,
    ``f64BitsToBf16RNE_nan_canonical, ``f64BitsToBf16RNE_inf, ``f64BitsToBf16RNE_value_spec,
    ``bf16ToF32_dyadic_exact, ``dyadicToF32BitsRNE_value_spec,
    ``fmafDyadicSum_sound, ``fmafFiniteBits_value_spec,
    ``cppIshrS_equiv_sshiftRight, ``cppIshrS_no_ub_shift_bounds,
    ``cppIshl_no_ub_shift_bounds, ``cppIshrU_no_ub_shift_bounds,
    ``cppIadd_two_complement_mod, ``cppIsub_two_complement_mod, ``cppImul_two_complement_mod]
  for theoremName in theorems do
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{theoremName} uses a nonstandard axiom {axiomName}"
    logInfo m!"{theoremName} axioms {axioms.toList}"
