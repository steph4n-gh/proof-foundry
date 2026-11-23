import PnP.Core

/-
  L-pcx-002: PHP(3,2) — three pigeons cannot fit injectively into two holes.
  Variables: pigeon p in hole h ↦ 2p + h, so vars 0..5.
-/
namespace PnP.Lemmas.L_pcx_002

open PnP

/-- PHP(3,2) evaluates to an explicit Boolean formula in the six variables 0..5. -/
theorem eval_php_3_2 (a : Assignment) :
    evalCNF a (PHP 3 2) =
      ((a 0 || a 1) && (a 2 || a 3) && (a 4 || a 5) &&
       (!a 0 || !a 2) && (!a 0 || !a 4) && (!a 2 || !a 4) &&
       (!a 1 || !a 3) && (!a 1 || !a 5) && (!a 3 || !a 5)) := by
  simp [PHP, phpPigeonClause, phpHoleClauses, phpVar, evalCNF, evalClause, evalLit,
    List.range_succ, Bool.and_assoc]

theorem php_3_2_unsat : Unsatisfiable (PHP 3 2) := by
  intro a
  rw [eval_php_3_2]
  cases a 0 <;> cases a 1 <;> cases a 2 <;> cases a 3 <;> cases a 4 <;> cases a 5 <;> rfl

end PnP.Lemmas.L_pcx_002
