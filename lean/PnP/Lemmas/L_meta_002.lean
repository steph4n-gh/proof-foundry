import PnP.Core

/-
  L-meta-002: No DAGCircuit over {NOT, AND, OR, XOR, CONST} with at most 1 gate
  can compute 3-bit Majority (MAJ3), because any such circuit leaves at least
  one of the 3 input wires unreferenced.
-/
namespace PnP.Lemmas.L_meta_002

private theorem exists_fin3_ne_two (w1 w2 : Nat) :
    ∃ i : Fin 3, i.val ≠ w1 ∧ i.val ≠ w2 := by
  by_cases h10 : w1 = 0
  · by_cases h21 : w2 = 1
    · exact ⟨⟨2, by decide⟩, by dsimp; omega, by dsimp; omega⟩
    · exact ⟨⟨1, by decide⟩, by dsimp; omega, by dsimp; omega⟩
  · by_cases h20 : w2 = 0
    · by_cases h11 : w1 = 1
      · exact ⟨⟨2, by decide⟩, by dsimp; omega, by dsimp; omega⟩
      · exact ⟨⟨1, by decide⟩, by dsimp; omega, by dsimp; omega⟩
    · exact ⟨⟨0, by decide⟩, by dsimp; omega, by dsimp; omega⟩

private theorem init_getD_flip (x : BoolVec 3) (i : Fin 3) (w : Nat) (hne : i.val ≠ w) :
    (Array.ofFn (fun j : Fin 3 => flipBit x i j)).getD w false =
    (Array.ofFn (fun j : Fin 3 => x j)).getD w false := by
  match w with
  | 0 =>
    have hne' : (⟨0, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨0, by decide⟩ = x ⟨0, by decide⟩
    simp only [flipBit, if_neg hne']
  | 1 =>
    have hne' : (⟨1, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨1, by decide⟩ = x ⟨1, by decide⟩
    simp only [flipBit, if_neg hne']
  | 2 =>
    have hne' : (⟨2, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨2, by decide⟩ = x ⟨2, by decide⟩
    simp only [flipBit, if_neg hne']
  | k + 3 =>
    have hlt : ¬ (k + 3 < 3) := by omega
    simp [Array.getD, hlt]

private theorem push_getD_flip (x : BoolVec 3) (i : Fin 3) (v1 v2 : Bool) (w : Nat)
    (hne : i.val ≠ w) (hv : w = 3 → v1 = v2) :
    ((Array.ofFn (fun j : Fin 3 => flipBit x i j)).push v1).getD w false =
    ((Array.ofFn (fun j : Fin 3 => x j)).push v2).getD w false := by
  match w with
  | 0 =>
    have hne' : (⟨0, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨0, by decide⟩ = x ⟨0, by decide⟩
    simp only [flipBit, if_neg hne']
  | 1 =>
    have hne' : (⟨1, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨1, by decide⟩ = x ⟨1, by decide⟩
    simp only [flipBit, if_neg hne']
  | 2 =>
    have hne' : (⟨2, by decide⟩ : Fin 3) ≠ i := fun h => hne (congrArg Fin.val h).symm
    change flipBit x i ⟨2, by decide⟩ = x ⟨2, by decide⟩
    simp only [flipBit, if_neg hne']
  | 3 =>
    change v1 = v2
    exact hv rfl
  | k + 4 =>
    have hlt : ¬ (k + 4 < 3 + 1) := by omega
    simp [Array.getD, hlt]

private theorem dag_size_le_one_unused_input (c : DAGCircuit 3) (hs : c.size ≤ 1) :
    ∃ i : Fin 3, ∀ x : BoolVec 3, c.eval (flipBit x i) = c.eval x := by
  rcases c with ⟨gates, out⟩
  match gates, hs with
  | [], _ =>
    rcases exists_fin3_ne_two out out with ⟨i, hi, _⟩
    refine ⟨i, fun x => ?_⟩
    exact init_getD_flip x i out hi
  | [op], _ =>
    by_cases hout : out = 3
    · subst hout
      cases op with
      | const b =>
        refine ⟨⟨0, by decide⟩, fun x => ?_⟩
        exact push_getD_flip x ⟨0, by decide⟩ b b 3 (by decide) (fun _ => rfl)
      | not w =>
        rcases exists_fin3_ne_two w w with ⟨i, hi, _⟩
        refine ⟨i, fun x => ?_⟩
        apply push_getD_flip x i _ _ 3 (by omega)
        intro _
        dsimp only
        rw [init_getD_flip x i w hi]
      | and w1 w2 =>
        rcases exists_fin3_ne_two w1 w2 with ⟨i, h1, h2⟩
        refine ⟨i, fun x => ?_⟩
        apply push_getD_flip x i _ _ 3 (by omega)
        intro _
        dsimp only
        rw [init_getD_flip x i w1 h1, init_getD_flip x i w2 h2]
      | or w1 w2 =>
        rcases exists_fin3_ne_two w1 w2 with ⟨i, h1, h2⟩
        refine ⟨i, fun x => ?_⟩
        apply push_getD_flip x i _ _ 3 (by omega)
        intro _
        dsimp only
        rw [init_getD_flip x i w1 h1, init_getD_flip x i w2 h2]
      | xor w1 w2 =>
        rcases exists_fin3_ne_two w1 w2 with ⟨i, h1, h2⟩
        refine ⟨i, fun x => ?_⟩
        apply push_getD_flip x i _ _ 3 (by omega)
        intro _
        dsimp only
        rw [init_getD_flip x i w1 h1, init_getD_flip x i w2 h2]
    · rcases exists_fin3_ne_two out out with ⟨i, hi, _⟩
      refine ⟨i, fun x => ?_⟩
      exact push_getD_flip x i _ _ out hi (fun h => absurd h hout)
  | _ :: _ :: _, hs =>
    simp [DAGCircuit.size] at hs

private theorem maj3_depends_all (i : Fin 3) :
    ∃ x : BoolVec 3, maj3 x ≠ maj3 (flipBit x i) := by
  have h : i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
    rcases i with ⟨v, hv⟩
    match v, hv with
    | 0, _ => left; rfl
    | 1, _ => right; left; rfl
    | 2, _ => right; right; rfl
  rcases h with rfl | rfl | rfl
  · exact ⟨fun j => j.val == 1, by decide⟩
  · exact ⟨fun j => j.val == 0, by decide⟩
  · exact ⟨fun j => j.val == 0, by decide⟩

theorem maj3_no_one_gate_dag (c : DAGCircuit 3) (hs : c.size ≤ 1) : ¬ c.Computes maj3 := by
  intro hc
  rcases dag_size_le_one_unused_input c hs with ⟨i, hinv⟩
  rcases maj3_depends_all i with ⟨x, hdep⟩
  apply hdep
  rw [← hc x, ← hc (flipBit x i), hinv x]

end PnP.Lemmas.L_meta_002
