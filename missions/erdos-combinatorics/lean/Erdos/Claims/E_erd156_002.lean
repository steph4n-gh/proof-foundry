import Erdos.Core

/-
  E-erd156-002: Erdős Problem #156 Small-N Synthesis.
  Explicit 5-element maximal Sidon subset A = [1, 4, 11, 15, 17] ⊆ {1, ..., 30},
  beating the 6-element greedy Sidon set [1, 2, 4, 8, 13, 21] and proving
  ∃ A : List Nat, A.length ≤ 6 ∧ IsMaximalSidon 30 A.
-/
namespace Erdos.Claims.E_erd156_002

def sidonWitness30 : List Nat := [1, 4, 11, 15, 17]

private def isSidonBool (A : List Nat) : Bool :=
  A.all fun a => A.all fun b => A.all fun c => A.all fun d =>
    !(decide (a ≤ b) && decide (c ≤ d) && (a + b == c + d)) || (a == c && b == d)

private theorem isSidonBool_sound (A : List Nat) (h : isSidonBool A = true) : IsSidon A := by
  intro a ha b hb c hc d hd hab hcd hsum
  unfold isSidonBool at h
  have h1 := List.all_eq_true.mp h a ha
  have h2 := List.all_eq_true.mp h1 b hb
  have h3 := List.all_eq_true.mp h2 c hc
  have h4 := List.all_eq_true.mp h3 d hd
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_true,
    decide_eq_false_iff_not, beq_eq_false_iff_ne, beq_iff_eq] at h4
  rcases h4 with ((h_le1 | h_le2) | h_ne) | ⟨hac, hbd⟩
  · exact absurd hab h_le1
  · exact absurd hcd h_le2
  · exact absurd hsum h_ne
  · exact ⟨hac, hbd⟩

private theorem sidon_pair_eq {B : List Nat} (h : IsSidon B)
    {p q r s : Nat} (hp : p ∈ B) (hq : q ∈ B) (hr : r ∈ B) (hs : s ∈ B)
    (hsum : p + q = r + s) : (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  if hpq : p ≤ q then
    if hrs : r ≤ s then
      exact Or.inl (h p hp q hq r hr s hs hpq hrs hsum)
    else
      have ⟨h1, h2⟩ := h p hp q hq s hs r hr hpq (by omega) (by omega)
      exact Or.inr ⟨h1, h2⟩
  else
    if hrs : r ≤ s then
      have ⟨h1, h2⟩ := h q hq p hp r hr s hs (by omega) hrs (by omega)
      exact Or.inr ⟨h2, h1⟩
    else
      have ⟨h1, h2⟩ := h q hq p hp s hs r hr (by omega) (by omega) (by omega)
      exact Or.inl ⟨h2, h1⟩

private def isBlockedBool (A : List Nat) (x : Nat) : Bool :=
  A.any fun a => A.any fun b =>
    (x + x == a + b) || A.any fun c => x + a == b + c

private theorem isBlockedBool_sound (A : List Nat) (x : Nat)
    (hb : isBlockedBool A x = true) (hnot : x ∉ A) : ¬ IsSidon (x :: A) := by
  intro hsid
  unfold isBlockedBool at hb
  rcases List.any_eq_true.mp hb with ⟨a, ha, h1⟩
  rcases List.any_eq_true.mp h1 with ⟨b, hb', h2⟩
  rcases Bool.or_eq_true_iff.mp h2 with h2x | h3
  · have hsum : x + x = a + b := beq_iff_eq.mp h2x
    rcases sidon_pair_eq hsid List.mem_cons_self List.mem_cons_self
      (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb') hsum with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hnot ha
    · exact hnot hb'
  · rcases List.any_eq_true.mp h3 with ⟨c, hc, hsumB⟩
    have hsum : x + a = b + c := beq_iff_eq.mp hsumB
    rcases sidon_pair_eq hsid List.mem_cons_self (List.mem_cons_of_mem x ha)
      (List.mem_cons_of_mem x hb') (List.mem_cons_of_mem x hc) hsum with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hnot hb'
    · exact hnot hc

private def allBlockedInRange (N : Nat) (A : List Nat) : Bool :=
  (List.range N).all fun i =>
    let x := i + 1
    A.contains x || isBlockedBool A x

private theorem allBlockedInRange_sound (N : Nat) (A : List Nat)
    (h : allBlockedInRange N A = true) :
    ∀ x : Nat, 1 ≤ x → x ≤ N → x ∉ A → ¬ IsSidon (x :: A) := by
  intro x hx1 hxN hnot
  unfold allBlockedInRange at h
  have hmem : x - 1 ∈ List.range N := List.mem_range.mpr (by omega)
  have hx := List.all_eq_true.mp h (x - 1) hmem
  have heq : x - 1 + 1 = x := by omega
  rw [heq] at hx
  rcases Bool.or_eq_true_iff.mp hx with hcont | hblk
  · exact absurd (List.contains_iff_mem.mp hcont) hnot
  · exact isBlockedBool_sound A x hblk hnot

private theorem witness_sidon_bool : isSidonBool sidonWitness30 = true := rfl

private theorem witness_all_blocked : allBlockedInRange 30 sidonWitness30 = true := rfl

theorem small_maximal_sidon_30 : ∃ A : List Nat, A.length ≤ 6 ∧ IsMaximalSidon 30 A := by
  refine ⟨sidonWitness30, by decide, ?_, ?_, ?_, ?_⟩
  · decide
  · intro a ha
    simp only [sidonWitness30, List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  · exact isSidonBool_sound sidonWitness30 witness_sidon_bool
  · exact allBlockedInRange_sound 30 sidonWitness30 witness_all_blocked

end Erdos.Claims.E_erd156_002
