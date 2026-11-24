import SortNet.Core
import SortNet.Statements.SN_003

namespace SortNet.Claims.SN_003

private inductive Pair6 where
  | p01 | p02 | p03 | p12 | p13 | p23
  deriving DecidableEq

private def toComp : Pair6 → Fin 4 × Fin 4
  | .p01 => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | .p02 => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | .p03 => (⟨0, by decide⟩, ⟨3, by decide⟩)
  | .p12 => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | .p13 => (⟨1, by decide⟩, ⟨3, by decide⟩)
  | .p23 => (⟨2, by decide⟩, ⟨3, by decide⟩)

private def badMask : Pair6 → Nat
  | .p01 => 0x2222
  | .p02 => 0x0a0a
  | .p03 => 0x00aa
  | .p12 => 0x0c0c
  | .p13 => 0x00cc
  | .p23 => 0x00f0

private def notBadMask : Pair6 → Nat
  | .p01 => 0xdddd
  | .p02 => 0xf5f5
  | .p03 => 0xff55
  | .p12 => 0xf3f3
  | .p13 => 0xff33
  | .p23 => 0xff0f

private def delta : Pair6 → Nat
  | .p01 => 1
  | .p02 => 3
  | .p03 => 7
  | .p12 => 2
  | .p13 => 6
  | .p23 => 4

private def stepMask (p : Pair6) (mask : Nat) : Nat :=
  (mask &&& notBadMask p) ||| ((mask &&& badMask p) <<< delta p)

private def isSortedMask (mask : Nat) : Bool :=
  (mask &&& 0x2efe) == 0

private def canSort : Nat → Nat → Bool
  | 0, mask => isSortedMask mask
  | r + 1, mask =>
    isSortedMask mask ||
    canSort r (stepMask .p01 mask) ||
    canSort r (stepMask .p02 mask) ||
    canSort r (stepMask .p03 mask) ||
    canSort r (stepMask .p12 mask) ||
    canSort r (stepMask .p13 mask) ||
    canSort r (stepMask .p23 mask)

private theorem canSort_of_isSorted : ∀ (r mask : Nat), isSortedMask mask = true → canSort r mask = true
  | 0, _, h => h
  | _ + 1, _, h => by simp [canSort, h]

private theorem canSort_step (p : Pair6) (r mask : Nat) (h : canSort r (stepMask p mask) = true) :
    canSort (r + 1) mask = true := by
  cases p <;> simp [canSort, h]

private theorem canSort_mono : ∀ (r mask : Nat), canSort r mask = true → canSort (r + 1) mask = true
  | 0, mask, h => canSort_of_isSorted 1 mask h
  | r + 1, mask, h => by
    unfold canSort at h
    simp only [Bool.or_eq_true] at h
    rcases h with (((((h | h) | h) | h) | h) | h) | h
    · exact canSort_of_isSorted (r + 2) mask h
    · exact canSort_step .p01 (r + 1) mask (canSort_mono r _ h)
    · exact canSort_step .p02 (r + 1) mask (canSort_mono r _ h)
    · exact canSort_step .p03 (r + 1) mask (canSort_mono r _ h)
    · exact canSort_step .p12 (r + 1) mask (canSort_mono r _ h)
    · exact canSort_step .p13 (r + 1) mask (canSort_mono r _ h)
    · exact canSort_step .p23 (r + 1) mask (canSort_mono r _ h)

private def enc (v : Fin 4 → Bool) : Nat :=
  (if v 0 then 1 else 0) +
  (if v 1 then 2 else 0) +
  (if v 2 then 4 else 0) +
  (if v 3 then 8 else 0)

private def dec (k : Nat) : Fin 4 → Bool :=
  fun i => Nat.testBit k i.val

private theorem enc_lt (v : Fin 4 → Bool) : enc v < 16 := by
  unfold enc
  cases v 0 <;> cases v 1 <;> cases v 2 <;> cases v 3 <;> decide

private theorem dec_enc (v : Fin 4 → Bool) : dec (enc v) = v := by
  funext i
  rcases i with ⟨idx, hidx⟩
  cases h0 : v 0 <;> cases h1 : v 1 <;> cases h2 : v 2 <;> cases h3 : v 3 <;>
    (match idx, hidx with
      | 0, _ => change Nat.testBit (enc v) 0 = v 0; simp only [enc, h0, h1, h2, h3]; decide
      | 1, _ => change Nat.testBit (enc v) 1 = v 1; simp only [enc, h0, h1, h2, h3]; decide
      | 2, _ => change Nat.testBit (enc v) 2 = v 2; simp only [enc, h0, h1, h2, h3]; decide
      | 3, _ => change Nat.testBit (enc v) 3 = v 3; simp only [enc, h0, h1, h2, h3]; decide
      | idx + 4, h => omega)

private theorem enc_dec : ∀ (k : Nat), k < 16 → enc (dec k) = k := by
  intro k hk
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
  | _ + 16 => omega

private theorem applyCompBool_same {n : Nat} (a : Fin n) (v : Fin n → Bool) :
    SortNet.applyCompBool (a, a) v = v := by
  funext k
  unfold SortNet.applyCompBool
  simp only [Nat.le_refl, ↓reduceIte]
  by_cases hk : k = a
  · subst hk; simp
  · simp [hk]

private theorem applyCompBool_symm {n : Nat} (a b : Fin n) (v : Fin n → Bool) :
    SortNet.applyCompBool (a, b) v = SortNet.applyCompBool (b, a) v := by
  funext k
  unfold SortNet.applyCompBool
  by_cases h1 : a.val ≤ b.val
  · by_cases h2 : b.val ≤ a.val
    · have hab : a = b := Fin.ext (Nat.le_antisymm h1 h2)
      subst hab; rfl
    · simp [h1, h2]
  · have h2 : b.val ≤ a.val := by omega
    simp [h1, h2]

private theorem classify_comp (c : Fin 4 × Fin 4) :
    (∀ v : Fin 4 → Bool, SortNet.applyCompBool c v = v) ∨
    (∃ p : Pair6, ∀ v : Fin 4 → Bool, SortNet.applyCompBool c v = SortNet.applyCompBool (toComp p) v) := by
  rcases c with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  by_cases heq : a = b
  · subst heq
    exact Or.inl (applyCompBool_same ⟨a, ha⟩)
  · right
    match a, ha, b, hb with
    | 0, _, 1, _ => exact ⟨.p01, fun _ => rfl⟩
    | 1, _, 0, _ => exact ⟨.p01, applyCompBool_symm _ _⟩
    | 0, _, 2, _ => exact ⟨.p02, fun _ => rfl⟩
    | 2, _, 0, _ => exact ⟨.p02, applyCompBool_symm _ _⟩
    | 0, _, 3, _ => exact ⟨.p03, fun _ => rfl⟩
    | 3, _, 0, _ => exact ⟨.p03, applyCompBool_symm _ _⟩
    | 1, _, 2, _ => exact ⟨.p12, fun _ => rfl⟩
    | 2, _, 1, _ => exact ⟨.p12, applyCompBool_symm _ _⟩
    | 1, _, 3, _ => exact ⟨.p13, fun _ => rfl⟩
    | 3, _, 1, _ => exact ⟨.p13, applyCompBool_symm _ _⟩
    | 2, _, 3, _ => exact ⟨.p23, fun _ => rfl⟩
    | 3, _, 2, _ => exact ⟨.p23, applyCompBool_symm _ _⟩
    | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ => exact absurd rfl heq
    | _ + 4, ha, _, _ => omega
    | _, _, _ + 4, hb => omega

private def checkFixed (p : Pair6) (k : Nat) : Bool :=
  !(Nat.testBit (notBadMask p) k) ||
  (enc (SortNet.applyCompBool (toComp p) (dec k)) == k)

private def checkSwapped (p : Pair6) (k : Nat) : Bool :=
  !(decide (delta p ≤ k) && Nat.testBit (badMask p) (k - delta p)) ||
  (enc (SortNet.applyCompBool (toComp p) (dec (k - delta p))) == k)

private theorem checkFixed_all : ∀ (p : Pair6) (k : Nat), k < 16 → checkFixed p k = true := by
  intro p k hk
  cases p <;>
    (match k with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
      | _ + 16 => omega)

private theorem checkSwapped_all : ∀ (p : Pair6) (k : Nat), k < 16 → checkSwapped p k = true := by
  intro p k hk
  cases p <;>
    (match k with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
      | _ + 16 => omega)

private theorem stepMask_preimage (p : Pair6) (mask : Nat) (w : Fin 4 → Bool)
    (h : Nat.testBit (stepMask p mask) (enc w) = true) :
    ∃ u : Fin 4 → Bool, Nat.testBit mask (enc u) = true ∧ SortNet.applyCompBool (toComp p) u = w := by
  unfold stepMask at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  have hlt : enc w < 16 := enc_lt w
  rcases h with h1 | h2
  · rw [Nat.testBit_and, Bool.and_eq_true] at h1
    refine ⟨w, h1.1, ?_⟩
    have hchk := checkFixed_all p (enc w) hlt
    simp only [checkFixed, h1.2, Bool.not_true, Bool.false_or, beq_iff_eq] at hchk
    rw [dec_enc] at hchk
    have hdec := congrArg dec hchk
    rwa [dec_enc, dec_enc] at hdec
  · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_and, Bool.and_eq_true] at h2
    have hm_lt : enc w - delta p < 16 := by omega
    refine ⟨dec (enc w - delta p), ?_, ?_⟩
    · rw [enc_dec _ hm_lt]; exact h2.2.1
    · have hchk := checkSwapped_all p (enc w) hlt
      simp only [checkSwapped, h2.1, decide_true, h2.2.2, Bool.and_true, Bool.not_true,
        Bool.false_or, beq_iff_eq] at hchk
      have hdec := congrArg dec hchk
      rwa [dec_enc, dec_enc] at hdec

private theorem unsorted_witness : ∀ (k : Nat), k < 16 → Nat.testBit 0x2efe k = true →
    ¬ SortNet.isSortedBool (dec k) := by
  intro k hk hbit hsort
  match k with
  | 1 => exact absurd (hsort ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)) (by decide)
  | 2 => exact absurd (hsort ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)) (by decide)
  | 3 => exact absurd (hsort ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)) (by decide)
  | 4 => exact absurd (hsort ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)) (by decide)
  | 5 => exact absurd (hsort ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)) (by decide)
  | 6 => exact absurd (hsort ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)) (by decide)
  | 7 => exact absurd (hsort ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)) (by decide)
  | 9 => exact absurd (hsort ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)) (by decide)
  | 10 => exact absurd (hsort ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)) (by decide)
  | 11 => exact absurd (hsort ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide)) (by decide)
  | 13 => exact absurd (hsort ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)) (by decide)
  | 0 | 8 | 12 | 14 | 15 => exact absurd hbit (by decide)
  | _ + 16 => omega

private theorem isSortedMask_of_sorted (mask : Nat)
    (h : ∀ v : Fin 4 → Bool, Nat.testBit mask (enc v) = true → SortNet.isSortedBool v) :
    isSortedMask mask = true := by
  unfold isSortedMask
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hk : k < 16
  · cases hbit : Nat.testBit 0x2efe k
    · simp
    · cases hm : Nat.testBit mask k
      · simp
      · exfalso
        have hsort := h (dec k) (by rwa [enc_dec k hk])
        exact unsorted_witness k hk hbit hsort
  · have hlt : 0x2efe < 2 ^ k :=
      Nat.lt_of_lt_of_le (by decide : 0x2efe < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (Nat.not_lt.1 hk))
    rw [Nat.testBit_lt_two_pow hlt, Bool.and_false]

private theorem canSort_of_sorts : ∀ (net : SortNet.Net 4) (r mask : Nat),
    net.length ≤ r →
    (∀ v : Fin 4 → Bool, Nat.testBit mask (enc v) = true → SortNet.isSortedBool (SortNet.evalBool net v)) →
    canSort r mask = true
  | [], r, mask, _, h =>
    canSort_of_isSorted r mask (isSortedMask_of_sorted mask h)
  | c :: rest, 0, _, hlen, _ => by
    simp at hlen
  | c :: rest, r + 1, mask, hlen, h => by
    have hlen' : rest.length ≤ r := by simpa using hlen
    rcases classify_comp c with hsame | ⟨p, hp⟩
    · apply canSort_mono r mask
      apply canSort_of_sorts rest r mask hlen'
      intro v hv
      have h1 := h v hv
      simpa [SortNet.evalBool, List.foldl_cons, hsame v] using h1
    · apply canSort_step p r mask
      apply canSort_of_sorts rest r (stepMask p mask) hlen'
      intro w hw
      rcases stepMask_preimage p mask w hw with ⟨u, hu, huw⟩
      have h1 := h u hu
      simpa [SortNet.evalBool, List.foldl_cons, hp u, huw] using h1

private theorem canSort_four_false : canSort 4 0xFFFF = false := by
  decide +kernel

theorem four_wire_needs_five : SortNet.Statements.SN_003.Claim := by
  intro net hlen hsorter
  have htrue : canSort 4 0xFFFF = true :=
    canSort_of_sorts net 4 0xFFFF hlen (fun v _ => hsorter v)
  rw [canSort_four_false] at htrue
  exact Bool.noConfusion htrue

end SortNet.Claims.SN_003
