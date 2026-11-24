import Codes.Statements.EC_002

namespace Codes.Claims.EC_002

private theorem not_mem_erase_of_nodup {a : Nat} : ∀ {L : List Nat}, L.Nodup → a ∉ L.erase a
  | [], _ => by simp
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    by_cases hxa : x = a
    · subst hxa; simp [hnd.1]
    · have hbeq : (x == a) = false := beq_false_of_ne hxa
      simp [hbeq, Ne.symm hxa, not_mem_erase_of_nodup hnd.2]

private theorem nodup_length_le : ∀ (M : Nat) (L : List Nat),
    L.Nodup → (∀ x ∈ L, x < M) → L.length ≤ M
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => absurd (hlt x (List.mem_cons_self ..)) (Nat.not_lt_zero x)
  | M + 1, L, hnd, hlt => by
    have hsub : (L.erase M).Sublist L := List.erase_sublist
    have hnd' : (L.erase M).Nodup := hnd.sublist hsub
    have hlt' : ∀ x ∈ L.erase M, x < M := by
      intro x hx
      have hxL : x ∈ L := hsub.subset hx
      have hle : x ≤ M := Nat.lt_succ_iff.mp (hlt x hxL)
      have hne : x ≠ M := by
        intro hEq
        subst hEq
        exact not_mem_erase_of_nodup hnd hx
      exact Nat.lt_of_le_of_ne hle hne
    have hIH : (L.erase M).length ≤ M := nodup_length_le M (L.erase M) hnd' hlt'
    have hlen : L.length ≤ (L.erase M).length + 1 := by
      by_cases hM : M ∈ L
      · have := List.length_erase_of_mem hM
        omega
      · rw [List.erase_of_not_mem hM]
        omega
    omega

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem xor_mod_two_le (a b : Nat) : (a ^^^ b) % 2 ≤ a % 2 + b % 2 := by
  have h1 : ∀ x : Nat, x % 2 = if x.testBit 0 then 1 else 0 := by
    intro x
    simp [Nat.testBit_zero]
    cases Nat.mod_two_eq_zero_or_one x with
    | inl h => simp [h]
    | inr h => simp [h]
  rw [h1 (a ^^^ b), h1 a, h1 b, Nat.testBit_xor]
  cases a.testBit 0 <;> cases b.testBit 0 <;> decide

private theorem popCountAux_xor_le : ∀ (k a b : Nat),
    Codes.popCountAux k (a ^^^ b) ≤ Codes.popCountAux k a + Codes.popCountAux k b
  | 0, _, _ => Nat.le_refl 0
  | k + 1, a, b => by
    simp only [Codes.popCountAux]
    rw [xor_div_two]
    have h0 := xor_mod_two_le a b
    have h1 := popCountAux_xor_le k (a / 2) (b / 2)
    omega

private theorem hammingDist_triangle {n : Nat} (u w v : BitVec n) :
    Codes.hammingDist u v ≤ Codes.hammingDist u w + Codes.hammingDist w v := by
  unfold Codes.hammingDist Codes.hammingWeight
  have hxor : u ^^^ v = (u ^^^ w) ^^^ (w ^^^ v) := by
    rw [BitVec.xor_assoc, ← BitVec.xor_assoc w w v, BitVec.xor_self, BitVec.zero_xor]
  rw [hxor, BitVec.toNat_xor]
  exact popCountAux_xor_le n (u ^^^ w).toNat (w ^^^ v).toNat

private theorem popCountAux_two_pow : ∀ (n i : Nat), i < n →
    Codes.popCountAux n (2 ^ i) = 1
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, 0, _ => by
    simp [Codes.popCountAux, Codes.popCountAux_zero]
  | n + 1, i + 1, hi => by
    simp only [Codes.popCountAux, Nat.pow_succ]
    have hmod : (2 ^ i * 2) % 2 = 0 := by omega
    have hdiv : (2 ^ i * 2) / 2 = 2 ^ i := by omega
    rw [hmod, hdiv, Nat.zero_add]
    exact popCountAux_two_pow n i (Nat.lt_of_succ_lt_succ hi)

private theorem two_pow_lt {n i : Nat} (hi : i < n) : 2 ^ i < 2 ^ n :=
  Nat.pow_lt_pow_right (by decide) hi

private theorem two_pow_inj : ∀ {i j : Nat}, 2 ^ i = 2 ^ j → i = j
  | 0, 0, _ => rfl
  | 0, j + 1, h => by
    have : 1 < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by decide) (Nat.succ_pos j)
    omega
  | i + 1, 0, h => by
    have : 1 < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by decide) (Nat.succ_pos i)
    omega
  | i + 1, j + 1, h => by
    have h' : 2 ^ i * 2 = 2 ^ j * 2 := by simpa [Nat.pow_succ] using h
    have hij : 2 ^ i = 2 ^ j := by omega
    exact congrArg Nat.succ (two_pow_inj hij)

private def unitVec (n : Nat) (i : Fin n) : BitVec n :=
  BitVec.ofNat n (2 ^ i.val)

private theorem unitVec_toNat (n : Nat) (i : Fin n) :
    (unitVec n i).toNat = 2 ^ i.val := by
  unfold unitVec
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (two_pow_lt i.isLt)

private theorem unitVec_weight (n : Nat) (i : Fin n) :
    Codes.hammingWeight (unitVec n i) = 1 := by
  unfold Codes.hammingWeight
  rw [unitVec_toNat]
  exact popCountAux_two_pow n i.val i.isLt

private def ball (n : Nat) (c : BitVec n) : List (BitVec n) :=
  c :: (List.finRange n).map (fun i => c ^^^ unitVec n i)

private theorem ball_length (n : Nat) (c : BitVec n) :
    (ball n c).length = n + 1 := by
  simp [ball]

private theorem ball_dist_le_one {n : Nat} {c x : BitVec n} (hx : x ∈ ball n c) :
    Codes.hammingDist c x ≤ 1 := by
  unfold ball at hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · rw [Codes.hammingDist_self]
    exact Nat.zero_le 1
  · rcases List.mem_map.mp hx' with ⟨i, _, rfl⟩
    unfold Codes.hammingDist
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, unitVec_weight]
    exact Nat.le_refl 1

private theorem ball_nodup (n : Nat) (c : BitVec n) : (ball n c).Nodup := by
  unfold ball
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨i, _, hi⟩
    have h0 : unitVec n i = 0#n := by
      have h1 : c ^^^ (c ^^^ unitVec n i) = c ^^^ c := congrArg (c ^^^ ·) hi
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] at h1
      exact h1
    have hw1 := unitVec_weight n i
    rw [h0] at hw1
    unfold Codes.hammingWeight at hw1
    simp [Codes.popCountAux_zero] at hw1
  · exact List.Pairwise.map (fun i => c ^^^ unitVec n i) (fun i j hij hEq => hij (by
      have h1 : c ^^^ (c ^^^ unitVec n i) = c ^^^ (c ^^^ unitVec n j) :=
        congrArg (c ^^^ ·) hEq
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.zero_xor] at h1
      have h2 : (unitVec n i).toNat = (unitVec n j).toNat := congrArg BitVec.toNat h1
      rw [unitVec_toNat, unitVec_toNat] at h2
      exact Fin.ext (two_pow_inj h2))) (List.nodup_finRange n)

private theorem ball_disjoint {n : Nat} {c1 c2 : BitVec n}
    (hdist : 3 ≤ Codes.hammingDist c1 c2) :
    ∀ x ∈ ball n c1, x ∉ ball n c2 := by
  intro x hx1 hx2
  have h1 := ball_dist_le_one hx1
  have h2 := ball_dist_le_one hx2
  have htri := hammingDist_triangle c1 x c2
  rw [Codes.hammingDist_comm x c2] at htri
  omega

private theorem flatMap_ball_length (n : Nat) : ∀ (C : List (BitVec n)),
    (C.flatMap (ball n)).length = C.length * (n + 1)
  | [] => by simp
  | c :: cs => by
    simp [List.flatMap_cons, ball_length, flatMap_ball_length n cs, Nat.succ_mul, Nat.add_comm]

private theorem flatMap_ball_nodup {n : Nat} : ∀ {C : List (BitVec n)},
    Codes.IsBinaryCode n 3 C → (C.flatMap (ball n)).Nodup
  | [], _ => by simp
  | c :: cs, ⟨hnd, hdist⟩ => by
    rw [List.nodup_cons] at hnd
    have hcs : Codes.IsBinaryCode n 3 cs := by
      refine ⟨hnd.2, ?_⟩
      intro u hu v hv huv
      exact hdist u (List.mem_cons_of_mem c hu) v (List.mem_cons_of_mem c hv) huv
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨ball_nodup n c, flatMap_ball_nodup hcs, ?_⟩
    intro x hx1 y hy2 heq
    subst heq
    rcases List.mem_flatMap.mp hy2 with ⟨c', hc', hxc'⟩
    have hne : c ≠ c' := fun h => hnd.1 (h ▸ hc')
    have hd3 : 3 ≤ Codes.hammingDist c c' :=
      hdist c (List.mem_cons_self ..) c' (List.mem_cons_of_mem c hc') hne
    exact ball_disjoint hd3 x hx1 hxc'

theorem sphere_packing_bound : Codes.Statements.EC_002.Claim := by
  intro n C hcode
  let B := C.flatMap (ball n)
  have hBnd : B.Nodup := flatMap_ball_nodup hcode
  have hBlen : B.length = C.length * (n + 1) := flatMap_ball_length n C
  let L := B.map BitVec.toNat
  have hLnd : L.Nodup :=
    List.Pairwise.map BitVec.toNat (fun _ _ hne heq => hne (BitVec.eq_of_toNat_eq heq)) hBnd
  have hLlt : ∀ x ∈ L, x < 2 ^ n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
    exact v.isLt
  have hle : L.length ≤ 2 ^ n := nodup_length_le (2 ^ n) L hLnd hLlt
  simpa [L, hBlen] using hle

end Codes.Claims.EC_002
