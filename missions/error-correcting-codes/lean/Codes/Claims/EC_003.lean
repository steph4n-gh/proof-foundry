import Codes.Core
import Codes.Statements.EC_003

namespace Codes.Claims.EC_003

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem mod_two_eq_ite_testBit (x : Nat) :
    x % 2 = if x.testBit 0 then 1 else 0 := by
  simp only [Nat.testBit_zero]
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h => simp [h]
  | inr h => simp [h]

private theorem xor_mod_two (a b : Nat) :
    (a ^^^ b) % 2 = if a % 2 = b % 2 then 0 else 1 := by
  rw [mod_two_eq_ite_testBit (a ^^^ b), mod_two_eq_ite_testBit a, mod_two_eq_ite_testBit b,
    Nat.testBit_xor]
  cases a.testBit 0 <;> cases b.testBit 0 <;> decide

private def countPar (p : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x % 2 = p then 1 else 0) + countPar p xs

private theorem countPar_add : ∀ (L : List Nat), countPar 0 L + countPar 1 L = L.length
  | [] => rfl
  | x :: xs => by
    have ih := countPar_add xs
    simp only [countPar, List.length_cons]
    cases Nat.mod_two_eq_zero_or_one x with
    | inl h => simp [h]; omega
    | inr h => simp [h]; omega

private def sumBit0One (a : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => (a ^^^ b) % 2 + sumBit0One a bs

private theorem sumBit0One_eq (a : Nat) : ∀ (L : List Nat),
    sumBit0One a L = if a % 2 = 0 then countPar 1 L else countPar 0 L
  | [] => by simp [sumBit0One, countPar]
  | b :: bs => by
    have ih := sumBit0One_eq a bs
    simp only [sumBit0One, countPar, xor_mod_two, ih]
    cases Nat.mod_two_eq_zero_or_one a with
    | inl ha =>
      cases Nat.mod_two_eq_zero_or_one b with
      | inl hb => simp [ha, hb]
      | inr hb => simp [ha, hb]
    | inr ha =>
      cases Nat.mod_two_eq_zero_or_one b with
      | inl hb => simp [ha, hb]
      | inr hb => simp [ha, hb]

private def sumBit0Go (L : List Nat) : List Nat → Nat
  | [] => 0
  | a :: as => sumBit0One a L + sumBit0Go L as

private theorem sumBit0Go_eq (L : List Nat) : ∀ (A : List Nat),
    sumBit0Go L A = countPar 0 A * countPar 1 L + countPar 1 A * countPar 0 L
  | [] => by simp [sumBit0Go, countPar]
  | a :: as => by
    have ih := sumBit0Go_eq L as
    simp only [sumBit0Go, countPar, sumBit0One_eq, ih]
    cases Nat.mod_two_eq_zero_or_one a with
    | inl ha =>
      simp only [ha, ↓reduceIte, Nat.add_mul, Nat.one_mul]
      have hne : (0 : Nat) ≠ 1 := by decide
      simp only [hne, ↓reduceIte]
      omega
    | inr ha =>
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [ha, hne, ↓reduceIte, Nat.add_mul, Nat.one_mul, Nat.zero_add]
      omega

private theorem four_mul_le_sq_add (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : (a + (a + t)) * (a + (a + t)) = 4 * (a * (a + t)) + t * t := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm t a]
      omega
    omega
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 : ((b + t) + b) * ((b + t) + b) = 4 * ((b + t) * b) + t * t := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm t b]
      omega
    omega

private theorem two_mul_sumBit0 (L : List Nat) :
    2 * sumBit0Go L L ≤ L.length * L.length := by
  rw [sumBit0Go_eq L L, ← countPar_add L]
  have hcomm : countPar 1 L * countPar 0 L = countPar 0 L * countPar 1 L := Nat.mul_comm _ _
  have h4 := four_mul_le_sq_add (countPar 0 L) (countPar 1 L)
  omega

private def sumPopOne (k a : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => Codes.popCountAux k (a ^^^ b) + sumPopOne k a bs

private def sumPopGo (k : Nat) (L : List Nat) : List Nat → Nat
  | [] => 0
  | a :: as => sumPopOne k a L + sumPopGo k L as

private theorem sumPopOne_succ (k a : Nat) : ∀ (L : List Nat),
    sumPopOne (k + 1) a L = sumBit0One a L + sumPopOne k (a / 2) (L.map (· / 2))
  | [] => rfl
  | b :: bs => by
    have ih := sumPopOne_succ k a bs
    simp only [sumPopOne, sumBit0One, List.map_cons, Codes.popCountAux, xor_div_two, ih]
    omega

private theorem sumPopGo_succ (k : Nat) (L : List Nat) : ∀ (A : List Nat),
    sumPopGo (k + 1) L A = sumBit0Go L A + sumPopGo k (L.map (· / 2)) (A.map (· / 2))
  | [] => rfl
  | a :: as => by
    have ih := sumPopGo_succ k L as
    simp only [sumPopGo, sumBit0Go, List.map_cons, sumPopOne_succ, ih]
    omega

private theorem sumPopGo_zero (L : List Nat) : ∀ (A : List Nat), sumPopGo 0 L A = 0
  | [] => rfl
  | a :: as => by
    have h1 : ∀ (B : List Nat), sumPopOne 0 a B = 0 := by
      intro B
      induction B with
      | nil => rfl
      | cons b bs ih => simp [sumPopOne, Codes.popCountAux, ih]
    simp [sumPopGo, h1, sumPopGo_zero L as]

private theorem two_mul_sumPopGo_le : ∀ (k : Nat) (L : List Nat),
    2 * sumPopGo k L L ≤ k * (L.length * L.length)
  | 0, L => by simp [sumPopGo_zero]
  | k + 1, L => by
    rw [sumPopGo_succ]
    have hbit := two_mul_sumBit0 L
    have ih := two_mul_sumPopGo_le k (L.map (· / 2))
    rw [List.length_map] at ih
    have hmul : (k + 1) * (L.length * L.length) = L.length * L.length + k * (L.length * L.length) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    omega

private theorem sumPopOne_ge_of_not_mem {n d : Nat} (u : BitVec n) :
    ∀ {D : List (BitVec n)},
      u ∉ D →
      (∀ v ∈ D, u ≠ v → d ≤ Codes.hammingDist u v) →
      D.length * d ≤ sumPopOne n u.toNat (D.map BitVec.toNat)
  | [], _, _ => by simp [sumPopOne]
  | v :: vs, hnot, hdist => by
    have huv : u ≠ v := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hnot' : u ∉ vs := fun h => hnot (List.mem_cons_of_mem v h)
    have hd : d ≤ Codes.popCountAux n (u.toNat ^^^ v.toNat) := by
      have h := hdist v (List.mem_cons_self ..) huv
      unfold Codes.hammingDist Codes.hammingWeight at h
      rwa [BitVec.toNat_xor] at h
    have ih := sumPopOne_ge_of_not_mem u hnot' (fun w hw => hdist w (List.mem_cons_of_mem v hw))
    simp only [List.map_cons, sumPopOne, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem sumPopOne_ge_of_mem {n d : Nat} (u : BitVec n) :
    ∀ {D : List (BitVec n)},
      D.Nodup → u ∈ D →
      (∀ v ∈ D, u ≠ v → d ≤ Codes.hammingDist u v) →
      (D.length - 1) * d ≤ sumPopOne n u.toNat (D.map BitVec.toNat)
  | [], _, hmem, _ => absurd hmem List.not_mem_nil
  | v :: vs, hnd, hmem, hdist => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, sumPopOne, List.length_cons, Nat.add_sub_cancel]
    by_cases huv : u = v
    · subst huv
      have ih := sumPopOne_ge_of_not_mem u hnd.1 (fun w hw => hdist w (List.mem_cons_of_mem u hw))
      omega
    · have hmem' : u ∈ vs := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd rfl huv
        · exact h
      have hpos : 0 < vs.length := List.length_pos_of_mem hmem'
      have hd : d ≤ Codes.popCountAux n (u.toNat ^^^ v.toNat) := by
        have h := hdist v (List.mem_cons_self ..) huv
        unfold Codes.hammingDist Codes.hammingWeight at h
        rwa [BitVec.toNat_xor] at h
      have ih := sumPopOne_ge_of_mem u hnd.2 hmem' (fun w hw => hdist w (List.mem_cons_of_mem v hw))
      have hmul : vs.length * d = (vs.length - 1) * d + d := by
        calc vs.length * d = ((vs.length - 1) + 1) * d := by rw [Nat.sub_add_cancel hpos]
          _ = (vs.length - 1) * d + d := by rw [Nat.add_mul, Nat.one_mul]
      omega

private theorem sumPopGo_ge {n d : Nat} {C : List (BitVec n)} (hcode : Codes.IsBinaryCode n d C) :
    ∀ {A : List (BitVec n)}, (∀ u ∈ A, u ∈ C) →
      A.length * ((C.length - 1) * d) ≤ sumPopGo n (C.map BitVec.toNat) (A.map BitVec.toNat)
  | [], _ => by simp [sumPopGo]
  | u :: us, hsub => by
    have huC : u ∈ C := hsub u (List.mem_cons_self ..)
    have h1 := sumPopOne_ge_of_mem u hcode.1 huC (fun v hv huv => hcode.2 u huC v hv huv)
    have ih := sumPopGo_ge hcode (fun w hw => hsub w (List.mem_cons_of_mem u hw))
    simp only [List.map_cons, sumPopGo, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem plotkin_bound : Codes.Statements.EC_003.Claim := by
  intro n d C hlt hcode
  by_cases hM : C.length = 0
  · simp [hM]
  · have hMpos : 0 < C.length := Nat.pos_of_ne_zero hM
    have hlo := sumPopGo_ge hcode (A := C) (fun _ hu => hu)
    have hhi := two_mul_sumPopGo_le n (C.map BitVec.toNat)
    rw [List.length_map] at hhi
    have hchain : 2 * (C.length * ((C.length - 1) * d)) ≤ n * (C.length * C.length) := by omega
    have hleft : 2 * (C.length * ((C.length - 1) * d)) = C.length * ((C.length - 1) * (2 * d)) := by
      rw [Nat.mul_left_comm, Nat.mul_left_comm 2 (C.length - 1) d]
    have hright : n * (C.length * C.length) = C.length * (C.length * n) := by
      rw [Nat.mul_comm n (C.length * C.length), Nat.mul_assoc]
    rw [hleft, hright] at hchain
    have hcancel : (C.length - 1) * (2 * d) ≤ C.length * n :=
      Nat.le_of_mul_le_mul_left hchain hMpos
    have hsplit1 : C.length * (2 * d - n) + C.length * n = C.length * (2 * d) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    have hsplit2 : C.length * (2 * d) = (C.length - 1) * (2 * d) + 2 * d := by
      calc C.length * (2 * d) = ((C.length - 1) + 1) * (2 * d) := by rw [Nat.sub_add_cancel hMpos]
        _ = (C.length - 1) * (2 * d) + 2 * d := by rw [Nat.add_mul, Nat.one_mul]
    omega

end Codes.Claims.EC_003
