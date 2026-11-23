import PnP.Core

namespace PnP.Lemmas.L_lib_003
open PnP

private theorem pow_mono (n a b : Nat) (h : a ≤ b) : (n + 1) ^ a ≤ (n + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos n) h

theorem polyBounded_add_mul {f g : Nat → Nat} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) ∧ PolyBounded (fun n => f n * g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  constructor
  · refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
    have a1 := h1 n
    have a2 := h2 n
    have b1 := pow_mono n k1 (max k1 k2) (Nat.le_max_left _ _)
    have b2 := pow_mono n k2 (max k1 k2) (Nat.le_max_right _ _)
    have m1 := Nat.mul_le_mul_left c1 b1
    have m2 := Nat.mul_le_mul_left c2 b2
    simp only [Nat.add_mul]
    omega
  · refine ⟨4 * c1 * c2, k1 + k2, fun n => ?_⟩
    have a1 := h1 n
    have a2 := h2 n
    have hAP : (n + 1) ^ k1 ≤ (n + 1) ^ (k1 + k2) := pow_mono n k1 _ (Nat.le_add_right _ _)
    have hBP : (n + 1) ^ k2 ≤ (n + 1) ^ (k1 + k2) := pow_mono n k2 _ (Nat.le_add_left _ _)
    have hP1 : 1 ≤ (n + 1) ^ (k1 + k2) := Nat.one_le_pow _ _ (Nat.succ_pos n)
    have hAB : (n + 1) ^ k1 * (n + 1) ^ k2 = (n + 1) ^ (k1 + k2) := by rw [← Nat.pow_add]
    generalize (n + 1) ^ k1 = A at *
    generalize (n + 1) ^ k2 = B at *
    generalize (n + 1) ^ (k1 + k2) = P at *
    have step : f n * g n ≤ (c1 * A + c1) * (c2 * B + c2) := Nat.mul_le_mul a1 a2
    have expand : (c1 * A + c1) * (c2 * B + c2)
        = c1 * c2 * (A * B + A + B + 1) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      omega
    have hsum : A * B + A + B + 1 ≤ 4 * P := by omega
    have : c1 * c2 * (A * B + A + B + 1) ≤ c1 * c2 * (4 * P) := Nat.mul_le_mul_left _ hsum
    have e2 : c1 * c2 * (4 * P) = 4 * c1 * c2 * P := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    show f n * g n ≤ 4 * c1 * c2 * P + 4 * c1 * c2
    omega

end PnP.Lemmas.L_lib_003
