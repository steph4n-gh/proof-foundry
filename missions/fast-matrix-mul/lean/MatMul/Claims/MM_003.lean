import MatMul.Statements.MM_003

namespace MatMul.Claims.MM_003

private def naiveCoeff {m n p : Nat} (s : MatMul.SchemeInt m n p)
    (a : Fin (m * n)) (b : Fin (n * p)) (c : Fin (m * p)) : Int :=
  match s with
  | [] => 0
  | t :: ts => t.left a * t.right b * t.output c + naiveCoeff ts a b c

private theorem foldl_add_shift {α : Type} (f : α → Int) :
    ∀ (l : List α) (init : Int),
      l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, Int.zero_add]
    rw [foldl_add_shift f xs (init + f x), foldl_add_shift f xs (f x), Int.add_assoc]

private theorem coeffInt_eq_naiveCoeff {m n p : Nat} (s : MatMul.SchemeInt m n p)
    (a : Fin (m * n)) (b : Fin (n * p)) (c : Fin (m * p)) :
    MatMul.coeffInt s a b c = naiveCoeff s a b c := by
  induction s with
  | nil => rfl
  | cons t ts ih =>
    unfold MatMul.coeffInt at ih ⊢
    simp only [List.filterMap_cons, naiveCoeff]
    cases hk : (t.left a * t.right b == 0) with
    | true =>
      have hk0 : t.left a * t.right b = 0 := beq_iff_eq.mp hk
      simp only [↓reduceIte, hk0, Int.zero_mul, Int.zero_add]
      exact ih
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_cons, Int.zero_add]
      rw [foldl_add_shift (fun (x : Int × (Fin (m * p) → Int)) => x.1 * x.2 c)]
      exact congrArg (t.left a * t.right b * t.output c + ·) ih

private theorem naiveCoeff_append {m n p : Nat} (s₁ s₂ : MatMul.SchemeInt m n p)
    (a : Fin (m * n)) (b : Fin (n * p)) (c : Fin (m * p)) :
    naiveCoeff (s₁ ++ s₂) a b c = naiveCoeff s₁ a b c + naiveCoeff s₂ a b c := by
  induction s₁ with
  | nil => simp [naiveCoeff]
  | cons t ts ih =>
    simp [naiveCoeff, ih, Int.add_assoc]

private theorem div_lt_of_lt_mul {x a b : Nat} (h : x < a * b) : x / b < a :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])

private theorem pair_lt_mul {x y a b : Nat} (hx : x < a) (hy : y < b) :
    x * b + y < a * b := by
  have h1 : (x + 1) * b ≤ a * b := Nat.mul_le_mul_right b hx
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

private def split₁ {M₁ M₂ N₁ N₂ : Nat} (hM₂ : 0 < M₂) (hN₂ : 0 < N₂)
    (idx : Fin ((M₁ * M₂) * (N₁ * N₂))) : Fin (M₁ * N₁) :=
  let I := idx.val / (N₁ * N₂)
  let J := idx.val % (N₁ * N₂)
  have hI : I < M₁ * M₂ := div_lt_of_lt_mul idx.isLt
  have hN12 : 0 < N₁ * N₂ :=
    Nat.pos_of_ne_zero fun heq => by
      have h0 : M₁ * M₂ * (N₁ * N₂) = 0 := by rw [heq, Nat.mul_zero]
      have hlt : idx.val < 0 := h0 ▸ idx.isLt
      exact Nat.not_lt_zero _ hlt
  have hJ : J < N₁ * N₂ := Nat.mod_lt _ hN12
  ⟨(I / M₂) * N₁ + (J / N₂), pair_lt_mul (div_lt_of_lt_mul hI) (div_lt_of_lt_mul hJ)⟩

private def split₂ {M₁ M₂ N₁ N₂ : Nat} (hM₂ : 0 < M₂) (hN₂ : 0 < N₂)
    (idx : Fin ((M₁ * M₂) * (N₁ * N₂))) : Fin (M₂ * N₂) :=
  let I := idx.val / (N₁ * N₂)
  let J := idx.val % (N₁ * N₂)
  ⟨(I % M₂) * N₂ + (J % N₂), pair_lt_mul (Nat.mod_lt I hM₂) (Nat.mod_lt J hN₂)⟩

private theorem div_mod_eq_iff {x y : Nat} (d : Nat) :
    x = y ↔ x / d = y / d ∧ x % d = y % d := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    have hx := Nat.div_add_mod x d
    have hy := Nat.div_add_mod y d
    rw [← hx, ← hy, h1, h2]

private theorem pair_div {q r d : Nat} (hr : r < d) : (q * d + r) / d = q := by
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le r) hr),
    Nat.div_eq_of_lt hr, Nat.add_zero]

private theorem pair_mod {q r d : Nat} (hr : r < d) : (q * d + r) % d = r := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

private theorem contributes_iff {m n p : Nat} (hp : 0 < p)
    (a : Fin (m * n)) (b : Fin (n * p)) (c : Fin (m * p)) :
    MatMul.contributes a b c = true ↔
      a.val % n = b.val / p ∧ c.val / p = a.val / n ∧ c.val % p = b.val % p := by
  unfold MatMul.contributes
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [h2]; exact pair_div (Nat.mod_lt b.val hp)
    · rw [h2]; exact pair_mod (Nat.mod_lt b.val hp)
  · intro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    have hc := Nat.div_add_mod c.val p
    rw [h2, h3, Nat.mul_comm] at hc
    omega

private theorem contributes_tensor {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (a : Fin ((m₁ * m₂) * (n₁ * n₂)))
    (b : Fin ((n₁ * n₂) * (p₁ * p₂)))
    (c : Fin ((m₁ * m₂) * (p₁ * p₂))) :
    MatMul.contributes a b c =
      (MatMul.contributes (split₁ hm₂ hn₂ a) (split₁ hn₂ hp₂ b) (split₁ hm₂ hp₂ c) &&
       MatMul.contributes (split₂ hm₂ hn₂ a) (split₂ hn₂ hp₂ b) (split₂ hm₂ hp₂ c)) := by
  have hp12 : 0 < p₁ * p₂ := Nat.mul_pos hp₁ hp₂
  have hn12 : 0 < n₁ * n₂ := Nat.mul_pos hn₁ hn₂
  have haJ : a.val % (n₁ * n₂) / n₂ < n₁ := div_lt_of_lt_mul (Nat.mod_lt a.val hn12)
  have hbL : b.val % (p₁ * p₂) / p₂ < p₁ := div_lt_of_lt_mul (Nat.mod_lt b.val hp12)
  have hcL : c.val % (p₁ * p₂) / p₂ < p₁ := div_lt_of_lt_mul (Nat.mod_lt c.val hp12)
  have ha1_div : (split₁ hm₂ hn₂ a).val / n₁ = a.val / (n₁ * n₂) / m₂ := by unfold split₁; exact pair_div haJ
  have ha1_mod : (split₁ hm₂ hn₂ a).val % n₁ = a.val % (n₁ * n₂) / n₂ := by unfold split₁; exact pair_mod haJ
  have hb1_div : (split₁ hn₂ hp₂ b).val / p₁ = b.val / (p₁ * p₂) / n₂ := by unfold split₁; exact pair_div hbL
  have hb1_mod : (split₁ hn₂ hp₂ b).val % p₁ = b.val % (p₁ * p₂) / p₂ := by unfold split₁; exact pair_mod hbL
  have hc1_div : (split₁ hm₂ hp₂ c).val / p₁ = c.val / (p₁ * p₂) / m₂ := by unfold split₁; exact pair_div hcL
  have hc1_mod : (split₁ hm₂ hp₂ c).val % p₁ = c.val % (p₁ * p₂) / p₂ := by unfold split₁; exact pair_mod hcL
  have ha2_div : (split₂ hm₂ hn₂ a).val / n₂ = a.val / (n₁ * n₂) % m₂ := by unfold split₂; exact pair_div (Nat.mod_lt _ hn₂)
  have ha2_mod : (split₂ hm₂ hn₂ a).val % n₂ = a.val % (n₁ * n₂) % n₂ := by unfold split₂; exact pair_mod (Nat.mod_lt _ hn₂)
  have hb2_div : (split₂ hn₂ hp₂ b).val / p₂ = b.val / (p₁ * p₂) % n₂ := by unfold split₂; exact pair_div (Nat.mod_lt _ hp₂)
  have hb2_mod : (split₂ hn₂ hp₂ b).val % p₂ = b.val % (p₁ * p₂) % p₂ := by unfold split₂; exact pair_mod (Nat.mod_lt _ hp₂)
  have hc2_div : (split₂ hm₂ hp₂ c).val / p₂ = c.val / (p₁ * p₂) % m₂ := by unfold split₂; exact pair_div (Nat.mod_lt _ hp₂)
  have hc2_mod : (split₂ hm₂ hp₂ c).val % p₂ = c.val % (p₁ * p₂) % p₂ := by unfold split₂; exact pair_mod (Nat.mod_lt _ hp₂)
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, contributes_iff hp12, contributes_iff hp₁, contributes_iff hp₂]
  rw [ha1_div, ha1_mod, hb1_div, hb1_mod, hc1_div, hc1_mod]
  rw [ha2_div, ha2_mod, hb2_div, hb2_mod, hc2_div, hc2_mod]
  constructor
  · intro ⟨h1, h2, h3⟩
    have ⟨h1a, h1b⟩ := (div_mod_eq_iff n₂).mp h1
    have ⟨h2a, h2b⟩ := (div_mod_eq_iff m₂).mp h2
    have ⟨h3a, h3b⟩ := (div_mod_eq_iff p₂).mp h3
    exact ⟨⟨h1a, h2a, h3a⟩, ⟨h1b, h2b, h3b⟩⟩
  · intro ⟨⟨h1a, h2a, h3a⟩, ⟨h1b, h2b, h3b⟩⟩
    exact ⟨(div_mod_eq_iff n₂).mpr ⟨h1a, h1b⟩,
           (div_mod_eq_iff m₂).mpr ⟨h2a, h2b⟩,
           (div_mod_eq_iff p₂).mpr ⟨h3a, h3b⟩⟩

private def tensorTerm {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₂ : 0 < n₂) (hp₂ : 0 < p₂)
    (t₁ : MatMul.Term Int m₁ n₁ p₁) (t₂ : MatMul.Term Int m₂ n₂ p₂) :
    MatMul.Term Int (m₁ * m₂) (n₁ * n₂) (p₁ * p₂) where
  left := fun a => t₁.left (split₁ hm₂ hn₂ a) * t₂.left (split₂ hm₂ hn₂ a)
  right := fun b => t₁.right (split₁ hn₂ hp₂ b) * t₂.right (split₂ hn₂ hp₂ b)
  output := fun c => t₁.output (split₁ hm₂ hp₂ c) * t₂.output (split₂ hm₂ hp₂ c)

private def tensorScheme {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₂ : 0 < n₂) (hp₂ : 0 < p₂)
    (s₁ : MatMul.SchemeInt m₁ n₁ p₁) (s₂ : MatMul.SchemeInt m₂ n₂ p₂) :
    MatMul.SchemeInt (m₁ * m₂) (n₁ * n₂) (p₁ * p₂) :=
  s₁.flatMap fun t₁ => s₂.map fun t₂ => tensorTerm hm₂ hn₂ hp₂ t₁ t₂

private theorem tensorScheme_length {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₂ : 0 < n₂) (hp₂ : 0 < p₂)
    (s₁ : MatMul.SchemeInt m₁ n₁ p₁) (s₂ : MatMul.SchemeInt m₂ n₂ p₂) :
    (tensorScheme hm₂ hn₂ hp₂ s₁ s₂).length = s₁.length * s₂.length := by
  unfold tensorScheme
  induction s₁ with
  | nil => simp
  | cons t₁ ts₁ ih =>
    simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

private theorem int_prod_shuffle (a₁ a₂ b₁ b₂ c₁ c₂ : Int) :
    a₁ * a₂ * (b₁ * b₂) * (c₁ * c₂) = (a₁ * b₁ * c₁) * (a₂ * b₂ * c₂) := by
  rw [Int.mul_assoc a₁ a₂ (b₁ * b₂)]
  rw [← Int.mul_assoc a₂ b₁ b₂, Int.mul_comm a₂ b₁, Int.mul_assoc b₁ a₂ b₂]
  rw [← Int.mul_assoc a₁ b₁ (a₂ * b₂)]
  rw [Int.mul_assoc (a₁ * b₁) (a₂ * b₂) (c₁ * c₂)]
  rw [← Int.mul_assoc (a₂ * b₂) c₁ c₂, Int.mul_comm (a₂ * b₂) c₁, Int.mul_assoc c₁ (a₂ * b₂) c₂]
  rw [← Int.mul_assoc (a₁ * b₁) c₁ (a₂ * b₂ * c₂)]

private theorem naiveCoeff_map_tensor {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₂ : 0 < n₂) (hp₂ : 0 < p₂)
    (t₁ : MatMul.Term Int m₁ n₁ p₁) (s₂ : MatMul.SchemeInt m₂ n₂ p₂)
    (a : Fin ((m₁ * m₂) * (n₁ * n₂)))
    (b : Fin ((n₁ * n₂) * (p₁ * p₂)))
    (c : Fin ((m₁ * m₂) * (p₁ * p₂))) :
    naiveCoeff (s₂.map (tensorTerm hm₂ hn₂ hp₂ t₁)) a b c =
      (t₁.left (split₁ hm₂ hn₂ a) * t₁.right (split₁ hn₂ hp₂ b) * t₁.output (split₁ hm₂ hp₂ c)) *
        naiveCoeff s₂ (split₂ hm₂ hn₂ a) (split₂ hn₂ hp₂ b) (split₂ hm₂ hp₂ c) := by
  induction s₂ with
  | nil => simp [naiveCoeff]
  | cons t₂ ts₂ ih =>
    simp only [List.map_cons, naiveCoeff, tensorTerm]
    rw [ih, int_prod_shuffle, Int.mul_add]

private theorem naiveCoeff_tensorScheme {m₁ n₁ p₁ m₂ n₂ p₂ : Nat}
    (hm₂ : 0 < m₂) (hn₂ : 0 < n₂) (hp₂ : 0 < p₂)
    (s₁ : MatMul.SchemeInt m₁ n₁ p₁) (s₂ : MatMul.SchemeInt m₂ n₂ p₂)
    (a : Fin ((m₁ * m₂) * (n₁ * n₂)))
    (b : Fin ((n₁ * n₂) * (p₁ * p₂)))
    (c : Fin ((m₁ * m₂) * (p₁ * p₂))) :
    naiveCoeff (tensorScheme hm₂ hn₂ hp₂ s₁ s₂) a b c =
      naiveCoeff s₁ (split₁ hm₂ hn₂ a) (split₁ hn₂ hp₂ b) (split₁ hm₂ hp₂ c) *
        naiveCoeff s₂ (split₂ hm₂ hn₂ a) (split₂ hn₂ hp₂ b) (split₂ hm₂ hp₂ c) := by
  unfold tensorScheme
  induction s₁ with
  | nil => simp [naiveCoeff]
  | cons t₁ ts₁ ih =>
    simp only [List.flatMap_cons, naiveCoeff]
    rw [naiveCoeff_append, naiveCoeff_map_tensor, ih, Int.add_mul]

theorem compose : MatMul.Statements.MM_003.Claim := by
  intro m₁ n₁ p₁ m₂ n₂ p₂ r₁ r₂ ⟨s₁, hlen₁, hok₁⟩ ⟨s₂, hlen₂, hok₂⟩
  by_cases hpos : 0 < m₂ ∧ 0 < n₁ ∧ 0 < n₂ ∧ 0 < p₁ ∧ 0 < p₂
  · rcases hpos with ⟨hm₂, hn₁, hn₂, hp₁, hp₂⟩
    refine ⟨tensorScheme hm₂ hn₂ hp₂ s₁ s₂, ?_, ?_⟩
    · rw [tensorScheme_length]
      exact Nat.mul_le_mul hlen₁ hlen₂
    · intro a b c
      rw [coeffInt_eq_naiveCoeff, naiveCoeff_tensorScheme]
      rw [← coeffInt_eq_naiveCoeff s₁, ← coeffInt_eq_naiveCoeff s₂]
      rw [hok₁, hok₂, contributes_tensor hm₂ hn₁ hn₂ hp₁ hp₂ a b c]
      cases MatMul.contributes (split₁ hm₂ hn₂ a) (split₁ hn₂ hp₂ b) (split₁ hm₂ hp₂ c) <;>
        cases MatMul.contributes (split₂ hm₂ hn₂ a) (split₂ hn₂ hp₂ b) (split₂ hm₂ hp₂ c) <;>
        rfl
  · refine ⟨[], Nat.zero_le _, ?_⟩
    intro a b c
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have : False := by
      have h0 : m₂ = 0 ∨ n₁ = 0 ∨ n₂ = 0 ∨ p₁ = 0 ∨ p₂ = 0 := by omega
      rcases h0 with rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact this.elim

end MatMul.Claims.MM_003
