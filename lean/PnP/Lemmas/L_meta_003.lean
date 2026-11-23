import PnP.Core

/-!
  L-meta-003: the exact B2 (all 16 binary ops, arbitrary fan-out) circuit size of
  3-bit Majority is 4.

  Upper bound: `w3 = x0 ∧ x1`, `w4 = x0 ∨ x1`, `w5 = w4 ∧ x2`, `w6 = w3 ∨ w5`.

  Lower bound (no circuit with ≤ 3 gates computes MAJ3):
  * every wire is abstracted to its 8-bit truth table (a `Nat`; bit `i` is the value
    on the input with index `i = x0 + 2 x1 + 4 x2`); MAJ3 has table `232`;
  * a simulation lemma shows the table fold `tw` tracks `B2Circuit.evalWires` bit-wise;
  * `sepT t a b` is a fast bit-mask test for "table `t` is *some* binary function of
    tables `a` and `b`" (4 classes of inputs); `sepT_sound` proves it is necessary;
  * the reachable tables of 1, 2, 3 gates are covered by six small kernel-checked
    certificates (`decide +kernel`, no `native_decide`, no extra axioms):
    - `F1` (38 tables) is closed under one gate over `{0, x0, x1, x2}`;
    - no pair from `f1 :: S0` separates MAJ3 (kills gates 1, 2 and pairs w/o gate 2);
    - a final gate reading gate 2 and an input/const/itself needs gate 2's table in
      `Bad0` (8 tables), and no `Bad0` table is a binary function of `f1` and one more
      wire; gates 2 built from inputs only are handled by the `F1 × F1` table.
-/
namespace PnP.Lemmas.L_meta_003

open PnP

/-! ### 8-bit truth tables -/

def allOps : List B2Op :=
  [⟨false, false, false, false⟩, ⟨false, false, false, true⟩, ⟨false, false, true, false⟩,
   ⟨false, false, true, true⟩, ⟨false, true, false, false⟩, ⟨false, true, false, true⟩,
   ⟨false, true, true, false⟩, ⟨false, true, true, true⟩, ⟨true, false, false, false⟩,
   ⟨true, false, false, true⟩, ⟨true, false, true, false⟩, ⟨true, false, true, true⟩,
   ⟨true, true, false, false⟩, ⟨true, true, false, true⟩, ⟨true, true, true, false⟩,
   ⟨true, true, true, true⟩]

theorem mem_allOps (op : B2Op) : op ∈ allOps := by
  rcases op with ⟨b00, b01, b10, b11⟩
  cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide

/-- Apply a binary op bit-wise to two 8-bit truth tables. -/
def opT (op : B2Op) (a b : Nat) : Nat :=
  (cond op.b00 ((255 ^^^ a) &&& (255 ^^^ b)) 0) ||| (cond op.b01 ((255 ^^^ a) &&& b) 0) |||
  (cond op.b10 (a &&& (255 ^^^ b)) 0) ||| (cond op.b11 (a &&& b) 0)

theorem testBit_255 (i : Nat) : (255 : Nat).testBit i = decide (i < 8) := by
  have h : (255 : Nat) = 2 ^ 8 - 1 := rfl
  rw [h, Nat.testBit_two_pow_sub_one]

theorem testBit_cond (c : Bool) (x i : Nat) : (cond c x 0).testBit i = (c && x.testBit i) := by
  cases c <;> simp

theorem opT_bit (op : B2Op) (a b i : Nat) (hi : i < 8) :
    (opT op a b).testBit i = op.eval (a.testBit i) (b.testBit i) := by
  have h255 : (255 : Nat).testBit i = true := by
    rw [testBit_255]; exact decide_eq_true hi
  rcases op with ⟨b00, b01, b10, b11⟩
  simp only [opT, Nat.testBit_or, testBit_cond, Nat.testBit_and, Nat.testBit_xor, h255]
  cases a.testBit i <;> cases b.testBit i <;> simp [B2Op.eval]

theorem cond_lt (c : Bool) {x : Nat} (h : x < 2 ^ 8) : cond c x 0 < 2 ^ 8 := by
  cases c
  · exact Nat.two_pow_pos 8
  · exact h

theorem opT_lt (op : B2Op) (a b : Nat) (hb : b < 256) : opT op a b < 256 := by
  have hb' : b < 2 ^ 8 := hb
  have hnb : 255 ^^^ b < 2 ^ 8 := Nat.xor_lt_two_pow (by decide) hb'
  show opT op a b < 2 ^ 8
  exact Nat.or_lt_two_pow
    (Nat.or_lt_two_pow
      (Nat.or_lt_two_pow (cond_lt _ (Nat.and_lt_two_pow _ hnb)) (cond_lt _ (Nat.and_lt_two_pow _ hb')))
      (cond_lt _ (Nat.and_lt_two_pow _ hnb)))
    (cond_lt _ (Nat.and_lt_two_pow _ hb'))

/-! ### Separation test: is table `t` a binary function of tables `a`, `b`? -/

def selB (α : Bool) (a : Nat) : Nat := cond α a (255 ^^^ a)

def clsT (t k : Nat) : Bool := (k &&& t == 0) || (k &&& (255 ^^^ t) == 0)

def sepT (t a b : Nat) : Bool :=
  clsT t (selB false a &&& selB false b &&& 255) && clsT t (selB false a &&& selB true b &&& 255) &&
  clsT t (selB true a &&& selB false b &&& 255) && clsT t (selB true a &&& selB true b &&& 255)

theorem land_eq_zero {x y : Nat} (h : ∀ i, x.testBit i = true → y.testBit i = false) :
    x &&& y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases hx : x.testBit i
  · rfl
  · simp [h i hx]

theorem clsT_of (t K : Nat) (v : Bool)
    (hK : ∀ i, K.testBit i = true → i < 8 ∧ t.testBit i = v) : clsT t K = true := by
  cases v
  · have h0 : K &&& t = 0 := land_eq_zero (fun i hi => (hK i hi).2)
    simp [clsT, h0]
  · have h0 : K &&& (255 ^^^ t) = 0 := land_eq_zero (fun i hi => by
      obtain ⟨h8, ht⟩ := hK i hi
      rw [Nat.testBit_xor, testBit_255, ht]
      simp [h8])
    simp [clsT, h0]

theorem selB_bit (α : Bool) (a i : Nat) (h8 : i < 8) (h : (selB α a).testBit i = true) :
    a.testBit i = α := by
  cases α
  · simp only [selB, cond, Nat.testBit_xor, testBit_255, decide_eq_true h8] at h
    cases ha : a.testBit i
    · rfl
    · rw [ha] at h; exact absurd h (by decide)
  · exact h

theorem sepT_sound (t a b : Nat) (g : Bool → Bool → Bool)
    (h : ∀ i, i < 8 → g (a.testBit i) (b.testBit i) = t.testBit i) : sepT t a b = true := by
  have key : ∀ α β : Bool, clsT t (selB α a &&& selB β b &&& 255) = true := by
    intro α β
    apply clsT_of t _ (g α β)
    intro i hi
    rw [Nat.testBit_and, Nat.testBit_and, testBit_255] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨ha, hb⟩, h8⟩ := hi
    refine ⟨h8, ?_⟩
    rw [← h i h8, selB_bit α a i h8 ha, selB_bit β b i h8 hb]
  simp [sepT, key]

/-! ### MAJ3-specific notions (MAJ3 has truth table 232) -/

/-- Table `t` agrees with MAJ3 on all 8 inputs. -/
def Hits (t : Nat) : Prop := ∀ i, i < 8 → t.testBit i = (232 : Nat).testBit i

def sep (a b : Nat) : Bool := sepT 232 a b

theorem sep_of (a b : Nat) (g : Bool → Bool → Bool)
    (h : ∀ i, i < 8 → g (a.testBit i) (b.testBit i) = (232 : Nat).testBit i) : sep a b = true :=
  sepT_sound 232 a b g h

theorem sep_of_hits (op : B2Op) (a b : Nat) (h : Hits (opT op a b)) : sep a b = true :=
  sep_of a b op.eval (fun i hi => by rw [← opT_bit op a b i hi]; exact h i hi)

/-- Tables of the wires readable before any gate: const-false, x0, x1, x2. -/
def S0 : List Nat := [0, 170, 204, 240]

def bad0 (t : Nat) : Bool := sep t t || sep t 0 || sep t 170 || sep t 204 || sep t 240

/-- All tables computable by one gate from `S0`. -/
def F1 : List Nat :=
  [0, 170, 136, 160, 204, 192, 240, 34, 10, 68, 12, 80, 48, 102, 90, 60, 238, 250, 252, 255, 85,
   51, 15, 17, 5, 3, 153, 165, 195, 187, 175, 221, 207, 245, 243, 119, 95, 63]

/-- Every table `t < 256` with `bad0 t`. -/
def Bad0 : List Nat := [23, 24, 36, 66, 189, 219, 231, 232]

/-! ### Kernel-checked certificates (`decide +kernel`: kernel evaluation, no extra axioms) -/

set_option maxRecDepth 100000

theorem cert_F1 : ∀ op ∈ allOps, ∀ a ∈ S0, ∀ b ∈ S0, opT op a b ∈ F1 := by decide +kernel

theorem cert_pairs : ∀ f1 ∈ F1, ∀ a ∈ f1 :: S0, ∀ b ∈ f1 :: S0, sep a b = false := by
  decide +kernel

theorem cert_bad0_F1 : ∀ f ∈ F1, bad0 f = false := by decide +kernel

theorem cert_cross : ∀ f1 ∈ F1, ∀ f2 ∈ F1, sep f2 f1 = false := by decide +kernel

theorem cert_mixed : ∀ f1 ∈ F1, ∀ c ∈ f1 :: S0, ∀ t ∈ Bad0, sepT t f1 c = false := by
  decide +kernel

theorem cert_bad0 : ∀ t ∈ List.range 256, bad0 t = false ∨ t ∈ Bad0 := by decide +kernel

theorem S0_lt : ∀ x ∈ S0, x < 256 := by decide

theorem F1_lt : ∀ x ∈ F1, x < 256 := by decide

/-! ### No table reachable with ≤ 3 gates agrees with MAJ3 -/

theorem not_hits_S0 : ∀ t ∈ S0, ¬ Hits t := by
  intro t ht hH
  simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact absurd (hH 3 (by decide)) (by decide)
  · exact absurd (hH 1 (by decide)) (by decide)
  · exact absurd (hH 2 (by decide)) (by decide)
  · exact absurd (hH 3 (by decide)) (by decide)

/-- A gate reading two wires of `f1 :: S0` never agrees with MAJ3. -/
theorem hit_f (f1 : Nat) (hf1 : f1 ∈ F1) (op : B2Op) (a b : Nat)
    (ha : a ∈ f1 :: S0) (hb : b ∈ f1 :: S0) : ¬ Hits (opT op a b) := by
  intro hH
  have h2 := cert_pairs f1 hf1 a ha b hb
  rw [sep_of_hits op a b hH] at h2
  exact Bool.noConfusion h2

/-- A final gate `g (f2, b')` with `b'` among `f2 :: f1 :: S0` never agrees with MAJ3. -/
theorem key3 (f1 : Nat) (hf1 : f1 ∈ F1) (op2 : B2Op) (a2 b2 : Nat)
    (ha2 : a2 ∈ f1 :: S0) (hb2 : b2 ∈ f1 :: S0) (b' : Nat)
    (hb' : b' ∈ opT op2 a2 b2 :: f1 :: S0) (g : Bool → Bool → Bool)
    (hg : ∀ i, i < 8 → g ((opT op2 a2 b2).testBit i) (b'.testBit i) = (232 : Nat).testBit i) :
    False := by
  have pairs := cert_pairs f1 hf1
  have f1_mem : f1 ∈ f1 :: S0 := List.mem_cons_self
  have lt_S1 : ∀ x ∈ f1 :: S0, x < 256 := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact F1_lt x hf1
    · exact S0_lt x hx'
  have f2_lt : opT op2 a2 b2 < 256 := opT_lt _ _ _ (lt_S1 b2 hb2)
  have hbit : ∀ i, i < 8 → (opT op2 a2 b2).testBit i = op2.eval (a2.testBit i) (b2.testBit i) :=
    fun i hi => opT_bit op2 a2 b2 i hi
  have decomp : (opT op2 a2 b2 ∈ F1) ∨
      (∃ c ∈ f1 :: S0, ∃ o : Bool → Bool → Bool,
        ∀ i, i < 8 → (opT op2 a2 b2).testBit i = o (f1.testBit i) (c.testBit i)) := by
    rcases List.mem_cons.1 ha2 with rfl | ha2'
    · exact Or.inr ⟨b2, hb2, op2.eval, hbit⟩
    · rcases List.mem_cons.1 hb2 with rfl | hb2'
      · exact Or.inr ⟨a2, ha2, fun x y => op2.eval y x, hbit⟩
      · exact Or.inl (cert_F1 op2 (mem_allOps op2) a2 ha2' b2 hb2')
  generalize opT op2 a2 b2 = f2 at hb' hg f2_lt decomp
  have hsep : sep f2 b' = true := sep_of f2 b' g hg
  have bad_of : (b' = f2 ∨ b' ∈ S0) → bad0 f2 = true := by
    intro hcase
    rcases hcase with rfl | hS0
    · simp [bad0, hsep]
    · simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at hS0
      rcases hS0 with rfl | rfl | rfl | rfl <;> simp [bad0, hsep]
  rcases List.mem_cons.1 hb' with hbf2 | hb''
  · -- final gate reads gate 2 twice: a unary function of gate 2
    rcases decomp with hA | ⟨c, hc, o, ho⟩
    · have := cert_bad0_F1 f2 hA
      rw [bad_of (Or.inl hbf2)] at this
      exact Bool.noConfusion this
    · subst hbf2
      have hs : sep f1 c = true :=
        sep_of f1 c (fun α γ => g (o α γ) (o α γ)) (fun i hi => by
          rw [← ho i hi]; exact hg i hi)
      rw [pairs f1 f1_mem c hc] at hs
      exact Bool.noConfusion hs
  · rcases List.mem_cons.1 hb'' with rfl | hS0
    · -- final gate reads gate 2 and gate 1
      rcases decomp with hA | ⟨c, hc, o, ho⟩
      · have := cert_cross b' hf1 f2 hA
        rw [hsep] at this
        exact Bool.noConfusion this
      · have hs : sep b' c = true :=
          sep_of b' c (fun α γ => g (o α γ) α) (fun i hi => by
            rw [← ho i hi]; exact hg i hi)
        rw [pairs b' f1_mem c hc] at hs
        exact Bool.noConfusion hs
    · -- final gate reads gate 2 and an input / constant wire
      have hbad := bad_of (Or.inr hS0)
      rcases decomp with hA | ⟨c, hc, o, ho⟩
      · have := cert_bad0_F1 f2 hA
        rw [hbad] at this
        exact Bool.noConfusion this
      · have hmem : f2 ∈ Bad0 := by
          rcases cert_bad0 f2 (List.mem_range.2 f2_lt) with h | h
          · rw [hbad] at h; exact Bool.noConfusion h
          · exact h
        have hs : sepT f2 f1 c = true := sepT_sound f2 f1 c o (fun i hi => (ho i hi).symm)
        rw [cert_mixed f1 hf1 c hc f2 hmem] at hs
        exact Bool.noConfusion hs

/-- A third gate never agrees with MAJ3. -/
theorem no_hit3 (f1 : Nat) (hf1 : f1 ∈ F1) (op2 : B2Op) (a2 b2 : Nat)
    (ha2 : a2 ∈ f1 :: S0) (hb2 : b2 ∈ f1 :: S0) (op3 : B2Op) (a3 b3 : Nat)
    (ha3 : a3 ∈ opT op2 a2 b2 :: f1 :: S0) (hb3 : b3 ∈ opT op2 a2 b2 :: f1 :: S0) :
    ¬ Hits (opT op3 a3 b3) := by
  intro hH
  have H3 : ∀ i, i < 8 → op3.eval (a3.testBit i) (b3.testBit i) = (232 : Nat).testBit i :=
    fun i hi => by rw [← opT_bit op3 a3 b3 i hi]; exact hH i hi
  rcases List.mem_cons.1 ha3 with rfl | ha3'
  · exact key3 f1 hf1 op2 a2 b2 ha2 hb2 b3 hb3 op3.eval H3
  · rcases List.mem_cons.1 hb3 with rfl | hb3'
    · exact key3 f1 hf1 op2 a2 b2 ha2 hb2 a3 (List.mem_cons_of_mem _ ha3')
        (fun x y => op3.eval y x) H3
    · exact hit_f f1 hf1 op3 a3 b3 ha3' hb3' hH

/-! ### Table fold for circuits and the simulation lemma -/

def stepB (acc : Array Bool) (g : B2Gate) : Array Bool :=
  acc.push (g.op.eval (acc.getD g.w1 false) (acc.getD g.w2 false))

def stepT (acc : Array Nat) (g : B2Gate) : Array Nat :=
  acc.push (opT g.op (acc.getD g.w1 0) (acc.getD g.w2 0))

def T0 : Array Nat := #[170, 204, 240]

def tw (gates : List B2Gate) : Array Nat := gates.foldl stepT T0

theorem getD_push {α : Type} (A : Array α) (v d : α) (w : Nat) :
    (A.push v).getD w d = if w = A.size then v else A.getD w d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> simp

/-- Input index of an assignment: `x0 + 2 x1 + 4 x2`. -/
def idx (x : BoolVec 3) : Nat :=
  cond (x ⟨0, by decide⟩) 1 0 + cond (x ⟨1, by decide⟩) 2 0 + cond (x ⟨2, by decide⟩) 4 0

theorem idx_facts (x : BoolVec 3) :
    idx x < 8 ∧ x ⟨0, by decide⟩ = (170 : Nat).testBit (idx x) ∧
    x ⟨1, by decide⟩ = (204 : Nat).testBit (idx x) ∧
    x ⟨2, by decide⟩ = (240 : Nat).testBit (idx x) ∧
    maj3 x = (232 : Nat).testBit (idx x) := by
  simp only [idx, maj3]
  generalize x ⟨0, by decide⟩ = a
  generalize x ⟨1, by decide⟩ = b
  generalize x ⟨2, by decide⟩ = c
  cases a <;> cases b <;> cases c <;> decide

def ofIdx (i : Nat) : BoolVec 3 := fun j => i.testBit j.val

theorem idx_ofIdx : ∀ i, i < 8 → idx (ofIdx i) = i := by decide

def Sim (k : Nat) (A : Array Bool) (T : Array Nat) : Prop :=
  A.size = T.size ∧ ∀ w, A.getD w false = (T.getD w 0).testBit k

theorem sim_step (k : Nat) (hk : k < 8) (A : Array Bool) (T : Array Nat) (g : B2Gate)
    (h : Sim k A T) : Sim k (stepB A g) (stepT T g) := by
  obtain ⟨hs, hw⟩ := h
  refine ⟨by simp [stepB, stepT, hs], fun w => ?_⟩
  simp only [stepB, stepT, getD_push, hs]
  split
  · rw [opT_bit _ _ _ _ hk, hw g.w1, hw g.w2]
  · exact hw w

theorem sim_fold (k : Nat) (hk : k < 8) (gates : List B2Gate) :
    ∀ (A : Array Bool) (T : Array Nat), Sim k A T →
      Sim k (gates.foldl stepB A) (gates.foldl stepT T) := by
  induction gates with
  | nil => intro A T h; exact h
  | cons g gs ih => intro A T h; exact ih _ _ (sim_step k hk A T g h)

theorem sim_init (x : BoolVec 3) : Sim (idx x) (Array.ofFn fun i : Fin 3 => x i) T0 := by
  obtain ⟨_, h0, h1, h2, _⟩ := idx_facts x
  refine ⟨by simp [T0], fun w => ?_⟩
  match w with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | k + 3 =>
    have hlt : ¬ (k + 3 < 3) := by omega
    simp [Array.getD, T0, hlt]

theorem eval_sim (c : B2Circuit 3) (x : BoolVec 3) :
    c.eval x = ((tw c.gates).getD c.outputWire 0).testBit (idx x) :=
  (sim_fold (idx x) (idx_facts x).1 c.gates _ _ (sim_init x)).2 c.outputWire

/-! ### Wire-table membership for ≤ 3 gates -/

theorem T0_mem (w : Nat) : T0.getD w 0 ∈ S0 := by
  match w with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    have hlt : ¬ (k + 3 < 3) := by omega
    simp [Array.getD, T0, hlt, S0]

theorem push_mem (T : Array Nat) (L : List Nat) (v : Nat) (h : ∀ w, T.getD w 0 ∈ L) (w : Nat) :
    (T.push v).getD w 0 ∈ v :: L := by
  rw [getD_push]
  split
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h w)

def f1v (g0 : B2Gate) : Nat := opT g0.op (T0.getD g0.w1 0) (T0.getD g0.w2 0)

def T1 (g0 : B2Gate) : Array Nat := T0.push (f1v g0)

def f2v (g0 g1 : B2Gate) : Nat := opT g1.op ((T1 g0).getD g1.w1 0) ((T1 g0).getD g1.w2 0)

def T2 (g0 g1 : B2Gate) : Array Nat := (T1 g0).push (f2v g0 g1)

def f3v (g0 g1 g2 : B2Gate) : Nat :=
  opT g2.op ((T2 g0 g1).getD g2.w1 0) ((T2 g0 g1).getD g2.w2 0)

theorem no_hit_all (g0 g1 g2 : B2Gate) :
    ∀ t ∈ f3v g0 g1 g2 :: f2v g0 g1 :: f1v g0 :: S0, ¬ Hits t := by
  have hf1 : f1v g0 ∈ F1 := cert_F1 g0.op (mem_allOps _) _ (T0_mem _) _ (T0_mem _)
  have sub : ∀ x ∈ S0, x ∈ f1v g0 :: S0 := fun x hx => List.mem_cons_of_mem _ hx
  have mem1 : ∀ w, (T1 g0).getD w 0 ∈ f1v g0 :: S0 := push_mem T0 S0 _ T0_mem
  have mem2 : ∀ w, (T2 g0 g1).getD w 0 ∈ f2v g0 g1 :: f1v g0 :: S0 := push_mem _ _ _ mem1
  intro t ht
  rcases List.mem_cons.1 ht with rfl | ht
  · exact no_hit3 (f1v g0) hf1 g1.op _ _ (mem1 _) (mem1 _) g2.op _ _ (mem2 _) (mem2 _)
  rcases List.mem_cons.1 ht with rfl | ht
  · exact hit_f (f1v g0) hf1 g1.op _ _ (mem1 _) (mem1 _)
  rcases List.mem_cons.1 ht with rfl | ht
  · exact hit_f (f1v g0) hf1 g0.op _ _ (sub _ (T0_mem _)) (sub _ (T0_mem _))
  exact not_hits_S0 t ht

theorem no_hit_tw (gates : List B2Gate) (hs : gates.length ≤ 3) (w : Nat) :
    ¬ Hits ((tw gates).getD w 0) := by
  have d : B2Gate := ⟨B2Op.opAnd, 0, 0⟩
  match gates, hs with
  | [], _ =>
    exact no_hit_all d d d _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (T0_mem w))))
  | [g0], _ =>
    have hm : (tw [g0]).getD w 0 ∈ f1v g0 :: S0 := push_mem T0 S0 _ T0_mem w
    exact no_hit_all g0 d d _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  | [g0, g1], _ =>
    have hm : (tw [g0, g1]).getD w 0 ∈ f2v g0 g1 :: f1v g0 :: S0 :=
      push_mem _ _ _ (push_mem T0 S0 _ T0_mem) w
    exact no_hit_all g0 g1 d _ (List.mem_cons_of_mem _ hm)
  | [g0, g1, g2], _ =>
    have hm : (tw [g0, g1, g2]).getD w 0 ∈ f3v g0 g1 g2 :: f2v g0 g1 :: f1v g0 :: S0 :=
      push_mem _ _ _ (push_mem _ _ _ (push_mem T0 S0 _ T0_mem)) w
    exact no_hit_all g0 g1 g2 _ hm
  | _ :: _ :: _ :: _ :: _, hs => simp at hs

/-! ### Main theorem -/

def maj3Circuit : B2Circuit 3 :=
  { gates := [⟨B2Op.opAnd, 0, 1⟩, ⟨B2Op.opOr, 0, 1⟩, ⟨B2Op.opAnd, 4, 2⟩, ⟨B2Op.opOr, 3, 5⟩],
    outputWire := 6 }

theorem maj3Circuit_table : (tw maj3Circuit.gates).getD maj3Circuit.outputWire 0 = 232 := by
  decide

theorem maj3Circuit_computes : maj3Circuit.Computes maj3 := by
  intro x
  rw [eval_sim, maj3Circuit_table, (idx_facts x).2.2.2.2]

theorem maj3_lower (c : B2Circuit 3) (hc : c.Computes maj3) : 4 ≤ c.size := by
  apply Nat.le_of_not_lt
  intro hlt
  have hs : c.gates.length ≤ 3 := by
    unfold B2Circuit.size at hlt
    omega
  apply no_hit_tw c.gates hs c.outputWire
  intro i hi
  have h := hc (ofIdx i)
  rw [eval_sim, (idx_facts _).2.2.2.2, idx_ofIdx i hi] at h
  exact h

theorem maj3_exact_b2_size_four :
    (∃ c : B2Circuit 3, c.size = 4 ∧ c.Computes maj3) ∧
    (∀ c : B2Circuit 3, c.Computes maj3 → 4 ≤ c.size) :=
  ⟨⟨maj3Circuit, rfl, maj3Circuit_computes⟩, maj3_lower⟩

end PnP.Lemmas.L_meta_003
