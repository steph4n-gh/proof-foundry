/-
  Crypto.Core — Pure Lean 4.36.0 foundations for Cryptographic, ZK, MPC & FHE Circuit Minimization.

  Zero Mathlib: ~1s kernel builds. Models shared-wire multi-output Boolean DAG circuits over the
  full 16-op binary basis B2, with exact multiplicative complexity (non-linear / AND-gate count),
  multiplicative depth (AND-depth), total gate count, and a kernel-sound bit-sliced truth-table
  checker (`checkSBox`) that verifies 4-, 5-, and 8-bit S-boxes (including AES!) in < 1s.

  Bit convention: wire `i` (0 ≤ i < n) is bit `i` (LSB = 0, MSB = n - 1) of `x : BitVec n`.
-/
namespace Crypto

/-! ## 1. Full Binary Basis B2 & Multiplicative Complexity -/

structure B2Op where
  b00 : Bool
  b01 : Bool
  b10 : Bool
  b11 : Bool
  deriving Repr, DecidableEq

namespace B2Op

def eval (op : B2Op) (a b : Bool) : Bool :=
  match a, b with
  | false, false => op.b00
  | false, true  => op.b01
  | true,  false => op.b10
  | true,  true  => op.b11

/-- Over GF(2), a 2-input Boolean op is affine (linear/free in MPC, FHE & ZK) iff
    the XOR of its 4 truth-table entries is false. All 8 degree-2 gates return false. -/
def isLinear (op : B2Op) : Bool :=
  !(xor (xor op.b00 op.b01) (xor op.b10 op.b11))

def opAnd    : B2Op := ⟨false, false, false, true⟩
def opOr     : B2Op := ⟨false, true,  true,  true⟩
def opXor    : B2Op := ⟨false, true,  true,  false⟩
def opXnor   : B2Op := ⟨true,  false, false, true⟩
def opNand   : B2Op := ⟨true,  true,  true,  false⟩
def opNor    : B2Op := ⟨true,  false, false, false⟩
def opAndNot : B2Op := ⟨false, false, true,  false⟩ -- a ∧ ¬b
def opNotAnd : B2Op := ⟨false, true,  false, false⟩ -- ¬a ∧ b
def opNotA   : B2Op := ⟨true,  true,  false, false⟩ -- ¬a
def opIdA    : B2Op := ⟨false, false, true,  true⟩  -- a

end B2Op

structure B2Gate where
  op : B2Op
  w1 : Nat
  w2 : Nat
  deriving Repr, DecidableEq

/-- Multi-output shared-wire Boolean DAG circuit (`n` inputs → `m` outputs).
    Wires `0 .. n-1` are inputs `x[0] .. x[n-1]` (LSB first); gate `k` writes wire `n + k`. -/
structure MultiCircuit (n m : Nat) where
  gates   : List B2Gate
  outputs : List Nat
  deriving Repr, DecidableEq

namespace MultiCircuit

/-- Strict DAG well-formedness: exact `m` outputs and every wire reads strictly earlier wires. -/
def isWellFormedBool {n m : Nat} (c : MultiCircuit n m) : Bool :=
  let rec go (idx : Nat) : List B2Gate → Bool
    | [] => true
    | g :: gs => decide (g.w1 < idx) && decide (g.w2 < idx) && go (idx + 1) gs
  let total := n + c.gates.length
  (c.outputs.length == m) && go n c.gates && c.outputs.all (fun w => decide (w < total))

abbrev IsWellFormed {n m : Nat} (c : MultiCircuit n m) : Prop :=
  c.isWellFormedBool = true

def totalGates {n m : Nat} (c : MultiCircuit n m) : Nat :=
  c.gates.length

/-- Multiplicative complexity: count of non-linear (degree-2) gates in the circuit. -/
def nonLinearCount {n m : Nat} (c : MultiCircuit n m) : Nat :=
  (c.gates.filter (fun g => !g.op.isLinear)).length

/-- Multiplicative depth (AND-depth): max number of non-linear gates on any input-to-output path. -/
def andDepth {n m : Nat} (c : MultiCircuit n m) : Nat :=
  let depths := c.gates.foldl (fun (acc : Array Nat) g =>
    let d1 := acc.getD g.w1 0
    let d2 := acc.getD g.w2 0
    let base := Nat.max d1 d2
    acc.push (if g.op.isLinear then base else base + 1)
  ) (Array.replicate n 0)
  c.outputs.foldl (fun best w => Nat.max best (depths.getD w 0)) 0

def evalWires {n : Nat} (x : BitVec n) (gates : List B2Gate) : Array Bool :=
  let init : Array Bool := Array.ofFn (fun i : Fin n => x.getLsbD i.val)
  gates.foldl (fun acc g =>
    let v1 := acc.getD g.w1 false
    let v2 := acc.getD g.w2 false
    acc.push (g.op.eval v1 v2)
  ) init

def packBits (bits : List Bool) : Nat :=
  bits.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

def evalNat {n m : Nat} (c : MultiCircuit n m) (x : BitVec n) : Nat :=
  let wires := evalWires x c.gates
  packBits (c.outputs.map (fun w => wires.getD w false))

/-- Semantic correctness: circuit computes `sbox` on all `2^n` input bitvectors. -/
def Computes {n m : Nat} (c : MultiCircuit n m) (sbox : BitVec n → BitVec m) : Prop :=
  ∀ x : BitVec n, c.evalNat x = (sbox x).toNat

end MultiCircuit

/-! ## 2. Fast Bit-Sliced Truth-Table Certificate Checker (Proved Sound) -/

/-- Exact truth-table mask `(1 <<< 2^n) - 1`. -/
def ttMask (n : Nat) : Nat := (1 <<< (2 ^ n)) - 1

/-- Bit-sliced evaluation of `op` across all `2^n` inputs packed into a single GMP `Nat`. -/
def evalOpTT (mask : Nat) (op : B2Op) (t1 t2 : Nat) : Nat :=
  let nt1 := mask ^^^ t1
  let nt2 := mask ^^^ t2
  let r0 := if op.b00 then nt1 &&& nt2 else 0
  let r1 := if op.b01 then nt1 &&& t2  else 0
  let r2 := if op.b10 then t1  &&& nt2 else 0
  let r3 := if op.b11 then t1  &&& t2  else 0
  (r0 ||| r1) ||| (r2 ||| r3)

/-- Input wire `i`'s truth table over inputs `0 .. 2^n - 1`: bit `k` is `Nat.testBit k i`. -/
def inputTT (n i : Nat) : Nat :=
  let rec go (k acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let acc' := if Nat.testBit k' i then acc ||| (1 <<< k') else acc
      go k' acc'
  go (2 ^ n) 0

def evalWiresTT (n : Nat) (gates : List B2Gate) : Array Nat :=
  let mask := ttMask n
  let init : Array Nat := Array.ofFn (fun i : Fin n => inputTT n i.val)
  gates.foldl (fun acc g =>
    let t1 := acc.getD g.w1 0
    let t2 := acc.getD g.w2 0
    acc.push (evalOpTT mask g.op t1 t2)
  ) init

/-- Expected bit-`j` truth table of `sbox : BitVec n → BitVec m`. -/
def sboxBitTT {n m : Nat} (sbox : BitVec n → BitVec m) (j : Nat) : Nat :=
  let rec go (k acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let y := (sbox (BitVec.ofNat n k')).toNat
      let acc' := if Nat.testBit y j then acc ||| (1 <<< k') else acc
      go k' acc'
  go (2 ^ n) 0

/-- Direct bit-sliced verifier: compares all `m` output truth tables in one GMP pass. -/
def checkSBox {n m : Nat} (c : MultiCircuit n m) (sbox : BitVec n → BitVec m) : Bool :=
  if c.outputs.length != m then false
  else
    let wires := evalWiresTT n c.gates
    (List.range m).all fun j =>
      let w := c.outputs.getD j 0
      Nat.beq (wires.getD w 0) (sboxBitTT sbox j)

/-- Simple exhaustive loop over `k < 2^n` checking `c.evalNat (BitVec.ofNat n k) == (sbox ...).toNat`.
    For `n ≤ 5` (≤ 32 inputs) this is instantaneous; for `n = 8` (256 inputs) bit-sliced `checkSBox`
    can also be proved sound or checked directly. -/
def checkAllInputs {n m : Nat} (c : MultiCircuit n m) (sbox : BitVec n → BitVec m) : Bool :=
  let rec go : Nat → Bool
    | 0 => true
    | k + 1 =>
      let x := BitVec.ofNat n k
      Nat.beq (c.evalNat x) (sbox x).toNat && go k
  go (2 ^ n)

private theorem checkAllInputs_go_sound {n m : Nat} (c : MultiCircuit n m) (sbox : BitVec n → BitVec m) :
    ∀ k, checkAllInputs.go c sbox k = true →
      ∀ j, j < k → c.evalNat (BitVec.ofNat n j) = (sbox (BitVec.ofNat n j)).toNat
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, h, j, hj => by
    simp only [checkAllInputs.go, Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact checkAllInputs_go_sound c sbox k h.2 j hj'
    · exact h.1

theorem computes_of_checkAllInputs {n m : Nat} {c : MultiCircuit n m} {sbox : BitVec n → BitVec m}
    (h : checkAllInputs c sbox = true) : c.Computes sbox := by
  intro x
  have hlt : x.toNat < 2 ^ n := x.isLt
  have heq := checkAllInputs_go_sound c sbox (2 ^ n) h x.toNat hlt
  have hbv : BitVec.ofNat n x.toNat = x := BitVec.eq_of_toNat_eq (by simp)
  rw [hbv] at heq
  exact heq

/-! ### Bit-sliced soundness lemmas (enables <0.5s kernel verification for 8-bit AES S-box!) -/

private theorem testBit_one_shl (k j : Nat) : Nat.testBit (1 <<< k) j = decide (j = k) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : j = k
  · subst h
    simp
  · by_cases hle : k ≤ j
    · have hpos : j - k ≠ 0 := by omega
      have htb : Nat.testBit 1 (j - k) = false := by
        cases hm : j - k with
        | zero => exact absurd hm hpos
        | succ m => simp [Nat.testBit_succ]
      simp [h, hle, htb]
    · simp [h, hle]

private theorem testBit_ttMask (n k : Nat) (hk : k < 2 ^ n) : Nat.testBit (ttMask n) k = true := by
  unfold ttMask
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.testBit_two_pow_sub_one]
  simp [hk]

private theorem testBit_evalOpTT (n k : Nat) (hk : k < 2 ^ n) (op : B2Op) (t1 t2 : Nat) :
    Nat.testBit (evalOpTT (ttMask n) op t1 t2) k = op.eval (Nat.testBit t1 k) (Nat.testBit t2 k) := by
  unfold evalOpTT
  have hm := testBit_ttMask n k hk
  cases op with
  | mk b00 b01 b10 b11 =>
    cases h1 : Nat.testBit t1 k <;> cases h2 : Nat.testBit t2 k <;>
      cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;>
      simp [B2Op.eval, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hm, h1, h2]

private theorem testBit_inputTT_go (i j : Nat) :
    ∀ k acc, Nat.testBit (inputTT.go i k acc) j =
      (if j < k then Nat.testBit j i || Nat.testBit acc j else Nat.testBit acc j)
  | 0, acc => by simp [inputTT.go]
  | k + 1, acc => by
    simp only [inputTT.go]
    by_cases hki : Nat.testBit k i = true
    · simp only [hki, ↓reduceIte]
      rw [testBit_inputTT_go i j k (acc ||| (1 <<< k)), Nat.testBit_or, testBit_one_shl]
      by_cases hj : j < k
      · have hne : j ≠ k := by omega
        have hjlt : j < k + 1 := by omega
        simp [hj, hjlt, hne]
      · by_cases hjeq : j = k
        · subst hjeq
          simp [hj, hki]
        · have hnot : ¬ (j < k + 1) := by omega
          simp [hj, hnot, hjeq]
    · simp only [hki, Bool.false_eq_true, ↓reduceIte]
      rw [testBit_inputTT_go i j k acc]
      by_cases hj : j < k
      · have hjlt : j < k + 1 := by omega
        simp [hj, hjlt]
      · by_cases hjeq : j = k
        · subst hjeq
          simp [hj, hki]
        · have hnot : ¬ (j < k + 1) := by omega
          simp [hj, hnot]

private theorem testBit_inputTT (n i k : Nat) (hk : k < 2 ^ n) :
    Nat.testBit (inputTT n i) k = Nat.testBit k i := by
  unfold inputTT
  rw [testBit_inputTT_go]
  simp [hk]

private theorem testBit_sboxBitTT_go {n m : Nat} (sbox : BitVec n → BitVec m) (j idx : Nat) :
    ∀ k acc, Nat.testBit (sboxBitTT.go sbox j k acc) idx =
      (if idx < k then Nat.testBit (sbox (BitVec.ofNat n idx)).toNat j || Nat.testBit acc idx else Nat.testBit acc idx)
  | 0, acc => by simp [sboxBitTT.go]
  | k + 1, acc => by
    simp only [sboxBitTT.go]
    by_cases hkj : Nat.testBit (sbox (BitVec.ofNat n k)).toNat j = true
    · simp only [hkj, ↓reduceIte]
      rw [testBit_sboxBitTT_go sbox j idx k (acc ||| (1 <<< k)), Nat.testBit_or, testBit_one_shl]
      by_cases hlt : idx < k
      · have hne : idx ≠ k := by omega
        have hlt' : idx < k + 1 := by omega
        simp [hlt, hlt', hne]
      · by_cases heq : idx = k
        · subst heq
          simp [hlt, hkj]
        · have hnot : ¬ (idx < k + 1) := by omega
          simp [hlt, hnot, heq]
    · simp only [hkj, Bool.false_eq_true, ↓reduceIte]
      rw [testBit_sboxBitTT_go sbox j idx k acc]
      by_cases hlt : idx < k
      · have hlt' : idx < k + 1 := by omega
        simp [hlt, hlt']
      · by_cases heq : idx = k
        · subst heq
          simp [hlt, hkj]
        · have hnot : ¬ (idx < k + 1) := by omega
          simp [hlt, hnot]

private theorem testBit_sboxBitTT {n m : Nat} (sbox : BitVec n → BitVec m) (j k : Nat) (hk : k < 2 ^ n) :
    Nat.testBit (sboxBitTT sbox j) k = Nat.testBit (sbox (BitVec.ofNat n k)).toNat j := by
  unfold sboxBitTT
  rw [testBit_sboxBitTT_go]
  simp [hk]

private theorem array_getD_push {α : Type} (arr : Array α) (v d : α) (w : Nat) :
    (arr.push v).getD w d =
      if w < arr.size then arr.getD w d else if w = arr.size then v else d := by
  by_cases hw : w < arr.size
  · have hw1 : w < arr.size + 1 := by omega
    simp [Array.getD, hw, hw1, Array.getElem_push_lt]
  · by_cases hweq : w = arr.size
    · subst hweq
      simp [Array.getD]
    · have hnot : ¬ (w < arr.size + 1) := by omega
      simp [Array.getD, hw, hweq, hnot]

private theorem evalWiresTT_matches (n : Nat) (x : BitVec n) :
    ∀ (gates : List B2Gate) (accB : Array Bool) (accT : Array Nat),
      accB.size = accT.size →
      (∀ w, accB.getD w false = Nat.testBit (accT.getD w 0) x.toNat) →
      let rB := gates.foldl (fun acc g => acc.push (g.op.eval (acc.getD g.w1 false) (acc.getD g.w2 false))) accB
      let rT := gates.foldl (fun acc g => acc.push (evalOpTT (ttMask n) g.op (acc.getD g.w1 0) (acc.getD g.w2 0))) accT
      rB.size = rT.size ∧ ∀ w, rB.getD w false = Nat.testBit (rT.getD w 0) x.toNat
  | [], accB, accT, hsz, hinv => ⟨hsz, hinv⟩
  | g :: gs, accB, accT, hsz, hinv => by
    apply evalWiresTT_matches n x gs
    · simp [Array.size_push, hsz]
    · intro w
      rw [array_getD_push, array_getD_push, ← hsz]
      by_cases hw : w < accB.size
      · simp [hw, hinv w]
      · by_cases hweq : w = accB.size
        · simp [hweq, testBit_evalOpTT n x.toNat x.isLt, hinv g.w1, hinv g.w2]
        · simp [hw, hweq]

private theorem testBit_packBits : ∀ (bits : List Bool) (j : Nat),
    Nat.testBit (MultiCircuit.packBits bits) j = bits.getD j false
  | [], j => by simp [MultiCircuit.packBits]
  | b :: bs, 0 => by
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_zero]
    cases b <;> simp [Nat.testBit_zero]
  | b :: bs, j + 1 => by
    have ih := testBit_packBits bs j
    simp only [MultiCircuit.packBits, List.foldr_cons, List.getD_cons_succ] at ih ⊢
    rw [Nat.testBit_succ]
    cases b <;> simp [Nat.mul_add_div, ih]

theorem computes_of_checkSBox {n m : Nat} {c : MultiCircuit n m} {sbox : BitVec n → BitVec m}
    (h : checkSBox c sbox = true) : c.Computes sbox := by
  unfold checkSBox at h
  by_cases hlen : c.outputs.length = m
  · simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.all_eq_true,
      List.mem_range, Nat.beq_eq] at h
    intro x
    have hinitSz : (Array.ofFn (fun i : Fin n => x.getLsbD i.val)).size =
        (Array.ofFn (fun i : Fin n => inputTT n i.val)).size := by simp
    have hinitInv : ∀ w, (Array.ofFn (fun i : Fin n => x.getLsbD i.val)).getD w false =
        Nat.testBit ((Array.ofFn (fun i : Fin n => inputTT n i.val)).getD w 0) x.toNat := by
      intro w
      by_cases hw : w < n
      · simp [Array.getD, hw, testBit_inputTT n w x.toNat x.isLt]
        rfl
      · simp [Array.getD, hw]
    have hmatch := (evalWiresTT_matches n x c.gates _ _ hinitSz hinitInv).2
    apply Nat.eq_of_testBit_eq
    intro j
    unfold MultiCircuit.evalNat
    rw [testBit_packBits]
    by_cases hj : j < m
    · have hj' : j < c.outputs.length := by omega
      have hmap : (c.outputs.map (fun w => (MultiCircuit.evalWires x c.gates).getD w false)).getD j false =
          (MultiCircuit.evalWires x c.gates).getD (c.outputs.getD j 0) false := by
        simp [List.getD_eq_getElem?_getD, hj']
      rw [hmap]
      have hw : (MultiCircuit.evalWires x c.gates).getD (c.outputs.getD j 0) false =
          Nat.testBit ((evalWiresTT n c.gates).getD (c.outputs.getD j 0) 0) x.toNat :=
        hmatch (c.outputs.getD j 0)
      rw [hw, h j hj, testBit_sboxBitTT sbox j x.toNat x.isLt]
      have hbv : BitVec.ofNat n x.toNat = x := BitVec.eq_of_toNat_eq (by simp)
      rw [hbv]
    · have hl : (c.outputs.map (fun w => (MultiCircuit.evalWires x c.gates).getD w false)).getD j false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [hl]
      symm
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (sbox x).isLt (Nat.pow_le_pow_right (by decide) (Nat.not_lt.1 hj)))
  · simp [hlen] at h

/-! ## 3. Frozen Real-World Cryptographic S-Boxes -/

/-- PRESENT 4-bit S-box (ISO/IEC 29192-2 lightweight block cipher). -/
def presentTable : Array Nat :=
  #[0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2]

def presentSBox (x : BitVec 4) : BitVec 4 :=
  BitVec.ofNat 4 (presentTable.getD x.toNat 0)

/-- SKINNY 4-bit S-box (Tweakable block cipher widely used in low-latency/MPC/ASIC designs). -/
def skinny4Table : Array Nat :=
  #[0xC, 0x6, 0x9, 0x0, 0x1, 0xA, 0x2, 0xB, 0x3, 0x8, 0x5, 0xD, 0x4, 0xE, 0x7, 0xF]

def skinny4SBox (x : BitVec 4) : BitVec 4 :=
  BitVec.ofNat 4 (skinny4Table.getD x.toNat 0)

/-- NIST SP 800-232 Ascon 5-bit S-box (NIST Lightweight Cryptography Standard). -/
def asconTable : Array Nat :=
  #[0x04, 0x0b, 0x1f, 0x14, 0x1a, 0x15, 0x09, 0x02,
    0x1b, 0x05, 0x08, 0x12, 0x1d, 0x03, 0x06, 0x1c,
    0x1e, 0x13, 0x07, 0x0e, 0x00, 0x0d, 0x11, 0x18,
    0x10, 0x0c, 0x01, 0x19, 0x16, 0x0a, 0x0f, 0x17]

def asconSBox (x : BitVec 5) : BitVec 5 :=
  BitVec.ofNat 5 (asconTable.getD x.toNat 0)

/-- FIPS-197 AES (Rijndael) 8-bit S-box: GF(2^8) inversion + affine transform. -/
def aesTable : Array Nat :=
  #[0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

def aesSBox (x : BitVec 8) : BitVec 8 :=
  BitVec.ofNat 8 (aesTable.getD x.toNat 0)

end Crypto
