/-
  Codes.Core — Pure Lean 4.36.0 foundations for binary error-correcting codes
  (Sloane / Brouwer / Grassl tables of `A(n,d)` and constant-weight `A(n,d,w)`).

  Zero Mathlib: ~1s kernel builds. Words are `BitVec n`; Hamming weight and distance are
  exact bit counts. Besides the frozen specification (`hammingWeight`, `hammingDist`,
  `IsBinaryCode`, `IsConstantWeightCode`) this file ships a Boolean certificate checker
  (`checkDist`, `checkWeight`) together with soundness theorems, so an explicit witness with
  hundreds of codewords is verified by a single `decide +kernel` call (standard axioms only).
-/
namespace Codes

/-! ## Frozen specification -/

/-- `popCountAux k x` is the number of `1` bits among the lowest `k` binary digits of `x`. -/
def popCountAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => x % 2 + popCountAux k (x / 2)

/-- Hamming weight of a length-`n` binary word: the number of coordinates equal to `1`. -/
def hammingWeight {n : Nat} (v : BitVec n) : Nat :=
  popCountAux n v.toNat

/-- Hamming distance: the number of coordinates in which `u` and `v` differ. -/
def hammingDist {n : Nat} (u v : BitVec n) : Nat :=
  hammingWeight (u ^^^ v)

/-- `C` is a binary code of length `n` and minimum distance at least `d`: its codewords are
    pairwise distinct (so `C.length` is the number of codewords) and any two distinct
    codewords differ in at least `d` coordinates. `A(n,d)` is the largest such `C.length`. -/
def IsBinaryCode (n d : Nat) (C : List (BitVec n)) : Prop :=
  C.Nodup ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → d ≤ hammingDist u v

/-- `C` is a binary constant-weight code: a binary code of length `n` and minimum distance at
    least `d` in which every codeword has Hamming weight exactly `w`. `A(n,d,w)` is the largest
    such `C.length`. -/
def IsConstantWeightCode (n d w : Nat) (C : List (BitVec n)) : Prop :=
  IsBinaryCode n d C ∧ ∀ u ∈ C, hammingWeight u = w

/-! ## Basic lemmas -/

theorem popCountAux_zero : ∀ k : Nat, popCountAux k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [popCountAux, popCountAux_zero k]

theorem hammingDist_self {n : Nat} (u : BitVec n) : hammingDist u u = 0 := by
  simp [hammingDist, hammingWeight, BitVec.xor_self, popCountAux_zero]

theorem hammingDist_comm {n : Nat} (u v : BitVec n) : hammingDist u v = hammingDist v u := by
  unfold hammingDist
  rw [BitVec.xor_comm]

/-! ## Arithmetic lemmas about `popCountAux` -/

theorem popCountAux_add : ∀ (a b x : Nat),
    popCountAux (a + b) x = popCountAux a x + popCountAux b (x / 2 ^ a)
  | 0, b, x => by simp [popCountAux]
  | a + 1, b, x => by
    rw [Nat.add_right_comm]
    simp only [popCountAux]
    rw [popCountAux_add a b (x / 2), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    omega

theorem popCountAux_mod : ∀ (k x : Nat), popCountAux k (x % 2 ^ k) = popCountAux k x
  | 0, _ => rfl
  | k + 1, x => by
    simp only [popCountAux]
    rw [Nat.pow_succ', Nat.mod_mul_right_div_self, popCountAux_mod k (x / 2),
      Nat.mod_mod_of_dvd x (Nat.dvd_mul_right 2 (2 ^ k))]

/-- High zero bits do not count: if `x < 2^k` then counting more than `k` bits changes nothing. -/
theorem popCountAux_of_lt {k m x : Nat} (hx : x < 2 ^ k) (hkm : k ≤ m) :
    popCountAux m x = popCountAux k x := by
  have hm : m = k + (m - k) := by omega
  rw [hm, popCountAux_add, Nat.div_eq_of_lt hx, popCountAux_zero, Nat.add_zero]

/-! ## Fast certificate checker (proved sound below)

  The kernel spends most of its time unfolding type-class instances and structural-recursion
  helpers, so the checker uses raw `Nat.*` primitives (GMP-accelerated in the kernel), a
  `Nat.rec` loop, and a 12-bit popcount lookup table packed into one `Nat`. This verifies all
  32,640 pairs of a 256-word code of length 17 in about 1.5s. Usage in a claim file:
  ```
  def code : List (BitVec 17) := [0x0#17, 0x1B3#17, ...]
  theorem ok : IsBinaryCode 17 6 code :=
    isBinaryCode_of_checkDist (by decide) (by decide +kernel)
  ```
-/

/-- Nibble `b` (bits `4b .. 4b+3`) of `popTable12` is the number of `1` bits of `b`, for every
    `b < 4096` (checked exhaustively in `pop12_eq`). -/
def popTable12 : Nat :=
    (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 <<< 0)
    ||| (0x9887877687767665877676657665655487767665766565547665655465545443877676657665655476656554655454437665655465545443655454435443433287767665766565547665655465545443766565546554544365545443544343327665655465545443655454435443433265545443544343325443433243323221 <<< 1024)
    ||| (0x9887877687767665877676657665655487767665766565547665655465545443877676657665655476656554655454437665655465545443655454435443433287767665766565547665655465545443766565546554544365545443544343327665655465545443655454435443433265545443544343325443433243323221 <<< 2048)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 3072)
    ||| (0x9887877687767665877676657665655487767665766565547665655465545443877676657665655476656554655454437665655465545443655454435443433287767665766565547665655465545443766565546554544365545443544343327665655465545443655454435443433265545443544343325443433243323221 <<< 4096)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 5120)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 6144)
    ||| (0xbaa9a998a9989887a998988798878776a9989887988787769887877687767665a998988798878776988787768776766598878776877676658776766576656554a9989887988787769887877687767665988787768776766587767665766565549887877687767665877676657665655487767665766565547665655465545443 <<< 7168)
    ||| (0x9887877687767665877676657665655487767665766565547665655465545443877676657665655476656554655454437665655465545443655454435443433287767665766565547665655465545443766565546554544365545443544343327665655465545443655454435443433265545443544343325443433243323221 <<< 8192)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 9216)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 10240)
    ||| (0xbaa9a998a9989887a998988798878776a9989887988787769887877687767665a998988798878776988787768776766598878776877676658776766576656554a9989887988787769887877687767665988787768776766587767665766565549887877687767665877676657665655487767665766565547665655465545443 <<< 11264)
    ||| (0xa998988798878776988787768776766598878776877676658776766576656554988787768776766587767665766565548776766576656554766565546554544398878776877676658776766576656554877676657665655476656554655454438776766576656554766565546554544376656554655454436554544354434332 <<< 12288)
    ||| (0xbaa9a998a9989887a998988798878776a9989887988787769887877687767665a998988798878776988787768776766598878776877676658776766576656554a9989887988787769887877687767665988787768776766587767665766565549887877687767665877676657665655487767665766565547665655465545443 <<< 13312)
    ||| (0xbaa9a998a9989887a998988798878776a9989887988787769887877687767665a998988798878776988787768776766598878776877676658776766576656554a9989887988787769887877687767665988787768776766587767665766565549887877687767665877676657665655487767665766565547665655465545443 <<< 14336)
    ||| (0xcbbabaa9baa9a998baa9a998a9989887baa9a998a9989887a998988798878776baa9a998a9989887a998988798878776a9989887988787769887877687767665baa9a998a9989887a998988798878776a9989887988787769887877687767665a998988798878776988787768776766598878776877676658776766576656554 <<< 15360)

/-- Popcount of a 12-bit chunk, by table lookup. -/
def pop12 (b : Nat) : Nat :=
  Nat.mod (Nat.shiftRight popTable12 (Nat.mul 4 b)) 16

/-- `fastPop c x` counts the `1` bits among the lowest `12 c` bits of `x`, twelve at a time. -/
def fastPop (c : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => Nat.add (pop12 (Nat.mod x 4096)) (ih (Nat.div x 4096))) c

/-- Number of 12-bit chunks covering `n` bits. -/
def chunks (n : Nat) : Nat := (n + 11) / 12

/-- Fast Hamming weight (equal to `hammingWeight`, see `fastWeight_eq`). -/
def fastWeight {n : Nat} (u : BitVec n) : Nat :=
  fastPop (chunks n) u.toNat

/-- Fast Hamming distance (equal to `hammingDist`, see `fastDist_eq`). -/
def fastDist {n : Nat} (u v : BitVec n) : Nat :=
  fastPop (chunks n) (Nat.xor u.toNat v.toNat)

/-- Exhaustive table audit loop: `checkTable k = true` iff `pop12 b = popCountAux 12 b` for all
    `b < k`. -/
def checkTable (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b ih => Nat.beq (pop12 b) (popCountAux 12 b) && ih) k

theorem checkTable_sound : ∀ {k : Nat}, checkTable k = true → ∀ b, b < k → pop12 b = popCountAux 12 b
  | 0, _, b, hb => absurd hb (Nat.not_lt_zero b)
  | k + 1, h, b, hb => by
    have h' : Nat.beq (pop12 k) (popCountAux 12 k) = true ∧ checkTable k = true := by
      simpa [checkTable] using h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · exact checkTable_sound h'.2 b hb
    · exact Nat.eq_of_beq_eq_true h'.1

theorem pop12_eq : ∀ b, b < 4096 → pop12 b = popCountAux 12 b :=
  checkTable_sound (by decide +kernel)

theorem fastPop_eq : ∀ (c x : Nat), fastPop c x = popCountAux (12 * c) x
  | 0, _ => rfl
  | c + 1, x => by
    show pop12 (x % 4096) + fastPop c (x / 4096) = _
    rw [pop12_eq _ (Nat.mod_lt _ (by decide)), fastPop_eq c,
      show (4096 : Nat) = 2 ^ 12 from rfl, popCountAux_mod, Nat.mul_succ, Nat.add_comm _ 12,
      popCountAux_add]

theorem popCountAux_eq_fastPop {n x : Nat} (hx : x < 2 ^ n) :
    popCountAux n x = fastPop (chunks n) x := by
  rw [fastPop_eq, popCountAux_of_lt (m := 12 * chunks n) hx (by unfold chunks; omega)]

theorem fastWeight_eq {n : Nat} (u : BitVec n) : fastWeight u = hammingWeight u :=
  (popCountAux_eq_fastPop u.isLt).symm

theorem fastDist_eq {n : Nat} (u v : BitVec n) : fastDist u v = hammingDist u v := by
  unfold fastDist hammingDist hammingWeight
  rw [popCountAux_eq_fastPop (u ^^^ v).isLt, BitVec.toNat_xor]
  rfl

/-- `farFrom d u vs = true` iff every `v ∈ vs` is at Hamming distance `≥ d` from `u`. -/
def farFrom {n : Nat} (d : Nat) (u : BitVec n) : List (BitVec n) → Bool
  | [] => true
  | v :: vs => Nat.ble d (fastDist u v) && farFrom d u vs

/-- `checkDist d C = true` iff all `M(M-1)/2` pairs of list positions are at distance `≥ d`. -/
def checkDist {n : Nat} (d : Nat) : List (BitVec n) → Bool
  | [] => true
  | u :: us => farFrom d u us && checkDist d us

/-- `checkWeight w C = true` iff every codeword has Hamming weight exactly `w`. -/
def checkWeight {n : Nat} (w : Nat) : List (BitVec n) → Bool
  | [] => true
  | u :: us => Nat.beq (fastWeight u) w && checkWeight w us

theorem farFrom_sound {n d : Nat} {u : BitVec n} :
    ∀ {vs : List (BitVec n)}, farFrom d u vs = true → ∀ v ∈ vs, d ≤ hammingDist u v
  | [], _, v, hv => absurd hv (List.not_mem_nil)
  | w :: ws, h, v, hv => by
    simp only [farFrom, Bool.and_eq_true, Nat.ble_eq, fastDist_eq] at h
    rcases List.mem_cons.1 hv with rfl | hv'
    · exact h.1
    · exact farFrom_sound h.2 v hv'

theorem checkDist_sound {n d : Nat} :
    ∀ {C : List (BitVec n)}, checkDist d C = true → C.Pairwise (fun u v => d ≤ hammingDist u v)
  | [], _ => List.Pairwise.nil
  | u :: us, h => by
    simp only [checkDist, Bool.and_eq_true] at h
    exact List.Pairwise.cons (farFrom_sound h.1) (checkDist_sound h.2)

theorem checkWeight_sound {n w : Nat} :
    ∀ {C : List (BitVec n)}, checkWeight w C = true → ∀ u ∈ C, hammingWeight u = w
  | [], _, u, hu => absurd hu (List.not_mem_nil)
  | x :: xs, h, u, hu => by
    simp only [checkWeight, Bool.and_eq_true, Nat.beq_eq, fastWeight_eq] at h
    rcases List.mem_cons.1 hu with rfl | hu'
    · exact h.1
    · exact checkWeight_sound h.2 u hu'

/-- A pairwise relation that is symmetric holds between any two distinct members. -/
theorem pairwise_forall_ne {α : Type} {R : α → α → Prop} (hs : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact h.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hs (h.1 a ha')
      · exact pairwise_forall_ne hs h.2 a ha' b hb' hab

/-- Soundness of the distance certificate: for `d ≥ 1` it also certifies `C.Nodup`. -/
theorem isBinaryCode_of_checkDist {n d : Nat} {C : List (BitVec n)}
    (hd : 0 < d) (h : checkDist d C = true) : IsBinaryCode n d C := by
  have hp := checkDist_sound h
  refine ⟨hp.imp ?_, pairwise_forall_ne ?_ hp⟩
  · intro u v huv heq
    subst heq
    rw [hammingDist_self] at huv
    exact absurd hd (Nat.not_lt.2 huv)
  · intro a b hab
    rw [hammingDist_comm]
    exact hab

/-- Soundness of the constant-weight certificate. -/
theorem isConstantWeightCode_of_check {n d w : Nat} {C : List (BitVec n)}
    (hd : 0 < d) (h1 : checkDist d C = true) (h2 : checkWeight w C = true) :
    IsConstantWeightCode n d w C :=
  ⟨isBinaryCode_of_checkDist hd h1, checkWeight_sound h2⟩

end Codes
