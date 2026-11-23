import PnP.Core

namespace PnP.Lemmas.L_clb_005

private def pushGate (a : Array Bool) (g : B2Gate) : Array Bool :=
  a.push (g.op.eval (a.getD g.w1 false) (a.getD g.w2 false))

private theorem readPush (a : Array Bool) (b : Bool) (w : Nat) :
    (a.push b).getD w false = if w = a.size then b else a.getD w false := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

-- Work backward from the output. Expanding a live gate replaces its output
-- with its two operands, even when either operand already occurs in the list.
private theorem outputSupport (gs : List B2Gate) (m out : Nat) :
    ∃ ws : List Nat, ws.length ≤ gs.length + 1 ∧
      ∀ a b : Array Bool, a.size = m → b.size = m →
        (∀ w ∈ ws, a.getD w false = b.getD w false) →
        (gs.foldl pushGate a).getD out false = (gs.foldl pushGate b).getD out false := by
  induction gs generalizing m with
  | nil =>
    exact ⟨[out], by simp, fun a b _ _ h => h out (by simp)⟩
  | cons g gs ih =>
    obtain ⟨ws, hlen, hs⟩ := ih (m + 1)
    by_cases hmem : m ∈ ws
    · let rest := ws.filter (fun w => w != m)
      have hshort : rest.length < ws.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨m, hmem, by simp⟩
      refine ⟨g.w1 :: g.w2 :: rest, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro a b ha hb hagree
        change (gs.foldl pushGate (pushGate a g)).getD out false =
          (gs.foldl pushGate (pushGate b g)).getD out false
        apply hs _ _ (by simp [pushGate, ha]) (by simp [pushGate, hb])
        intro w hw
        simp only [pushGate, readPush, ha, hb]
        by_cases hwm : w = m
        · simp only [hwm, ite_true]
          rw [hagree g.w1 (by simp), hagree g.w2 (by simp)]
        · simp only [hwm, ite_false]
          exact hagree w (by simp [rest, hw, hwm])
    · refine ⟨ws, by simp only [List.length_cons]; omega, ?_⟩
      intro a b ha hb hagree
      change (gs.foldl pushGate (pushGate a g)).getD out false =
        (gs.foldl pushGate (pushGate b g)).getD out false
      apply hs _ _ (by simp [pushGate, ha]) (by simp [pushGate, hb])
      intro w hw
      have hwm : w ≠ m := fun h => hmem (h ▸ hw)
      simpa only [pushGate, readPush, ha, hb, hwm, ite_false] using hagree w hw

theorem b2_depends_all_lower_bound {n : Nat} (c : B2Circuit n) (f : BoolFn n)
    (hc : c.Computes f) (hdep : ∀ i : Fin n, DependsOn f i) : n ≤ c.size + 1 := by
  obtain ⟨ws, hlen, hs⟩ := outputSupport c.gates n c.outputWire
  have hsub : List.range n ⊆ ws := by
    intro w hw
    have hi : w < n := List.mem_range.mp hw
    let i : Fin n := ⟨w, hi⟩
    by_cases hmem : w ∈ ws
    · exact hmem
    exfalso
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    rw [← hc x, ← hc (flipBit x i)]
    change (c.gates.foldl pushGate (Array.ofFn x)).getD c.outputWire false =
      (c.gates.foldl pushGate (Array.ofFn (flipBit x i))).getD c.outputWire false
    apply hs _ _ (by simp) (by simp)
    intro j hj
    by_cases hjn : j < n
    · have hji : (⟨j, hjn⟩ : Fin n) ≠ i := by
        intro h
        have hval : j = w := congrArg Fin.val h
        exact hmem (hval ▸ hj)
      simp [Array.getD, hjn, flipBit, hji]
    · simp [Array.getD, hjn]
  have hn := List.nodup_range.length_le_of_subset hsub
  rw [List.length_range] at hn
  exact Nat.le_trans hn hlen

end PnP.Lemmas.L_clb_005
