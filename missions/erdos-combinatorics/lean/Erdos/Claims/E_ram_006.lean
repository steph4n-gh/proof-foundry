import Erdos.Statements.E_ram_006

namespace Erdos.Claims.E_ram_006

private def adj13 (u v : Fin 13) : Bool :=
  let d := (u.val + 13 - v.val) % 13
  d == 1 || d == 5 || d == 8 || d == 12

private def graph13 : Erdos.SimpleGraph 13 where
  adj := adj13
  symm := by decide
  loopless := by decide

private def noIndep : Nat → Nat → List (Fin 13) → Bool
  | _, 0, _ => false
  | _, _ + 1, [] => true
  | 0, _ + 1, _ :: _ => false
  | fuel + 1, k + 1, x :: xs =>
    noIndep fuel k (xs.filter (fun y => !adj13 x y)) && noIndep fuel (k + 1) xs

private theorem noIndep_sound :
    ∀ (fuel k : Nat) (avail : List (Fin 13)), noIndep fuel k avail = true →
      ∀ S : List (Fin 13), S.length = k → S.Nodup →
        (∀ u ∈ S, u ∈ avail) →
        (∀ u ∈ S, ∀ v ∈ S, adj13 u v = false) → False
  | _, 0, _, h, _, _, _, _, _ => by simp [noIndep] at h
  | _, k + 1, [], _, S, hlen, _, hsub, _ => by
    cases S with
    | nil => simp at hlen
    | cons u _ => exact absurd (hsub u (List.mem_cons_self ..)) (List.not_mem_nil)
  | 0, _ + 1, _ :: _, h, _, _, _, _, _ => by simp [noIndep] at h
  | fuel + 1, k + 1, x :: xs, h, S, hlen, hnd, hsub, hind => by
    simp only [noIndep, Bool.and_eq_true] at h
    by_cases hxS : x ∈ S
    · let S' := S.erase x
      have hlen' : S'.length = k := by
        dsimp only [S']
        rw [List.length_erase_of_mem hxS]
        omega
      have hnd' : S'.Nodup := hnd.sublist List.erase_sublist
      have hsub' : ∀ u ∈ S', u ∈ xs.filter (fun y => !adj13 x y) := by
        intro u hu
        have huS : u ∈ S := List.erase_sublist.subset hu
        have hux : u ≠ x := by
          intro heq; subst heq
          have : ∀ {l : List (Fin 13)}, l.Nodup → u ∉ l.erase u := by
            intro l
            induction l with
            | nil => intro _; simp
            | cons a as ih =>
              intro hnda
              rw [List.nodup_cons] at hnda
              by_cases hau : a = u
              · subst hau; simp [hnda.1]
              · have hbeq : (a == u) = false := beq_false_of_ne hau
                simp [hbeq, Ne.symm hau, ih hnda.2]
          exact this hnd hu
        have huxs : u ∈ xs := by
          rcases List.mem_cons.mp (hsub u huS) with rfl | h'
          · exact absurd rfl hux
          · exact h'
        have hadj : adj13 x u = false := hind x hxS u huS
        exact List.mem_filter.mpr ⟨huxs, by simp [hadj]⟩
      have hind' : ∀ u ∈ S', ∀ v ∈ S', adj13 u v = false :=
        fun u hu v hv => hind u (List.erase_sublist.subset hu) v (List.erase_sublist.subset hv)
      exact noIndep_sound fuel k (xs.filter (fun y => !adj13 x y)) h.1 S' hlen' hnd' hsub' hind'
    · have hsub' : ∀ u ∈ S, u ∈ xs := by
        intro u hu
        rcases List.mem_cons.mp (hsub u hu) with rfl | h'
        · exact absurd hu hxS
        · exact h'
      exact noIndep_sound fuel (k + 1) xs h.2 S hlen hnd hsub' hind

private theorem noIndep5_ok : noIndep 13 5 (List.finRange 13) = true := by
  decide +kernel

private theorem noTriangle_ok :
    ∀ a b c : Fin 13, !(adj13 a b && adj13 b c && adj13 a c) = true := by
  decide +kernel

theorem ramsey35_gt_13 : Erdos.Statements.E_ram_006.Claim := by
  intro hram
  rcases hram graph13 with ⟨a, b, c, hab, hbc, hac⟩ |
    ⟨v0, v1, v2, v3, v4,
     h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
     a01, a02, a03, a04, a12, a13, a14, a23, a24, a34⟩
  · have h := noTriangle_ok a b c
    change adj13 a b = true at hab
    change adj13 b c = true at hbc
    change adj13 a c = true at hac
    simp [hab, hbc, hac] at h
  · refine noIndep_sound 13 5 (List.finRange 13) noIndep5_ok [v0, v1, v2, v3, v4] rfl ?_ ?_ ?_
    · simp [List.nodup_cons, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
    · intro u _; exact List.mem_finRange u
    · intro u hu v hv
      have hsym : ∀ u v, adj13 u v = adj13 v u := graph13.symm
      have hloop : ∀ v, adj13 v v = false := graph13.loopless
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl | rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hloop _
        | exact a01 | exact a02 | exact a03 | exact a04
        | exact a12 | exact a13 | exact a14
        | exact a23 | exact a24 | exact a34
        | (rw [hsym]; exact a01) | (rw [hsym]; exact a02) | (rw [hsym]; exact a03) | (rw [hsym]; exact a04)
        | (rw [hsym]; exact a12) | (rw [hsym]; exact a13) | (rw [hsym]; exact a14)
        | (rw [hsym]; exact a23) | (rw [hsym]; exact a24) | (rw [hsym]; exact a34)

end Erdos.Claims.E_ram_006
