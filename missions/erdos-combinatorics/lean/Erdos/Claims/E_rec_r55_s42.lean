import Erdos.Statements.E_rec_r55

namespace Erdos.Claims.E_rec_r55_s42

open Erdos

private def row42 (u : Nat) : Nat :=
  match u with
  | 0 => 1139573399136
  | 1 => 2500436905360
  | 2 => 1561790522080
  | 3 => 3123547570640
  | 4 => 3562820363146
  | 5 => 4114865099589
  | 6 => 2414515753773
  | 7 => 1586221114142
  | 8 => 3181056688890
  | 9 => 2030509228533
  | 10 => 2787047241731
  | 11 => 1945372390403
  | 12 => 202841631841
  | 13 => 2399245261972
  | 14 => 409566162066
  | 15 => 1774326471784
  | 16 => 1807214769546
  | 17 => 800857016419
  | 18 => 506521130131
  | 19 => 3129522453061
  | 20 => 3614406380653
  | 21 => 4149287660702
  | 22 => 74871674701
  | 23 => 1894305105695
  | 24 => 2708288572207
  | 25 => 1446286176897
  | 26 => 3162621600066
  | 27 => 2969010762834
  | 28 => 1596236953761
  | 29 => 2674997992774
  | 30 => 2049442270857
  | 31 => 4012357005076
  | 32 => 3909910581405
  | 33 => 3632353407086
  | 34 => 1184893368634
  | 35 => 2900723693109
  | 36 => 2767499215608
  | 37 => 1411929027060
  | 38 => 697785142158
  | 39 => 3684220768040
  | 40 => 2919817644725
  | 41 => 1768137696634
  | _ => 0

private def adj42 (u v : Fin 42) : Bool :=
  Nat.testBit (row42 u.val) v.val

private def coAdj42 (u v : Fin 42) : Bool :=
  (u != v) && !adj42 u v

private theorem adj42_symm : ∀ u v : Fin 42, adj42 u v = adj42 v u := by
  decide +kernel

private theorem adj42_loopless : ∀ v : Fin 42, adj42 v v = false := by
  decide +kernel

private theorem coAdj42_symm : ∀ u v : Fin 42, coAdj42 u v = coAdj42 v u := by
  decide +kernel

private def G42 : SimpleGraph 42 where
  adj := adj42
  symm := adj42_symm
  loopless := adj42_loopless

private def IsClique (edge : Fin 42 → Fin 42 → Bool) : List (Fin 42) → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, edge x y = true) ∧ IsClique edge xs

private theorem isClique_all_pairs {edge : Fin 42 → Fin 42 → Bool}
    (hsym : ∀ u v, edge u v = edge v u) :
    ∀ {c : List (Fin 42)}, IsClique edge c →
    ∀ {a b}, a ∈ c → b ∈ c → a ≠ b → edge a b = true
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, ⟨hx, hxs⟩, a, b, ha, hb, hne => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hx b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rw [hsym]; exact hx a ha'
      · exact isClique_all_pairs hsym hxs ha' hb' hne

private theorem isClique_erase {edge : Fin 42 → Fin 42 → Bool} :
    ∀ {c : List (Fin 42)} (x : Fin 42), IsClique edge c → IsClique edge (c.erase x)
  | [], _, _ => trivial
  | y :: ys, x, ⟨hy, hys⟩ => by
    simp only [List.erase_cons]
    split
    · exact hys
    · refine ⟨fun z hz => hy z (List.mem_of_mem_erase hz), isClique_erase x hys⟩

private theorem not_mem_erase_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α} {x : α}, l.Nodup → x ∉ l.erase x
  | [], _, _ => by simp
  | y :: ys, x, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.erase_cons]
    cases hxy : (y == x)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
      refine ⟨(fun h => by subst h; rw [beq_self_eq_true] at hxy; cases hxy), not_mem_erase_of_nodup hnd.2⟩
    · simp only [↓reduceIte]
      have : y = x := beq_iff_eq.mp hxy
      subst this
      exact hnd.1

private def noCliqueLoop (edge : Fin 42 → Fin 42 → Bool) (sub : List (Fin 42) → Bool) :
    List (Fin 42) → Bool
  | [] => true
  | x :: xs => sub (xs.filter (fun y => edge x y)) && noCliqueLoop edge sub xs

private def noClique (edge : Fin 42 → Fin 42 → Bool) : Nat → List (Fin 42) → Bool
  | 0, _ => false
  | k + 1, l => noCliqueLoop edge (noClique edge k) l

private theorem noCliqueLoop_sound (edge : Fin 42 → Fin 42 → Bool)
    (hsym : ∀ u v, edge u v = edge v u) (k : Nat)
    (sub : List (Fin 42) → Bool)
    (hsub_sound : ∀ l', sub l' = true →
      ∀ c' : List (Fin 42), c'.length = k → c'.Nodup → (∀ y ∈ c', y ∈ l') → IsClique edge c' → False) :
    ∀ l : List (Fin 42), noCliqueLoop edge sub l = true →
    ∀ c : List (Fin 42), c.length = k + 1 → c.Nodup → (∀ y ∈ c, y ∈ l) → IsClique edge c → False
  | [], _, c, hlen, _, hsub, _ => by
    cases c with
    | nil => simp at hlen
    | cons a _ => exact nomatch hsub a (List.mem_cons_self ..)
  | x :: xs, h, c, hlen, hnd, hsub, hcl => by
    simp only [noCliqueLoop, Bool.and_eq_true] at h
    by_cases hx : x ∈ c
    · have hcl' : IsClique edge (c.erase x) := isClique_erase x hcl
      have hnd' : (c.erase x).Nodup := hnd.erase x
      have hlen' : (c.erase x).length = k := by
        rw [List.length_erase_of_mem hx, hlen]; rfl
      have hsub' : ∀ y ∈ c.erase x, y ∈ xs.filter (fun y => edge x y) := by
        intro y hy
        have hyc : y ∈ c := List.mem_of_mem_erase hy
        have hne : x ≠ y := fun heq => not_mem_erase_of_nodup hnd (heq ▸ hy)
        have hyxs : y ∈ xs := by
          rcases List.mem_cons.mp (hsub y hyc) with rfl | h'
          · exact absurd rfl hne
          · exact h'
        exact List.mem_filter.mpr ⟨hyxs, isClique_all_pairs hsym hcl hx hyc hne⟩
      exact hsub_sound _ h.1 (c.erase x) hlen' hnd' hsub' hcl'
    · have hsub' : ∀ y ∈ c, y ∈ xs := by
        intro y hy
        rcases List.mem_cons.mp (hsub y hy) with rfl | h'
        · exact absurd hy hx
        · exact h'
      exact noCliqueLoop_sound edge hsym k sub hsub_sound xs h.2 c hlen hnd hsub' hcl

private theorem noClique_sound (edge : Fin 42 → Fin 42 → Bool)
    (hsym : ∀ u v, edge u v = edge v u) :
    ∀ (k : Nat) (l : List (Fin 42)), noClique edge k l = true →
    ∀ (c : List (Fin 42)), c.length = k → c.Nodup → (∀ y ∈ c, y ∈ l) → IsClique edge c → False
  | 0, _, h => fun _ _ _ _ _ => by simp [noClique] at h
  | k + 1, l, h => noCliqueLoop_sound edge hsym k (noClique edge k) (noClique_sound edge hsym k) l h

set_option maxHeartbeats 0 in
private theorem noK5_check : noClique adj42 5 (List.finRange 42) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem noI5_check : noClique coAdj42 5 (List.finRange 42) = true := by
  decide +kernel

private theorem ne_of_adj {u v : Fin 42} (h : adj42 u v = true) : u ≠ v := by
  intro heq; subst heq; rw [adj42_loopless] at h; cases h

private theorem no_k5 : ¬ HasK5 G42 := by
  rintro ⟨v0, v1, v2, v3, v4, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have hnd : [v0, v1, v2, v3, v4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨ne_of_adj h01, ne_of_adj h02, ne_of_adj h03, ne_of_adj h04⟩,
           ⟨ne_of_adj h12, ne_of_adj h13, ne_of_adj h14⟩,
           ⟨ne_of_adj h23, ne_of_adj h24⟩, ne_of_adj h34⟩
  have hcl : IsClique adj42 [v0, v1, v2, v3, v4] := by
    refine ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨(fun y hy => nomatch hy), trivial⟩⟩⟩⟩⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h01
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h02
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact h03
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact h04
            · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h12
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h13
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact h14
          · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h23
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h24
        · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h34
      · exact nomatch hy
  exact noClique_sound adj42 adj42_symm 5 (List.finRange 42) noK5_check
    [v0, v1, v2, v3, v4] rfl hnd (fun y _ => List.mem_finRange y) hcl

private theorem coAdj_of_ne_false {u v : Fin 42} (hne : u ≠ v) (hf : adj42 u v = false) :
    coAdj42 u v = true := by
  simp [coAdj42, bne_iff_ne, hne, hf]

private theorem no_i5 : ¬ HasIndep5 G42 := by
  rintro ⟨v0, v1, v2, v3, v4,
    n01, n02, n03, n04, n12, n13, n14, n23, n24, n34,
    f01, f02, f03, f04, f12, f13, f14, f23, f24, f34⟩
  have hnd : [v0, v1, v2, v3, v4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨n01, n02, n03, n04⟩, ⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩
  have hcl : IsClique coAdj42 [v0, v1, v2, v3, v4] := by
    refine ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨fun y hy => ?_, ⟨(fun y hy => nomatch hy), trivial⟩⟩⟩⟩⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact coAdj_of_ne_false n01 f01
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact coAdj_of_ne_false n02 f02
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact coAdj_of_ne_false n03 f03
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact coAdj_of_ne_false n04 f04
            · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact coAdj_of_ne_false n12 f12
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact coAdj_of_ne_false n13 f13
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact coAdj_of_ne_false n14 f14
          · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact coAdj_of_ne_false n23 f23
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact coAdj_of_ne_false n24 f24
        · exact nomatch hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact coAdj_of_ne_false n34 f34
      · exact nomatch hy
  exact noClique_sound coAdj42 coAdj42_symm 5 (List.finRange 42) noI5_check
    [v0, v1, v2, v3, v4] rfl hnd (fun y _ => List.mem_finRange y) hcl

theorem record : Erdos.Statements.E_rec_r55.Record 42 :=
  ⟨42, G42, Nat.le_refl 42, no_k5, no_i5⟩

end Erdos.Claims.E_rec_r55_s42
