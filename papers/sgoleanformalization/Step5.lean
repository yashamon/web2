/- Step5.lean — Step 2 (untrapped components are live) and Step 5 (no
   two dead components are adjacent: adjacent dead stones share their
   A⁺ component). The die-at analysis of def_diesat, per stone. -/
import Step1
open SgoDisplay

variable {n : Nat}

/-! ### Step 2. -/

theorem step2_untrapped_live (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z0 : Nat) (hz0 : z0 < n*n)
    (hocc0 : occD (jointPlaced n A i0 i1) z0 = true)
    (huntrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) z0) = false) :
    ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      c1.get q = (jointPlaced n A i0 i1).get q := by
  rcases step1_dichotomy A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
    z0 hz0 hocc0 with h | ⟨_, htrap⟩
  · exact h
  · rw [htrap] at huntrap
    exact Bool.noConfusion huntrap

/-! ### The die-at classification (def_diesat, per stone). -/

theorem died_classify (base : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n base c i = some r) (z : Nat)
    (hz : z < n*n)
    (hoccP : occD (placedN n base c i) z = true)
    (hrem : occD r z = false) :
    z ∈ deadOppN n base c i ∨
    (suicideN n base c i = true ∧ z ∈ ownCompN n base c i) := by
  have hres := goMoveN_result base c i r hr
  by_cases hzd : z ∈ deadOppN n base c i
  · exact Or.inl hzd
  · right
    have hznotd : ¬ (deadOppN n base c i).contains z = true :=
      fun hcont => hzd (List.contains_iff_mem.mp hcont)
    have hsz : suicideN n base c i = true := by
      cases hs : suicideN n base c i
      · exfalso
        have hocc : occD r z = true := by
          rw [hres]
          split
          · next hstrue =>
            rw [hs] at hstrue
            exact Bool.noConfusion hstrue
          · rw [occD_afterCapN base c i z hz, if_neg hznotd]
            exact hoccP
        rw [hocc] at hrem
        exact Bool.noConfusion hrem
      · rfl
    refine ⟨hsz, ?_⟩
    rw [hres, if_pos hsz, occD_erasedN base c i z hz] at hrem
    cases ho : (ownCompN n base c i).contains z
    · exfalso
      rw [ho] at hrem
      simp only [Bool.false_eq_true, if_false] at hrem
      rw [occD_afterCapN base c i z hz, if_neg hznotd] at hrem
      rw [hoccP] at hrem
      exact Bool.noConfusion hrem
    · exact List.contains_iff_mem.mp ho

/-! ### Colors on A⁺. -/

theorem joint_kind_bw (A : Display n) (i0 i1 : Nat)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hclass : IsClassical A) (q : Nat)
    (hq : occD (jointPlaced n A i0 i1) q = true) :
    kindAt (jointPlaced n A i0 i1) q = some .b ∨
    kindAt (jointPlaced n A i0 i1) q = some .w := by
  by_cases h1 : q = i1
  · subst q
    exact Or.inr (kindAt_joint_i1 A i0 i1 hwf hi1)
  · by_cases h0 : q = i0
    · subst q
      exact Or.inl (kindAt_joint_i0 A i0 i1 hwf hi0 hne)
    · have hqA : occD A q = true := by
        rw [← occD_joint_other A i0 i1 q h0 h1]
        exact hq
      rcases kind_some_of_occ hqA with ⟨k, hk⟩
      have hkj : kindAt (jointPlaced n A i0 i1) q = some k := by
        rw [kindAt_joint_other A i0 i1 q h0 h1]
        exact hk
      cases k with
      | b => exact Or.inl hkj
      | w => exact Or.inr hkj
      | r => exact absurd hk (hclass q)

/-! ### One-move contradictions. -/

/-- A dead-list stone adjacent to an own-component stone defeats the
    suicide condition: its emptied cell is a liberty. -/
theorem own_dead_adjacent_contra (base : Display n) (c : DKind) (i : Nat)
    (t z : Nat) (ht : t < n*n)
    (htd : t ∈ deadOppN n base c i)
    (hzo : z ∈ ownCompN n base c i)
    (hsui : suicideN n base c i = true)
    (hadj : adjI n t z = true) : False := by
  have htCB : occD (afterCapN n base c i) t = false := by
    rw [occD_afterCapN base c i t ht,
      if_pos (List.contains_iff_mem.mpr htd)]
  have hlib : noLibD (afterCapN n base c i)
      (componentD (afterCapN n base c i) i) = false :=
    (noLibD_eq_false_iff _ _).mpr
      ⟨t, List.mem_range.mpr ht, htCB, z, hzo, hadj⟩
  unfold suicideN ownCompN at hsui
  rw [hsui] at hlib
  exact Bool.noConfusion hlib

/-- Reading A⁺ kinds on the first move's board (off i1). -/
theorem kind_joint_PB0 (A : Display n) (i0 i1 z : Nat) (hz1 : z ≠ i1) :
    kindAt (jointPlaced n A i0 i1) z = kindAt (placedN n A .b i0) z := by
  unfold kindAt
  rw [joint_vs_PB0 A i0 i1 z hz1]

/-- The Step 5 core: adjacent stones dying at different moves cannot
    exist — the first-move victim's cell is a liberty of the
    second-move victim's component in the second placed diagram. -/
theorem dieat_mixed_contra (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hi1 : i1 < n*n) (hne : i0 ≠ i1) (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (x y : Nat) (hx : x < n*n) (hy : y < n*n)
    (hxP : occD (placedN n A .b i0) x = true)
    (hxdead : occD d1 x = false)
    (hyP : occD (placedN n d1 .w i1) y = true)
    (hydead : occD c1 y = false)
    (hadj : adjI n x y = true) : False := by
  have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
  have hnl := (goMoveN_removed d1 .w i1 c1 hwfd1 hi1 (by decide) hb2
    y hy hyP hydead).1
  have hxi1 : x ≠ i1 := by
    intro h
    subst x
    rw [occD_placedN_ne A .b i0 i1 (fun hh => hne hh.symm), hi1A] at hxP
    exact Bool.noConfusion hxP
  have hxPB1 : occD (placedN n d1 .w i1) x = false := by
    rw [occD_placedN_ne d1 .w i1 x hxi1]
    exact hxdead
  rcases kind_some_of_occ hyP with ⟨k, hk⟩
  have hlib : noLibD (placedN n d1 .w i1)
      (componentD (placedN n d1 .w i1) y) = false :=
    (noLibD_eq_false_iff _ _).mpr
      ⟨x, List.mem_range.mpr hx, hxPB1, y, componentD_mem_self _ y k hk,
        hadj⟩
  rw [hnl] at hlib
  exact Bool.noConfusion hlib

/-- Both stones die at the first move, opposite colors: the white one
    is captured, the black one suicided, and the emptied capture is a
    liberty at the suicide condition. -/
theorem both_die_m0_contra (A : Display n) (i0 : Nat) (d1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n)
    (hb1 : goMoveN n A .b i0 = some d1)
    (sw sb : Nat) (hsw : sw < n*n) (hsb : sb < n*n)
    (hkw : kindAt (placedN n A .b i0) sw = some .w)
    (hkb : kindAt (placedN n A .b i0) sb = some .b)
    (hswP : occD (placedN n A .b i0) sw = true)
    (hsbP : occD (placedN n A .b i0) sb = true)
    (hswd : occD d1 sw = false) (hsbd : occD d1 sb = false)
    (hadj : adjI n sw sb = true) : False := by
  have hcw := died_classify A .b i0 d1 hb1 sw hsw hswP hswd
  have hcb := died_classify A .b i0 d1 hb1 sb hsb hsbP hsbd
  -- the white stone is captured
  have hswdead : sw ∈ deadOppN n A .b i0 := by
    rcases hcw with h | ⟨_, hown⟩
    · exact h
    · exfalso
      have hroot : kindAt (afterCapN n A .b i0) i0 = some .b :=
        kindAt_afterCapN_self A .b i0 hwf hi0 (by decide)
      have : kindAt (afterCapN n A .b i0) sw = some .b :=
        componentD_kind _ i0 .b hroot sw hown
      have hpb : kindAt (placedN n A .b i0) sw = some .b :=
        (kind_c_agree_afterCapN A .b i0 (by decide) sw
          (List.mem_range.mpr hsw)).mpr this
      rw [hkw] at hpb
      exact DKind.noConfusion (Option.some.inj hpb)
  -- the black stone is suicided
  rcases hcb with h | ⟨hsui, hown⟩
  · exfalso
    rcases (mem_deadOppN_iff A .b i0 sb).mp h with ⟨_, hk, _⟩
    rw [hkb] at hk
    exact DKind.noConfusion (Option.some.inj hk)
  · exact own_dead_adjacent_contra A .b i0 sw sb hsw hswdead hown hsui hadj

/-- Both stones die at the second move, opposite colors: mirror. -/
theorem both_die_m1_contra (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n) (hi1 : i1 < n*n)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (sw sb : Nat) (hsw : sw < n*n) (hsb : sb < n*n)
    (hkw : kindAt (placedN n d1 .w i1) sw = some .w)
    (hkb : kindAt (placedN n d1 .w i1) sb = some .b)
    (hswP : occD (placedN n d1 .w i1) sw = true)
    (hsbP : occD (placedN n d1 .w i1) sb = true)
    (hswd : occD c1 sw = false) (hsbd : occD c1 sb = false)
    (hadj : adjI n sb sw = true) : False := by
  have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
  have hcw := died_classify d1 .w i1 c1 hb2 sw hsw hswP hswd
  have hcb := died_classify d1 .w i1 c1 hb2 sb hsb hsbP hsbd
  -- the black stone is captured
  have hsbdead : sb ∈ deadOppN n d1 .w i1 := by
    rcases hcb with h | ⟨_, hown⟩
    · exact h
    · exfalso
      have hroot : kindAt (afterCapN n d1 .w i1) i1 = some .w :=
        kindAt_afterCapN_self d1 .w i1 hwfd1 hi1 (by decide)
      have : kindAt (afterCapN n d1 .w i1) sb = some .w :=
        componentD_kind _ i1 .w hroot sb hown
      have hpb : kindAt (placedN n d1 .w i1) sb = some .w :=
        (kind_c_agree_afterCapN d1 .w i1 (by decide) sb
          (List.mem_range.mpr hsb)).mpr this
      rw [hkb] at hpb
      exact DKind.noConfusion (Option.some.inj hpb)
  -- the white stone is suicided
  rcases hcw with h | ⟨hsui, hown⟩
  · exfalso
    rcases (mem_deadOppN_iff d1 .w i1 sw).mp h with ⟨_, hk, _⟩
    rw [hkw] at hk
    exact DKind.noConfusion (Option.some.inj hk)
  · exact own_dead_adjacent_contra d1 .w i1 sb sw hsb hsbdead hown hsui hadj

/-! ### Step 5: adjacent dead stones share their A⁺ component. -/

theorem step5_adjacent_dead_same_comp (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false) (hclass : IsClassical A)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (t z : Nat) (ht : t < n*n) (hz : z < n*n)
    (htP : occD (jointPlaced n A i0 i1) t = true)
    (hzP : occD (jointPlaced n A i0 i1) z = true)
    (htdead : occD c1 t = false) (hzdead : occD c1 z = false)
    (hadj : adjI n t z = true) :
    z ∈ componentD (jointPlaced n A i0 i1) t := by
  by_cases hksame : kindAt (jointPlaced n A i0 i1) z
      = kindAt (jointPlaced n A i0 i1) t
  · rcases kind_some_of_occ htP with ⟨k, hkt⟩
    exact componentD_maximal (jointPlaced n A i0 i1) t k hkt z
      (List.mem_range.mpr hz) (hksame.trans hkt) t
      (componentD_mem_self _ t k hkt) (adjI_symm hadj)
  · exfalso
    -- classify each stone's death move
    have hclassify : ∀ s, s < n*n →
        occD (jointPlaced n A i0 i1) s = true → occD c1 s = false →
        (s ≠ i1 ∧ occD (placedN n A .b i0) s = true ∧
          occD d1 s = false) ∨
        (occD (placedN n d1 .w i1) s = true) := by
      intro s hs hsP hsdead
      by_cases hs1 : s = i1
      · right
        subst s
        have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
        exact occD_of_kind (kindAt_placedN_self d1 .w i1 hwfd1 hi1)
      · have hsPB0 : occD (placedN n A .b i0) s = true := by
          unfold occD at hsP ⊢
          rw [← joint_vs_PB0 A i0 i1 s hs1]
          exact hsP
        cases hd1s : occD d1 s with
        | false => exact Or.inl ⟨hs1, hsPB0, rfl⟩
        | true =>
          right
          rw [occD_placedN_ne d1 .w i1 s hs1]
          exact hd1s
    -- kinds are black or white, and differ
    rcases joint_kind_bw A i0 i1 hwf hi0 hi1 hne hclass t htP with htb | htw <;>
      rcases joint_kind_bw A i0 i1 hwf hi0 hi1 hne hclass z hzP with hzb | hzw
    -- goals in order: (t b, z b), (t b, z w), (t w, z b), (t w, z w)
    · exact hksame (hzb.trans htb.symm)
    -- t black, z white
    ·
      rcases hclassify t ht htP htdead with ⟨ht1, htPB0, htd1⟩ | htPB1 <;>
        rcases hclassify z hz hzP hzdead with ⟨hz1, hzPB0, hzd1⟩ | hzPB1
      · -- both die at m0: sw := z, sb := t
        exact both_die_m0_contra A i0 d1 hwf hi0 hb1 z t hz ht
          ((kind_joint_PB0 A i0 i1 z hz1).symm.trans hzw)
          ((kind_joint_PB0 A i0 i1 t ht1).symm.trans htb)
          hzPB0 htPB0 hzd1 htd1 (adjI_symm hadj)
      · -- t at m0, z at m1
        exact dieat_mixed_contra A i0 i1 d1 c1 hi1 hne hi1A hb1 hb2
          t z ht hz htPB0 htd1 hzPB1 hzdead hadj
      · -- z at m0, t at m1
        exact dieat_mixed_contra A i0 i1 d1 c1 hi1 hne hi1A hb1 hb2
          z t hz ht hzPB0 hzd1 htPB1 htdead (adjI_symm hadj)
      · -- both at m1: sw := z, sb := t; adjacency sb sw = adjI t z
        exact both_die_m1_contra A i0 i1 d1 c1 hi1 hb1 hb2 z t hz ht
          ((kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 z hzPB1).trans hzw)
          ((kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 t htPB1).trans htb)
          hzPB1 htPB1 hzdead htdead hadj
    -- t white, z black
    ·
      rcases hclassify t ht htP htdead with ⟨ht1, htPB0, htd1⟩ | htPB1 <;>
        rcases hclassify z hz hzP hzdead with ⟨hz1, hzPB0, hzd1⟩ | hzPB1
      · exact both_die_m0_contra A i0 d1 hwf hi0 hb1 t z ht hz
          ((kind_joint_PB0 A i0 i1 t ht1).symm.trans htw)
          ((kind_joint_PB0 A i0 i1 z hz1).symm.trans hzb)
          htPB0 hzPB0 htd1 hzd1 hadj
      · exact dieat_mixed_contra A i0 i1 d1 c1 hi1 hne hi1A hb1 hb2
          t z ht hz htPB0 htd1 hzPB1 hzdead hadj
      · exact dieat_mixed_contra A i0 i1 d1 c1 hi1 hne hi1A hb1 hb2
          z t hz ht hzPB0 hzd1 htPB1 htdead (adjI_symm hadj)
      · exact both_die_m1_contra A i0 i1 d1 c1 hi1 hb1 hb2 t z ht hz
          ((kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 t htPB1).trans htw)
          ((kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 z hzPB1).trans hzb)
          htPB1 hzPB1 htdead hzdead (adjI_symm hadj)
    · exact hksame (hzw.trans htw.symm)
