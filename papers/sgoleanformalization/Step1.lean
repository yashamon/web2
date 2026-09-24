/- Step1.lean — the removal dichotomy of the printed Step 1: every
   component of the joint placed diagram A⁺ stands entire in the
   composite or is entirely empty there, and an empty one is trapped
   in A⁺. Engine: Infra5's per-move removal + the block. -/
import Infra5
open SgoDisplay

variable {n : Nat}

/-- The joint placed diagram A⁺ (Black at i0, then White at i1;
    placements commute cell-wise for i0 ≠ i1). -/
def jointPlaced (n : Nat) (A : Display n) (i0 i1 : Nat) : Display n :=
  placedN n (placedN n A .b i0) .w i1

/-! ### Sizes. -/

theorem set_size (D : Display n) (i : Nat) (c : Cell) :
    (D.set i c).cells.size = D.cells.size := by
  unfold Display.set
  exact Array.size_setIfInBounds _ _ _

theorem WFD_placedN (A : Display n) (c : DKind) (i : Nat)
    (hwf : WFD A) : WFD (placedN n A c i) := by
  unfold WFD placedN
  rw [set_size]
  exact hwf

/-! ### Reading A⁺. -/

theorem kindAt_joint_i1 (A : Display n) (i0 i1 : Nat)
    (hwf : WFD A) (hi1 : i1 < n*n) :
    kindAt (jointPlaced n A i0 i1) i1 = some .w :=
  kindAt_placedN_self (placedN n A .b i0) .w i1
    (WFD_placedN A .b i0 hwf) hi1

theorem kindAt_joint_i0 (A : Display n) (i0 i1 : Nat)
    (hwf : WFD A) (hi0 : i0 < n*n) (hne : i0 ≠ i1) :
    kindAt (jointPlaced n A i0 i1) i0 = some .b := by
  unfold jointPlaced
  rw [kindAt_placedN_ne _ .w i1 i0 hne]
  exact kindAt_placedN_self A .b i0 hwf hi0

theorem kindAt_joint_other (A : Display n) (i0 i1 z : Nat)
    (hz0 : z ≠ i0) (hz1 : z ≠ i1) :
    kindAt (jointPlaced n A i0 i1) z = kindAt A z := by
  unfold jointPlaced
  rw [kindAt_placedN_ne _ .w i1 z hz1, kindAt_placedN_ne A .b i0 z hz0]

theorem occD_joint_other (A : Display n) (i0 i1 z : Nat)
    (hz0 : z ≠ i0) (hz1 : z ≠ i1) :
    occD (jointPlaced n A i0 i1) z = occD A z := by
  unfold jointPlaced
  rw [occD_placedN_ne _ .w i1 z hz1, occD_placedN_ne A .b i0 z hz0]

/-- A⁺ agrees with the first move's placed diagram off i1. -/
theorem joint_vs_PB0 (A : Display n) (i0 i1 z : Nat) (hz1 : z ≠ i1) :
    (jointPlaced n A i0 i1).get z = (placedN n A .b i0).get z := by
  unfold jointPlaced placedN
  exact get_set_ne _ i1 z _ hz1

/-! ### Standing cells keep their values. -/

/-- A cell occupied in a move's output carries the placed diagram's
    cell. -/
theorem goMoveN_standing (d : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n d c i = some r) (z : Nat)
    (hocc : occD r z = true) :
    r.get z = (placedN n d c i).get z := by
  rcases goMoveN_get d c i r hr z with h | h
  · unfold occD at hocc
    rw [h] at hocc
    exact absurd hocc (by simp)
  · exact h

/-! ### Output sizes. -/

theorem afterCapN_size (A : Display n) (c : DKind) (i : Nat) :
    (afterCapN n A c i).cells.size = n*n := by
  unfold afterCapN
  simp [Array.size_map, Array.size_range]

theorem erasedN_size (A : Display n) (c : DKind) (i : Nat) :
    (erasedN n A c i).cells.size = n*n := by
  unfold erasedN
  simp [Array.size_map, Array.size_range]

theorem goMoveN_size (d : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n d c i = some r) :
    r.cells.size = n*n := by
  rw [goMoveN_result d c i r hr]
  split
  · exact erasedN_size d c i
  · exact afterCapN_size d c i

/-- A standing stone of the composite carries its A⁺ cell. -/
theorem composite_standing_cell (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n) (hwf : WFD A) (hi1 : i1 < n*n)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z : Nat) (hocc : occD c1 z = true) :
    c1.get z = (jointPlaced n A i0 i1).get z := by
  rw [goMoveN_standing d1 .w i1 c1 hb2 z hocc]
  by_cases hz1 : z = i1
  · subst z
    have h1 : (placedN n d1 .w i1).get i1 = some (.w, 0) := by
      unfold placedN
      exact get_set_self d1 i1 _
        (by rw [goMoveN_size A .b i0 d1 hb1]; exact hi1)
    have h2 : (jointPlaced n A i0 i1).get i1 = some (.w, 0) := by
      unfold jointPlaced placedN
      exact get_set_self _ i1 _ (by rw [set_size, hwf]; exact hi1)
    rw [h1, h2]
  · have hLHS : (placedN n d1 .w i1).get z = d1.get z := by
      unfold placedN
      exact get_set_ne d1 i1 z _ hz1
    rw [hLHS, joint_vs_PB0 A i0 i1 z hz1]
    have hoccd1 : occD d1 z = true := by
      have hcell := goMoveN_standing d1 .w i1 c1 hb2 z hocc
      unfold occD at hocc ⊢
      rw [hcell, hLHS] at hocc
      exact hocc
    exact goMoveN_standing A .b i0 d1 hb1 z hoccd1

/-! ### Persistence and the removal source. -/

/-- An A⁺-side stone emptied by the first move stays empty in the
    composite (the printed "in particular"). -/
theorem persist_PB0 (A : Display n) (i0 i1 : Nat) (d1 c1 : Display n)
    (hne : i0 ≠ i1) (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z : Nat)
    (hoccP : occD (placedN n A .b i0) z = true)
    (hempd1 : occD d1 z = false) :
    occD c1 z = false := by
  by_cases hz0 : z = i0
  · subst z
    exact block_persist_placement A i0 i1 d1 c1 hne hb1 hb2 hempd1
  · have hoccA : occD A z = true := by
      rw [← occD_placedN_ne A .b i0 z hz0]
      exact hoccP
    have hzi1 : z ≠ i1 := by
      intro h
      rw [h, hi1A] at hoccA
      exact Bool.noConfusion hoccA
    exact goMoveN_fills_only d1 .w i1 z c1 hb2 hempd1 hzi1

/-- Where a removed A⁺ stone died: in a component of the first move's
    placed diagram, or of the second's — trapped there, and entirely
    empty in the composite either way. -/
theorem removal_source (A : Display n) (i0 i1 : Nat) (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (w : Nat) (hw : w < n*n)
    (hoccw : occD (jointPlaced n A i0 i1) w = true)
    (hempw : occD c1 w = false) :
    (occD (placedN n A .b i0) w = true ∧
      noLibD (placedN n A .b i0) (componentD (placedN n A .b i0) w) = true ∧
      ∀ q, q ∈ componentD (placedN n A .b i0) w → occD c1 q = false) ∨
    (occD (placedN n d1 .w i1) w = true ∧
      noLibD (placedN n d1 .w i1) (componentD (placedN n d1 .w i1) w) = true ∧
      ∀ q, q ∈ componentD (placedN n d1 .w i1) w → occD c1 q = false) := by
  have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
  by_cases hz1 : w = i1
  · subst w
    right
    have hoccP : occD (placedN n d1 .w i1) i1 = true :=
      occD_of_kind (kindAt_placedN_self d1 .w i1 hwfd1 hi1)
    rcases goMoveN_removed d1 .w i1 c1 hwfd1 hi1 (by decide) hb2 i1 hi1
      hoccP hempw with ⟨hnl, hall⟩
    exact ⟨hoccP, hnl, hall⟩
  · have hoccPB0 : occD (placedN n A .b i0) w = true := by
      unfold occD at hoccw ⊢
      rw [← joint_vs_PB0 A i0 i1 w hz1]
      exact hoccw
    cases hd1w : occD d1 w with
    | true =>
      right
      have hoccPB1 : occD (placedN n d1 .w i1) w = true := by
        rw [occD_placedN_ne d1 .w i1 w hz1]
        exact hd1w
      rcases goMoveN_removed d1 .w i1 c1 hwfd1 hi1 (by decide) hb2 w hw
        hoccPB1 hempw with ⟨hnl, hall⟩
      exact ⟨hoccPB1, hnl, hall⟩
    | false =>
      left
      rcases goMoveN_removed A .b i0 d1 hwf hi0 (by decide) hb1 w hw
        hoccPB0 hd1w with ⟨hnl, hall⟩
      refine ⟨hoccPB0, hnl, ?_⟩
      intro q hq
      -- q is a PB0 stone emptied by move 0; persist to the composite
      rcases kind_some_of_occ hoccPB0 with ⟨k, hk⟩
      have hqocc : occD (placedN n A .b i0) q = true :=
        occD_of_kind (componentD_kind _ w k hk q hq)
      exact persist_PB0 A i0 i1 d1 c1 hne hi1A hb1 hb2 q hqocc (hall q hq)

/-! ### The crossing pair contradiction. -/

/-- A second-move-board stone reads its A⁺ kind. -/
theorem kind_PB1_joint (A : Display n) (i0 i1 : Nat) (d1 : Display n)
    (hwf : WFD A) (hi1 : i1 < n*n)
    (hb1 : goMoveN n A .b i0 = some d1)
    (x : Nat) (hx : occD (placedN n d1 .w i1) x = true) :
    kindAt (placedN n d1 .w i1) x = kindAt (jointPlaced n A i0 i1) x := by
  have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
  by_cases hx1 : x = i1
  · subst x
    rw [kindAt_placedN_self d1 .w i1 hwfd1 hi1,
      kindAt_joint_i1 A i0 i1 hwf hi1]
  · rw [kindAt_placedN_ne d1 .w i1 x hx1]
    have hoccd1 : occD d1 x = true := by
      rw [← occD_placedN_ne d1 .w i1 x hx1]
      exact hx
    have hcell := goMoveN_standing A .b i0 d1 hb1 x hoccd1
    unfold kindAt
    rw [hcell, joint_vs_PB0 A i0 i1 x hx1]

/-- Adjacent same-kind A⁺ stones share their fate in the composite:
    one standing and one empty is impossible. -/
theorem step1_pair (A : Display n) (i0 i1 : Nat) (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z w : Nat) (hzb : z < n*n) (hwb : w < n*n)
    (hk : kindAt (jointPlaced n A i0 i1) z
      = kindAt (jointPlaced n A i0 i1) w)
    (hwocc : occD (jointPlaced n A i0 i1) w = true)
    (hadj : adjI n z w = true)
    (hzocc : occD c1 z = true) (hwemp : occD c1 w = false) : False := by
  rcases kind_some_of_occ hwocc with ⟨kw, hkw⟩
  have hkz : kindAt (jointPlaced n A i0 i1) z = some kw := by
    rw [hk]; exact hkw
  rcases removal_source A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
    w hwb hwocc hwemp with ⟨hoccQ, hnl, hall⟩ | ⟨hoccQ, hnl, hall⟩
  · -- died at the first move: R lives on PB0
    have hwi1 : w ≠ i1 := by
      intro h
      subst w
      rw [occD_placedN_ne A .b i0 i1 (fun hh => hne hh.symm), hi1A] at hoccQ
      exact Bool.noConfusion hoccQ
    have hkPB0w : kindAt (placedN n A .b i0) w = some kw := by
      unfold kindAt
      rw [← joint_vs_PB0 A i0 i1 w hwi1]
      exact hkw
    have hwR : w ∈ componentD (placedN n A .b i0) w :=
      componentD_mem_self _ w kw hkPB0w
    by_cases hz1 : z = i1
    · -- z is m1's stone: its intersection is a liberty of R in PB0
      subst z
      have hempPB0i1 : occD (placedN n A .b i0) i1 = false := by
        rw [occD_placedN_ne A .b i0 i1 (fun hh => hne hh.symm)]
        exact hi1A
      have hlib : noLibD (placedN n A .b i0)
          (componentD (placedN n A .b i0) w) = false :=
        (noLibD_eq_false_iff _ _).mpr
          ⟨i1, List.mem_range.mpr hi1, hempPB0i1, w, hwR, hadj⟩
      rw [hnl] at hlib
      exact Bool.noConfusion hlib
    · -- z is a PB0 stone of R's kind adjacent to R: it lies in R
      have hkPB0z : kindAt (placedN n A .b i0) z = some kw := by
        unfold kindAt
        rw [← joint_vs_PB0 A i0 i1 z hz1]
        exact hkz
      have hzR : z ∈ componentD (placedN n A .b i0) w :=
        componentD_maximal (placedN n A .b i0) w kw hkPB0w z
          (List.mem_range.mpr hzb) hkPB0z w hwR hadj
      have := hall z hzR
      rw [hzocc] at this
      exact Bool.noConfusion this
  · -- died at the second move: R lives on PB1; a c1 stone is a PB1 stone
    have hoccPB1z : occD (placedN n d1 .w i1) z = true := by
      have hcell := goMoveN_standing d1 .w i1 c1 hb2 z hzocc
      unfold occD at hzocc ⊢
      rw [← hcell]
      exact hzocc
    have hkPB1w : kindAt (placedN n d1 .w i1) w = some kw := by
      rw [kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 w hoccQ]
      exact hkw
    have hkPB1z : kindAt (placedN n d1 .w i1) z = some kw := by
      rw [kind_PB1_joint A i0 i1 d1 hwf hi1 hb1 z hoccPB1z]
      exact hkz
    have hwR : w ∈ componentD (placedN n d1 .w i1) w :=
      componentD_mem_self _ w kw hkPB1w
    have hzR : z ∈ componentD (placedN n d1 .w i1) w :=
      componentD_maximal (placedN n d1 .w i1) w kw hkPB1w z
        (List.mem_range.mpr hzb) hkPB1z w hwR hadj
    have := hall z hzR
    rw [hzocc] at this
    exact Bool.noConfusion this

/-! ### Uniformity along components. -/

theorem occ_PB0_le_joint (A : Display n) (i0 i1 : Nat)
    (hwf : WFD A) (hi1 : i1 < n*n) (x : Nat)
    (hx : occD (placedN n A .b i0) x = true) :
    occD (jointPlaced n A i0 i1) x = true := by
  by_cases hx1 : x = i1
  · subst x
    exact occD_of_kind (kindAt_joint_i1 A i0 i1 hwf hi1)
  · unfold occD
    rw [joint_vs_PB0 A i0 i1 x hx1]
    exact hx

theorem occ_PB1_le_joint (A : Display n) (i0 i1 : Nat) (d1 : Display n)
    (hwf : WFD A) (hi1 : i1 < n*n)
    (hb1 : goMoveN n A .b i0 = some d1) (x : Nat)
    (hx : occD (placedN n d1 .w i1) x = true) :
    occD (jointPlaced n A i0 i1) x = true := by
  by_cases hx1 : x = i1
  · subst x
    exact occD_of_kind (kindAt_joint_i1 A i0 i1 hwf hi1)
  · have hoccd1 : occD d1 x = true := by
      rw [← occD_placedN_ne d1 .w i1 x hx1]
      exact hx
    have hcell := goMoveN_standing A .b i0 d1 hb1 x hoccd1
    apply occ_PB0_le_joint A i0 i1 hwf hi1 x
    unfold occD at hoccd1 ⊢
    rw [← hcell]
    exact hoccd1

/-- The composite's occupancy is constant on each A⁺ component. -/
theorem step1_uniform (A : Display n) (i0 i1 : Nat) (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z0 : Nat) (hz0 : z0 < n*n)
    (hocc0 : occD (jointPlaced n A i0 i1) z0 = true)
    (q : Nat) (hq : q ∈ componentD (jointPlaced n A i0 i1) z0) :
    occD c1 q = occD c1 z0 := by
  rcases kind_some_of_occ hocc0 with ⟨k, hk0⟩
  have hconn := (componentD_mem_iff (jointPlaced n A i0 i1) z0 k hk0 q).mp hq
  clear hq
  induction hconn with
  | refl => rfl
  | step hc hqi hqk hadj ih =>
    next j q' =>
    have hkj : kindAt (jointPlaced n A i0 i1) j = some k :=
      ConnK_kind hk0 hc
    have hjb : j ∈ allIdx n :=
      ConnK_board (List.mem_range.mpr hz0) hc
    have hjocc : occD (jointPlaced n A i0 i1) j = true :=
      occD_of_kind hkj
    have hq'occ : occD (jointPlaced n A i0 i1) q' = true :=
      occD_of_kind hqk
    cases hcq : occD c1 q' with
    | false =>
      cases hcj : occD c1 j with
      | false =>
        rw [hcj] at ih
        exact ih
      | true =>
        exact (step1_pair A i0 i1 d1 c1 hwf hi0 hi1
          hne hi1A hb1 hb2 j q' (List.mem_range.mp hjb)
          (List.mem_range.mp hqi)
          (by rw [hkj, hqk]) hq'occ (adjI_symm hadj) hcj hcq).elim
    | true =>
      cases hcj : occD c1 j with
      | false =>
        exact (step1_pair A i0 i1 d1 c1 hwf hi0 hi1
          hne hi1A hb1 hb2 q' j (List.mem_range.mp hqi)
          (List.mem_range.mp hjb)
          (by rw [hkj, hqk]) hjocc hadj hcq hcj).elim
      | true =>
        rw [hcj] at ih
        exact ih

/-! ### Step 1, the removal dichotomy. -/

theorem step1_dichotomy (A : Display n) (i0 i1 : Nat) (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z0 : Nat) (hz0 : z0 < n*n)
    (hocc0 : occD (jointPlaced n A i0 i1) z0 = true) :
    (∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      c1.get q = (jointPlaced n A i0 i1).get q) ∨
    ((∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
        occD c1 q = false) ∧
      noLibD (jointPlaced n A i0 i1)
        (componentD (jointPlaced n A i0 i1) z0) = true) := by
  rcases kind_some_of_occ hocc0 with ⟨k, hk0⟩
  cases hfate : occD c1 z0 with
  | true =>
    left
    intro q hq
    have hqocc : occD c1 q = true := by
      rw [step1_uniform A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
        z0 hz0 hocc0 q hq]
      exact hfate
    exact composite_standing_cell A i0 i1 d1 c1 hwf hi1 hb1 hb2 q hqocc
  | false =>
    right
    have hallemp : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
        occD c1 q = false := by
      intro q hq
      rw [step1_uniform A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
        z0 hz0 hocc0 q hq]
      exact hfate
    refine ⟨hallemp, ?_⟩
    cases hnl : noLibD (jointPlaced n A i0 i1)
        (componentD (jointPlaced n A i0 i1) z0) with
    | true => rfl
    | false =>
      exfalso
      rcases (noLibD_eq_false_iff _ _).mp hnl with
        ⟨lib, hlibb, hlibemp, r, hrC, hadjlr⟩
      have hrk : kindAt (jointPlaced n A i0 i1) r = some k :=
        componentD_kind _ z0 k hk0 r hrC
      have hrb : r ∈ allIdx n := componentD_board (List.mem_range.mpr hz0)
        hk0 hrC
      have hrocc : occD (jointPlaced n A i0 i1) r = true := occD_of_kind hrk
      have hremp : occD c1 r = false := hallemp r hrC
      rcases removal_source A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
        r (List.mem_range.mp hrb) hrocc hremp with
        ⟨hoccQ, hnlQ, _⟩ | ⟨hoccQ, hnlQ, _⟩
      · have hlibQ : occD (placedN n A .b i0) lib = false := by
          cases hlq : occD (placedN n A .b i0) lib with
          | false => rfl
          | true =>
            have := occ_PB0_le_joint A i0 i1 hwf hi1 lib hlq
            rw [hlibemp] at this
            exact Bool.noConfusion this
        rcases kind_some_of_occ hoccQ with ⟨kr, hkr⟩
        have hrmem : r ∈ componentD (placedN n A .b i0) r :=
          componentD_mem_self _ r kr hkr
        have hcontra : noLibD (placedN n A .b i0)
            (componentD (placedN n A .b i0) r) = false :=
          (noLibD_eq_false_iff _ _).mpr ⟨lib, hlibb, hlibQ, r, hrmem, hadjlr⟩
        rw [hnlQ] at hcontra
        exact Bool.noConfusion hcontra
      · have hlibQ : occD (placedN n d1 .w i1) lib = false := by
          cases hlq : occD (placedN n d1 .w i1) lib with
          | false => rfl
          | true =>
            have := occ_PB1_le_joint A i0 i1 d1 hwf hi1 hb1 lib hlq
            rw [hlibemp] at this
            exact Bool.noConfusion this
        rcases kind_some_of_occ hoccQ with ⟨kr, hkr⟩
        have hrmem : r ∈ componentD (placedN n d1 .w i1) r :=
          componentD_mem_self _ r kr hkr
        have hcontra : noLibD (placedN n d1 .w i1)
            (componentD (placedN n d1 .w i1) r) = false :=
          (noLibD_eq_false_iff _ _).mpr ⟨lib, hlibb, hlibQ, r, hrmem, hadjlr⟩
        rw [hnlQ] at hcontra
        exact Bool.noConfusion hcontra
