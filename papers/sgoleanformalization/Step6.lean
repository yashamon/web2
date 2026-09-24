/- Step6.lean — Step 6: the basic capture reduction at turn t removes
   only dead stones. Invariant: cells are the placed display's or
   emptied-dead, and removals are whole A⁺ components. -/
import Step4
import Step5
import DispInfra
open SgoDisplay

variable {n : Nat}

/-- The placed display. -/
def PJ (D : Display n) (t i0 i1 : Nat) : Display n :=
  placeJoint D t (some i0) (some i1)

/-- A dead stone: on the joint placed diagram, gone in the composite. -/
def DeadStone (A : Display n) (i0 i1 : Nat) (c1 : Display n)
    (z : Nat) : Prop :=
  occD (jointPlaced n A i0 i1) z = true ∧ occD c1 z = false

/-- The Step 6 invariant for iterates of the reduction. -/
def CapIter (A D : Display n) (t i0 i1 : Nat) (c1 : Display n)
    (E : Display n) : Prop :=
  WFD E ∧
  (∀ z, z < n*n → E.get z = (PJ D t i0 i1).get z ∨
    (E.get z = none ∧ DeadStone A i0 i1 c1 z)) ∧
  (∀ z, z < n*n → occD (jointPlaced n A i0 i1) z = true →
    occD E z = false →
    ∀ y, y ∈ componentD (jointPlaced n A i0 i1) z → occD E y = false)

/-- The placed display and the joint placed diagram share cells. -/
theorem PJ_cells (A D : Display n) (t i0 i1 : Nat)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A) (z : Nat) :
    kindAt (PJ D t i0 i1) z = kindAt (jointPlaced n A i0 i1) z := by
  by_cases hz1 : z = i1
  · subst z
    unfold kindAt PJ
    rw [placeJoint_get_i1 D t i0 i1 hne hwfD hi1]
    exact (kindAt_joint_i1 A i0 i1 hwfA hi1).symm
  · by_cases hz0 : z = i0
    · subst z
      unfold kindAt PJ
      rw [placeJoint_get_i0 D t i0 i1 hne hwfD hi0]
      exact (kindAt_joint_i0 A i0 i1 hwfA hi0 hne).symm
    · unfold kindAt PJ
      rw [placeJoint_get_other D t i0 i1 z hne hz0 hz1]
      have h2 := kindAt_joint_other A i0 i1 z hz0 hz1
      unfold kindAt at h2
      rw [h2]
      have h3 := hcells z
      unfold kindAt at h3
      exact h3

/-- Occupancies agree as well. -/
theorem PJ_occ (A D : Display n) (t i0 i1 : Nat)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A) (z : Nat) :
    occD (PJ D t i0 i1) z = occD (jointPlaced n A i0 i1) z := by
  have hk := PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z
  unfold kindAt at hk
  unfold occD
  cases hg1 : (PJ D t i0 i1).get z <;>
    cases hg2 : (jointPlaced n A i0 i1).get z
  · rfl
  · rw [hg1, hg2] at hk
    simp at hk
  · rw [hg1, hg2] at hk
    simp at hk
  · rfl

/-- Stamps: the placements carry t. -/
theorem PJ_stamp_i0 (D : Display n) (t i0 i1 : Nat)
    (hwfD : WFD D) (hi0 : i0 < n*n) (hne : i0 ≠ i1) :
    stampAt (PJ D t i0 i1) i0 = t := by
  unfold stampAt PJ
  rw [placeJoint_get_i0 D t i0 i1 hne hwfD hi0]
  rfl

theorem PJ_stamp_i1 (D : Display n) (t i0 i1 : Nat)
    (hwfD : WFD D) (hi1 : i1 < n*n) (hne : i0 ≠ i1) :
    stampAt (PJ D t i0 i1) i1 = t := by
  unfold stampAt PJ
  rw [placeJoint_get_i1 D t i0 i1 hne hwfD hi1]
  rfl

theorem PJ_stamp_other (D : Display n) (t i0 i1 : Nat)
    (hne : i0 ≠ i1) (hst : StampsBelow D t) (z : Nat)
    (hz0 : z ≠ i0) (hz1 : z ≠ i1) :
    stampAt (PJ D t i0 i1) z < t := by
  unfold stampAt PJ
  rw [placeJoint_get_other D t i0 i1 z hne hz0 hz1]
  exact hst z

theorem PJ_stamp_le (D : Display n) (t i0 i1 : Nat)
    (hwfD : WFD D) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hst : StampsBelow D t) (z : Nat) :
    stampAt (PJ D t i0 i1) z ≤ t := by
  by_cases hz0 : z = i0
  · subst z
    rw [PJ_stamp_i0 D t i0 i1 hwfD hi0 hne]
    exact Nat.le_refl t
  · by_cases hz1 : z = i1
    · subst z
      rw [PJ_stamp_i1 D t i0 i1 hwfD hi1 hne]
      exact Nat.le_refl t
    · exact Nat.le_of_lt (PJ_stamp_other D t i0 i1 hne hst z hz0 hz1)

/-! ### Reading an iterate under the invariant. -/

theorem get_oob (E : Display n) (hwf : WFD E) (z : Nat)
    (hz : ¬ z < n*n) : E.get z = none := by
  unfold Display.get Array.getD
  rw [dif_neg (by rw [hwf]; exact hz)]

/-- An occupied iterate cell is the placed display's cell. -/
theorem CapIter_occ_cell (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hE : CapIter A D t i0 i1 c1 E) (z : Nat)
    (hz : occD E z = true) : E.get z = (PJ D t i0 i1).get z := by
  by_cases hzb : z < n*n
  · rcases hE.2.1 z hzb with h | ⟨hnone, _⟩
    · exact h
    · unfold occD at hz
      rw [hnone] at hz
      exact Bool.noConfusion hz
  · exfalso
    unfold occD at hz
    rw [get_oob E hE.1 z hzb] at hz
    exact Bool.noConfusion hz

/-- Live stones stand in every iterate. -/
theorem CapIter_live_stands (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hE : CapIter A D t i0 i1 c1 E) (z : Nat) (hzb : z < n*n)
    (hocc : occD (jointPlaced n A i0 i1) z = true)
    (hlive : occD c1 z = true) :
    E.get z = (PJ D t i0 i1).get z := by
  rcases hE.2.1 z hzb with h | ⟨_, _, hdead⟩
  · exact h
  · rw [hlive] at hdead
    exact Bool.noConfusion hdead

/-- Iterate stones are placed-display stones (kinds carried). -/
theorem CapIter_kind (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hE : CapIter A D t i0 i1 c1 E) (z : Nat) (k : DKind)
    (hk : kindAt E z = some k) :
    kindAt (PJ D t i0 i1) z = some k := by
  have hocc : occD E z = true := occD_of_kind hk
  unfold kindAt at hk ⊢
  rw [← CapIter_occ_cell A D t i0 i1 c1 E hE z hocc]
  exact hk

/-- Iterate components embed in joint placed diagram components. -/
theorem CapIter_comp_sub (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A)
    (hE : CapIter A D t i0 i1 c1 E) (z : Nat) (k : DKind)
    (hk : kindAt E z = some k) :
    ∀ y, y ∈ componentD E z → y ∈ componentD (jointPlaced n A i0 i1) z := by
  have hkP : kindAt (jointPlaced n A i0 i1) z = some k := by
    rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z]
    exact CapIter_kind A D t i0 i1 c1 E hE z k hk
  intro y hy
  rw [componentD_mem_iff (jointPlaced n A i0 i1) z k hkP y]
  refine ConnK_transport E (jointPlaced n A i0 i1) k ?_
    ((componentD_mem_iff E z k hk y).mp hy)
  intro x _ hx
  rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells x]
  exact CapIter_kind A D t i0 i1 c1 E hE x k hx

/-- A standing stone of an entirely-standing joint component spans it:
    the iterate component equals the A⁺ component. -/
theorem CapIter_comp_eq (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A)
    (hE : CapIter A D t i0 i1 c1 E) (z : Nat) (k : DKind)
    (hk : kindAt E z = some k)
    (hall : ∀ y, y ∈ componentD (jointPlaced n A i0 i1) z →
      occD E y = true) :
    ∀ y, y ∈ componentD E z ↔ y ∈ componentD (jointPlaced n A i0 i1) z := by
  have hkP : kindAt (jointPlaced n A i0 i1) z = some k := by
    rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z]
    exact CapIter_kind A D t i0 i1 c1 E hE z k hk
  intro y
  constructor
  · exact CapIter_comp_sub A D t i0 i1 c1 E hwfA hwfD hi0 hi1 hne
      hcells hE z k hk y
  · refine componentD_transport_rel (jointPlaced n A i0 i1) E k z hkP ?_ y
    intro m hm
    have hmkP : kindAt (jointPlaced n A i0 i1) m = some k :=
      componentD_kind _ z k hkP m hm
    have hmP : kindAt (PJ D t i0 i1) m = some k := by
      rw [PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells m]
      exact hmkP
    have hcell : E.get m = (PJ D t i0 i1).get m :=
      CapIter_occ_cell A D t i0 i1 c1 E hE m (hall m hm)
    unfold kindAt at hmP ⊢
    rw [hcell]
    exact hmP

/-! ### noLibD depends only on occupancy. -/

theorem noLibD_occ_congr (D E : Display n)
    (h : ∀ z, occD D z = occD E z) (comp : List Nat) :
    noLibD D comp = noLibD E comp := by
  unfold noLibD
  have hfun : (fun q => !(!occD D q && comp.any fun r => adjI n q r))
      = (fun q => !(!occD E q && comp.any fun r => adjI n q r)) :=
    funext fun q => by rw [h q]
  rw [hfun]

/-! ### A dead old component touches its opposite placement. -/

theorem dead_old_adjacent (A : Display n) (i0 i1 : Nat)
    (hwfA : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hlegal : IsLegal A)
    (z0 : Nat) (hz0 : z0 < n*n) (hz0A : occD A z0 = true)
    (hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD A q = true)
    (htrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) z0) = true)
    (k : DKind) (hkA : kindAt A z0 = some k) :
    (k = .w → ∃ m, m ∈ componentD (jointPlaced n A i0 i1) z0 ∧
      adjI n i0 m = true) ∧
    (k = .b → ∃ m, m ∈ componentD (jointPlaced n A i0 i1) z0 ∧
      adjI n i1 m = true) := by
  have holdeq := old_component_eq A i0 i1 hi0A hi1A z0 hz0A hold
  have hz00 : z0 ≠ i0 := by
    intro h; rw [h, hi0A] at hz0A; exact Bool.noConfusion hz0A
  have hz01 : z0 ≠ i1 := by
    intro h; rw [h, hi1A] at hz0A; exact Bool.noConfusion hz0A
  have hkP : kindAt (jointPlaced n A i0 i1) z0 = some k := by
    rw [kindAt_joint_other A i0 i1 z0 hz00 hz01]
    exact hkA
  rcases (noLibD_eq_false_iff _ _).mp (hlegal z0 (occD_of_kind hkA))
    with ⟨l, hlb, hlA, m, hm, hadj⟩
  have hmT : m ∈ componentD (jointPlaced n A i0 i1) z0 :=
    (holdeq m).mpr hm
  have hnotother : ¬ (l ≠ i0 ∧ l ≠ i1) := by
    rintro ⟨hl0, hl1⟩
    have hlP : occD (jointPlaced n A i0 i1) l = false := by
      rw [occD_joint_other A i0 i1 l hl0 hl1]
      exact hlA
    have hlib : noLibD (jointPlaced n A i0 i1)
        (componentD (jointPlaced n A i0 i1) z0) = false :=
      (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, hlP, m, hmT, hadj⟩
    rw [htrap] at hlib
    exact Bool.noConfusion hlib
  constructor
  · intro hkw
    subst k
    -- the liberty is not i1 (the white stone there would join)
    have hl1 : l ≠ i1 := by
      intro h
      subst l
      have hjoin : i1 ∈ componentD (jointPlaced n A i0 i1) z0 :=
        componentD_maximal (jointPlaced n A i0 i1) z0 .w hkP i1
          (List.mem_range.mpr hi1) (kindAt_joint_i1 A i0 i1 hwfA hi1)
          m hmT hadj
      have := hold i1 hjoin
      rw [hi1A] at this
      exact Bool.noConfusion this
    have hl0 : l = i0 := by
      by_cases h : l = i0
      · exact h
      · exact absurd ⟨h, hl1⟩ hnotother
    subst l
    exact ⟨m, hmT, hadj⟩
  · intro hkb
    subst k
    have hl0 : l ≠ i0 := by
      intro h
      subst l
      have hjoin : i0 ∈ componentD (jointPlaced n A i0 i1) z0 :=
        componentD_maximal (jointPlaced n A i0 i1) z0 .b hkP i0
          (List.mem_range.mpr hi0)
          (kindAt_joint_i0 A i0 i1 hwfA hi0 hne) m hmT hadj
      have := hold i0 hjoin
      rw [hi0A] at this
      exact Bool.noConfusion this
    have hl1 : l = i1 := by
      by_cases h : l = i1
      · exact h
      · exact absurd ⟨hl0, h⟩ hnotother
    subst l
    exact ⟨m, hmT, hadj⟩


/-- The standing-donor branch of Step 6: a standing dead donor is a
    trapped blocker, defeating condition 3a. -/
theorem step6_blocker (A D : Display n) (t i0 i1 : Nat)
    (d1 c1 d2 c2 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (E : Display n) (hE : CapIter A D t i0 i1 c1 E)
    (hclassE : IsClassical E)
    (p : Nat) (hp : p ∈ allIdx n) (k : DKind)
    (hkE : kindAt E p = some k) (hknr : k ≠ .r)
    (hnoLibE : noLibD E (componentD E p) = true)
    (hEoccle : ∀ w, occD E w = true → occD (PJ D t i0 i1) w = true)
    (y : Nat) (hy : y ∈ componentD E p) (hykE : kindAt E y = some k)
    (hyAP : y ∈ componentD (jointPlaced n A i0 i1) p)
    (hyb : y ∈ allIdx n)
    (hykAP : kindAt (jointPlaced n A i0 i1) y = some k)
    (hlive : occD c1 y = true)
    (hcompB : ∀ q, q ∈ componentD E p ↔
      q ∈ componentD (jointPlaced n A i0 i1) y)
    (l : Nat) (hlb : l < n*n)
    (hlPocc : occD (jointPlaced n A i0 i1) l = true)
    (hldead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
      occD c1 q = false)
    (hlE : occD E l = true)
    (m : Nat) (hmB : m ∈ componentD (jointPlaced n A i0 i1) y)
    (hadjlm : adjI n l m = true)
    (hkne : kindAt (jointPlaced n A i0 i1) l
      ≠ kindAt (jointPlaced n A i0 i1) y)
    (h3a : ((allIdx n).filter (fun z => occD E z &&
        !(componentD E p).contains z &&
        (componentD E p).any fun q => adjI n z q)).all
      (fun z => !((kindAt E z == some k.opp ||
        kindAt E z == some DKind.r) && stoneTrappedBy E z k t))
      = true) : False := by
  -- l's kinds
  rcases kind_some_of_occ hlPocc with ⟨kl, hklAP⟩
  have hlcell : E.get l = (PJ D t i0 i1).get l :=
    CapIter_occ_cell A D t i0 i1 c1 E hE l hlE
  have hklE : kindAt E l = some kl := by
    unfold kindAt
    rw [hlcell]
    rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get l)
      = kindAt (PJ D t i0 i1) l from rfl,
      PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells l]
    exact hklAP
  have hkbw : k = .b ∨ k = .w := by
    cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hknr
  have hklopp : kl = k.opp := by
    rcases joint_kind_bw A i0 i1 hwfA hi0 hi1 hne hclass l hlPocc
      with h | h <;> rcases hkbw with rfl | rfl
    · exact absurd (h.trans hykAP.symm) hkne
    · rw [hklAP] at h
      exact Option.some.inj h
    · rw [hklAP] at h
      exact Option.some.inj h
    · exact absurd (h.trans hykAP.symm) hkne
  -- T stands entire in E
  have hTstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
      occD E q = true := by
    intro q hq
    cases hqE : occD E q
    · exfalso
      have hqb := componentD_board (List.mem_range.mpr hlb) hklAP hq
      have hqocc : occD (jointPlaced n A i0 i1) q = true :=
        occD_of_kind (componentD_kind _ l kl hklAP q hq)
      have hwhole := hE.2.2 q (List.mem_range.mp hqb) hqocc hqE
      have hlmem : l ∈ componentD (jointPlaced n A i0 i1) q :=
        (componentD_eq_mem (jointPlaced n A i0 i1) l q kl
          (List.mem_range.mpr hlb) hklAP hq l).mpr
          (componentD_mem_self _ l kl hklAP)
      have := hwhole l hlmem
      rw [hlE] at this
      exact Bool.noConfusion this
    · rfl
  have hcompeql := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0 hi1
    hne hcells hE l kl hklE hTstand
  -- T is trapped in A⁺ (it is dead)
  have htrapT : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) l) = true := by
    rcases step1_dichotomy A i0 i1 d1 c1 hwfA hi0 hi1 hne hi1A hb1 hb2
      l hlb hlPocc with h | ⟨_, htrap⟩
    · exfalso
      have hcell := h l (componentD_mem_self _ l kl hklAP)
      have : occD c1 l = true := by
        unfold occD
        rw [hcell]
        exact hlPocc
      rw [hldead l (componentD_mem_self _ l kl hklAP)] at this
      exact Bool.noConfusion this
    · exact htrap
  -- no liberties in E either
  have hnoLibEl : noLibD E (componentD E l) = true := by
    cases hnl : noLibD E (componentD E l)
    · exfalso
      rcases (noLibD_eq_false_iff _ _).mp hnl with
        ⟨l', hl'b, hl'E, m', hm', hadj'⟩
      have hm'T : m' ∈ componentD (jointPlaced n A i0 i1) l :=
        (hcompeql m').mp hm'
      cases hl'AP : occD (jointPlaced n A i0 i1) l'
      · -- an A⁺ liberty of the dead donor: contradiction
        have hlib : noLibD (jointPlaced n A i0 i1)
            (componentD (jointPlaced n A i0 i1) l) = false :=
          (noLibD_eq_false_iff _ _).mpr
            ⟨l', hl'b, hl'AP, m', hm'T, hadj'⟩
        rw [htrapT] at hlib
        exact Bool.noConfusion hlib
      · -- a removed dead stone adjacent to T: it lies in T, standing
        have hl'dead : DeadStone A i0 i1 c1 l' := by
          rcases hE.2.1 l' (List.mem_range.mp hl'b) with h | ⟨_, hdead⟩
          · exfalso
            have hoccE : occD E l' = true := by
              unfold occD
              rw [h]
              have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne
                hcells l'
              unfold occD at hpo
              rw [hpo]
              exact hl'AP
            rw [hl'E] at hoccE
            exact Bool.noConfusion hoccE
          · exact hdead
        have hm'dead : DeadStone A i0 i1 c1 m' := by
          refine ⟨occD_of_kind (componentD_kind _ l kl hklAP m' hm'T),
            hldead m' hm'T⟩
        have hl'T : l' ∈ componentD (jointPlaced n A i0 i1) m' :=
          step5_adjacent_dead_same_comp A i0 i1 d1 c1 hwfA hi0 hi1 hne
            hi1A hclass hb1 hb2 m' l'
            (List.mem_range.mp (componentD_board
              (List.mem_range.mpr hlb) hklAP hm'T))
            (List.mem_range.mp hl'b) hm'dead.1 hl'dead.1
            hm'dead.2 hl'dead.2 (adjI_symm hadj')
        have hl'inT : l' ∈ componentD (jointPlaced n A i0 i1) l :=
          (componentD_eq_mem (jointPlaced n A i0 i1) l m' kl
            (List.mem_range.mpr hlb) hklAP hm'T l').mp hl'T
        have := hTstand l' hl'inT
        rw [hl'E] at this
        exact Bool.noConfusion this
    · rfl
  -- every visible stamp is at most t
  have hstampE : ∀ z, occD E z = true → stampAt E z ≤ t := by
    intro z hz
    unfold stampAt
    rw [CapIter_occ_cell A D t i0 i1 c1 E hE z hz]
    exact PJ_stamp_le D t i0 i1 hwfD hi0 hi1 hne hst z
  -- and t is attained
  have hwitness : ∃ w, (w ∈ (componentD E l).map (stampAt E) ∨
      w ∈ (((allIdx n).filter fun z => occD E z &&
        !(componentD E l).contains z &&
        (componentD E l).any fun q => adjI n z q).map (stampAt E)))
      ∧ w = t := by
    by_cases hfreshT : i0 ∈ componentD (jointPlaced n A i0 i1) l ∨
        i1 ∈ componentD (jointPlaced n A i0 i1) l
    · -- fresh: the placement stone sits in the component with stamp t
      rcases hfreshT with hf | hf
      · refine ⟨stampAt E i0, Or.inl (List.mem_map.mpr
          ⟨i0, (hcompeql i0).mpr hf, rfl⟩), ?_⟩
        unfold stampAt
        rw [CapIter_occ_cell A D t i0 i1 c1 E hE i0 (hTstand i0 hf)]
        exact PJ_stamp_i0 D t i0 i1 hwfD hi0 hne
      · refine ⟨stampAt E i1, Or.inl (List.mem_map.mpr
          ⟨i1, (hcompeql i1).mpr hf, rfl⟩), ?_⟩
        unfold stampAt
        rw [CapIter_occ_cell A D t i0 i1 c1 E hE i1 (hTstand i1 hf)]
        exact PJ_stamp_i1 D t i0 i1 hwfD hi1 hne
    · -- old: the opposite placement neighbors the component
      have holdT : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
          occD A q = true := by
        intro q hq
        have hq0 : q ≠ i0 := fun h => hfreshT (Or.inl (h ▸ hq))
        have hq1 : q ≠ i1 := fun h => hfreshT (Or.inr (h ▸ hq))
        rw [← occD_joint_other A i0 i1 q hq0 hq1]
        exact occD_of_kind (componentD_kind _ l kl hklAP q hq)
      have hlA : occD A l = true :=
        holdT l (componentD_mem_self _ l kl hklAP)
      have hl0 : l ≠ i0 := by
        intro h; rw [h, hi0A] at hlA; exact Bool.noConfusion hlA
      have hl1 : l ≠ i1 := by
        intro h; rw [h, hi1A] at hlA; exact Bool.noConfusion hlA
      have hklA : kindAt A l = some kl := by
        rw [← kindAt_joint_other A i0 i1 l hl0 hl1]
        exact hklAP
      have hadjpl := dead_old_adjacent A i0 i1 hwfA hi0 hi1 hne hi0A
        hi1A hlegal l hlb hlA holdT htrapT kl hklA
      -- pick the opposite placement by color
      have hplace : ∃ iM, iM < n*n ∧ (iM = i0 ∨ iM = i1) ∧
          kindAt (jointPlaced n A i0 i1) iM = some kl.opp ∧
          ∃ m'', m'' ∈ componentD (jointPlaced n A i0 i1) l ∧
            adjI n iM m'' = true := by
        rcases hkbw with rfl | rfl
        · rcases hadjpl.1 hklopp with ⟨m'', hm'', hadj''⟩
          refine ⟨i0, hi0, Or.inl rfl, ?_, m'', hm'', hadj''⟩
          rw [kindAt_joint_i0 A i0 i1 hwfA hi0 hne, hklopp]
          rfl
        · rcases hadjpl.2 hklopp with ⟨m'', hm'', hadj''⟩
          refine ⟨i1, hi1, Or.inr rfl, ?_, m'', hm'', hadj''⟩
          rw [kindAt_joint_i1 A i0 i1 hwfA hi1, hklopp]
          rfl
      rcases hplace with ⟨iM, hiMb, hiMid, hiMk, m'', hm''T, hadjim⟩
      have hiMocc : occD (jointPlaced n A i0 i1) iM = true :=
        occD_of_kind hiMk
      have hiMlive : occD c1 iM = true := by
        cases hc : occD c1 iM
        · exfalso
          have hm''dead : DeadStone A i0 i1 c1 m'' :=
            ⟨occD_of_kind (componentD_kind _ l kl hklAP m'' hm''T),
              hldead m'' hm''T⟩
          have hiMT : iM ∈ componentD (jointPlaced n A i0 i1) m'' :=
            step5_adjacent_dead_same_comp A i0 i1 d1 c1 hwfA hi0 hi1
              hne hi1A hclass hb1 hb2 m'' iM
              (List.mem_range.mp (componentD_board
                (List.mem_range.mpr hlb) hklAP hm''T))
              hiMb hm''dead.1 hiMocc hm''dead.2 hc
              (adjI_symm hadjim)
          have hiMinT : iM ∈ componentD (jointPlaced n A i0 i1) l :=
            (componentD_eq_mem (jointPlaced n A i0 i1) l m'' kl
              (List.mem_range.mpr hlb) hklAP hm''T iM).mp hiMT
          rcases hiMid with rfl | rfl
          · exact hfreshT (Or.inl hiMinT)
          · exact hfreshT (Or.inr hiMinT)
        · rfl
      have hiMcell : E.get iM = (PJ D t i0 i1).get iM :=
        CapIter_live_stands A D t i0 i1 c1 E hE iM hiMb hiMocc hiMlive
      have hiMoccE : occD E iM = true := by
        unfold occD
        rw [hiMcell]
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells iM
        unfold occD at hpo
        rw [hpo]
        exact hiMocc
      have hiMstamp : stampAt E iM = t := by
        unfold stampAt
        rw [hiMcell]
        rcases hiMid with h | h
        · rw [h]
          exact PJ_stamp_i0 D t i0 i1 hwfD hi0 hne
        · rw [h]
          exact PJ_stamp_i1 D t i0 i1 hwfD hi1 hne
      have hklnr : kl ≠ .r := by
        rcases hkbw with rfl | rfl <;> rw [hklopp] <;> decide
      -- iM is a neighbor of the component in E
      have hiMnotmem : ¬ (componentD E l).contains iM = true := by
        intro hcont
        have hmem := List.contains_iff_mem.mp hcont
        have hkEiM : kindAt E iM = some kl :=
          componentD_kind E l kl hklE iM hmem
        have hPk : kindAt (PJ D t i0 i1) iM = some kl := by
          unfold kindAt at hkEiM ⊢
          rw [← hiMcell]
          exact hkEiM
        rw [PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells iM,
          hiMk] at hPk
        exact opp_ne_self hklnr (Option.some.inj hPk)
      have hany : (componentD E l).any (fun q => adjI n iM q) = true :=
        List.any_eq_true.mpr ⟨m'', (hcompeql m'').mpr hm''T, hadjim⟩
      refine ⟨stampAt E iM, Or.inr (List.mem_map.mpr
        ⟨iM, List.mem_filter.mpr ⟨List.mem_range.mpr hiMb, ?_⟩, rfl⟩),
        hiMstamp⟩
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hiMoccE, ?_⟩, hany⟩
      rw [Bool.not_eq_true']
      cases hc : (componentD E l).contains iM
      · rfl
      · exact absurd hc hiMnotmem
  -- assemble the trapped-on-turn fact
  have hmax : ((componentD E l).map (stampAt E) ++
      (((allIdx n).filter fun z => occD E z &&
        !(componentD E l).contains z &&
        (componentD E l).any fun q => adjI n z q).map
        (stampAt E))).foldl Nat.max 0 = t := by
    apply Nat.le_antisymm
    · apply foldl_max_le _ _ _ (Nat.zero_le _)
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
        exact hstampE a (occD_of_kind (componentD_kind E l kl hklE a ha))
      · rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
        have := (List.mem_filter.mp ha).2
        rw [Bool.and_eq_true, Bool.and_eq_true] at this
        exact hstampE a this.1.1
    · rcases hwitness with ⟨w, hw, rfl⟩
      exact le_foldl_max _ _ _ (List.mem_append.mpr hw)
  have htot : trappedOnTurn E (componentD E l) t = true := by
    simp only [trappedOnTurn]
    rw [Bool.and_eq_true]
    refine ⟨hnoLibEl, ?_⟩
    rw [beq_iff_eq]
    exact hmax
  -- the blocker defeats 3a
  have hstb : stoneTrappedBy E l k t = true := by
    simp only [stoneTrappedBy]
    rw [hklE, hklopp]
    rcases hkbw with rfl | rfl <;> simp <;> exact htot
  have hlmemfilter : l ∈ (allIdx n).filter (fun z => occD E z &&
      !(componentD E p).contains z &&
      (componentD E p).any fun q => adjI n z q) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hlb, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hlE, ?_⟩, List.any_eq_true.mpr
      ⟨m, (hcompB m).mpr hmB, hadjlm⟩⟩
    rw [Bool.not_eq_true']
    cases hc : (componentD E p).contains l
    · rfl
    · exfalso
      have hmem := List.contains_iff_mem.mp hc
      have : kindAt E l = some k := componentD_kind E p k hkE l hmem
      rw [hklE] at this
      have hkk := Option.some.inj this
      rw [hklopp] at hkk
      exact opp_ne_self hknr hkk
  have hpred := List.all_eq_true.mp h3a l hlmemfilter
  rw [hklE, hklopp, hstb] at hpred
  simp at hpred

/-! ### The heart of Step 6: captured components are dead, and whole. -/

theorem captured_dead_entire (A D : Display n) (t i0 i1 : Nat)
    (d1 c1 d2 c2 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (E : Display n) (hE : CapIter A D t i0 i1 c1 E)
    (p : Nat) (hp : p ∈ allIdx n) (k : DKind)
    (hkE : kindAt E p = some k)
    (hcap : isCaptured E (componentD E p) k t = true) :
    (∀ y, y ∈ componentD E p → DeadStone A i0 i1 c1 y) ∧
    (∀ y, y ∈ componentD (jointPlaced n A i0 i1) p →
      y ∈ componentD E p) := by
  have hkAP : kindAt (jointPlaced n A i0 i1) p = some k := by
    rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells p]
    exact CapIter_kind A D t i0 i1 c1 E hE p k hkE
  have hclassE : IsClassical E := by
    intro x hx
    have hP := CapIter_kind A D t i0 i1 c1 E hE x .r hx
    rw [PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells x] at hP
    rcases joint_kind_bw A i0 i1 hwfA hi0 hi1 hne hclass x
      (occD_of_kind hP) with h | h
    · rw [hP] at h
      exact DKind.noConfusion (Option.some.inj h)
    · rw [hP] at h
      exact DKind.noConfusion (Option.some.inj h)
  have hknr : k ≠ .r := fun hkr => hclassE p (hkr ▸ hkE)
  -- decompose the capture condition
  have hcap' := hcap
  simp only [isCaptured] at hcap'
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcap'
  obtain ⟨⟨htrapE, _⟩, hthird⟩ := hcap'
  have hnoLibE : noLibD E (componentD E p) = true := by
    have h := htrapE
    simp only [trappedOnTurn] at h
    rw [Bool.and_eq_true] at h
    exact h.1
  -- occupancy embedding
  have hEoccle : ∀ w, occD E w = true → occD (PJ D t i0 i1) w = true := by
    intro w hw
    unfold occD
    rw [← CapIter_occ_cell A D t i0 i1 c1 E hE w hw]
    exact hw
  have halldead : ∀ y, y ∈ componentD E p → DeadStone A i0 i1 c1 y := by
    intro y hy
    have hykE : kindAt E y = some k := componentD_kind E p k hkE y hy
    have hyAP : y ∈ componentD (jointPlaced n A i0 i1) p :=
      CapIter_comp_sub A D t i0 i1 c1 E hwfA hwfD hi0 hi1 hne hcells
        hE p k hkE y hy
    have hyb : y ∈ allIdx n := componentD_board hp hkAP hyAP
    have hykAP : kindAt (jointPlaced n A i0 i1) y = some k :=
      componentD_kind _ p k hkAP y hyAP
    have hyAocc : occD (jointPlaced n A i0 i1) y = true :=
      occD_of_kind hykAP
    refine ⟨hyAocc, ?_⟩
    cases hlive : occD c1 y
    · rfl
    · exfalso
      -- y is live: its whole A⁺ component stands
      have hstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) y →
          c1.get q = (jointPlaced n A i0 i1).get q := by
        rcases step1_dichotomy A i0 i1 d1 c1 hwfA hi0 hi1 hne hi1A
          hb1 hb2 y (List.mem_range.mp hyb) hyAocc with h | ⟨hallemp, _⟩
        · exact h
        · exfalso
          have := hallemp y (componentD_mem_self _ y k hykAP)
          rw [hlive] at this
          exact Bool.noConfusion this
      have hBlive : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) y →
          occD c1 q = true := by
        intro q hq
        have hqk := componentD_kind _ y k hykAP q hq
        unfold occD
        rw [hstand q hq]
        exact occD_of_kind hqk
      have hBstandE : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) y →
          occD E q = true := by
        intro q hq
        have hqk := componentD_kind _ y k hykAP q hq
        have hqb := componentD_board hyb hykAP hq
        have hqAocc : occD (jointPlaced n A i0 i1) q = true :=
          occD_of_kind hqk
        have hcell := CapIter_live_stands A D t i0 i1 c1 E hE q
          (List.mem_range.mp hqb) hqAocc (hBlive q hq)
        unfold occD
        rw [hcell]
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells q
        unfold occD at hpo
        rw [hpo]
        exact hqAocc
      have hcompeqy := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0
        hi1 hne hcells hE y k hykE hBstandE
      have heqp := componentD_eq_mem E p y k hp hkE hy
      have hcompB : ∀ q, q ∈ componentD E p ↔
          q ∈ componentD (jointPlaced n A i0 i1) y :=
        fun q => (heqp q).symm.trans (hcompeqy q)
      -- B is trapped in A⁺
      have htrapP : noLibD (PJ D t i0 i1) (componentD E p) = true :=
        noLibD_mono _ E _ hEoccle hnoLibE
      have htrapAP : noLibD (jointPlaced n A i0 i1)
          (componentD E p) = true := by
        rw [noLibD_occ_congr (jointPlaced n A i0 i1) (PJ D t i0 i1)
          (fun z => (PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne
            hcells z).symm) (componentD E p)]
        exact htrapP
      have htrapB : noLibD (jointPlaced n A i0 i1)
          (componentD (jointPlaced n A i0 i1) y) = true := by
        rw [← noLibD_congr _ _ _ hcompB]
        exact htrapAP
      -- Step 4: fresh, with a dead donor
      obtain ⟨hfresh, l, hlb, hlPocc, hldead, ⟨m, hmB, hadjlm⟩, hkne⟩ :=
        step4_live_trapped A i0 i1 d1 c1 d2 c2 hwfA hi0 hi1 hne hi0A
          hi1A hclass hlegal hb1 hb2 hw1 hw2 hcomm y
          (List.mem_range.mp hyb) hyAocc htrapB hlive
      -- 3b is refuted by the fresh placement's stamp
      have hfreshstamp : ∃ f, f ∈ componentD E p ∧ stampAt E f = t := by
        rcases hfresh with hf | hf
        · refine ⟨i0, (hcompB i0).mpr hf, ?_⟩
          have hcell := CapIter_occ_cell A D t i0 i1 c1 E hE i0
            (hBstandE i0 hf)
          unfold stampAt
          rw [hcell]
          exact PJ_stamp_i0 D t i0 i1 hwfD hi0 hne
        · refine ⟨i1, (hcompB i1).mpr hf, ?_⟩
          have hcell := CapIter_occ_cell A D t i0 i1 c1 E hE i1
            (hBstandE i1 hf)
          unfold stampAt
          rw [hcell]
          exact PJ_stamp_i1 D t i0 i1 hwfD hi1 hne
      -- the donor's stone-level analysis
      rw [Bool.or_eq_true] at hthird
      rcases hthird with h3a | h3b
      · -- 3a: every adjacent opposite stone unblocked — but l blocks
        cases hlE : occD E l
        · -- the donor cell is empty in E: a liberty of the component
          have hlEmpty : occD E l = false := hlE
          have hmE : m ∈ componentD E p := (hcompB m).mpr hmB
          have hlib : noLibD E (componentD E p) = false :=
            (noLibD_eq_false_iff _ _).mpr
              ⟨l, List.mem_range.mpr hlb, hlEmpty, m, hmE, hadjlm⟩
          rw [hnoLibE] at hlib
          exact Bool.noConfusion hlib
        · -- the donor stands: it is a trapped blocker
          exact step6_blocker A D t i0 i1 d1 c1 d2 c2 hwfA hwfD hi0 hi1
            hne hi0A hi1A hclass hlegal hcells hst hb1 hb2 hw1 hw2 hcomm
            E hE hclassE p hp k hkE hknr hnoLibE hEoccle
            y hy hykE hyAP hyb hykAP hlive hcompB
            l hlb hlPocc hldead hlE m hmB hadjlm hkne h3a
      · -- 3b: the component carries a turn stamp
        rw [Bool.and_eq_true] at h3b
        rcases hfreshstamp with ⟨f, hfmem, hfstamp⟩
        have := List.all_eq_true.mp h3b.1 f hfmem
        rw [hfstamp] at this
        simp at this
  refine ⟨halldead, ?_⟩
  -- entire: the whole-component clause keeps standing dead comps whole
  have hpocc : occD E p = true := occD_of_kind hkE
  have hallstand : ∀ y', y' ∈ componentD (jointPlaced n A i0 i1) p →
      occD E y' = true := by
    intro y' hy'
    cases hy'E : occD E y'
    · exfalso
      have hy'b := componentD_board hp hkAP hy'
      have hy'occ : occD (jointPlaced n A i0 i1) y' = true :=
        occD_of_kind (componentD_kind _ p k hkAP y' hy')
      have hwhole := hE.2.2 y' (List.mem_range.mp hy'b) hy'occ hy'E
      have hpmem : p ∈ componentD (jointPlaced n A i0 i1) y' :=
        (componentD_eq_mem (jointPlaced n A i0 i1) p y' k hp hkAP hy'
          p).mpr (componentD_mem_self _ p k hkAP)
      have := hwhole p hpmem
      rw [hpocc] at this
      exact Bool.noConfusion this
    · rfl
  exact fun y hy => (CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0 hi1
    hne hcells hE p k hkE hallstand y).mpr hy

/-! ### Step 6: the invariant is preserved by the basic reduction. -/

theorem CapIter_classical (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hclass : IsClassical A) (hcells : SameCells D A)
    (hE : CapIter A D t i0 i1 c1 E) : IsClassical E := by
  intro x hx
  have hP := CapIter_kind A D t i0 i1 c1 E hE x .r hx
  rw [PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells x] at hP
  rcases joint_kind_bw A i0 i1 hwfA hi0 hi1 hne hclass x
    (occD_of_kind hP) with h | h
  · rw [hP] at h
    exact DKind.noConfusion (Option.some.inj h)
  · rw [hP] at h
    exact DKind.noConfusion (Option.some.inj h)

theorem step6_preserved (A D : Display n) (t i0 i1 : Nat)
    (d1 c1 d2 c2 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (E : Display n) (hE : CapIter A D t i0 i1 c1 E) :
    CapIter A D t i0 i1 c1 (basicCap E t) := by
  have hclassE : IsClassical E := CapIter_classical A D t i0 i1 c1 E
    hwfA hwfD hi0 hi1 hne hclass hcells hE
  have hdead : ∀ z, z ∈ capturedOf E t .b ++ capturedOf E t .w →
      DeadStone A i0 i1 c1 z ∧
      (∀ y, y ∈ componentD (jointPlaced n A i0 i1) z →
        y ∈ capturedOf E t .b ++ capturedOf E t .w) := by
    intro z hz
    rcases List.mem_append.mp hz with hzc | hzc
    · rcases (mem_capturedOf E t .b z).mp hzc with ⟨p, hp, hkp, hcap, hzE⟩
      obtain ⟨hd, hent⟩ := captured_dead_entire A D t i0 i1 d1 c1 d2 c2
        hwfA hwfD hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst
        hb1 hb2 hw1 hw2 hcomm E hE p hp .b hkp hcap
      have hkAP : kindAt (jointPlaced n A i0 i1) p = some .b := by
        rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells p]
        exact CapIter_kind A D t i0 i1 c1 E hE p .b hkp
      have hzAP : z ∈ componentD (jointPlaced n A i0 i1) p :=
        CapIter_comp_sub A D t i0 i1 c1 E hwfA hwfD hi0 hi1 hne hcells
          hE p .b hkp z hzE
      refine ⟨hd z hzE, ?_⟩
      intro y hy
      have hyp : y ∈ componentD (jointPlaced n A i0 i1) p :=
        (componentD_eq_mem (jointPlaced n A i0 i1) p z .b hp hkAP
          hzAP y).mp hy
      exact List.mem_append.mpr (Or.inl ((mem_capturedOf E t .b y).mpr
        ⟨p, hp, hkp, hcap, hent y hyp⟩))
    · rcases (mem_capturedOf E t .w z).mp hzc with ⟨p, hp, hkp, hcap, hzE⟩
      obtain ⟨hd, hent⟩ := captured_dead_entire A D t i0 i1 d1 c1 d2 c2
        hwfA hwfD hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst
        hb1 hb2 hw1 hw2 hcomm E hE p hp .w hkp hcap
      have hkAP : kindAt (jointPlaced n A i0 i1) p = some .w := by
        rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells p]
        exact CapIter_kind A D t i0 i1 c1 E hE p .w hkp
      have hzAP : z ∈ componentD (jointPlaced n A i0 i1) p :=
        CapIter_comp_sub A D t i0 i1 c1 E hwfA hwfD hi0 hi1 hne hcells
          hE p .w hkp z hzE
      refine ⟨hd z hzE, ?_⟩
      intro y hy
      have hyp : y ∈ componentD (jointPlaced n A i0 i1) p :=
        (componentD_eq_mem (jointPlaced n A i0 i1) p z .w hp hkAP
          hzAP y).mp hy
      exact List.mem_append.mpr (Or.inr ((mem_capturedOf E t .w y).mpr
        ⟨p, hp, hkp, hcap, hent y hyp⟩))
  refine ⟨basicCap_size E t, ?_, ?_⟩
  · -- cells clause
    intro z hz
    rw [basicCap_get E t hclassE z hz]
    cases hc : (capturedOf E t .b ++ capturedOf E t .w).contains z
    · simp only [Bool.false_eq_true, if_false]
      exact hE.2.1 z hz
    · simp only [if_true]
      exact Or.inr ⟨trivial, (hdead z (List.contains_iff_mem.mp hc)).1⟩
  · -- whole-component clause
    intro z hz hzAP hzE
    have hkz := kind_some_of_occ hzAP
    rcases hkz with ⟨kz, hkzAP⟩
    intro y hy
    have hyb := componentD_board (List.mem_range.mpr hz) hkzAP hy
    rw [occD_basicCap E t hclassE y (List.mem_range.mp hyb)]
    rw [occD_basicCap E t hclassE z hz] at hzE
    cases hcz : (capturedOf E t .b ++ capturedOf E t .w).contains z
    · -- z was removed earlier: the whole component already is
      rw [hcz] at hzE
      simp only [Bool.false_eq_true, if_false] at hzE
      have hwhole := hE.2.2 z hz hzAP hzE
      cases hcy : (capturedOf E t .b ++ capturedOf E t .w).contains y
      · simp only [Bool.false_eq_true, if_false]
        exact hwhole y hy
      · simp only [if_true]
    · -- z is newly captured: its whole component is in the dead list
      have hzc := List.contains_iff_mem.mp hcz
      have hyc : y ∈ capturedOf E t .b ++ capturedOf E t .w := by
        have := (hdead z hzc).2
        exact this y hy
      rw [List.contains_iff_mem.mpr hyc]
      simp
