/- Step3.lean — Step 3: old trapped components are dead. The white case
   is captured by m0 along the first composite; the BLACK case is
   captured by m1 along the SECOND composite and lands in c1 through
   the commuting hypothesis — hcomm is load-bearing here. -/
import Step1
open SgoDisplay

variable {n : Nat}

/-- Equal stone patterns give equal occupancy. -/
theorem occ_eq_of_samecells {c1 c2 : Display n}
    (hcomm : SameCells c1 c2) (q : Nat) : occD c1 q = occD c2 q := by
  have hk := hcomm q
  unfold kindAt at hk
  unfold occD
  cases hg1 : c1.get q <;> cases hg2 : c2.get q
  · rfl
  · rw [hg1, hg2] at hk
    simp at hk
  · rw [hg1, hg2] at hk
    simp at hk
  · rfl

/-- The persistence conditional, color-generic: a first-placed-diagram
    stone emptied by the first move is empty after the second. -/
theorem persist_first_general (A : Display n) (cF cS : DKind)
    (iF iS : Nat) (dF rS : Display n)
    (hne : iF ≠ iS) (hiSA : occD A iS = false)
    (h1 : goMoveN n A cF iF = some dF)
    (h2 : goMoveN n dF cS iS = some rS)
    (z : Nat) (hoccP : occD (placedN n A cF iF) z = true)
    (hemp : occD dF z = false) :
    occD rS z = false := by
  by_cases hzF : z = iF
  · subst z
    exact goMoveN_fills_only dF cS iS iF rS h2 hemp hne
  · have hoccA : occD A z = true := by
      rw [← occD_placedN_ne A cF iF z hzF]
      exact hoccP
    have hzS : z ≠ iS := by
      intro h
      rw [h, hiSA] at hoccA
      exact Bool.noConfusion hoccA
    exact goMoveN_fills_only dF cS iS z rS h2 hemp hzS

/-- An old A⁺ component (all stones A-stones) is an A component:
    its connectivity avoids the fresh intersections. -/
theorem old_component_eq (A : Display n) (i0 i1 : Nat)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (z0 : Nat) (hz0A : occD A z0 = true)
    (hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD A q = true) :
    ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 ↔
      q ∈ componentD A z0 := by
  have hz00 : z0 ≠ i0 := by
    intro h; rw [h, hi0A] at hz0A; exact Bool.noConfusion hz0A
  have hz01 : z0 ≠ i1 := by
    intro h; rw [h, hi1A] at hz0A; exact Bool.noConfusion hz0A
  rcases kind_some_of_occ hz0A with ⟨k, hkA⟩
  have hkP : kindAt (jointPlaced n A i0 i1) z0 = some k := by
    rw [kindAt_joint_other A i0 i1 z0 hz00 hz01]
    exact hkA
  intro q
  constructor
  · intro hq
    rw [componentD_mem_iff A z0 k hkA q]
    have hconn := (componentD_mem_iff _ z0 k hkP q).mp hq
    clear hq
    induction hconn with
    | refl => exact ConnK.refl
    | step hc hqi hqk hadj ih =>
      next j q' =>
      have hq'T := (componentD_mem_iff _ z0 k hkP q').mpr
        (ConnK.step hc hqi hqk hadj)
      have hq'A : occD A q' = true := hold q' hq'T
      have hq'0 : q' ≠ i0 := by
        intro h; rw [h, hi0A] at hq'A; exact Bool.noConfusion hq'A
      have hq'1 : q' ≠ i1 := by
        intro h; rw [h, hi1A] at hq'A; exact Bool.noConfusion hq'A
      have hq'k : kindAt A q' = some k := by
        rw [← kindAt_joint_other A i0 i1 q' hq'0 hq'1]
        exact hqk
      exact ConnK.step ih hqi hq'k hadj
  · intro hq
    rw [componentD_mem_iff _ z0 k hkP q]
    have hconn := (componentD_mem_iff A z0 k hkA q).mp hq
    refine ConnK_transport A (jointPlaced n A i0 i1) k ?_ hconn
    intro x _ hx
    have hxA : occD A x = true := occD_of_kind hx
    have hx0 : x ≠ i0 := by
      intro h; rw [h, hi0A] at hxA; exact Bool.noConfusion hxA
    have hx1 : x ≠ i1 := by
      intro h; rw [h, hi1A] at hxA; exact Bool.noConfusion hxA
    rw [kindAt_joint_other A i0 i1 x hx0 hx1]
    exact hx

/-- The capture core, color-generic: an A-component of color cM.opp
    whose A-liberties all equal iM lies in the dead list of the cM
    move at iM. -/
theorem old_trapped_captured (A : Display n) (cM : DKind) (iM : Nat)
    (hwf : WFD A) (hiM : iM < n*n) (hcM : cM ≠ .r)
    (hiMA : occD A iM = false)
    (z0 : Nat) (hz0 : z0 < n*n) (hz0A : occD A z0 = true)
    (hkA : kindAt A z0 = some cM.opp)
    (hsole : ∀ l m, l ∈ allIdx n → occD A l = false →
      m ∈ componentD A z0 → adjI n l m = true → l = iM) :
    ∀ q, q ∈ componentD A z0 → q ∈ deadOppN n A cM iM := by
  have hagree : ∀ x, x ∈ allIdx n →
      (kindAt A x = some cM.opp ↔
        kindAt (placedN n A cM iM) x = some cM.opp) := by
    intro x _
    by_cases hxM : x = iM
    · subst x
      rw [kind_none_of_unocc hiMA, kindAt_placedN_self A cM iM hwf hiM]
      constructor
      · intro h; exact Option.noConfusion h
      · intro h; exact absurd (Option.some.inj h).symm (opp_ne_self hcM)
    · rw [kindAt_placedN_ne A cM iM x hxM]
  have hz0M : z0 ≠ iM := by
    intro h; rw [h, hiMA] at hz0A; exact Bool.noConfusion hz0A
  have hkP : kindAt (placedN n A cM iM) z0 = some cM.opp :=
    (hagree z0 (List.mem_range.mpr hz0)).mp hkA
  have htrans := componentD_transport A (placedN n A cM iM) cM.opp
    hagree z0 hkA hkP
  have hnl : noLibD (placedN n A cM iM)
      (componentD (placedN n A cM iM) z0) = true := by
    cases hnl0 : noLibD (placedN n A cM iM)
        (componentD (placedN n A cM iM) z0)
    · exfalso
      rcases (noLibD_eq_false_iff _ _).mp hnl0 with ⟨l, hlb, hlemp, m, hm, hadj⟩
      have hlM : l ≠ iM := by
        intro h
        subst l
        rw [occD_of_kind (kindAt_placedN_self A cM iM hwf hiM)] at hlemp
        exact Bool.noConfusion hlemp
      have hlA : occD A l = false := by
        rw [← occD_placedN_ne A cM iM l hlM]
        exact hlemp
      exact hlM (hsole l m hlb hlA ((htrans m).mpr hm) hadj)
    · rfl
  intro q hq
  exact deadOppN_component_closed A cM iM z0 q
    ((mem_deadOppN_iff A cM iM z0).mpr
      ⟨List.mem_range.mpr hz0, hkP, hnl⟩)
    ((htrans q).mp hq)

/-! ### Step 3: old trapped components are dead. -/

theorem step3_old_trapped_dead (A : Display n) (i0 i1 : Nat)
    (d1 c1 d2 c2 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (z0 : Nat) (hz0 : z0 < n*n) (hz0A : occD A z0 = true)
    (hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD A q = true)
    (htrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) z0) = true) :
    ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD c1 q = false := by
  have holdeq := old_component_eq A i0 i1 hi0A hi1A z0 hz0A hold
  have hz00 : z0 ≠ i0 := by
    intro h; rw [h, hi0A] at hz0A; exact Bool.noConfusion hz0A
  have hz01 : z0 ≠ i1 := by
    intro h; rw [h, hi1A] at hz0A; exact Bool.noConfusion hz0A
  rcases kind_some_of_occ hz0A with ⟨k, hkA⟩
  have hkP : kindAt (jointPlaced n A i0 i1) z0 = some k := by
    rw [kindAt_joint_other A i0 i1 z0 hz00 hz01]
    exact hkA
  cases k with
  | r => exact absurd hkA (hclass z0)
  | w =>
    -- white: sole liberty i0, captured by the black move, composite 1
    have hsole : ∀ l m, l ∈ allIdx n → occD A l = false →
        m ∈ componentD A z0 → adjI n l m = true → l = i0 := by
      intro l m hlb hlA hm hadj
      have hmT : m ∈ componentD (jointPlaced n A i0 i1) z0 :=
        (holdeq m).mpr hm
      by_cases hl0 : l = i0
      · exact hl0
      · exfalso
        by_cases hl1 : l = i1
        · -- the white stone at i1 would join the component
          subst l
          have hjoin : i1 ∈ componentD (jointPlaced n A i0 i1) z0 :=
            componentD_maximal (jointPlaced n A i0 i1) z0 .w hkP i1
              (List.mem_range.mpr hi1) (kindAt_joint_i1 A i0 i1 hwf hi1)
              m hmT hadj
          have := hold i1 hjoin
          rw [hi1A] at this
          exact Bool.noConfusion this
        · -- an off-placement liberty survives into A⁺
          have hlP : occD (jointPlaced n A i0 i1) l = false := by
            rw [occD_joint_other A i0 i1 l hl0 hl1]
            exact hlA
          have hlib : noLibD (jointPlaced n A i0 i1)
              (componentD (jointPlaced n A i0 i1) z0) = false :=
            (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, hlP, m, hmT, hadj⟩
          rw [htrap] at hlib
          exact Bool.noConfusion hlib
    have hdead := old_trapped_captured A .b i0 hwf hi0 (by decide) hi0A
      z0 hz0 hz0A hkA hsole
    intro q hq
    have hqA := (holdeq q).mp hq
    have hqdead := hdead q hqA
    rcases (mem_deadOppN_iff A .b i0 q).mp hqdead with ⟨hqb, hqk, _⟩
    have hqd1 : occD d1 q = false :=
      occD_output_dead A .b i0 d1 hb1 q (List.mem_range.mp hqb) hqdead
    exact persist_PB0 A i0 i1 d1 c1 hne hi1A hb1 hb2 q
      (occD_of_kind hqk) hqd1
  | b =>
    -- black: sole liberty i1, captured by the white move, composite 2;
    -- commuting carries the emptiness into c1
    have hsole : ∀ l m, l ∈ allIdx n → occD A l = false →
        m ∈ componentD A z0 → adjI n l m = true → l = i1 := by
      intro l m hlb hlA hm hadj
      have hmT : m ∈ componentD (jointPlaced n A i0 i1) z0 :=
        (holdeq m).mpr hm
      by_cases hl1 : l = i1
      · exact hl1
      · exfalso
        by_cases hl0 : l = i0
        · subst l
          have hjoin : i0 ∈ componentD (jointPlaced n A i0 i1) z0 :=
            componentD_maximal (jointPlaced n A i0 i1) z0 .b hkP i0
              (List.mem_range.mpr hi0)
              (kindAt_joint_i0 A i0 i1 hwf hi0 hne) m hmT hadj
          have := hold i0 hjoin
          rw [hi0A] at this
          exact Bool.noConfusion this
        · have hlP : occD (jointPlaced n A i0 i1) l = false := by
            rw [occD_joint_other A i0 i1 l hl0 hl1]
            exact hlA
          have hlib : noLibD (jointPlaced n A i0 i1)
              (componentD (jointPlaced n A i0 i1) z0) = false :=
            (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, hlP, m, hmT, hadj⟩
          rw [htrap] at hlib
          exact Bool.noConfusion hlib
    have hdead := old_trapped_captured A .w i1 hwf hi1 (by decide) hi1A
      z0 hz0 hz0A hkA hsole
    intro q hq
    have hqA := (holdeq q).mp hq
    have hqdead := hdead q hqA
    rcases (mem_deadOppN_iff A .w i1 q).mp hqdead with ⟨hqb, hqk, _⟩
    have hqd2 : occD d2 q = false :=
      occD_output_dead A .w i1 d2 hw1 q (List.mem_range.mp hqb) hqdead
    have hqc2 : occD c2 q = false :=
      persist_first_general A .w .b i1 i0 d2 c2 (fun h => hne h.symm)
        hi0A hw1 hw2 q (occD_of_kind hqk) hqd2
    rw [occ_eq_of_samecells hcomm q]
    exact hqc2
