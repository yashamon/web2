/- Step4.lean — Step 4: live trapped components are fresh, with a dead
   donor. Consumes Step 1 (dichotomy), Step 3 (old trapped are dead),
   and Infra6 (output legality). -/
import Step3
import Step5
import Infra6
open SgoDisplay

variable {n : Nat}

/-- B's stones are a component of the composite: membership of the
    composite component of a live stone agrees with its A⁺ component. -/
theorem live_component_eq (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi1A : occD A i1 = false)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (z0 : Nat) (hz0 : z0 < n*n) (k : DKind)
    (hocc0 : occD (jointPlaced n A i0 i1) z0 = true)
    (hk0 : kindAt (jointPlaced n A i0 i1) z0 = some k)
    (hstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      c1.get q = (jointPlaced n A i0 i1).get q) :
    ∀ q, q ∈ componentD c1 z0 ↔
      q ∈ componentD (jointPlaced n A i0 i1) z0 := by
  have hk0c : kindAt c1 z0 = some k := by
    unfold kindAt
    rw [hstand z0 (componentD_mem_self _ z0 k hk0)]
    exact hk0
  intro q
  constructor
  · -- composite stones are A⁺ stones with the same cells
    intro hq
    rw [componentD_mem_iff (jointPlaced n A i0 i1) z0 k hk0 q]
    refine ConnK_transport c1 (jointPlaced n A i0 i1) k ?_
      ((componentD_mem_iff c1 z0 k hk0c q).mp hq)
    intro z _ hz
    have hzocc : occD c1 z = true := occD_of_kind hz
    have hcell := composite_standing_cell A i0 i1 d1 c1 hwf hi1
      hb1 hb2 z hzocc
    unfold kindAt at hz ⊢
    rw [← hcell]
    exact hz
  · -- standing members keep kind k in the composite
    intro hq
    refine componentD_transport_rel (jointPlaced n A i0 i1) c1 k z0
      hk0 ?_ q hq
    intro m hm
    have hmk : kindAt (jointPlaced n A i0 i1) m = some k :=
      componentD_kind _ z0 k hk0 m hm
    unfold kindAt
    rw [hstand m hm]
    exact hmk

/-! ### Step 4. -/

theorem step4_live_trapped (A : Display n) (i0 i1 : Nat)
    (d1 c1 d2 c2 : Display n)
    (hwf : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (z0 : Nat) (hz0 : z0 < n*n)
    (hocc0 : occD (jointPlaced n A i0 i1) z0 = true)
    (htrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) z0) = true)
    (hlive : occD c1 z0 = true) :
    (i0 ∈ componentD (jointPlaced n A i0 i1) z0 ∨
      i1 ∈ componentD (jointPlaced n A i0 i1) z0) ∧
    ∃ l, l < n*n ∧ occD (jointPlaced n A i0 i1) l = true ∧
      (∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
        occD c1 q = false) ∧
      (∃ m, m ∈ componentD (jointPlaced n A i0 i1) z0 ∧
        adjI n l m = true) ∧
      kindAt (jointPlaced n A i0 i1) l
        ≠ kindAt (jointPlaced n A i0 i1) z0 := by
  rcases kind_some_of_occ hocc0 with ⟨k, hk0⟩
  -- the component stands entire
  have hstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      c1.get q = (jointPlaced n A i0 i1).get q := by
    rcases step1_dichotomy A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
      z0 hz0 hocc0 with h | ⟨hallemp, _⟩
    · exact h
    · exfalso
      have := hallemp z0 (componentD_mem_self _ z0 k hk0)
      rw [hlive] at this
      exact Bool.noConfusion this
  constructor
  · -- fresh, else Step 3 kills it
    by_cases h0 : i0 ∈ componentD (jointPlaced n A i0 i1) z0
    · exact Or.inl h0
    · by_cases h1 : i1 ∈ componentD (jointPlaced n A i0 i1) z0
      · exact Or.inr h1
      · exfalso
        -- old: all members are A-stones
        have hz00 : z0 ≠ i0 := by
          intro h
          subst z0
          exact h0 (componentD_mem_self _ i0 k hk0)
        have hz01 : z0 ≠ i1 := by
          intro h
          subst z0
          exact h1 (componentD_mem_self _ i1 k hk0)
        have hz0A : occD A z0 = true := by
          rw [← occD_joint_other A i0 i1 z0 hz00 hz01]
          exact hocc0
        have hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
            occD A q = true := by
          intro q hq
          have hq0 : q ≠ i0 := fun h => h0 (h ▸ hq)
          have hq1 : q ≠ i1 := fun h => h1 (h ▸ hq)
          have : occD (jointPlaced n A i0 i1) q = true :=
            occD_of_kind (componentD_kind _ z0 k hk0 q hq)
          rw [← occD_joint_other A i0 i1 q hq0 hq1]
          exact this
        have hdead := step3_old_trapped_dead A i0 i1 d1 c1 d2 c2 hwf
          hi0 hi1 hne hi0A hi1A hclass hb1 hb2 hw1 hw2 hcomm z0 hz0
          hz0A hold htrap
        have := hdead z0 (componentD_mem_self _ z0 k hk0)
        rw [hlive] at this
        exact Bool.noConfusion this
  · -- the donor, from the composite's legality
    have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
    have hlegald1 : IsLegal d1 :=
      goMoveN_legal A .b i0 d1 hwf hi0 (by decide) hclass hlegal hb1
    have hclassd1 : IsClassical d1 :=
      goMoveN_classical A .b i0 d1 hclass (by decide) hb1
    have hlegalc1 : IsLegal c1 :=
      goMoveN_legal d1 .w i1 c1 hwfd1 hi1 (by decide) hclassd1
        hlegald1 hb2
    have hBeq := live_component_eq A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A
      hb1 hb2 z0 hz0 k hocc0 hk0 hstand
    rcases (noLibD_eq_false_iff _ _).mp (hlegalc1 z0 hlive) with
      ⟨l, hlb, hlc1, m, hm, hadj⟩
    have hmB : m ∈ componentD (jointPlaced n A i0 i1) z0 := (hBeq m).mp hm
    -- the liberty cell is occupied in A⁺
    have hlP : occD (jointPlaced n A i0 i1) l = true := by
      cases ho : occD (jointPlaced n A i0 i1) l
      · exfalso
        have hlib : noLibD (jointPlaced n A i0 i1)
            (componentD (jointPlaced n A i0 i1) z0) = false :=
          (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, ho, m, hmB, hadj⟩
        rw [htrap] at hlib
        exact Bool.noConfusion hlib
      · rfl
    -- its A⁺ component is dead
    have hldead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
        occD c1 q = false := by
      rcases step1_dichotomy A i0 i1 d1 c1 hwf hi0 hi1 hne hi1A hb1 hb2
        l (List.mem_range.mp hlb) hlP with h | ⟨hallemp, _⟩
      · exfalso
        rcases kind_some_of_occ hlP with ⟨kl, hkl⟩
        have hcell := h l (componentD_mem_self _ l kl hkl)
        have : occD c1 l = true := by
          unfold occD
          rw [hcell]
          exact hlP
        rw [hlc1] at this
        exact Bool.noConfusion this
      · exact hallemp
    -- opposite colored
    have hkne : kindAt (jointPlaced n A i0 i1) l
        ≠ kindAt (jointPlaced n A i0 i1) z0 := by
      intro heq
      have hlk : kindAt (jointPlaced n A i0 i1) l = some k := by
        rw [heq]; exact hk0
      have hlB : l ∈ componentD (jointPlaced n A i0 i1) z0 :=
        componentD_maximal (jointPlaced n A i0 i1) z0 k hk0 l hlb hlk
          m hmB hadj
      have hcell := hstand l hlB
      have : occD c1 l = true := by
        unfold occD
        rw [hcell]
        exact hlP
      rw [hlc1] at this
      exact Bool.noConfusion this
    exact ⟨l, List.mem_range.mp hlb, hlP, hldead, ⟨m, hmB, hadj⟩, hkne⟩
