/- Step8.lean — Step 8 and the assembly: after the turn-t reduction
   removes the dead components, every stage is idle, and the
   resolution equals Cap_t alone with the composite's stone pattern.
   The final theorem lem_onestage_final closes the printed lemma. -/
import Step7
import Infra6
open SgoDisplay

variable {n : Nat}

/-! ### Display equality vs its Boolean test. -/

theorem display_eq_of_beq {X Y : Display n} (h : (X == Y) = true) :
    X = Y := by
  have hcells : (X.cells.isEqv Y.cells (· == ·)) = true := h
  rcases (Array.isEqv_iff_rel X.cells Y.cells _).mp hcells with ⟨hsz, hpt⟩
  have : X.cells = Y.cells :=
    Array.ext X.cells Y.cells hsz
      (fun i h1 _ => beq_iff_eq.mp (hpt i h1))
  cases X
  cases Y
  simp only at this
  rw [this]

theorem display_beq_self (X : Display n) : (X == X) = true := by
  show (X.cells.isEqv X.cells (· == ·)) = true
  exact Array.isEqv_self_beq X.cells

/-! ### In-bounds cell reads. -/

theorem get_in_bounds (X : Display n) (i : Nat)
    (h : i < X.cells.size) : X.get i = X.cells[i] := by
  unfold Display.get
  simp [Array.getD, h]

theorem display_ext {X Y : Display n} (h : X.cells = Y.cells) :
    X = Y := by
  cases X
  cases Y
  congr 1

/-! ### No captures on a legal board. -/

theorem nocap_of_legal (R c1 : Display n)
    (hsame : SameCells R c1) (hlegal1 : IsLegal c1)
    (k : DKind) (t' : Nat) : capturedOf R t' k = [] := by
  cases hd : capturedOf R t' k with
  | nil => rfl
  | cons w tl =>
    exfalso
    have hw : w ∈ capturedOf R t' k := by
      rw [hd]
      exact List.mem_cons.mpr (Or.inl rfl)
    rcases (mem_capturedOf R t' k w).mp hw with ⟨p, _, hkp, hcap, _⟩
    have htrap : noLibD R (componentD R p) = true := by
      have h := hcap
      simp only [isCaptured] at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      have h2 := h.1.1
      simp only [trappedOnTurn] at h2
      rw [Bool.and_eq_true] at h2
      exact h2.1
    have hkc1 : kindAt c1 p = some k := by
      rw [← hsame p]
      exact hkp
    have hagree : ∀ z, z ∈ allIdx n →
        (kindAt R z = some k ↔ kindAt c1 z = some k) := by
      intro z _
      rw [hsame z]
    have hcompeq := componentD_transport R c1 k hagree p hkp hkc1
    have hnl1 : noLibD c1 (componentD c1 p) = true := by
      rw [← noLibD_congr _ _ _ hcompeq,
        ← noLibD_occ_congr R c1 (occ_eq_of_samecells hsame)]
      exact htrap
    have := hlegal1 p (occD_of_kind hkc1)
    rw [hnl1] at this
    exact Bool.noConfusion this

/-! ### The reduction fixes a legal, well-formed board. -/

theorem basicCap_id (R : Display n) (hclassR : IsClassical R)
    (hwfR : WFD R)
    (hnocap : ∀ k t', capturedOf R t' k = []) (t' : Nat) :
    basicCap R t' = R := by
  have hsz : (basicCap R t').cells.size = R.cells.size := by
    rw [basicCap_size, hwfR]
  have hcells : (basicCap R t').cells = R.cells := by
    apply Array.ext _ _ hsz
    intro i h1 h2
    have hib : i < n*n := by
      rw [← hwfR]
      exact h2
    rw [← get_in_bounds (basicCap R t') i h1, ← get_in_bounds R i h2,
      basicCap_get R t' hclassR i hib, hnocap .b t', hnocap .w t']
    simp
  exact display_ext hcells

theorem capFix_id (R : Display n) (t' : Nat)
    (hb : basicCap R t' = R) :
    ∀ fuel, capFix fuel R t' = R
  | 0 => by simp only [capFix]
  | fuel+1 => by
    simp only [capFix]
    rw [hb, if_pos (display_beq_self R)]

theorem stages_id (R : Display n)
    (hb : ∀ t', basicCap R t' = R) :
    ∀ fuel t', stages fuel R t' = R
  | 0, _ => by simp only [stages]
  | fuel+1, t' => by
    simp only [stages]
    cases ht0 : (t' == 0)
    · simp only [Bool.false_eq_true, if_false]
      rw [capFix_id R t' (hb t') (n*n+1),
        if_pos (display_beq_self R)]
    · simp only [if_true]

/-- After the dead are removed, the board carries the composite's
    stone pattern. -/
theorem removed_samecells (A D : Display n) (t i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (R : Display n) (hR : CapIter A D t i0 i1 c1 R)
    (hrm : ∀ z, z < n*n → DeadStone A i0 i1 c1 z →
      occD R z = false) :
    SameCells R c1 := by
  intro x
  by_cases hxb : x < n*n
  · cases hAP : occD (jointPlaced n A i0 i1) x
    · have hR0 : occD R x = false := by
        cases ho : occD R x
        · rfl
        · exfalso
          have hcell := CapIter_occ_cell A D t i0 i1 c1 R hR x ho
          have hoccP : occD (PJ D t i0 i1) x = true := by
            unfold occD
            rw [← hcell]
            exact ho
          rw [PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells x,
            hAP] at hoccP
          exact Bool.noConfusion hoccP
      have hc0 : occD c1 x = false := by
        cases ho : occD c1 x
        · rfl
        · exfalso
          have h1 := goMoveN_occ_le d1 .w i1 c1 hb2 x ho
          have h2 := occ_PB1_le_joint A i0 i1 d1 hwfA hi1 hb1 x h1
          rw [hAP] at h2
          exact Bool.noConfusion h2
      rw [kind_none_of_unocc hR0, kind_none_of_unocc hc0]
    · cases hlv : occD c1 x
      · have hgone := hrm x hxb ⟨hAP, hlv⟩
        rw [kind_none_of_unocc hgone, kind_none_of_unocc hlv]
      · have hcell := CapIter_live_stands A D t i0 i1 c1 R hR x hxb
          hAP hlv
        have hc1cell := composite_standing_cell A i0 i1 d1 c1 hwfA hi1
          hb1 hb2 x hlv
        unfold kindAt
        rw [hcell, hc1cell]
        rw [show Option.map (fun c => c.1) ((PJ D t i0 i1).get x)
          = kindAt (PJ D t i0 i1) x from rfl,
          PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells x]
        rfl
  · have h1 : R.get x = none := get_oob R hR.1 x hxb
    have h2 : c1.get x = none :=
      get_oob c1 (goMoveN_size d1 .w i1 c1 hb2) x hxb
    unfold kindAt
    rw [h1, h2]

/-! ### The lemma. -/

/-- lem_onestage, general form, PROVED: on a legal classical board,
    for a commuting joint move, the resolution of the placed display
    is the turn-t capture fixpoint alone, and its stone pattern is the
    classical composite's. -/
theorem lem_onestage_final
    (hn : 2 ≤ n) (t : Nat) (ht : 1 ≤ t)
    (A D : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (i0 i1 : Nat) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (c1 c2 : Display n)
    (hcomp1 : (goMoveN n A .b i0).bind (fun d => goMoveN n d .w i1)
      = some c1)
    (hcomp2 : (goMoveN n A .w i1).bind (fun d => goMoveN n d .b i0)
      = some c2)
    (hcomm : SameCells c1 c2) :
    stages (t + 1) (placeJoint D t (some i0) (some i1)) t
      = capFix (n*n + 1) (placeJoint D t (some i0) (some i1)) t
    ∧ SameCells (stages (t + 1)
        (placeJoint D t (some i0) (some i1)) t) c1 := by
  -- split the composites
  rcases bind_move_split A .b .w i0 i1 c1 hcomp1 with ⟨d1, hb1, hb2⟩
  rcases bind_move_split A .w .b i1 i0 c2 hcomp2 with ⟨d2, hw1, hw2⟩
  have hi0A : occD A i0 = false := goMoveN_empty_at A .b i0 d1 hb1
  have hi1A : occD A i1 = false := goMoveN_empty_at A .w i1 d2 hw1
  -- the composite is legal
  have hwfd1 : WFD d1 := goMoveN_size A .b i0 d1 hb1
  have hlegald1 : IsLegal d1 :=
    goMoveN_legal A .b i0 d1 hwfA hi0 (by decide) hclass hlegal hb1
  have hclassd1 : IsClassical d1 :=
    goMoveN_classical A .b i0 d1 hclass (by decide) hb1
  have hlegalc1 : IsLegal c1 :=
    goMoveN_legal d1 .w i1 c1 hwfd1 hi1 (by decide) hclassd1
      hlegald1 hb2
  -- invariant iterates
  have hP : CapIter A D t i0 i1 c1 (PJ D t i0 i1) :=
    CapIter_P A D t i0 i1 c1 hwfA hwfD hi0 hi1 hne hcells
  have hD1 : CapIter A D t i0 i1 c1 (basicCap (PJ D t i0 i1) t) :=
    step6_preserved A D t i0 i1 d1 c1 d2 c2 hwfA hwfD hi0 hi1 hne
      hi0A hi1A hclass hlegal hcells hst hb1 hb2 hw1 hw2 hcomm _ hP
  have hD2 : CapIter A D t i0 i1 c1
      (basicCap (basicCap (PJ D t i0 i1) t) t) :=
    step6_preserved A D t i0 i1 d1 c1 d2 c2 hwfA hwfD hi0 hi1 hne
      hi0A hi1A hclass hlegal hcells hst hb1 hb2 hw1 hw2 hcomm _ hD1
  have hrm2 : ∀ z, z < n*n → DeadStone A i0 i1 c1 z →
      occD (basicCap (basicCap (PJ D t i0 i1) t) t) z = false :=
    fun z hz hd => step7_all_dead_removed A D t i0 i1 d1 c1 d2 c2
      hwfA hwfD hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst
      hb1 hb2 hw1 hw2 hcomm z hz hd
  have ht0 : (t == 0) = false := by
    cases hb : (t == 0)
    · rfl
    · exfalso
      have := beq_iff_eq.mp hb
      omega
  have hfuel : (n*n : Nat) = (n*n - 1) + 1 := by
    have : 0 < n*n := Nat.lt_of_le_of_lt (Nat.zero_le i0) hi0
    omega
  show stages (t + 1) (PJ D t i0 i1) t
      = capFix (n*n + 1) (PJ D t i0 i1) t
    ∧ SameCells (stages (t + 1) (PJ D t i0 i1) t) c1
  cases hg1 : (basicCap (PJ D t i0 i1) t == PJ D t i0 i1)
  · cases hg2 : (basicCap (basicCap (PJ D t i0 i1) t) t
        == basicCap (PJ D t i0 i1) t)
    · -- two removing applications: R = D2
      have hsame := removed_samecells A D t i0 i1 d1 c1 hwfA hwfD hi0
        hi1 hne hcells hb1 hb2 _ hD2 hrm2
      have hclassD2 := CapIter_classical A D t i0 i1 c1 _ hwfA hwfD
        hi0 hi1 hne hclass hcells hD2
      have hbfix : ∀ t'', basicCap
          (basicCap (basicCap (PJ D t i0 i1) t) t) t''
          = basicCap (basicCap (PJ D t i0 i1) t) t :=
        fun t'' => basicCap_id _ hclassD2 hD2.1
          (fun k t3 => nocap_of_legal _ c1 hsame hlegalc1 k t3) t''
      have hcapfix : capFix (n*n + 1) (PJ D t i0 i1) t
          = basicCap (basicCap (PJ D t i0 i1) t) t := by
        simp only [capFix]
        rw [hg1]
        simp only [Bool.false_eq_true, if_false]
        rw [hfuel]
        simp only [capFix]
        rw [hg2]
        simp only [Bool.false_eq_true, if_false]
        exact capFix_id _ t (hbfix t) (n*n - 1)
      have hstages : stages (t + 1) (PJ D t i0 i1) t
          = basicCap (basicCap (PJ D t i0 i1) t) t := by
        simp only [stages]
        rw [ht0]
        simp only [Bool.false_eq_true, if_false]
        rw [hcapfix]
        cases hg3 : (basicCap (basicCap (PJ D t i0 i1) t) t
            == PJ D t i0 i1)
        · simp only [Bool.false_eq_true, if_false]
          exact stages_id _ hbfix t (t - 1)
        · simp only [if_true]
          exact (display_eq_of_beq hg3).symm
      refine ⟨hstages.trans hcapfix.symm, ?_⟩
      rw [hstages]
      exact hsame
    · -- one removing application: R = D1
      have hD2eq := display_eq_of_beq hg2
      have hrm1 : ∀ z, z < n*n → DeadStone A i0 i1 c1 z →
          occD (basicCap (PJ D t i0 i1) t) z = false := by
        intro z hz hd
        have := hrm2 z hz hd
        rw [hD2eq] at this
        exact this
      have hsame := removed_samecells A D t i0 i1 d1 c1 hwfA hwfD hi0
        hi1 hne hcells hb1 hb2 _ hD1 hrm1
      have hclassD1 := CapIter_classical A D t i0 i1 c1 _ hwfA hwfD
        hi0 hi1 hne hclass hcells hD1
      have hbfix : ∀ t'', basicCap (basicCap (PJ D t i0 i1) t) t''
          = basicCap (PJ D t i0 i1) t :=
        fun t'' => basicCap_id _ hclassD1 hD1.1
          (fun k t3 => nocap_of_legal _ c1 hsame hlegalc1 k t3) t''
      have hcapfix : capFix (n*n + 1) (PJ D t i0 i1) t
          = basicCap (PJ D t i0 i1) t := by
        simp only [capFix]
        rw [hg1]
        simp only [Bool.false_eq_true, if_false]
        rw [hfuel]
        simp only [capFix]
        rw [hg2]
        simp only [if_true]
      have hstages : stages (t + 1) (PJ D t i0 i1) t
          = basicCap (PJ D t i0 i1) t := by
        simp only [stages]
        rw [ht0]
        simp only [Bool.false_eq_true, if_false]
        rw [hcapfix]
        cases hg3 : (basicCap (PJ D t i0 i1) t == PJ D t i0 i1)
        · simp only [Bool.false_eq_true, if_false]
          exact stages_id _ hbfix t (t - 1)
        · simp only [if_true]
          exact (display_eq_of_beq hg3).symm
      refine ⟨hstages.trans hcapfix.symm, ?_⟩
      rw [hstages]
      exact hsame
  · -- nothing to remove: R = P
    have hD1eq := display_eq_of_beq hg1
    have hrmP : ∀ z, z < n*n → DeadStone A i0 i1 c1 z →
        occD (PJ D t i0 i1) z = false := by
      intro z hz hd
      have := hrm2 z hz hd
      rw [hD1eq, hD1eq] at this
      exact this
    have hsame := removed_samecells A D t i0 i1 d1 c1 hwfA hwfD hi0
      hi1 hne hcells hb1 hb2 _ hP hrmP
    have hcapfix : capFix (n*n + 1) (PJ D t i0 i1) t
        = PJ D t i0 i1 := by
      simp only [capFix]
      rw [hg1]
      simp only [if_true]
    have hstages : stages (t + 1) (PJ D t i0 i1) t
        = PJ D t i0 i1 := by
      simp only [stages]
      rw [ht0]
      simp only [Bool.false_eq_true, if_false]
      rw [hcapfix, if_pos (display_beq_self _)]
    refine ⟨hstages.trans hcapfix.symm, ?_⟩
    rw [hstages]
    exact hsame
