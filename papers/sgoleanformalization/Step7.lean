/- Step7.lean — Step 7: every dead component is emptied within two
   applications of the basic reduction from the placed display. -/
import Step6
open SgoDisplay

variable {n : Nat}

/-- The placed display satisfies the invariant. -/
theorem CapIter_P (A D : Display n) (t i0 i1 : Nat) (c1 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hcells : SameCells D A) :
    CapIter A D t i0 i1 c1 (PJ D t i0 i1) := by
  refine ⟨placeJoint_size D t i0 i1 hne hwfD, ?_, ?_⟩
  · intro z _
    exact Or.inl rfl
  · intro z hz hAP hP
    exfalso
    rw [PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z, hAP] at hP
    exact Bool.noConfusion hP

/-- Condition 2 holds vacuously on a classical display. -/
theorem cond2_true (E : Display n) (hclassE : IsClassical E)
    (comp : List Nat) (c : DKind) :
    (((allIdx n).filter fun z =>
        kindAt E z == some DKind.r && comp.any fun q => adjI n z q).all
      fun r' => (allIdx n).all fun z =>
        !(adjI n z r' && (kindAt E z == some DKind.b ||
          kindAt E z == some DKind.w) &&
          (let Dc := componentD E z
           !(Dc.all comp.contains && comp.all Dc.contains) &&
           noLibD E Dc && kindAt E z != some c))) = true := by
  have hnil : ((allIdx n).filter fun z =>
      kindAt E z == some DKind.r && comp.any fun q => adjI n z q) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _
    intro hcontra
    rw [Bool.and_eq_true] at hcontra
    exact hclassE a (beq_iff_eq.mp hcontra.1)
  rw [hnil]
  rfl

/-- A standing dead stone spans a fully standing component. -/
theorem dead_stands_entire (A D : Display n) (t i0 i1 : Nat)
    (c1 : Display n) (E : Display n)
    (hE : CapIter A D t i0 i1 c1 E)
    (z : Nat) (hzb : z < n*n) (k : DKind)
    (hkAP : kindAt (jointPlaced n A i0 i1) z = some k)
    (hzE : occD E z = true) :
    ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z → occD E q = true := by
  intro q hq
  cases hqE : occD E q
  · exfalso
    have hqb := componentD_board (List.mem_range.mpr hzb) hkAP hq
    have hqocc : occD (jointPlaced n A i0 i1) q = true :=
      occD_of_kind (componentD_kind _ z k hkAP q hq)
    have hwhole := hE.2.2 q (List.mem_range.mp hqb) hqocc hqE
    have hzmem : z ∈ componentD (jointPlaced n A i0 i1) q :=
      (componentD_eq_mem (jointPlaced n A i0 i1) z q k
        (List.mem_range.mpr hzb) hkAP hq z).mpr
        (componentD_mem_self _ z k hkAP)
    have := hwhole z hzmem
    rw [hzE] at this
    exact Bool.noConfusion this
  · rfl

/-- A standing dead component is trapped on turn t in the iterate. -/
theorem dead_trappedOnTurn (A D : Display n) (t i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (E : Display n) (hE : CapIter A D t i0 i1 c1 E)
    (l : Nat) (hlb : l < n*n) (kl : DKind)
    (hklAP : kindAt (jointPlaced n A i0 i1) l = some kl)
    (hldead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
      occD c1 q = false)
    (hlE : occD E l = true) :
    trappedOnTurn E (componentD E l) t = true := by
  have hlPocc : occD (jointPlaced n A i0 i1) l = true :=
    occD_of_kind hklAP
  have hlcell : E.get l = (PJ D t i0 i1).get l :=
    CapIter_occ_cell A D t i0 i1 c1 E hE l hlE
  have hklE : kindAt E l = some kl := by
    unfold kindAt
    rw [hlcell]
    rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get l)
      = kindAt (PJ D t i0 i1) l from rfl,
      PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells l]
    exact hklAP
  have hklbw : kl = .b ∨ kl = .w := by
    rcases joint_kind_bw A i0 i1 hwfA hi0 hi1 hne hclass l hlPocc
      with h | h
    · rw [hklAP] at h
      exact Or.inl (Option.some.inj h)
    · rw [hklAP] at h
      exact Or.inr (Option.some.inj h)
  have hTstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
      occD E q = true :=
    dead_stands_entire A D t i0 i1 c1 E hE l hlb kl hklAP hlE
  have hcompeql := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0 hi1
    hne hcells hE l kl hklE hTstand
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
  have hnoLibEl : noLibD E (componentD E l) = true := by
    cases hnl : noLibD E (componentD E l)
    · exfalso
      rcases (noLibD_eq_false_iff _ _).mp hnl with
        ⟨l', hl'b, hl'E, m', hm', hadj'⟩
      have hm'T : m' ∈ componentD (jointPlaced n A i0 i1) l :=
        (hcompeql m').mp hm'
      cases hl'AP : occD (jointPlaced n A i0 i1) l'
      · have hlib : noLibD (jointPlaced n A i0 i1)
            (componentD (jointPlaced n A i0 i1) l) = false :=
          (noLibD_eq_false_iff _ _).mpr
            ⟨l', hl'b, hl'AP, m', hm'T, hadj'⟩
        rw [htrapT] at hlib
        exact Bool.noConfusion hlib
      · have hl'dead : DeadStone A i0 i1 c1 l' := by
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
        have hm'dead : DeadStone A i0 i1 c1 m' :=
          ⟨occD_of_kind (componentD_kind _ l kl hklAP m' hm'T),
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
  have hstampE : ∀ z, occD E z = true → stampAt E z ≤ t := by
    intro z hz
    unfold stampAt
    rw [CapIter_occ_cell A D t i0 i1 c1 E hE z hz]
    exact PJ_stamp_le D t i0 i1 hwfD hi0 hi1 hne hst z
  have hwitness : ∃ w, (w ∈ (componentD E l).map (stampAt E) ∨
      w ∈ (((allIdx n).filter fun z => occD E z &&
        !(componentD E l).contains z &&
        (componentD E l).any fun q => adjI n z q).map (stampAt E)))
      ∧ w = t := by
    by_cases hfreshT : i0 ∈ componentD (jointPlaced n A i0 i1) l ∨
        i1 ∈ componentD (jointPlaced n A i0 i1) l
    · rcases hfreshT with hf | hf
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
    · have holdT : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) l →
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
      have hplace : ∃ iM, iM < n*n ∧ (iM = i0 ∨ iM = i1) ∧
          ∃ m'', m'' ∈ componentD (jointPlaced n A i0 i1) l ∧
            adjI n iM m'' = true := by
        rcases hklbw with rfl | rfl
        · rcases hadjpl.2 rfl with ⟨m'', hm'', hadj''⟩
          exact ⟨i1, hi1, Or.inr rfl, m'', hm'', hadj''⟩
        · rcases hadjpl.1 rfl with ⟨m'', hm'', hadj''⟩
          exact ⟨i0, hi0, Or.inl rfl, m'', hm'', hadj''⟩
      rcases hplace with ⟨iM, hiMb, hiMid, m'', hm''T, hadjim⟩
      have hiMk : kindAt (jointPlaced n A i0 i1) iM = some .b ∨
          kindAt (jointPlaced n A i0 i1) iM = some .w := by
        rcases hiMid with h | h
        · rw [h]
          exact Or.inl (kindAt_joint_i0 A i0 i1 hwfA hi0 hne)
        · rw [h]
          exact Or.inr (kindAt_joint_i1 A i0 i1 hwfA hi1)
      have hiMocc : occD (jointPlaced n A i0 i1) iM = true := by
        rcases hiMk with h | h
        · exact occD_of_kind h
        · exact occD_of_kind h
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
              hiMb hm''dead.1 hiMocc hm''dead.2 hc (adjI_symm hadjim)
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
      have hiMnotmem : ¬ (componentD E l).contains iM = true := by
        intro hcont
        have hmem := List.contains_iff_mem.mp hcont
        have hiMinT : iM ∈ componentD (jointPlaced n A i0 i1) l :=
          (hcompeql iM).mp hmem
        rcases hiMid with rfl | rfl
        · exact hfreshT (Or.inl hiMinT)
        · exact hfreshT (Or.inr hiMinT)
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
  simp only [trappedOnTurn]
  rw [Bool.and_eq_true]
  refine ⟨hnoLibEl, ?_⟩
  rw [beq_iff_eq]
  exact hmax

/-- bne from ne, Nat. -/
theorem bne_of_ne {a b : Nat} (h : a ≠ b) : (a != b) = true := by
  unfold bne
  cases hc : (a == b)
  · rfl
  · exact absurd (beq_iff_eq.mp hc) h

/-- A dead old component standing in an iterate is captured there. -/
theorem dead_old_captured (A D : Display n) (t i0 i1 : Nat)
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
    (z0 : Nat) (hz0b : z0 < n*n) (kz : DKind)
    (hkzAP : kindAt (jointPlaced n A i0 i1) z0 = some kz)
    (hdead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD c1 q = false)
    (hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD A q = true)
    (hz0E : occD E z0 = true) :
    z0 ∈ capturedOf E t kz := by
  have hclassE : IsClassical E := CapIter_classical A D t i0 i1 c1 E
    hwfA hwfD hi0 hi1 hne hclass hcells hE
  have hz0cell : E.get z0 = (PJ D t i0 i1).get z0 :=
    CapIter_occ_cell A D t i0 i1 c1 E hE z0 hz0E
  have hkzE : kindAt E z0 = some kz := by
    unfold kindAt
    rw [hz0cell]
    rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get z0)
      = kindAt (PJ D t i0 i1) z0 from rfl,
      PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z0]
    exact hkzAP
  have hTstand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD E q = true :=
    dead_stands_entire A D t i0 i1 c1 E hE z0 hz0b kz hkzAP hz0E
  have hcompeq := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0 hi1
    hne hcells hE z0 kz hkzE hTstand
  have htrap : trappedOnTurn E (componentD E z0) t = true :=
    dead_trappedOnTurn A D t i0 i1 d1 c1 hwfA hwfD hi0 hi1 hne hi0A
      hi1A hclass hlegal hcells hst hb1 hb2 E hE z0 hz0b kz hkzAP
      hdead hz0E
  -- 3b, first conjunct: no stone of the component carries the turn
  have hconj1 : (componentD E z0).all
      (fun q => stampAt E q != t) = true := by
    rw [List.all_eq_true]
    intro q hq
    have hqAP : q ∈ componentD (jointPlaced n A i0 i1) z0 :=
      (hcompeq q).mp hq
    have hqA : occD A q = true := hold q hqAP
    have hq0 : q ≠ i0 := by
      intro h; rw [h, hi0A] at hqA; exact Bool.noConfusion hqA
    have hq1 : q ≠ i1 := by
      intro h; rw [h, hi1A] at hqA; exact Bool.noConfusion hqA
    have hstamp : stampAt E q < t := by
      unfold stampAt
      rw [CapIter_occ_cell A D t i0 i1 c1 E hE q (hTstand q hqAP)]
      exact PJ_stamp_other D t i0 i1 hne hst q hq0 hq1
    exact bne_of_ne (Nat.ne_of_lt hstamp)
  -- 3b, second conjunct: adjacent trapped components carry the turn
  have hconj2 : (((allIdx n).filter fun z => occD E z &&
      !(componentD E z0).contains z &&
      (componentD E z0).any fun q => adjI n z q).all fun z =>
        let Dc := componentD E z
        !(trappedOnTurn E Dc t &&
          !(Dc.any fun q => stampAt E q == t &&
            kindAt E q != some DKind.r))) = true := by
    rw [List.all_eq_true]
    intro z hzf
    have hzprops := (List.mem_filter.mp hzf).2
    rw [Bool.and_eq_true, Bool.and_eq_true] at hzprops
    obtain ⟨⟨hzE, hznc⟩, hzany⟩ := hzprops
    rcases List.any_eq_true.mp hzany with ⟨m0, hm0, hadjz⟩
    cases htz : trappedOnTurn E (componentD E z) t
    · simp [htz]
    · -- z is live: else it joins the dead component
      have hm0AP : m0 ∈ componentD (jointPlaced n A i0 i1) z0 :=
        (hcompeq m0).mp hm0
      have hm0dead : DeadStone A i0 i1 c1 m0 :=
        ⟨occD_of_kind (componentD_kind _ z0 kz hkzAP m0 hm0AP),
          hdead m0 hm0AP⟩
      have hzb : z < n*n := List.mem_range.mp (List.mem_filter.mp hzf).1
      have hzAP : occD (jointPlaced n A i0 i1) z = true := by
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z
        unfold occD at hpo ⊢
        rw [← CapIter_occ_cell A D t i0 i1 c1 E hE z hzE] at hpo
        rw [← hpo]
        exact hzE
      have hzlive : occD c1 z = true := by
        cases hc : occD c1 z
        · exfalso
          have hzT : z ∈ componentD (jointPlaced n A i0 i1) m0 :=
            step5_adjacent_dead_same_comp A i0 i1 d1 c1 hwfA hi0 hi1
              hne hi1A hclass hb1 hb2 m0 z
              (List.mem_range.mp (componentD_board
                (List.mem_range.mpr hz0b) hkzAP hm0AP))
              hzb hm0dead.1 hzAP hm0dead.2 hc (adjI_symm hadjz)
          have hzin : z ∈ componentD (jointPlaced n A i0 i1) z0 :=
            (componentD_eq_mem (jointPlaced n A i0 i1) z0 m0 kz
              (List.mem_range.mpr hz0b) hkzAP hm0AP z).mp hzT
          have : z ∈ componentD E z0 := (hcompeq z).mpr hzin
          rw [List.contains_iff_mem.mpr this] at hznc
          exact Bool.noConfusion hznc
        · rfl
      -- z's component is a live trapped component: fresh by Step 4
      rcases kind_some_of_occ hzAP with ⟨kz', hkz'⟩
      have hkz'E : kindAt E z = some kz' := by
        unfold kindAt
        rw [CapIter_occ_cell A D t i0 i1 c1 E hE z hzE]
        rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get z)
          = kindAt (PJ D t i0 i1) z from rfl,
          PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z]
        exact hkz'
      have hstandz : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z →
          c1.get q = (jointPlaced n A i0 i1).get q := by
        rcases step1_dichotomy A i0 i1 d1 c1 hwfA hi0 hi1 hne hi1A hb1
          hb2 z hzb hzAP with h | ⟨hallemp, _⟩
        · exact h
        · exfalso
          have := hallemp z (componentD_mem_self _ z kz' hkz')
          rw [hzlive] at this
          exact Bool.noConfusion this
      have hzstandE : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z →
          occD E q = true := by
        intro q hq
        have hqk := componentD_kind _ z kz' hkz' q hq
        have hqb := componentD_board (List.mem_range.mpr hzb) hkz' hq
        have hqlive : occD c1 q = true := by
          unfold occD
          rw [hstandz q hq]
          exact occD_of_kind hqk
        have hcell := CapIter_live_stands A D t i0 i1 c1 E hE q
          (List.mem_range.mp hqb) (occD_of_kind hqk) hqlive
        unfold occD
        rw [hcell]
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells q
        unfold occD at hpo
        rw [hpo]
        exact occD_of_kind hqk
      have hcompeqz := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0
        hi1 hne hcells hE z kz' hkz'E hzstandE
      -- trapped in A⁺
      have hnoLibz : noLibD E (componentD E z) = true := by
        have h := htz
        simp only [trappedOnTurn] at h
        rw [Bool.and_eq_true] at h
        exact h.1
      have hEoccle : ∀ w, occD E w = true →
          occD (PJ D t i0 i1) w = true := by
        intro w hw
        unfold occD
        rw [← CapIter_occ_cell A D t i0 i1 c1 E hE w hw]
        exact hw
      have htrapAP : noLibD (jointPlaced n A i0 i1)
          (componentD (jointPlaced n A i0 i1) z) = true := by
        have h1 : noLibD (PJ D t i0 i1) (componentD E z) = true :=
          noLibD_mono _ E _ hEoccle hnoLibz
        have h2 : noLibD (jointPlaced n A i0 i1)
            (componentD E z) = true := by
          rw [noLibD_occ_congr (jointPlaced n A i0 i1) (PJ D t i0 i1)
            (fun w => (PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne
              hcells w).symm) (componentD E z)]
          exact h1
        rw [← noLibD_congr _ _ _ hcompeqz]
        exact h2
      obtain ⟨hfresh, _⟩ := step4_live_trapped A i0 i1 d1 c1 d2 c2
        hwfA hi0 hi1 hne hi0A hi1A hclass hlegal hb1 hb2 hw1 hw2
        hcomm z hzb hzAP htrapAP hzlive
      -- the fresh placement carries the turn stamp
      have hexists : (componentD E z).any (fun q =>
          stampAt E q == t && kindAt E q != some DKind.r) = true := by
        rcases hfresh with hf | hf
        · refine List.any_eq_true.mpr ⟨i0, (hcompeqz i0).mpr hf, ?_⟩
          rw [Bool.and_eq_true]
          have hcell := CapIter_occ_cell A D t i0 i1 c1 E hE i0
            (hzstandE i0 hf)
          constructor
          · rw [beq_iff_eq]
            unfold stampAt
            rw [hcell]
            exact PJ_stamp_i0 D t i0 i1 hwfD hi0 hne
          · have : kindAt E i0 = some .b := by
              unfold kindAt
              rw [hcell]
              rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get i0)
                = kindAt (PJ D t i0 i1) i0 from rfl,
                PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells i0]
              exact kindAt_joint_i0 A i0 i1 hwfA hi0 hne
            rw [this]
            rfl
        · refine List.any_eq_true.mpr ⟨i1, (hcompeqz i1).mpr hf, ?_⟩
          rw [Bool.and_eq_true]
          have hcell := CapIter_occ_cell A D t i0 i1 c1 E hE i1
            (hzstandE i1 hf)
          constructor
          · rw [beq_iff_eq]
            unfold stampAt
            rw [hcell]
            exact PJ_stamp_i1 D t i0 i1 hwfD hi1 hne
          · have : kindAt E i1 = some .w := by
              unfold kindAt
              rw [hcell]
              rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get i1)
                = kindAt (PJ D t i0 i1) i1 from rfl,
                PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells i1]
              exact kindAt_joint_i1 A i0 i1 hwfA hi1
            rw [this]
            rfl
      simp only [htz, hexists]
      rfl
  -- assemble the capture
  have hcap : isCaptured E (componentD E z0) kz t = true := by
    simp only [isCaptured]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨htrap, cond2_true E hclassE (componentD E z0) kz⟩, ?_⟩
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true]
    exact ⟨hconj1, hconj2⟩
  exact (mem_capturedOf E t kz z0).mpr
    ⟨z0, List.mem_range.mpr hz0b, hkzE, hcap,
      componentD_mem_self E z0 kz hkzE⟩

/-- A component captured by one move is disjoint from the OTHER
    placement's fresh component: an old part of that component would
    hold the other placement intersection as a liberty in the
    capturing move's placed diagram. -/
theorem deadOpp_disjoint_othercomp (A : Display n) (i0 i1 : Nat)
    (cM : DKind) (iM iOther : Nat)
    (hio : (cM = .b ∧ iM = i0 ∧ iOther = i1) ∨
      (cM = .w ∧ iM = i1 ∧ iOther = i0))
    (hwfA : WFD A) (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (l : Nat) (hld : l ∈ deadOppN n A cM iM)
    (hlT : l ∈ componentD (jointPlaced n A i0 i1) iOther) : False := by
  have hcMnr : cM ≠ .r := by
    rcases hio with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
  have hiOthb : iOther < n*n := by
    rcases hio with ⟨_, _, ho⟩ | ⟨_, _, ho⟩
    · rw [ho]; exact hi1
    · rw [ho]; exact hi0
  have hiMb : iM < n*n := by
    rcases hio with ⟨_, hm, _⟩ | ⟨_, hm, _⟩
    · rw [hm]; exact hi0
    · rw [hm]; exact hi1
  have hiOthA : occD A iOther = false := by
    rcases hio with ⟨_, _, ho⟩ | ⟨_, _, ho⟩
    · rw [ho]; exact hi1A
    · rw [ho]; exact hi0A
  have hiMne : iM ≠ iOther := by
    rcases hio with ⟨_, hm, ho⟩ | ⟨_, hm, ho⟩
    · rw [hm, ho]; exact hne
    · rw [hm, ho]; exact fun h => hne h.symm
  have hkOth : kindAt (jointPlaced n A i0 i1) iOther = some cM.opp := by
    rcases hio with ⟨rfl, _, ho⟩ | ⟨rfl, _, ho⟩
    · rw [ho]; exact kindAt_joint_i1 A i0 i1 hwfA hi1
    · rw [ho]; exact kindAt_joint_i0 A i0 i1 hwfA hi0 hne
  have hkM : kindAt (jointPlaced n A i0 i1) iM = some cM := by
    rcases hio with ⟨rfl, hm, _⟩ | ⟨rfl, hm, _⟩
    · rw [hm]; exact kindAt_joint_i0 A i0 i1 hwfA hi0 hne
    · rw [hm]; exact kindAt_joint_i1 A i0 i1 hwfA hi1
  have hother : ∀ z, z ≠ iM → z ≠ iOther →
      kindAt (jointPlaced n A i0 i1) z = kindAt A z := by
    intro z hzM hzOth
    rcases hio with ⟨_, hm, ho⟩ | ⟨_, hm, ho⟩
    · rw [hm] at hzM
      rw [ho] at hzOth
      exact kindAt_joint_other A i0 i1 z hzM hzOth
    · rw [hm] at hzM
      rw [ho] at hzOth
      exact kindAt_joint_other A i0 i1 z hzOth hzM
  rcases (mem_deadOppN_iff A cM iM l).mp hld with ⟨hlb, hlkP, hlnl⟩
  have hlM : l ≠ iM := by
    intro h
    subst l
    rw [kindAt_placedN_self A cM iM hwfA hiMb] at hlkP
    exact opp_ne_self hcMnr (Option.some.inj hlkP).symm
  have hlAk : kindAt A l = some cM.opp := by
    rw [← kindAt_placedN_ne A cM iM l hlM]
    exact hlkP
  have hlOth : l ≠ iOther := by
    intro h
    subst l
    rw [kind_none_of_unocc hiOthA] at hlAk
    exact Option.noConfusion hlAk
  have hiOthPB : occD (placedN n A cM iM) iOther = false := by
    rw [occD_placedN_ne A cM iM iOther (fun h => hiMne h.symm)]
    exact hiOthA
  have hconn : ConnK (jointPlaced n A i0 i1) cM.opp l iOther := by
    have hlk : kindAt (jointPlaced n A i0 i1) l = some cM.opp := by
      rw [hother l hlM hlOth]
      exact hlAk
    have h1 := (componentD_mem_iff (jointPlaced n A i0 i1) iOther
      cM.opp hkOth l).mp hlT
    exact ConnK_symm (List.mem_range.mpr hiOthb) hkOth h1
  have hkey : ∀ x, ConnK (jointPlaced n A i0 i1) cM.opp l x →
      ((x ≠ iOther → (x ∈ componentD (placedN n A cM iM) l ∨
        ∃ j, j ∈ componentD (placedN n A cM iM) l ∧
          adjI n iOther j = true)) ∧
       (x = iOther → ∃ j, j ∈ componentD (placedN n A cM iM) l ∧
          adjI n iOther j = true)) := by
    intro x hx
    induction hx with
    | refl =>
      constructor
      · intro _
        exact Or.inl (componentD_mem_self _ l cM.opp hlkP)
      · intro h
        exact absurd h hlOth
    | step hc hqi hqk hadj ih =>
      next j q =>
      rcases ih with ⟨ihne, ihend⟩
      constructor
      · intro hqOth
        by_cases hjOth : j = iOther
        · exact Or.inr (ihend hjOth)
        · rcases ihne hjOth with hj | hW
          · left
            have hqM : q ≠ iM := by
              intro h
              subst q
              rw [hkM] at hqk
              exact opp_ne_self hcMnr (Option.some.inj hqk).symm
            have hqPB : kindAt (placedN n A cM iM) q = some cM.opp := by
              rw [kindAt_placedN_ne A cM iM q hqM, ← hother q hqM hqOth]
              exact hqk
            exact componentD_maximal (placedN n A cM iM) l cM.opp hlkP
              q hqi hqPB j hj hadj
          · exact Or.inr hW
      · intro hqOth
        subst q
        have hjOth : j ≠ iOther := by
          intro h
          subst j
          rw [adjI_irrefl] at hadj
          exact Bool.noConfusion hadj
        rcases ihne hjOth with hj | hW
        · exact ⟨j, hj, hadj⟩
        · exact hW
  rcases (hkey iOther hconn).2 rfl with ⟨j, hj, hadjOth⟩
  have hlib : noLibD (placedN n A cM iM)
      (componentD (placedN n A cM iM) l) = false :=
    (noLibD_eq_false_iff _ _).mpr
      ⟨iOther, List.mem_range.mpr hiOthb, hiOthPB, j, hj, hadjOth⟩
  rw [hlnl] at hlib
  exact Bool.noConfusion hlib

/-- A shield breaker for the black placed component: a dead stone of an
    old dead component adjacent to it. -/
def ShieldBreaker (A : Display n) (i0 i1 : Nat) (c1 : Display n)
    (zR : Nat) : Prop :=
  ∃ w', w' < n*n ∧ DeadStone A i0 i1 c1 w' ∧
    (∀ q, q ∈ componentD (jointPlaced n A i0 i1) w' → occD A q = true) ∧
    ∃ zw, zw ∈ componentD (jointPlaced n A i0 i1) zR ∧
      adjI n w' zw = true

/-- Orientation 1: the black placed component, live and trapped, has a
    shield breaker. -/
theorem shield_breaker_b (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hwfA : WFD A)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (hZlive : occD c1 i0 = true)
    (hZtrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) i0) = true) :
    ShieldBreaker A i0 i1 c1 i0 := by
  by_cases hbr : ShieldBreaker A i0 i1 c1 i0
  · exact hbr
  · exfalso
    -- a captured white adjacent to the component would be a breaker
    have hnodead : ∀ l' m', l' ∈ deadOppN n A .b i0 →
        m' ∈ componentD (jointPlaced n A i0 i1) i0 →
        adjI n l' m' = true → False := by
      intro l' m' hl'd hm'Z hadj'
      apply hbr
      rcases (mem_deadOppN_iff A .b i0 l').mp hl'd with ⟨hl'b, hl'k, _⟩
      have hl'i0 : l' ≠ i0 := by
        intro h
        subst l'
        rw [kindAt_placedN_self A .b i0 hwfA hi0] at hl'k
        exact DKind.noConfusion (Option.some.inj hl'k)
      have hl'A : kindAt A l' = some .w := by
        rw [← kindAt_placedN_ne A .b i0 l' hl'i0]
        exact hl'k
      have hl'i1 : l' ≠ i1 := by
        intro h
        subst l'
        rw [kind_none_of_unocc hi1A] at hl'A
        exact Option.noConfusion hl'A
      have hl'AP : kindAt (jointPlaced n A i0 i1) l' = some .w := by
        rw [kindAt_joint_other A i0 i1 l' hl'i0 hl'i1]
        exact hl'A
      have hl'd1 : occD d1 l' = false :=
        occD_output_dead A .b i0 d1 hb1 l' (List.mem_range.mp hl'b) hl'd
      have hl'c1 : occD c1 l' = false :=
        persist_PB0 A i0 i1 d1 c1 hne hi1A hb1 hb2 l'
          (occD_of_kind hl'k) hl'd1
      refine ⟨l', List.mem_range.mp hl'b,
        ⟨occD_of_kind hl'AP, hl'c1⟩, ?_, m', hm'Z, hadj'⟩
      -- the component is old: white, and disjoint from i1's component
      intro q hq
      have hqk : kindAt (jointPlaced n A i0 i1) q = some .w :=
        componentD_kind _ l' .w hl'AP q hq
      have hq0 : q ≠ i0 := by
        intro h
        subst q
        rw [kindAt_joint_i0 A i0 i1 hwfA hi0 hne] at hqk
        exact DKind.noConfusion (Option.some.inj hqk)
      have hq1 : q ≠ i1 := by
        intro h
        subst q
        -- then l' would lie in i1's fresh component
        have hl'in : l' ∈ componentD (jointPlaced n A i0 i1) i1 := by
          have := componentD_eq_mem (jointPlaced n A i0 i1) l' i1 .w
            hl'b hl'AP hq
          exact (this l').mpr
            (componentD_mem_self _ l' .w hl'AP)
        exact deadOpp_disjoint_othercomp A i0 i1 .b i0 i1
          (Or.inl ⟨rfl, rfl, rfl⟩) hwfA hi0 hi1 hne hi0A hi1A l'
          hl'd hl'in
      rw [← occD_joint_other A i0 i1 q hq0 hq1]
      exact occD_of_kind hqk
    -- the placed component's data
    have hkZ : kindAt (jointPlaced n A i0 i1) i0 = some .b :=
      kindAt_joint_i0 A i0 i1 hwfA hi0 hne
    cases hsui : suicideN n A .b i0
    · -- no suicide: the component dies at the second move
      have hres := goMoveN_result A .b i0 d1 hb1
      rw [hsui] at hres
      simp at hres
      -- i0 stands in d1
      have hd1i0 : kindAt d1 i0 = some .b := by
        rw [hres]
        exact kindAt_afterCapN_self A .b i0 hwfA hi0 (by decide)
      have hPB1i0 : kindAt (placedN n d1 .w i1) i0 = some .b := by
        rw [kindAt_placedN_ne d1 .w i1 i0 hne]
        exact hd1i0
      -- its second-placed component has no liberties
      have hnl : noLibD (placedN n d1 .w i1)
          (componentD (placedN n d1 .w i1) i0) = true := by
        cases hnl0 : noLibD (placedN n d1 .w i1)
            (componentD (placedN n d1 .w i1) i0)
        · exfalso
          rcases (noLibD_eq_false_iff _ _).mp hnl0 with
            ⟨l', hl'b, hl'E, m', hm', hadj'⟩
          -- transport the member into the A⁺ component
          have hm'Z : m' ∈ componentD (jointPlaced n A i0 i1) i0 := by
            rw [componentD_mem_iff (jointPlaced n A i0 i1) i0 .b hkZ m']
            refine ConnK_transport (placedN n d1 .w i1)
              (jointPlaced n A i0 i1) .b ?_
              ((componentD_mem_iff (placedN n d1 .w i1) i0 .b
                hPB1i0 m').mp hm')
            intro x _ hx
            have hx1 : x ≠ i1 := by
              intro h
              subst x
              rw [kindAt_placedN_self d1 .w i1
                (goMoveN_size A .b i0 d1 hb1) hi1] at hx
              exact DKind.noConfusion (Option.some.inj hx)
            rw [kindAt_placedN_ne d1 .w i1 x hx1] at hx
            have hoccd1x : occD d1 x = true := occD_of_kind hx
            have hcell := goMoveN_standing A .b i0 d1 hb1 x hoccd1x
            have hxPB0 : kindAt (placedN n A .b i0) x = some .b := by
              unfold kindAt at hx ⊢
              rw [← hcell]
              exact hx
            by_cases hx0 : x = i0
            · subst x
              exact hkZ
            · rw [kindAt_placedN_ne A .b i0 x hx0] at hxPB0
              rw [kindAt_joint_other A i0 i1 x hx0 hx1]
              exact hxPB0
          have hl'i1 : l' ≠ i1 := by
            intro h
            subst l'
            rw [occD_of_kind (kindAt_placedN_self d1 .w i1
              (goMoveN_size A .b i0 d1 hb1) hi1)] at hl'E
            exact Bool.noConfusion hl'E
          have hl'd1 : occD d1 l' = false := by
            rw [← occD_placedN_ne d1 .w i1 l' hl'i1]
            exact hl'E
          cases hl'A : occD A l'
          · -- an untouched empty cell: an A⁺ liberty of the component
            have hl'i0 : l' ≠ i0 := by
              intro h
              subst l'
              have : occD d1 i0 = true := occD_of_kind hd1i0
              rw [hl'd1] at this
              exact Bool.noConfusion this
            have hl'AP : occD (jointPlaced n A i0 i1) l' = false := by
              rw [occD_joint_other A i0 i1 l' hl'i0 hl'i1]
              exact hl'A
            have hlib : noLibD (jointPlaced n A i0 i1)
                (componentD (jointPlaced n A i0 i1) i0) = false :=
              (noLibD_eq_false_iff _ _).mpr
                ⟨l', hl'b, hl'AP, m', hm'Z, hadj'⟩
            rw [hZtrap] at hlib
            exact Bool.noConfusion hlib
          · -- died at the first move: a breaker after all
            have hl'i0 : l' ≠ i0 := by
              intro h
              subst l'
              rw [hi0A] at hl'A
              exact Bool.noConfusion hl'A
            have hl'PB0 : occD (placedN n A .b i0) l' = true := by
              rw [occD_placedN_ne A .b i0 l' hl'i0]
              exact hl'A
            rcases died_classify A .b i0 d1 hb1 l'
              (List.mem_range.mp hl'b) hl'PB0 hl'd1 with hdead | ⟨hs, _⟩
            · exact hnodead l' m' hdead hm'Z hadj'
            · rw [hsui] at hs
              exact Bool.noConfusion hs
        · rfl
      -- the component is removed by the second move
      have hi0dead : i0 ∈ deadOppN n d1 .w i1 :=
        (mem_deadOppN_iff d1 .w i1 i0).mpr
          ⟨List.mem_range.mpr hi0, hPB1i0, hnl⟩
      have := occD_output_dead d1 .w i1 c1 hb2 i0 hi0 hi0dead
      rw [hZlive] at this
      exact Bool.noConfusion this
    · -- suicide: the placed component dies at once
      have hiown : i0 ∈ ownCompN n A .b i0 :=
        componentD_mem_self _ i0 .b
          (kindAt_afterCapN_self A .b i0 hwfA hi0 (by decide))
      have hd1i0 : occD d1 i0 = false := by
        have hres := goMoveN_result A .b i0 d1 hb1
        rw [hres, if_pos hsui, occD_erasedN A .b i0 i0 hi0,
          if_pos (List.contains_iff_mem.mpr hiown)]
      have hc1i0 : occD c1 i0 = false :=
        persist_PB0 A i0 i1 d1 c1 hne hi1A hb1 hb2 i0
          (occD_of_kind (kindAt_placedN_self A .b i0 hwfA hi0)) hd1i0
      rw [hZlive] at hc1i0
      exact Bool.noConfusion hc1i0

/-- Orientation 2: the white placed component, live and trapped, has a
    shield breaker (runs along the second composite, landing in c1
    through the commuting hypothesis). -/
theorem shield_breaker_w (A : Display n) (i0 i1 : Nat)
    (d2 c2 c1 : Display n)
    (hwfA : WFD A)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hw1 : goMoveN n A .w i1 = some d2)
    (hw2 : goMoveN n d2 .b i0 = some c2)
    (hcomm : SameCells c1 c2)
    (hZlive : occD c1 i1 = true)
    (hZtrap : noLibD (jointPlaced n A i0 i1)
      (componentD (jointPlaced n A i0 i1) i1) = true) :
    ShieldBreaker A i0 i1 c1 i1 := by
  by_cases hbr : ShieldBreaker A i0 i1 c1 i1
  · exact hbr
  · exfalso
    have hnodead : ∀ l' m', l' ∈ deadOppN n A .w i1 →
        m' ∈ componentD (jointPlaced n A i0 i1) i1 →
        adjI n l' m' = true → False := by
      intro l' m' hl'd hm'Z hadj'
      apply hbr
      rcases (mem_deadOppN_iff A .w i1 l').mp hl'd with ⟨hl'b, hl'k, _⟩
      have hl'i1 : l' ≠ i1 := by
        intro h
        subst l'
        rw [kindAt_placedN_self A .w i1 hwfA hi1] at hl'k
        exact DKind.noConfusion (Option.some.inj hl'k)
      have hl'A : kindAt A l' = some .b := by
        rw [← kindAt_placedN_ne A .w i1 l' hl'i1]
        exact hl'k
      have hl'i0 : l' ≠ i0 := by
        intro h
        subst l'
        rw [kind_none_of_unocc hi0A] at hl'A
        exact Option.noConfusion hl'A
      have hl'AP : kindAt (jointPlaced n A i0 i1) l' = some .b := by
        rw [kindAt_joint_other A i0 i1 l' hl'i0 hl'i1]
        exact hl'A
      have hl'd2 : occD d2 l' = false :=
        occD_output_dead A .w i1 d2 hw1 l' (List.mem_range.mp hl'b) hl'd
      have hl'c2 : occD c2 l' = false :=
        persist_first_general A .w .b i1 i0 d2 c2
          (fun h => hne h.symm) hi0A hw1 hw2 l'
          (occD_of_kind hl'k) hl'd2
      have hl'c1 : occD c1 l' = false := by
        rw [occ_eq_of_samecells hcomm l']
        exact hl'c2
      refine ⟨l', List.mem_range.mp hl'b,
        ⟨occD_of_kind hl'AP, hl'c1⟩, ?_, m', hm'Z, hadj'⟩
      intro q hq
      have hqk : kindAt (jointPlaced n A i0 i1) q = some .b :=
        componentD_kind _ l' .b hl'AP q hq
      have hq1 : q ≠ i1 := by
        intro h
        subst q
        rw [kindAt_joint_i1 A i0 i1 hwfA hi1] at hqk
        exact DKind.noConfusion (Option.some.inj hqk)
      have hq0 : q ≠ i0 := by
        intro h
        subst q
        have hl'in : l' ∈ componentD (jointPlaced n A i0 i1) i0 := by
          have := componentD_eq_mem (jointPlaced n A i0 i1) l' i0 .b
            hl'b hl'AP hq
          exact (this l').mpr
            (componentD_mem_self _ l' .b hl'AP)
        exact deadOpp_disjoint_othercomp A i0 i1 .w i1 i0
          (Or.inr ⟨rfl, rfl, rfl⟩) hwfA hi0 hi1 hne hi0A hi1A l'
          hl'd hl'in
      rw [← occD_joint_other A i0 i1 q hq0 hq1]
      exact occD_of_kind hqk
    have hkZ : kindAt (jointPlaced n A i0 i1) i1 = some .w :=
      kindAt_joint_i1 A i0 i1 hwfA hi1
    cases hsui : suicideN n A .w i1
    · have hres := goMoveN_result A .w i1 d2 hw1
      rw [hsui] at hres
      simp at hres
      have hd2i1 : kindAt d2 i1 = some .w := by
        rw [hres]
        exact kindAt_afterCapN_self A .w i1 hwfA hi1 (by decide)
      have hPB2i1 : kindAt (placedN n d2 .b i0) i1 = some .w := by
        rw [kindAt_placedN_ne d2 .b i0 i1 (fun h => hne h.symm)]
        exact hd2i1
      have hnl : noLibD (placedN n d2 .b i0)
          (componentD (placedN n d2 .b i0) i1) = true := by
        cases hnl0 : noLibD (placedN n d2 .b i0)
            (componentD (placedN n d2 .b i0) i1)
        · exfalso
          rcases (noLibD_eq_false_iff _ _).mp hnl0 with
            ⟨l', hl'b, hl'E, m', hm', hadj'⟩
          have hm'Z : m' ∈ componentD (jointPlaced n A i0 i1) i1 := by
            rw [componentD_mem_iff (jointPlaced n A i0 i1) i1 .w hkZ m']
            refine ConnK_transport (placedN n d2 .b i0)
              (jointPlaced n A i0 i1) .w ?_
              ((componentD_mem_iff (placedN n d2 .b i0) i1 .w
                hPB2i1 m').mp hm')
            intro x _ hx
            have hx0 : x ≠ i0 := by
              intro h
              subst x
              rw [kindAt_placedN_self d2 .b i0
                (goMoveN_size A .w i1 d2 hw1) hi0] at hx
              exact DKind.noConfusion (Option.some.inj hx)
            rw [kindAt_placedN_ne d2 .b i0 x hx0] at hx
            have hoccd2x : occD d2 x = true := occD_of_kind hx
            have hcell := goMoveN_standing A .w i1 d2 hw1 x hoccd2x
            have hxPB : kindAt (placedN n A .w i1) x = some .w := by
              unfold kindAt at hx ⊢
              rw [← hcell]
              exact hx
            by_cases hx1 : x = i1
            · subst x
              exact hkZ
            · rw [kindAt_placedN_ne A .w i1 x hx1] at hxPB
              rw [kindAt_joint_other A i0 i1 x hx0 hx1]
              exact hxPB
          have hl'i0 : l' ≠ i0 := by
            intro h
            subst l'
            rw [occD_of_kind (kindAt_placedN_self d2 .b i0
              (goMoveN_size A .w i1 d2 hw1) hi0)] at hl'E
            exact Bool.noConfusion hl'E
          have hl'd2 : occD d2 l' = false := by
            rw [← occD_placedN_ne d2 .b i0 l' hl'i0]
            exact hl'E
          cases hl'A : occD A l'
          · have hl'i1 : l' ≠ i1 := by
              intro h
              subst l'
              have : occD d2 i1 = true := occD_of_kind hd2i1
              rw [hl'd2] at this
              exact Bool.noConfusion this
            have hl'AP : occD (jointPlaced n A i0 i1) l' = false := by
              rw [occD_joint_other A i0 i1 l' hl'i0 hl'i1]
              exact hl'A
            have hlib : noLibD (jointPlaced n A i0 i1)
                (componentD (jointPlaced n A i0 i1) i1) = false :=
              (noLibD_eq_false_iff _ _).mpr
                ⟨l', hl'b, hl'AP, m', hm'Z, hadj'⟩
            rw [hZtrap] at hlib
            exact Bool.noConfusion hlib
          · have hl'i1 : l' ≠ i1 := by
              intro h
              subst l'
              rw [hi1A] at hl'A
              exact Bool.noConfusion hl'A
            have hl'PB : occD (placedN n A .w i1) l' = true := by
              rw [occD_placedN_ne A .w i1 l' hl'i1]
              exact hl'A
            rcases died_classify A .w i1 d2 hw1 l'
              (List.mem_range.mp hl'b) hl'PB hl'd2 with hdead | ⟨hs, _⟩
            · exact hnodead l' m' hdead hm'Z hadj'
            · rw [hsui] at hs
              exact Bool.noConfusion hs
        · rfl
      have hi1dead : i1 ∈ deadOppN n d2 .b i0 :=
        (mem_deadOppN_iff d2 .b i0 i1).mpr
          ⟨List.mem_range.mpr hi1, hPB2i1, hnl⟩
      have hc2 := occD_output_dead d2 .b i0 c2 hw2 i1 hi1 hi1dead
      rw [← occ_eq_of_samecells hcomm i1, hZlive] at hc2
      exact Bool.noConfusion hc2
    · have hiown : i1 ∈ ownCompN n A .w i1 :=
        componentD_mem_self _ i1 .w
          (kindAt_afterCapN_self A .w i1 hwfA hi1 (by decide))
      have hd2i1 : occD d2 i1 = false := by
        have hres := goMoveN_result A .w i1 d2 hw1
        rw [hres, if_pos hsui, occD_erasedN A .w i1 i1 hi1,
          if_pos (List.contains_iff_mem.mpr hiown)]
      have hc2i1 : occD c2 i1 = false :=
        persist_first_general A .w .b i1 i0 d2 c2
          (fun h => hne h.symm) hi0A hw1 hw2 i1
          (occD_of_kind (kindAt_placedN_self A .w i1 hwfA hi1)) hd2i1
      rw [← occ_eq_of_samecells hcomm i1, hZlive] at hc2i1
      exact Bool.noConfusion hc2i1

/-- basicCap only empties. -/
theorem basicCap_occ_le (X : Display n) (t : Nat)
    (hclassX : IsClassical X) (z : Nat)
    (h : occD (basicCap X t) z = true) : occD X z = true := by
  by_cases hz : z < n*n
  · rw [occD_basicCap X t hclassX z hz] at h
    cases hc : (capturedOf X t .b ++ capturedOf X t .w).contains z
    · rw [hc] at h
      simpa using h
    · rw [hc] at h
      simp at h
  · exfalso
    unfold occD at h
    rw [basicCap_get_oob X t z hz] at h
    exact Bool.noConfusion h

/-- A standing dead component with no trapped blocker is captured. -/
theorem dead_fresh_captured_when_unblocked (A D : Display n)
    (t i0 i1 : Nat) (d1 c1 : Display n)
    (hwfA : WFD A) (hwfD : WFD D)
    (hi0 : i0 < n*n) (hi1 : i1 < n*n) (hne : i0 ≠ i1)
    (hi0A : occD A i0 = false) (hi1A : occD A i1 = false)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hb1 : goMoveN n A .b i0 = some d1)
    (hb2 : goMoveN n d1 .w i1 = some c1)
    (E : Display n) (hE : CapIter A D t i0 i1 c1 E)
    (z0 : Nat) (hz0b : z0 < n*n) (kz : DKind)
    (hkzAP : kindAt (jointPlaced n A i0 i1) z0 = some kz)
    (hdead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD c1 q = false)
    (hz0E : occD E z0 = true)
    (hnob : ∀ z, occD E z = true →
      (componentD E z0).contains z = false →
      (componentD E z0).any (fun q => adjI n z q) = true →
      stoneTrappedBy E z kz t = false) :
    z0 ∈ capturedOf E t kz := by
  have hclassE : IsClassical E := CapIter_classical A D t i0 i1 c1 E
    hwfA hwfD hi0 hi1 hne hclass hcells hE
  have hkzE : kindAt E z0 = some kz := by
    unfold kindAt
    rw [CapIter_occ_cell A D t i0 i1 c1 E hE z0 hz0E]
    rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get z0)
      = kindAt (PJ D t i0 i1) z0 from rfl,
      PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z0]
    exact hkzAP
  have htrap : trappedOnTurn E (componentD E z0) t = true :=
    dead_trappedOnTurn A D t i0 i1 d1 c1 hwfA hwfD hi0 hi1 hne hi0A
      hi1A hclass hlegal hcells hst hb1 hb2 E hE z0 hz0b kz hkzAP
      hdead hz0E
  have h3a : (((allIdx n).filter fun z => occD E z &&
      !(componentD E z0).contains z &&
      (componentD E z0).any fun q => adjI n z q).all
    (fun z => !((kindAt E z == some kz.opp ||
      kindAt E z == some DKind.r) && stoneTrappedBy E z kz t)))
      = true := by
    rw [List.all_eq_true]
    intro z hzf
    have hzp := (List.mem_filter.mp hzf).2
    rw [Bool.and_eq_true, Bool.and_eq_true] at hzp
    obtain ⟨⟨hzE, hznc⟩, hzany⟩ := hzp
    rw [Bool.not_eq_true'] at hznc
    rw [hnob z hzE hznc hzany]
    simp
  have hcap : isCaptured E (componentD E z0) kz t = true := by
    simp only [isCaptured]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨htrap, cond2_true E hclassE (componentD E z0) kz⟩, ?_⟩
    rw [Bool.or_eq_true]
    exact Or.inl h3a
  exact (mem_capturedOf E t kz z0).mpr
    ⟨z0, List.mem_range.mpr hz0b, hkzE, hcap,
      componentD_mem_self E z0 kz hkzE⟩

/-- Once the dead old components are gone, a dead fresh component has
    no trapped blocker: the blocker would be the other placement's
    live component, freed by its captured shield breaker. -/
theorem no_blocker_when_olds_gone (A D : Display n) (t i0 i1 : Nat)
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
    (holdsgone : ∀ w', w' < n*n → DeadStone A i0 i1 c1 w' →
      (∀ q, q ∈ componentD (jointPlaced n A i0 i1) w' →
        occD A q = true) → occD E w' = false)
    (z0 : Nat) (hz0b : z0 < n*n) (kz : DKind)
    (hkzAP : kindAt (jointPlaced n A i0 i1) z0 = some kz)
    (hdead : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
      occD c1 q = false)
    (hz0E : occD E z0 = true)
    (z : Nat) (hzE : occD E z = true)
    (hznc : (componentD E z0).contains z = false)
    (hzany : (componentD E z0).any (fun q => adjI n z q) = true) :
    stoneTrappedBy E z kz t = false := by
  have hclassE : IsClassical E := CapIter_classical A D t i0 i1 c1 E
    hwfA hwfD hi0 hi1 hne hclass hcells hE
  cases hstb : stoneTrappedBy E z kz t
  · rfl
  · exfalso
    -- unpack the blocker condition
    have hkzE : kindAt E z0 = some kz := by
      unfold kindAt
      rw [CapIter_occ_cell A D t i0 i1 c1 E hE z0 hz0E]
      rw [show Option.map (fun x => x.1) ((PJ D t i0 i1).get z0)
        = kindAt (PJ D t i0 i1) z0 from rfl,
        PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z0]
      exact hkzAP
    have hzb : z < n*n := by
      by_cases h : z < n*n
      · exact h
      · exfalso
        unfold occD at hzE
        rw [get_oob E hE.1 z h] at hzE
        exact Bool.noConfusion hzE
    rcases hk : kindAt E z with _ | kzz
    · simp [stoneTrappedBy, hk] at hstb
    · have hkzz : kzz = kz.opp ∧
          trappedOnTurn E (componentD E z) t = true := by
        cases kzz with
        | r => exact absurd hk (hclassE z)
        | b =>
          cases hbeq : (DKind.b == kz.opp)
          · exfalso
            simp [stoneTrappedBy, hk, hbeq] at hstb
          · refine ⟨beq_iff_eq.mp hbeq, ?_⟩
            simp [stoneTrappedBy, hk, hbeq] at hstb
            exact hstb
        | w =>
          cases hbeq : (DKind.w == kz.opp)
          · exfalso
            simp [stoneTrappedBy, hk, hbeq] at hstb
          · refine ⟨beq_iff_eq.mp hbeq, ?_⟩
            simp [stoneTrappedBy, hk, hbeq] at hstb
            exact hstb
      obtain ⟨hkzzopp, htz⟩ := hkzz
      -- z is adjacent to the dead component
      rcases List.any_eq_true.mp hzany with ⟨m0, hm0, hadjz⟩
      have hz0stand : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z0 →
          occD E q = true :=
        dead_stands_entire A D t i0 i1 c1 E hE z0 hz0b kz hkzAP hz0E
      have hcompeq0 := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0
        hi1 hne hcells hE z0 kz hkzE hz0stand
      have hm0AP : m0 ∈ componentD (jointPlaced n A i0 i1) z0 :=
        (hcompeq0 m0).mp hm0
      have hm0dead : DeadStone A i0 i1 c1 m0 :=
        ⟨occD_of_kind (componentD_kind _ z0 kz hkzAP m0 hm0AP),
          hdead m0 hm0AP⟩
      have hzAP : occD (jointPlaced n A i0 i1) z = true := by
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z
        unfold occD at hpo ⊢
        rw [← CapIter_occ_cell A D t i0 i1 c1 E hE z hzE] at hpo
        rw [← hpo]
        exact hzE
      -- z is live
      have hzlive : occD c1 z = true := by
        cases hc : occD c1 z
        · exfalso
          have hzT : z ∈ componentD (jointPlaced n A i0 i1) m0 :=
            step5_adjacent_dead_same_comp A i0 i1 d1 c1 hwfA hi0 hi1
              hne hi1A hclass hb1 hb2 m0 z
              (List.mem_range.mp (componentD_board
                (List.mem_range.mpr hz0b) hkzAP hm0AP))
              hzb hm0dead.1 hzAP hm0dead.2 hc (adjI_symm hadjz)
          have hzin : z ∈ componentD (jointPlaced n A i0 i1) z0 :=
            (componentD_eq_mem (jointPlaced n A i0 i1) z0 m0 kz
              (List.mem_range.mpr hz0b) hkzAP hm0AP z).mp hzT
          have : z ∈ componentD E z0 := (hcompeq0 z).mpr hzin
          rw [List.contains_iff_mem.mpr this] at hznc
          exact Bool.noConfusion hznc
        · rfl
      -- z's A⁺ kind
      have hzkAP : kindAt (jointPlaced n A i0 i1) z = some kz.opp := by
        rw [← PJ_cells A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells z]
        unfold kindAt
        rw [← CapIter_occ_cell A D t i0 i1 c1 E hE z hzE]
        have hk2 := hk
        unfold kindAt at hk2
        rw [hk2, hkzzopp]
      -- z's component stands entire and is trapped in A⁺
      have hstandz : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z →
          c1.get q = (jointPlaced n A i0 i1).get q := by
        rcases step1_dichotomy A i0 i1 d1 c1 hwfA hi0 hi1 hne hi1A hb1
          hb2 z hzb hzAP with h | ⟨hallemp, _⟩
        · exact h
        · exfalso
          have := hallemp z (componentD_mem_self _ z kz.opp hzkAP)
          rw [hzlive] at this
          exact Bool.noConfusion this
      have hzstandE : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z →
          occD E q = true := by
        intro q hq
        have hqk := componentD_kind _ z kz.opp hzkAP q hq
        have hqb := componentD_board (List.mem_range.mpr hzb) hzkAP hq
        have hqlive : occD c1 q = true := by
          unfold occD
          rw [hstandz q hq]
          exact occD_of_kind hqk
        have hcell := CapIter_live_stands A D t i0 i1 c1 E hE q
          (List.mem_range.mp hqb) (occD_of_kind hqk) hqlive
        unfold occD
        rw [hcell]
        have hpo := PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells q
        unfold occD at hpo
        rw [hpo]
        exact occD_of_kind hqk
      have hkzE' : kindAt E z = some kz.opp := by
        rw [hk, hkzzopp]
      have hcompeqz := CapIter_comp_eq A D t i0 i1 c1 E hwfA hwfD hi0
        hi1 hne hcells hE z kz.opp hkzE' hzstandE
      have hnoLibz : noLibD E (componentD E z) = true := by
        have h := htz
        simp only [trappedOnTurn] at h
        rw [Bool.and_eq_true] at h
        exact h.1
      have hEoccle : ∀ w, occD E w = true →
          occD (PJ D t i0 i1) w = true := by
        intro w hw
        unfold occD
        rw [← CapIter_occ_cell A D t i0 i1 c1 E hE w hw]
        exact hw
      have htrapAP : noLibD (jointPlaced n A i0 i1)
          (componentD (jointPlaced n A i0 i1) z) = true := by
        have h1 : noLibD (PJ D t i0 i1) (componentD E z) = true :=
          noLibD_mono _ E _ hEoccle hnoLibz
        have h2 : noLibD (jointPlaced n A i0 i1)
            (componentD E z) = true := by
          rw [noLibD_occ_congr (jointPlaced n A i0 i1) (PJ D t i0 i1)
            (fun w => (PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne
              hcells w).symm) (componentD E z)]
          exact h1
        rw [← noLibD_congr _ _ _ hcompeqz]
        exact h2
      obtain ⟨hfresh, _⟩ := step4_live_trapped A i0 i1 d1 c1 d2 c2
        hwfA hi0 hi1 hne hi0A hi1A hclass hlegal hb1 hb2 hw1 hw2
        hcomm z hzb hzAP htrapAP hzlive
      -- the component is the other placement's; break its shield
      have hbreak : ∃ w' zw, w' < n*n ∧ DeadStone A i0 i1 c1 w' ∧
          (∀ q, q ∈ componentD (jointPlaced n A i0 i1) w' →
            occD A q = true) ∧
          zw ∈ componentD (jointPlaced n A i0 i1) z ∧
          adjI n w' zw = true := by
        rcases hfresh with hf | hf
        · -- contains i0: black component
          have hkb : kindAt (jointPlaced n A i0 i1) i0 = some kz.opp :=
            componentD_kind _ z kz.opp hzkAP i0 hf
          have hZeq := componentD_eq_mem (jointPlaced n A i0 i1) z i0
            kz.opp (List.mem_range.mpr hzb) hzkAP hf
          have hZlive : occD c1 i0 = true := by
            unfold occD
            rw [hstandz i0 hf]
            exact occD_of_kind hkb
          have hZtrap : noLibD (jointPlaced n A i0 i1)
              (componentD (jointPlaced n A i0 i1) i0) = true := by
            rw [noLibD_congr _ _ _ hZeq]
            exact htrapAP
          rcases shield_breaker_b A i0 i1 d1 c1 hwfA hi0 hi1 hne hi0A
            hi1A hclass hlegal hb1 hb2 hZlive hZtrap with
            ⟨w', hw'b, hw'd, hw'old, zw, hzwZ, hadjw⟩
          exact ⟨w', zw, hw'b, hw'd, hw'old, (hZeq zw).mp hzwZ, hadjw⟩
        · have hkw : kindAt (jointPlaced n A i0 i1) i1 = some kz.opp :=
            componentD_kind _ z kz.opp hzkAP i1 hf
          have hZeq := componentD_eq_mem (jointPlaced n A i0 i1) z i1
            kz.opp (List.mem_range.mpr hzb) hzkAP hf
          have hZlive : occD c1 i1 = true := by
            unfold occD
            rw [hstandz i1 hf]
            exact occD_of_kind hkw
          have hZtrap : noLibD (jointPlaced n A i0 i1)
              (componentD (jointPlaced n A i0 i1) i1) = true := by
            rw [noLibD_congr _ _ _ hZeq]
            exact htrapAP
          rcases shield_breaker_w A i0 i1 d2 c2 c1 hwfA hi0 hi1 hne
            hi0A hi1A hclass hlegal hw1 hw2 hcomm hZlive hZtrap with
            ⟨w', hw'b, hw'd, hw'old, zw, hzwZ, hadjw⟩
          exact ⟨w', zw, hw'b, hw'd, hw'old, (hZeq zw).mp hzwZ, hadjw⟩
      rcases hbreak with ⟨w', zw, hw'b, hw'd, hw'old, hzwz, hadjw⟩
      -- the breaker is gone in E: a liberty of the blocker's component
      have hw'E : occD E w' = false := holdsgone w' hw'b hw'd hw'old
      have hzwE : zw ∈ componentD E z := (hcompeqz zw).mpr hzwz
      have hlib : noLibD E (componentD E z) = false :=
        (noLibD_eq_false_iff _ _).mpr
          ⟨w', List.mem_range.mpr hw'b, hw'E, zw, hzwE, hadjw⟩
      rw [hnoLibz] at hlib
      exact Bool.noConfusion hlib

/-- Step 7: every dead stone is gone after two applications of the
    basic reduction from the placed display. -/
theorem step7_all_dead_removed (A D : Display n) (t i0 i1 : Nat)
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
    (z : Nat) (hzb : z < n*n) (hzd : DeadStone A i0 i1 c1 z) :
    occD (basicCap (basicCap (PJ D t i0 i1) t) t) z = false := by
  have hP : CapIter A D t i0 i1 c1 (PJ D t i0 i1) :=
    CapIter_P A D t i0 i1 c1 hwfA hwfD hi0 hi1 hne hcells
  have hD1 : CapIter A D t i0 i1 c1 (basicCap (PJ D t i0 i1) t) :=
    step6_preserved A D t i0 i1 d1 c1 d2 c2 hwfA hwfD hi0 hi1 hne
      hi0A hi1A hclass hlegal hcells hst hb1 hb2 hw1 hw2 hcomm _ hP
  have hclassP : IsClassical (PJ D t i0 i1) :=
    CapIter_classical A D t i0 i1 c1 _ hwfA hwfD hi0 hi1 hne hclass
      hcells hP
  have hclassD1 : IsClassical (basicCap (PJ D t i0 i1) t) :=
    CapIter_classical A D t i0 i1 c1 _ hwfA hwfD hi0 hi1 hne hclass
      hcells hD1
  -- dead components are entirely dead
  have hcompdead : ∀ w', w' < n*n → DeadStone A i0 i1 c1 w' →
      ∀ q, q ∈ componentD (jointPlaced n A i0 i1) w' →
        occD c1 q = false := by
    intro w' hw'b hd
    rcases step1_dichotomy A i0 i1 d1 c1 hwfA hi0 hi1 hne hi1A hb1
      hb2 w' hw'b hd.1 with h | ⟨he, _⟩
    · exfalso
      rcases kind_some_of_occ hd.1 with ⟨kw, hkw⟩
      have hcell := h w' (componentD_mem_self _ w' kw hkw)
      have : occD c1 w' = true := by
        unfold occD
        rw [hcell]
        exact hd.1
      rw [hd.2] at this
      exact Bool.noConfusion this
    · exact he
  -- kinds on the board are black or white
  have hbw : ∀ w' k, occD (jointPlaced n A i0 i1) w' = true →
      kindAt (jointPlaced n A i0 i1) w' = some k →
      k = .b ∨ k = .w := by
    intro w' k hocc hk
    rcases joint_kind_bw A i0 i1 hwfA hi0 hi1 hne hclass w' hocc
      with h | h
    · rw [hk] at h
      exact Or.inl (Option.some.inj h)
    · rw [hk] at h
      exact Or.inr (Option.some.inj h)
  -- a captured stone of either color is gone after one application
  have hgone : ∀ (X : Display n), IsClassical X →
      ∀ w' k, w' < n*n → (k = .b ∨ k = .w) →
      w' ∈ capturedOf X t k → occD (basicCap X t) w' = false := by
    intro X hclassX w' k hw'b hkbw hmem
    rw [occD_basicCap X t hclassX w' hw'b]
    have hcont : (capturedOf X t .b ++ capturedOf X t .w).contains w'
        = true := by
      apply List.contains_iff_mem.mpr
      rcases hkbw with rfl | rfl
      · exact List.mem_append.mpr (Or.inl hmem)
      · exact List.mem_append.mpr (Or.inr hmem)
    rw [if_pos hcont]
  -- dead old components are gone in D1
  have holdsgone : ∀ w', w' < n*n → DeadStone A i0 i1 c1 w' →
      (∀ q, q ∈ componentD (jointPlaced n A i0 i1) w' →
        occD A q = true) →
      occD (basicCap (PJ D t i0 i1) t) w' = false := by
    intro w' hw'b hd hold
    rcases kind_some_of_occ hd.1 with ⟨kw, hkw⟩
    have hw'P : occD (PJ D t i0 i1) w' = true := by
      rw [PJ_occ A D t i0 i1 hwfA hwfD hi0 hi1 hne hcells w']
      exact hd.1
    have hcap := dead_old_captured A D t i0 i1 d1 c1 d2 c2 hwfA hwfD
      hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst hb1 hb2 hw1 hw2
      hcomm _ hP w' hw'b kw hkw (hcompdead w' hw'b hd) hold hw'P
    exact hgone _ hclassP w' kw hw'b (hbw w' kw hd.1 hkw) hcap
  -- main split
  rcases kind_some_of_occ hzd.1 with ⟨kz, hkz⟩
  by_cases hfresh : z ∈ componentD (jointPlaced n A i0 i1) z ∧
      (i0 ∈ componentD (jointPlaced n A i0 i1) z ∨
        i1 ∈ componentD (jointPlaced n A i0 i1) z)
  · -- fresh: gone in one or two applications
    cases hzD1 : occD (basicCap (PJ D t i0 i1) t) z
    · -- already gone: monotone
      cases hz2 : occD (basicCap (basicCap (PJ D t i0 i1) t) t) z
      · rfl
      · exfalso
        have := basicCap_occ_le _ t hclassD1 z hz2
        rw [hzD1] at this
        exact Bool.noConfusion this
    · -- captured at the second application
      have hnob : ∀ zb, occD (basicCap (PJ D t i0 i1) t) zb = true →
          (componentD (basicCap (PJ D t i0 i1) t) z).contains zb
            = false →
          (componentD (basicCap (PJ D t i0 i1) t) z).any
            (fun q => adjI n zb q) = true →
          stoneTrappedBy (basicCap (PJ D t i0 i1) t) zb kz t
            = false := by
        intro zb hzbE hzbnc hzbany
        exact no_blocker_when_olds_gone A D t i0 i1 d1 c1 d2 c2 hwfA
          hwfD hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst hb1 hb2
          hw1 hw2 hcomm _ hD1 holdsgone z hzb kz hkz
          (hcompdead z hzb hzd) hzD1 zb hzbE hzbnc hzbany
      have hcap := dead_fresh_captured_when_unblocked A D t i0 i1 d1
        c1 hwfA hwfD hi0 hi1 hne hi0A hi1A hclass hlegal hcells hst
        hb1 hb2 _ hD1 z hzb kz hkz (hcompdead z hzb hzd) hzD1 hnob
      exact hgone _ hclassD1 z kz hzb (hbw z kz hzd.1 hkz) hcap
  · -- old: gone after the first application already
    have hold : ∀ q, q ∈ componentD (jointPlaced n A i0 i1) z →
        occD A q = true := by
      intro q hq
      have hq0 : q ≠ i0 := by
        intro h
        exact hfresh ⟨componentD_mem_self _ z kz hkz,
          Or.inl (h ▸ hq)⟩
      have hq1 : q ≠ i1 := by
        intro h
        exact hfresh ⟨componentD_mem_self _ z kz hkz,
          Or.inr (h ▸ hq)⟩
      rw [← occD_joint_other A i0 i1 q hq0 hq1]
      exact occD_of_kind (componentD_kind _ z kz hkz q hq)
    have hz1 := holdsgone z hzb hzd hold
    cases hz2 : occD (basicCap (basicCap (PJ D t i0 i1) t) t) z
    · rfl
    · exfalso
      have := basicCap_occ_le _ t hclassD1 z hz2
      rw [hz1] at this
      exact Bool.noConfusion this
