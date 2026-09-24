/- SgoStage1.lean — the main theorem, milestone 2d, display side: the
   pass-variant one-stage lemma. A turn with exactly one real move
   resolves to the classical move: stages (t+1) on the singly-placed
   display is SameCells the goMoveN output.

   Structure: readers for the stamped single placement (placedT);
   kind/occ/component transport to the classical placed diagram
   (placedN); the dead-adjacency fact (a libertyless component of the
   placed diagram lost its last liberty to the placement); the
   trapped-on-turn computations (the fresh stamp is the max; old
   components away from the placement are not trapped on t); the
   capture computation (capturedOf at t = the classical dead, with the
   suicide case via cond 3a and the capture case via cond 3b); the
   basicCap assembly; and the fixpoint/stages wrap through
   nocap_of_legal on the classical output. -/
import SgoInv

open SgoGo SgoDisplay SgoInv

variable {n : Nat}

/-! ### The stamped single placement -/

/-- One stone of color c stamped t. The two single-move joint
    placements are instances. -/
def placedT (D : Display n) (t : Nat) (c : DKind) (i : Nat) : Display n :=
  D.set i (some (c, t))

theorem placeJoint_left (D : Display n) (t i : Nat) :
    placeJoint D t (some i) none = placedT D t .b i := rfl

theorem placeJoint_right (D : Display n) (t i : Nat) :
    placeJoint D t none (some i) = placedT D t .w i := rfl

theorem pT_get_self (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) :
    (placedT D t c i).get i = some (c, t) :=
  get_set_self D i _ (by rw [hwfD]; exact hi)

theorem pT_get_ne (D : Display n) (t : Nat) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : (placedT D t c i).get z = D.get z :=
  get_set_ne D i z _ hz

theorem pT_kind_self (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) :
    kindAt (placedT D t c i) i = some c := by
  unfold kindAt
  rw [pT_get_self D t c i hwfD hi]
  rfl

theorem pT_kind_ne (D : Display n) (t : Nat) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : kindAt (placedT D t c i) z = kindAt D z := by
  unfold kindAt
  rw [pT_get_ne D t c i z hz]

theorem pT_occ_self (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) :
    occD (placedT D t c i) i = true := by
  unfold occD
  rw [pT_get_self D t c i hwfD hi]
  rfl

theorem pT_occ_ne (D : Display n) (t : Nat) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : occD (placedT D t c i) z = occD D z := by
  unfold occD
  rw [pT_get_ne D t c i z hz]

theorem pT_stamp_self (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) :
    stampAt (placedT D t c i) i = t := by
  unfold stampAt
  rw [pT_get_self D t c i hwfD hi]
  rfl

theorem pT_stamp_ne (D : Display n) (t : Nat) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : stampAt (placedT D t c i) z = stampAt D z := by
  unfold stampAt
  rw [pT_get_ne D t c i z hz]

theorem pT_wfd (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) : WFD (placedT D t c i) := by
  unfold WFD placedT
  rw [set_size]
  exact hwfD

/-- An occupied cell is on the board. -/
theorem kind_in_bounds {D : Display n} (hwf : WFD D) {p : Nat} {k : DKind}
    (hk : kindAt D p = some k) : p < n*n := by
  by_cases hp : p < n*n
  · exact hp
  · exfalso
    unfold kindAt at hk
    rw [get_oob D hwf p hp] at hk
    cases hk

/-! ### Transport to the classical placed diagram -/

theorem pT_samecells (t : Nat) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n)
    (hcells : SameCells D A) :
    SameCells (placedT D t c i) (placedN n A c i) := by
  intro z
  by_cases hz : z = i
  · subst hz
    rw [pT_kind_self D t c z hwfD hi, kindAt_placedN_self A c z hwfA hi]
  · rw [pT_kind_ne D t c i z hz, kindAt_placedN_ne A c i z hz]
    exact hcells z

theorem pT_classical (t : Nat) (A D : Display n) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n)
    (hcells : SameCells D A) (hclass : IsClassical A) (hc : c ≠ .r) :
    IsClassical (placedT D t c i) := by
  intro z
  by_cases hz : z = i
  · subst hz
    rw [pT_kind_self D t c z hwfD hi]
    intro h
    exact hc (Option.some.inj h)
  · rw [pT_kind_ne D t c i z hz, hcells z]
    exact hclass z

theorem pT_comp (t : Nat) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n)
    (hcells : SameCells D A)
    (p : Nat) (k : DKind)
    (hk : kindAt (placedT D t c i) p = some k) :
    ∀ q, q ∈ componentD (placedT D t c i) p
      ↔ q ∈ componentD (placedN n A c i) p := by
  have hkPL : kindAt (placedN n A c i) p = some k := by
    rw [← pT_samecells t A D c i hwfA hwfD hi hcells p]
    exact hk
  exact componentD_transport _ _ k
    (fun z _ => by rw [pT_samecells t A D c i hwfA hwfD hi hcells z])
    p hk hkPL

theorem pT_noLib (t : Nat) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n)
    (hcells : SameCells D A) (l : List Nat) :
    noLibD (placedT D t c i) l = noLibD (placedN n A c i) l :=
  noLibD_occ_congr _ _
    (fun z => occ_eq_of_samecells
      (pT_samecells t A D c i hwfA hwfD hi hcells) z) l

/-! ### Dead components touch the placement -/

/-- A libertyless opposite colored component of the placed diagram had
    its last liberty at the placement intersection: the placement is
    adjacent to it. -/
theorem dead_adjacent_opp (A : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hi : i < n*n) (hc : c ≠ .r)
    (hlegal : IsLegal A) (hemp : occD A i = false)
    (p : Nat) (hk : kindAt (placedN n A c i) p = some c.opp)
    (hdead : noLibD (placedN n A c i)
      (componentD (placedN n A c i) p) = true) :
    ∃ w, w ∈ componentD (placedN n A c i) p ∧ adjI n i w = true := by
  have hagree : ∀ z, z ∈ allIdx n →
      (kindAt (placedN n A c i) z = some c.opp
        ↔ kindAt A z = some c.opp) := by
    intro z _
    by_cases hz : z = i
    · subst hz
      rw [kindAt_placedN_self A c z hwfA hi]
      constructor
      · intro h
        exact absurd (Option.some.inj h).symm (opp_ne_self hc)
      · intro h
        exfalso
        have hocc := occD_of_kind h
        rw [hemp] at hocc
        exact Bool.noConfusion hocc
    · rw [kindAt_placedN_ne A c i z hz]
  have hpb : p < n*n := kind_in_bounds (WFD_placedN A c i hwfA) hk
  have hpA : kindAt A p = some c.opp :=
    (hagree p (List.mem_range.mpr hpb)).mp hk
  have hcompA : ∀ q, q ∈ componentD (placedN n A c i) p
      ↔ q ∈ componentD A p :=
    componentD_transport _ _ c.opp hagree p hk hpA
  have hlibA : noLibD A (componentD A p) = false :=
    hlegal p (occD_of_kind hpA)
  rcases (noLibD_eq_false_iff _ _).mp hlibA with ⟨q, hqb, hqemp, w, hw, hadj⟩
  have hwPL : w ∈ componentD (placedN n A c i) p := (hcompA w).mpr hw
  by_cases hqi : q = i
  · subst hqi
    exact ⟨w, hwPL, hadj⟩
  · exfalso
    have hqPL : occD (placedN n A c i) q = false := by
      rw [occD_placedN_ne A c i q hqi]
      exact hqemp
    have hlib : noLibD (placedN n A c i)
        (componentD (placedN n A c i) p) = false :=
      (noLibD_eq_false_iff _ _).mpr ⟨q, hqb, hqPL, w, hwPL, hadj⟩
    rw [hdead] at hlib
    exact Bool.noConfusion hlib

/-! ### Trapped on the placement turn -/

/-- The stamp clause, positive form: a libertyless component whose
    stones are old, with an adjacent occupied fresh cell, is trapped
    ON the placement turn. -/
theorem trapped_on_t (D : Display n) (t : Nat)
    (hle : ∀ z, stampAt D z ≤ t)
    (T : List Nat) (hnl : noLibD D T = true)
    (x : Nat) (hxb : x < n*n) (hxocc : occD D x = true)
    (hxst : stampAt D x = t) (hxT : ¬ x ∈ T)
    (hxadj : T.any (fun q => adjI n x q) = true) :
    trappedOnTurn D T t = true := by
  simp only [trappedOnTurn]
  rw [Bool.and_eq_true]
  refine ⟨hnl, ?_⟩
  have hcx : T.contains x = false := by
    cases hcx : T.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.mp hcx) hxT
  have hxfil : x ∈ (allIdx n).filter fun z =>
      occD D z && !T.contains z && T.any fun q => adjI n z q := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hxb, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hxocc, ?_⟩, hxadj⟩
    rw [hcx]
    rfl
  have hxmem : t ∈ (T.map (stampAt D)) ++
      (((allIdx n).filter fun z =>
        occD D z && !T.contains z && T.any fun q => adjI n z q).map
        (stampAt D)) := by
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_map.mpr
    exact ⟨x, hxfil, hxst⟩
  have hallle : ∀ y, y ∈ (T.map (stampAt D)) ++
      (((allIdx n).filter fun z =>
        occD D z && !T.contains z && T.any fun q => adjI n z q).map
        (stampAt D)) → y ≤ t := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_map.mp h with ⟨a, _, rfl⟩
      exact hle a
    · rcases List.mem_map.mp h with ⟨a, _, rfl⟩
      exact hle a
  have heq : ((T.map (stampAt D)) ++
      (((allIdx n).filter fun z =>
        occD D z && !T.contains z && T.any fun q => adjI n z q).map
        (stampAt D))).foldl Nat.max 0 = t :=
    Nat.le_antisymm
      (foldl_max_le _ 0 t (Nat.zero_le t) hallle)
      (le_foldl_max _ 0 t hxmem)
  exact beq_iff_eq.mpr heq

/-- The stamp clause, negative form: a component of old stones whose
    occupied neighbors are all old is not trapped on the placement
    turn. -/
theorem not_trapped_on_t (D : Display n) (t : Nat) (ht : 1 ≤ t)
    (T : List Nat)
    (hTst : ∀ q, q ∈ T → stampAt D q < t)
    (hnbr : ∀ z, z < n*n → occD D z = true → ¬ z ∈ T →
      T.any (fun q => adjI n z q) = true → stampAt D z < t) :
    trappedOnTurn D T t = false := by
  simp only [trappedOnTurn]
  cases hnl : noLibD D T
  · rfl
  · rw [Bool.true_and]
    have hallle : ∀ y, y ∈ (T.map (stampAt D)) ++
        (((allIdx n).filter fun z =>
          occD D z && !T.contains z && T.any fun q => adjI n z q).map
          (stampAt D)) → y ≤ t - 1 := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
        have := hTst a ha
        omega
      · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
        have hprops := (List.mem_filter.mp ha).2
        rw [Bool.and_eq_true, Bool.and_eq_true] at hprops
        obtain ⟨⟨hocc, hnc⟩, hany⟩ := hprops
        have hamem : ¬ a ∈ T := by
          intro hmem
          rw [List.contains_iff_mem.mpr hmem] at hnc
          exact Bool.noConfusion hnc
        have := hnbr a (List.mem_range.mp (List.mem_filter.mp ha).1)
          hocc hamem hany
        omega
    have hlt : ((T.map (stampAt D)) ++
        (((allIdx n).filter fun z =>
          occD D z && !T.contains z && T.any fun q => adjI n z q).map
          (stampAt D))).foldl Nat.max 0 < t := by
      have hle := foldl_max_le _ 0 (t-1) (Nat.zero_le _) hallle
      omega
    cases hbe : (((T.map (stampAt D)) ++
        (((allIdx n).filter fun z =>
          occD D z && !T.contains z && T.any fun q => adjI n z q).map
          (stampAt D))).foldl Nat.max 0 == t)
    · rfl
    · exfalso
      have := beq_iff_eq.mp hbe
      omega

/-! ### Stamp bounds and kind classification on the placed display -/

theorem pT_stamp_le (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) (hst : StampsBelow D t) :
    ∀ z, stampAt (placedT D t c i) z ≤ t := by
  intro z
  by_cases hz : z = i
  · subst hz
    rw [pT_stamp_self D t c z hwfD hi]
    exact Nat.le_refl t
  · rw [pT_stamp_ne D t c i z hz]
    exact Nat.le_of_lt (hst z)

theorem pT_stamp_old (D : Display n) (t : Nat) (c : DKind) (i : Nat)
    (hst : StampsBelow D t) :
    ∀ z, z ≠ i → stampAt (placedT D t c i) z < t := by
  intro z hz
  rw [pT_stamp_ne D t c i z hz]
  exact hst z

/-- A stone of the placed display: the fresh stone, or an old stone of
    the base diagram. -/
theorem pT_kind_cases (t : Nat) (A D : Display n) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) (hcells : SameCells D A)
    (z : Nat) (k : DKind) (hk : kindAt (placedT D t c i) z = some k) :
    (z = i ∧ k = c) ∨ (z ≠ i ∧ kindAt A z = some k) := by
  by_cases hz : z = i
  · subst hz
    rw [pT_kind_self D t c z hwfD hi] at hk
    exact Or.inl ⟨rfl, (Option.some.inj hk).symm⟩
  · rw [pT_kind_ne D t c i z hz, hcells z] at hk
    exact Or.inr ⟨hz, hk⟩

/-- On a classical board a stone is the mover's color or its opposite. -/
theorem kind_c_or_opp (c k : DKind) (hc : c ≠ .r) (hk : k ≠ .r) :
    k = c ∨ k = c.opp := by
  cases c with
  | b => cases k with
    | b => exact Or.inl rfl
    | w => exact Or.inr rfl
    | r => exact absurd rfl hk
  | w => cases k with
    | b => exact Or.inr rfl
    | w => exact Or.inl rfl
    | r => exact absurd rfl hk
  | r => exact absurd rfl hc

/-! ### stoneTrappedBy, evaluated on classical stones -/

/-- At a defender stone the test reads its component's trapping. -/
theorem stoneTrappedBy_defender (D : Display n) (z : Nat)
    (attacker : DKind) (t : Nat) (ha : attacker ≠ .r)
    (hk : kindAt D z = some attacker.opp) :
    stoneTrappedBy D z attacker t
      = trappedOnTurn D (componentD D z) t := by
  cases attacker with
  | b => simp [stoneTrappedBy, hk, DKind.opp]
  | w => simp [stoneTrappedBy, hk, DKind.opp]
  | r => exact absurd rfl ha

/-- At a stone of the attacker's own color the test is false. -/
theorem stoneTrappedBy_own (D : Display n) (z : Nat)
    (attacker : DKind) (t : Nat) (ha : attacker ≠ .r)
    (hk : kindAt D z = some attacker) :
    stoneTrappedBy D z attacker t = false := by
  cases attacker with
  | b => simp [stoneTrappedBy, hk, DKind.opp]
  | w => simp [stoneTrappedBy, hk, DKind.opp]
  | r => exact absurd rfl ha

/-- Bool bridge: an unequal kind pair under bne. -/
theorem kind_bne_r (c : DKind) (hc : c ≠ .r) :
    ((some c : Option DKind) != some DKind.r) = true := by
  cases c with
  | b => rfl
  | w => rfl
  | r => exact absurd rfl hc

/-- An own colored component avoiding the placement is not trapped on
    the placement turn (its cells and neighbors are all old: were the
    fresh stone adjacent, maximality would absorb it). -/
theorem own_color_comp_not_trapped
    (t : Nat) (ht : 1 ≤ t) (D : Display n) (c : DKind) (i : Nat)
    (hwfD : WFD D) (hi : i < n*n) (hst : StampsBelow D t)
    (z : Nat) (hkz : kindAt (placedT D t c i) z = some c)
    (hiz : ¬ i ∈ componentD (placedT D t c i) z) :
    trappedOnTurn (placedT D t c i)
      (componentD (placedT D t c i) z) t = false := by
  apply not_trapped_on_t _ t ht
  · intro q hq
    have hqi : q ≠ i := fun h => hiz (h ▸ hq)
    exact pT_stamp_old D t c i hst q hqi
  · intro z' hz'b hocc hz'nc hany
    by_cases hz'i : z' = i
    · exfalso
      subst hz'i
      rcases List.any_eq_true.mp hany with ⟨m, hm, hadjm⟩
      exact hiz (componentD_maximal _ z c hkz z'
        (List.mem_range.mpr hz'b)
        (pT_kind_self D t c z' hwfD hi) m hm hadjm)
    · exact pT_stamp_old D t c i hst z' hz'i

/-- Bool bridge: the right disjunct decides an or. -/
theorem bool_or_right {a b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]
  cases a <;> rfl

/-! ### The capture computation: the opposite color -/

/-- capturedOf at the placement turn, opposite color: exactly the
    classical dead. -/
theorem capturedOf_opp_iff
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hemp : occD A i = false) :
    ∀ x, x ∈ capturedOf (placedT D t c i) t c.opp
      ↔ x ∈ deadOppN n A c i := by
  intro x
  constructor
  · intro hx
    rcases (mem_capturedOf _ t c.opp x).mp hx with ⟨p, hpb, hkp, hcap, hxc⟩
    have htrap : trappedOnTurn (placedT D t c i)
        (componentD (placedT D t c i) p) t = true := by
      have h := hcap
      simp only [isCaptured] at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact h.1.1
    have hnlP : noLibD (placedT D t c i)
        (componentD (placedT D t c i) p) = true := by
      have h := htrap
      simp only [trappedOnTurn] at h
      rw [Bool.and_eq_true] at h
      exact h.1
    have hkpPL : kindAt (placedN n A c i) p = some c.opp := by
      rw [← pT_samecells t A D c i hwfA hwfD hi hcells p]
      exact hkp
    have hcompiff := pT_comp t A D c i hwfA hwfD hi hcells p c.opp hkp
    have hnlPL : noLibD (placedN n A c i)
        (componentD (placedN n A c i) p) = true := by
      rw [← noLibD_congr _ _ _ hcompiff,
        ← pT_noLib t A D c i hwfA hwfD hi hcells]
      exact hnlP
    have hxPL : x ∈ componentD (placedN n A c i) p := (hcompiff x).mp hxc
    have hxb : x ∈ allIdx n := componentD_board hpb hkpPL hxPL
    have hkxPL : kindAt (placedN n A c i) x = some c.opp :=
      componentD_kind _ p c.opp hkpPL x hxPL
    have hxcomp : ∀ q, q ∈ componentD (placedN n A c i) x
        ↔ q ∈ componentD (placedN n A c i) p :=
      componentD_eq_mem _ p x c.opp hpb hkpPL hxPL
    rw [mem_deadOppN_iff]
    refine ⟨hxb, hkxPL, ?_⟩
    rw [noLibD_congr _ _ _ hxcomp]
    exact hnlPL
  · intro hx
    rcases (mem_deadOppN_iff A c i x).mp hx with ⟨hxb, hkxPL, hnlPL⟩
    have hkxP : kindAt (placedT D t c i) x = some c.opp := by
      rw [pT_samecells t A D c i hwfA hwfD hi hcells x]
      exact hkxPL
    have hcompiff := pT_comp t A D c i hwfA hwfD hi hcells x c.opp hkxP
    have hnlP : noLibD (placedT D t c i)
        (componentD (placedT D t c i) x) = true := by
      rw [pT_noLib t A D c i hwfA hwfD hi hcells,
        noLibD_congr _ _ _ hcompiff]
      exact hnlPL
    rcases dead_adjacent_opp A c i hwfA hi hc hlegal hemp x hkxPL hnlPL
      with ⟨w, hwPL, hadj⟩
    have hwP : w ∈ componentD (placedT D t c i) x := (hcompiff w).mpr hwPL
    have hiT : ¬ i ∈ componentD (placedT D t c i) x := by
      intro hmem
      have hki := componentD_kind _ x c.opp hkxP i hmem
      rw [pT_kind_self D t c i hwfD hi] at hki
      exact opp_ne_self hc (Option.some.inj hki).symm
    have htrap : trappedOnTurn (placedT D t c i)
        (componentD (placedT D t c i) x) t = true := by
      apply trapped_on_t _ t (pT_stamp_le D t c i hwfD hi hst) _ hnlP i hi
        (pT_occ_self D t c i hwfD hi) (pT_stamp_self D t c i hwfD hi) hiT
      exact List.any_eq_true.mpr ⟨w, hwP, hadj⟩
    have hcap : isCaptured (placedT D t c i)
        (componentD (placedT D t c i) x) c.opp t = true := by
      simp only [isCaptured]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨htrap, cond2_true _
        (pT_classical t A D c i hwfD hi hcells hclass hc) _ c.opp⟩, ?_⟩
      apply bool_or_right
      rw [Bool.and_eq_true]
      constructor
      · rw [List.all_eq_true]
        intro q hq
        have hqi : q ≠ i := fun h => hiT (h ▸ hq)
        exact bne_of_ne (Nat.ne_of_lt (pT_stamp_old D t c i hst q hqi))
      · rw [List.all_eq_true]
        intro z hzf
        have hzprops := (List.mem_filter.mp hzf).2
        rw [Bool.and_eq_true, Bool.and_eq_true] at hzprops
        obtain ⟨⟨hzocc, hznc⟩, hzany⟩ := hzprops
        by_cases hiz : i ∈ componentD (placedT D t c i) z
        · have hany : (componentD (placedT D t c i) z).any
              (fun q => stampAt (placedT D t c i) q == t &&
                kindAt (placedT D t c i) q != some DKind.r) = true := by
            apply List.any_eq_true.mpr
            refine ⟨i, hiz, ?_⟩
            rw [Bool.and_eq_true]
            refine ⟨beq_iff_eq.mpr (pT_stamp_self D t c i hwfD hi), ?_⟩
            rw [pT_kind_self D t c i hwfD hi]
            exact kind_bne_r c hc
          rw [hany]
          simp
        · have hzb : z < n*n :=
            List.mem_range.mp (List.mem_filter.mp hzf).1
          rcases kind_some_of_occ hzocc with ⟨kz, hkz⟩
          have hkznr : kz ≠ .r := fun h =>
            (pT_classical t A D c i hwfD hi hcells hclass hc) z (h ▸ hkz)
          have hkzc : kz = c := by
            rcases kind_c_or_opp c kz hc hkznr with h | h
            · exact h
            · exfalso
              subst h
              rcases List.any_eq_true.mp hzany with ⟨m, hm, hadjm⟩
              have hzin : z ∈ componentD (placedT D t c i) x :=
                componentD_maximal _ x c.opp hkxP z
                  (List.mem_range.mpr hzb) hkz m hm hadjm
              rw [List.contains_iff_mem.mpr hzin] at hznc
              simp at hznc
          subst hkzc
          rw [own_color_comp_not_trapped t ht D kz i hwfD hi hst z hkz hiz]
          simp
    exact (mem_capturedOf _ t c.opp x).mpr
      ⟨x, hxb, hkxP, hcap, componentD_mem_self _ x c.opp hkxP⟩

/-- Bool bridge: eliminating an or. -/
theorem bool_or_elim {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a
  · rw [Bool.false_or] at h
    exact Or.inr h
  · exact Or.inl rfl

/-- The positive trapping via a fresh member. -/
theorem trapped_on_t_mem (D : Display n) (t : Nat)
    (hle : ∀ z, stampAt D z ≤ t)
    (T : List Nat) (hnl : noLibD D T = true)
    (x : Nat) (hx : x ∈ T) (hxst : stampAt D x = t) :
    trappedOnTurn D T t = true := by
  simp only [trappedOnTurn]
  rw [Bool.and_eq_true]
  refine ⟨hnl, ?_⟩
  have hxmem : t ∈ (T.map (stampAt D)) ++
      (((allIdx n).filter fun z =>
        occD D z && !T.contains z && T.any fun q => adjI n z q).map
        (stampAt D)) := by
    apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_map.mpr
    exact ⟨x, hx, hxst⟩
  have hallle : ∀ y, y ∈ (T.map (stampAt D)) ++
      (((allIdx n).filter fun z =>
        occD D z && !T.contains z && T.any fun q => adjI n z q).map
        (stampAt D)) → y ≤ t := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_map.mp h with ⟨a, _, rfl⟩
      exact hle a
    · rcases List.mem_map.mp h with ⟨a, _, rfl⟩
      exact hle a
  exact beq_iff_eq.mpr (Nat.le_antisymm
    (foldl_max_le _ 0 t (Nat.zero_le t) hallle)
    (le_foldl_max _ 0 t hxmem))

/-! ### The capture computation: the mover's color -/

/-- The classical capture step agrees with the placed diagram on the
    mover's color (only opposite stones are removed). -/
theorem afterCapN_agree_own (A : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hc : c ≠ .r) :
    ∀ z, z ∈ allIdx n →
      (kindAt (afterCapN n A c i) z = some c
        ↔ kindAt (placedN n A c i) z = some c) := by
  intro z hz
  have hzb : z < n*n := List.mem_range.mp hz
  unfold kindAt
  rw [afterCapN_get A c i z, if_pos hzb]
  by_cases hcont : (deadOppN n A c i).contains z = true
  · rw [if_pos hcont]
    have hmem := List.contains_iff_mem.mp hcont
    rcases (mem_deadOppN_iff A c i z).mp hmem with ⟨_, hkz, _⟩
    constructor
    · intro h
      cases h
    · intro h
      exfalso
      unfold kindAt at hkz
      rw [h] at hkz
      exact opp_ne_self hc (Option.some.inj hkz).symm
  · rw [if_neg hcont]

/-- The mover's capture at the placement turn, no suicide: nothing of
    the mover's color is captured. -/
theorem capturedOf_own_nosui
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hemp : occD A i = false)
    (hns : suicideN n A c i = false) :
    capturedOf (placedT D t c i) t c = [] := by
  cases hcl : capturedOf (placedT D t c i) t c with
  | nil => rfl
  | cons y tl =>
    exfalso
    have hy : y ∈ capturedOf (placedT D t c i) t c := by
      rw [hcl]
      exact List.mem_cons_self y tl
    rcases (mem_capturedOf _ t c y).mp hy with ⟨p, hpb, hkp, hcap, _⟩
    have htrap : trappedOnTurn (placedT D t c i)
        (componentD (placedT D t c i) p) t = true := by
      have h := hcap
      simp only [isCaptured] at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      exact h.1.1
    by_cases hip : i ∈ componentD (placedT D t c i) p
    · -- the placed component: it has a liberty after the captures
      have hnlP : noLibD (placedT D t c i)
          (componentD (placedT D t c i) p) = true := by
        have h := htrap
        simp only [trappedOnTurn] at h
        rw [Bool.and_eq_true] at h
        exact h.1
      have hiff : ∀ q, q ∈ componentD (placedT D t c i) i
          ↔ q ∈ componentD (placedT D t c i) p :=
        componentD_eq_mem _ p i c hpb hkp hip
      have hnsl : noLibD (afterCapN n A c i) (ownCompN n A c i) = false := by
        unfold suicideN at hns
        exact hns
      rcases (noLibD_eq_false_iff _ _).mp hnsl
        with ⟨l, hlb, hlemp, m, hm, hadjl⟩
      have hkiAC : kindAt (afterCapN n A c i) i = some c := by
        rw [(afterCapN_agree_own A c i hwfA hc i (List.mem_range.mpr hi))]
        exact kindAt_placedN_self A c i hwfA hi
      have hkiPL : kindAt (placedN n A c i) i = some c :=
        kindAt_placedN_self A c i hwfA hi
      have hkiP : kindAt (placedT D t c i) i = some c :=
        pT_kind_self D t c i hwfD hi
      have hmPL : m ∈ componentD (placedN n A c i) i :=
        (componentD_transport _ _ c (afterCapN_agree_own A c i hwfA hc)
          i hkiAC hkiPL m).mp hm
      have hmP : m ∈ componentD (placedT D t c i) i :=
        (pT_comp t A D c i hwfA hwfD hi hcells i c hkiP m).mpr hmPL
      have hmp : m ∈ componentD (placedT D t c i) p := (hiff m).mp hmP
      cases hlPL : occD (placedN n A c i) l with
      | false =>
        have hlP : occD (placedT D t c i) l = false := by
          rw [occ_eq_of_samecells
            (pT_samecells t A D c i hwfA hwfD hi hcells) l]
          exact hlPL
        have hlib : noLibD (placedT D t c i)
            (componentD (placedT D t c i) p) = false :=
          (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, hlP, m, hmp, hadjl⟩
        rw [hnlP] at hlib
        exact Bool.noConfusion hlib
      | true =>
        -- the liberty was a captured stone: its component blocks 3a
        have hlbn : l < n*n := List.mem_range.mp hlb
        have hldead : l ∈ deadOppN n A c i := by
          by_cases hcont : (deadOppN n A c i).contains l = true
          · exact List.contains_iff_mem.mp hcont
          · exfalso
            have hget : (afterCapN n A c i).get l
                = (placedN n A c i).get l := by
              rw [afterCapN_get A c i l, if_pos hlbn, if_neg hcont]
            have hocc : occD (afterCapN n A c i) l
                = occD (placedN n A c i) l := by
              unfold occD
              rw [hget]
            rw [hlemp, hlPL] at hocc
            exact Bool.noConfusion hocc
        rcases (mem_deadOppN_iff A c i l).mp hldead
          with ⟨_, hklPL, hnllPL⟩
        have hklP : kindAt (placedT D t c i) l = some c.opp := by
          rw [pT_samecells t A D c i hwfA hwfD hi hcells l]
          exact hklPL
        -- 3b's freshness fails at the fresh stone
        have hfr : ((componentD (placedT D t c i) p).all
            fun q => stampAt (placedT D t c i) q != t) = false := by
          apply List.all_eq_false.mpr
          refine ⟨i, hip, ?_⟩
          rw [pT_stamp_self D t c i hwfD hi]
          simp
        have h3or := by
          have h := hcap
          simp only [isCaptured] at h
          rw [Bool.and_eq_true, Bool.and_eq_true] at h
          exact h.2
        rcases bool_or_elim h3or with h3a | h3b
        · -- 3a refuted at the dead component adjacent through l
          have hlfil : l ∈ (allIdx n).filter fun z =>
              occD (placedT D t c i) z &&
              !(componentD (placedT D t c i) p).contains z &&
              (componentD (placedT D t c i) p).any
                fun q => adjI n z q := by
            apply List.mem_filter.mpr
            refine ⟨hlb, ?_⟩
            rw [Bool.and_eq_true, Bool.and_eq_true]
            refine ⟨⟨occD_of_kind hklP, ?_⟩, ?_⟩
            · have hnotmem : ¬ l ∈ componentD (placedT D t c i) p := by
                intro hmem
                have := componentD_kind _ p c hkp l hmem
                rw [hklP] at this
                exact opp_ne_self hc (Option.some.inj this)
              cases hcnt : (componentD (placedT D t c i) p).contains l
              · rfl
              · exact absurd (List.contains_iff_mem.mp hcnt) hnotmem
            · exact List.any_eq_true.mpr ⟨m, hmp, hadjl⟩
          have hbool := List.all_eq_true.mp h3a l hlfil
          rw [Bool.not_eq_true'] at hbool
          rw [show (kindAt (placedT D t c i) l == some c.opp) = true
              from beq_iff_eq.mpr hklP, Bool.true_or, Bool.true_and]
            at hbool
          rw [stoneTrappedBy_defender _ l c t hc hklP] at hbool
          -- but that component is trapped on t
          have hcompiff := pT_comp t A D c i hwfA hwfD hi hcells
            l c.opp hklP
          have hnllP : noLibD (placedT D t c i)
              (componentD (placedT D t c i) l) = true := by
            rw [pT_noLib t A D c i hwfA hwfD hi hcells,
              noLibD_congr _ _ _ hcompiff]
            exact hnllPL
          rcases dead_adjacent_opp A c i hwfA hi hc hlegal hemp
            l hklPL hnllPL with ⟨w, hwPL, hadjw⟩
          have hwP : w ∈ componentD (placedT D t c i) l :=
            (hcompiff w).mpr hwPL
          have hiT : ¬ i ∈ componentD (placedT D t c i) l := by
            intro hmem
            have := componentD_kind _ l c.opp hklP i hmem
            rw [pT_kind_self D t c i hwfD hi] at this
            exact opp_ne_self hc (Option.some.inj this).symm
          have htrapl : trappedOnTurn (placedT D t c i)
              (componentD (placedT D t c i) l) t = true := by
            apply trapped_on_t _ t (pT_stamp_le D t c i hwfD hi hst)
              _ hnllP i hi (pT_occ_self D t c i hwfD hi)
              (pT_stamp_self D t c i hwfD hi) hiT
            exact List.any_eq_true.mpr ⟨w, hwP, hadjw⟩
          rw [htrapl] at hbool
          exact Bool.noConfusion hbool
        · rw [Bool.and_eq_true] at h3b
          rw [h3b.1] at hfr
          exact Bool.noConfusion hfr
    · -- an old component of the mover's color: not trapped on t
      have hnt := own_color_comp_not_trapped t ht D c i hwfD hi hst
        p hkp hip
      rw [hnt] at htrap
      exact Bool.noConfusion htrap

/-- Bool bridge: the left disjunct decides an or. -/
theorem bool_or_left {a b : Bool} (h : a = true) : (a || b) = true := by
  rw [h]
  rfl

/-- With nothing captured, the capture step is the placed diagram. -/
theorem afterCapN_nocap_get (A : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hdead : deadOppN n A c i = []) :
    ∀ z, (afterCapN n A c i).get z = (placedN n A c i).get z := by
  intro z
  rw [afterCapN_get]
  by_cases hzb : z < n*n
  · rw [if_pos hzb, hdead]
    rfl
  · rw [if_neg hzb]
    exact (get_oob _ (WFD_placedN A c i hwfA) z hzb).symm

/-- The mover's capture at the placement turn, suicide: exactly the
    placed component. -/
theorem capturedOf_own_sui
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (hemp : occD A i = false)
    (hsui : suicideN n A c i = true) :
    ∀ x, x ∈ capturedOf (placedT D t c i) t c
      ↔ x ∈ componentD (placedT D t c i) i := by
  have hdead : deadOppN n A c i = [] :=
    suicide_no_captures A c i hwfA hi hc hlegal hemp hsui
  have hACget := afterCapN_nocap_get A c i hwfA hdead
  have hACocc : ∀ z, occD (afterCapN n A c i) z
      = occD (placedN n A c i) z := by
    intro z
    unfold occD
    rw [hACget z]
  have hACkind : ∀ z, kindAt (afterCapN n A c i) z
      = kindAt (placedN n A c i) z := by
    intro z
    unfold kindAt
    rw [hACget z]
  have hkiPL : kindAt (placedN n A c i) i = some c :=
    kindAt_placedN_self A c i hwfA hi
  have hkiAC : kindAt (afterCapN n A c i) i = some c := by
    rw [hACkind i]
    exact hkiPL
  have hkiP : kindAt (placedT D t c i) i = some c :=
    pT_kind_self D t c i hwfD hi
  have hACPL : ∀ q, q ∈ componentD (afterCapN n A c i) i
      ↔ q ∈ componentD (placedN n A c i) i :=
    componentD_transport _ _ c (fun z _ => by rw [hACkind z])
      i hkiAC hkiPL
  have hPPL := pT_comp t A D c i hwfA hwfD hi hcells i c hkiP
  have hnsl : noLibD (afterCapN n A c i)
      (componentD (afterCapN n A c i) i) = true := by
    unfold suicideN at hsui
    exact hsui
  have hnlPL : noLibD (placedN n A c i)
      (componentD (placedN n A c i) i) = true := by
    rw [← noLibD_occ_congr _ _ hACocc, ← noLibD_congr _ _ _ hACPL]
    exact hnsl
  have hnlP : noLibD (placedT D t c i)
      (componentD (placedT D t c i) i) = true := by
    rw [pT_noLib t A D c i hwfA hwfD hi hcells,
      noLibD_congr _ _ _ hPPL]
    exact hnlPL
  have hcap : isCaptured (placedT D t c i)
      (componentD (placedT D t c i) i) c t = true := by
    simp only [isCaptured]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, cond2_true _
      (pT_classical t A D c i hwfD hi hcells hclass hc) _ c⟩, ?_⟩
    · exact trapped_on_t_mem _ t (pT_stamp_le D t c i hwfD hi hst)
        _ hnlP i (componentD_mem_self _ i c hkiP)
        (pT_stamp_self D t c i hwfD hi)
    · apply bool_or_left
      rw [List.all_eq_true]
      intro z hzf
      have hzprops := (List.mem_filter.mp hzf).2
      rw [Bool.and_eq_true, Bool.and_eq_true] at hzprops
      obtain ⟨⟨hzocc, hznc⟩, hzany⟩ := hzprops
      have hzb : z < n*n := List.mem_range.mp (List.mem_filter.mp hzf).1
      rcases kind_some_of_occ hzocc with ⟨kz, hkz⟩
      have hkznr : kz ≠ .r := fun h =>
        (pT_classical t A D c i hwfD hi hcells hclass hc) z (h ▸ hkz)
      have hkzopp : kz = c.opp := by
        rcases kind_c_or_opp c kz hc hkznr with h | h
        · exfalso
          rw [h] at hkz
          rcases List.any_eq_true.mp hzany with ⟨m, hm, hadjm⟩
          have hzin : z ∈ componentD (placedT D t c i) i :=
            componentD_maximal _ i c hkiP z (List.mem_range.mpr hzb)
              hkz m hm hadjm
          rw [List.contains_iff_mem.mpr hzin] at hznc
          simp at hznc
        · exact h
      subst hkzopp
      have hkzPL : kindAt (placedN n A c i) z = some c.opp := by
        rw [← pT_samecells t A D c i hwfA hwfD hi hcells z]
        exact hkz
      have hnldead : noLibD (placedN n A c i)
          (componentD (placedN n A c i) z) = false := by
        cases hnl : noLibD (placedN n A c i)
            (componentD (placedN n A c i) z)
        · rfl
        · exfalso
          have hzdead : z ∈ deadOppN n A c i :=
            (mem_deadOppN_iff A c i z).mpr
              ⟨List.mem_range.mpr hzb, hkzPL, hnl⟩
          rw [hdead] at hzdead
          cases hzdead
      have hnlzP : noLibD (placedT D t c i)
          (componentD (placedT D t c i) z) = false := by
        rw [pT_noLib t A D c i hwfA hwfD hi hcells,
          noLibD_congr _ _ _
            (pT_comp t A D c i hwfA hwfD hi hcells z c.opp hkz)]
        exact hnldead
      have hnottr : trappedOnTurn (placedT D t c i)
          (componentD (placedT D t c i) z) t = false := by
        simp only [trappedOnTurn]
        rw [hnlzP]
        rfl
      rw [stoneTrappedBy_defender _ z c t hc hkz, hnottr]
      simp
  intro x
  constructor
  · intro hx
    rcases (mem_capturedOf _ t c x).mp hx with ⟨p, hpb, hkp, hcapp, hxc⟩
    by_cases hip : i ∈ componentD (placedT D t c i) p
    · exact (componentD_eq_mem _ p i c hpb hkp hip x).mpr hxc
    · exfalso
      have htrapp : trappedOnTurn (placedT D t c i)
          (componentD (placedT D t c i) p) t = true := by
        have h := hcapp
        simp only [isCaptured] at h
        rw [Bool.and_eq_true, Bool.and_eq_true] at h
        exact h.1.1
      rw [own_color_comp_not_trapped t ht D c i hwfD hi hst p hkp hip]
        at htrapp
      exact Bool.noConfusion htrapp
  · intro hx
    exact (mem_capturedOf _ t c x).mpr
      ⟨i, List.mem_range.mpr hi, hkiP, hcap, hx⟩

/-! ### The basic reduction is the classical move -/

/-- The two capture colors, read against the mover's orientation. -/
theorem capturedOf_bw_iff (P : Display n) (t : Nat) (c : DKind)
    (hc : c ≠ .r) (x : Nat) :
    x ∈ capturedOf P t .b ++ capturedOf P t .w
      ↔ (x ∈ capturedOf P t c ∨ x ∈ capturedOf P t c.opp) := by
  cases c with
  | b => exact List.mem_append
  | w =>
    rw [List.mem_append]
    exact Or.comm
  | r => exact absurd rfl hc

/-- One basic reduction of the placed display is the classical move's
    diagram. -/
theorem basicCap_samecells
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (r : Display n) (hmv : goMoveN n A c i = some r) :
    SameCells (basicCap (placedT D t c i) t) r := by
  have hemp : occD A i = false := goMoveN_empty_at A c i r hmv
  have hre : r = if suicideN n A c i then erasedN n A c i
      else afterCapN n A c i := by
    unfold goMoveN at hmv
    rw [hemp] at hmv
    simp only [Bool.false_eq_true, if_false] at hmv
    exact (Option.some.inj hmv).symm
  have hclP : IsClassical (placedT D t c i) :=
    pT_classical t A D c i hwfD hi hcells hclass hc
  -- the captured set, against the mover's orientation
  have hcontiff : ∀ x, ((capturedOf (placedT D t c i) t .b
      ++ capturedOf (placedT D t c i) t .w).contains x = true)
      ↔ (x ∈ capturedOf (placedT D t c i) t c
        ∨ x ∈ deadOppN n A c i) := by
    intro x
    rw [List.contains_iff_mem, capturedOf_bw_iff (placedT D t c i) t c hc x,
      capturedOf_opp_iff t ht A D c i hwfA hwfD hi hc hclass
        hlegal hcells hst hemp x]
  intro x
  by_cases hxb : x < n*n
  · have hget := basicCap_get (placedT D t c i) t hclP x hxb
    cases hsui : suicideN n A c i with
    | false =>
      have hrac : r = afterCapN n A c i := by
        rw [hre, hsui]
        simp
      have hxiff : ((capturedOf (placedT D t c i) t .b
          ++ capturedOf (placedT D t c i) t .w).contains x = true)
          ↔ x ∈ deadOppN n A c i := by
        rw [hcontiff x,
          capturedOf_own_nosui t ht A D c i hwfA hwfD hi hc hclass
            hlegal hcells hst hemp hsui]
        constructor
        · rintro (h | h)
          · cases h
          · exact h
        · exact Or.inr
      by_cases hd : x ∈ deadOppN n A c i
      · unfold kindAt
        rw [hget, if_pos (hxiff.mpr hd), hrac, afterCapN_get,
          if_pos hxb, if_pos (List.contains_iff_mem.mpr hd)]
      · have hcont : (capturedOf (placedT D t c i) t .b
            ++ capturedOf (placedT D t c i) t .w).contains x = false := by
          cases hcnt : (capturedOf (placedT D t c i) t .b
              ++ capturedOf (placedT D t c i) t .w).contains x
          · rfl
          · exact absurd (hxiff.mp hcnt) hd
        have hdcont : (deadOppN n A c i).contains x = false := by
          cases hcnt : (deadOppN n A c i).contains x
          · rfl
          · exact absurd (List.contains_iff_mem.mp hcnt) hd
        unfold kindAt
        rw [hget, if_neg (by rw [hcont]; exact Bool.noConfusion),
          hrac, afterCapN_get, if_pos hxb,
          if_neg (by rw [hdcont]; exact Bool.noConfusion)]
        exact pT_samecells t A D c i hwfA hwfD hi hcells x
    | true =>
      have hrer : r = erasedN n A c i := by
        rw [hre, hsui]
        simp
      have hdead : deadOppN n A c i = [] :=
        suicide_no_captures A c i hwfA hi hc hlegal hemp hsui
      have hACget := afterCapN_nocap_get A c i hwfA hdead
      -- own component, transported P → placedN → afterCapN
      have hkiP : kindAt (placedT D t c i) i = some c :=
        pT_kind_self D t c i hwfD hi
      have hkiPL : kindAt (placedN n A c i) i = some c :=
        kindAt_placedN_self A c i hwfA hi
      have hACkind : ∀ z, kindAt (afterCapN n A c i) z
          = kindAt (placedN n A c i) z := by
        intro z
        unfold kindAt
        rw [hACget z]
      have hkiAC : kindAt (afterCapN n A c i) i = some c := by
        rw [hACkind i]
        exact hkiPL
      have hACPL : ∀ q, q ∈ componentD (afterCapN n A c i) i
          ↔ q ∈ componentD (placedN n A c i) i :=
        componentD_transport _ _ c (fun z _ => by rw [hACkind z])
          i hkiAC hkiPL
      have hPPL := pT_comp t A D c i hwfA hwfD hi hcells i c hkiP
      have hxiff : ((capturedOf (placedT D t c i) t .b
          ++ capturedOf (placedT D t c i) t .w).contains x = true)
          ↔ x ∈ componentD (placedT D t c i) i := by
        rw [hcontiff x, hdead,
          capturedOf_own_sui t ht A D c i hwfA hwfD hi hc hclass
            hlegal hcells hst hemp hsui x]
        constructor
        · rintro (h | h)
          · exact h
          · cases h
        · exact Or.inl
      by_cases hd : x ∈ componentD (placedT D t c i) i
      · have hown : (ownCompN n A c i).contains x = true := by
          apply List.contains_iff_mem.mpr
          exact (hACPL x).mpr ((hPPL x).mp hd)
        unfold kindAt
        rw [hget, if_pos (hxiff.mpr hd), hrer, erasedN_get,
          if_pos hxb, if_pos hown]
      · have hcont : (capturedOf (placedT D t c i) t .b
            ++ capturedOf (placedT D t c i) t .w).contains x = false := by
          cases hcnt : (capturedOf (placedT D t c i) t .b
              ++ capturedOf (placedT D t c i) t .w).contains x
          · rfl
          · exact absurd (hxiff.mp hcnt) hd
        have hown : (ownCompN n A c i).contains x = false := by
          cases hcnt : (ownCompN n A c i).contains x
          · rfl
          · exact absurd ((hPPL x).mpr ((hACPL x).mp
              (List.contains_iff_mem.mp hcnt))) hd
        unfold kindAt
        rw [hget, if_neg (by rw [hcont]; exact Bool.noConfusion),
          hrer, erasedN_get, if_pos hxb,
          if_neg (by rw [hown]; exact Bool.noConfusion), hACget x]
        exact pT_samecells t A D c i hwfA hwfD hi hcells x
  · -- off the board: both none
    have h1 : (basicCap (placedT D t c i) t).get x = none :=
      basicCap_get_oob _ t x hxb
    have h2 : r.get x = none :=
      get_oob r (goMoveN_size A c i r hmv) x hxb
    unfold kindAt
    rw [h1, h2]

/-! ### The one-stage resolution of a single move -/

/-- The pass-variant one-stage lemma: a single placement resolves to
    the classical move — the stage recursion on the placed display is
    SameCells the goMoveN output. -/
theorem onestage_single
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (c : DKind) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (r : Display n) (hmv : goMoveN n A c i = some r) :
    SameCells (stages (t+1) (placedT D t c i) t) r := by
  have hbc : SameCells (basicCap (placedT D t c i) t) r :=
    basicCap_samecells t ht A D c i hwfA hwfD hi hc hclass hlegal
      hcells hst r hmv
  have hrcl : IsClassical r := goMoveN_classical A c i r hclass hc hmv
  have hrleg : IsLegal r :=
    goMoveN_legal A c i r hwfA hi hc hclass hlegal hmv
  -- the capture fixpoint of the placed display
  have hX : SameCells (capFix (n*n+1) (placedT D t c i) t) r := by
    simp only [capFix]
    by_cases htest : (basicCap (placedT D t c i) t
        == placedT D t c i) = true
    · rw [if_pos htest]
      rw [← display_eq_of_beq htest]
      exact hbc
    · rw [if_neg htest]
      have hclbc : IsClassical (basicCap (placedT D t c i) t) := by
        intro z hz
        rw [hbc z] at hz
        exact hrcl z hz
      have hwfbc : WFD (basicCap (placedT D t c i) t) :=
        basicCap_size _ t
      rw [capFix_id _ t (basicCap_id _ hclbc hwfbc
        (fun k t' => nocap_of_legal _ r hbc hrleg k t') t) (n*n)]
      exact hbc
  -- the stage recursion stops after the placement turn
  simp only [stages]
  have htz : (t == 0) = false := by
    cases t with
    | zero => exact absurd ht (by omega)
    | succ t' => rfl
  rw [htz]
  simp only [Bool.false_eq_true, if_false]
  by_cases htest : (capFix (n*n+1) (placedT D t c i) t
      == placedT D t c i) = true
  · rw [if_pos htest]
    rw [← display_eq_of_beq htest]
    exact hX
  · rw [if_neg htest]
    have hXcl : IsClassical (capFix (n*n+1) (placedT D t c i) t) := by
      intro z hz
      rw [hX z] at hz
      exact hrcl z hz
    have hXwf : WFD (capFix (n*n+1) (placedT D t c i) t) :=
      capFix_wfd _ _ t (pT_wfd D t c i hwfD)
    rw [stages_id _ (fun t' => basicCap_id _ hXcl hXwf
      (fun k t'' => nocap_of_legal _ r hX hrleg k t'') t') t (t-1)]
    exact hX

/-- The left instance: Black moves, White passes. -/
theorem onestage_left
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (r : Display n) (hmv : goMoveN n A .b i = some r) :
    SameCells (resolveTurn D t (some i) none) r := by
  unfold resolveTurn
  rw [placeJoint_left]
  exact onestage_single t ht A D .b i hwfA hwfD hi
    (by intro h; cases h) hclass hlegal hcells hst r hmv

/-- The right instance: White moves, Black passes. -/
theorem onestage_right
    (t : Nat) (ht : 1 ≤ t) (A D : Display n) (i : Nat)
    (hwfA : WFD A) (hwfD : WFD D) (hi : i < n*n)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (hcells : SameCells D A) (hst : StampsBelow D t)
    (r : Display n) (hmv : goMoveN n A .w i = some r) :
    SameCells (resolveTurn D t none (some i)) r := by
  unfold resolveTurn
  rw [placeJoint_right]
  exact onestage_single t ht A D .w i hwfA hwfD hi
    (by intro h; cases h) hclass hlegal hcells hst r hmv
