/- DispInfra.lean — display-side infrastructure: fold-max lemmas,
   membership congruence for the capture conditions, and the
   capturedOf characterization. -/
import Step4
open SgoDisplay

variable {n : Nat}

/-! ### Fold-max lemmas. -/

theorem foldl_max_acc_le (l : List Nat) (acc : Nat) :
    acc ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    exact Nat.le_trans (Nat.le_max_left acc a) (ih (Nat.max acc a))

theorem foldl_max_le (l : List Nat) (acc m : Nat)
    (hacc : acc ≤ m) (h : ∀ x, x ∈ l → x ≤ m) :
    l.foldl Nat.max acc ≤ m := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a t ih =>
    exact ih (Nat.max acc a)
      (Nat.max_le.mpr ⟨hacc, h a (List.mem_cons.mpr (Or.inl rfl))⟩)
      (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem le_foldl_max (l : List Nat) (acc x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => cases hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact Nat.le_trans (Nat.le_max_right acc x) (foldl_max_acc_le t _)
    · exact ih (Nat.max acc a) hxt

theorem nat_max_cases (a b : Nat) :
    Nat.max a b = a ∨ Nat.max a b = b := by
  show max a b = a ∨ max a b = b
  rw [Nat.max_def]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem foldl_max_mem (l : List Nat) (acc : Nat) :
    l.foldl Nat.max acc = acc ∨ l.foldl Nat.max acc ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons a t ih =>
    simp only [List.foldl]
    rcases ih (Nat.max acc a) with h | h
    · rw [h]
      rcases nat_max_cases acc a with h' | h'
      · exact Or.inl h'
      · rw [h']
        exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- Membership-equal lists have equal max-folds. -/
theorem foldl_max_congr (l l' : List Nat)
    (h : ∀ x, x ∈ l ↔ x ∈ l') :
    l.foldl Nat.max 0 = l'.foldl Nat.max 0 := by
  apply Nat.le_antisymm
  · apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    exact le_foldl_max l' 0 x ((h x).mp hx)
  · apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    exact le_foldl_max l 0 x ((h x).mpr hx)

/-! ### Membership congruence for the capture conditions. -/

theorem contains_congr_mem (l l' : List Nat) (x : Nat)
    (h : ∀ y, y ∈ l ↔ y ∈ l') : l.contains x = l'.contains x := by
  cases hc : l'.contains x
  · cases hc2 : l.contains x
    · rfl
    · have h2 : l'.contains x = true :=
        List.contains_iff_mem.mpr ((h x).mp (List.contains_iff_mem.mp hc2))
      rw [hc] at h2
      exact Bool.noConfusion h2
  · exact List.contains_iff_mem.mpr
      ((h x).mpr (List.contains_iff_mem.mp hc))

theorem all_congr_mem (l l' : List Nat) (p : Nat → Bool)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : l.all p = l'.all p := by
  cases hb : l.all p
  · cases ha : l'.all p
    · rfl
    · rcases List.all_eq_false.mp hb with ⟨x, hx, hpx⟩
      have : p x = true := List.all_eq_true.mp ha x ((h x).mp hx)
      exact absurd this hpx
  · symm
    rw [List.all_eq_true] at hb ⊢
    intro x hx
    exact hb x ((h x).mpr hx)

theorem trappedOnTurn_congr (D : Display n) (comp comp' : List Nat)
    (t : Nat) (h : ∀ x, x ∈ comp ↔ x ∈ comp') :
    trappedOnTurn D comp t = trappedOnTurn D comp' t := by
  have hcont : List.contains comp = List.contains comp' :=
    funext fun x => contains_congr_mem comp comp' x h
  have hany : List.any comp = List.any comp' :=
    funext fun p => any_congr_mem comp comp' p h
  unfold trappedOnTurn
  rw [noLibD_congr D comp comp' h, hcont, hany]
  congr 2
  show (List.foldl Nat.max 0 (List.map (stampAt D) comp ++
      List.map (stampAt D) (List.filter (fun z => occD D z &&
        !comp'.contains z && comp'.any fun q => adjI n z q)
        (allIdx n))) == t)
    = (List.foldl Nat.max 0 (List.map (stampAt D) comp' ++
      List.map (stampAt D) (List.filter (fun z => occD D z &&
        !comp'.contains z && comp'.any fun q => adjI n z q)
        (allIdx n))) == t)
  congr 1
  apply foldl_max_congr
  intro x
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨a, ha, rfl⟩ | hnbr)
    · exact Or.inl ⟨a, (h a).mp ha, rfl⟩
    · exact Or.inr hnbr
  · rintro (⟨a, ha, rfl⟩ | hnbr)
    · exact Or.inl ⟨a, (h a).mpr ha, rfl⟩
    · exact Or.inr hnbr

theorem isCaptured_congr (D : Display n) (comp comp' : List Nat)
    (c : DKind) (t : Nat) (h : ∀ x, x ∈ comp ↔ x ∈ comp') :
    isCaptured D comp c t = isCaptured D comp' c t := by
  have hcont : List.contains comp = List.contains comp' :=
    funext fun x => contains_congr_mem comp comp' x h
  have hany : List.any comp = List.any comp' :=
    funext fun p => any_congr_mem comp comp' p h
  have hall : List.all comp = List.all comp' :=
    funext fun p => all_congr_mem comp comp' p h
  unfold isCaptured isCapturedOT residualCap
  rw [trappedOnTurn_congr D comp comp' t h, noLibD_congr D comp comp' h,
    hcont, hany, hall]

/-! ### The two routes of def_captured: Conditions 1–3, and the residual
    route of Conditions 2 and 4 (cond_residual). On a component trapped on
    the turn, the residual route implies the first. -/

theorem noLibD_of_trappedOnTurn {D : Display n} {comp : List Nat} {t : Nat}
    (h : trappedOnTurn D comp t = true) : noLibD D comp = true := by
  simp only [trappedOnTurn, Bool.and_eq_true] at h
  exact h.1

theorem stoneTrapped_of_stoneTrappedBy {D : Display n} {z : Nat}
    {a : DKind} {t : Nat} (h : stoneTrappedBy D z a t = true) :
    stoneTrapped D z a = true := by
  unfold stoneTrappedBy at h
  unfold stoneTrapped
  cases hk : kindAt D z with
  | none => rw [hk] at h; exact h
  | some k =>
    rw [hk] at h
    cases k with
    | r => exact noLibD_of_trappedOnTurn h
    | b =>
      simp only at h ⊢
      by_cases hd : (DKind.b == a.opp) = true
      · rw [if_pos hd] at h ⊢
        exact noLibD_of_trappedOnTurn h
      · rw [if_neg hd] at h
        exact Bool.noConfusion h
    | w =>
      simp only at h ⊢
      by_cases hd : (DKind.w == a.opp) = true
      · rw [if_pos hd] at h ⊢
        exact noLibD_of_trappedOnTurn h
      · rw [if_neg hd] at h
        exact Bool.noConfusion h

theorem isCaptured_of_OT {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (h : isCapturedOT D comp c t = true) :
    isCaptured D comp c t = true := by
  unfold isCaptured
  rw [h, Bool.true_or]

theorem isCaptured_cases {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (h : isCaptured D comp c t = true) :
    isCapturedOT D comp c t = true ∨ residualCap D comp c = true := by
  unfold isCaptured at h
  exact Bool.or_eq_true _ _ ▸ h

theorem noLibD_of_residual {D : Display n} {comp : List Nat} {c : DKind}
    (h : residualCap D comp c = true) : noLibD D comp = true := by
  simp only [residualCap, Bool.and_eq_true] at h
  exact h.1.1

theorem noLibD_of_isCapturedOT {D : Display n} {comp : List Nat}
    {c : DKind} {t : Nat} (h : isCapturedOT D comp c t = true) :
    noLibD D comp = true := by
  simp only [isCapturedOT, Bool.and_eq_true] at h
  exact noLibD_of_trappedOnTurn h.1.1

theorem noLibD_of_isCaptured {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (h : isCaptured D comp c t = true) : noLibD D comp = true := by
  rcases isCaptured_cases h with h | h
  · exact noLibD_of_isCapturedOT h
  · exact noLibD_of_residual h

/-- The residual route implies the first on a component trapped on the
    turn: Condition 4 gives Condition 3a. -/
theorem OT_of_residual {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (hres : residualCap D comp c = true)
    (htr : trappedOnTurn D comp t = true) :
    isCapturedOT D comp c t = true := by
  simp only [residualCap, Bool.and_eq_true] at hres
  obtain ⟨⟨_, h2⟩, h4⟩ := hres
  simp only [isCapturedOT, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨htr, h2⟩, Or.inl ?_⟩
  rw [List.all_eq_true] at h4 ⊢
  intro z hz
  have hz4 := h4 z hz
  cases hst : stoneTrappedBy D z c t
  · simp
  · rw [stoneTrapped_of_stoneTrappedBy hst] at hz4
    exact hz4

/-- A captured component trapped on the turn satisfies Conditions 1–3. -/
theorem isCapturedOT_of_isCaptured {D : Display n} {comp : List Nat}
    {c : DKind} {t : Nat} (h : isCaptured D comp c t = true)
    (htr : trappedOnTurn D comp t = true) : isCapturedOT D comp c t = true := by
  rcases isCaptured_cases h with h | h
  · exact h
  · exact OT_of_residual h htr

/-- Condition 2 (cond_unambiguous0) holds on either route. -/
theorem cond2_of_isCaptured {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (h : isCaptured D comp c t = true) :
    (((allIdx n).filter fun z =>
        kindAt D z == some DKind.r && comp.any fun q => adjI n z q).all
      fun r' => (allIdx n).all fun z =>
        !(adjI n z r' && (kindAt D z == some DKind.b ||
          kindAt D z == some DKind.w) &&
          (let Dc := componentD D z
           !(Dc.all comp.contains && comp.all Dc.contains) &&
           noLibD D Dc && kindAt D z != some c))) = true := by
  rcases isCaptured_cases h with h | h
  · simp only [isCapturedOT, Bool.and_eq_true] at h
    exact h.1.2
  · simp only [residualCap, Bool.and_eq_true] at h
    exact h.1.2

/-- A trapped component holding a stone of the latest stamp t (no stamp
    exceeding t) is trapped on turn t. -/
theorem trappedOnTurn_of_member (D : Display n) (comp : List Nat) (t : Nat)
    (hnl : noLibD D comp = true)
    (hle : ∀ z, occD D z = true → stampAt D z ≤ t)
    (hocc : ∀ z, z ∈ comp → occD D z = true)
    (f : Nat) (hf : f ∈ comp) (hft : stampAt D f = t) :
    trappedOnTurn D comp t = true := by
  simp only [trappedOnTurn]
  rw [Bool.and_eq_true]
  refine ⟨hnl, ?_⟩
  rw [beq_iff_eq]
  apply Nat.le_antisymm
  · apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact hle a (hocc a ha)
    · rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
      have := (List.mem_filter.mp ha).2
      rw [Bool.and_eq_true, Bool.and_eq_true] at this
      exact hle a this.1.1
  · rw [← hft]
    exact le_foldl_max _ _ _
      (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩)))

theorem isCaptured_false_of_noLibD {D : Display n} {comp : List Nat}
    {c : DKind} {t : Nat} (h : noLibD D comp = false) :
    isCaptured D comp c t = false := by
  cases hc : isCaptured D comp c t
  · rfl
  · rw [noLibD_of_isCaptured hc] at h
    exact Bool.noConfusion h

/-! ### The capturedOf characterization. -/

def capStep (D : Display n) (t : Nat) (k : DKind)
    (acc : List Nat × List Nat) (p : Nat) : List Nat × List Nat :=
  let (seen, caps) := acc
  if kindAt D p == some k && !seen.contains p then
    let comp := componentD D p
    (seen ++ comp, if isCaptured D comp k t then caps ++ comp else caps)
  else acc

theorem capturedOf_eq_fold (D : Display n) (t : Nat) (k : DKind) :
    capturedOf D t k
      = ((allIdx n).foldl (capStep D t k) ([], [])).2 := rfl

theorem capStep_eq (D : Display n) (t : Nat) (k : DKind)
    (seen caps : List Nat) (p : Nat) :
    capStep D t k (seen, caps) p
      = if kindAt D p == some k && !seen.contains p then
          (seen ++ componentD D p,
            if isCaptured D (componentD D p) k t
            then caps ++ componentD D p else caps)
        else (seen, caps) := rfl

/-- The scan invariant: seen roots carry whole components, captured
    ones lie whole in caps; caps members come from captured
    components. -/
def CapInv (D : Display n) (t : Nat) (k : DKind)
    (seen caps : List Nat) : Prop :=
  (∀ s, s ∈ seen → s ∈ allIdx n ∧ kindAt D s = some k ∧
    (∀ y, y ∈ componentD D s → y ∈ seen) ∧
    (isCaptured D (componentD D s) k t = true →
      ∀ y, y ∈ componentD D s → y ∈ caps)) ∧
  (∀ x, x ∈ caps → ∃ p, p ∈ allIdx n ∧ kindAt D p = some k ∧
    isCaptured D (componentD D p) k t = true ∧ x ∈ componentD D p)

theorem capFold_inv (D : Display n) (t : Nat) (k : DKind) :
    ∀ (l : List Nat) (seen caps : List Nat),
      (∀ p, p ∈ l → p ∈ allIdx n) →
      CapInv D t k seen caps →
      CapInv D t k (l.foldl (capStep D t k) (seen, caps)).1
        (l.foldl (capStep D t k) (seen, caps)).2 ∧
      (∀ s, s ∈ seen → s ∈ (l.foldl (capStep D t k) (seen, caps)).1) ∧
      (∀ p, p ∈ l → kindAt D p = some k →
        p ∈ (l.foldl (capStep D t k) (seen, caps)).1)
  | [], seen, caps, _, hinv => by
    exact ⟨hinv, fun s hs => hs, fun p hp => absurd hp (List.not_mem_nil p)⟩
  | p :: l', seen, caps, hl, hinv => by
    have hpb : p ∈ allIdx n := hl p (List.mem_cons.mpr (Or.inl rfl))
    have hl' : ∀ q, q ∈ l' → q ∈ allIdx n :=
      fun q hq => hl q (List.mem_cons.mpr (Or.inr hq))
    simp only [List.foldl]
    rw [capStep_eq]
    by_cases hbeq : (kindAt D p == some k) = true
    · have hkp : kindAt D p = some k := beq_iff_eq.mp hbeq
      by_cases hns : seen.contains p = true
      · -- already seen: no change
        have hcond : (kindAt D p == some k && !seen.contains p) = false := by
          rw [hbeq, hns]
          rfl
        rw [hcond]
        simp only [Bool.false_eq_true, if_false]
        rcases capFold_inv D t k l' seen caps hl' hinv with ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        intro q hq hkq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact h2 q (List.contains_iff_mem.mp hns)
        · exact h3 q hq' hkq
      · -- fresh root: the whole component enters
        have hcond : (kindAt D p == some k && !seen.contains p) = true := by
          rw [hbeq]
          cases hc : seen.contains p
          · rfl
          · exact absurd hc hns
        rw [hcond]
        simp only [if_true]
        have hpns : p ∉ seen := fun hmem => hns (List.contains_iff_mem.mpr hmem)
        -- the new accumulator
        have hcompsub : ∀ s, s ∈ componentD D p →
            s ∈ allIdx n ∧ kindAt D s = some k ∧
            (∀ y, y ∈ componentD D s → y ∈ componentD D p) := by
          intro s hs
          refine ⟨componentD_board hpb hkp hs,
            componentD_kind D p k hkp s hs, ?_⟩
          intro y hy
          exact (componentD_eq_mem D p s k hpb hkp hs y).mp hy
        have hinv' : CapInv D t k (seen ++ componentD D p)
            (if isCaptured D (componentD D p) k t
              then caps ++ componentD D p else caps) := by
          constructor
          · intro s hs
            rcases List.mem_append.mp hs with hso | hsn
            · rcases hinv.1 s hso with ⟨hb, hk, hcl, hcap⟩
              refine ⟨hb, hk, fun y hy => List.mem_append.mpr
                (Or.inl (hcl y hy)), ?_⟩
              intro hcapd y hy
              split
              · exact List.mem_append.mpr (Or.inl (hcap hcapd y hy))
              · exact hcap hcapd y hy
            · rcases hcompsub s hsn with ⟨hb, hk, hsub⟩
              refine ⟨hb, hk, fun y hy => List.mem_append.mpr
                (Or.inr (hsub y hy)), ?_⟩
              intro hcapd y hy
              have hcapp : isCaptured D (componentD D p) k t = true := by
                rw [← isCaptured_congr D (componentD D s) (componentD D p)
                  k t (componentD_eq_mem D p s k hpb hkp hsn)]
                exact hcapd
              rw [if_pos hcapp]
              exact List.mem_append.mpr (Or.inr (hsub y hy))
          · intro x hx
            split at hx
            · next hcapp =>
              rcases List.mem_append.mp hx with hxo | hxn
              · exact hinv.2 x hxo
              · exact ⟨p, hpb, hkp, hcapp, hxn⟩
            · exact hinv.2 x hx
        rcases capFold_inv D t k l' (seen ++ componentD D p) _ hl' hinv'
          with ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩
        · intro s hs
          exact h2 s (List.mem_append.mpr (Or.inl hs))
        · intro q hq hkq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact h2 q (List.mem_append.mpr
              (Or.inr (componentD_mem_self D q k hkq)))
          · exact h3 q hq' hkq
    · -- wrong kind: no change
      have hcond : (kindAt D p == some k && !seen.contains p) = false := by
        cases hb : (kindAt D p == some k)
        · rfl
        · exact absurd hb hbeq
      rw [hcond]
      simp only [Bool.false_eq_true, if_false]
      rcases capFold_inv D t k l' seen caps hl' hinv with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      intro q hq hkq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd (beq_iff_eq.mpr hkq) hbeq
      · exact h3 q hq' hkq

/-- Membership in capturedOf: exactly the stones of captured
    components. -/
theorem mem_capturedOf (D : Display n) (t : Nat) (k : DKind) (x : Nat) :
    x ∈ capturedOf D t k ↔
    ∃ p, p ∈ allIdx n ∧ kindAt D p = some k ∧
      isCaptured D (componentD D p) k t = true ∧
      x ∈ componentD D p := by
  rw [capturedOf_eq_fold]
  have hinv0 : CapInv D t k [] [] :=
    ⟨fun s hs => absurd hs (List.not_mem_nil s),
     fun y hy => absurd hy (List.not_mem_nil y)⟩
  rcases capFold_inv D t k (allIdx n) [] [] (fun p hp => hp) hinv0
    with ⟨⟨hseen, hcaps⟩, _, hall⟩
  constructor
  · exact hcaps x
  · rintro ⟨p, hpb, hkp, hcap, hx⟩
    have hpseen := hall p hpb hkp
    rcases hseen p hpseen with ⟨_, _, _, hcapcl⟩
    exact hcapcl hcap x hx

/-! ### basicCap readers (classical displays: no q-stones). -/

theorem basicCap_size (D : Display n) (t : Nat) :
    (basicCap D t).cells.size = n*n := by
  simp only [basicCap]
  simp [Array.size_map, Array.size_range]

theorem basicCap_get (D : Display n) (t : Nat) (hnr : IsClassical D)
    (p : Nat) (hp : p < n*n) :
    (basicCap D t).get p =
      if (capturedOf D t .b ++ capturedOf D t .w).contains p then none
      else D.get p := by
  have hbr : (kindAt D p == some DKind.r) = false := by
    cases hb : (kindAt D p == some DKind.r)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) (hnr p)
  simp only [basicCap]
  rw [get_map_range, if_pos hp]
  cases hd : (capturedOf D t .b ++ capturedOf D t .w).contains p
  · simp only [Bool.false_eq_true, if_false]
    rw [hbr]
    simp
  · simp

theorem basicCap_get_oob (D : Display n) (t : Nat) (p : Nat)
    (hp : ¬ p < n*n) : (basicCap D t).get p = none := by
  simp only [basicCap]
  rw [get_map_range, if_neg hp]

theorem occD_basicCap (D : Display n) (t : Nat) (hnr : IsClassical D)
    (p : Nat) (hp : p < n*n) :
    occD (basicCap D t) p =
      if (capturedOf D t .b ++ capturedOf D t .w).contains p then false
      else occD D p := by
  unfold occD
  rw [basicCap_get D t hnr p hp]
  cases hd : (capturedOf D t .b ++ capturedOf D t .w).contains p <;> simp

/-! ### The placed display P. -/

theorem placeJoint_eq (D : Display n) (t : Nat) (i0 i1 : Nat)
    (hne : i0 ≠ i1) :
    placeJoint D t (some i0) (some i1)
      = (D.set i0 (some (.b, t))).set i1 (some (.w, t)) := by
  have hb : (i0 == i1) = false := by
    cases hc : (i0 == i1)
    · rfl
    · exact absurd (beq_iff_eq.mp hc) hne
  simp only [placeJoint]
  rw [hb]
  simp

theorem placeJoint_get_i1 (D : Display n) (t : Nat) (i0 i1 : Nat)
    (hne : i0 ≠ i1) (hwf : WFD D) (hi1 : i1 < n*n) :
    (placeJoint D t (some i0) (some i1)).get i1 = some (.w, t) := by
  rw [placeJoint_eq D t i0 i1 hne]
  exact get_set_self _ i1 _ (by rw [set_size, hwf]; exact hi1)

theorem placeJoint_get_i0 (D : Display n) (t : Nat) (i0 i1 : Nat)
    (hne : i0 ≠ i1) (hwf : WFD D) (hi0 : i0 < n*n) :
    (placeJoint D t (some i0) (some i1)).get i0 = some (.b, t) := by
  rw [placeJoint_eq D t i0 i1 hne, get_set_ne _ i1 i0 _ hne]
  exact get_set_self _ i0 _ (by rw [hwf]; exact hi0)

theorem placeJoint_get_other (D : Display n) (t : Nat) (i0 i1 z : Nat)
    (hne : i0 ≠ i1) (hz0 : z ≠ i0) (hz1 : z ≠ i1) :
    (placeJoint D t (some i0) (some i1)).get z = D.get z := by
  rw [placeJoint_eq D t i0 i1 hne, get_set_ne _ i1 z _ hz1,
    get_set_ne _ i0 z _ hz0]

theorem placeJoint_size (D : Display n) (t : Nat) (i0 i1 : Nat)
    (hne : i0 ≠ i1) (hwf : WFD D) :
    WFD (placeJoint D t (some i0) (some i1)) := by
  unfold WFD
  rw [placeJoint_eq D t i0 i1 hne, set_size, set_size]
  exact hwf
