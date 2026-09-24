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
  unfold isCaptured
  rw [trappedOnTurn_congr D comp comp' t h, hcont, hany, hall]

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
