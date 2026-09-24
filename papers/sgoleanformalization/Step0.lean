/- Step0.lean — the same-intersection companion: on a legal classical
   board (n ≥ 2) the two same-intersection composites cannot both be
   defined. Route: both first moves must suicide; a legal suicide
   captures nothing; a neighbor of the shared intersection then lies in
   the other color's dead list, which is empty — contradiction. -/
import Infra2
import Infra4
open SgoDisplay

variable {n : Nat}

/-! ### Kind arithmetic. -/

theorem opp_ne_self {c : DKind} (hc : c ≠ .r) : c.opp ≠ c := by
  cases c <;> first | decide | exact absurd rfl hc

theorem opp_opp {c : DKind} (hc : c ≠ .r) : c.opp.opp = c := by
  cases c <;> first | decide | exact absurd rfl hc

theorem opp_ne_r {c : DKind} (hc : c ≠ .r) : c.opp ≠ .r := by
  cases c <;> first | decide | exact absurd rfl hc

/-! ### Cell-reading helpers. -/

theorem occD_of_kind {D : Display n} {w : Nat} {k : DKind}
    (h : kindAt D w = some k) : occD D w = true := by
  unfold kindAt at h
  unfold occD
  cases hg : D.get w
  · rw [hg] at h; simp at h
  · rfl

theorem kind_none_of_unocc {D : Display n} {w : Nat}
    (h : occD D w = false) : kindAt D w = none := by
  unfold occD at h
  unfold kindAt
  cases hg : D.get w
  · rfl
  · rw [hg] at h; simp at h

theorem kind_some_of_occ {D : Display n} {w : Nat}
    (h : occD D w = true) : ∃ k, kindAt D w = some k := by
  unfold occD at h
  unfold kindAt
  cases hg : D.get w
  · rw [hg] at h; simp at h
  · next cell => exact ⟨cell.1, rfl⟩

theorem adjI_irrefl (i : Nat) : adjI n i i = false := by
  cases hadj : adjI n i i
  · rfl
  · exfalso
    simp only [adjI, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hadj
    omega

/-! ### Reading the placed diagram and the capture stage. -/

theorem kindAt_placedN_self (A : Display n) (c : DKind) (i : Nat)
    (hwf : WFD A) (hi : i < n*n) :
    kindAt (placedN n A c i) i = some c := by
  unfold kindAt placedN
  rw [get_set_self A i _ (by rw [hwf]; exact hi)]
  rfl

theorem kindAt_placedN_ne (A : Display n) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : kindAt (placedN n A c i) z = kindAt A z := by
  unfold kindAt placedN
  rw [get_set_ne A i z _ hz]

theorem occD_placedN_ne (A : Display n) (c : DKind) (i z : Nat)
    (hz : z ≠ i) : occD (placedN n A c i) z = occD A z := by
  unfold occD placedN
  rw [get_set_ne A i z _ hz]

theorem mem_deadOppN_iff (A : Display n) (c : DKind) (i w : Nat) :
    w ∈ deadOppN n A c i ↔
    w ∈ allIdx n ∧ kindAt (placedN n A c i) w = some c.opp ∧
      noLibD (placedN n A c i) (componentD (placedN n A c i) w) = true := by
  unfold deadOppN
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨h2, h3⟩

theorem i_not_mem_deadOppN (A : Display n) (c : DKind) (i : Nat)
    (hwf : WFD A) (hi : i < n*n) (hc : c ≠ .r) :
    i ∉ deadOppN n A c i := by
  intro hmem
  rcases (mem_deadOppN_iff A c i i).mp hmem with ⟨_, hk, _⟩
  rw [kindAt_placedN_self A c i hwf hi] at hk
  exact opp_ne_self hc (Option.some.inj hk).symm

theorem kindAt_afterCapN (A : Display n) (c : DKind) (i z : Nat)
    (hz : z < n*n) :
    kindAt (afterCapN n A c i) z =
      if (deadOppN n A c i).contains z then none
      else kindAt (placedN n A c i) z := by
  unfold kindAt
  rw [afterCapN_get, if_pos hz]
  cases hd : (deadOppN n A c i).contains z <;> simp

theorem occD_afterCapN (A : Display n) (c : DKind) (i z : Nat)
    (hz : z < n*n) :
    occD (afterCapN n A c i) z =
      if (deadOppN n A c i).contains z then false
      else occD (placedN n A c i) z := by
  unfold occD
  rw [afterCapN_get, if_pos hz]
  cases hd : (deadOppN n A c i).contains z <;> simp

theorem kindAt_afterCapN_self (A : Display n) (c : DKind) (i : Nat)
    (hwf : WFD A) (hi : i < n*n) (hc : c ≠ .r) :
    kindAt (afterCapN n A c i) i = some c := by
  have hni : ¬ (deadOppN n A c i).contains i = true := fun hcont =>
    i_not_mem_deadOppN A c i hwf hi hc (List.contains_iff_mem.mp hcont)
  rw [kindAt_afterCapN A c i i hi, if_neg hni,
    kindAt_placedN_self A c i hwf hi]

theorem componentD_board {D : Display n} {i : Nat} {k : DKind}
    (hi : i ∈ allIdx n) (hk : kindAt D i = some k) {q : Nat}
    (hq : q ∈ componentD D i) : q ∈ allIdx n :=
  ConnK_board hi ((componentD_mem_iff D i k hk q).mp hq)

/-- The shape of a defined move's output. -/
theorem goMoveN_result (d : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n d c i = some r) :
    r = if suicideN n d c i = true then erasedN n d c i
        else afterCapN n d c i := by
  unfold goMoveN at hr
  cases hocc : occD d i
  · rw [hocc] at hr
    simp at hr
    exact hr.symm
  · rw [hocc] at hr
    simp at hr

/-! ### A legal suicide captures nothing. -/

theorem suicide_no_captures (A : Display n) (c : DKind) (i : Nat)
    (hwf : WFD A) (hi : i < n*n) (hc : c ≠ .r)
    (hlegal : IsLegal A) (hemp : occD A i = false)
    (hsui : suicideN n A c i = true) :
    deadOppN n A c i = [] := by
  cases hd : deadOppN n A c i with
  | nil => rfl
  | cons w tl =>
    exfalso
    have hw : w ∈ deadOppN n A c i := by
      rw [hd]; exact List.mem_cons.mpr (Or.inl rfl)
    rcases (mem_deadOppN_iff A c i w).mp hw with ⟨hwb, hwk, hwnl⟩
    have hwi : w ≠ i := by
      intro h
      rw [h, kindAt_placedN_self A c i hwf hi] at hwk
      exact opp_ne_self hc (Option.some.inj hwk).symm
    have hwkA : kindAt A w = some c.opp := by
      rw [← kindAt_placedN_ne A c i w hwi]; exact hwk
    have hocc : occD A w = true := occD_of_kind hwkA
    rcases (noLibD_eq_false_iff A (componentD A w)).mp (hlegal w hocc)
      with ⟨q, hqb, hqe, r0, hr0, hadj⟩
    -- A and the placed diagram agree on opposite-colored cells
    have hagree : ∀ z, z ∈ allIdx n →
        (kindAt A z = some c.opp ↔
          kindAt (placedN n A c i) z = some c.opp) := by
      intro z _
      by_cases hzi : z = i
      · subst z
        rw [kind_none_of_unocc hemp, kindAt_placedN_self A c i hwf hi]
        constructor
        · intro h; exact Option.noConfusion h
        · intro h; exact absurd (Option.some.inj h).symm (opp_ne_self hc)
      · rw [kindAt_placedN_ne A c i z hzi]
    have htrans := componentD_transport A (placedN n A c i) c.opp hagree
      w hwkA hwk
    have hr0P : r0 ∈ componentD (placedN n A c i) w := (htrans r0).mp hr0
    -- the liberty must be the placement intersection
    have hqi : q = i := by
      by_cases hqi : q = i
      · exact hqi
      exfalso
      have hqeP : occD (placedN n A c i) q = false := by
        rw [occD_placedN_ne A c i q hqi]; exact hqe
      have hfalse : noLibD (placedN n A c i)
          (componentD (placedN n A c i) w) = false :=
        (noLibD_eq_false_iff _ _).mpr ⟨q, hqb, hqeP, r0, hr0P, hadj⟩
      rw [hwnl] at hfalse
      exact Bool.noConfusion hfalse
    subst q
    -- the component member r0 adjacent to the placement dies too
    have hr0b : r0 ∈ allIdx n := componentD_board hwb hwkA hr0
    have hr0kA : kindAt A r0 = some c.opp :=
      componentD_kind A w c.opp hwkA r0 hr0
    have hr0i : r0 ≠ i := by
      intro h
      rw [h, kind_none_of_unocc hemp] at hr0kA
      exact Option.noConfusion hr0kA
    have hr0P' : kindAt (placedN n A c i) r0 = some c.opp := by
      rw [kindAt_placedN_ne A c i r0 hr0i]; exact hr0kA
    have hr0dead : r0 ∈ deadOppN n A c i := by
      refine (mem_deadOppN_iff A c i r0).mpr ⟨hr0b, hr0P', ?_⟩
      have hmemeq := componentD_eq_mem (placedN n A c i) w r0 c.opp
        hwb hwk hr0P
      rw [noLibD_congr (placedN n A c i) _ _ hmemeq]
      exact hwnl
    -- its emptied cell is a liberty of the placed component: no suicide
    have hkCBi : kindAt (afterCapN n A c i) i = some c :=
      kindAt_afterCapN_self A c i hwf hi hc
    have himem : i ∈ componentD (afterCapN n A c i) i :=
      componentD_mem_self _ i c hkCBi
    have hr0CB : occD (afterCapN n A c i) r0 = false := by
      rw [occD_afterCapN A c i r0 (List.mem_range.mp hr0b),
        if_pos (List.contains_iff_mem.mpr hr0dead)]
    have hlib : noLibD (afterCapN n A c i)
        (componentD (afterCapN n A c i) i) = false :=
      (noLibD_eq_false_iff _ _).mpr
        ⟨r0, hr0b, hr0CB, i, himem, adjI_symm hadj⟩
    unfold suicideN ownCompN at hsui
    rw [hsui] at hlib
    exact Bool.noConfusion hlib

/-! ### The neighbor contradiction. -/

/-- With both dead lists empty and the c-side suiciding, a c-colored
    neighbor of the shared placement intersection would lie in the
    opposite color's dead list — impossible. -/
theorem same_isect_neighbor_contra (A : Display n) (i : Nat)
    (hwf : WFD A) (hi : i < n*n) (hemp : occD A i = false)
    (c : DKind) (hc : c ≠ .r)
    (hsc : suicideN n A c i = true)
    (hdc : deadOppN n A c i = [])
    (hdopp : deadOppN n A c.opp i = [])
    (j : Nat) (hj : j < n*n) (hadjji : adjI n j i = true)
    (hjk : kindAt A j = some c) : False := by
  have hji : j ≠ i := by
    intro h
    rw [h, kind_none_of_unocc hemp] at hjk
    exact Option.noConfusion hjk
  have hnilc : ∀ z : Nat, ¬ (([] : List Nat).contains z = true) :=
    fun z hcont => Bool.noConfusion hcont
  have hkCB : ∀ z, z < n*n →
      kindAt (afterCapN n A c i) z = kindAt (placedN n A c i) z := by
    intro z hz
    rw [kindAt_afterCapN A c i z hz, hdc, if_neg (hnilc z)]
  have hoCB : ∀ z, z < n*n →
      occD (afterCapN n A c i) z = occD (placedN n A c i) z := by
    intro z hz
    rw [occD_afterCapN A c i z hz, hdc, if_neg (hnilc z)]
  have hkCBi : kindAt (afterCapN n A c i) i = some c := by
    rw [hkCB i hi, kindAt_placedN_self A c i hwf hi]
  have hkCBj : kindAt (afterCapN n A c i) j = some c := by
    rw [hkCB j hj, kindAt_placedN_ne A c i j hji]
    exact hjk
  have hib : i ∈ allIdx n := List.mem_range.mpr hi
  have hjb : j ∈ allIdx n := List.mem_range.mpr hj
  have himem : i ∈ componentD (afterCapN n A c i) i :=
    componentD_mem_self _ i c hkCBi
  have hjOB : j ∈ componentD (afterCapN n A c i) i :=
    componentD_maximal (afterCapN n A c i) i c hkCBi j hjb hkCBj i
      himem hadjji
  have hsOB : noLibD (afterCapN n A c i)
      (componentD (afterCapN n A c i) i) = true := by
    unfold suicideN ownCompN at hsc
    exact hsc
  have hnlPW : noLibD (placedN n A c.opp i)
      (componentD (placedN n A c.opp i) j) = true := by
    cases hnl : noLibD (placedN n A c.opp i)
        (componentD (placedN n A c.opp i) j)
    · exfalso
      rcases (noLibD_eq_false_iff _ _).mp hnl with
        ⟨q, hqb, hqe, r0, hr0, hadj⟩
      have hkPWi : kindAt (placedN n A c.opp i) i = some c.opp :=
        kindAt_placedN_self A c.opp i hwf hi
      have hqi : q ≠ i := by
        intro h
        rw [h, occD_of_kind hkPWi] at hqe
        exact Bool.noConfusion hqe
      have hqeA : occD A q = false := by
        rw [← occD_placedN_ne A c.opp i q hqi]
        exact hqe
      have hkPWj : kindAt (placedN n A c.opp i) j = some c := by
        rw [kindAt_placedN_ne A c.opp i j hji]; exact hjk
      have hagreeWA : ∀ z, z ∈ allIdx n →
          kindAt (placedN n A c.opp i) z = some c → kindAt A z = some c := by
        intro z _ hz
        by_cases hzi : z = i
        · subst z
          rw [hkPWi] at hz
          exact absurd (Option.some.inj hz) (opp_ne_self hc)
        · rw [← kindAt_placedN_ne A c.opp i z hzi]; exact hz
      have hr0A : r0 ∈ componentD A j := by
        rw [componentD_mem_iff A j c hjk r0]
        exact ConnK_transport (placedN n A c.opp i) A c hagreeWA
          ((componentD_mem_iff (placedN n A c.opp i) j c hkPWj r0).mp hr0)
      have hagreeACB : ∀ z, z ∈ allIdx n →
          kindAt A z = some c → kindAt (afterCapN n A c i) z = some c := by
        intro z hzb hz
        have hzi : z ≠ i := by
          intro h
          rw [h, kind_none_of_unocc hemp] at hz
          exact Option.noConfusion hz
        rw [hkCB z (List.mem_range.mp hzb), kindAt_placedN_ne A c i z hzi]
        exact hz
      have hr0CB : r0 ∈ componentD (afterCapN n A c i) j := by
        rw [componentD_mem_iff (afterCapN n A c i) j c hkCBj r0]
        exact ConnK_transport A (afterCapN n A c i) c hagreeACB
          ((componentD_mem_iff A j c hjk r0).mp hr0A)
      have hr0OB : r0 ∈ componentD (afterCapN n A c i) i :=
        (componentD_eq_mem (afterCapN n A c i) i j c hib hkCBi hjOB r0).mp
          hr0CB
      have hqCB : occD (afterCapN n A c i) q = false := by
        rw [hoCB q (List.mem_range.mp hqb), occD_placedN_ne A c i q hqi]
        exact hqeA
      have hlib : noLibD (afterCapN n A c i)
          (componentD (afterCapN n A c i) i) = false :=
        (noLibD_eq_false_iff _ _).mpr ⟨q, hqb, hqCB, r0, hr0OB, hadj⟩
      rw [hsOB] at hlib
      exact Bool.noConfusion hlib
    · rfl
  have hkPWj' : kindAt (placedN n A c.opp i) j = some c.opp.opp := by
    rw [kindAt_placedN_ne A c.opp i j hji, opp_opp hc]
    exact hjk
  have hjdead : j ∈ deadOppN n A c.opp i :=
    (mem_deadOppN_iff A c.opp i j).mpr ⟨hjb, hkPWj', hnlPW⟩
  rw [hdopp] at hjdead
  exact List.not_mem_nil j hjdead

/-! ### Step 0: same-intersection distinctness. -/

theorem step0_same_intersection (hn : 2 ≤ n) (A : Display n) (i : Nat)
    (hwf : WFD A) (hi : i < n*n)
    (hclass : IsClassical A) (hlegal : IsLegal A)
    (c1 c2 : Display n)
    (h1 : (goMoveN n A .b i).bind (fun d => goMoveN n d .w i) = some c1)
    (h2 : (goMoveN n A .w i).bind (fun d => goMoveN n d .b i) = some c2) :
    False := by
  rcases bind_move_split A .b .w i i c1 h1 with ⟨d1, hb1, hb2⟩
  rcases bind_move_split A .w .b i i c2 h2 with ⟨d2, hw1, hw2⟩
  have hemp : occD A i = false := goMoveN_empty_at A .b i d1 hb1
  have hd1emp : occD d1 i = false := goMoveN_empty_at d1 .w i c1 hb2
  have hd2emp : occD d2 i = false := goMoveN_empty_at d2 .b i c2 hw2
  have hforce : ∀ (c : DKind), c ≠ .r → ∀ (d : Display n),
      goMoveN n A c i = some d → occD d i = false →
      suicideN n A c i = true := by
    intro c hc d hmove hdemp
    cases hs : suicideN n A c i
    · exfalso
      have hd : d = afterCapN n A c i := by
        have hres := goMoveN_result A c i d hmove
        rw [hs] at hres
        simpa using hres
      have hni : ¬ (deadOppN n A c i).contains i = true := fun hcont =>
        i_not_mem_deadOppN A c i hwf hi hc (List.contains_iff_mem.mp hcont)
      have hocc : occD d i = true := by
        rw [hd, occD_afterCapN A c i i hi, if_neg hni]
        exact occD_of_kind (kindAt_placedN_self A c i hwf hi)
      rw [hdemp] at hocc
      exact Bool.noConfusion hocc
    · rfl
  have hsb : suicideN n A .b i = true := hforce .b (by decide) d1 hb1 hd1emp
  have hsw : suicideN n A .w i = true := hforce .w (by decide) d2 hw1 hd2emp
  have hdb : deadOppN n A .b i = [] :=
    suicide_no_captures A .b i hwf hi (by decide) hlegal hemp hsb
  have hdw : deadOppN n A .w i = [] :=
    suicide_no_captures A .w i hwf hi (by decide) hlegal hemp hsw
  rcases exists_neighbor hn i hi with ⟨j, hj, hadjji⟩
  have hjocc : occD A j = true := by
    cases hjo : occD A j
    · exfalso
      have hji : j ≠ i := by
        intro h
        rw [h, adjI_irrefl] at hadjji
        exact Bool.noConfusion hadjji
      have hnilc : ¬ (([] : List Nat).contains j = true) :=
        fun hcont => Bool.noConfusion hcont
      have hoCBj : occD (afterCapN n A .b i) j = false := by
        rw [occD_afterCapN A .b i j hj, hdb, if_neg hnilc,
          occD_placedN_ne A .b i j hji]
        exact hjo
      have hkCBi : kindAt (afterCapN n A .b i) i = some .b :=
        kindAt_afterCapN_self A .b i hwf hi (by decide)
      have himem : i ∈ componentD (afterCapN n A .b i) i :=
        componentD_mem_self _ i .b hkCBi
      have hlib : noLibD (afterCapN n A .b i)
          (componentD (afterCapN n A .b i) i) = false :=
        (noLibD_eq_false_iff _ _).mpr
          ⟨j, List.mem_range.mpr hj, hoCBj, i, himem, hadjji⟩
      unfold suicideN ownCompN at hsb
      rw [hsb] at hlib
      exact Bool.noConfusion hlib
    · rfl
  rcases kind_some_of_occ hjocc with ⟨kj, hkj⟩
  cases kj with
  | b =>
    exact same_isect_neighbor_contra A i hwf hi hemp .b (by decide)
      hsb hdb hdw j hj hadjji hkj
  | w =>
    exact same_isect_neighbor_contra A i hwf hi hemp .w (by decide)
      hsw hdw hdb j hj hadjji hkj
  | r => exact hclass j hkj
