/- Infra6.lean — output invariants of one classical move: the output is
   classical, and legal (every component of the output has a liberty).
   Feeds Step 4 (which reads legality of a'). -/
import Step1
open SgoDisplay

variable {n : Nat}

/-- Relativized component transport: if every member of x's D-component
    keeps kind k in E, the component embeds in x's E-component. -/
theorem componentD_transport_rel (D E : Display n) (k : DKind) (x : Nat)
    (hkD : kindAt D x = some k)
    (hsur : ∀ m, m ∈ componentD D x → kindAt E m = some k) :
    ∀ m, m ∈ componentD D x → m ∈ componentD E x := by
  intro m hm
  have hkE : kindAt E x = some k := hsur x (componentD_mem_self D x k hkD)
  rw [componentD_mem_iff E x k hkE]
  have hconn := (componentD_mem_iff D x k hkD m).mp hm
  clear hm
  induction hconn with
  | refl => exact ConnK.refl
  | step hc hqi hqk hadj ih =>
    next j q' =>
    have hq'D := (componentD_mem_iff D x k hkD q').mpr
      (ConnK.step hc hqi hqk hadj)
    exact ConnK.step ih hqi (hsur q' hq'D) hadj

/-- Output stones are placed-diagram stones. -/
theorem goMoveN_occ_le (base : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n base c i = some r) (z : Nat)
    (hz : occD r z = true) : occD (placedN n base c i) z = true := by
  unfold occD at hz ⊢
  rw [goMoveN_standing base c i r hr z hz] at hz
  exact hz

/-- A surviving cell keeps its placed-diagram kind. -/
theorem kindAt_standing (base : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n base c i = some r) (z : Nat)
    (hz : occD r z = true) :
    kindAt r z = kindAt (placedN n base c i) z := by
  unfold kindAt
  rw [goMoveN_standing base c i r hr z hz]

/-- The output of a non-r move on a classical display is classical. -/
theorem goMoveN_classical (base : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hclass : IsClassical base) (hc : c ≠ .r)
    (hr : goMoveN n base c i = some r) : IsClassical r := by
  intro x hx
  -- x carries kind r in the output: it is occupied, so reads placedN
  have hocc : occD r x = true := occD_of_kind hx
  rw [kindAt_standing base c i r hr x hocc] at hx
  by_cases hxi : x = i
  · subst x
    by_cases hlt : i < base.cells.size
    · -- placed cell reads back: kind c ≠ r
      unfold kindAt placedN at hx
      rw [get_set_self base i _ hlt] at hx
      simp at hx
      exact hc hx
    · -- out of bounds: the set no-ops and the cell reads base
      have hnoop : (placedN n base c i).get i = base.get i := by
        unfold placedN Display.set Display.get Array.setD Array.setIfInBounds
        rw [dif_neg hlt]
      unfold kindAt at hx
      rw [hnoop] at hx
      exact hclass i hx
  · rw [kindAt_placedN_ne base c i x hxi] at hx
    exact hclass x hx

/-- One classical move preserves legality: every component of the
    output has a liberty. -/
theorem goMoveN_legal (base : Display n) (c : DKind) (i : Nat)
    (r : Display n)
    (hwf : WFD base) (hi : i < n*n) (hc : c ≠ .r)
    (hclass : IsClassical base) (hlegal : IsLegal base)
    (hr : goMoveN n base c i = some r) : IsLegal r := by
  intro x hx
  have hemp : occD base i = false := goMoveN_empty_at base c i r hr
  have hoccP : occD (placedN n base c i) x = true :=
    goMoveN_occ_le base c i r hr x hx
  rcases kind_some_of_occ hoccP with ⟨kx, hkxP⟩
  have hkxr : kindAt r x = some kx := by
    rw [kindAt_standing base c i r hr x hx]
    exact hkxP
  have hres := goMoveN_result base c i r hr
  have hxb : x < n*n := by
    by_cases h : x < n*n
    · exact h
    · exfalso
      unfold occD at hx
      rw [hres] at hx
      split at hx
      · rw [erasedN_get, if_neg h] at hx
        simp at hx
      · rw [afterCapN_get, if_neg h] at hx
        simp at hx
  by_cases hkc : kx = c.opp
  · -- opposite-color survivor: its placed component kept a liberty
    subst hkc
    have hxnd : x ∉ deadOppN n base c i := by
      intro hd
      have hdd := occD_output_dead base c i r hr x hxb hd
      rw [hdd] at hx
      exact Bool.noConfusion hx
    have hnlP : noLibD (placedN n base c i)
        (componentD (placedN n base c i) x) = false := by
      cases hnl : noLibD (placedN n base c i)
          (componentD (placedN n base c i) x)
      · rfl
      · exact absurd ((mem_deadOppN_iff base c i x).mpr
          ⟨List.mem_range.mpr hxb, hkxP, hnl⟩) hxnd
    rcases (noLibD_eq_false_iff _ _).mp hnlP with ⟨l, hlb, hlP, m, hm, hadj⟩
    have hsur : ∀ m', m' ∈ componentD (placedN n base c i) x →
        kindAt r m' = some c.opp := by
      intro m' hm'
      have hm'k : kindAt (placedN n base c i) m' = some c.opp :=
        componentD_kind _ x c.opp hkxP m' hm'
      have hm'b : m' ∈ allIdx n :=
        componentD_board (List.mem_range.mpr hxb) hkxP hm'
      have hm'nd : m' ∉ deadOppN n base c i := by
        intro hd
        rcases (mem_deadOppN_iff base c i m').mp hd with ⟨_, _, hnl'⟩
        have hmm := componentD_eq_mem (placedN n base c i) x m' c.opp
          (List.mem_range.mpr hxb) hkxP hm'
        rw [noLibD_congr _ _ _ hmm, hnlP] at hnl'
        exact Bool.noConfusion hnl'
      have hm'nc : ¬ (deadOppN n base c i).contains m' = true :=
        fun hcont => hm'nd (List.contains_iff_mem.mp hcont)
      have hm'nown : ¬ (ownCompN n base c i).contains m' = true := by
        intro hcont
        have hown := List.contains_iff_mem.mp hcont
        have : kindAt (afterCapN n base c i) m' = some c :=
          componentD_kind _ i c
            (kindAt_afterCapN_self base c i hwf hi hc) m' hown
        have hpk : kindAt (placedN n base c i) m' = some c :=
          (kind_c_agree_afterCapN base c i hc m' hm'b).mpr this
        rw [hm'k] at hpk
        exact opp_ne_self hc (Option.some.inj hpk)
      have hocc' : occD r m' = true := by
        rw [hres]
        split
        · rw [occD_erasedN base c i m' (List.mem_range.mp hm'b),
            if_neg hm'nown,
            occD_afterCapN base c i m' (List.mem_range.mp hm'b),
            if_neg hm'nc]
          exact occD_of_kind hm'k
        · rw [occD_afterCapN base c i m' (List.mem_range.mp hm'b),
            if_neg hm'nc]
          exact occD_of_kind hm'k
      rw [kindAt_standing base c i r hr m' hocc']
      exact hm'k
    have hmr : m ∈ componentD r x :=
      componentD_transport_rel (placedN n base c i) r c.opp x hkxP hsur m hm
    have hlr : occD r l = false := by
      cases ho : occD r l
      · rfl
      · exfalso
        have hoP := goMoveN_occ_le base c i r hr l ho
        rw [hlP] at hoP
        exact Bool.noConfusion hoP
    exact (noLibD_eq_false_iff _ _).mpr ⟨l, hlb, hlr, m, hmr, hadj⟩
  · -- the survivor has the mover's color
    have hkxnr : kx ≠ .r := by
      intro h
      exact goMoveN_classical base c i r hclass hc hr x (h ▸ hkxr)
    have hkxc : kx = c := by
      cases c <;> cases kx <;>
        first
          | rfl
          | exact absurd rfl hc
          | exact absurd rfl hkc
          | exact absurd rfl hkxnr
    subst kx
    by_cases hsui : suicideN n base c i = true
    · -- suicide: the whole own component is gone; x is an untouched
      -- base component whose base liberty survives (i itself is empty)
      have hdnil := suicide_no_captures base c i hwf hi hc hlegal hemp hsui
      have hiown : i ∈ ownCompN n base c i :=
        componentD_mem_self _ i c
          (kindAt_afterCapN_self base c i hwf hi hc)
      have hxnown : x ∉ ownCompN n base c i := by
        intro hown
        have hxe : occD r x = false := by
          rw [hres, if_pos hsui, occD_erasedN base c i x hxb,
            if_pos (List.contains_iff_mem.mpr hown)]
        rw [hxe] at hx
        exact Bool.noConfusion hx
      have hxi : x ≠ i := fun h => hxnown (h ▸ hiown)
      have hkxA : kindAt base x = some c := by
        rw [← kindAt_placedN_ne base c i x hxi]
        exact hkxP
      rcases (noLibD_eq_false_iff _ _).mp (hlegal x (occD_of_kind hkxA))
        with ⟨l0, hl0b, hl0A, m0, hm0, hadj0⟩
      have hagree : ∀ z, z ∈ allIdx n → kindAt base z = some c →
          kindAt (afterCapN n base c i) z = some c := by
        intro z hz hzk
        have hzi : z ≠ i := by
          intro h
          rw [h, kind_none_of_unocc hemp] at hzk
          exact Option.noConfusion hzk
        have hnc : ¬ (([] : List Nat).contains z = true) :=
          fun hcont => Bool.noConfusion hcont
        rw [kindAt_afterCapN base c i z (List.mem_range.mp hz), hdnil,
          if_neg hnc, kindAt_placedN_ne base c i z hzi]
        exact hzk
      have hsur : ∀ m', m' ∈ componentD base x → kindAt r m' = some c := by
        intro m' hm'
        have hm'k : kindAt base m' = some c :=
          componentD_kind base x c hkxA m' hm'
        have hm'b : m' ∈ allIdx n :=
          componentD_board (List.mem_range.mpr hxb) hkxA hm'
        have hm'i : m' ≠ i := by
          intro h
          rw [h, kind_none_of_unocc hemp] at hm'k
          exact Option.noConfusion hm'k
        have hm'kP : kindAt (placedN n base c i) m' = some c := by
          rw [kindAt_placedN_ne base c i m' hm'i]
          exact hm'k
        have hm'nown : m' ∉ ownCompN n base c i := by
          intro hown
          have hxm' : x ∈ componentD base m' :=
            (componentD_eq_mem base x m' c (List.mem_range.mpr hxb)
              hkxA hm' x).mpr (componentD_mem_self base x c hkxA)
          have hkm'CB : kindAt (afterCapN n base c i) m' = some c :=
            hagree m' hm'b hm'k
          have hxCB : x ∈ componentD (afterCapN n base c i) m' := by
            rw [componentD_mem_iff _ m' c hkm'CB x]
            exact ConnK_transport base (afterCapN n base c i) c hagree
              ((componentD_mem_iff base m' c hm'k x).mp hxm')
          exact hxnown ((componentD_eq_mem (afterCapN n base c i) i m' c
            (List.mem_range.mpr hi)
            (kindAt_afterCapN_self base c i hwf hi hc) hown x).mp hxCB)
        have hno : ¬ (ownCompN n base c i).contains m' = true :=
          fun hcont => hm'nown (List.contains_iff_mem.mp hcont)
        have hnc : ¬ (([] : List Nat).contains m' = true) :=
          fun hcont => Bool.noConfusion hcont
        have hocc' : occD r m' = true := by
          rw [hres, if_pos hsui,
            occD_erasedN base c i m' (List.mem_range.mp hm'b), if_neg hno,
            occD_afterCapN base c i m' (List.mem_range.mp hm'b), hdnil,
            if_neg hnc]
          exact occD_of_kind hm'kP
        rw [kindAt_standing base c i r hr m' hocc']
        exact hm'kP
      have hmr : m0 ∈ componentD r x :=
        componentD_transport_rel base r c x hkxA hsur m0 hm0
      have hlr : occD r l0 = false := by
        cases ho : occD r l0
        · rfl
        · exfalso
          have hoP := goMoveN_occ_le base c i r hr l0 ho
          by_cases hl0i : l0 = i
          · subst l0
            have hie : occD r i = false := by
              rw [hres, if_pos hsui, occD_erasedN base c i i hi,
                if_pos (List.contains_iff_mem.mpr hiown)]
            rw [hie] at ho
            exact Bool.noConfusion ho
          · rw [occD_placedN_ne base c i l0 hl0i, hl0A] at hoP
            exact Bool.noConfusion hoP
      exact (noLibD_eq_false_iff _ _).mpr ⟨l0, hl0b, hlr, m0, hmr, hadj0⟩
    · -- no suicide: r is the capture stage
      have hrCB : r = afterCapN n base c i := by
        rw [hres, if_neg hsui]
      have hkCBi : kindAt (afterCapN n base c i) i = some c :=
        kindAt_afterCapN_self base c i hwf hi hc
      by_cases hxown : x ∈ ownCompN n base c i
      · -- the placed component: no-suicide IS its liberty
        have hnso : noLibD (afterCapN n base c i) (ownCompN n base c i)
            = false := by
          have hsf : suicideN n base c i = false := by
            cases hs : suicideN n base c i
            · rfl
            · exact absurd hs hsui
          unfold suicideN at hsf
          exact hsf
        have hmm := componentD_eq_mem (afterCapN n base c i) i x c
          (List.mem_range.mpr hi) hkCBi hxown
        rw [hrCB, noLibD_congr _ _ _ hmm]
        exact hnso
      · -- an own-colored component apart from the placed one
        have hxi : x ≠ i := fun h =>
          hxown (h ▸ componentD_mem_self _ i c hkCBi)
        have hkxA : kindAt base x = some c := by
          rw [← kindAt_placedN_ne base c i x hxi]
          exact hkxP
        rcases (noLibD_eq_false_iff _ _).mp
          (hlegal x (occD_of_kind hkxA)) with ⟨l0, hl0b, hl0A, m0, hm0, hadj0⟩
        have hagree : ∀ z, z ∈ allIdx n → kindAt base z = some c →
            kindAt (afterCapN n base c i) z = some c := by
          intro z hz hzk
          have hzi : z ≠ i := by
            intro h
            rw [h, kind_none_of_unocc hemp] at hzk
            exact Option.noConfusion hzk
          have hzkP : kindAt (placedN n base c i) z = some c := by
            rw [kindAt_placedN_ne base c i z hzi]
            exact hzk
          have hznd : z ∉ deadOppN n base c i := by
            intro hd
            rcases (mem_deadOppN_iff base c i z).mp hd with ⟨_, hk', _⟩
            rw [hzkP] at hk'
            exact opp_ne_self hc (Option.some.inj hk').symm
          have hznc : ¬ (deadOppN n base c i).contains z = true :=
            fun hcont => hznd (List.contains_iff_mem.mp hcont)
          rw [kindAt_afterCapN base c i z (List.mem_range.mp hz),
            if_neg hznc]
          exact hzkP
        have hkxCB : kindAt (afterCapN n base c i) x = some c :=
          hagree x (List.mem_range.mpr hxb) hkxA
        have hmr : m0 ∈ componentD (afterCapN n base c i) x := by
          rw [componentD_mem_iff _ x c hkxCB m0]
          exact ConnK_transport base (afterCapN n base c i) c hagree
            ((componentD_mem_iff base x c hkxA m0).mp hm0)
        have hl0i : l0 ≠ i := by
          intro h
          subst l0
          have hm0k : kindAt base m0 = some c :=
            componentD_kind base x c hkxA m0 hm0
          have hiCB : i ∈ componentD (afterCapN n base c i) x :=
            componentD_maximal (afterCapN n base c i) x c hkxCB i
              (List.mem_range.mpr hi) hkCBi m0 hmr hadj0
          exact hxown ((componentD_eq_mem (afterCapN n base c i) x i c
            (List.mem_range.mpr hxb) hkxCB hiCB x).mpr
            (componentD_mem_self _ x c hkxCB))
        have hlr : occD (afterCapN n base c i) l0 = false := by
          rw [occD_afterCapN base c i l0 (List.mem_range.mp hl0b)]
          split
          · rfl
          · rw [occD_placedN_ne base c i l0 hl0i]
            exact hl0A
        rw [hrCB]
        exact (noLibD_eq_false_iff _ _).mpr ⟨l0, hl0b, hlr, m0, hmr, hadj0⟩
