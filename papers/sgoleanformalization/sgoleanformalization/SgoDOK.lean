/- SgoDOK.lean — the main theorem, milestone 3b: the DSGo reachability
   invariant and game axioms. The invariant carries occupancy
   inclusion (the re-cut's test) instead of SGo's compatibility, plus
   nonemptiness of the entanglement — DSGo's re-cut is provably
   vacuous (delta_out), so the decoherence survives whole, which is
   what the paper's radius-infinity argument turns on. -/
import SgoDInv

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge SgoNat SgoDInv

namespace SgoDOK

variable {n : Nat}

/-! ### Stamps survive the postprocessing -/

theorem dR_get_cases (t : Nat) (M : List (Display n)) (D : Display n)
    (i : Nat) :
    (deltaRound n t M D).get i = none
    ∨ ∃ k k' st, D.get i = some (k, st)
        ∧ (deltaRound n t M D).get i = some (k', st) := by
  by_cases hi : i < n*n
  · cases hg : D.get i with
    | none => exact Or.inl (dR_get_none t M D hi hg)
    | some c =>
      obtain ⟨kk, st⟩ := c
      cases hevv : evSet n M i with
      | mk hbv hwv =>
        have hread := dR_get_pair t M D hi hg hevv
        by_cases hnbf : (!hbv && !hwv) = true
        · rw [if_pos hnbf] at hread
          exact Or.inl hread
        · rw [if_neg hnbf] at hread
          by_cases hqr : (kk == DKind.r && st == t) = true
          · rw [if_pos hqr] at hread
            by_cases hb1 : (hbv && !hwv) = true
            · rw [if_pos hb1] at hread
              exact Or.inr ⟨kk, .b, st, rfl, hread⟩
            · rw [if_neg hb1] at hread
              by_cases hw1 : (hwv && !hbv) = true
              · rw [if_pos hw1] at hread
                exact Or.inr ⟨kk, .w, st, rfl, hread⟩
              · rw [if_neg hw1] at hread
                exact Or.inr ⟨kk, kk, st, rfl, hread⟩
          · rw [if_neg hqr] at hread
            exact Or.inr ⟨kk, kk, st, rfl, hread⟩
  · exact Or.inl (dR_get_oob t M D hi)

theorem deltaAux_stamp (t : Nat) (fuel : Nat) :
    ∀ (D : Display n) (M : List (Display n)) (i : Nat),
    (deltaAux n t fuel D M).1.get i = none
    ∨ ∃ k k' st, D.get i = some (k, st)
        ∧ (deltaAux n t fuel D M).1.get i = some (k', st) := by
  induction fuel with
  | zero =>
    intro D M i
    cases hg : D.get i with
    | none => exact Or.inl hg
    | some c =>
      obtain ⟨k, st⟩ := c
      exact Or.inr ⟨k, k, st, rfl, hg⟩
  | succ fuel ih =>
    intro D M i
    have hunf : deltaAux n t (fuel+1) D M
        = if (deltaRound n t M D == D) = true
          then (deltaRound n t M D, recut n (deltaRound n t M D) M)
          else deltaAux n t fuel (deltaRound n t M D)
            (recut n (deltaRound n t M D) M) := rfl
    by_cases htest : (deltaRound n t M D == D) = true
    · rw [hunf, if_pos htest]
      exact dR_get_cases t M D i
    · rw [hunf, if_neg htest]
      rcases ih (deltaRound n t M D) (recut n (deltaRound n t M D) M) i
        with h | ⟨k, k', st, hD', hres⟩
      · exact Or.inl h
      · rcases dR_get_cases t M D i with h0 | ⟨j, j', st', hD, hDR⟩
        · rw [h0] at hD'
          cases hD'
        · rw [hDR] at hD'
          have he := Option.some.inj hD'
          have he2 : st' = st := congrArg Prod.snd he
          exact Or.inr ⟨j, k', st', hD, by rw [he2]; exact hres⟩

/-! ### Placement occupancy -/

theorem pJ_occ_mono (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    {j : Nat} (hocc : occD D j = true) :
    occD (placeJoint D t m0 m1) j = true := by
  have hset : ∀ (E : Display n) (i : Nat) (c : DKind) (s : Nat),
      occD E j = true → occD (E.set i (some (c, s))) j = true := by
    intro E i c s h
    by_cases hji : j = i
    · subst hji
      unfold occD
      by_cases hjb : j < E.cells.size
      · rw [get_set_self E j _ hjb]
        rfl
      · rw [show (E.set j (some (c, s))).get j = E.get j from by
          unfold Display.set Display.get Array.setD Array.setIfInBounds
          rw [dif_neg hjb]]
        exact h
    · unfold occD
      rw [get_set_ne E i j _ hji]
      exact h
  cases m0 with
  | none =>
    cases m1 with
    | none => exact hocc
    | some p1 => exact hset D p1 .w t hocc
  | some p0 =>
    cases m1 with
    | none => exact hset D p0 .b t hocc
    | some p1 =>
      simp only [placeJoint]
      by_cases hpp : (p0 == p1) = true
      · rw [if_pos hpp]
        exact hset D p0 .r t hocc
      · rw [if_neg hpp]
        exact hset _ p1 .w t (hset D p0 .b t hocc)

theorem pJ_occ_target0 (D : Display n) (t : Nat) {i : Nat}
    (m1 : Option Nat) (hwf : WFD D) (hi : i < n*n) :
    occD (placeJoint D t (some i) m1) i = true := by
  cases m1 with
  | none =>
    show occD (D.set i (some (.b, t))) i = true
    unfold occD
    rw [get_set_self D i _ (by rw [hwf]; exact hi)]
    rfl
  | some p1 =>
    simp only [placeJoint]
    by_cases hpp : (i == p1) = true
    · rw [if_pos hpp]
      unfold occD
      rw [get_set_self D i _ (by rw [hwf]; exact hi)]
      rfl
    · rw [if_neg hpp]
      unfold occD
      rw [get_set_ne _ p1 i _ (fun h => hpp (beq_iff_eq.mpr h)),
        get_set_self D i _ (by rw [hwf]; exact hi)]
      rfl

theorem pJ_occ_target1 (D : Display n) (t : Nat) (m0 : Option Nat)
    {i : Nat} (hwf : WFD D) (hi : i < n*n) :
    occD (placeJoint D t m0 (some i)) i = true := by
  cases m0 with
  | none =>
    show occD (D.set i (some (.w, t))) i = true
    unfold occD
    rw [get_set_self D i _ (by rw [hwf]; exact hi)]
    rfl
  | some p0 =>
    simp only [placeJoint]
    by_cases hpp : (p0 == i) = true
    · rw [if_pos hpp]
      have he : p0 = i := beq_iff_eq.mp hpp
      subst he
      unfold occD
      rw [get_set_self D p0 _ (by rw [hwf]; exact hi)]
      rfl
    · rw [if_neg hpp]
      unfold occD
      rw [get_set_self _ i _ (by rw [set_size, hwf]; exact hi)]
      rfl

/-! ### The move-restricted output combinator -/

theorem serialP_out_moves {P : Display n → Prop}
    {m0 m1 : Option Nat}
    (hstep : ∀ (d : Display n) (c : DKind), c ≠ .r → ∀ i r,
      (m0 = some i ∨ m1 = some i) → P d →
      goMoveN n d c i = some r → P r)
    {b : Display n} (hb : P b)
    {l : List (Display n)} (hl : serialP n b m0 m1 = some l) :
    ∀ x, x ∈ l → P x := by
  have hbStep : ∀ (d : Display n) (c : DKind), c ≠ .r →
      ∀ (mo : Option Nat), (mo = m0 ∨ mo = m1) → ∀ r,
      P d → bStep n d c mo = some r → P r := by
    intro d c hc mo hmo r hd hr
    cases mo with
    | none =>
      cases hr
      exact hd
    | some i =>
      refine hstep d c hc i r ?_ hd hr
      rcases hmo with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  have hb2 : ∀ (c0 c1 : DKind), c0 ≠ .r → c1 ≠ .r →
      ∀ (x0 x1 : Option Nat), (x0 = m0 ∨ x0 = m1) →
      (x1 = m0 ∨ x1 = m1) → ∀ r,
      bStep2 n b c0 c1 x0 x1 = some r → P r := by
    intro c0 c1 h0 h1 x0 x1 hx0 hx1 r hr
    unfold bStep2 at hr
    cases hs : bStep n b c0 x0 with
    | none => rw [hs] at hr; cases hr
    | some d1 =>
      rw [hs] at hr
      exact hbStep d1 c1 h1 x1 hx1 r (hbStep b c0 h0 x0 hx0 d1 hb hs) hr
  have hbw : (DKind.b : DKind) ≠ .r := by intro h; cases h
  have hww : (DKind.w : DKind) ≠ .r := by intro h; cases h
  intro x hx
  cases h01 : bStep2 n b .b .w m0 m1 with
  | some a01 =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a10 =>
      simp only [serialP, h01, h10] at hl
      cases hl
      rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
      · exact h ▸ hb2 .b .w hbw hww m0 m1 (Or.inl rfl) (Or.inr rfl)
          a01 h01
      · have hxa : x = a10 := by simpa using h
        exact hxa ▸ hb2 .w .b hww hbw m1 m0 (Or.inr rfl) (Or.inl rfl)
          a10 h10
    | none =>
      cases hy : bStep n b .w m1 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
        · exact h ▸ hb2 .b .w hbw hww m0 m1 (Or.inl rfl) (Or.inr rfl)
            a01 h01
        · have hxa : x = y := by simpa using h
          exact hxa ▸ hbStep b .w hww m1 (Or.inr rfl) y hb hy
  | none =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a10 =>
      cases hy : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
        · exact h ▸ hbStep b .b hbw m0 (Or.inl rfl) y hb hy
        · have hxa : x = a10 := by simpa using h
          exact hxa ▸ hb2 .w .b hww hbw m1 m0 (Or.inr rfl) (Or.inl rfl)
            a10 h10
    | none =>
      cases hx0 : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hx0])
      | some x0 =>
        cases hx1 : bStep n b .w m1 with
        | none =>
          exact absurd hl (by simp [serialP, h01, h10, hx0, hx1])
        | some x1 =>
          simp only [serialP, h01, h10, hx0, hx1] at hl
          cases hl
          rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
          · exact h ▸ hbStep b .b hbw m0 (Or.inl rfl) x0 hb hx0
          · have hxa : x = x1 := by simpa using h
            exact hxa ▸ hbStep b .w hww m1 (Or.inr rfl) x1 hb hx1

/-- A serialization output list is nonempty. -/
theorem serialP_ne_nil {b : Display n} {m0 m1 : Option Nat}
    {l : List (Display n)} (hl : serialP n b m0 m1 = some l) :
    l ≠ [] := by
  have hpair : ∀ (x y : Display n), dedupD n [x, y] ≠ [] := by
    intro x y h
    have : x ∈ dedupD n [x, y] :=
      (mem_dedupD_iff _ _).mpr (List.mem_cons_self x [y])
    rw [h] at this
    cases this
  cases h01 : bStep2 n b .b .w m0 m1 with
  | some a01 =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a10 =>
      simp only [serialP, h01, h10] at hl
      cases hl
      exact hpair _ _
    | none =>
      cases hy : bStep n b .w m1 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        exact hpair _ _
  | none =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a10 =>
      cases hy : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        exact hpair _ _
    | none =>
      cases hx0 : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hx0])
      | some x0 =>
        cases hx1 : bStep n b .w m1 with
        | none =>
          exact absurd hl (by simp [serialP, h01, h10, hx0, hx1])
        | some x1 =>
          simp only [serialP, h01, h10, hx0, hx1] at hl
          cases hl
          exact hpair _ _

/-! ### Occupancy inclusion through a turn -/

/-- occInc against a display with more occupancy. -/
theorem occIncB_mono {D D' b : Display n}
    (hm : ∀ j, occD D j = true → occD D' j = true)
    (h : occIncB n D b = true) : occIncB n D' b = true := by
  unfold occIncB at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro j hj
  rcases bool_or_elim (h j hj) with ho | hb
  · exact bool_or_left (hm j ho)
  · exact bool_or_right hb

/-- Serialization outputs stay under the placed display's occupancy:
    a branch move lands only on its own slot's target, and the
    placement put a stone there. -/
theorem serialP_occInc {Dp : Display n} {m0 m1 : Option Nat}
    (h0 : ∀ i, m0 = some i → occD Dp i = true)
    (h1 : ∀ i, m1 = some i → occD Dp i = true)
    {b : Display n} (hb : occIncB n Dp b = true)
    {l : List (Display n)} (hl : serialP n b m0 m1 = some l) :
    ∀ x, x ∈ l → occIncB n Dp x = true := by
  refine serialP_out_moves ?_ hb hl
  intro d c hc i r hmi hd hr
  unfold occIncB
  rw [List.all_eq_true]
  intro j hj
  have hjn : j < n*n := List.mem_range.mp hj
  cases hDp : occD Dp j with
  | true => exact bool_or_left rfl
  | false =>
    apply bool_or_right
    by_cases hji : j = i
    · subst hji
      rcases hmi with h | h
      · exact absurd (h0 j h) (by simp [hDp])
      · exact absurd (h1 j h) (by simp [hDp])
    · have hemp : occD d j = false := branch_empty_of_occInc hd hjn hDp
      have hre : occD r j = false := goMoveN_fills_only d c i j r hr hemp hji
      apply beq_iff_eq.mpr
      unfold kindAt
      unfold occD at hre
      cases hg : r.get j with
      | none => rfl
      | some cc =>
        rw [hg] at hre
        cases hre

/-! ### The DSGo turn shape -/

/-- The shape of a defined DSGo turn: nonfinal, both moves available
    on the display, and the components of the successor — the
    postprocessed placement and the re-cut entanglement. The double
    pass is not special: it runs through Δ like every turn and only
    sets the flag. -/
theorem dsgoEv_cases {s s' : SGoState n} {m0 m1 : Option Nat}
    (hst : dsgoEv n s m0 m1 = some s') :
    s.final = false ∧ availD n s.disp m0 = true ∧
    availD n s.disp m1 = true ∧
    ∃ dec, simEv n s.ent m0 m1 = some dec ∧
      s' = ⟨(delta n s.next (placeJoint s.disp s.next m0 m1) dec).1,
        s.next + 1,
        (delta n s.next (placeJoint s.disp s.next m0 m1) dec).2,
        m0.isNone && m1.isNone⟩ := by
  unfold dsgoEv at hst
  by_cases hf : s.final = true
  · rw [if_pos hf] at hst; cases hst
  · rw [if_neg hf] at hst
    have hfk : s.final = false := by
      cases hfc : s.final
      · rfl
      · exact absurd hfc hf
    by_cases hav : (availD n s.disp m0 && availD n s.disp m1) = true
    case neg =>
      have hbang : (!(availD n s.disp m0 && availD n s.disp m1)) = true := by
        cases hb : (availD n s.disp m0 && availD n s.disp m1)
        · rfl
        · exact absurd hb hav
      rw [if_pos hbang] at hst; cases hst
    case pos =>
      rw [if_neg (by simp [hav] :
        ¬((!(availD n s.disp m0 && availD n s.disp m1)) = true))] at hst
      have hsplit : availD n s.disp m0 = true ∧
          availD n s.disp m1 = true := by simpa using hav
      cases hse : simEv n s.ent m0 m1 with
      | none =>
        simp only [hse] at hst
        exact Option.noConfusion hst
      | some dec =>
        simp only [hse] at hst
        refine ⟨hfk, hsplit.1, hsplit.2, dec, rfl, ?_⟩
        cases hdel : delta n s.next (placeJoint s.disp s.next m0 m1) dec with
        | mk D' M' =>
          simp only [hdel] at hst
          cases hst
          rfl

/-- DSGo's E is defined exactly at non-final states with both moves
    display-available (under occupancy inclusion of the
    entanglement). -/
theorem dsgoEv_isSome_iff (s : SGoState n)
    (hc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true)
    (m0 m1 : Option Nat) :
    (dsgoEv n s m0 m1).isSome ↔
      (s.final = false ∧ availD n s.disp m0 = true ∧
       availD n s.disp m1 = true) := by
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨s', hs'⟩
    rcases dsgoEv_cases hs' with ⟨hf, h0, h1, -⟩
    exact ⟨hf, h0, h1⟩
  · rintro ⟨hf, h0, h1⟩
    unfold dsgoEv
    rw [if_neg (by simp [hf] : ¬(s.final = true))]
    rw [if_neg (by simp [h0, h1] :
      ¬((!(availD n s.disp m0 && availD n s.disp m1)) = true))]
    have hout : (simEv n s.ent m0 m1).isSome := by
      unfold simEv
      rcases Option.isSome_iff_exists.mp
        (simEvAux_isSome_of_occInc hc h0 h1) with ⟨out, houta⟩
      simp [houta]
    rcases Option.isSome_iff_exists.mp hout with ⟨dec, hdec⟩
    cases hdel : delta n s.next (placeJoint s.disp s.next m0 m1) dec with
    | mk D' M' => simp [hdec, hdel]

/-! ### The DSGo invariant -/

/-- The reachability invariant of DSGo: well-formedness and stamp
    bounds as in SGo, with compatibility replaced by occupancy
    inclusion (the re-cut's own test), plus nonemptiness and support
    of the display by the entanglement — the survival package. -/
structure InvD (s : SGoState n) : Prop where
  wfdD : WFD s.disp
  next_pos : 1 ≤ s.next
  stamps : StampsBelow s.disp s.next
  entWfd : ∀ b, b ∈ s.ent → WFD b
  entClassical : ∀ b, b ∈ s.ent → IsClassical b
  entZero : ∀ b, b ∈ s.ent → StampsZero b
  entInc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true
  entNe : s.ent ≠ []
  supp : ∀ i, i < n*n → occD s.disp i = true →
    ∃ b, b ∈ s.ent ∧ occD b i = true

theorem invD_init : InvD (initSGo n) := by
  refine ⟨emptyD_wfd, Nat.le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show stampAt (emptyD n) i < 1
    rw [stampAt_none _ i (emptyD_get i)]
    exact Nat.one_pos
  · intro b hb
    have hbe : b = emptyD n := by simpa [initSGo] using hb
    exact hbe ▸ emptyD_wfd
  · intro b hb
    have hbe : b = emptyD n := by simpa [initSGo] using hb
    intro i
    rw [hbe]
    unfold kindAt
    rw [emptyD_get i]
    simp
  · intro b hb
    have hbe : b = emptyD n := by simpa [initSGo] using hb
    intro i
    rw [hbe]
    exact stampAt_none _ i (emptyD_get i)
  · intro b hb
    have hbe : b = emptyD n := by simpa [initSGo] using hb
    subst hbe
    unfold occIncB
    rw [List.all_eq_true]
    intro j hj
    apply bool_or_right
    apply beq_iff_eq.mpr
    unfold kindAt
    rw [emptyD_get j]
    rfl
  · intro hcon
    cases hcon
  · intro i hi hocc
    have hg : (initSGo n).disp.get i = none := emptyD_get i
    unfold occD at hocc
    rw [hg] at hocc
    cases hocc

/-- The invariant is preserved by every defined dsgoEv step: the
    decoherence's branches inherit the branch properties from the
    serializations, land under the placed display's occupancy, and
    delta_out then says the re-cut keeps them all while the output
    display stays well-formed, stamp-bounded, above the branches and
    supported by them. -/
theorem invD_step {s s' : SGoState n} (h : InvD s) {m0 m1 : Option Nat}
    (hst : dsgoEv n s m0 m1 = some s') : InvD s' := by
  rcases dsgoEv_cases hst with ⟨hf, h0, h1, dec, hse, hs'⟩
  subst hs'
  have hkey : (∀ x, x ∈ dec →
      ∃ b, b ∈ s.ent ∧ ∃ l, serialP n b m0 m1 = some l ∧ x ∈ l)
      ∧ dec ≠ [] := by
    unfold simEv at hse
    cases hax : simEvAux n m0 m1 s.ent with
    | none => rw [hax] at hse; cases hse
    | some out =>
      rw [hax] at hse
      have hbs : dec = dedupD n out := by
        have hh : some (dedupD n out) = some dec := hse
        exact (Option.some.inj hh).symm
      constructor
      · intro x hx
        exact simEvAux_mem hax (mem_dedupD _ _ (hbs ▸ hx))
      · cases hent : s.ent with
        | nil => exact absurd hent h.entNe
        | cons b0 bs0 =>
          rw [hent] at hax
          cases hp : serialP n b0 m0 m1 with
          | none => exact absurd hax (by simp [simEvAux, hp])
          | some l =>
            cases hrr : simEvAux n m0 m1 bs0 with
            | none => exact absurd hax (by simp [simEvAux, hp, hrr])
            | some r =>
              simp only [simEvAux, hp, hrr] at hax
              have hor : l ++ r = out := Option.some.inj hax
              cases hl0 : l with
              | nil => exact absurd hl0 (serialP_ne_nil hp)
              | cons z zs =>
                intro hcon
                rw [hl0] at hor
                have hz : z ∈ dec := by
                  rw [hbs]
                  apply (mem_dedupD_iff _ _).mpr
                  rw [← hor]
                  exact List.mem_append.mpr
                    (Or.inl (List.mem_cons_self z zs))
                rw [hcon] at hz
                cases hz
  rcases hkey with ⟨hdecmem, hdecne⟩
  have hwfp : WFD (placeJoint s.disp s.next m0 m1) :=
    placeJoint_wfd _ _ _ _ h.wfdD
  have htgt0 : ∀ i, m0 = some i →
      occD (placeJoint s.disp s.next m0 m1) i = true := by
    intro i hi
    have hii : i < n*n := bounds_of_availD h0 i hi
    rw [hi]
    exact pJ_occ_target0 s.disp s.next m1 h.wfdD hii
  have htgt1 : ∀ i, m1 = some i →
      occD (placeJoint s.disp s.next m0 m1) i = true := by
    intro i hi
    have hii : i < n*n := bounds_of_availD h1 i hi
    rw [hi]
    exact pJ_occ_target1 s.disp s.next m0 h.wfdD hii
  have hdecWfd : ∀ x, x ∈ dec → WFD x := by
    intro x hx
    rcases hdecmem x hx with ⟨b0, hb0, l, hl, hxl⟩
    exact serialP_out
      (fun d c _ i r _ hr => goMoveN_size d c i r hr)
      (h.entWfd b0 hb0) hl x hxl
  have hdecCl : ∀ x, x ∈ dec → IsClassical x ∧ StampsZero x := by
    intro x hx
    rcases hdecmem x hx with ⟨b0, hb0, l, hl, hxl⟩
    exact serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl x hxl
  have hdecInc : ∀ x, x ∈ dec →
      occIncB n (placeJoint s.disp s.next m0 m1) x = true := by
    intro x hx
    rcases hdecmem x hx with ⟨b0, hb0, l, hl, hxl⟩
    refine serialP_occInc htgt0 htgt1 ?_ hl x hxl
    exact occIncB_mono
      (fun j ho => pJ_occ_mono s.disp s.next m0 m1 ho)
      (h.entInc b0 hb0)
  obtain ⟨hmem_iff, hwf', hinc', hsupp'⟩ :=
    delta_out s.next (placeJoint s.disp s.next m0 m1) dec hwfp
      (fun b hb => (hdecCl b hb).1) hdecInc
  refine ⟨hwf', Nat.le_succ_of_le h.next_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stamps: survive Δ at their placed values, all below next+1
    intro i
    show stampAt (delta n s.next (placeJoint s.disp s.next m0 m1) dec).1 i
      < s.next + 1
    have hsb : StampsBelow (placeJoint s.disp s.next m0 m1) (s.next + 1) :=
      placeJoint_stampsBelow _ _ _ _ h.stamps
    have hcase := deltaAux_stamp (n := n) s.next (2*(n*n)+2)
      (placeJoint s.disp s.next m0 m1) dec i
    unfold delta
    rcases hcase with hnone | ⟨k, k', st, hgp, hgo⟩
    · unfold stampAt
      rw [hnone]
      exact Nat.succ_pos _
    · have hlt : st < s.next + 1 := by
        have hh := hsb i
        unfold stampAt at hh
        rw [hgp] at hh
        exact hh
      unfold stampAt
      rw [hgo]
      exact hlt
  · intro b hb
    exact hdecWfd b ((hmem_iff b).mp hb)
  · intro b hb
    exact (hdecCl b ((hmem_iff b).mp hb)).1
  · intro b hb
    exact (hdecCl b ((hmem_iff b).mp hb)).2
  · intro b hb
    exact hinc' b ((hmem_iff b).mp hb)
  · -- nonemptiness: the re-cut is vacuous
    show (delta n s.next (placeJoint s.disp s.next m0 m1) dec).2 ≠ []
    intro hcon
    cases hdc : dec with
    | nil => exact hdecne hdc
    | cons z zs =>
      have hz : z ∈ (delta n s.next (placeJoint s.disp s.next m0 m1) dec).2 :=
        (hmem_iff z).mpr (hdc ▸ List.mem_cons_self z zs)
      rw [hcon] at hz
      cases hz
  · intro i hi hocc
    rcases hsupp' i hi hocc with ⟨b, hb, hbo⟩
    exact ⟨b, (hmem_iff b).mpr hb, hbo⟩

/-! ### The invariant along reachability, and the game axioms -/

theorem pairE_to_dsgoEv {s s' : SGoState n} {ma mb : goMv.M}
    (h : (dsgoGame n).pairE s ma mb = some s') :
    ∃ m0 m1, dsgoEv n s m0 m1 = some s' := by
  unfold dsgoGame at h
  simp only at h
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at h; cases h
  | some p =>
    rw [hsl] at h
    exact ⟨p.1, p.2, h⟩

theorem reach_invD {s : SGoState n} (h : SimReach (dsgoGame n) s) :
    InvD s := by
  induction h with
  | init => exact invD_init
  | step hr hst ih =>
    rcases pairE_to_dsgoEv hst with ⟨m0, m1, hev⟩
    exact invD_step ih hev

theorem availD_of_availD {s : SGoState n} {m : goMv.M}
    (hm : (dsgoGame n).avail s m) :
    ∀ w i, m = some (w, i) → availD n s.disp (some i) = true := by
  intro w i hmi
  rcases hm.2 with h | ⟨w', i', hmi', hi', hocc'⟩
  · rw [hmi] at h; cases h
  · rw [hmi] at hmi'
    cases hmi'
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi', hocc']
    rfl

/-- def_simultaneous's properties for DSGo over reachable states. -/
theorem dsgo_simOK : SimOK (dsgoGame n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- final_nomove
    intro s m _ hfin hav
    have h1 : s.final = true := hfin
    rw [hav.1] at h1
    cases h1
  · -- pass_available
    intro s _ hnf
    refine ⟨?_, Or.inl rfl⟩
    cases hfc : s.final
    · rfl
    · exact absurd hfc hnf
  · -- pair_of_avail
    intro s m0 m1 hr hd0 hd1 hav0 hav1
    have hInv := reach_invD hr
    have hfin : s.final = false := hav0.1
    have hpassD : availD n s.disp none = true := rfl
    unfold dsgoGame
    simp only
    cases m0 with
    | none =>
      cases m1 with
      | none =>
        show (dsgoEv n s none none).isSome
        exact (dsgoEv_isSome_iff s hInv.entInc none none).mpr
          ⟨hfin, hpassD, hpassD⟩
      | some p1 =>
        rcases hd1 with h | ⟨i, hi⟩
        · cases h
        · cases hi
          show (dsgoEv n s none (some i)).isSome
          exact (dsgoEv_isSome_iff s hInv.entInc none (some i)).mpr
            ⟨hfin, hpassD, availD_of_availD hav1 true i rfl⟩
    | some p0 =>
      rcases hd0 with h | ⟨i0, hi0⟩
      · cases h
      · cases hi0
        cases m1 with
        | none =>
          show (dsgoEv n s (some i0) none).isSome
          exact (dsgoEv_isSome_iff s hInv.entInc (some i0) none).mpr
            ⟨hfin, availD_of_availD hav0 false i0 rfl, hpassD⟩
        | some p1 =>
          rcases hd1 with h | ⟨i1, hi1⟩
          · cases h
          · cases hi1
            show (dsgoEv n s (some i0) (some i1)).isSome
            exact (dsgoEv_isSome_iff s hInv.entInc
              (some i0) (some i1)).mpr
              ⟨hfin, availD_of_availD hav0 false i0 rfl,
               availD_of_availD hav1 true i1 rfl⟩
  · -- avail_of_pair
    intro s m0 m1 hr hp
    have hInv := reach_invD hr
    rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
    unfold dsgoGame at hs'
    simp only at hs'
    cases hsl : slotMoves m0 m1 with
    | none => rw [hsl] at hs'; cases hs'
    | some p =>
      rw [hsl] at hs'
      have h2 : dsgoEv n s p.1 p.2 = some s' := hs'
      have hev : (dsgoEv n s p.1 p.2).isSome := by rw [h2]; rfl
      have hiff := (dsgoEv_isSome_iff s hInv.entInc p.1 p.2).mp hev
      have hfin := hiff.1
      have havOf : ∀ (m : goMv.M) (a : Option Nat),
          (∀ w i, m = some (w, i) → a = some i) →
          availD n s.disp a = true → (dsgoGame n).avail s m := by
        intro m a hshape hava
        refine ⟨hfin, ?_⟩
        cases m with
        | none => exact Or.inl rfl
        | some wi =>
          refine Or.inr ⟨wi.1, wi.2, rfl, ?_, ?_⟩
          · have ha := hshape wi.1 wi.2 rfl
            rw [ha] at hava
            unfold availD at hava
            have := Bool.and_eq_true (decide (wi.2 < n*n)) (!occD s.disp wi.2)
            rw [this] at hava
            exact of_decide_eq_true hava.1
          · have ha := hshape wi.1 wi.2 rfl
            rw [ha] at hava
            unfold availD at hava
            have := Bool.and_eq_true (decide (wi.2 < n*n)) (!occD s.disp wi.2)
            rw [this] at hava
            have hb := hava.2
            cases hoc : occD s.disp wi.2
            · rfl
            · rw [hoc] at hb; exact absurd hb (by simp)
      cases m0 with
      | none =>
        cases m1 with
        | none =>
            simp only [slotMoves] at hsl
            cases hsl
            exact ⟨havOf none none (by intro w i h; cases h) hiff.2.1,
                   havOf none none (by intro w i h; cases h) hiff.2.2⟩
        | some wi =>
            simp only [slotMoves] at hsl
            by_cases hw : wi.1 = true
            · rw [show wi = (wi.1, wi.2) from rfl, hw] at hsl
              simp only [if_true] at hsl
              cases hsl
              exact ⟨havOf none none (by intro w i h; cases h) hiff.2.1,
                     havOf (some wi) (some wi.2)
                       (by intro w i h; cases h; rfl) hiff.2.2⟩
            · have hwf : wi.1 = false := by
                cases hwc : wi.1
                · rfl
                · exact absurd hwc hw
              rw [show wi = (wi.1, wi.2) from rfl, hwf] at hsl
              simp only [Bool.false_eq_true, if_false] at hsl
              cases hsl
              exact ⟨havOf none none (by intro w i h; cases h) hiff.2.2,
                     havOf (some wi) (some wi.2)
                       (by intro w i h; cases h; rfl) hiff.2.1⟩
      | some wi0 =>
        cases m1 with
        | none =>
            simp only [slotMoves] at hsl
            by_cases hw : wi0.1 = true
            · rw [show wi0 = (wi0.1, wi0.2) from rfl, hw] at hsl
              simp only [if_true] at hsl
              cases hsl
              exact ⟨havOf (some wi0) (some wi0.2)
                       (by intro w i h; cases h; rfl) hiff.2.2,
                     havOf none none (by intro w i h; cases h) hiff.2.1⟩
            · have hwf : wi0.1 = false := by
                cases hwc : wi0.1
                · rfl
                · exact absurd hwc hw
              rw [show wi0 = (wi0.1, wi0.2) from rfl, hwf] at hsl
              simp only [Bool.false_eq_true, if_false] at hsl
              cases hsl
              exact ⟨havOf (some wi0) (some wi0.2)
                       (by intro w i h; cases h; rfl) hiff.2.1,
                     havOf none none (by intro w i h; cases h) hiff.2.2⟩
        | some wi1 =>
            simp only [slotMoves] at hsl
            by_cases hsame : (wi0.1 == wi1.1) = true
            · rw [show wi0 = (wi0.1, wi0.2) from rfl,
                show wi1 = (wi1.1, wi1.2) from rfl] at hsl
              rw [if_pos hsame] at hsl
              cases hsl
            · rw [show wi0 = (wi0.1, wi0.2) from rfl,
                show wi1 = (wi1.1, wi1.2) from rfl] at hsl
              rw [if_neg hsame] at hsl
              by_cases hw0 : wi0.1 = true
              · rw [hw0] at hsl
                simp only [if_true] at hsl
                cases hsl
                exact ⟨havOf (some wi0) (some wi0.2)
                         (by intro w i h; cases h; rfl) hiff.2.2,
                       havOf (some wi1) (some wi1.2)
                         (by intro w i h; cases h; rfl) hiff.2.1⟩
              · have hwf : wi0.1 = false := by
                  cases hwc : wi0.1
                  · rfl
                  · exact absurd hwc hw0
                rw [hwf] at hsl
                simp only [Bool.false_eq_true, if_false] at hsl
                cases hsl
                exact ⟨havOf (some wi0) (some wi0.2)
                         (by intro w i h; cases h; rfl) hiff.2.1,
                       havOf (some wi1) (some wi1.2)
                         (by intro w i h; cases h; rfl) hiff.2.2⟩
  · -- final_exists
    exact ⟨⟨emptyD n, 2, [emptyD n], true⟩, rfl⟩

end SgoDOK
