/- SgoKInv.lean — the main theorem, milestone 4a: the k-DSGo invariant and
   game axioms.

   Off the semiclassical window the delayed game's display can differ
   from every branch (that is the point of the delay), so the k-DSGo
   invariant carries occupancy inclusion in the SELF-supported form:
   whatever entered delta, its output entanglement passed the final
   re-cut against the output display — no input bundle needed, only
   the measure argument for the fuel (deltaAux_selfOut). The verdict
   queue keeps its length; verdict execution only removes stones and
   keeps recolored stamps, so stamp bounds survive it. -/
import SgoDFaith

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoDInv SgoDOK SgoDNat SgoDSemi

namespace SgoKInv

variable {n : Nat}

/-- The state projection to DSGo's data. -/
def toS (s : KState n) : SGoState n := ⟨s.disp, s.next, s.ent, s.final⟩

/-! ### Verdict execution -/

theorem execV_empty (D : Display n) : execV n emptyV D = D := rfl

/-- Preservation through a fold. -/
theorem foldl_pres {α : Type} (P : Display n → Prop)
    (f : Display n → α → Display n)
    (hf : ∀ A a, P A → P (f A a)) :
    ∀ (l : List α) (A : Display n), P A → P (l.foldl f A) := by
  intro l
  induction l with
  | nil => intro A h; exact h
  | cons a l ih =>
    intro A h
    exact ih (f A a) (hf A a h)

theorem execV_wfd (v : Verdict) (D : Display n) (hwf : WFD D) :
    WFD (execV n v D) := by
  unfold execV
  apply foldl_pres (fun A => WFD A)
  · intro A pr h
    obtain ⟨i, st, c⟩ := pr
    show WFD (match A.get i with
      | some (_, st') => if st' == st then A.set i (some (c, st')) else A
      | none => A)
    cases hg : A.get i with
    | none => exact h
    | some cc =>
      obtain ⟨k', st'⟩ := cc
      show WFD (if (st' == st) = true then A.set i (some (c, st')) else A)
      by_cases hst : (st' == st) = true
      · rw [if_pos hst]
        show (A.set i _).cells.size = n*n
        rw [set_size]
        exact h
      · rw [if_neg hst]
        exact h
  · apply foldl_pres (fun A => WFD A)
    · intro A pr h
      obtain ⟨i, st⟩ := pr
      show WFD (match A.get i with
        | some (_, st') => if st' == st then A.set i none else A
        | none => A)
      cases hg : A.get i with
      | none => exact h
      | some cc =>
        obtain ⟨k', st'⟩ := cc
        show WFD (if (st' == st) = true then A.set i none else A)
        by_cases hst : (st' == st) = true
        · rw [if_pos hst]
          show (A.set i _).cells.size = n*n
          rw [set_size]
          exact h
        · rw [if_neg hst]
          exact h
    · exact hwf

theorem stamps_set_none (D : Display n) (i : Nat) {u : Nat}
    (hu : 1 ≤ u) (hD : StampsBelow D u) :
    StampsBelow (D.set i none) u := by
  intro p
  by_cases hpi : p = i
  · subst hpi
    by_cases hb : p < D.cells.size
    · unfold stampAt
      rw [get_set_self D p _ hb]
      exact hu
    · unfold stampAt
      rw [show (D.set p (none : Option (DKind × Nat))).get p = D.get p
        from by
          unfold Display.set Display.get Array.setD Array.setIfInBounds
          rw [dif_neg hb]]
      exact hD p
  · unfold stampAt
    rw [get_set_ne D i p _ hpi]
    exact hD p

theorem execV_stampsBelow (v : Verdict) (D : Display n) {u : Nat}
    (hu : 1 ≤ u) (hD : StampsBelow D u) :
    StampsBelow (execV n v D) u := by
  unfold execV
  apply foldl_pres (fun A => StampsBelow A u)
  · intro A pr h
    obtain ⟨i, st, c⟩ := pr
    show StampsBelow (match A.get i with
      | some (_, st') => if st' == st then A.set i (some (c, st')) else A
      | none => A) u
    cases hg : A.get i with
    | none => exact h
    | some cc =>
      obtain ⟨k', st'⟩ := cc
      show StampsBelow
        (if (st' == st) = true then A.set i (some (c, st')) else A) u
      by_cases hst : (st' == st) = true
      · rw [if_pos hst]
        have hst' : st' < u := by
          have hp := h i
          unfold stampAt at hp
          rw [hg] at hp
          exact hp
        exact set_stampsBelow A i c st' u hst' h
      · rw [if_neg hst]
        exact h
  · apply foldl_pres (fun A => StampsBelow A u)
    · intro A pr h
      obtain ⟨i, st⟩ := pr
      show StampsBelow (match A.get i with
        | some (_, st') => if st' == st then A.set i none else A
        | none => A) u
      cases hg : A.get i with
      | none => exact h
      | some cc =>
        obtain ⟨k', st'⟩ := cc
        show StampsBelow (if (st' == st) = true then A.set i none else A) u
        by_cases hst : (st' == st) = true
        · rw [if_pos hst]
          exact stamps_set_none A i hu h
        · rw [if_neg hst]
          exact h
    · exact hD

/-! ### The k-DSGo turn shape -/

theorem kEv_cases {s s' : KState n} {m0 m1 : Option Nat}
    (hst : kEv n s m0 m1 = some s') :
    s.final = false ∧ availD n s.disp m0 = true ∧
    availD n s.disp m1 = true ∧
    ∃ v1 vrest dec, s.verdicts = v1 :: vrest ∧
      simEv n s.ent m0 m1 = some dec ∧
      s' = ⟨(delta n s.next
              (placeJoint (execV n v1 s.disp) s.next m0 m1) dec).1,
        s.next + 1,
        (delta n s.next
              (placeJoint (execV n v1 s.disp) s.next m0 m1) dec).2,
        vrest ++ [verOf n s.next
          (delta n s.next
              (placeJoint (execV n v1 s.disp) s.next m0 m1) dec).1],
        m0.isNone && m1.isNone⟩ := by
  unfold kEv at hst
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
      cases hq : s.verdicts with
      | nil =>
        simp only [hq] at hst
        exact Option.noConfusion hst
      | cons v1 vrest =>
        simp only [hq] at hst
        cases hse : simEv n s.ent m0 m1 with
        | none =>
          simp only [hse] at hst
          exact Option.noConfusion hst
        | some dec =>
          simp only [hse] at hst
          refine ⟨hfk, hsplit.1, hsplit.2, v1, vrest, dec, rfl, rfl, ?_⟩
          cases hdel : delta n s.next
              (placeJoint (execV n v1 s.disp) s.next m0 m1) dec with
          | mk D' M' =>
            simp only [hdel] at hst
            cases hst
            rfl

/-! ### The self-supported delta output -/

/-- Without any input bundle: the recursion's fuel suffices (the
    measure drops at every changing round), and whatever it outputs
    passed the final re-cut — members of the input list standing
    under the output display. -/
theorem deltaAux_selfOut (t : Nat) (fuel : Nat) :
    ∀ (D : Display n) (M : List (Display n)), WFD D → measD D < fuel →
    WFD (deltaAux n t fuel D M).1
    ∧ ∀ b, b ∈ (deltaAux n t fuel D M).2 →
        b ∈ M ∧ occIncB n (deltaAux n t fuel D M).1 b = true := by
  induction fuel with
  | zero =>
    intro D M hwf hm
    exact absurd hm (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro D M hwf hm
    have hunf : deltaAux n t (fuel+1) D M
        = if (deltaRound n t M D == D) = true
          then (deltaRound n t M D, recut n (deltaRound n t M D) M)
          else deltaAux n t fuel (deltaRound n t M D)
            (recut n (deltaRound n t M D) M) := rfl
    by_cases htest : (deltaRound n t M D == D) = true
    · rw [hunf, if_pos htest]
      refine ⟨dR_wfd t M D, ?_⟩
      intro b hb
      exact (recut_mem (deltaRound n t M D) M b).mp hb
    · rw [hunf, if_neg htest]
      have hne : ¬ deltaRound n t M D = D := by
        intro he
        apply htest
        rw [he]
        exact display_beq_self D
      have hdrop := dR_meas t M D hwf hne
      have hres := ih (deltaRound n t M D)
        (recut n (deltaRound n t M D) M) (dR_wfd t M D) (by omega)
      refine ⟨hres.1, ?_⟩
      intro b hb
      have h2 := hres.2 b hb
      exact ⟨((recut_mem _ _ b).mp h2.1).1, h2.2⟩

theorem delta_selfOut (t : Nat) (D : Display n) (M : List (Display n))
    (hwf : WFD D) :
    WFD (delta n t D M).1
    ∧ ∀ b, b ∈ (delta n t D M).2 →
        b ∈ M ∧ occIncB n (delta n t D M).1 b = true := by
  have hfuel : measD D < 2*(n*n) + 2 := by
    have := measD_le D
    omega
  exact deltaAux_selfOut t (2*(n*n) + 2) D M hwf hfuel

/-! ### The k-DSGo invariant -/

structure InvK (k : Nat) (s : KState n) : Prop where
  wfdD : WFD s.disp
  next_pos : 1 ≤ s.next
  stamps : StampsBelow s.disp s.next
  entWfd : ∀ b, b ∈ s.ent → WFD b
  entClassical : ∀ b, b ∈ s.ent → IsClassical b
  entZero : ∀ b, b ∈ s.ent → StampsZero b
  entInc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true
  vlen : s.verdicts.length = k

theorem invK_init (k : Nat) : InvK k (initK n k) := by
  refine ⟨emptyD_wfd, Nat.le_refl 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show stampAt (emptyD n) i < 1
    rw [stampAt_none _ i (emptyD_get i)]
    exact Nat.one_pos
  · intro b hb
    have hbe : b = emptyD n := by simpa [initK] using hb
    exact hbe ▸ emptyD_wfd
  · intro b hb
    have hbe : b = emptyD n := by simpa [initK] using hb
    intro i
    rw [hbe]
    unfold kindAt
    rw [emptyD_get i]
    simp
  · intro b hb
    have hbe : b = emptyD n := by simpa [initK] using hb
    intro i
    rw [hbe]
    exact stampAt_none _ i (emptyD_get i)
  · intro b hb
    have hbe : b = emptyD n := by simpa [initK] using hb
    subst hbe
    unfold occIncB
    rw [List.all_eq_true]
    intro j hj
    apply bool_or_right
    apply beq_iff_eq.mpr
    unfold kindAt
    rw [emptyD_get j]
    rfl
  · show (List.replicate k emptyV).length = k
    exact List.length_replicate k emptyV

theorem invK_step {k : Nat} {s s' : KState n} (h : InvK k s)
    {m0 m1 : Option Nat} (hst : kEv n s m0 m1 = some s') :
    InvK k s' := by
  rcases kEv_cases hst with
    ⟨hf, h0, h1, v1, vrest, dec, hq, hse, hs'⟩
  subst hs'
  have hdecmem : ∀ x, x ∈ dec →
      ∃ b, b ∈ s.ent ∧ ∃ l, serialP n b m0 m1 = some l ∧ x ∈ l :=
    fun x hx => simEv_mem hse hx
  have hwfE : WFD (execV n v1 s.disp) := execV_wfd v1 s.disp h.wfdD
  have hwfp : WFD (placeJoint (execV n v1 s.disp) s.next m0 m1) :=
    placeJoint_wfd _ _ _ _ hwfE
  obtain ⟨hwf', hself⟩ := delta_selfOut s.next
    (placeJoint (execV n v1 s.disp) s.next m0 m1) dec hwfp
  refine ⟨hwf', Nat.le_succ_of_le h.next_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- stamps
    intro i
    show stampAt (delta n s.next
        (placeJoint (execV n v1 s.disp) s.next m0 m1) dec).1 i
      < s.next + 1
    have hsb : StampsBelow
        (placeJoint (execV n v1 s.disp) s.next m0 m1) (s.next + 1) :=
      placeJoint_stampsBelow _ _ _ _
        (execV_stampsBelow v1 s.disp h.next_pos h.stamps)
    have hcase := deltaAux_stamp (n := n) s.next (2*(n*n)+2)
      (placeJoint (execV n v1 s.disp) s.next m0 m1) dec i
    unfold delta
    rcases hcase with hnone | ⟨kk, kk', st, hgp, hgo⟩
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
    rcases hdecmem b (hself b hb).1 with ⟨b0, hb0, l, hl, hbl⟩
    exact serialP_out
      (fun d c _ i r _ hr => goMoveN_size d c i r hr)
      (h.entWfd b0 hb0) hl b hbl
  · intro b hb
    rcases hdecmem b (hself b hb).1 with ⟨b0, hb0, l, hl, hbl⟩
    exact (serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl b hbl).1
  · intro b hb
    rcases hdecmem b (hself b hb).1 with ⟨b0, hb0, l, hl, hbl⟩
    exact (serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl b hbl).2
  · intro b hb
    exact (hself b hb).2
  · -- the queue keeps its length
    show (vrest ++ [verOf n s.next _]).length = k
    have hvl := h.vlen
    rw [hq, List.length_cons] at hvl
    rw [List.length_append]
    simpa using hvl

/-! ### The invariant along reachability, and the game axioms -/

theorem pairE_to_kEv {k : Nat} {s s' : KState n} {ma mb : goMv.M}
    (h : (kGame n k).pairE s ma mb = some s') :
    ∃ m0 m1, kEv n s m0 m1 = some s' := by
  unfold kGame at h
  simp only at h
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at h; cases h
  | some p =>
    rw [hsl] at h
    exact ⟨p.1, p.2, h⟩

theorem reach_invK {k : Nat} {s : KState n}
    (h : SimReach (kGame n k) s) : InvK k s := by
  induction h with
  | init => exact invK_init k
  | step hr hst ih =>
    rcases pairE_to_kEv hst with ⟨m0, m1, hev⟩
    exact invK_step ih hev

/-- kEv is defined exactly at non-final states with both moves
    display-available, under occupancy inclusion and a nonempty
    verdict queue. -/
theorem kEv_isSome_iff (s : KState n)
    (hc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true)
    (hqne : s.verdicts ≠ [])
    (m0 m1 : Option Nat) :
    (kEv n s m0 m1).isSome ↔
      (s.final = false ∧ availD n s.disp m0 = true ∧
       availD n s.disp m1 = true) := by
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨s', hs'⟩
    rcases kEv_cases hs' with ⟨hf, h0, h1, -⟩
    exact ⟨hf, h0, h1⟩
  · rintro ⟨hf, h0, h1⟩
    unfold kEv
    rw [if_neg (by simp [hf] : ¬(s.final = true))]
    rw [if_neg (by simp [h0, h1] :
      ¬((!(availD n s.disp m0 && availD n s.disp m1)) = true))]
    cases hq : s.verdicts with
    | nil => exact absurd hq hqne
    | cons v1 vrest =>
      have hout : (simEv n s.ent m0 m1).isSome := by
        unfold simEv
        rcases Option.isSome_iff_exists.mp
          (simEvAux_isSome_of_occInc hc h0 h1) with ⟨out, houta⟩
        simp [houta]
      rcases Option.isSome_iff_exists.mp hout with ⟨dec, hdec⟩
      cases hdel : delta n s.next
          (placeJoint (execV n v1 s.disp) s.next m0 m1) dec with
      | mk D' M' => simp [hdec, hdel]

theorem availD_of_availK {k : Nat} {s : KState n} {m : goMv.M}
    (hm : (kGame n k).avail s m) :
    ∀ w i, m = some (w, i) → availD n s.disp (some i) = true := by
  intro w i hmi
  rcases hm.2 with h | ⟨w', i', hmi', hi', hocc'⟩
  · rw [hmi] at h; cases h
  · rw [hmi] at hmi'
    cases hmi'
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi', hocc']
    rfl

/-- def_simultaneous's properties for k-DSGo over reachable states,
    for every k ≥ 1. -/
theorem k_simOK (k : Nat) (hk : 1 ≤ k) : SimOK (kGame n k) := by
  have hqne : ∀ {s : KState n}, SimReach (kGame n k) s →
      s.verdicts ≠ [] := by
    intro s hr hcon
    have hInv := reach_invK hr
    have hvl := hInv.vlen
    rw [hcon, List.length_nil] at hvl
    omega
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
    have hInv := reach_invK hr
    have hfin : s.final = false := hav0.1
    have hpassD : availD n s.disp none = true := rfl
    unfold kGame
    simp only
    cases m0 with
    | none =>
      cases m1 with
      | none =>
        show (kEv n s none none).isSome
        exact (kEv_isSome_iff s hInv.entInc (hqne hr)
          none none).mpr ⟨hfin, hpassD, hpassD⟩
      | some p1 =>
        rcases hd1 with h | ⟨i, hi⟩
        · cases h
        · cases hi
          show (kEv n s none (some i)).isSome
          exact (kEv_isSome_iff s hInv.entInc (hqne hr)
            none (some i)).mpr
            ⟨hfin, hpassD, availD_of_availK hav1 true i rfl⟩
    | some p0 =>
      rcases hd0 with h | ⟨i0, hi0⟩
      · cases h
      · cases hi0
        cases m1 with
        | none =>
          show (kEv n s (some i0) none).isSome
          exact (kEv_isSome_iff s hInv.entInc (hqne hr)
            (some i0) none).mpr
            ⟨hfin, availD_of_availK hav0 false i0 rfl, hpassD⟩
        | some p1 =>
          rcases hd1 with h | ⟨i1, hi1⟩
          · cases h
          · cases hi1
            show (kEv n s (some i0) (some i1)).isSome
            exact (kEv_isSome_iff s hInv.entInc (hqne hr)
              (some i0) (some i1)).mpr
              ⟨hfin, availD_of_availK hav0 false i0 rfl,
               availD_of_availK hav1 true i1 rfl⟩
  · -- avail_of_pair
    intro s m0 m1 hr hp
    have hInv := reach_invK hr
    rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
    unfold kGame at hs'
    simp only at hs'
    cases hsl : slotMoves m0 m1 with
    | none => rw [hsl] at hs'; cases hs'
    | some p =>
      rw [hsl] at hs'
      have h2 : kEv n s p.1 p.2 = some s' := hs'
      have hev : (kEv n s p.1 p.2).isSome := by rw [h2]; rfl
      have hiff := (kEv_isSome_iff s hInv.entInc (hqne hr)
        p.1 p.2).mp hev
      have hfin := hiff.1
      have havOf : ∀ (m : goMv.M) (a : Option Nat),
          (∀ w i, m = some (w, i) → a = some i) →
          availD n s.disp a = true → (kGame n k).avail s m := by
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
    exact ⟨⟨emptyD n, 2, [emptyD n], List.replicate k emptyV, true⟩, rfl⟩

end SgoKInv
