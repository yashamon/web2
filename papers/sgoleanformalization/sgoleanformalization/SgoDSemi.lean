/- SgoDSemi.lean — the main theorem, milestone 3d: the semiclassical field
   for DSGo.

   Along commuting turns the entanglement is a singleton {x}, and the
   Δ postprocessing computes the composite exactly: the placed display
   agrees with x wherever both are occupied (pJ_kind + the composite's
   cell analysis bStep2_kind), x is occupancy-included, so one round
   removes precisely the placement debris (dead stones under x), and
   the next round is the fixpoint. Hence the DSGo display carries the
   composite's cells — no one-stage resolution lemma is needed: Δ IS
   the resolution at semiclassical states. -/
import SgoDNat
import SgoSemi

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoDInv SgoDOK SgoDNat

namespace SgoDSemi

variable {n : Nat}

/-! ### Small conversions -/

theorem kind_none_of_unocc {D : Display n} {i : Nat}
    (h : occD D i = false) : kindAt D i = none := by
  unfold occD at h
  unfold kindAt
  cases hg : D.get i with
  | none => rfl
  | some c => rw [hg] at h; cases h

theorem occ_of_availD {D : Display n} {i : Nat}
    (h : availD n D (some i) = true) : occD D i = false := by
  unfold availD at h
  have hsplit := Bool.and_eq_true (decide (i < n*n)) (!occD D i)
  rw [hsplit] at h
  have hb := h.2
  cases hoc : occD D i
  · rfl
  · rw [hoc] at hb; exact absurd hb (by simp)

/-! ### The Δ recursion on a singleton entanglement -/

theorem any_singleton {M : List (Display n)} {x : Display n}
    (hM : ∀ b, b ∈ M ↔ b = x) (p : Display n → Bool) :
    M.any p = p x := by
  cases hp : p x with
  | true => exact List.any_eq_true.mpr ⟨x, (hM x).mpr rfl, hp⟩
  | false =>
    cases hany : M.any p with
    | false => rfl
    | true =>
      rcases List.any_eq_true.mp hany with ⟨b, hb, hpb⟩
      rw [(hM b).mp hb, hp] at hpb
      cases hpb

theorem evSet_singleton {M : List (Display n)} {x : Display n}
    (hM : ∀ b, b ∈ M ↔ b = x) (i : Nat) :
    evSet n M i
      = (kindAt x i == some .b, kindAt x i == some .w) := by
  show ((M.any fun b => kindAt b i == some .b),
    (M.any fun b => kindAt b i == some .w)) = _
  simp only [any_singleton hM]

/-- A displayed stone whose color the singleton branch confirms is
    kept by the round, value intact. -/
theorem dR_keep_cell (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : i < n*n) {k : DKind} {st : Nat}
    (hg : D.get i = some (k, st)) (hkr : k ≠ DKind.r)
    (hev : evSet n M i = (k == DKind.b, k == DKind.w)) :
    (deltaRound n t M D).get i = some (k, st) := by
  have hread := dR_get_pair t M D hi hg hev
  cases k with
  | r => exact absurd rfl hkr
  | b =>
    rw [if_neg (by decide :
        ¬((!(DKind.b == DKind.b) && !(DKind.b == DKind.w)) = true)),
      if_neg (fun h => Bool.noConfusion h)] at hread
    exact hread
  | w =>
    rw [if_neg (by decide :
        ¬((!(DKind.w == DKind.b) && !(DKind.w == DKind.w)) = true)),
      if_neg (fun h => Bool.noConfusion h)] at hread
    exact hread

/-- One round on a singleton {x}: if every displayed stone is either
    confirmed by x or absent from x, and x stands on occupied cells,
    the round computes exactly x's cells. -/
theorem dR_singleton {t : Nat} {Dp x : Display n}
    {M : List (Display n)}
    (hM : ∀ b, b ∈ M ↔ b = x) (hDpc : IsClassical Dp)
    (hxw : WFD x)
    (hinc : occIncB n Dp x = true)
    (hagree : ∀ i, i < n*n → ∀ k st, Dp.get i = some (k, st) →
      kindAt x i = none ∨ kindAt x i = some k) :
    SameCells (deltaRound n t M Dp) x := by
  intro i
  by_cases hi : i < n*n
  case neg =>
    unfold kindAt
    rw [dR_get_oob t M Dp hi, get_oob x hxw i hi]
  case pos =>
    cases hg : Dp.get i with
    | none =>
      have hde : occD Dp i = false := by
        unfold occD
        rw [hg]
        rfl
      have hxe : occD x i = false := branch_empty_of_occInc hinc hi hde
      have hgx : kindAt x i = none := kind_none_of_unocc hxe
      have hkdr : kindAt (deltaRound n t M Dp) i = none := by
        unfold kindAt
        rw [dR_get_none t M Dp hi hg]
        rfl
      rw [hkdr, hgx]
    | some c =>
      obtain ⟨k, st⟩ := c
      have hkr : k ≠ DKind.r := by
        intro hkk
        apply hDpc i
        unfold kindAt
        rw [hg, hkk]
        rfl
      rcases hagree i hi k st hg with hnone | hsome
      · -- x empty there: the round removes the stone
        have hevv : evSet n M i = (false, false) := by
          rw [evSet_singleton hM i, hnone]
          rfl
        have hread := dR_get_pair t M Dp hi hg hevv
        rw [if_pos (by decide : ((!false && !false) = true))] at hread
        have hkdr : kindAt (deltaRound n t M Dp) i = none := by
          unfold kindAt
          rw [hread]
          rfl
        rw [hkdr, hnone]
      · -- x confirms the stone: kept
        have hevv : evSet n M i = ((k == DKind.b), (k == DKind.w)) := by
          rw [evSet_singleton hM i, hsome]
          rfl
        have hread := dR_keep_cell t M Dp hi hg hkr hevv
        have hkdr : kindAt (deltaRound n t M Dp) i = some k := by
          unfold kindAt
          rw [hread]
          rfl
        rw [hkdr, hsome]

/-- A display carrying exactly the cells of the classical singleton
    branch is a fixpoint of the round. -/
theorem dR_fix {t : Nat} {E x : Display n} {M : List (Display n)}
    (hM : ∀ b, b ∈ M ↔ b = x)
    (hEw : WFD E) (hsc : SameCells E x) (hxc : IsClassical x) :
    deltaRound n t M E = E := by
  apply display_ext
  apply Array.ext
  · exact (dR_wfd t M E).trans hEw.symm
  · intro i h1 h2
    have hin : i < n*n := by
      rw [← dR_wfd t M E]
      exact h1
    have hgD := get_in_bounds (deltaRound n t M E) i
      (by rw [dR_wfd t M E]; exact hin)
    have hgE := get_in_bounds E i (by rw [hEw]; exact hin)
    rw [← hgD, ← hgE]
    cases hg : E.get i with
    | none => rw [dR_get_none t M E hin hg]
    | some c =>
      obtain ⟨k, st⟩ := c
      have hkx : kindAt x i = some k := by
        rw [← hsc i]
        unfold kindAt
        rw [hg]
        rfl
      have hkr : k ≠ DKind.r := by
        intro hkk
        subst hkk
        exact hxc i hkx
      have hevv : evSet n M i = ((k == DKind.b), (k == DKind.w)) := by
        rw [evSet_singleton hM i, hkx]
        rfl
      rw [dR_keep_cell t M E hin hg hkr hevv]

/-- At a round fixpoint the recursion stops in one step, whatever the
    remaining fuel. -/
theorem deltaAux_fix (t : Nat) (fuel : Nat) (D : Display n)
    (M : List (Display n)) (hfx : deltaRound n t M D = D) :
    deltaAux n t (fuel+1) D M = (D, recut n D M) := by
  have hunf : deltaAux n t (fuel+1) D M
      = if (deltaRound n t M D == D) = true
        then (deltaRound n t M D, recut n (deltaRound n t M D) M)
        else deltaAux n t fuel (deltaRound n t M D)
          (recut n (deltaRound n t M D) M) := rfl
  rw [hunf, hfx, if_pos (display_beq_self D)]

/-- The Δ output on a singleton {x} under the agreement hypotheses:
    the display becomes exactly x's cells, and the entanglement stays
    the singleton. -/
theorem delta_singleton {t : Nat} {Dp x : Display n}
    {M : List (Display n)}
    (hM : ∀ b, b ∈ M ↔ b = x) (hDpc : IsClassical Dp)
    (hxw : WFD x) (hxc : IsClassical x)
    (hinc : occIncB n Dp x = true)
    (hagree : ∀ i, i < n*n → ∀ k st, Dp.get i = some (k, st) →
      kindAt x i = none ∨ kindAt x i = some k) :
    SameCells (delta n t Dp M).1 x
    ∧ (∀ b, b ∈ (delta n t Dp M).2 ↔ b = x) := by
  have hD1 : SameCells (deltaRound n t M Dp) x :=
    dR_singleton hM hDpc hxw hinc hagree
  have hincx : occIncB n (deltaRound n t M Dp) x = true := by
    unfold occIncB
    rw [List.all_eq_true]
    intro j hj
    cases hocc : occD x j with
    | false =>
      apply bool_or_right
      apply beq_iff_eq.mpr
      exact kind_none_of_unocc hocc
    | true =>
      apply bool_or_left
      rw [occ_eq_of_samecells hD1 j]
      exact hocc
  have hrec : ∀ (M' : List (Display n)), (∀ b, b ∈ M' ↔ b = x) →
      ∀ b, b ∈ recut n (deltaRound n t M Dp) M' ↔ b = x := by
    intro M' hM' b
    rw [recut_mem]
    constructor
    · intro hb
      exact (hM' b).mp hb.1
    · intro hb
      subst hb
      exact ⟨(hM' b).mpr rfl, hincx⟩
  have hunf1 : deltaAux n t (2*(n*n)+2) Dp M
      = if (deltaRound n t M Dp == Dp) = true
        then (deltaRound n t M Dp, recut n (deltaRound n t M Dp) M)
        else deltaAux n t (2*(n*n)+1) (deltaRound n t M Dp)
          (recut n (deltaRound n t M Dp) M) := rfl
  by_cases htest : (deltaRound n t M Dp == Dp) = true
  · have heq : deltaRound n t M Dp = Dp := display_eq_of_beq htest
    have hout : delta n t Dp M = (Dp, recut n Dp M) :=
      deltaAux_fix t (2*(n*n)+1) Dp M heq
    rw [hout]
    exact ⟨heq ▸ hD1, heq ▸ hrec M hM⟩
  · have h1 : delta n t Dp M
        = deltaAux n t (2*(n*n)+1) (deltaRound n t M Dp)
          (recut n (deltaRound n t M Dp) M) := by
      show deltaAux n t (2*(n*n)+2) Dp M = _
      rw [hunf1, if_neg htest]
    have hM1 : ∀ b, b ∈ recut n (deltaRound n t M Dp) M ↔ b = x :=
      hrec M hM
    have hfix2 : deltaRound n t (recut n (deltaRound n t M Dp) M)
        (deltaRound n t M Dp) = deltaRound n t M Dp :=
      dR_fix hM1 (dR_wfd t M Dp) hD1 hxc
    have hout : delta n t Dp M
        = (deltaRound n t M Dp,
           recut n (deltaRound n t M Dp)
             (recut n (deltaRound n t M Dp) M)) := by
      rw [h1]
      exact deltaAux_fix t (2*(n*n)) _ _ hfix2
    rw [hout]
    exact ⟨hD1, hrec _ hM1⟩

/-! ### Classicality of the placement -/

theorem classical_set {D : Display n} (hD : IsClassical D) {c : DKind}
    (hc : c ≠ DKind.r) (i st : Nat) :
    IsClassical (D.set i (some (c, st))) := by
  intro j
  by_cases hji : j = i
  · subst hji
    by_cases hjb : j < D.cells.size
    · intro h
      apply hc
      unfold kindAt at h
      rw [get_set_self D j _ hjb] at h
      exact Option.some.inj h
    · intro h
      apply hD j
      have hgg : (D.set j (some (c, st))).get j = D.get j := by
        unfold Display.set Display.get Array.setD Array.setIfInBounds
        rw [dif_neg hjb]
      unfold kindAt at h ⊢
      rw [hgg] at h
      exact h
  · intro h
    apply hD j
    unfold kindAt at h ⊢
    rw [get_set_ne D i j _ hji] at h
    exact h

theorem pJ_classical {D : Display n} (hD : IsClassical D)
    {m0 m1 : Option Nat}
    (hne : ∀ i0 i1, m0 = some i0 → m1 = some i1 → i0 ≠ i1) (t : Nat) :
    IsClassical (placeJoint D t m0 m1) := by
  cases m0 with
  | none =>
    cases m1 with
    | none => exact hD
    | some p1 =>
      exact classical_set hD (by intro h; cases h) p1 t
  | some p0 =>
    cases m1 with
    | none =>
      exact classical_set hD (by intro h; cases h) p0 t
    | some p1 =>
      have hne' : p0 ≠ p1 := hne p0 p1 rfl rfl
      have hpj : placeJoint D t (some p0) (some p1)
          = (D.set p0 (some (DKind.b, t))).set p1 (some (DKind.w, t)) := by
        simp only [placeJoint]
        rw [if_neg (show ¬((p0 == p1) = true) from
          fun h => hne' (beq_iff_eq.mp h))]
      rw [hpj]
      exact classical_set (classical_set hD (by intro h; cases h) p0 t)
        (by intro h; cases h) p1 t

/-- Reading a placed display cell: black's target, white's target, or
    an untouched cell. -/
theorem pJ_kind (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    (hne : ∀ i0 i1, m0 = some i0 → m1 = some i1 → i0 ≠ i1)
    (hwf : WFD D) (h0 : ∀ i, m0 = some i → i < n*n)
    (h1 : ∀ i, m1 = some i → i < n*n) (p : Nat) :
    (m0 = some p ∧ kindAt (placeJoint D t m0 m1) p = some DKind.b)
    ∨ (m1 = some p ∧ kindAt (placeJoint D t m0 m1) p = some DKind.w)
    ∨ (m0 ≠ some p ∧ m1 ≠ some p
        ∧ kindAt (placeJoint D t m0 m1) p = kindAt D p) := by
  cases m0 with
  | none =>
    cases m1 with
    | none =>
      exact Or.inr (Or.inr ⟨fun h => Option.noConfusion h,
        fun h => Option.noConfusion h, rfl⟩)
    | some p1 =>
      by_cases hp : p = p1
      · subst hp
        refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rw [placeJoint_right]
        exact pT_kind_self D t .w p hwf (h1 p rfl)
      · refine Or.inr (Or.inr ⟨fun h => Option.noConfusion h, ?_, ?_⟩)
        · intro h
          exact hp ((Option.some.inj h).symm)
        · rw [placeJoint_right]
          exact pT_kind_ne D t .w p1 p hp
  | some p0 =>
    cases m1 with
    | none =>
      by_cases hp : p = p0
      · subst hp
        refine Or.inl ⟨rfl, ?_⟩
        rw [placeJoint_left]
        exact pT_kind_self D t .b p hwf (h0 p rfl)
      · refine Or.inr (Or.inr ⟨?_, fun h => Option.noConfusion h, ?_⟩)
        · intro h
          exact hp ((Option.some.inj h).symm)
        · rw [placeJoint_left]
          exact pT_kind_ne D t .b p0 p hp
    | some p1 =>
      have hne' : p0 ≠ p1 := hne p0 p1 rfl rfl
      have hpj : placeJoint D t (some p0) (some p1)
          = placedT (placedT D t .b p0) t .w p1 := by
        simp only [placeJoint]
        rw [if_neg (show ¬((p0 == p1) = true) from
          fun h => hne' (beq_iff_eq.mp h))]
        rfl
      have hw1 : WFD (placedT D t .b p0) := by
        unfold WFD placedT
        rw [set_size]
        exact hwf
      by_cases hp0 : p = p0
      · subst hp0
        refine Or.inl ⟨rfl, ?_⟩
        rw [hpj, pT_kind_ne _ t .w p1 p hne']
        exact pT_kind_self D t .b p hwf (h0 p rfl)
      · by_cases hp1 : p = p1
        · subst hp1
          refine Or.inr (Or.inl ⟨rfl, ?_⟩)
          rw [hpj]
          exact pT_kind_self _ t .w p hw1 (h1 p rfl)
        · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
          · intro h
            exact hp0 ((Option.some.inj h).symm)
          · intro h
            exact hp1 ((Option.some.inj h).symm)
          · rw [hpj, pT_kind_ne _ t .w p1 p hp1,
              pT_kind_ne D t .b p0 p hp0]

/-! ### The composite's cells -/

theorem bStep_wfd {b : Display n} (hbw : WFD b) {c : DKind}
    {mo : Option Nat} {r : Display n}
    (hr : bStep n b c mo = some r) : WFD r := by
  cases mo with
  | none => cases hr; exact hbw
  | some i => exact goMoveN_size b c i r hr

theorem bStep_legal {b : Display n} (hbw : WFD b) (hbc : IsClassical b)
    (hbl : IsLegal b) {c : DKind} (hc : c ≠ DKind.r) {mo : Option Nat}
    (hbnd : ∀ i, mo = some i → i < n*n) {r : Display n}
    (hr : bStep n b c mo = some r) : IsLegal r := by
  cases mo with
  | none => cases hr; exact hbl
  | some i => exact goMoveN_legal b c i r hbw (hbnd i rfl) hc hbc hbl hr

/-- A branch move changes a cell only to erase it or to place its own
    color at its own target. -/
theorem bStep_kind {b : Display n} (hbw : WFD b) {c : DKind}
    {mo : Option Nat} {r : Display n}
    (hr : bStep n b c mo = some r) (p : Nat) :
    kindAt r p = none ∨ kindAt r p = kindAt b p
    ∨ (mo = some p ∧ kindAt r p = some c) := by
  cases mo with
  | none =>
    cases hr
    exact Or.inr (Or.inl rfl)
  | some i =>
    rcases goMoveN_get b c i r hr p with h | h
    · refine Or.inl ?_
      unfold kindAt
      rw [h]
      rfl
    · by_cases hpi : p = i
      · subst hpi
        by_cases hib : p < n*n
        · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          have hpl : kindAt (placedN n b c p) p = some c :=
            kindAt_placedN_self b c p hbw hib
          unfold kindAt at hpl ⊢
          rw [h]
          exact hpl
        · refine Or.inr (Or.inl ?_)
          have hpl : (placedN n b c p).get p = b.get p := by
            unfold placedN Display.set Display.get Array.setD
              Array.setIfInBounds
            rw [dif_neg (by rw [hbw]; exact hib)]
          unfold kindAt
          rw [h, hpl]
      · refine Or.inr (Or.inl ?_)
        have hpl : (placedN n b c i).get p = b.get p := by
          unfold placedN
          exact get_set_ne b i p _ hpi
        unfold kindAt
        rw [h, hpl]

theorem bStep2_kind {b : Display n} (hbw : WFD b) {c0 c1 : DKind}
    {m0 m1 : Option Nat} {x : Display n}
    (hx : bStep2 n b c0 c1 m0 m1 = some x) (p : Nat) :
    kindAt x p = none ∨ kindAt x p = kindAt b p
    ∨ (m0 = some p ∧ kindAt x p = some c0)
    ∨ (m1 = some p ∧ kindAt x p = some c1) := by
  unfold bStep2 at hx
  cases h1 : bStep n b c0 m0 with
  | none => rw [h1] at hx; cases hx
  | some r1 =>
    rw [h1] at hx
    have hx2 : bStep n r1 c1 m1 = some x := hx
    have hr1w : WFD r1 := bStep_wfd hbw h1
    rcases bStep_kind hr1w hx2 p with h | h | ⟨hm, hk⟩
    · exact Or.inl h
    · rcases bStep_kind hbw h1 p with g | g | ⟨gm, gk⟩
      · exact Or.inl (h.trans g)
      · exact Or.inr (Or.inl (h.trans g))
      · exact Or.inr (Or.inr (Or.inl ⟨gm, h.trans gk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hm, hk⟩))

/-- Branch invariants through both composite moves. -/
theorem bStep2_pres {b : Display n} (hbw : WFD b) (hbc : IsClassical b)
    (hbz : StampsZero b) (hbl : IsLegal b) {c0 c1 : DKind}
    (hc0 : c0 ≠ DKind.r) (hc1 : c1 ≠ DKind.r) {m0 m1 : Option Nat}
    (hbnd0 : ∀ i, m0 = some i → i < n*n)
    (hbnd1 : ∀ i, m1 = some i → i < n*n) {x : Display n}
    (hx : bStep2 n b c0 c1 m0 m1 = some x) :
    WFD x ∧ IsClassical x ∧ StampsZero x ∧ IsLegal x := by
  unfold bStep2 at hx
  cases h1 : bStep n b c0 m0 with
  | none => rw [h1] at hx; cases hx
  | some r1 =>
    rw [h1] at hx
    have hx2 : bStep n r1 c1 m1 = some x := hx
    have hw1 : WFD r1 := bStep_wfd hbw h1
    have hp1 : IsClassical r1 ∧ StampsZero r1 := by
      cases m0 with
      | none => cases h1; exact ⟨hbc, hbz⟩
      | some i => exact goMoveN_preserves b c0 hc0 i r1 h1 ⟨hbc, hbz⟩
    have hl1 : IsLegal r1 := bStep_legal hbw hbc hbl hc0 hbnd0 h1
    have hp2 : IsClassical x ∧ StampsZero x := by
      cases m1 with
      | none => cases hx2; exact hp1
      | some i => exact goMoveN_preserves r1 c1 hc1 i x hx2 hp1
    exact ⟨bStep_wfd hw1 hx2, hp2.1, hp2.2,
      bStep_legal hw1 hp1.1 hl1 hc1 hbnd1 hx2⟩

/-! ### The semiclassical tracking -/

/-- A semiclassical state is reachable. -/
theorem semiC_reach {Mv : Moves} {G0 : SeqGame Mv} {G1 : SimulGame Mv}
    {s : G1.B} {a : G0.S} (h : SemiC G0 G1 s a) : SimReach G1 s := by
  induction h with
  | init => exact SimReach.init
  | step hsc hcomm hpair ih => exact SimReach.step ih hpair

/-- The tracked shape of a semiclassical DSGo state. -/
structure DTrack (s : SGoState n) (a : (goGame n).S) : Prop where
  reach : SimReach (dsgoGame n) s
  track : ∃ d, ((s.final = false ∧ a = PState.live d false false)
        ∨ (s.final = true ∧ a = PState.done d false))
      ∧ (∀ e, e ∈ s.ent ↔ e = d)
      ∧ SameCells s.disp d ∧ IsLegal d

/-- The semiclassical tracking, by induction on the recursion: the Δ
    postprocessing IS the resolution — the display converges to the
    composite's cells in at most two rounds. -/
theorem dsemiC_track (hn : 2 ≤ n) {s : SGoState n} {a : (goGame n).S}
    (h : SemiC (goGame n) (dsgoGame n) s a) : DTrack s a := by
  induction h with
  | init =>
    refine ⟨SimReach.init, emptyD n, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro e
      constructor
      · intro he
        have he' : e ∈ ([emptyD n] : List (Display n)) := he
        exact List.mem_singleton.mp he'
      · intro he
        rw [he]
        exact List.mem_cons_self _ _
    · intro z
      rfl
    · intro p hp
      unfold occD at hp
      rw [emptyD_get p] at hp
      cases hp
  | @step s a s' ma mb hsc hcomm hpair ih =>
    obtain ⟨d, hshape, hmemb, hdisp, hlegal⟩ := ih.track
    have hreach' : SimReach (dsgoGame n) s' := SimReach.step ih.reach hpair
    have hInv := reach_invD ih.reach
    have hd : d ∈ s.ent := (hmemb d).mpr rfl
    have hdw : WFD d := hInv.entWfd d hd
    have hdc : IsClassical d := hInv.entClassical d hd
    have hdz : StampsZero d := hInv.entZero d hd
    unfold dsgoGame at hpair
    simp only at hpair
    cases hsl : slotMoves ma mb with
    | none => rw [hsl] at hpair; cases hpair
    | some p =>
      rw [hsl] at hpair
      obtain ⟨m0, m1⟩ := p
      rcases dsgoEv_cases hpair with ⟨hfin, hav0, hav1, dec, hse, hs'⟩
      have ha : a = PState.live d false false := by
        rcases hshape with ⟨-, ha⟩ | ⟨hf, -⟩
        · exact ha
        · rw [hfin] at hf; cases hf
      subst ha
      have hb0 := bounds_of_availD hav0
      have hb1 := bounds_of_availD hav1
      rcases commute_comp hsl hb0 hb1 hcomm with ⟨x, hx, hy, hassoc⟩
      -- the targets are distinct: no collision on a legal classical
      -- board carries both composites
      have hne' : ∀ i0 i1, m0 = some i0 → m1 = some i1 → i0 ≠ i1 := by
        intro i0 i1 h0' h1' he
        subst he
        subst h0'
        subst h1'
        have hbs1 : Option.bind (goMoveN n d .b i0)
            (fun e => goMoveN n e .w i0) = some x := hx
        have hbs2 : Option.bind (goMoveN n d .w i0)
            (fun e => goMoveN n e .b i0) = some x := hy
        exact step0_same_intersection hn d i0 hdw (hb0 i0 rfl)
          hdc hlegal x x hbs1 hbs2
      have hxmem : x ∈ dedupD n [x, x] :=
        (mem_dedupD_iff _ _).mpr (List.mem_cons_self x [x])
      have hserial : serialP n d m0 m1 = some (dedupD n [x, x]) := by
        unfold serialP
        rw [hx, hy]
      have hpres := bStep2_pres hdw hdc hdz hlegal
        (by intro h; cases h) (by intro h; cases h) hb0 hb1 hx
      -- the decoherence is the singleton {x}
      have hdecx : ∀ e, e ∈ dec ↔ e = x := by
        intro e
        constructor
        · intro he
          rcases simEv_mem hse he with ⟨b, hb, l, hl, hel⟩
          have hbd : b = d := (hmemb b).mp hb
          subst hbd
          rw [hserial] at hl
          cases hl
          rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hel) with h | h
          · exact h
          · exact List.mem_singleton.mp h
        · intro he
          subst he
          have hout : ∃ out, simEvAux n m0 m1 s.ent = some out
              ∧ dec = dedupD n out := by
            unfold simEv at hse
            cases haux : simEvAux n m0 m1 s.ent with
            | none => rw [haux] at hse; cases hse
            | some out =>
              rw [haux] at hse
              exact ⟨out, rfl, (Option.some.inj hse).symm⟩
          rcases hout with ⟨out, haux, hdec⟩
          rw [hdec]
          exact (mem_dedupD_iff _ _).mpr
            (simEvAux_mem_of haux hd hserial hxmem)
      -- classicality of the display and the placement
      have hdispc : IsClassical s.disp := by
        intro i hri
        exact hdc i ((hdisp i).symm.trans hri)
      have hDpc : IsClassical (placeJoint s.disp s.next m0 m1) :=
        pJ_classical hdispc hne' s.next
      -- the composite is occupancy-included in the placement
      obtain ⟨-, -, hdinc⟩ := invD_delta hInv hav0 hav1 hse
      have hincx : occIncB n (placeJoint s.disp s.next m0 m1) x = true :=
        hdinc x ((hdecx x).mpr rfl)
      -- the placement agrees with the composite wherever occupied
      have hagree : ∀ i, i < n*n → ∀ k st,
          (placeJoint s.disp s.next m0 m1).get i = some (k, st) →
          kindAt x i = none ∨ kindAt x i = some k := by
        intro i hi k st hg
        have hk : kindAt (placeJoint s.disp s.next m0 m1) i = some k := by
          unfold kindAt
          rw [hg]
          rfl
        rcases pJ_kind s.disp s.next m0 m1 hne' hInv.wfdD hb0 hb1 i with
          ⟨hm, hkb⟩ | ⟨hm, hkw⟩ | ⟨hm0', hm1', hkeq⟩
        · -- black's target
          have hkk : k = DKind.b := Option.some.inj (hk.symm.trans hkb)
          subst hkk
          have hdi : kindAt d i = none := by
            apply kind_none_of_unocc
            rw [← occ_eq_of_samecells hdisp i]
            apply occ_of_availD
            rw [← hm]
            exact hav0
          rcases bStep2_kind hdw hx i with h | h | ⟨-, h⟩ | ⟨hm1x, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hdi)
          · exact Or.inr h
          · exact absurd rfl (hne' i i hm hm1x)
        · -- white's target
          have hkk : k = DKind.w := Option.some.inj (hk.symm.trans hkw)
          subst hkk
          have hdi : kindAt d i = none := by
            apply kind_none_of_unocc
            rw [← occ_eq_of_samecells hdisp i]
            apply occ_of_availD
            rw [← hm]
            exact hav1
          rcases bStep2_kind hdw hx i with h | h | ⟨hm0x, h⟩ | ⟨-, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hdi)
          · exact absurd rfl (hne' i i hm0x hm)
          · exact Or.inr h
        · -- an untouched cell
          have hdk : kindAt d i = some k :=
            (hdisp i).symm.trans (hkeq.symm.trans hk)
          rcases bStep2_kind hdw hx i with h | h | ⟨hm, -⟩ | ⟨hm, -⟩
          · exact Or.inl h
          · exact Or.inr (h.trans hdk)
          · exact absurd hm hm0'
          · exact absurd hm hm1'
      -- the Δ computes the composite
      have hdelta := delta_singleton (t := s.next) hdecx hDpc hpres.1
        hpres.2.1 hincx hagree
      subst hs'
      by_cases hnn : m0 = none ∧ m1 = none
      · -- the double pass: the composite is the branch, riding to
        -- its final
        obtain ⟨h00, h11⟩ := hnn
        subst h00
        subst h11
        refine ⟨hreach', x, Or.inr ⟨rfl, ?_⟩, hdelta.2, hdelta.1,
          hpres.2.2.2⟩
        rw [hassoc]
        rfl
      · -- a move turn
        have hflag : (m0.isNone && m1.isNone) = false := by
          cases hm0 : m0 with
          | some i0 => rfl
          | none =>
            cases hm1 : m1 with
            | some i1 => rfl
            | none => exact absurd ⟨hm0, hm1⟩ hnn
        refine ⟨hreach', x, Or.inl ⟨hflag, ?_⟩, hdelta.2, hdelta.1,
          hpres.2.2.2⟩
        rw [hassoc]
        exact repP_live hnn x

/-- The semiclassical field: along the recursion the branch set is
    the singleton of the associated state. -/
theorem dsgo_semiclassical (hn : 2 ≤ n) {s : SGoState n}
    {a : (goGame n).S} (h : SemiC (goGame n) (dsgoGame n) s a) :
    BSet.eqv (rhoD n s) (BSet.single a) := by
  obtain ⟨d, hshape, hmemb, -, -⟩ := (dsemiC_track hn h).track
  intro z
  constructor
  · rintro ⟨e, he, hze⟩
    have hed : e = d := (hmemb e).mp he
    subst hed
    rcases hshape with ⟨hf, ha⟩ | ⟨hf, ha⟩
    · rw [hf] at hze
      simp only [Bool.false_eq_true, if_false] at hze
      rw [ha]
      exact hze
    · rw [hf] at hze
      simp only [if_true] at hze
      rw [ha]
      exact hze
  · intro hz
    refine ⟨d, (hmemb d).mpr rfl, ?_⟩
    rcases hshape with ⟨hf, ha⟩ | ⟨hf, ha⟩
    · rw [hf]
      simp only [Bool.false_eq_true, if_false]
      rw [hz, ha]
    · rw [hf]
      simp only [if_true]
      rw [hz, ha]

/-- def_symmetrization, conditions 3 and 4: DSGo is a simultaneization
    of Go under the branch semantics. -/
theorem dsgo_isSimultaneization (hn : 2 ≤ n) :
    IsSimultaneization (goGame n) (dsgoGame n) (rhoD n) where
  rho_init := dsgo_rho_init
  nat_defined := fun hr hp => dsgo_nat_defined hr hp
  nat_incl := fun hr hst => dsgo_nat_incl hr hst
  semiclassical := fun h => dsgo_semiclassical hn h

end SgoDSemi
