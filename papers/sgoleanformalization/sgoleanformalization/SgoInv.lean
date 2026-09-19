/- SgoInv.lean — the main theorem, milestone 2a: the SGo reachability
   invariant, and the display-read definedness of sgoEv.

   The invariant Inv: the display is well formed with stamps below the
   next turn, and every branch of the entanglement is well formed,
   classical, stamp-zero, and compatible with the display. It holds at
   the initial state and is preserved by sgoEv.

   The payoff closes the M1 caveat: under Inv, sgoEv is defined
   exactly when the state is not final and both moves are
   display-available (sgoEv_isSome_iff) — the paper's availability.
   The key direction: a display-empty intersection is empty in every
   compatible branch, so each branch's P is defined
   (serialP_isSome_of_avail). -/
import Step8
import SgoSerial

open SgoGo SgoDisplay SgoSerial

namespace SgoInv

variable {n : Nat}

/-! ### Basic display facts -/

theorem emptyD_get (i : Nat) : (emptyD n).get i = none := by
  unfold emptyD Display.get Array.getD
  by_cases h : i < (Array.mkArray (n*n) (none : Cell)).size
  · simp only [h, dite_true]
    simp [Array.getElem_mkArray]
  · simp [h]

theorem emptyD_wfd : WFD (emptyD n) := by
  unfold emptyD WFD
  simp

theorem occD_false_iff (D : Display n) (i : Nat) :
    occD D i = false ↔ D.get i = none := by
  unfold occD
  cases h : D.get i <;> simp [h, Option.isSome]

theorem kindAt_none_of_empty (D : Display n) (i : Nat)
    (h : occD D i = false) : kindAt D i = none := by
  unfold kindAt
  rw [(occD_false_iff D i).mp h]
  rfl

theorem stampAt_none (D : Display n) (i : Nat) (h : D.get i = none) :
    stampAt D i = 0 := by
  unfold stampAt
  rw [h]
  rfl

theorem get_set_oob (D : Display n) (i : Nat) (c : Cell)
    (h : ¬ i < D.cells.size) (p : Nat) : (D.set i c).get p = D.get p := by
  unfold Display.set Display.get
  congr 1
  simp [Array.setD, Array.setIfInBounds, h]

/-! ### Size and stamp preservation through the display resolution -/

theorem placeJoint_wfd (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    (hw : WFD D) : WFD (placeJoint D t m0 m1) := by
  unfold WFD
  cases m0 with
  | none =>
    cases m1 with
    | none => simp only [placeJoint]; exact hw
    | some p1 => simp only [placeJoint]; rw [set_size]; exact hw
  | some p0 =>
    cases m1 with
    | none => simp only [placeJoint]; rw [set_size]; exact hw
    | some p1 =>
      simp only [placeJoint]
      by_cases h : p0 = p1
      · rw [if_pos (by simp [h] : (p0 == p1) = true), set_size]; exact hw
      · rw [if_neg (by simp [h] : ¬((p0 == p1) = true)),
          set_size, set_size]
        exact hw

theorem set_stampsBelow (D : Display n) (i : Nat) (k : DKind) (t u : Nat)
    (hu : t < u) (hD : StampsBelow D u) :
    StampsBelow (D.set i (some (k, t))) u := by
  intro p
  by_cases hp : p = i
  · subst hp
    by_cases hlt : p < D.cells.size
    · have := get_set_self D p (some (k, t)) hlt
      unfold stampAt
      rw [this]
      exact hu
    · unfold stampAt
      rw [get_set_oob D p _ hlt p]
      exact hD p
  · have := get_set_ne D i p (some (k, t)) hp
    unfold stampAt
    rw [this]
    exact hD p

theorem placeJoint_stampsBelow (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    (hD : StampsBelow D t) : StampsBelow (placeJoint D t m0 m1) (t+1) := by
  have hD' : StampsBelow D (t+1) := fun p => Nat.lt_succ_of_lt (hD p)
  have hlt : t < t + 1 := Nat.lt_succ_self t
  cases m0 with
  | none =>
    cases m1 with
    | none => simp only [placeJoint]; exact hD'
    | some p1 =>
      simp only [placeJoint]
      exact set_stampsBelow D p1 .w t (t+1) hlt hD'
  | some p0 =>
    cases m1 with
    | none =>
      simp only [placeJoint]
      exact set_stampsBelow D p0 .b t (t+1) hlt hD'
    | some p1 =>
      simp only [placeJoint]
      by_cases h : p0 = p1
      · rw [if_pos (by simp [h] : (p0 == p1) = true)]
        exact set_stampsBelow D p0 .r t (t+1) hlt hD'
      · rw [if_neg (by simp [h] : ¬((p0 == p1) = true))]
        exact set_stampsBelow _ p1 .w t (t+1) hlt
          (set_stampsBelow D p0 .b t (t+1) hlt hD')

theorem stampAt_map_range (m : Nat) (f : Nat → Cell) (p : Nat) :
    stampAt (⟨(Array.range m).map f⟩ : Display n) p
      = if p < m then ((f p).map (·.2)).getD 0 else 0 := by
  unfold stampAt
  rw [get_map_range]
  by_cases hp : p < m <;> simp [hp]

theorem basicCap_stampAt (D : Display n) (t : Nat) (p : Nat) :
    stampAt (basicCap D t) p = 0 ∨ stampAt (basicCap D t) p = stampAt D p := by
  simp only [basicCap]
  rw [stampAt_map_range]
  by_cases hp : p < n*n
  · simp only [hp, if_true]
    split
    · left; rfl
    · split
      · right
        unfold stampAt
        cases hc : D.get p <;> simp [hc]
      · split
        · right
          unfold stampAt
          cases hc : D.get p <;> simp [hc]
        · right; rfl
  · rw [if_neg hp]
    exact Or.inl rfl

theorem basicCap_stampsBelow (D : Display n) (t u : Nat) (hu : 1 ≤ u)
    (hD : StampsBelow D u) : StampsBelow (basicCap D t) u := by
  intro p
  rcases basicCap_stampAt D t p with h | h
  · rw [h]; exact hu
  · rw [h]; exact hD p

theorem capFix_wfd (fuel : Nat) (D : Display n) (t : Nat) (hw : WFD D) :
    WFD (capFix fuel D t) := by
  induction fuel generalizing D with
  | zero => exact hw
  | succ f ih =>
    simp only [capFix]
    split
    · exact hw
    · exact ih (basicCap D t) (basicCap_size D t)

theorem capFix_stampsBelow (fuel : Nat) (D : Display n) (t u : Nat)
    (hu : 1 ≤ u) (hD : StampsBelow D u) : StampsBelow (capFix fuel D t) u := by
  induction fuel generalizing D with
  | zero => exact hD
  | succ f ih =>
    simp only [capFix]
    split
    · exact hD
    · exact ih (basicCap D t) (basicCap_stampsBelow D t u hu hD)

theorem stages_wfd (fuel : Nat) (D : Display n) (t : Nat) (hw : WFD D) :
    WFD (stages fuel D t) := by
  induction fuel generalizing D t with
  | zero => exact hw
  | succ f ih =>
    simp only [stages]
    split
    · exact hw
    · split
      · exact hw
      · exact ih _ _ (capFix_wfd (n*n+1) D t hw)

theorem stages_stampsBelow (fuel : Nat) (D : Display n) (t u : Nat)
    (hu : 1 ≤ u) (hD : StampsBelow D u) : StampsBelow (stages fuel D t) u := by
  induction fuel generalizing D t with
  | zero => exact hD
  | succ f ih =>
    simp only [stages]
    split
    · exact hD
    · split
      · exact hD
      · exact ih _ _ (capFix_stampsBelow (n*n+1) D t u hu hD)

theorem resolveTurn_wfd (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    (hw : WFD D) : WFD (resolveTurn D t m0 m1) :=
  stages_wfd _ _ _ (placeJoint_wfd D t m0 m1 hw)

theorem resolveTurn_stampsBelow (D : Display n) (t : Nat) (m0 m1 : Option Nat)
    (hD : StampsBelow D t) : StampsBelow (resolveTurn D t m0 m1) (t+1) :=
  stages_stampsBelow _ _ _ _ (Nat.succ_le_succ (Nat.zero_le t))
    (placeJoint_stampsBelow D t m0 m1 hD)

/-! ### Branch preservation: a generic combinator over serialP -/

/-- Branch stamps are all zero. -/
def StampsZero (b : Display n) : Prop := ∀ i, stampAt b i = 0

theorem mem_dedupD (l : List (Display n)) (x : Display n)
    (hx : x ∈ dedupD n l) : x ∈ l := by
  induction l with
  | nil => exact absurd hx (by simp [dedupD])
  | cons a as ih =>
    simp only [dedupD] at hx
    split at hx
    · exact List.mem_cons_of_mem a (ih hx)
    · rcases List.mem_cons.mp hx with h | h
      · exact h ▸ List.mem_cons_self a as
      · exact List.mem_cons_of_mem a (ih h)

/-- Any property preserved by non-q goMoveN steps holds at every
    element of a serialP output. -/
theorem serialP_out {P : Display n → Prop}
    (hstep : ∀ (d : Display n) (c : DKind), c ≠ .r → ∀ i r,
      P d → goMoveN n d c i = some r → P r)
    {b : Display n} (hb : P b) {m0 m1 : Option Nat}
    {l : List (Display n)} (hl : serialP n b m0 m1 = some l) :
    ∀ x, x ∈ l → P x := by
  have hbStep : ∀ (d : Display n) (c : DKind), c ≠ .r → ∀ mo r,
      P d → bStep n d c mo = some r → P r := by
    intro d c hc mo r hd hr
    cases mo with
    | none => cases hr; exact hd
    | some i => exact hstep d c hc i r hd hr
  have hb2 : ∀ (c0 c1 : DKind), c0 ≠ .r → c1 ≠ .r → ∀ x0 x1 r,
      bStep2 n b c0 c1 x0 x1 = some r → P r := by
    intro c0 c1 h0 h1 x0 x1 r hr
    unfold bStep2 at hr
    cases hs : bStep n b c0 x0 with
    | none => rw [hs] at hr; cases hr
    | some d1 =>
      rw [hs] at hr
      exact hbStep d1 c1 h1 x1 r (hbStep b c0 h0 x0 d1 hb hs) hr
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
      · exact h ▸ hb2 .b .w hbw hww m0 m1 a01 h01
      · have hxa : x = a10 := by simpa using h
        exact hxa ▸ hb2 .w .b hww hbw m1 m0 a10 h10
    | none =>
      cases hy : bStep n b .w m1 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
        · exact h ▸ hb2 .b .w hbw hww m0 m1 a01 h01
        · have hxa : x = y := by simpa using h
          exact hxa ▸ hbStep b .w hww m1 y hb hy
  | none =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a10 =>
      cases hy : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hy])
      | some y =>
        simp only [serialP, h01, h10, hy] at hl
        cases hl
        rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
        · exact h ▸ hbStep b .b hbw m0 y hb hy
        · have hxa : x = a10 := by simpa using h
          exact hxa ▸ hb2 .w .b hww hbw m1 m0 a10 h10
    | none =>
      cases hx0 : bStep n b .b m0 with
      | none => exact absurd hl (by simp [serialP, h01, h10, hx0])
      | some x0 =>
        cases hx1 : bStep n b .w m1 with
        | none => exact absurd hl (by simp [serialP, h01, h10, hx0, hx1])
        | some x1 =>
          simp only [serialP, h01, h10, hx0, hx1] at hl
          cases hl
          rcases List.mem_cons.mp (mem_dedupD _ _ hx) with h | h
          · exact h ▸ hbStep b .b hbw m0 x0 hb hx0
          · have hxa : x = x1 := by simpa using h
            exact hxa ▸ hbStep b .w hww m1 x1 hb hx1

/-- goMoveN preserves classicality and stamp-zero (non-q moves). -/
theorem goMoveN_preserves (d : Display n) (c : DKind) (hc : c ≠ .r)
    (i : Nat) (r : Display n) (hr : goMoveN n d c i = some r)
    (h : IsClassical d ∧ StampsZero d) :
    IsClassical r ∧ StampsZero r := by
  have hget := goMoveN_get d c i r hr
  constructor
  · intro p
    rcases hget p with hp | hp
    · unfold kindAt; rw [hp]; simp
    · unfold kindAt
      rw [hp]
      unfold placedN
      by_cases hpi : p = i
      · subst hpi
        by_cases hlt : p < d.cells.size
        · rw [get_set_self d p _ hlt]
          simpa using hc
        · rw [get_set_oob d p _ hlt p]
          exact h.1 p
      · rw [get_set_ne d i p _ hpi]
        exact h.1 p
  · intro p
    rcases hget p with hp | hp
    · unfold stampAt; rw [hp]; rfl
    · unfold stampAt
      rw [hp]
      unfold placedN
      by_cases hpi : p = i
      · subst hpi
        by_cases hlt : p < d.cells.size
        · rw [get_set_self d p _ hlt]
          rfl
        · rw [get_set_oob d p _ hlt p]
          exact h.2 p
      · rw [get_set_ne d i p _ hpi]
        exact h.2 p

/-! ### Definedness under compatibility -/

theorem branch_empty_of_compat {D b : Display n}
    (hc : compatibleB n D b = true) {i : Nat} (hi : i < n*n)
    (hD : occD D i = false) : occD b i = false := by
  unfold compatibleB at hc
  have hmem : i ∈ allIdx n := by
    unfold allIdx; exact List.mem_range.mpr hi
  have hth := (List.all_eq_true.mp hc) i hmem
  cases hk : kindAt b i with
  | none =>
    rw [occD_false_iff]
    unfold kindAt at hk
    cases hg : b.get i
    · rfl
    · rw [hg] at hk; simp at hk
  | some k =>
    rw [hk] at hth
    rw [kindAt_none_of_empty D i hD] at hth
    simp at hth

theorem goMoveN_isSome_of_empty (d : Display n) (c : DKind) (i : Nat)
    (h : occD d i = false) : (goMoveN n d c i).isSome := by
  unfold goMoveN
  rw [h]
  simp

theorem serialP_isSome_of_avail {D b : Display n}
    (hc : compatibleB n D b = true) {m0 m1 : Option Nat}
    (h0 : availD n D m0 = true) (h1 : availD n D m1 = true) :
    (serialP n b m0 m1).isSome := by
  have hs : ∀ (c : DKind) (mo : Option Nat), availD n D mo = true →
      (bStep n b c mo).isSome := by
    intro c mo hav
    cases mo with
    | none => simp [bStep]
    | some i =>
      unfold availD at hav
      have hsplit : decide (i < n*n) = true ∧ (!occD D i) = true := by
        simpa using hav
      have hi : i < n*n := of_decide_eq_true hsplit.1
      have hnot := hsplit.2
      have hocc : occD D i = false := by
        cases hoc : occD D i
        · rfl
        · exact absurd hnot (by simp [hoc])
      exact goMoveN_isSome_of_empty b c i
        (branch_empty_of_compat hc hi hocc)
  rcases Option.isSome_iff_exists.mp (hs .b m0 h0) with ⟨x0, hx0⟩
  rcases Option.isSome_iff_exists.mp (hs .w m1 h1) with ⟨x1, hx1⟩
  cases h01 : bStep2 n b .b .w m0 m1 with
  | some a =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a' => simp [serialP, h01, h10]
    | none => simp [serialP, h01, h10, hx1]
  | none =>
    cases h10 : bStep2 n b .w .b m1 m0 with
    | some a' => simp [serialP, h01, h10, hx0]
    | none => simp [serialP, h01, h10, hx0, hx1]

theorem simEvAux_isSome {bs : List (Display n)} {D : Display n}
    (hc : ∀ b, b ∈ bs → compatibleB n D b = true) {m0 m1 : Option Nat}
    (h0 : availD n D m0 = true) (h1 : availD n D m1 = true) :
    (simEvAux n m0 m1 bs).isSome := by
  induction bs with
  | nil => simp [simEvAux]
  | cons b bs ih =>
    rcases Option.isSome_iff_exists.mp
      (serialP_isSome_of_avail (hc b (List.mem_cons_self b bs)) h0 h1)
      with ⟨l, hl⟩
    rcases Option.isSome_iff_exists.mp
      (ih (fun x hx => hc x (List.mem_cons_of_mem b hx))) with ⟨r, hr⟩
    simp [simEvAux, hl, hr]

/-- The M1 caveat closed: under compatibility, sgoEv is defined
    exactly at non-final states with both moves display-available. -/
theorem sgoEv_isSome_iff (s : SGoState n)
    (hc : ∀ b, b ∈ s.ent → compatibleB n s.disp b = true)
    (m0 m1 : Option Nat) :
    (sgoEv n s m0 m1).isSome ↔
      (s.final = false ∧ availD n s.disp m0 = true ∧
       availD n s.disp m1 = true) := by
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨s', hs'⟩
    unfold sgoEv at hs'
    by_cases hf : s.final = true
    · rw [if_pos hf] at hs'; cases hs'
    · rw [if_neg hf] at hs'
      have hfk : s.final = false := by
        cases hfc : s.final
        · rfl
        · exact absurd hfc hf
      by_cases hav : (availD n s.disp m0 && availD n s.disp m1) = true
      · have hsplit : availD n s.disp m0 = true ∧
            availD n s.disp m1 = true := by simpa using hav
        exact ⟨hfk, hsplit.1, hsplit.2⟩
      · have hbang : (!(availD n s.disp m0 && availD n s.disp m1)) = true := by
          cases hb : (availD n s.disp m0 && availD n s.disp m1)
          · rfl
          · exact absurd hb hav
        rw [if_pos hbang] at hs'
        cases hs'
  · rintro ⟨hf, h0, h1⟩
    unfold sgoEv
    rw [if_neg (by simp [hf] : ¬(s.final = true))]
    rw [if_neg (by simp [h0, h1] :
      ¬((!(availD n s.disp m0 && availD n s.disp m1)) = true))]
    have hout : (simEv n s.ent m0 m1).isSome := by
      unfold simEv
      rcases Option.isSome_iff_exists.mp (simEvAux_isSome hc h0 h1)
        with ⟨out, hout⟩
      simp [hout]
    rcases Option.isSome_iff_exists.mp hout with ⟨bs, hbs⟩
    cases m0 with
    | none =>
      cases m1 with
      | none => simp
      | some i1 => simp [hbs]
    | some i0 =>
      cases m1 with
      | none => simp [hbs]
      | some i1 => simp [hbs]

/-! ### The invariant -/

structure Inv (s : SGoState n) : Prop where
  wfdD : WFD s.disp
  next_pos : 1 ≤ s.next
  stamps : StampsBelow s.disp s.next
  entWfd : ∀ b, b ∈ s.ent → WFD b
  entClassical : ∀ b, b ∈ s.ent → IsClassical b
  entZero : ∀ b, b ∈ s.ent → StampsZero b
  entCompat : ∀ b, b ∈ s.ent → compatibleB n s.disp b = true

theorem inv_init : Inv (initSGo n) := by
  refine ⟨emptyD_wfd, Nat.le_refl 1, ?_, ?_, ?_, ?_, ?_⟩
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
    unfold compatibleB
    apply List.all_eq_true.mpr
    intro i _
    unfold kindAt
    rw [emptyD_get i]
    rfl

theorem simEvAux_mem {bs : List (Display n)} {m0 m1 : Option Nat}
    {out : List (Display n)} (h : simEvAux n m0 m1 bs = some out)
    {x : Display n} (hx : x ∈ out) :
    ∃ b, b ∈ bs ∧ ∃ l, serialP n b m0 m1 = some l ∧ x ∈ l := by
  induction bs generalizing out with
  | nil =>
    simp only [simEvAux] at h
    cases h
    cases hx
  | cons b bs ih =>
    cases hp : serialP n b m0 m1 with
    | none => exact absurd h (by simp [simEvAux, hp])
    | some l =>
      cases hr : simEvAux n m0 m1 bs with
      | none => exact absurd h (by simp [simEvAux, hp, hr])
      | some r =>
        simp only [simEvAux, hp, hr] at h
        cases h
        rcases List.mem_append.mp hx with hxl | hxr
        · exact ⟨b, List.mem_cons_self b bs, l, hp, hxl⟩
        · rcases ih hr hxr with ⟨b', hb', l', hl', hx'⟩
          exact ⟨b', List.mem_cons_of_mem b hb', l', hl', hx'⟩

/-- The state built by a non-double-pass sgoEv step satisfies the
    invariant. -/
theorem inv_step_core {s : SGoState n} (h : Inv s) {m0 m1 : Option Nat}
    {bs : List (Display n)} (hse : simEv n s.ent m0 m1 = some bs) :
    Inv (⟨resolveTurn s.disp s.next m0 m1, s.next + 1,
      bs.filter (compatibleB n (resolveTurn s.disp s.next m0 m1)),
      false⟩ : SGoState n) := by
  have hmem : ∀ x, x ∈ bs.filter
      (compatibleB n (resolveTurn s.disp s.next m0 m1)) →
      ∃ b, b ∈ s.ent ∧ ∃ l, serialP n b m0 m1 = some l ∧ x ∈ l := by
    intro x hx
    have hx' : x ∈ bs := (List.mem_filter.mp hx).1
    unfold simEv at hse
    cases hax : simEvAux n m0 m1 s.ent with
    | none => rw [hax] at hse; cases hse
    | some out =>
      rw [hax] at hse
      have hbs : bs = dedupD n out := by
        have hh : some (dedupD n out) = some bs := hse
        exact (Option.some.inj hh).symm
      exact simEvAux_mem hax (mem_dedupD _ _ (hbs ▸ hx'))
  refine ⟨resolveTurn_wfd _ _ _ _ h.wfdD,
    Nat.le_succ_of_le h.next_pos,
    resolveTurn_stampsBelow _ _ _ _ h.stamps, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rcases hmem b hb with ⟨b0, hb0, l, hl, hbl⟩
    exact serialP_out
      (fun d c _ i r _ hr => goMoveN_size d c i r hr)
      (h.entWfd b0 hb0) hl b hbl
  · intro b hb
    rcases hmem b hb with ⟨b0, hb0, l, hl, hbl⟩
    exact (serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl b hbl).1
  · intro b hb
    rcases hmem b hb with ⟨b0, hb0, l, hl, hbl⟩
    exact (serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl b hbl).2
  · intro b hb
    exact (List.mem_filter.mp hb).2

/-- The invariant is preserved by every defined sgoEv step. -/
theorem inv_step {s s' : SGoState n} (h : Inv s) {m0 m1 : Option Nat}
    (hst : sgoEv n s m0 m1 = some s') : Inv s' := by
  unfold sgoEv at hst
  by_cases hf : s.final = true
  · rw [if_pos hf] at hst; cases hst
  · rw [if_neg hf] at hst
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
      cases m0 with
      | none =>
        cases m1 with
        | none =>
          cases hst
          exact ⟨h.wfdD, Nat.le_succ_of_le h.next_pos,
            fun p => Nat.lt_succ_of_lt (h.stamps p),
            h.entWfd, h.entClassical, h.entZero, h.entCompat⟩
        | some i1 =>
          cases hse : simEv n s.ent none (some i1) with
          | none => simp only [hse] at hst; exact Option.noConfusion hst
          | some bs =>
            simp only [hse] at hst
            cases hst
            exact inv_step_core h hse
      | some i0 =>
        cases m1 with
        | none =>
          cases hse : simEv n s.ent (some i0) none with
          | none => simp only [hse] at hst; exact Option.noConfusion hst
          | some bs =>
            simp only [hse] at hst
            cases hst
            exact inv_step_core h hse
        | some i1 =>
          cases hse : simEv n s.ent (some i0) (some i1) with
          | none => simp only [hse] at hst; exact Option.noConfusion hst
          | some bs =>
            simp only [hse] at hst
            cases hst
            exact inv_step_core h hse

end SgoInv
