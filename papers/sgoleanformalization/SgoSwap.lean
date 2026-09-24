/- SgoSwap.lean — the main theorem, milestone 5: the color-swap symmetry
   of the display machinery.

   The whole capture stack is color-BLIND on index sets: components
   group same-kind stones, liberties and trapping read emptiness and
   stamps, and captures test them — none of it depends on WHICH color,
   only on same-kind and occupied. So the color swap swapD leaves
   componentD, noLibD, trappedOnTurn invariant (identical index sets),
   is equivariant for isCaptured/capturedOf (color ↦ opp, same sets),
   and commutes with basicCap, capFix, stages, placeJoint, goMoveN,
   serialP and delta. This one equivariance serves the SimSym of all
   four games and the SeqSym of Go. -/
import SgoDInv

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv

namespace SgoSwap

variable {n : Nat}

/-! ### The swap on kinds and cells -/

theorem opp_opp_all (k : DKind) : k.opp.opp = k := by cases k <;> rfl

def swapCell : Cell → Cell := fun c => c.map fun p => (p.1.opp, p.2)

theorem swapCell_none : swapCell none = none := rfl

theorem swapCell_swapCell (c : Cell) : swapCell (swapCell c) = c := by
  cases c with
  | none => rfl
  | some p => obtain ⟨k, st⟩ := p; show some (k.opp.opp, st) = some (k, st)
              rw [opp_opp_all]

def swapD (D : Display n) : Display n := ⟨D.cells.map swapCell⟩

theorem swapD_get (D : Display n) (i : Nat) :
    (swapD D).get i = swapCell (D.get i) := by
  show (D.cells.map swapCell).getD i none = swapCell (D.cells.getD i none)
  rw [Array.getD_eq_get?, Array.getD_eq_get?]
  rw [show (D.cells.map swapCell)[i]? = (D.cells[i]?).map swapCell from by
    rw [Array.getElem?_map]]
  cases h : D.cells[i]? with
  | none => rfl
  | some c => rfl

theorem swapD_size (D : Display n) :
    (swapD D).cells.size = D.cells.size := Array.size_map _ _

theorem swapD_wfd {D : Display n} (h : WFD D) : WFD (swapD D) := by
  unfold WFD; rw [swapD_size]; exact h

theorem swapD_swapD (D : Display n) : swapD (swapD D) = D := by
  apply display_ext
  apply Array.ext
  · rw [swapD_size, swapD_size]
  · intro i h1 h2
    have hib : i < (swapD (swapD D)).cells.size := h1
    rw [← get_in_bounds _ i h1, ← get_in_bounds _ i h2,
      swapD_get, swapD_get, swapCell_swapCell]

theorem kindAt_swapD (D : Display n) (i : Nat) :
    kindAt (swapD D) i = (kindAt D i).map DKind.opp := by
  unfold kindAt
  rw [swapD_get]
  cases h : D.get i with
  | none => rfl
  | some c => obtain ⟨k, st⟩ := c; rfl

theorem occD_swapD (D : Display n) (i : Nat) :
    occD (swapD D) i = occD D i := by
  unfold occD
  rw [swapD_get]
  cases h : D.get i with
  | none => rfl
  | some c => rfl

theorem stampAt_swapD (D : Display n) (i : Nat) :
    stampAt (swapD D) i = stampAt D i := by
  unfold stampAt
  rw [swapD_get]
  cases h : D.get i with
  | none => rfl
  | some c => obtain ⟨k, st⟩ := c; rfl

theorem kindAt_swapD_eq_some {D : Display n} {i : Nat} {k : DKind}
    (h : kindAt D i = some k) : kindAt (swapD D) i = some k.opp := by
  rw [kindAt_swapD, h]; rfl

@[simp] theorem opp_r : (DKind.r).opp = DKind.r := rfl
@[simp] theorem opp_b : (DKind.b).opp = DKind.w := rfl
@[simp] theorem opp_w : (DKind.w).opp = DKind.b := rfl

@[simp] theorem beq_opp_opp (a b : DKind) :
    (a.opp == b.opp) = (a == b) := by cases a <;> cases b <;> rfl

@[simp] theorem beq_map_opp (o : Option DKind) (k : DKind) :
    ((o.map DKind.opp) == some k.opp) = (o == some k) := by
  cases o with
  | none => rfl
  | some k' => show (some k'.opp == some k.opp) = (some k' == some k)
               simp

theorem swapD_set (D : Display n) (i : Nat) (c : Cell) :
    swapD (D.set i c) = (swapD D).set i (swapCell c) := by
  apply display_ext
  apply Array.ext
  · rw [swapD_size]
    show (D.set i c).cells.size = ((swapD D).set i (swapCell c)).cells.size
    rw [set_size, set_size, swapD_size]
  · intro p h1 h2
    have hib : p < (swapD (D.set i c)).cells.size := h1
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
    rw [swapD_get]
    by_cases hp : p = i
    · subst hp
      by_cases hb : p < D.cells.size
      · rw [get_set_self D p c hb, get_set_self (swapD D) p (swapCell c)
          (by rw [swapD_size]; exact hb)]
      · rw [get_set_oob D p c hb, get_set_oob (swapD D) p (swapCell c)
          (by rw [swapD_size]; exact hb), swapD_get]
    · rw [get_set_ne D i p c hp, get_set_ne (swapD D) i p (swapCell c) hp,
        swapD_get]

/-! ### Component / liberty / trapping are color-blind -/

/-- componentKAux depends only on the target-kind predicate and
    adjacency, both of which the swap preserves under k ↦ k.opp. -/
theorem componentKAux_swapD (D : Display n) (k : DKind) :
    ∀ (fuel : Nat) (comp frontier : List Nat),
    componentKAux n (swapD D) k.opp fuel comp frontier
      = componentKAux n D k fuel comp frontier := by
  intro fuel
  induction fuel with
  | zero => intro comp frontier; rfl
  | succ fuel ih =>
    intro comp frontier
    have hnext : ((allIdx n).filter fun q =>
        kindAt (swapD D) q == some k.opp && !comp.contains q
          && frontier.any fun r => adjI n q r)
        = ((allIdx n).filter fun q =>
        kindAt D q == some k && !comp.contains q
          && frontier.any fun r => adjI n q r) := by
      apply List.filter_congr
      intro q _
      simp only [kindAt_swapD, beq_map_opp]
    show componentKAux n (swapD D) k.opp (fuel+1) comp frontier = _
    unfold componentKAux
    rw [hnext]
    cases hc : ((allIdx n).filter fun q =>
        kindAt D q == some k && !comp.contains q
          && frontier.any fun r => adjI n q r) with
    | nil => rfl
    | cons a l => exact ih (comp ++ (a :: l)) (a :: l)

theorem componentD_swapD (D : Display n) (i : Nat) :
    componentD (swapD D) i = componentD D i := by
  unfold componentD
  rw [kindAt_swapD]
  cases h : kindAt D i with
  | none => rfl
  | some k =>
    show componentKAux n (swapD D) k.opp (n*n) [i] [i]
      = componentKAux n D k (n*n) [i] [i]
    exact componentKAux_swapD D k (n*n) [i] [i]

theorem noLibD_swapD (D : Display n) (comp : List Nat) :
    noLibD (swapD D) comp = noLibD D comp := by
  simp only [noLibD, occD_swapD]

theorem trappedOnTurn_swapD (D : Display n) (comp : List Nat) (t : Nat) :
    trappedOnTurn (swapD D) comp t = trappedOnTurn D comp t := by
  have hs : stampAt (swapD D) = stampAt D := funext (stampAt_swapD D)
  simp only [trappedOnTurn, occD_swapD, hs, noLibD_swapD]

/-! ### Reading helpers for the color-tagged clauses -/

theorem red_swap (D : Display n) (z : Nat) :
    (kindAt (swapD D) z == some .r) = (kindAt D z == some .r) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> rfl

theorem realStone_swap (D : Display n) (z : Nat) :
    (kindAt (swapD D) z == some .b || kindAt (swapD D) z == some .w)
      = (kindAt D z == some .b || kindAt D z == some .w) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> rfl

theorem eq_c_swap (D : Display n) (z : Nat) (c : DKind) :
    (kindAt (swapD D) z == some c) = (kindAt D z == some c.opp) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> cases c <;> rfl

theorem red_bne_swap (D : Display n) (z : Nat) :
    (kindAt (swapD D) z != some .r) = (kindAt D z != some .r) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> rfl

theorem neq_c_swap (D : Display n) (z : Nat) (c : DKind) :
    (kindAt (swapD D) z != some c) = (kindAt D z != some c.opp) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> cases c <;> rfl

theorem eq_copp_swap (D : Display n) (z : Nat) (c : DKind) :
    (kindAt (swapD D) z == some c.opp) = (kindAt D z == some c) := by
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k => cases k <;> cases c <;> rfl

/-! ### stoneTrappedBy and isCaptured are equivariant (color ↦ opp) -/

theorem replaceKind_swapD (D : Display n) (z : Nat) (k : DKind) :
    swapD (replaceKind D z k) = replaceKind (swapD D) z k.opp := by
  unfold replaceKind
  rw [swapD_set]
  congr 1
  rw [swapD_get]
  cases h : D.get z with
  | none => rfl
  | some c => obtain ⟨k', st⟩ := c; rfl

theorem stoneTrappedBy_swapD (D : Display n) (z : Nat) (attacker : DKind)
    (t : Nat) :
    stoneTrappedBy (swapD D) z attacker t
      = stoneTrappedBy D z attacker.opp t := by
  unfold stoneTrappedBy
  rw [kindAt_swapD]
  cases h : kindAt D z with
  | none => rfl
  | some k =>
    cases k with
    | r =>
      show trappedOnTurn (replaceKind (swapD D) z attacker.opp)
          (componentD (replaceKind (swapD D) z attacker.opp) z) t
        = trappedOnTurn (replaceKind D z attacker.opp.opp)
          (componentD (replaceKind D z attacker.opp.opp) z) t
      rw [← replaceKind_swapD D z attacker, componentD_swapD,
        trappedOnTurn_swapD, show attacker.opp.opp = attacker from
        opp_opp_all attacker]
    | b =>
      show (if (DKind.w == attacker.opp) = true
          then trappedOnTurn (swapD D) (componentD (swapD D) z) t
          else false)
        = (if (DKind.b == attacker.opp.opp) = true
          then trappedOnTurn D (componentD D z) t else false)
      rw [componentD_swapD, trappedOnTurn_swapD,
        show (DKind.w == attacker.opp) = (DKind.b == attacker.opp.opp) from by
          cases attacker <;> rfl]
    | w =>
      show (if (DKind.b == attacker.opp) = true
          then trappedOnTurn (swapD D) (componentD (swapD D) z) t
          else false)
        = (if (DKind.w == attacker.opp.opp) = true
          then trappedOnTurn D (componentD D z) t else false)
      rw [componentD_swapD, trappedOnTurn_swapD,
        show (DKind.b == attacker.opp) = (DKind.w == attacker.opp.opp) from by
          cases attacker <;> rfl]

theorem isCaptured_swapD (D : Display n) (comp : List Nat) (c : DKind)
    (t : Nat) :
    isCaptured (swapD D) comp c t = isCaptured D comp c.opp t := by
  have hs : stampAt (swapD D) = stampAt D := funext (stampAt_swapD D)
  have hcomp : ∀ z, componentD (swapD D) z = componentD D z :=
    componentD_swapD D
  simp only [isCaptured, trappedOnTurn_swapD, red_swap, red_bne_swap,
    realStone_swap, neq_c_swap, eq_copp_swap, noLibD_swapD, hcomp, hs,
    occD_swapD, stoneTrappedBy_swapD, opp_opp_all, opp_r]

/-! ### capturedOf and basicCap commute with the swap -/

theorem capStep_swapD (D : Display n) (t : Nat) (c : DKind) :
    capStep (swapD D) t c = capStep D t c.opp := by
  funext acc p
  obtain ⟨seen, caps⟩ := acc
  show (if kindAt (swapD D) p == some c && !seen.contains p then
      let comp := componentD (swapD D) p
      (seen ++ comp, if isCaptured (swapD D) comp c t then caps ++ comp else caps)
    else (seen, caps))
    = (if kindAt D p == some c.opp && !seen.contains p then
      let comp := componentD D p
      (seen ++ comp, if isCaptured D comp c.opp t then caps ++ comp else caps)
    else (seen, caps))
  simp only [eq_c_swap, componentD_swapD, isCaptured_swapD]

theorem capturedOf_swapD (D : Display n) (t : Nat) (c : DKind) :
    capturedOf (swapD D) t c = capturedOf D t c.opp := by
  rw [capturedOf_eq_fold, capturedOf_eq_fold, capStep_swapD]

/-- A q-stone cannot neighbor both a captured black and a captured
    white component: the white capture's cond_unambiguous0 forbids it.
    This makes basicCap's two recolor branches mutually exclusive, so
    the swap commutes with it. -/
theorem recolor_excl (D : Display n) (t p : Nat) (hp : p < n*n)
    (hr : kindAt D p = some .r)
    (hb : (capturedOf D t .b).any (fun q => adjI n p q) = true)
    (hw : (capturedOf D t .w).any (fun q => adjI n p q) = true) : False := by
  rcases List.any_eq_true.mp hb with ⟨qb, hqbmem, hadjb⟩
  rcases List.any_eq_true.mp hw with ⟨qw, hqwmem, hadjw⟩
  rw [mem_capturedOf] at hqbmem hqwmem
  obtain ⟨pb, hpbb, hpbk, hpbcap, hqbc⟩ := hqbmem
  obtain ⟨pw, hpwb, hpwk, hpwcap, hqwc⟩ := hqwmem
  have hqbboard : qb ∈ allIdx n := componentD_board hpbb hpbk hqbc
  -- unpack the white capture's unambiguity clause
  have hwc := hpwcap
  unfold isCaptured at hwc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hwc
  have hunamb := hwc.1.2
  -- p is a red adjacent to comp_w
  have hpred : p ∈ (allIdx n).filter fun z =>
      kindAt D z == some .r && (componentD D pw).any fun q => adjI n z q := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hp, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hr, List.any_eq_true.mpr
      ⟨qw, hqwc, hadjw⟩⟩
  have hqball := (List.all_eq_true.mp hunamb) p hpred
  have hz := (List.all_eq_true.mp hqball) qb hqbboard
  -- qb is black, adjacent to p, in a captured (trapped) component ≠ comp_w
  have hqbk : kindAt D qb = some .b := componentD_kind D pb .b hpbk qb hqbc
  have hbc := hpbcap
  unfold isCaptured at hbc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hbc
  have hbtrap := hbc.1.1
  have hqbcomp : ∀ x, x ∈ componentD D qb ↔ x ∈ componentD D pb :=
    componentD_eq_mem D pb qb .b hpbb hpbk hqbc
  have hnolib : noLibD D (componentD D qb) = true := by
    rw [noLibD_congr D _ _ hqbcomp]
    have := hbtrap
    unfold trappedOnTurn at this
    rw [Bool.and_eq_true] at this
    exact this.1
  -- comp_w ≠ comp_b (different colors)
  have hne : (!((componentD D qb).all (componentD D pw).contains
      && (componentD D pw).all (componentD D qb).contains)) = true := by
    cases hcc : ((componentD D qb).all (componentD D pw).contains
        && (componentD D pw).all (componentD D qb).contains) with
    | false => rfl
    | true =>
      exfalso
      rw [Bool.and_eq_true] at hcc
      have hpwin : pw ∈ componentD D qb :=
        List.mem_of_elem_eq_true ((List.all_eq_true.mp hcc.2) pw
          (componentD_mem_self D pw .w hpwk))
      have : kindAt D pw = some .b := componentD_kind D qb .b hqbk pw hpwin
      rw [hpwk] at this
      exact absurd this (by decide)
  -- every conjunct of the forbidden clause is true → contradiction
  have hadjqb : adjI n qb p = true := adjI_symm hadjb
  have hreal : (kindAt D qb == some .b || kindAt D qb == some .w) = true := by
    rw [hqbk]; rfl
  have hkne : (kindAt D qb != some DKind.w) = true := by rw [hqbk]; rfl
  simp [hadjqb, hreal, hkne, hnolib, hne] at hz

theorem contains_append_comm (l1 l2 : List Nat) (p : Nat) :
    (l1 ++ l2).contains p = (l2 ++ l1).contains p := by
  cases h1 : (l1 ++ l2).contains p with
  | true =>
    have hm : p ∈ l2 ++ l1 := List.mem_append.mpr
      (Or.symm (List.mem_append.mp (List.mem_of_elem_eq_true h1)))
    exact (List.elem_eq_true_of_mem hm).symm
  | false =>
    cases h2 : (l2 ++ l1).contains p with
    | true =>
      have hm : p ∈ l1 ++ l2 := List.mem_append.mpr
        (Or.symm (List.mem_append.mp (List.mem_of_elem_eq_true h2)))
      have h3 : (l1 ++ l2).contains p = true := List.elem_eq_true_of_mem hm
      rw [h1] at h3
      exact Bool.noConfusion h3
    | false => rfl

theorem basicCap_swapD (D : Display n) (t : Nat) :
    basicCap (swapD D) t = swapD (basicCap D t) := by
  apply display_ext
  apply Array.ext
  · rw [basicCap_size, swapD_size, basicCap_size]
  · intro p h1 h2
    have hib : p < n*n := by
      have := basicCap_size (swapD D) t; omega
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
    rw [swapD_get]
    -- unfold both basicCap cell maps
    have hbs : (basicCap (swapD D) t).get p
        = if (capturedOf (swapD D) t .b ++ capturedOf (swapD D) t .w).contains p
            then none
          else if kindAt (swapD D) p == some .r
              && (capturedOf (swapD D) t .w).any (fun q => adjI n p q) then
            ((swapD D).get p).map fun cell => (DKind.b, cell.2)
          else if kindAt (swapD D) p == some .r
              && (capturedOf (swapD D) t .b).any (fun q => adjI n p q) then
            ((swapD D).get p).map fun cell => (DKind.w, cell.2)
          else (swapD D).get p := by
      show (⟨(Array.range (n*n)).map _⟩ : Display n).get p = _
      rw [get_map_range, if_pos hib]
    have hbd : (basicCap D t).get p
        = if (capturedOf D t .b ++ capturedOf D t .w).contains p then none
          else if kindAt D p == some .r
              && (capturedOf D t .w).any (fun q => adjI n p q) then
            (D.get p).map fun cell => (DKind.b, cell.2)
          else if kindAt D p == some .r
              && (capturedOf D t .b).any (fun q => adjI n p q) then
            (D.get p).map fun cell => (DKind.w, cell.2)
          else D.get p := by
      show (⟨(Array.range (n*n)).map _⟩ : Display n).get p = _
      rw [get_map_range, if_pos hib]
    rw [hbs, hbd]
    simp only [capturedOf_swapD, opp_b, opp_w]
    rw [contains_append_comm (capturedOf D t .w) (capturedOf D t .b) p]
    by_cases hdead : (capturedOf D t .b ++ capturedOf D t .w).contains p = true
    · rw [if_pos hdead, if_pos hdead]; rfl
    · rw [if_neg hdead, if_neg hdead]
      cases hgp : D.get p with
      | none =>
        have hknr : (kindAt D p == some .r) = false := by
          unfold kindAt; rw [hgp]; rfl
        simp [red_swap, hknr, swapD_get, hgp]
      | some cell =>
        obtain ⟨kk, st⟩ := cell
        have hka : kindAt D p = some kk := by unfold kindAt; rw [hgp]; rfl
        cases kk with
        | b =>
          have hknr : (kindAt D p == some .r) = false := by rw [hka]; rfl
          simp [red_swap, hknr, swapD_get, hgp]
        | w =>
          have hknr : (kindAt D p == some .r) = false := by rw [hka]; rfl
          simp [red_swap, hknr, swapD_get, hgp]
        | r =>
          have hkr : (kindAt D p == some .r) = true := by rw [hka]; rfl
          by_cases hcb : (capturedOf D t .b).any (fun q => adjI n p q) = true
          · have hcw : (capturedOf D t .w).any (fun q => adjI n p q) = false := by
              cases hh : (capturedOf D t .w).any (fun q => adjI n p q) with
              | false => rfl
              | true => exact (recolor_excl D t p hib hka hcb hh).elim
            simp [red_swap, hkr, hcb, hcw, swapD_get, hgp, swapCell]
          · have hcbF : (capturedOf D t .b).any (fun q => adjI n p q) = false := by
              cases hh : (capturedOf D t .b).any (fun q => adjI n p q) with
              | false => rfl
              | true => exact absurd hh hcb
            by_cases hcw : (capturedOf D t .w).any (fun q => adjI n p q) = true
            · simp [red_swap, hkr, hcbF, hcw, swapD_get, hgp, swapCell]
            · have hcwF : (capturedOf D t .w).any (fun q => adjI n p q) = false := by
                cases hh : (capturedOf D t .w).any (fun q => adjI n p q) with
                | false => rfl
                | true => exact absurd hh hcw
              simp [red_swap, hkr, hcbF, hcwF, swapD_get, hgp]

/-! ### The swap is BEq-injective; capFix and stages commute -/

theorem swapD_beq (A B : Display n) : (swapD A == swapD B) = (A == B) := by
  cases h : (A == B) with
  | true =>
    rw [display_eq_of_beq h]; exact display_beq_self _
  | false =>
    cases h2 : (swapD A == swapD B) with
    | false => rfl
    | true =>
      have heq : swapD A = swapD B := display_eq_of_beq h2
      have : A = B := by
        have := congrArg swapD heq
        rwa [swapD_swapD, swapD_swapD] at this
      rw [this, display_beq_self] at h
      exact absurd h (by simp)

theorem capFix_swapD (fuel : Nat) (D : Display n) (t : Nat) :
    capFix fuel (swapD D) t = swapD (capFix fuel D t) := by
  induction fuel generalizing D with
  | zero => rfl
  | succ fuel ih =>
    show (if basicCap (swapD D) t == swapD D then swapD D
        else capFix fuel (basicCap (swapD D) t) t)
      = swapD (if basicCap D t == D then D else capFix fuel (basicCap D t) t)
    rw [basicCap_swapD, swapD_beq]
    by_cases hb : (basicCap D t == D) = true
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, ih (basicCap D t)]

theorem stages_swapD (fuel : Nat) (D : Display n) (t : Nat) :
    stages fuel (swapD D) t = swapD (stages fuel D t) := by
  induction fuel generalizing D t with
  | zero => rfl
  | succ fuel ih =>
    show (if t == 0 then swapD D
        else if capFix (n*n+1) (swapD D) t == swapD D then swapD D
          else stages fuel (capFix (n*n+1) (swapD D) t) (t-1))
      = swapD (if t == 0 then D
        else if capFix (n*n+1) D t == D then D
          else stages fuel (capFix (n*n+1) D t) (t-1))
    by_cases ht : (t == 0) = true
    · rw [if_pos ht, if_pos ht]
    · rw [if_neg ht, if_neg ht, capFix_swapD, swapD_beq]
      by_cases hb : (capFix (n*n+1) D t == D) = true
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb, ih (capFix (n*n+1) D t) (t-1)]

/-! ### Placement commutes with the swap under the slot swap -/

theorem set_set_comm (D : Display n) (i j : Nat) (ci cj : Cell)
    (h : i ≠ j) : (D.set i ci).set j cj = (D.set j cj).set i ci := by
  apply display_ext
  apply Array.ext
  · rw [set_size, set_size, set_size, set_size]
  · intro p hp1 hp2
    rw [← get_in_bounds _ p hp1, ← get_in_bounds _ p hp2]
    by_cases hpi : p = i
    · subst hpi
      -- now p ≠ j (h : p ≠ j)
      rw [get_set_ne (D.set p ci) j p cj h]
      by_cases hb : p < D.cells.size
      · rw [get_set_self D p ci hb,
          get_set_self (D.set j cj) p ci (by rw [set_size]; exact hb)]
      · rw [get_set_oob D p ci hb p,
          get_set_oob (D.set j cj) p ci (by rw [set_size]; exact hb) p,
          get_set_ne D j p cj h]
    · by_cases hpj : p = j
      · subst hpj
        -- now p ≠ i (hpi : p ≠ i)
        rw [get_set_ne (D.set p cj) i p ci hpi]
        by_cases hb : p < D.cells.size
        · rw [get_set_self (D.set i ci) p cj (by rw [set_size]; exact hb),
            get_set_self D p cj hb]
        · rw [get_set_oob (D.set i ci) p cj (by rw [set_size]; exact hb) p,
            get_set_oob D p cj hb p,
            get_set_ne D i p ci hpi]
      · rw [get_set_ne (D.set i ci) j p cj hpj, get_set_ne D i p ci hpi,
          get_set_ne (D.set j cj) i p ci hpi, get_set_ne D j p cj hpj]

theorem placeJoint_swapD (D : Display n) (t : Nat) (m0 m1 : Option Nat) :
    placeJoint (swapD D) t m1 m0 = swapD (placeJoint D t m0 m1) := by
  cases m0 with
  | none =>
    cases m1 with
    | none => rfl
    | some p1 =>
      show (swapD D).set p1 (some (.b, t)) = swapD (D.set p1 (some (.w, t)))
      rw [swapD_set]; rfl
  | some p0 =>
    cases m1 with
    | none =>
      show (swapD D).set p0 (some (.w, t)) = swapD (D.set p0 (some (.b, t)))
      rw [swapD_set]; rfl
    | some p1 =>
      by_cases hpp : p0 = p1
      · subst hpp
        show placeJoint (swapD D) t (some p0) (some p0)
          = swapD (placeJoint D t (some p0) (some p0))
        simp only [placeJoint]
        rw [if_pos (beq_iff_eq.mpr rfl), if_pos (beq_iff_eq.mpr rfl),
          swapD_set]; rfl
      · show placeJoint (swapD D) t (some p1) (some p0)
          = swapD (placeJoint D t (some p0) (some p1))
        simp only [placeJoint]
        rw [if_neg (show ¬((p1 == p0) = true) from
              fun e => hpp (beq_iff_eq.mp e).symm),
            if_neg (show ¬((p0 == p1) = true) from
              fun e => hpp (beq_iff_eq.mp e))]
        rw [swapD_set, swapD_set]
        show ((swapD D).set p1 (some (.b, t))).set p0 (some (.w, t))
          = ((swapD D).set p0 (swapCell (some (.b, t)))).set p1
              (swapCell (some (.w, t)))
        show ((swapD D).set p1 (some (.b, t))).set p0 (some (.w, t))
          = ((swapD D).set p0 (some (.w, t))).set p1 (some (.b, t))
        exact set_set_comm (swapD D) p1 p0 (some (.b, t)) (some (.w, t))
          (fun e => hpp e.symm)

theorem resolveTurn_swapD (D : Display n) (t : Nat) (m0 m1 : Option Nat) :
    resolveTurn (swapD D) t m1 m0 = swapD (resolveTurn D t m0 m1) := by
  unfold resolveTurn
  rw [placeJoint_swapD, stages_swapD]

/-! ### The classical move commutes with the swap (color ↦ opp) -/

theorem placedN_swapD (D : Display n) (c : DKind) (i : Nat) :
    placedN n (swapD D) c.opp i = swapD (placedN n D c i) := by
  unfold placedN
  rw [swapD_set]; rfl

theorem deadOppN_swapD (D : Display n) (c : DKind) (i : Nat) :
    deadOppN n (swapD D) c.opp i = deadOppN n D c i := by
  unfold deadOppN
  apply List.filter_congr
  intro p _
  rw [placedN_swapD, opp_opp_all]
  rw [eq_c_swap, componentD_swapD, noLibD_swapD]

theorem afterCapN_size (D : Display n) (c : DKind) (i : Nat) :
    (afterCapN n D c i).cells.size = n*n := by
  unfold afterCapN; rw [Array.size_map, Array.size_range]

theorem erasedN_size (D : Display n) (c : DKind) (i : Nat) :
    (erasedN n D c i).cells.size = n*n := by
  unfold erasedN; rw [Array.size_map, Array.size_range]

theorem afterCapN_swapD (D : Display n) (c : DKind) (i : Nat) :
    afterCapN n (swapD D) c.opp i = swapD (afterCapN n D c i) := by
  apply display_ext; apply Array.ext
  · rw [afterCapN_size, swapD_size, afterCapN_size]
  · intro p hp1 hp2
    have hib : p < n*n := by
      have h := hp1; rw [afterCapN_size] at h; exact h
    rw [← get_in_bounds _ p hp1, ← get_in_bounds _ p hp2, swapD_get]
    unfold afterCapN
    rw [get_map_range, get_map_range, if_pos hib, if_pos hib,
      deadOppN_swapD]
    by_cases hd : (deadOppN n D c i).contains p = true
    · rw [if_pos hd, if_pos hd]; rfl
    · rw [if_neg hd, if_neg hd, placedN_swapD, swapD_get]

theorem ownCompN_swapD (D : Display n) (c : DKind) (i : Nat) :
    ownCompN n (swapD D) c.opp i = ownCompN n D c i := by
  unfold ownCompN
  rw [afterCapN_swapD, componentD_swapD]

theorem suicideN_swapD (D : Display n) (c : DKind) (i : Nat) :
    suicideN n (swapD D) c.opp i = suicideN n D c i := by
  unfold suicideN
  rw [afterCapN_swapD, ownCompN_swapD, noLibD_swapD]

theorem erasedN_swapD (D : Display n) (c : DKind) (i : Nat) :
    erasedN n (swapD D) c.opp i = swapD (erasedN n D c i) := by
  apply display_ext; apply Array.ext
  · rw [erasedN_size, swapD_size, erasedN_size]
  · intro p hp1 hp2
    have hib : p < n*n := by
      have h := hp1; rw [erasedN_size] at h; exact h
    rw [← get_in_bounds _ p hp1, ← get_in_bounds _ p hp2, swapD_get]
    unfold erasedN
    rw [get_map_range, get_map_range, if_pos hib, if_pos hib,
      ownCompN_swapD]
    by_cases hd : (ownCompN n D c i).contains p = true
    · rw [if_pos hd, if_pos hd]; rfl
    · rw [if_neg hd, if_neg hd, afterCapN_swapD, swapD_get]

theorem goMoveN_swapD (D : Display n) (c : DKind) (i : Nat) :
    goMoveN n (swapD D) c.opp i = Option.map swapD (goMoveN n D c i) := by
  unfold goMoveN
  rw [occD_swapD]
  cases hocc : occD D i with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, if_false, Option.map_some]
    rw [suicideN_swapD]
    by_cases hs : suicideN n D c i = true
    · rw [if_pos hs, if_pos hs, erasedN_swapD]; rfl
    · rw [if_neg hs, if_neg hs, afterCapN_swapD]; rfl

/-! ### Go's own symmetry: the color-swap operator on the core -/

/-- The color swap on moves: flip a move's color, fix the pass. -/
def swapMv : goMv.M → goMv.M
  | none => none
  | some (w, i) => some (!w, i)

theorem swapMv_swapMv (m : goMv.M) : swapMv (swapMv m) = m := by
  cases m with
  | none => rfl
  | some wi => obtain ⟨w, i⟩ := wi; show some (!(!w), i) = some (w, i)
               rw [Bool.not_not]

theorem swapMv_pass : swapMv goMv.pass = goMv.pass := rfl

theorem swapMv_deg (m : goMv.M) : goMv.deg0 m ↔ goMv.deg1 (swapMv m) := by
  cases m with
  | none => exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  | some wi =>
    obtain ⟨w, i⟩ := wi
    cases w with
    | false => exact ⟨fun _ => Or.inr ⟨i, rfl⟩, fun _ => Or.inr ⟨i, rfl⟩⟩
    | true =>
      constructor
      · rintro (h | ⟨j, hj⟩)
        · exact absurd h (by simp)
        · exact absurd hj (by simp)
      · rintro (h | ⟨j, hj⟩)
        · exact absurd h (by simp [swapMv])
        · exact absurd hj (by simp [swapMv])

theorem goMvAct_swapD (D : Display n) (m : goMv.M) :
    goMvAct n (swapD D) (swapMv m) = Option.map swapD (goMvAct n D m) := by
  cases m with
  | none => rfl
  | some wi =>
    obtain ⟨w, i⟩ := wi
    show (if i < n*n then goMoveN n (swapD D) (if !w then .w else .b) i
        else none)
      = Option.map swapD (if i < n*n then goMoveN n D (if w then .w else .b) i
        else none)
    by_cases hib : i < n*n
    · rw [if_pos hib, if_pos hib]
      have hcolor : (if !w then DKind.w else DKind.b)
          = (if w then DKind.w else DKind.b).opp := by cases w <;> rfl
      rw [hcolor, goMoveN_swapD]
    · rw [if_neg hib, if_neg hib]; rfl

/-! ### Go is symmetric: SeqSym (goGame n) -/

theorem swapD_emptyD : swapD (emptyD n) = emptyD n := by
  apply display_ext; apply Array.ext
  · rw [swapD_size]
  · intro p hp1 hp2
    rw [← get_in_bounds _ p hp1, ← get_in_bounds _ p hp2]
    simp only [swapD_get, emptyD_get, swapCell_none]

theorem option_map_swapD_swapD (x : Option (Display n)) :
    Option.map swapD (Option.map swapD x) = x := by
  cases x with
  | none => rfl
  | some d => show some (swapD (swapD d)) = some d; rw [swapD_swapD]

/-- def_symmetric for Go, on the option-C core presentation. -/
theorem go_seqSym : SeqSym (goGame n) := by
  refine ⟨swapMv, swapD, swapMv_swapMv, swapMv_pass, swapMv_deg,
    swapD_swapD, swapD_emptyD, fun _ => Iff.rfl, ?_⟩
  intro c m
  show Option.map swapD (goMvAct n (swapD c) (swapMv m)) = goMvAct n c m
  rw [goMvAct_swapD, option_map_swapD_swapD]

theorem goOK : GoOK n := go_seqSym

end SgoSwap
