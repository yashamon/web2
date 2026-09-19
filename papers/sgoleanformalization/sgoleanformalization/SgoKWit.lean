/- SgoKWit.lean — the main theorem, milestone 4c: k-DSGo is NOT faithful
   within distance k+1, at board side ≥ 5.

   The delayed-verdict witness. A semiclassical setup places a white
   stone whose sole liberty is the collision intersection A2 and the
   black wall A4 that will later surround A3; the A2/A2 collision splits
   the entanglement into the black-captures branch a0 (A1 emptied) and
   the white-joins branch a1 (A1 kept), and stores the verdict that the
   objective reduction removes A1 and makes the q-stone at A2 black. That
   verdict ages k-1 turns in a corner pocket (a prepared one-point
   suicide — a genuine, non-interacting move that leaves display and
   entanglement fixed), then fires on the final turn B3/A3: executing it
   empties A1 and blackens A2, so White's A3 dies in the surviving branch
   a0'' yet, protected through the Δ removal round by the a1 branches and
   discarded only at the re-cut, stands on the display. The display shows
   a stone dead in every surviving branch: the interface fails at
   distance k+1, while it holds within k (SgoKNat). -/
import SgoKNat
import SgoWit

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoSimple SgoWit SgoDInv SgoDOK SgoDNat SgoDSemi
  SgoDFaith SgoKInv SgoKNat

namespace SgoKWit

variable {n : Nat}

/-! ### Single-move commuting steps for k-DSGo (setup) -/

/-- One black single-move turn from a tracked semiclassical k-DSGo
    state: the verdict queue is all-empty (SgoKNat), so the executed
    verdict is the identity and the turn is a DSGo turn on the display,
    which the commuting single move tracks classically. -/
theorem ksemi_step_B (hn : 2 ≤ n) {k : Nat} (hk : 1 ≤ k) {s : KState n}
    {d r : Display n} {i : Nat}
    (hsc : SemiC (goGame n) (kGame n k) s (PState.live d false false))
    (hi : i < n*n) (hocc : occD d i = false)
    (hmv : goMoveN n d .b i = some r) :
    ∃ s', (kGame n k).pairE s (some (false, i)) none = some s'
      ∧ SemiC (goGame n) (kGame n k) s' (PState.live r false false) := by
  obtain ⟨hproj, hallq, hreach⟩ := ksemiC_project hn hsc
  obtain ⟨d', hshape, hmemb, hdisp, -⟩ := (dsemiC_track hn hproj).track
  have hInv := reach_invK hreach
  have hdd : d' = d := by
    rcases hshape with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae; rfl
    · cases hae
  rw [hdd] at hdisp
  have hfin : s.final = false := by
    rcases hshape with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hx : bStep2 n d .b .w (some i) none = some r := by
    show (goMoveN n d .b i).bind (fun d1 => bStep n d1 .w none) = some r
    rw [hmv]; rfl
  have hy : bStep2 n d .w .b none (some i) = some r := hmv
  have hb0 : ∀ j, (some i : Option Nat) = some j → j < n*n := by
    intro j hj; cases hj; exact hi
  have hb1 : ∀ j, (none : Option Nat) = some j → j < n*n := by
    intro j hj; cases hj
  have hcomm := commuteAt_BW hb0 hb1 hx hy
  have ha := assoc_BW hb0 hb1 hx (by rintro ⟨hc, -⟩; cases hc)
  have hdisp2 : SameCells s.disp d := hdisp
  have hav0 : availD n s.disp (some i) = true := by
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi, occ_eq_of_samecells hdisp2 i, hocc]; rfl
  have hqne : s.verdicts ≠ [] := by
    rw [hallq]; intro hcon
    have h2 := congrArg List.length hcon
    rw [List.length_replicate] at h2; simp at h2; omega
  have hEv : (kEv n s (some i) none).isSome :=
    (kEv_isSome_iff s hInv.entInc hqne (some i) none).mpr
      ⟨hfin, hav0, rfl⟩
  have hp : ((kGame n k).pairE s (some (false, i)) none).isSome = true := hEv
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  have hstep := SemiC.step hsc hcomm hs'
  rw [ha] at hstep
  exact ⟨s', hs', hstep⟩

/-- One white single-move turn from a tracked semiclassical k-DSGo
    state. -/
theorem ksemi_step_W (hn : 2 ≤ n) {k : Nat} (hk : 1 ≤ k) {s : KState n}
    {d r : Display n} {i : Nat}
    (hsc : SemiC (goGame n) (kGame n k) s (PState.live d false false))
    (hi : i < n*n) (hocc : occD d i = false)
    (hmv : goMoveN n d .w i = some r) :
    ∃ s', (kGame n k).pairE s (some (true, i)) none = some s'
      ∧ SemiC (goGame n) (kGame n k) s' (PState.live r false false) := by
  obtain ⟨hproj, hallq, hreach⟩ := ksemiC_project hn hsc
  obtain ⟨d', hshape, hmemb, hdisp, -⟩ := (dsemiC_track hn hproj).track
  have hInv := reach_invK hreach
  have hdd : d' = d := by
    rcases hshape with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae; rfl
    · cases hae
  rw [hdd] at hdisp
  have hfin : s.final = false := by
    rcases hshape with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hx : bStep2 n d .b .w none (some i) = some r := hmv
  have hy : bStep2 n d .w .b (some i) none = some r := by
    show (goMoveN n d .w i).bind (fun d1 => bStep n d1 .b none) = some r
    rw [hmv]; rfl
  have hb0 : ∀ j, (none : Option Nat) = some j → j < n*n := by
    intro j hj; cases hj
  have hb1 : ∀ j, (some i : Option Nat) = some j → j < n*n := by
    intro j hj; cases hj; exact hi
  have hcomm := commuteAt_WB hb0 hb1 hx hy
  have ha := assoc_WB hb0 hb1 hy (by rintro ⟨-, hc⟩; cases hc)
  have hdisp2 : SameCells s.disp d := hdisp
  have hav1 : availD n s.disp (some i) = true := by
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi, occ_eq_of_samecells hdisp2 i, hocc]; rfl
  have hqne : s.verdicts ≠ [] := by
    rw [hallq]; intro hcon
    have h2 := congrArg List.length hcon
    rw [List.length_replicate] at h2; simp at h2; omega
  have hEv : (kEv n s none (some i)).isSome :=
    (kEv_isSome_iff s hInv.entInc hqne none (some i)).mpr
      ⟨hfin, rfl, hav1⟩
  have hp : ((kGame n k).pairE s (some (true, i)) none).isSome = true := hEv
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  have hstep := SemiC.step hsc hcomm hs'
  rw [ha] at hstep
  exact ⟨s', hs', hstep⟩

/-! ### The pocket geometry (a far corner, for the aging suicide) -/

/-- The corner pocket intersection and its two walls, plus the walls'
    escape liberties, at the far (bottom-right) corner. -/
def dP  (n : Nat) : Nat := (n-1)*n + (n-1)
def dW1 (n : Nat) : Nat := (n-1)*n + (n-2)
def dW2 (n : Nat) : Nat := (n-2)*n + (n-1)
def dE1 (n : Nat) : Nat := (n-1)*n + (n-3)
def dE2 (n : Nat) : Nat := (n-3)*n + (n-1)

/-- The three products relate by one row of the board. -/
theorem mrel (hn : 5 ≤ n) :
    (n-1)*n + n = n*n ∧ (n-2)*n + n = (n-1)*n ∧ (n-3)*n + n = (n-2)*n := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Nat.succ_mul (n-1) n
    rw [Nat.succ_eq_add_one, show n-1+1 = n from by omega] at h; omega
  · have h := Nat.succ_mul (n-2) n
    rw [Nat.succ_eq_add_one, show n-2+1 = n-1 from by omega] at h; omega
  · have h := Nat.succ_mul (n-3) n
    rw [Nat.succ_eq_add_one, show n-3+1 = n-2 from by omega] at h; omega

/-- Bounds and distinctness of the pocket cells from the witness cells
    {0,1,2,3,n,n+1,n+2} and from each other. -/
theorem pk_bounds (hn : 5 ≤ n) :
    dP n < n*n ∧ dW1 n < n*n ∧ dW2 n < n*n ∧ dE1 n < n*n ∧ dE2 n < n*n := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  simp only [dP, dW1, dW2, dE1, dE2]; omega

theorem adj_W1_P (hn : 5 ≤ n) : adjI n (dW1 n) (dP n) = true := by
  have h := adjI_step_y (n := n) (x := n-1) (y := n-2) (by omega) (by omega)
    (by omega)
  have e : (n-1)*n + ((n-2)+1) = dP n := by simp only [dP]; omega
  rw [e] at h; exact h

theorem adj_W2_P (hn : 5 ≤ n) : adjI n (dW2 n) (dP n) = true := by
  have h := adjI_step_x (n := n) (x := n-2) (y := n-1) (by omega) (by omega)
    (by omega)
  have e : ((n-2)+1)*n + (n-1) = dP n := by
    simp only [dP]; rw [show (n-2)+1 = n-1 from by omega]
  rw [e] at h; exact h

theorem adj_E1_W1 (hn : 5 ≤ n) : adjI n (dE1 n) (dW1 n) = true := by
  have h := adjI_step_y (n := n) (x := n-1) (y := n-3) (by omega) (by omega)
    (by omega)
  have e : (n-1)*n + ((n-3)+1) = dW1 n := by simp only [dW1]; omega
  rw [e] at h; exact h

theorem adj_E2_W2 (hn : 5 ≤ n) : adjI n (dE2 n) (dW2 n) = true := by
  have h := adjI_step_x (n := n) (x := n-3) (y := n-1) (by omega) (by omega)
    (by omega)
  have e : ((n-3)+1)*n + (n-1) = dW2 n := by
    simp only [dW2]; rw [show (n-3)+1 = n-2 from by omega]
  rw [e] at h; exact h

/-- Board-size bounds for the small witness cells at side ≥ 5. -/
theorem sb (hn : 5 ≤ n) : 3 < n*n ∧ 2 < n*n ∧ 1 < n*n ∧ 0 < n*n
    ∧ n < n*n ∧ n+1 < n*n ∧ n+2 < n*n := by
  have h : 5*5 ≤ n*n := Nat.mul_le_mul (by omega) (by omega)
  have h2n : n*2 ≤ n*n := Nat.mul_le_mul_left n (by omega)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Distinctness of the pocket cells from the witness cells and from
    each other (all we need for the kind tables). -/
theorem pk_ne (hn : 5 ≤ n) :
    dW1 n ≠ 0 ∧ dW1 n ≠ 1 ∧ dW1 n ≠ 2 ∧ dW1 n ≠ 3 ∧ dW1 n ≠ n ∧ dW1 n ≠ n+1
      ∧ dW1 n ≠ n+2 ∧ dW1 n ≠ dW2 n
    ∧ dW2 n ≠ 0 ∧ dW2 n ≠ 1 ∧ dW2 n ≠ 2 ∧ dW2 n ≠ 3 ∧ dW2 n ≠ n ∧ dW2 n ≠ n+1
      ∧ dW2 n ≠ n+2
    ∧ dP n ≠ 0 ∧ dP n ≠ 1 ∧ dP n ≠ 2 ∧ dP n ≠ 3 ∧ dP n ≠ n ∧ dP n ≠ n+1
      ∧ dP n ≠ n+2 ∧ dP n ≠ dW1 n ∧ dP n ≠ dW2 n := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  have hnn : n ≤ n*n := Nat.le_mul_of_pos_left n (by omega)
  simp only [dP, dW1, dW2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-- Distinctness of the walls' escape liberties from the witness/pocket
    cells that carry stones (all we need for the suicide's captures). -/
theorem dE_ne (hn : 5 ≤ n) :
    dE1 n ≠ 0 ∧ dE1 n ≠ 1 ∧ dE1 n ≠ 3 ∧ dE1 n ≠ n ∧ dE1 n ≠ dW1 n
      ∧ dE1 n ≠ dW2 n ∧ dE1 n ≠ dP n
    ∧ dE2 n ≠ 0 ∧ dE2 n ≠ 1 ∧ dE2 n ≠ 3 ∧ dE2 n ≠ n ∧ dE2 n ≠ dW1 n
      ∧ dE2 n ≠ dW2 n ∧ dE2 n ≠ dP n := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  have hb : 2*n ≤ (n-3)*n := Nat.mul_le_mul_right n (by omega)
  simp only [dP, dW1, dW2, dE1, dE2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

/-! ### The setup displays (branch diagrams, stamp 0) -/

def kd1 (n : Nat) : Display n := (emptyD n).set 3 (some (.b, 0))
def kd2 (n : Nat) : Display n := (kd1 n).set n (some (.b, 0))
def kd3 (n : Nat) : Display n := (kd2 n).set (dW1 n) (some (.w, 0))
def kd4 (n : Nat) : Display n := (kd3 n).set (dW2 n) (some (.w, 0))
def kd5 (n : Nat) : Display n := (kd4 n).set 0 (some (.w, 0))

theorem kd1_wfd : WFD (kd1 (n := n)) := wfd_set _ _ _ emptyD_wfd
theorem kd2_wfd : WFD (kd2 (n := n)) := wfd_set _ _ _ kd1_wfd
theorem kd3_wfd : WFD (kd3 (n := n)) := wfd_set _ _ _ kd2_wfd
theorem kd4_wfd : WFD (kd4 (n := n)) := wfd_set _ _ _ kd3_wfd
theorem kd5_wfd : WFD (kd5 (n := n)) := wfd_set _ _ _ kd4_wfd

theorem kd1_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (kd1 (n := n)) w = if w = 3 then some .b else none := by
  show kindAt ((emptyD n).set 3 (some (.b, 0))) w = _
  rw [kind_set _ _ (sb hn).1 emptyD_wfd]
  by_cases h : w = 3
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, emptyD_kind]

theorem kd2_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (kd2 (n := n)) w
      = if w = n then some .b else if w = 3 then some .b else none := by
  show kindAt ((kd1 n).set n (some (.b, 0))) w = _
  rw [kind_set _ _ (sb hn).2.2.2.2.1 kd1_wfd]
  by_cases h : w = n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd1_kind hn]

theorem kd3_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (kd3 (n := n)) w
      = if w = dW1 n then some .w else if w = n then some .b
        else if w = 3 then some .b else none := by
  show kindAt ((kd2 n).set (dW1 n) (some (.w, 0))) w = _
  rw [kind_set _ _ (pk_bounds hn).2.1 kd2_wfd]
  by_cases h : w = dW1 n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd2_kind hn]

theorem kd4_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (kd4 (n := n)) w
      = if w = dW2 n then some .w else if w = dW1 n then some .w
        else if w = n then some .b else if w = 3 then some .b else none := by
  show kindAt ((kd3 n).set (dW2 n) (some (.w, 0))) w = _
  rw [kind_set _ _ (pk_bounds hn).2.2.1 kd3_wfd]
  by_cases h : w = dW2 n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd3_kind hn]

theorem kd5_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (kd5 (n := n)) w
      = if w = 0 then some .w else if w = dW2 n then some .w
        else if w = dW1 n then some .w else if w = n then some .b
        else if w = 3 then some .b else none := by
  show kindAt ((kd4 n).set 0 (some (.w, 0))) w = _
  rw [kind_set _ _ (sb hn).2.2.2.1 kd4_wfd]
  by_cases h : w = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd4_kind hn]

/-! ### The setup moves (quiet single placements) -/

theorem adj_2_3 (hn : 5 ≤ n) : adjI n 2 3 = true := by
  have h := adjI_step_y (n := n) (x := 0) (y := 2) (by omega) (by omega)
    (by omega)
  have e : 0*n + 2 = 2 := by omega
  have e1 : 0*n + (2+1) = 3 := by omega
  rw [e, e1] at h; exact h

/-- A component has a liberty: p carries kind k and q is an empty
    neighbor. -/
theorem has_lib (D : Display n) (p q : Nat) (k : DKind) (hq : q < n*n)
    (hqocc : occD D q = false) (hkp : kindAt D p = some k)
    (hadj : adjI n q p = true) :
    noLibD D (componentD D p) = false :=
  (noLibD_eq_false_iff _ _).mpr
    ⟨q, List.mem_range.mpr hq, hqocc, p, componentD_mem_self D p k hkp, hadj⟩

/-- Emptiness helpers for the setup displays. -/
theorem kd2_none (hn : 5 ≤ n) {w : Nat} (hnn : w ≠ n) (h3 : w ≠ 3) :
    occD (kd2 (n := n)) w = false :=
  occ_of_kind_eq (by rw [kd2_kind hn, if_neg hnn, if_neg h3])
theorem kd3_none (hn : 5 ≤ n) {w : Nat} (hd1 : w ≠ dW1 n) (hnn : w ≠ n)
    (h3 : w ≠ 3) : occD (kd3 (n := n)) w = false :=
  occ_of_kind_eq (by rw [kd3_kind hn, if_neg hd1, if_neg hnn, if_neg h3])
theorem kd4_none (hn : 5 ≤ n) {w : Nat} (hd2 : w ≠ dW2 n) (hd1 : w ≠ dW1 n)
    (hnn : w ≠ n) (h3 : w ≠ 3) : occD (kd4 (n := n)) w = false :=
  occ_of_kind_eq (by rw [kd4_kind hn, if_neg hd2, if_neg hd1, if_neg hnn,
    if_neg h3])
theorem kd5_none (hn : 5 ≤ n) {w : Nat} (h0 : w ≠ 0) (hd2 : w ≠ dW2 n)
    (hd1 : w ≠ dW1 n) (hnn : w ≠ n) (h3 : w ≠ 3) :
    occD (kd5 (n := n)) w = false :=
  occ_of_kind_eq (by rw [kd5_kind hn, if_neg h0, if_neg hd2, if_neg hd1,
    if_neg hnn, if_neg h3])

theorem km1 (hn : 5 ≤ n) : goMoveN n (emptyD n) .b 3 = some (kd1 (n := n)) := by
  have hpl : placedN n (emptyD n) .b 3 = kd1 (n := n) := rfl
  have hdead : deadOppN n (emptyD n) .b 3 = [] := by
    apply deadOpp_nil_of
    intro p hk
    exfalso
    rw [hpl, kd1_kind hn] at hk
    by_cases h3 : p = 3 <;> simp [h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ emptyD_wfd (occ_of_kind_eq (emptyD_kind 3))
    hdead (suicideN_false_of _ _ _ emptyD_wfd (sb hn).1 (by intro h; cases h)
      hdead ?_)
  rw [hpl]
  exact has_lib _ 3 2 .b (sb hn).2.1
    (occ_of_kind_eq (by rw [kd1_kind hn, if_neg (by omega)]))
    (by rw [kd1_kind hn, if_pos rfl]) (adj_2_3 hn)

theorem km2 (hn : 5 ≤ n) : goMoveN n (kd1 (n := n)) .b n = some (kd2 (n := n)) := by
  have hpl : placedN n (kd1 (n := n)) .b n = kd2 (n := n) := rfl
  have hdead : deadOppN n (kd1 (n := n)) .b n = [] := by
    apply deadOpp_nil_of
    intro p hk
    exfalso
    rw [hpl, kd2_kind hn] at hk
    by_cases hnn : p = n <;> by_cases h3 : p = 3 <;> simp [hnn, h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ kd1_wfd
    (occ_of_kind_eq (by rw [kd1_kind hn, if_neg (by omega)]))
    hdead (suicideN_false_of _ _ _ kd1_wfd (sb hn).2.2.2.2.1
      (by intro h; cases h) hdead ?_)
  rw [hpl]
  exact has_lib _ n (n+1) .b (sb hn).2.2.2.2.2.1
    (kd2_none hn (by omega) (by omega))
    (by rw [kd2_kind hn, if_pos rfl]) (adjI_symm (adj_n_n1 (by omega)))

theorem km3 (hn : 5 ≤ n) :
    goMoveN n (kd2 (n := n)) .w (dW1 n) = some (kd3 (n := n)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hpl : placedN n (kd2 (n := n)) .w (dW1 n) = kd3 (n := n) := rfl
  have hdead : deadOppN n (kd2 (n := n)) .w (dW1 n) = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl, kd3_kind hn] at hk
    by_cases hd1 : p = dW1 n
    · simp [hd1, DKind.opp] at hk
    · by_cases hnn : p = n
      · rw [hpl, hnn]
        exact has_lib _ n (n+1) .b (sb hn).2.2.2.2.2.1
          (kd3_none hn (Ne.symm hw1_n1) (by omega) (by omega))
          (by rw [kd3_kind hn, if_neg (Ne.symm hw1_n), if_pos rfl])
          (adjI_symm (adj_n_n1 (by omega)))
      · by_cases h3 : p = 3
        · subst h3
          rw [hpl]
          exact has_lib _ 3 2 .b (sb hn).2.1
            (kd3_none hn (Ne.symm hw1_2) (by omega) (by omega))
            (by rw [kd3_kind hn, if_neg (Ne.symm hw1_3), if_neg (by omega),
              if_pos rfl]) (adj_2_3 hn)
        · simp [hd1, hnn, h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ kd2_wfd (kd2_none hn hw1_n hw1_3)
    hdead (suicideN_false_of _ _ _ kd2_wfd (pk_bounds hn).2.1
      (by intro h; cases h) hdead ?_)
  rw [hpl]
  exact has_lib _ (dW1 n) (dP n) .w (pk_bounds hn).1
    (kd3_none hn hp_w1 hp_n hp_3)
    (by rw [kd3_kind hn, if_pos rfl]) (adjI_symm (adj_W1_P hn))

theorem km4 (hn : 5 ≤ n) :
    goMoveN n (kd3 (n := n)) .w (dW2 n) = some (kd4 (n := n)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hpl : placedN n (kd3 (n := n)) .w (dW2 n) = kd4 (n := n) := rfl
  have hdead : deadOppN n (kd3 (n := n)) .w (dW2 n) = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl, kd4_kind hn] at hk
    by_cases hd2 : p = dW2 n
    · simp [hd2, DKind.opp] at hk
    · by_cases hd1 : p = dW1 n
      · simp [hd1, hd2, DKind.opp] at hk
      · by_cases hnn : p = n
        · rw [hpl, hnn]
          exact has_lib _ n (n+1) .b (sb hn).2.2.2.2.2.1
            (kd4_none hn (Ne.symm hw2_n1) (Ne.symm hw1_n1) (by omega) (by omega))
            (by rw [kd4_kind hn, if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n),
              if_pos rfl]) (adjI_symm (adj_n_n1 (by omega)))
        · by_cases h3 : p = 3
          · subst h3
            rw [hpl]
            exact has_lib _ 3 2 .b (sb hn).2.1
              (kd4_none hn (Ne.symm hw2_2) (Ne.symm hw1_2) (by omega) (by omega))
              (by rw [kd4_kind hn, if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3),
                if_neg (by omega), if_pos rfl]) (adj_2_3 hn)
          · simp [hd2, hd1, hnn, h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ kd3_wfd (kd3_none hn (Ne.symm hw1_w2) hw2_n hw2_3)
    hdead (suicideN_false_of _ _ _ kd3_wfd (pk_bounds hn).2.2.1
      (by intro h; cases h) hdead ?_)
  rw [hpl]
  exact has_lib _ (dW2 n) (dP n) .w (pk_bounds hn).1
    (kd4_none hn hp_w2 hp_w1 hp_n hp_3)
    (by rw [kd4_kind hn, if_pos rfl]) (adjI_symm (adj_W2_P hn))

theorem km5 (hn : 5 ≤ n) :
    goMoveN n (kd4 (n := n)) .w 0 = some (kd5 (n := n)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hpl : placedN n (kd4 (n := n)) .w 0 = kd5 (n := n) := rfl
  have hdead : deadOppN n (kd4 (n := n)) .w 0 = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl, kd5_kind hn] at hk
    by_cases h0 : p = 0
    · simp [h0, DKind.opp] at hk
    · by_cases hd2 : p = dW2 n
      · simp [hd2, h0, DKind.opp] at hk
      · by_cases hd1 : p = dW1 n
        · simp [hd1, hd2, h0, DKind.opp] at hk
        · by_cases hnn : p = n
          · rw [hpl, hnn]
            exact has_lib _ n (n+1) .b (sb hn).2.2.2.2.2.1
              (kd5_none hn (by omega) (Ne.symm hw2_n1) (Ne.symm hw1_n1)
                (by omega) (by omega))
              (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_n),
                if_neg (Ne.symm hw1_n), if_pos rfl])
              (adjI_symm (adj_n_n1 (by omega)))
          · by_cases h3 : p = 3
            · subst h3
              rw [hpl]
              exact has_lib _ 3 2 .b (sb hn).2.1
                (kd5_none hn (by omega) (Ne.symm hw2_2) (Ne.symm hw1_2)
                  (by omega) (by omega))
                (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_3),
                  if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl])
                (adj_2_3 hn)
            · simp [h0, hd2, hd1, hnn, h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ kd4_wfd
    (kd4_none hn (Ne.symm hw2_0) (Ne.symm hw1_0) (by omega) (by omega))
    hdead (suicideN_false_of _ _ _ kd4_wfd (sb hn).2.2.2.1
      (by intro h; cases h) hdead ?_)
  rw [hpl]
  exact has_lib _ 0 1 .w (sb hn).2.2.1
    (kd5_none hn (by omega) (Ne.symm hw2_1) (Ne.symm hw1_1) (by omega) (by omega))
    (by rw [kd5_kind hn, if_pos rfl]) (adjI_symm (adj_0_1 (by omega)))

/-! ### The semiclassical setup state -/

/-- Five commuting single moves reach a semiclassical k-DSGo state
    whose display carries the witness cells (kd5). -/
theorem setup_reach (hn : 5 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    ∃ s0, SemiC (goGame n) (kGame n k) s0
      (PState.live (kd5 (n := n)) false false) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hn2 : 2 ≤ n := by omega
  have h0 : SemiC (goGame n) (kGame n k) (kGame n k).q0
      (PState.live (emptyD n) false false) := SemiC.init
  obtain ⟨s1, -, hsc1⟩ := ksemi_step_B hn2 hk h0 (sb hn).1
    (occ_of_kind_eq (emptyD_kind 3)) (km1 hn)
  obtain ⟨s2, -, hsc2⟩ := ksemi_step_B hn2 hk hsc1 (sb hn).2.2.2.2.1
    (occ_of_kind_eq (by rw [kd1_kind hn, if_neg (by omega)])) (km2 hn)
  obtain ⟨s3, -, hsc3⟩ := ksemi_step_W hn2 hk hsc2 (pk_bounds hn).2.1
    (kd2_none hn hw1_n hw1_3) (km3 hn)
  obtain ⟨s4, -, hsc4⟩ := ksemi_step_W hn2 hk hsc3 (pk_bounds hn).2.2.1
    (kd3_none hn (Ne.symm hw1_w2) hw2_n hw2_3) (km4 hn)
  obtain ⟨s5, -, hsc5⟩ := ksemi_step_W hn2 hk hsc4 (sb hn).2.2.2.1
    (kd4_none hn (Ne.symm hw2_0) (Ne.symm hw1_0) (by omega) (by omega)) (km5 hn)
  exact ⟨s5, hsc5⟩

/-! ### The collision branches -/

/-- The white-joins branch a1: White plays A2, keeping A1. -/
def ba1 (n : Nat) : Display n := (kd5 (n := n)).set 1 (some (.w, 0))
/-- The black-captures branch a0: Black plays A2, capturing A1. -/
def ba0 (n : Nat) : Display n :=
  ((kd5 (n := n)).set 1 (some (.b, 0))).set 0 none

theorem ba1_wfd : WFD (ba1 (n := n)) := wfd_set _ _ _ kd5_wfd
theorem ba0_wfd : WFD (ba0 (n := n)) := wfd_set _ _ _ (wfd_set _ _ _ kd5_wfd)

theorem ba1_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba1 (n := n)) w
      = if w = 1 then some .w else if w = 0 then some .w
        else if w = dW2 n then some .w else if w = dW1 n then some .w
        else if w = n then some .b else if w = 3 then some .b else none := by
  show kindAt ((kd5 n).set 1 (some (.w, 0))) w = _
  rw [kind_set _ _ (sb hn).2.2.1 kd5_wfd]
  by_cases h : w = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd5_kind hn]

theorem ba0_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba0 (n := n)) w
      = if w = 0 then none else if w = 1 then some .b
        else if w = dW2 n then some .w else if w = dW1 n then some .w
        else if w = n then some .b else if w = 3 then some .b else none := by
  show kindAt (((kd5 n).set 1 (some (.b, 0))).set 0 none) w = _
  rw [show kindAt (((kd5 n).set 1 (some (.b, 0))).set 0 none) w
      = if w = 0 then none else kindAt ((kd5 n).set 1 (some (.b, 0))) w from by
    by_cases h : w = 0
    · subst h; rw [if_pos rfl]; unfold kindAt
      rw [get_set_self _ _ _ (by rw [set_size, kd5_wfd]; exact (sb hn).2.2.2.1)]
      rfl
    · rw [if_neg h]; unfold kindAt; rw [get_set_ne _ _ _ _ h]]
  by_cases h0 : w = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, kind_set _ _ (sb hn).2.2.1 kd5_wfd]
    by_cases h1 : w = 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, kd5_kind hn, if_neg h0]

/-- The placement diagram kd5 + Black@A2 (before capture). -/
theorem pd1_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (placedN n (kd5 (n := n)) .b 1) w
      = if w = 1 then some .b else if w = 0 then some .w
        else if w = dW2 n then some .w else if w = dW1 n then some .w
        else if w = n then some .b else if w = 3 then some .b else none := by
  show kindAt ((kd5 n).set 1 (some (.b, 0))) w = _
  rw [kind_set _ _ (sb hn).2.2.1 kd5_wfd]
  by_cases h : w = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, kd5_kind hn]

theorem gmw1 (hn : 5 ≤ n) :
    goMoveN n (kd5 (n := n)) .w 1 = some (ba1 (n := n)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hpl : placedN n (kd5 (n := n)) .w 1 = ba1 (n := n) := rfl
  have hdead : deadOppN n (kd5 (n := n)) .w 1 = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl, ba1_kind hn] at hk
    by_cases h1 : p = 1
    · simp [h1, DKind.opp] at hk
    · by_cases h0 : p = 0
      · simp [h0, h1, DKind.opp] at hk
      · by_cases hd2 : p = dW2 n
        · simp [hd2, h0, h1, DKind.opp] at hk
        · by_cases hd1 : p = dW1 n
          · simp [hd1, hd2, h0, h1, DKind.opp] at hk
          · by_cases hnn : p = n
            · rw [hpl, hnn]
              exact has_lib _ n (n+1) .b (sb hn).2.2.2.2.2.1
                (occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega),
                  if_neg (by omega), if_neg (Ne.symm hw2_n1),
                  if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)]))
                (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
                  if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl])
                (adjI_symm (adj_n_n1 (by omega)))
            · by_cases h3 : p = 3
              · subst h3
                rw [hpl]
                exact has_lib _ 3 2 .b (sb hn).2.1
                  (occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega),
                    if_neg (by omega), if_neg (Ne.symm hw2_2),
                    if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]))
                  (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
                    if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3),
                    if_neg (by omega), if_pos rfl])
                  (adj_2_3 hn)
              · simp [h1, h0, hd2, hd1, hnn, h3, DKind.opp] at hk
  refine goMoveN_quiet _ _ _ kd5_wfd
    (occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_1),
      if_neg (Ne.symm hw1_1), if_neg (by omega), if_neg (by omega)]))
    hdead (suicideN_false_of _ _ _ kd5_wfd (sb hn).2.2.1
      (by intro h; cases h) hdead ?_)
  rw [hpl]
  exact has_lib _ 1 2 .w (sb hn).2.1
    (occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega),
      if_neg (by omega)]))
    (by rw [ba1_kind hn, if_pos rfl]) (adjI_symm (adj_1_2 (by omega)))

theorem pd1_none (hn : 5 ≤ n) {w : Nat} (h1 : w ≠ 1) (h0 : w ≠ 0)
    (hd2 : w ≠ dW2 n) (hd1 : w ≠ dW1 n) (hnn : w ≠ n) (h3 : w ≠ 3) :
    occD (placedN n (kd5 (n := n)) .b 1) w = false :=
  occ_of_kind_eq (by rw [pd1_kind hn, if_neg h1, if_neg h0, if_neg hd2,
    if_neg hd1, if_neg hnn, if_neg h3])

/-- Black@A2 captures exactly A1. -/
theorem dead_b1 (hn : 5 ≤ n) {p : Nat} :
    p ∈ deadOppN n (kd5 (n := n)) .b 1 ↔ p = 0 := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  rw [mem_deadOppN_iff]
  constructor
  · rintro ⟨-, hk, hnl⟩
    rw [pd1_kind hn] at hk
    by_cases h0 : p = 0
    · exact h0
    · exfalso
      by_cases h1 : p = 1
      · rw [if_pos h1] at hk; simp [DKind.opp] at hk
      · by_cases hd2 : p = dW2 n
        · subst hd2
          have hlib : noLibD (placedN n (kd5 n) .b 1)
              (componentD (placedN n (kd5 n) .b 1) (dW2 n)) = false :=
            has_lib _ (dW2 n) (dP n) .w (pk_bounds hn).1
              (pd1_none hn (by omega) hp_0 hp_w2 hp_w1 hp_n hp_3)
              (by rw [pd1_kind hn, if_neg hw2_1, if_neg hw2_0,
                if_pos rfl]) (adjI_symm (adj_W2_P hn))
          rw [hlib] at hnl; cases hnl
        · by_cases hd1 : p = dW1 n
          · subst hd1
            have hlib : noLibD (placedN n (kd5 n) .b 1)
                (componentD (placedN n (kd5 n) .b 1) (dW1 n)) = false :=
              has_lib _ (dW1 n) (dP n) .w (pk_bounds hn).1
                (pd1_none hn (by omega) hp_0 hp_w2 hp_w1 hp_n hp_3)
                (by rw [pd1_kind hn, if_neg hw1_1, if_neg hw1_0,
                  if_neg hw1_w2, if_pos rfl]) (adjI_symm (adj_W1_P hn))
            rw [hlib] at hnl; cases hnl
          · rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1] at hk
            by_cases hnn : p = n
            · rw [if_pos hnn] at hk; simp [DKind.opp] at hk
            · by_cases h3 : p = 3
              · rw [if_neg hnn, if_pos h3] at hk; simp [DKind.opp] at hk
              · rw [if_neg hnn, if_neg h3] at hk; cases hk
  · intro h0
    subst h0
    refine ⟨List.mem_range.mpr (sb hn).2.2.2.1, ?_, ?_⟩
    · show kindAt (placedN n (kd5 n) .b 1) 0 = some DKind.w
      rw [pd1_kind hn, if_neg (by omega), if_pos rfl]
    · apply noLibD_true_of
      intro q hq hocc m hm hadj
      have hcs := comp_singleton (placedN n (kd5 n) .b 1) 0 .w
        (by rw [pd1_kind hn, if_neg (by omega), if_pos rfl])
        (by intro r hr hadjr
            rcases nbr_0 (by omega) hadjr with h | h
            · rw [h, pd1_kind hn, if_pos rfl]; decide
            · rw [h, pd1_kind hn, if_neg (by omega), if_neg (by omega),
                if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl]
              decide)
      have hm0 : m = 0 := (hcs m).mp hm
      subst hm0
      rcases nbr_0 (by omega) hadj with h | h
      · rw [h, occ_true_of_kind (show kindAt (placedN n (kd5 n) .b 1) 1
          = some .b from by rw [pd1_kind hn, if_pos rfl])] at hocc
        exact Bool.noConfusion hocc
      · rw [h, occ_true_of_kind (show kindAt (placedN n (kd5 n) .b 1) n
          = some .b from by rw [pd1_kind hn, if_neg (by omega), if_neg (by omega),
            if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl])] at hocc
        exact Bool.noConfusion hocc

/-- After the capture, the display is exactly ba0. -/
theorem afterCap_b1 (hn : 5 ≤ n) :
    afterCapN n (kd5 (n := n)) .b 1 = ba0 (n := n) := by
  have hsz : (afterCapN n (kd5 (n := n)) .b 1).cells.size = n*n := by
    unfold afterCapN; simp [Array.size_map, Array.size_range]
  have hba0 : ∀ p, p ≠ 0 → (ba0 (n := n)).get p
      = (placedN n (kd5 (n := n)) .b 1).get p := by
    intro p hp0
    show (((kd5 n).set 1 (some (.b, 0))).set 0 none).get p
      = ((kd5 n).set 1 (some (.b, 0))).get p
    rw [get_set_ne _ _ _ _ hp0]
  apply display_ext; apply Array.ext
  · rw [hsz, show (ba0 (n := n)).cells.size = n*n from by
      unfold ba0; rw [set_size, set_size]; exact kd5_wfd]
  · intro p h1 h2
    have hib : p < n*n := by omega
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
    show (afterCapN n (kd5 (n := n)) .b 1).get p = (ba0 (n := n)).get p
    rw [afterCapN_get, if_pos hib]
    by_cases hp0 : p = 0
    · rw [if_pos (List.contains_iff_mem.mpr ((dead_b1 hn).mpr hp0))]
      rw [hp0]
      show none = (((kd5 n).set 1 (some (.b, 0))).set 0 none).get 0
      rw [get_set_self _ _ _ (by rw [set_size, kd5_wfd]; exact (sb hn).2.2.2.1)]
    · rw [if_neg (by intro hc; exact hp0 ((dead_b1 hn).mp
        (List.contains_iff_mem.mp hc)))]
      exact (hba0 p hp0).symm

theorem gmb1 (hn : 5 ≤ n) :
    goMoveN n (kd5 (n := n)) .b 1 = some (ba0 (n := n)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hsui : suicideN n (kd5 (n := n)) .b 1 = false := by
    show noLibD (afterCapN n (kd5 (n := n)) .b 1)
      (componentD (afterCapN n (kd5 (n := n)) .b 1) 1) = false
    rw [afterCap_b1 hn]
    exact has_lib _ 1 0 .b (sb hn).2.2.2.1
      (occ_of_kind_eq (by rw [ba0_kind hn, if_pos rfl]))
      (by rw [ba0_kind hn, if_neg (by omega), if_pos rfl])
      (adj_0_1 (by omega))
  unfold goMoveN
  rw [occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_1),
    if_neg (Ne.symm hw1_1), if_neg (by omega), if_neg (by omega)])]
  simp only [Bool.false_eq_true, if_false, hsui]
  rw [afterCap_b1 hn]

/-- A move onto an occupied intersection is undefined. -/
theorem goMoveN_occ_none (d : Display n) (c : DKind) (i : Nat)
    (h : occD d i = true) : goMoveN n d c i = none := by
  unfold goMoveN; rw [if_pos h]

/-- serialP when neither composite is defined but both single moves
    are — proved at the abstract display so no capture reduction fires. -/
theorem serialP_none_none {a : Display n} {m0 m1 : Option Nat}
    {x y : Display n}
    (h1 : bStep2 n a .b .w m0 m1 = none) (h2 : bStep2 n a .w .b m1 m0 = none)
    (hx : bStep n a .b m0 = some x) (hy : bStep n a .w m1 = some y) :
    serialP n a m0 m1 = some (dedupD n [x, y]) := by
  unfold serialP
  rw [h1, h2, hx, hy]

set_option maxHeartbeats 800000 in
/-- The collision A2/A2 serializes to the two branches. -/
theorem coll_serialP (hn : 5 ≤ n) :
    serialP n (kd5 (n := n)) (some 1) (some 1)
      = some (dedupD n [ba0 (n := n), ba1 (n := n)]) := by
  have e2b : goMoveN n (ba0 n) .w 1 = none :=
    goMoveN_occ_none (ba0 n) .w 1 (occ_true_of_kind
      (show kindAt (ba0 (n := n)) 1 = some .b from by
        rw [ba0_kind hn, if_neg (by omega), if_pos rfl]))
  have e2w : goMoveN n (ba1 n) .b 1 = none :=
    goMoveN_occ_none (ba1 n) .b 1 (occ_true_of_kind
      (show kindAt (ba1 (n := n)) 1 = some .w from by rw [ba1_kind hn, if_pos rfl]))
  have hbw : bStep2 n (kd5 (n := n)) .b .w (some 1) (some 1) = none := by
    simp only [bStep2, bStep, gmb1 hn, e2b, Option.some_bind]
  have hwb : bStep2 n (kd5 (n := n)) .w .b (some 1) (some 1) = none := by
    simp only [bStep2, bStep, gmw1 hn, e2w, Option.some_bind]
  exact serialP_none_none hbw hwb (gmb1 hn) (gmw1 hn)

/-! ### General delta-fixpoint machinery -/

/-- `any` over a list that is exactly the pair {x, y}. -/
theorem any_pair {M : List (Display n)} {x y : Display n}
    (hx : x ∈ M) (hy : y ∈ M) (hall : ∀ b, b ∈ M → b = x ∨ b = y)
    (p : Display n → Bool) : M.any p = (p x || p y) := by
  cases hM : M.any p with
  | true =>
    rcases List.any_eq_true.mp hM with ⟨b, hb, hpb⟩
    rcases hall b hb with rfl | rfl
    · rw [hpb]; rfl
    · rw [hpb]; simp
  | false =>
    have hpx : p x = false := by
      cases hpx : p x with
      | false => rfl
      | true => rw [List.any_eq_true.mpr ⟨x, hx, hpx⟩] at hM; cases hM
    have hpy : p y = false := by
      cases hpy : p y with
      | false => rfl
      | true => rw [List.any_eq_true.mpr ⟨y, hy, hpy⟩] at hM; cases hM
    simp [hpx, hpy]

/-- A display is a round fixpoint if every stone is kept. -/
theorem deltaRound_fix {t : Nat} {Dp : Display n} {M : List (Display n)}
    (hwf : WFD Dp)
    (h : ∀ i, i < n*n → ∀ kk st, Dp.get i = some (kk, st) →
      (deltaRound n t M Dp).get i = some (kk, st)) :
    deltaRound n t M Dp = Dp := by
  apply display_ext; apply Array.ext
  · exact (dR_wfd t M Dp).trans hwf.symm
  · intro i h1 h2
    have hin : i < n*n := by rw [← dR_wfd t M Dp]; exact h1
    rw [← get_in_bounds (deltaRound n t M Dp) i (by rw [dR_wfd t M Dp]; exact hin),
        ← get_in_bounds Dp i (by rw [hwf]; exact hin)]
    cases hg : Dp.get i with
    | none => rw [dR_get_none t M Dp hin hg]
    | some c => obtain ⟨kk, st⟩ := c; rw [h i hin kk st hg]

/-- At a round fixpoint the recursion stops in one step. -/
theorem delta_fix {t : Nat} {Dp : Display n} {M : List (Display n)}
    (hfix : deltaRound n t M Dp = Dp) :
    delta n t Dp M = (Dp, recut n Dp M) :=
  deltaAux_fix t (2*(n*n)+1) Dp M hfix

/-! ### The collision result state -/

/-- The collision display: the setup display with a q-stone at A2. -/
def Dcol (D : Display n) (t0 : Nat) : Display n := D.set 1 (some (.r, t0))

theorem Dcol_kind (hn : 5 ≤ n) {D : Display n} (hsc : SameCells D (kd5 n))
    (hwf : WFD D) (t0 w : Nat) :
    kindAt (Dcol D t0) w
      = if w = 1 then some .r else kindAt (kd5 (n := n)) w := by
  show kindAt (D.set 1 (some (.r, t0))) w = _
  rw [kind_set _ _ (sb hn).2.2.1 hwf]
  by_cases h : w = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, hsc]

/-- ev of the two-branch entanglement, read off ba0/ba1. -/
theorem evSet_pair (hn : 5 ≤ n) {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n) (i : Nat) :
    evSet n dec i
      = ((kindAt (ba0 n) i == some .b) || (kindAt (ba1 n) i == some .b),
         (kindAt (ba0 n) i == some .w) || (kindAt (ba1 n) i == some .w)) := by
  have hx : ba0 n ∈ dec := (hdec _).mpr (Or.inl rfl)
  have hy : ba1 n ∈ dec := (hdec _).mpr (Or.inr rfl)
  show ((dec.any fun b => kindAt b i == some .b),
        (dec.any fun b => kindAt b i == some .w)) = _
  rw [any_pair hx hy (fun b hb => (hdec b).mp hb),
      any_pair hx hy (fun b hb => (hdec b).mp hb)]

/-- The collision display is a Δ-round fixpoint of the two-branch
    entanglement: every stone is backed and the q-stone is two-color. -/
theorem dcol_round_fix (hn : 5 ≤ n) {D : Display n} (hsc : SameCells D (kd5 n))
    (hwf : WFD D) (tr t0 : Nat) {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n) :
    deltaRound n tr dec (Dcol D t0) = Dcol D t0 := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hwfc : WFD (Dcol D t0) := wfd_set _ _ _ hwf
  apply deltaRound_fix hwfc
  intro i hi kk st hg
  have hk : kindAt (Dcol D t0) i = some kk := by unfold kindAt; rw [hg]; rfl
  rw [Dcol_kind hn hsc hwf] at hk
  by_cases h1 : i = 1
  · -- the q-stone: two-color ev keeps it
    subst h1
    have hkr : kk = DKind.r := by rw [if_pos rfl] at hk; exact (Option.some.inj hk).symm
    subst hkr
    have hev : evSet n dec 1 = (true, true) := by
      rw [evSet_pair hn hdec 1,
        show kindAt (ba0 n) 1 = some .b from by rw [ba0_kind hn, if_neg (by omega), if_pos rfl],
        show kindAt (ba1 n) 1 = some .w from by rw [ba1_kind hn, if_pos rfl]]; rfl
    rw [dR_get_pair tr dec (Dcol D t0) hi hg hev]
    simp
  · rw [if_neg h1, kd5_kind hn] at hk
    -- non-collision cells: dR_keep_cell with the matching ev
    have key : ∀ (kc : DKind), kk = kc → kc ≠ .r →
        evSet n dec i = ((kc == DKind.b), (kc == DKind.w)) →
        (deltaRound n tr dec (Dcol D t0)).get i = some (kk, st) := by
      intro kc hkc hkr hev
      subst hkc
      exact dR_keep_cell tr dec (Dcol D t0) hi hg hkr hev
    by_cases h0 : i = 0
    · subst h0
      exact key .w (by rw [if_pos rfl] at hk; exact (Option.some.inj hk).symm)
        (by decide) (by rw [evSet_pair hn hdec 0,
          show kindAt (ba0 n) 0 = none from by rw [ba0_kind hn, if_pos rfl],
          show kindAt (ba1 n) 0 = some .w from by rw [ba1_kind hn, if_neg (by omega), if_pos rfl]]; rfl)
    · by_cases hd2 : i = dW2 n
      · subst hd2
        exact key .w (by rw [if_neg hw2_0, if_pos rfl] at hk; exact (Option.some.inj hk).symm)
          (by decide) (by rw [evSet_pair hn hdec (dW2 n),
            show kindAt (ba0 n) (dW2 n) = some .w from by rw [ba0_kind hn, if_neg hw2_0, if_neg hw2_1, if_pos rfl],
            show kindAt (ba1 n) (dW2 n) = some .w from by rw [ba1_kind hn, if_neg hw2_1, if_neg hw2_0, if_pos rfl]]; rfl)
      · by_cases hd1 : i = dW1 n
        · subst hd1
          exact key .w (by rw [if_neg hw1_0, if_neg hw1_w2, if_pos rfl] at hk; exact (Option.some.inj hk).symm)
            (by decide) (by rw [evSet_pair hn hdec (dW1 n),
              show kindAt (ba0 n) (dW1 n) = some .w from by rw [ba0_kind hn, if_neg hw1_0, if_neg hw1_1, if_neg hw1_w2, if_pos rfl],
              show kindAt (ba1 n) (dW1 n) = some .w from by rw [ba1_kind hn, if_neg hw1_1, if_neg hw1_0, if_neg hw1_w2, if_pos rfl]]; rfl)
        · by_cases hnn : i = n
          · refine key .b ?_ (by decide) ?_
            · rw [hnn, if_neg (by omega), if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl] at hk
              exact (Option.some.inj hk).symm
            · rw [hnn, evSet_pair hn hdec n,
                show kindAt (ba0 n) n = some .b from by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl],
                show kindAt (ba1 n) n = some .b from by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl]]
              rfl
          · by_cases h3 : i = 3
            · subst h3
              exact key .b (by rw [if_neg (by omega), if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl] at hk; exact (Option.some.inj hk).symm)
                (by decide) (by rw [evSet_pair hn hdec 3,
                  show kindAt (ba0 n) 3 = some .b from by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl],
                  show kindAt (ba1 n) 3 = some .b from by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]]; rfl)
            · exfalso
              rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at hk
              cases hk

/-- The round's value at a cell depends only on the input there. -/
theorem dR_get_congr (t : Nat) (M : List (Display n)) (D D' : Display n) (i : Nat)
    (h : D.get i = D'.get i) :
    (deltaRound n t M D).get i = (deltaRound n t M D').get i := by
  by_cases hi : i < n*n
  · rw [dR_get_in t M D hi, dR_get_in t M D' hi, h]
  · rw [dR_get_oob t M D hi, dR_get_oob t M D' hi]

/-- The pocket-suicide round: from the collision display with a lone
    unbacked black stone dropped in the corner pocket, the removal round
    discards the pocket stone and reproduces the collision display. -/
theorem pad_round (hn : 5 ≤ n) {D : Display n} (hsc : SameCells D (kd5 n))
    (hwf : WFD D) (tr t0 : Nat) {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n) :
    deltaRound n tr dec ((Dcol D t0).set (dP n) (some (.b, tr)))
      = Dcol D t0 := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hwfc : WFD (Dcol D t0) := wfd_set _ _ _ hwf
  have hround := dcol_round_fix hn hsc hwf tr t0 hdec
  have hdPlt : dP n < n*n := (pk_bounds hn).1
  have hev : evSet n dec (dP n) = (false, false) := by
    rw [evSet_pair hn hdec (dP n),
      show kindAt (ba0 n) (dP n) = none from by
        rw [ba0_kind hn, if_neg hp_0, if_neg hp_1, if_neg hp_w2, if_neg hp_w1,
          if_neg hp_n, if_neg hp_3],
      show kindAt (ba1 n) (dP n) = none from by
        rw [ba1_kind hn, if_neg hp_1, if_neg hp_0, if_neg hp_w2, if_neg hp_w1,
          if_neg hp_n, if_neg hp_3]]
    rfl
  have hdPnone : (Dcol D t0).get (dP n) = none := by
    rw [Dcol, get_set_ne _ _ _ _ hp_1]
    exact Option.map_eq_none'.mp (by
      show kindAt D (dP n) = none
      rw [hsc, kd5_kind hn, if_neg hp_0, if_neg hp_w2, if_neg hp_w1,
        if_neg hp_n, if_neg hp_3])
  apply display_ext; apply Array.ext
  · rw [dR_wfd, hwfc]
  · intro i h1 h2
    have hin : i < n*n := by rw [← dR_wfd tr dec _]; exact h1
    rw [← get_in_bounds _ i (by rw [dR_wfd]; exact hin),
        ← get_in_bounds (Dcol D t0) i (by rw [hwfc]; exact hin)]
    by_cases hdp : i = dP n
    · subst hdp
      rw [dR_get_in tr dec _ hin,
        get_set_self _ _ _ (by rw [hwfc]; exact hin), hev, hdPnone]
      rfl
    · rw [dR_get_congr tr dec _ (Dcol D t0) i (get_set_ne _ _ _ _ hdp),
        hround]

/-- A one-point suicide is a no-op: placing a color at a cell whose own
    component becomes the lone dead group (capturing nothing) returns the
    board unchanged. -/
theorem goMoveN_suicide (d : Display n) (c : DKind) (i : Nat)
    (hwf : WFD d) (hemp : occD d i = false)
    (hdead : deadOppN n d c i = [])
    (hsui : suicideN n d c i = true)
    (hcomp : ∀ q, q ∈ ownCompN n d c i ↔ q = i) :
    goMoveN n d c i = some d := by
  have hdi : d.get i = none := by
    rcases hg : d.get i with _ | cc
    · rfl
    · exact absurd hemp (by simp [occD, hg])
  unfold goMoveN
  rw [hemp]
  simp only [Bool.false_eq_true, if_false, hsui, if_true, Option.some.injEq]
  apply display_ext; apply Array.ext
  · rw [erasedN_size]; exact hwf.symm
  · intro p h1 h2
    have hp : p < n*n := by rw [erasedN_size] at h1; exact h1
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2, erasedN_get, if_pos hp]
    by_cases hpi : p = i
    · subst hpi
      rw [if_pos (List.contains_iff_mem.mpr ((hcomp p).mpr rfl)), hdi]
    · rw [if_neg (fun hc => hpi ((hcomp p).mp (List.contains_iff_mem.mp hc))),
        afterCapN_get, if_pos hp, hdead]
      simp only [List.contains_nil, Bool.false_eq_true, if_false]
      show (placedN n d c i).get p = d.get p
      rw [placedN]; exact get_set_ne _ _ _ _ hpi

/-- Occupancy inclusion from a pointwise domination. -/
theorem occIncB_of {D b : Display n}
    (h : ∀ i, i < n*n → kindAt b i ≠ none → occD D i = true) :
    occIncB n D b = true := by
  unfold occIncB
  rw [List.all_eq_true]
  intro i hi
  cases hk : kindAt b i with
  | none => exact bool_or_right (by simp [hk])
  | some k =>
    exact bool_or_left (h i (List.mem_range.mp hi) (by rw [hk]; exact fun hh => Option.noConfusion hh))

/-- The collision display occupancy, read off kd5. -/
theorem occD_Dcol (hn : 5 ≤ n) {D : Display n} (hd : SameCells D (kd5 n))
    (hwf : WFD D) (t0 i : Nat) :
    occD (Dcol D t0) i = if i = 1 then true else occD (kd5 (n := n)) i := by
  show occD (D.set 1 (some (.r, t0))) i = _
  by_cases hi : i < n*n
  · rw [occ_set _ _ (sb hn).2.2.1 hwf]
    by_cases h1 : i = 1
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, occ_eq_of_samecells hd i]
  · rw [if_neg (by have := (sb hn).2.2.1; omega : ¬ i = 1)]
    rw [occ_of_get_none (get_oob _ (wfd_set _ _ _ hwf) i hi),
      occ_of_get_none (get_oob _ kd5_wfd i hi)]

/-- The black-captures branch stands under the collision display. -/
theorem occInc_ba0 (hn : 5 ≤ n) {D : Display n} (hd : SameCells D (kd5 n))
    (hwf : WFD D) (t0 : Nat) : occIncB n (Dcol D t0) (ba0 n) = true := by
  apply occIncB_of
  intro i hi hne
  rw [occD_Dcol hn hd hwf]
  by_cases h1 : i = 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h0 : i = 0
    · exfalso; apply hne; rw [ba0_kind hn, if_pos h0]
    · have hkeq : kindAt (ba0 n) i = kindAt (kd5 (n := n)) i := by
        rw [ba0_kind hn, if_neg h0, if_neg h1, kd5_kind hn, if_neg h0]
      rw [hkeq] at hne
      cases hkk : kindAt (kd5 (n := n)) i with
      | none => rw [hkk] at hne; exact absurd rfl hne
      | some kc => exact occ_true_of_kind hkk

/-- The white-joins branch stands under the collision display. -/
theorem occInc_ba1 (hn : 5 ≤ n) {D : Display n} (hd : SameCells D (kd5 n))
    (hwf : WFD D) (t0 : Nat) : occIncB n (Dcol D t0) (ba1 n) = true := by
  apply occIncB_of
  intro i hi hne
  rw [occD_Dcol hn hd hwf]
  by_cases h1 : i = 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    have hkeq : kindAt (ba1 n) i = kindAt (kd5 (n := n)) i := by
      show kindAt ((kd5 n).set 1 (some (.w, 0))) i = _
      unfold kindAt; rw [get_set_ne _ _ _ _ h1]
    rw [hkeq] at hne
    cases hkk : kindAt (kd5 (n := n)) i with
    | none => rw [hkk] at hne; exact absurd rfl hne
    | some kc => exact occ_true_of_kind hkk

set_option maxHeartbeats 1000000 in
/-- The A2/A2 collision step: from a semiclassical state carrying the
    witness cells, it splits into the two branches and stores the
    objective-reduction verdict. -/
theorem coll_step (hn : 5 ≤ n) {k : Nat} {s0 : KState n}
    (hd : SameCells s0.disp (kd5 n)) (hwf : WFD s0.disp)
    (hentInc : ∀ b, b ∈ s0.ent → occIncB n s0.disp b = true)
    (hentK : ∀ b, b ∈ s0.ent → b = kd5 n) (hkd5 : kd5 n ∈ s0.ent)
    (hq : s0.verdicts = List.replicate k emptyV) (hk : 1 ≤ k)
    (hf : s0.final = false) :
    ∃ s1, (kGame n k).pairE s0 (some (false, 1)) (some (true, 1)) = some s1
      ∧ s1.disp = Dcol s0.disp s0.next
      ∧ (∀ b, b ∈ s1.ent ↔ b = ba0 n ∨ b = ba1 n)
      ∧ s1.verdicts
          = List.replicate (k-1) emptyV ++ [verOf n s0.next (Dcol s0.disp s0.next)]
      ∧ s1.next = s0.next + 1 ∧ s1.final = false := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hocc1 : occD s0.disp 1 = false := by
    rw [occ_eq_of_samecells hd 1]
    exact occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega),
      if_neg (Ne.symm hw2_1), if_neg (Ne.symm hw1_1), if_neg (by omega),
      if_neg (by omega)])
  have hav : availD n s0.disp (some 1) = true := by
    show (decide (1 < n*n) && !occD s0.disp 1) = true
    rw [decide_eq_true (sb hn).2.2.1, hocc1]; rfl
  have hqne : s0.verdicts ≠ [] := by
    rw [hq]; intro hcon
    have := congrArg List.length hcon
    rw [List.length_replicate] at this; simp at this; omega
  have hEv : (kEv n s0 (some 1) (some 1)).isSome :=
    (kEv_isSome_iff s0 hentInc hqne (some 1) (some 1)).mpr ⟨hf, hav, hav⟩
  rcases Option.isSome_iff_exists.mp hEv with ⟨s1, hs1⟩
  rcases kEv_cases hs1 with ⟨hf', hav0, hav1, v1, vrest, dec, hq', hse, hs'⟩
  -- the popped verdict is empty; the rest is k-1 empties
  have hqrepl : s0.verdicts = emptyV :: List.replicate (k-1) emptyV := by
    rw [hq]; cases k with
    | zero => omega
    | succ kk => rw [List.replicate_succ]; simp
  rw [hqrepl] at hq'
  have hv1 : v1 = emptyV := ((List.cons.injEq .. ▸ hq').1).symm
  have hvr : vrest = List.replicate (k-1) emptyV := ((List.cons.injEq .. ▸ hq').2).symm
  subst hv1
  -- dec is exactly {ba0, ba1}
  have hdecmem : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n := by
    rcases Option.map_eq_some'.mp hse with ⟨out, hout, hdd⟩
    intro b
    constructor
    · intro hb
      rw [← hdd] at hb
      have hbout : b ∈ out := (mem_dedupD_iff _ _).mp hb
      rcases simEvAux_mem hout hbout with ⟨b', hb', l, hl, hbl⟩
      have hbk : b' = kd5 n := hentK b' hb'
      subst hbk
      rw [coll_serialP hn] at hl
      have hll : l = dedupD n [ba0 n, ba1 n] := (Option.some.inj hl).symm
      rw [hll] at hbl
      have hbl2 : b ∈ [ba0 n, ba1 n] := (mem_dedupD_iff _ _).mp hbl
      rcases List.mem_cons.mp hbl2 with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr h
        · cases h
    · intro hb
      rw [← hdd]
      apply (mem_dedupD_iff _ _).mpr
      rcases hb with h | h
      · subst h
        exact simEvAux_mem_of hout hkd5 (coll_serialP hn)
          ((mem_dedupD_iff _ _).mpr (List.mem_cons_self _ _))
      · subst h
        exact simEvAux_mem_of hout hkd5 (coll_serialP hn)
          ((mem_dedupD_iff _ _).mpr (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
  -- the delta computes the collision display and keeps both branches
  have hpj : placeJoint (execV n emptyV s0.disp) s0.next (some 1) (some 1)
      = Dcol s0.disp s0.next := by
    rw [execV_empty]; exact placeJoint_collision s0.disp s0.next 1
  have hdelta : delta n s0.next (placeJoint (execV n emptyV s0.disp) s0.next
      (some 1) (some 1)) dec = (Dcol s0.disp s0.next, recut n (Dcol s0.disp s0.next) dec) := by
    rw [hpj]; exact delta_fix (dcol_round_fix hn hd hwf s0.next s0.next hdecmem)
  refine ⟨s1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (kGame n k).pairE s0 (some (false, 1)) (some (true, 1))
      = kEv n s0 (some 1) (some 1) from rfl]
    exact hs1
  · rw [hs']
    show (delta n s0.next _ dec).1 = _
    rw [hdelta]
  · rw [hs']
    intro b
    show b ∈ (delta n s0.next _ dec).2 ↔ _
    rw [hdelta, recut_mem]
    constructor
    · rintro ⟨hbd, -⟩; exact (hdecmem b).mp hbd
    · intro hb
      refine ⟨(hdecmem b).mpr hb, ?_⟩
      rcases hb with h | h
      · rw [h]; exact occInc_ba0 hn hd hwf s0.next
      · rw [h]; exact occInc_ba1 hn hd hwf s0.next
  · rw [hs']
    show vrest ++ [verOf n s0.next (delta n s0.next _ dec).1] = _
    rw [hdelta, hvr]
  · rw [hs']
  · rw [hs']; rfl

/-! ### The pocket-suicide padding turn -/

/-- The only board neighbors of the far corner are its two walls. -/
theorem nbr_dP (hn : 5 ≤ n) {q : Nat} (hq : q < n*n)
    (h : adjI n q (dP n) = true) : q = dW1 n ∨ q = dW2 n := by
  have hn0 : 0 < n := by omega
  have hdPeq : dP n = (n-1) + n*(n-1) := by
    simp only [dP]; rw [Nat.mul_comm (n-1) n]; omega
  have hdPd : dP n / n = n - 1 := by
    rw [hdPeq, Nat.add_mul_div_left _ _ hn0,
      Nat.div_eq_of_lt (show n - 1 < n by omega), Nat.zero_add]
  have hdPm : dP n % n = n - 1 := by
    rw [hdPeq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show n - 1 < n by omega)]
  have hqm : q % n < n := Nat.mod_lt q hn0
  have hqe := div_mod_recomp (n := n) (q := q) hn0
  have hqd : q / n < n := Nat.div_lt_of_lt_mul hq
  rcases adjI_inv h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [hdPd] at hx; rw [hdPm] at hy
    rcases hy with h' | h'
    · left
      show q = (n-1)*n + (n-2)
      rw [hx] at hqe; omega
    · exfalso; omega
  · rw [hdPm] at hy; rw [hdPd] at hx
    rcases hx with h' | h'
    · right
      show q = (n-2)*n + (n-1)
      rw [show q / n = n - 2 by omega, hy] at hqe; omega
    · exfalso; omega

/-- Playing black in the far corner is a suicide no-op: it captures no
    white group (hypothesis `hdead`), its own stone is libertyless, so the
    board returns unchanged. -/
theorem pocket_suicide (hn : 5 ≤ n) {d : Display n} (hwf : WFD d)
    (hdP : occD d (dP n) = false)
    (hw1 : occD d (dW1 n) = true) (hw2 : occD d (dW2 n) = true)
    (hnw1 : kindAt d (dW1 n) ≠ some .b) (hnw2 : kindAt d (dW2 n) ≠ some .b)
    (hdead : deadOppN n d .b (dP n) = []) :
    goMoveN n d .b (dP n) = some d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hp_w1, hp_w2⟩ := pk_ne hn
  have hdPlt : dP n < n*n := (pk_bounds hn).1
  have hAC := afterCapN_nocap_get d .b (dP n) hwf hdead
  have hACkind : ∀ z, kindAt (afterCapN n d .b (dP n)) z
      = kindAt (placedN n d .b (dP n)) z := by
    intro z; unfold kindAt; rw [hAC z]
  have hACocc : ∀ z, occD (afterCapN n d .b (dP n)) z
      = occD (placedN n d .b (dP n)) z := by
    intro z; unfold occD; rw [hAC z]
  have hplkind1 : kindAt (placedN n d .b (dP n)) (dW1 n) = kindAt d (dW1 n) := by
    unfold kindAt placedN; rw [get_set_ne _ _ _ _ (Ne.symm hp_w1)]
  have hplkind2 : kindAt (placedN n d .b (dP n)) (dW2 n) = kindAt d (dW2 n) := by
    unfold kindAt placedN; rw [get_set_ne _ _ _ _ (Ne.symm hp_w2)]
  have hplocc1 : occD (placedN n d .b (dP n)) (dW1 n) = occD d (dW1 n) := by
    unfold occD placedN; rw [get_set_ne _ _ _ _ (Ne.symm hp_w1)]
  have hplocc2 : occD (placedN n d .b (dP n)) (dW2 n) = occD d (dW2 n) := by
    unfold occD placedN; rw [get_set_ne _ _ _ _ (Ne.symm hp_w2)]
  have hkiA : kindAt (afterCapN n d .b (dP n)) (dP n) = some .b := by
    rw [hACkind]; exact kindAt_placedN_self d .b (dP n) hwf hdPlt
  have hnb : ∀ q, q < n*n → adjI n q (dP n) = true →
      kindAt (afterCapN n d .b (dP n)) q ≠ some .b := by
    intro q hq hadj
    rw [hACkind]
    rcases nbr_dP hn hq hadj with h | h
    · subst h; rw [hplkind1]; exact hnw1
    · subst h; rw [hplkind2]; exact hnw2
  have hcomp : ∀ q, q ∈ ownCompN n d .b (dP n) ↔ q = dP n :=
    comp_singleton _ (dP n) .b hkiA hnb
  have hsui : suicideN n d .b (dP n) = true := by
    show noLibD (afterCapN n d .b (dP n)) (ownCompN n d .b (dP n)) = true
    apply noLibD_true_of
    intro q hq hqocc m hm hadj
    rw [(hcomp m).mp hm] at hadj
    rcases nbr_dP hn hq hadj with h | h
    · subst h; rw [hACocc, hplocc1, hw1] at hqocc; exact Bool.noConfusion hqocc
    · subst h; rw [hACocc, hplocc2, hw2] at hqocc; exact Bool.noConfusion hqocc
  exact goMoveN_suicide d .b (dP n) hwf hdP hdead hsui hcomp

/-- The corner suicide captures no white group in the black-captures
    branch: the only white stones are the two pocket walls, each with an
    escape liberty. -/
theorem dead_ba0 (hn : 5 ≤ n) : deadOppN n (ba0 n) .b (dP n) = [] := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have htrK : ∀ z, z ≠ dP n →
      kindAt (placedN n (ba0 n) .b (dP n)) z = kindAt (ba0 n) z :=
    fun z hz => by unfold kindAt placedN; rw [get_set_ne _ _ _ _ hz]
  have htrO : ∀ z, z ≠ dP n →
      occD (placedN n (ba0 n) .b (dP n)) z = occD (ba0 n) z :=
    fun z hz => by unfold occD placedN; rw [get_set_ne _ _ _ _ hz]
  apply deadOpp_nil_of
  intro p hp
  have hpne : p ≠ dP n := by
    intro he; rw [he, kindAt_placedN_self (ba0 n) .b (dP n) ba0_wfd
      (pk_bounds hn).1] at hp; exact absurd hp (by decide)
  have hk : kindAt (ba0 n) p = some .w := by rw [htrK p hpne] at hp; exact hp
  rw [ba0_kind hn] at hk
  by_cases h0 : p = 0
  · rw [if_pos h0] at hk; exact absurd hk (by decide)
  · by_cases h1 : p = 1
    · rw [if_neg h0, if_pos h1] at hk; exact absurd hk (by decide)
    · by_cases hd2 : p = dW2 n
      · subst hd2
        refine has_lib _ (dW2 n) (dE2 n) .w (pk_bounds hn).2.2.2.2 ?_ ?_ (adj_E2_W2 hn)
        · rw [htrO (dE2 n) he2_P]
          exact occ_of_kind_eq (by rw [ba0_kind hn, if_neg he2_0, if_neg he2_1,
            if_neg he2_w2, if_neg he2_w1, if_neg he2_n, if_neg he2_3])
        · rw [htrK (dW2 n) (Ne.symm hp_w2), ba0_kind hn, if_neg hw2_0,
            if_neg hw2_1, if_pos rfl]
      · by_cases hd1 : p = dW1 n
        · subst hd1
          refine has_lib _ (dW1 n) (dE1 n) .w (pk_bounds hn).2.2.2.1 ?_ ?_ (adj_E1_W1 hn)
          · rw [htrO (dE1 n) he1_P]
            exact occ_of_kind_eq (by rw [ba0_kind hn, if_neg he1_0, if_neg he1_1,
              if_neg he1_w2, if_neg he1_w1, if_neg he1_n, if_neg he1_3])
          · rw [htrK (dW1 n) (Ne.symm hp_w1), ba0_kind hn, if_neg hw1_0,
              if_neg hw1_1, if_neg hw1_w2, if_pos rfl]
        · exfalso
          rw [if_neg h0, if_neg h1, if_neg hd2, if_neg hd1] at hk
          by_cases hnn : p = n
          · rw [if_pos hnn] at hk; exact absurd hk (by decide)
          · by_cases h3 : p = 3
            · rw [if_neg hnn, if_pos h3] at hk; exact absurd hk (by decide)
            · rw [if_neg hnn, if_neg h3] at hk; exact absurd hk (by decide)

/-- The corner suicide captures no white group in the white-joins branch:
    the walls have escape liberties, and the A1/A2 white group breathes at
    B2. -/
theorem dead_ba1 (hn : 5 ≤ n) : deadOppN n (ba1 n) .b (dP n) = [] := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have htrK : ∀ z, z ≠ dP n →
      kindAt (placedN n (ba1 n) .b (dP n)) z = kindAt (ba1 n) z :=
    fun z hz => by unfold kindAt placedN; rw [get_set_ne _ _ _ _ hz]
  have htrO : ∀ z, z ≠ dP n →
      occD (placedN n (ba1 n) .b (dP n)) z = occD (ba1 n) z :=
    fun z hz => by unfold occD placedN; rw [get_set_ne _ _ _ _ hz]
  have hadj_01 : adjI n 0 1 = true := by
    have := adjI_step_y (n:=n) (x:=0) (y:=0) (by omega) (by omega) (by omega)
    simpa using this
  have hadj_1n1 : adjI n 1 (n+1) = true := by
    have := adjI_step_x (n:=n) (x:=0) (y:=1) (by omega) (by omega) (by omega)
    simpa using this
  have hk0 : kindAt (placedN n (ba1 n) .b (dP n)) 0 = some .w := by
    rw [htrK 0 (Ne.symm hp_0), ba1_kind hn, if_neg (by omega), if_pos rfl]
  have hk1 : kindAt (placedN n (ba1 n) .b (dP n)) 1 = some .w := by
    rw [htrK 1 (Ne.symm hp_1), ba1_kind hn, if_pos rfl]
  have hoccn1 : occD (placedN n (ba1 n) .b (dP n)) (n+1) = false := by
    rw [htrO (n+1) (Ne.symm hp_n1)]
    exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega),
      if_neg (by omega)])
  apply deadOpp_nil_of
  intro p hp
  have hpne : p ≠ dP n := by
    intro he; rw [he, kindAt_placedN_self (ba1 n) .b (dP n) ba1_wfd
      (pk_bounds hn).1] at hp; exact absurd hp (by decide)
  have hk : kindAt (ba1 n) p = some .w := by rw [htrK p hpne] at hp; exact hp
  by_cases h1 : p = 1
  · subst h1
    exact has_lib _ 1 (n+1) .w (sb hn).2.2.2.2.2.1 hoccn1 hk1 (adjI_symm hadj_1n1)
  · by_cases h0 : p = 0
    · subst h0
      apply (noLibD_eq_false_iff _ _).mpr
      exact ⟨n+1, List.mem_range.mpr (sb hn).2.2.2.2.2.1, hoccn1, 1,
        (componentD_mem_iff (placedN n (ba1 n) .b (dP n)) 0 .w hk0 1).mpr
          (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1
            (adjI_symm hadj_01)), adjI_symm hadj_1n1⟩
    · rw [ba1_kind hn] at hk
      by_cases hd2 : p = dW2 n
      · subst hd2
        refine has_lib _ (dW2 n) (dE2 n) .w (pk_bounds hn).2.2.2.2 ?_ ?_ (adj_E2_W2 hn)
        · rw [htrO (dE2 n) he2_P]
          exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg he2_1, if_neg he2_0,
            if_neg he2_w2, if_neg he2_w1, if_neg he2_n, if_neg he2_3])
        · rw [htrK (dW2 n) (Ne.symm hp_w2), ba1_kind hn, if_neg hw2_1,
            if_neg hw2_0, if_pos rfl]
      · by_cases hd1 : p = dW1 n
        · subst hd1
          refine has_lib _ (dW1 n) (dE1 n) .w (pk_bounds hn).2.2.2.1 ?_ ?_ (adj_E1_W1 hn)
          · rw [htrO (dE1 n) he1_P]
            exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg he1_1, if_neg he1_0,
              if_neg he1_w2, if_neg he1_w1, if_neg he1_n, if_neg he1_3])
          · rw [htrK (dW1 n) (Ne.symm hp_w1), ba1_kind hn, if_neg hw1_1,
              if_neg hw1_0, if_neg hw1_w2, if_pos rfl]
        · exfalso
          rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1] at hk
          by_cases hnn : p = n
          · rw [if_pos hnn] at hk; exact absurd hk (by decide)
          · by_cases h3 : p = 3
            · rw [if_neg hnn, if_pos h3] at hk; exact absurd hk (by decide)
            · rw [if_neg hnn, if_neg h3] at hk; exact absurd hk (by decide)

/-- Black in the corner is a no-op on the black-captures branch. -/
theorem sui_ba0 (hn : 5 ≤ n) : goMoveN n (ba0 n) .b (dP n) = some (ba0 n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hkw1 : kindAt (ba0 n) (dW1 n) = some .w := by
    rw [ba0_kind hn, if_neg hw1_0, if_neg hw1_1, if_neg hw1_w2, if_pos rfl]
  have hkw2 : kindAt (ba0 n) (dW2 n) = some .w := by
    rw [ba0_kind hn, if_neg hw2_0, if_neg hw2_1, if_pos rfl]
  exact pocket_suicide hn ba0_wfd
    (occ_of_kind_eq (by rw [ba0_kind hn, if_neg hp_0, if_neg hp_1, if_neg hp_w2,
      if_neg hp_w1, if_neg hp_n, if_neg hp_3]))
    (occ_true_of_kind hkw1) (occ_true_of_kind hkw2)
    (by rw [hkw1]; decide) (by rw [hkw2]; decide) (dead_ba0 hn)

/-- Black in the corner is a no-op on the white-joins branch. -/
theorem sui_ba1 (hn : 5 ≤ n) : goMoveN n (ba1 n) .b (dP n) = some (ba1 n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hkw1 : kindAt (ba1 n) (dW1 n) = some .w := by
    rw [ba1_kind hn, if_neg hw1_1, if_neg hw1_0, if_neg hw1_w2, if_pos rfl]
  have hkw2 : kindAt (ba1 n) (dW2 n) = some .w := by
    rw [ba1_kind hn, if_neg hw2_1, if_neg hw2_0, if_pos rfl]
  exact pocket_suicide hn ba1_wfd
    (occ_of_kind_eq (by rw [ba1_kind hn, if_neg hp_1, if_neg hp_0, if_neg hp_w2,
      if_neg hp_w1, if_neg hp_n, if_neg hp_3]))
    (occ_true_of_kind hkw1) (occ_true_of_kind hkw2)
    (by rw [hkw1]; decide) (by rw [hkw2]; decide) (dead_ba1 hn)

/-- The pocket-suicide move serializes to a single unchanged branch. -/
theorem pad_serialP {d : Display n} (hsui : goMoveN n d .b (dP n) = some d) :
    serialP n d (some (dP n)) none = some (dedupD n [d, d]) := by
  have hbw : bStep2 n d .b .w (some (dP n)) none = some d := by
    simp only [bStep2, bStep, hsui, Option.some_bind]
  have hwb : bStep2 n d .w .b none (some (dP n)) = some d := by
    simp only [bStep2, bStep, hsui, Option.some_bind]
  unfold serialP; rw [hbw, hwb]

/-- The pocket-suicide postprocessing: round one discards the corner
    stone, round two is a fixpoint — the display returns to the collision
    display and both branches are re-cut in. -/
theorem delta_padstep (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_pad t_c : Nat) {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n) :
    delta n t_pad ((Dcol D0 t_c).set (dP n) (some (.b, t_pad))) dec
      = (Dcol D0 t_c, recut n (Dcol D0 t_c) (recut n (Dcol D0 t_c) dec)) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hsz : (Dcol D0 t_c).cells.size = n*n := wfd_set _ _ _ hwf
  have hDcolP : (Dcol D0 t_c).get (dP n) = none := by
    rw [Dcol, get_set_ne _ _ _ _ hp_1]
    exact Option.map_eq_none'.mp (by
      show kindAt D0 (dP n) = none
      rw [hsc, kd5_kind hn, if_neg hp_0, if_neg hp_w2, if_neg hp_w1, if_neg hp_n,
        if_neg hp_3])
  have hround1 : deltaRound n t_pad dec ((Dcol D0 t_c).set (dP n) (some (.b, t_pad)))
      = Dcol D0 t_c := pad_round hn hsc hwf t_pad t_c hdec
  have hrecmem : ∀ b, b ∈ recut n (Dcol D0 t_c) dec ↔ b = ba0 n ∨ b = ba1 n := by
    intro b; rw [recut_mem]
    constructor
    · rintro ⟨hbd, -⟩; exact (hdec b).mp hbd
    · intro hb
      refine ⟨(hdec b).mpr hb, ?_⟩
      rcases hb with h | h
      · rw [h]; exact occInc_ba0 hn hsc hwf t_c
      · rw [h]; exact occInc_ba1 hn hsc hwf t_c
  have hne : ¬ (deltaRound n t_pad dec ((Dcol D0 t_c).set (dP n) (some (.b, t_pad)))
      == (Dcol D0 t_c).set (dP n) (some (.b, t_pad))) = true := by
    rw [hround1]; intro hc
    have heq : Dcol D0 t_c = (Dcol D0 t_c).set (dP n) (some (.b, t_pad)) :=
      display_eq_of_beq hc
    have h1 : (Dcol D0 t_c).get (dP n)
        = ((Dcol D0 t_c).set (dP n) (some (.b, t_pad))).get (dP n) :=
      congrArg (fun D => D.get (dP n)) heq
    rw [hDcolP, get_set_self _ _ _ (by rw [hsz]; exact (pk_bounds hn).1)] at h1
    exact Option.noConfusion h1
  have hround2 : deltaRound n t_pad (recut n (Dcol D0 t_c) dec) (Dcol D0 t_c)
      = Dcol D0 t_c := dcol_round_fix hn hsc hwf t_pad t_c hrecmem
  show deltaAux n t_pad (2*(n*n)+2) ((Dcol D0 t_c).set (dP n) (some (.b, t_pad))) dec = _
  rw [show deltaAux n t_pad (2*(n*n)+2) ((Dcol D0 t_c).set (dP n) (some (.b, t_pad))) dec
      = if (deltaRound n t_pad dec ((Dcol D0 t_c).set (dP n) (some (.b, t_pad)))
            == (Dcol D0 t_c).set (dP n) (some (.b, t_pad))) = true
        then _ else deltaAux n t_pad (2*(n*n)+1)
          (deltaRound n t_pad dec ((Dcol D0 t_c).set (dP n) (some (.b, t_pad))))
          (recut n (deltaRound n t_pad dec ((Dcol D0 t_c).set (dP n) (some (.b, t_pad)))) dec)
      from rfl, if_neg hne, hround1]
  exact deltaAux_fix t_pad (2*(n*n)) (Dcol D0 t_c) (recut n (Dcol D0 t_c) dec) hround2

set_option maxHeartbeats 1000000 in
/-- One pocket-suicide padding turn: the display and entanglement are
    fixed, the front (empty) verdict is popped and a fresh verdict is
    stored at the back. -/
theorem pad_step (hn : 5 ≤ n) {k : Nat} {s : KState n} {D0 : Display n} {t_c : Nat}
    {rest : List Verdict}
    (hsc : SameCells D0 (kd5 n)) (hwf : WFD D0)
    (hdisp : s.disp = Dcol D0 t_c)
    (hent : ∀ b, b ∈ s.ent ↔ b = ba0 n ∨ b = ba1 n)
    (hq : s.verdicts = emptyV :: rest)
    (hf : s.final = false) :
    ∃ s', (kGame n k).pairE s (some (false, dP n)) none = some s'
      ∧ s'.disp = Dcol D0 t_c
      ∧ (∀ b, b ∈ s'.ent ↔ b = ba0 n ∨ b = ba1 n)
      ∧ s'.verdicts = rest ++ [verOf n s.next (Dcol D0 t_c)]
      ∧ s'.next = s.next + 1 ∧ s'.final = false := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hdPlt : dP n < n*n := (pk_bounds hn).1
  have hoccdP : occD s.disp (dP n) = false := by
    rw [hdisp, occD_Dcol hn hsc hwf t_c (dP n), if_neg hp_1]
    exact kd5_none hn hp_0 hp_w2 hp_w1 hp_n hp_3
  have hav : availD n s.disp (some (dP n)) = true := by
    show (decide (dP n < n*n) && !occD s.disp (dP n)) = true
    rw [decide_eq_true hdPlt, hoccdP]; rfl
  have hentInc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true := by
    intro b hb; rw [hdisp]
    rcases (hent b).mp hb with h | h
    · rw [h]; exact occInc_ba0 hn hsc hwf t_c
    · rw [h]; exact occInc_ba1 hn hsc hwf t_c
  have hqne : s.verdicts ≠ [] := by rw [hq]; exact List.cons_ne_nil _ _
  have hEv : (kEv n s (some (dP n)) none).isSome :=
    (kEv_isSome_iff s hentInc hqne (some (dP n)) none).mpr ⟨hf, hav, rfl⟩
  rcases Option.isSome_iff_exists.mp hEv with ⟨s', hs'⟩
  rcases kEv_cases hs' with ⟨hf', hav0, hav1, v1, vrest, dec, hq', hse, hseq⟩
  rw [hq] at hq'
  have hv1 : v1 = emptyV := ((List.cons.injEq .. ▸ hq').1).symm
  have hvr : vrest = rest := ((List.cons.injEq .. ▸ hq').2).symm
  subst hv1
  have hdecmem : ∀ b, b ∈ dec ↔ b = ba0 n ∨ b = ba1 n := by
    rcases Option.map_eq_some'.mp hse with ⟨out, hout, hdd⟩
    intro b; constructor
    · intro hb
      rw [← hdd] at hb
      have hbout : b ∈ out := (mem_dedupD_iff _ _).mp hb
      rcases simEvAux_mem hout hbout with ⟨b', hb', l, hl, hbl⟩
      rcases (hent b').mp hb' with h | h
      · subst h; rw [pad_serialP (sui_ba0 hn)] at hl
        rw [(Option.some.inj hl).symm] at hbl
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hbl) with h' | h'
        · exact Or.inl h'
        · rcases List.mem_cons.mp h' with h' | h'
          · exact Or.inl h'
          · cases h'
      · subst h; rw [pad_serialP (sui_ba1 hn)] at hl
        rw [(Option.some.inj hl).symm] at hbl
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hbl) with h' | h'
        · exact Or.inr h'
        · rcases List.mem_cons.mp h' with h' | h'
          · exact Or.inr h'
          · cases h'
    · intro hb
      rw [← hdd]
      apply (mem_dedupD_iff _ _).mpr
      rcases hb with h | h
      · subst h
        exact simEvAux_mem_of hout ((hent (ba0 n)).mpr (Or.inl rfl))
          (pad_serialP (sui_ba0 hn)) ((mem_dedupD_iff _ _).mpr (List.mem_cons_self _ _))
      · subst h
        exact simEvAux_mem_of hout ((hent (ba1 n)).mpr (Or.inr rfl))
          (pad_serialP (sui_ba1 hn)) ((mem_dedupD_iff _ _).mpr (List.mem_cons_self _ _))
  have hpj : placeJoint (execV n emptyV s.disp) s.next (some (dP n)) none
      = (Dcol D0 t_c).set (dP n) (some (.b, s.next)) := by
    rw [execV_empty, hdisp]; rfl
  have hdelta : delta n s.next (placeJoint (execV n emptyV s.disp) s.next
      (some (dP n)) none) dec
      = (Dcol D0 t_c, recut n (Dcol D0 t_c) (recut n (Dcol D0 t_c) dec)) := by
    rw [hpj]; exact delta_padstep hn hsc hwf s.next t_c hdecmem
  have hmemfinal : ∀ b, b ∈ recut n (Dcol D0 t_c) (recut n (Dcol D0 t_c) dec)
      ↔ b = ba0 n ∨ b = ba1 n := by
    intro b; rw [recut_mem, recut_mem]
    constructor
    · rintro ⟨⟨hbd, -⟩, -⟩; exact (hdecmem b).mp hbd
    · intro hb
      have hocc : occIncB n (Dcol D0 t_c) b = true := by
        rcases hb with h | h
        · rw [h]; exact occInc_ba0 hn hsc hwf t_c
        · rw [h]; exact occInc_ba1 hn hsc hwf t_c
      exact ⟨⟨(hdecmem b).mpr hb, hocc⟩, hocc⟩
  refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (kGame n k).pairE s (some (false, dP n)) none
      = kEv n s (some (dP n)) none from rfl]
    exact hs'
  · rw [hseq]; show (delta n s.next _ dec).1 = _; rw [hdelta]
  · rw [hseq]; intro b; show b ∈ (delta n s.next _ dec).2 ↔ _
    rw [hdelta]; exact hmemfinal b
  · rw [hseq]
    show vrest ++ [verOf n s.next (delta n s.next _ dec).1] = _
    rw [hdelta, hvr]
  · rw [hseq]
  · rw [hseq]; rfl

/-- Aging the delayed verdict: after `m` pocket-suicide padding turns the
    display and entanglement are unchanged and the queue has shed its `m`
    leading empties, so the collision verdict has risen to the front. The
    within-distance advances by `m`. -/
theorem pad_reach (hn : 5 ≤ n) {k : Nat} {D0 : Display n} {t_c : Nat}
    (hsc : SameCells D0 (kd5 n)) (hwf : WFD D0) :
    ∀ (m : Nat) (s : KState n) (d : Nat) (rest : List Verdict),
      s.disp = Dcol D0 t_c →
      (∀ b, b ∈ s.ent ↔ b = ba0 n ∨ b = ba1 n) →
      s.verdicts = List.replicate m emptyV ++ verOf n t_c (Dcol D0 t_c) :: rest →
      s.final = false →
      WithinD (goGame n) (kGame n k) (rhoK n) d s →
      ∃ s', s'.disp = Dcol D0 t_c
        ∧ (∀ b, b ∈ s'.ent ↔ b = ba0 n ∨ b = ba1 n)
        ∧ (∃ rest', s'.verdicts = verOf n t_c (Dcol D0 t_c) :: rest')
        ∧ s'.final = false
        ∧ WithinD (goGame n) (kGame n k) (rhoK n) (d+m) s' := by
  intro m
  induction m with
  | zero =>
    intro s d rest hdisp hent hq hf hW
    exact ⟨s, hdisp, hent, ⟨rest, hq⟩, hf, by simpa using hW⟩
  | succ mm ih =>
    intro s d rest hdisp hent hq hf hW
    have hqfront : s.verdicts
        = emptyV :: (List.replicate mm emptyV ++ verOf n t_c (Dcol D0 t_c) :: rest) := by
      rw [hq, List.replicate_succ]; rfl
    obtain ⟨s', hp, hdisp', hent', hq', -, hf'⟩ :=
      pad_step hn hsc hwf hdisp hent hqfront hf
    have hW' : WithinD (goGame n) (kGame n k) (rhoK n) (d+1) s' := WithinD.step hW hp
    have hq'' : s'.verdicts = List.replicate mm emptyV
        ++ verOf n t_c (Dcol D0 t_c) :: (rest ++ [verOf n s.next (Dcol D0 t_c)]) := by
      rw [hq', List.append_assoc, List.cons_append]
    obtain ⟨s'', hdisp'', hent'', hqf'', hf'', hW''⟩ :=
      ih s' (d+1) (rest ++ [verOf n s.next (Dcol D0 t_c)]) hdisp' hent' hq'' hf' hW'
    refine ⟨s'', hdisp'', hent'', hqf'', hf'', ?_⟩
    rw [show d + (mm+1) = (d+1) + mm from by omega]; exact hW''

end SgoKWit
