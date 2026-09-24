/- SgoKWit.lean — theorem 5.2, milestone 4c: k-DSGo is NOT faithful
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

set_option maxHeartbeats 4000000 in
/-- The collision A2/A2 serializes to the two branches. -/
theorem coll_serialP (hn : 5 ≤ n) :
    serialP n (kd5 (n := n)) (some 1) (some 1)
      = some (dedupD n [ba0 (n := n), ba1 (n := n)]) := by
  have hbw : bStep2 n (kd5 (n := n)) .b .w (some 1) (some 1) = none := by
    show (goMoveN n (kd5 n) .b 1).bind (fun d1 => goMoveN n d1 .w 1) = none
    rw [gmb1 hn]
    exact goMoveN_occ_none (ba0 n) .w 1 (occ_true_of_kind
      (show kindAt (ba0 (n := n)) 1 = some .b from by
        rw [ba0_kind hn, if_neg (by omega), if_pos rfl]))
  have hwb : bStep2 n (kd5 (n := n)) .w .b (some 1) (some 1) = none := by
    show (goMoveN n (kd5 n) .w 1).bind (fun d1 => goMoveN n d1 .b 1) = none
    rw [gmw1 hn]
    exact goMoveN_occ_none (ba1 n) .b 1 (occ_true_of_kind
      (show kindAt (ba1 (n := n)) 1 = some .w from by rw [ba1_kind hn, if_pos rfl]))
  sorry

end SgoKWit
