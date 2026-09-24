/- SgoKFin.lean — the main theorem, milestone 4c, the final turn.

   The delayed collision verdict fires: executing it on the aged
   collision display empties A1 and blackens A2 (the objective reduction
   of the collision), then the joint move B3/A3 is played. White's A3
   dies in the surviving branch a0'' yet, protected through the Δ removal
   round by the recut-away white-joins branch, stands on the display —
   a stone dead in every surviving branch, at distance k+1. -/
import SgoKWit

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoSimple SgoWit SgoDInv SgoDOK SgoDNat SgoDSemi
  SgoDFaith SgoKInv SgoKNat SgoKWit

namespace SgoKWit

variable {n : Nat}

/-! ### filterMap over a range with a single hit -/

theorem count_range (j m : Nat) : (List.range m).count j = if j < m then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.count_append, ih, List.count_cons, List.count_nil]
    by_cases hjm : j = m
    · subst hjm
      rw [if_neg (Nat.lt_irrefl j), if_pos (Nat.lt_succ_self j)]; simp
    · have hmj : (m == j) = false := by simp [Ne.symm hjm]
      by_cases hlt : j < m
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt), hmj]; simp
      · rw [if_neg hlt, if_neg (show ¬ j < m+1 by omega), hmj]; simp

theorem filterMap_count {β : Type} (g : Nat → Option β) (b : β) (j : Nat)
    (hgj : g j = some b) (hother : ∀ i, i ≠ j → g i = none) (L : List Nat) :
    List.filterMap g L = List.replicate (L.count j) b := by
  induction L with
  | nil => rfl
  | cons a L' ih =>
    rw [List.filterMap_cons, List.count_cons]
    by_cases ha : a = j
    · subst ha
      rw [hgj, ih, show L'.count a + (if (a == a) = true then 1 else 0) = L'.count a + 1 from by simp,
        List.replicate_succ]
    · rw [hother a ha, ih, show L'.count j + (if (a == j) = true then 1 else 0) = L'.count j from by
        simp [ha]]

/-- filterMap over the board with a single hit at j yields the singleton. -/
theorem filterMap_range_single {β : Type} (g : Nat → Option β) (b : β) (j m : Nat)
    (hj : j < m) (hgj : g j = some b) (hother : ∀ i, i ≠ j → g i = none) :
    (List.range m).filterMap g = [b] := by
  rw [filterMap_count g b j hgj hother, count_range, if_pos hj]; rfl

/-! ### Occupancy/kind of the collision display at the witness cells -/

theorem kd5_kind_0 (hn : 5 ≤ n) : kindAt (kd5 (n := n)) 0 = some .w := by
  rw [kd5_kind hn, if_pos rfl]

theorem kd5_kind_n (hn : 5 ≤ n) : kindAt (kd5 (n := n)) n = some .b := by
  obtain ⟨_, _, _, _, hw1_n, _, _, _, _, _, _, _, hw2_n, _⟩ := pk_ne hn
  rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_n),
    if_neg (Ne.symm hw1_n), if_pos rfl]

theorem kd5_kind_3 (hn : 5 ≤ n) : kindAt (kd5 (n := n)) 3 = some .b := by
  obtain ⟨_, _, _, hw1_3, _, _, _, _, _, _, _, hw2_3, _⟩ := pk_ne hn
  rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_3),
    if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]

/-! ### The objective reduction of the collision display -/

/-- Stamps of the collision display: the q-stone carries the collision
    turn, every other cell keeps its setup stamp. -/
theorem stampAt_Dcol_ne {D0 : Display n} (t0 : Nat) {z : Nat} (hz : z ≠ 1) :
    stampAt (Dcol D0 t0) z = stampAt D0 z := by
  unfold Dcol stampAt
  rw [get_set_ne _ _ _ _ hz]

theorem stampAt_Dcol_one (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t0 : Nat) :
    stampAt (Dcol D0 t0) 1 = t0 := by
  unfold Dcol stampAt
  rw [get_set_self _ _ _ (by rw [hwf]; exact (sb hn).2.2.1)]; rfl

theorem stampAt_Dcol_le (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) {t0 : Nat}
    (hst : StampsBelow D0 t0) : ∀ z, stampAt (Dcol D0 t0) z ≤ t0 := by
  intro z
  by_cases hz : z = 1
  · rw [hz, stampAt_Dcol_one hn hwf]; exact Nat.le_refl t0
  · rw [stampAt_Dcol_ne t0 hz]; exact Nat.le_of_lt (hst z)

/-- The A1 white stone spans a singleton component in the collision
    display (its only neighbors are the q-stone and the B1 black wall). -/
theorem comp0_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) :
    ∀ q, q ∈ componentD (Dcol D0 t0) 0 ↔ q = 0 := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hk0 : kindAt (Dcol D0 t0) 0 = some .w := by
    rw [Dcol_kind hn hsc hwf, if_neg (by omega), kd5_kind_0 hn]
  apply comp_singleton (Dcol D0 t0) 0 .w hk0
  intro q hq hadj
  rcases nbr_0 (by omega) hadj with h | h
  · subst h; rw [Dcol_kind hn hsc hwf, if_pos rfl]; decide
  · rw [h, Dcol_kind hn hsc hwf, if_neg (show n ≠ 1 by omega), kd5_kind_n hn]; decide

/-- The A1 white stone is libertyless in the collision display. -/
theorem noLib0_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) :
    noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) 0) = true := by
  apply noLibD_true_of
  intro q hq hqocc m hm hadj
  rw [(comp0_Dcol hn hsc hwf t0 m).mp hm] at hadj
  rcases nbr_0 (by omega) hadj with h | h
  · subst h
    rw [occD_Dcol hn hsc hwf, if_pos rfl] at hqocc; exact Bool.noConfusion hqocc
  · rw [h, occD_Dcol hn hsc hwf, if_neg (show n ≠ 1 by omega),
      occ_true_of_kind (kd5_kind_n hn)] at hqocc
    exact Bool.noConfusion hqocc

/-- The q-stone at A2 is the only red cell in the collision display. -/
theorem kd5_not_red (hn : 5 ≤ n) (r : Nat) : kindAt (kd5 (n := n)) r ≠ some .r := by
  rw [kd5_kind hn]
  by_cases h0 : r = 0
  · rw [if_pos h0]; decide
  · by_cases hd2 : r = dW2 n
    · rw [if_neg h0, if_pos hd2]; decide
    · by_cases hd1 : r = dW1 n
      · rw [if_neg h0, if_neg hd2, if_pos hd1]; decide
      · by_cases hnn : r = n
        · rw [if_neg h0, if_neg hd2, if_neg hd1, if_pos hnn]; decide
        · by_cases h3 : r = 3
          · rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_pos h3]; decide
          · rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3]; decide

theorem red_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) {r : Nat}
    (h : kindAt (Dcol D0 t0) r = some .r) : r = 1 := by
  by_cases hr : r = 1
  · exact hr
  · rw [Dcol_kind hn hsc hwf, if_neg hr] at h
    exact absurd h (kd5_not_red hn r)

/-- A2 is occupied and libertyful once made definite; helper occupancies. -/
theorem occ_Dcol_1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : occD (Dcol D0 t0) 1 = true := by
  rw [occD_Dcol hn hsc hwf, if_pos rfl]

theorem occ_Dcol_n (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : occD (Dcol D0 t0) n = true := by
  rw [occD_Dcol hn hsc hwf, if_neg (show n ≠ 1 by omega), occ_true_of_kind (kd5_kind_n hn)]

/-- The A1 white stone is trapped on the collision turn: libertyless,
    with the fresh q-stone (stamp t_c) among its neighbours. -/
theorem trapped_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) :
    trappedOnTurn (Dcol D0 t_c) (componentD (Dcol D0 t_c) 0) t_c = true := by
  have hadj10 : adjI n 1 0 = true := adjI_symm (by
    have := adjI_step_y (n:=n) (x:=0) (y:=0) (by omega) (by omega) (by omega)
    simpa using this)
  apply trapped_on_t (Dcol D0 t_c) t_c (stampAt_Dcol_le hn hwf hst)
    (componentD (Dcol D0 t_c) 0) (noLib0_Dcol hn hsc hwf t_c) 1 (sb hn).2.2.1
    (occ_Dcol_1 hn hsc hwf t_c) (stampAt_Dcol_one hn hwf t_c)
    (by intro hmem; rw [comp0_Dcol hn hsc hwf t_c 1] at hmem; omega)
    (List.any_eq_true.mpr ⟨0, (comp0_Dcol hn hsc hwf t_c 0).mpr rfl, hadj10⟩)

/-- Empty/kind helpers on the collision display at A3 and B2. -/
theorem occ_Dcol_2 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : occD (Dcol D0 t0) 2 = false := by
  obtain ⟨_, _, hw1_2, _, _, _, _, _, _, _, hw2_2, _⟩ := pk_ne hn
  rw [occD_Dcol hn hsc hwf, if_neg (by omega)]
  exact occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_2),
    if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])

theorem occ_Dcol_n1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : occD (Dcol D0 t0) (n+1) = false := by
  obtain ⟨_, _, _, _, _, hw1_n1, _, _, _, _, _, _, _, hw2_n1, _⟩ := pk_ne hn
  rw [occD_Dcol hn hsc hwf, if_neg (by omega)]
  exact occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_n1),
    if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)])

theorem kind_Dcol_1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : kindAt (Dcol D0 t0) 1 = some .r := by
  rw [Dcol_kind hn hsc hwf, if_pos rfl]

theorem kind_Dcol_n (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : kindAt (Dcol D0 t0) n = some .b := by
  obtain ⟨_, _, _, _, hw1_n, _, _, _, _, _, _, _, hw2_n, _⟩ := pk_ne hn
  rw [Dcol_kind hn hsc hwf, if_neg (show n ≠ 1 by omega), kd5_kind_n hn]

theorem kind_Dcol_0 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : kindAt (Dcol D0 t0) 0 = some .w := by
  rw [Dcol_kind hn hsc hwf, if_neg (by omega), kd5_kind_0 hn]

theorem kind_Dcol_2 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : kindAt (Dcol D0 t0) 2 = none := by
  obtain ⟨_, _, hw1_2, _, _, _, _, _, _, _, hw2_2, _⟩ := pk_ne hn
  rw [Dcol_kind hn hsc hwf, if_neg (by omega), kd5_kind hn, if_neg (by omega),
    if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]

theorem kind_Dcol_n1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : kindAt (Dcol D0 t0) (n+1) = none := by
  obtain ⟨_, _, _, _, _, hw1_n1, _, _, _, _, _, _, _, hw2_n1, _⟩ := pk_ne hn
  rw [Dcol_kind hn hsc hwf, if_neg (by omega), kd5_kind hn, if_neg (by omega),
    if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)]

/-- A2's q-stone group and B1's black group each have a liberty in the
    collision display (so neither is trapped). -/
theorem noLib_Dcol_1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) 1) = false := by
  have hadj : adjI n 2 1 = true := adjI_symm (by
    have := adjI_step_y (n:=n) (x:=0) (y:=1) (by omega) (by omega) (by omega)
    simpa using this)
  exact has_lib (Dcol D0 t0) 1 2 .r (sb hn).2.1 (occ_Dcol_2 hn hsc hwf t0)
    (kind_Dcol_1 hn hsc hwf t0) hadj

theorem noLib_Dcol_n (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) : noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) n) = false := by
  have hadj : adjI n (n+1) n = true := adjI_symm (by
    have := adjI_step_y (n:=n) (x:=1) (y:=0) (by omega) (by omega) (by omega)
    simpa using this)
  exact has_lib (Dcol D0 t0) n (n+1) .b (sb hn).2.2.2.2.2.1 (occ_Dcol_n1 hn hsc hwf t0)
    (kind_Dcol_n hn hsc hwf t0) hadj

set_option maxHeartbeats 800000 in
/-- The A1 white stone is captured on the collision turn: the objective
    reduction resolves the A2 collision in Black's favour. -/
theorem isCaptured0_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) :
    isCaptured (Dcol D0 t_c) (componentD (Dcol D0 t_c) 0) .w t_c = true := by
  simp only [isCaptured]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨trapped_Dcol hn hsc hwf hst, ?_⟩, ?_⟩
  · -- cond_unambiguous0: the only red is A2, whose non-white neighbours are empty
    rw [List.all_eq_true]
    intro r hr
    have hrr : kindAt (Dcol D0 t_c) r = some .r := by
      have hh := (List.mem_filter.mp hr).2
      rw [Bool.and_eq_true] at hh
      exact beq_iff_eq.mp hh.1
    have hr1 : r = 1 := red_Dcol hn hsc hwf t_c hrr
    subst hr1
    rw [List.all_eq_true]
    intro z hz
    cases hzadj : adjI n z 1
    · rfl
    · rcases nbr_1 (by omega) hzadj with h | h | h
      · subst h; simp [kind_Dcol_0 hn hsc hwf]
      · subst h; simp [kind_Dcol_2 hn hsc hwf]
      · subst h; simp [kind_Dcol_n1 hn hsc hwf]
  · -- (3b): comp stones are old, adjacent stones are not trapped
    apply bool_or_right
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true]
      intro q hq
      rw [(comp0_Dcol hn hsc hwf t_c q).mp hq, stampAt_Dcol_ne t_c (show (0:Nat) ≠ 1 by omega)]
      exact bne_of_ne (Nat.ne_of_lt (hst 0))
    · rw [List.all_eq_true]
      intro z hz
      have hcompany : (componentD (Dcol D0 t_c) 0).any (fun q => adjI n z q) = true := by
        have hh := (List.mem_filter.mp hz).2
        rw [Bool.and_eq_true, Bool.and_eq_true] at hh
        exact hh.2
      rcases List.any_eq_true.mp hcompany with ⟨m, hm, hadjm⟩
      rw [(comp0_Dcol hn hsc hwf t_c m).mp hm] at hadjm
      rcases nbr_0 (by omega) hadjm with h | h
      · subst h
        have ht1 : trappedOnTurn (Dcol D0 t_c) (componentD (Dcol D0 t_c) 1) t_c = false := by
          unfold trappedOnTurn; rw [noLib_Dcol_1 hn hsc hwf t_c]; rfl
        rw [ht1]; rfl
      · rw [h]
        have htn : trappedOnTurn (Dcol D0 t_c) (componentD (Dcol D0 t_c) n) t_c = false := by
          unfold trappedOnTurn; rw [noLib_Dcol_n hn hsc hwf t_c]; rfl
        rw [htn]; rfl

/-! ### The captured sets of the collision display -/

theorem white_kd5 (hn : 5 ≤ n) {p : Nat} (h : kindAt (kd5 (n := n)) p = some .w) :
    p = 0 ∨ p = dW1 n ∨ p = dW2 n := by
  rw [kd5_kind hn] at h
  by_cases h0 : p = 0
  · exact Or.inl h0
  · by_cases hd2 : p = dW2 n
    · exact Or.inr (Or.inr hd2)
    · by_cases hd1 : p = dW1 n
      · exact Or.inr (Or.inl hd1)
      · exfalso
        by_cases hnn : p = n
        · rw [if_neg h0, if_neg hd2, if_neg hd1, if_pos hnn] at h; exact absurd h (by decide)
        · by_cases h3 : p = 3
          · rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_pos h3] at h
            exact absurd h (by decide)
          · rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
            exact absurd h (by decide)

theorem black_kd5 (hn : 5 ≤ n) {p : Nat} (h : kindAt (kd5 (n := n)) p = some .b) :
    p = 3 ∨ p = n := by
  rw [kd5_kind hn] at h
  by_cases hnn : p = n
  · exact Or.inr hnn
  · by_cases h3 : p = 3
    · exact Or.inl h3
    · exfalso
      by_cases h0 : p = 0
      · rw [if_pos h0] at h; exact absurd h (by decide)
      · by_cases hd2 : p = dW2 n
        · rw [if_neg h0, if_pos hd2] at h; exact absurd h (by decide)
        · by_cases hd1 : p = dW1 n
          · rw [if_neg h0, if_neg hd2, if_pos hd1] at h; exact absurd h (by decide)
          · rw [if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
            exact absurd h (by decide)

theorem white_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) {p : Nat} (h : kindAt (Dcol D0 t0) p = some .w) :
    p = 0 ∨ p = dW1 n ∨ p = dW2 n := by
  by_cases hp1 : p = 1
  · rw [hp1, kind_Dcol_1 hn hsc hwf] at h; exact absurd h (by decide)
  · rw [Dcol_kind hn hsc hwf, if_neg hp1] at h; exact white_kd5 hn h

theorem black_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) {p : Nat} (h : kindAt (Dcol D0 t0) p = some .b) :
    p = 3 ∨ p = n := by
  by_cases hp1 : p = 1
  · rw [hp1, kind_Dcol_1 hn hsc hwf] at h; exact absurd h (by decide)
  · rw [Dcol_kind hn hsc hwf, if_neg hp1] at h; exact black_kd5 hn h

theorem isCaptured_false_of_noLib {D : Display n} {comp : List Nat} {c : DKind}
    {t : Nat} (h : noLibD D comp = false) : isCaptured D comp c t = false := by
  have ht : trappedOnTurn D comp t = false := by unfold trappedOnTurn; rw [h]; rfl
  simp only [isCaptured, ht, Bool.false_and]

theorem noLib_Dcol_dW1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) :
    noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) (dW1 n)) = false := by
  obtain ⟨hw1_0, hw1_1, _, _, _, _, _, hw1_w2, _⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, _⟩ := dE_ne hn
  have hkw1 : kindAt (Dcol D0 t0) (dW1 n) = some .w := by
    rw [Dcol_kind hn hsc hwf, if_neg hw1_1, kd5_kind hn, if_neg hw1_0, if_neg hw1_w2, if_pos rfl]
  have hoe1 : occD (Dcol D0 t0) (dE1 n) = false := by
    rw [occD_Dcol hn hsc hwf, if_neg he1_1]
    exact kd5_none hn he1_0 he1_w2 he1_w1 he1_n he1_3
  exact has_lib (Dcol D0 t0) (dW1 n) (dE1 n) .w (pk_bounds hn).2.2.2.1 hoe1 hkw1 (adj_E1_W1 hn)

theorem noLib_Dcol_dW2 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) :
    noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) (dW2 n)) = false := by
  obtain ⟨_, _, _, _, _, _, _, _, hw2_0, hw2_1, _⟩ := pk_ne hn
  obtain ⟨_, _, _, _, _, _, _, he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, _⟩ := dE_ne hn
  have hkw2 : kindAt (Dcol D0 t0) (dW2 n) = some .w := by
    rw [Dcol_kind hn hsc hwf, if_neg hw2_1, kd5_kind hn, if_neg hw2_0, if_pos rfl]
  have hoe2 : occD (Dcol D0 t0) (dE2 n) = false := by
    rw [occD_Dcol hn hsc hwf, if_neg he2_1]
    exact kd5_none hn he2_0 he2_w2 he2_w1 he2_n he2_3
  exact has_lib (Dcol D0 t0) (dW2 n) (dE2 n) .w (pk_bounds hn).2.2.2.2 hoe2 hkw2 (adj_E2_W2 hn)

theorem noLib_Dcol_3 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t0 : Nat) :
    noLibD (Dcol D0 t0) (componentD (Dcol D0 t0) 3) = false := by
  have hadj : adjI n 2 3 = true := adj_2_3 hn
  have hk3 : kindAt (Dcol D0 t0) 3 = some .b := by
    rw [Dcol_kind hn hsc hwf, if_neg (by omega), kd5_kind_3 hn]
  exact has_lib (Dcol D0 t0) 3 2 .b (sb hn).2.1 (occ_Dcol_2 hn hsc hwf t0) hk3 hadj

/-- The captured white set is exactly {A1}. -/
theorem capturedW_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) :
    ∀ x, x ∈ capturedOf (Dcol D0 t_c) t_c .w ↔ x = 0 := by
  intro x
  constructor
  · intro hx
    rcases (mem_capturedOf _ t_c .w x).mp hx with ⟨p, hpb, hkp, hcap, hxp⟩
    rcases white_Dcol hn hsc hwf t_c hkp with h0 | hd1 | hd2
    · rw [h0] at hxp; exact (comp0_Dcol hn hsc hwf t_c x).mp hxp
    · rw [hd1, isCaptured_false_of_noLib (noLib_Dcol_dW1 hn hsc hwf t_c)] at hcap
      exact absurd hcap (by decide)
    · rw [hd2, isCaptured_false_of_noLib (noLib_Dcol_dW2 hn hsc hwf t_c)] at hcap
      exact absurd hcap (by decide)
  · intro hx; subst hx
    exact (mem_capturedOf _ t_c .w 0).mpr ⟨0, List.mem_range.mpr (sb hn).2.2.2.1,
      kind_Dcol_0 hn hsc hwf t_c, isCaptured0_Dcol hn hsc hwf hst,
      (comp0_Dcol hn hsc hwf t_c 0).mpr rfl⟩

/-- No black group is captured in the collision display. -/
theorem capturedB_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) :
    ∀ x, x ∈ capturedOf (Dcol D0 t_c) t_c .b ↔ False := by
  intro x
  constructor
  · intro hx
    rcases (mem_capturedOf _ t_c .b x).mp hx with ⟨p, hpb, hkp, hcap, hxp⟩
    rcases black_Dcol hn hsc hwf t_c hkp with h3 | hnn
    · rw [h3, isCaptured_false_of_noLib (noLib_Dcol_3 hn hsc hwf t_c)] at hcap
      exact absurd hcap (by decide)
    · rw [hnn, isCaptured_false_of_noLib (noLib_Dcol_n hn hsc hwf t_c)] at hcap
      exact absurd hcap (by decide)
  · intro h; exact h.elim

/-- The objective reduction of the collision display: A1 emptied, A2 made
    definitely black (its q-stone stamp preserved). -/
def Eres (D0 : Display n) (t_c : Nat) : Display n :=
  ((Dcol D0 t_c).set 1 (some (.b, t_c))).set 0 none

theorem Eres_get_0 (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t_c : Nat) :
    (Eres D0 t_c).get 0 = none := by
  have hsz : (Dcol D0 t_c).cells.size = n*n := wfd_set _ _ _ hwf
  unfold Eres
  rw [get_set_self _ _ _ (by rw [set_size, hsz]; exact (sb hn).2.2.2.1)]

theorem basicCap_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) :
    basicCap (Dcol D0 t_c) t_c = Eres D0 t_c := by
  have hwfDcol : WFD (Dcol D0 t_c) := wfd_set _ _ _ hwf
  have hsz1 : (Dcol D0 t_c).cells.size = n*n := hwfDcol
  have hdead0 : (capturedOf (Dcol D0 t_c) t_c .b
      ++ capturedOf (Dcol D0 t_c) t_c .w).contains 0 = true :=
    List.contains_iff_mem.mpr (List.mem_append.mpr
      (Or.inr ((capturedW_Dcol hn hsc hwf hst 0).mpr rfl)))
  have hdeadne : ∀ p, p ≠ 0 → (capturedOf (Dcol D0 t_c) t_c .b
      ++ capturedOf (Dcol D0 t_c) t_c .w).contains p = false := by
    intro p hp
    cases hc : (capturedOf (Dcol D0 t_c) t_c .b
        ++ capturedOf (Dcol D0 t_c) t_c .w).contains p
    · rfl
    · exfalso
      rcases List.mem_append.mp (List.contains_iff_mem.mp hc) with h | h
      · exact (capturedB_Dcol hn hsc hwf t_c p).mp h
      · exact hp ((capturedW_Dcol hn hsc hwf hst p).mp h)
  have hany1 : (capturedOf (Dcol D0 t_c) t_c .w).any (fun q => adjI n 1 q) = true := by
    have hadj10 : adjI n 1 0 = true := adjI_symm (by
      have := adjI_step_y (n:=n) (x:=0) (y:=0) (by omega) (by omega) (by omega)
      simpa using this)
    exact List.any_eq_true.mpr ⟨0, (capturedW_Dcol hn hsc hwf hst 0).mpr rfl, hadj10⟩
  apply display_ext; apply Array.ext
  · rw [basicCap_size]
    show n*n = (Eres D0 t_c).cells.size
    unfold Eres; rw [set_size, set_size, hsz1]
  · intro p h1 h2
    have hp : p < n*n := by rw [basicCap_size] at h1; exact h1
    rw [← get_in_bounds _ p h1, ← get_in_bounds (Eres D0 t_c) p h2]
    show (basicCap (Dcol D0 t_c) t_c).get p = (Eres D0 t_c).get p
    unfold basicCap
    rw [get_map_range, if_pos hp]
    by_cases hp0 : p = 0
    · subst hp0
      rw [if_pos hdead0, Eres_get_0 hn hwf]
    · rw [if_neg (by rw [hdeadne p hp0]; exact Bool.noConfusion)]
      unfold Eres
      rw [get_set_ne _ _ _ _ hp0]
      by_cases hp1 : p = 1
      · subst hp1
        rw [get_set_self _ _ _ (by rw [hsz1]; exact (sb hn).2.2.1)]
        rw [if_pos (by rw [kind_Dcol_1 hn hsc hwf, hany1]; rfl)]
        have hg1 : (Dcol D0 t_c).get 1 = some (.r, t_c) :=
          get_set_self D0 1 (some (.r, t_c)) (by rw [hwf]; exact (sb hn).2.2.1)
        rw [hg1]; rfl
      · rw [get_set_ne _ _ _ _ hp1]
        have hnr : (kindAt (Dcol D0 t_c) p == some DKind.r) = false := by
          cases hb : (kindAt (Dcol D0 t_c) p == some DKind.r)
          · rfl
          · exact absurd (red_Dcol hn hsc hwf t_c (beq_iff_eq.mp hb)) hp1
        rw [if_neg (by rw [hnr]; exact Bool.noConfusion),
          if_neg (by rw [hnr]; exact Bool.noConfusion)]

/-! ### orOp of the collision display equals the resolved display -/

theorem Eres_kind (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) (p : Nat) :
    kindAt (Eres D0 t_c) p
      = if p = 0 then none else if p = 1 then some .b else kindAt (kd5 (n := n)) p := by
  have hsz : (Dcol D0 t_c).cells.size = n*n := wfd_set _ _ _ hwf
  have hwfDcol : WFD (Dcol D0 t_c) := wfd_set _ _ _ hwf
  unfold Eres
  by_cases hp0 : p = 0
  · subst hp0; rw [if_pos rfl]
    unfold kindAt; rw [get_set_self _ _ _ (by rw [set_size, hsz]; exact (sb hn).2.2.2.1)]; rfl
  · rw [if_neg hp0]
    have hkne : kindAt (((Dcol D0 t_c).set 1 (some (.b, t_c))).set 0 none) p
        = kindAt ((Dcol D0 t_c).set 1 (some (.b, t_c))) p := by
      unfold kindAt; rw [get_set_ne _ _ _ _ hp0]
    rw [hkne, kind_set (Dcol D0 t_c) 1 (sb hn).2.2.1 hwfDcol .b t_c p]
    by_cases hp1 : p = 1
    · rw [if_pos hp1, if_pos hp1]
    · rw [if_neg hp1, if_neg hp1, Dcol_kind hn hsc hwf, if_neg hp1]

theorem occ_kd5_cases (hn : 5 ≤ n) {i : Nat} (h : occD (kd5 (n := n)) i = true) :
    i = 0 ∨ i = 3 ∨ i = n ∨ i = dW1 n ∨ i = dW2 n := by
  rcases kind_some_of_occ h with ⟨k, hk⟩
  cases k with
  | w => rcases white_kd5 hn hk with h' | h' | h'
         · exact Or.inl h'
         · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
         · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  | b => rcases black_kd5 hn hk with h' | h'
         · exact Or.inr (Or.inl h')
         · exact Or.inr (Or.inr (Or.inl h'))
  | r => exact absurd hk (kd5_not_red hn i)

theorem occ_Eres_cases (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) {i : Nat} (h : occD (Eres D0 t_c) i = true) :
    i = 1 ∨ i = 3 ∨ i = n ∨ i = dW1 n ∨ i = dW2 n := by
  rcases kind_some_of_occ h with ⟨k, hk⟩
  by_cases hi1 : i = 1
  · exact Or.inl hi1
  · by_cases hi0 : i = 0
    · rw [Eres_kind hn hsc hwf, if_pos hi0] at hk; exact absurd hk (by simp)
    · rw [Eres_kind hn hsc hwf, if_neg hi0, if_neg hi1] at hk
      rcases occ_kd5_cases hn (occ_true_of_kind hk) with h' | h' | h' | h' | h'
      · exact absurd h' hi0
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

/-- The resolved display is legal: every stone breathes (A2's black group
    now breathes at the emptied A1). -/
theorem isLegal_Eres (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) : IsLegal (Eres D0 t_c) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  -- occ/kind readers on Eres via Eres_kind
  have hkE : ∀ p, kindAt (Eres D0 t_c) p
      = if p = 0 then none else if p = 1 then some .b else kindAt (kd5 (n := n)) p :=
    Eres_kind hn hsc hwf t_c
  have hoccE : ∀ p, p ≠ 0 → p ≠ 1 → occD (Eres D0 t_c) p = occD (kd5 (n := n)) p := by
    intro p hp0 hp1
    have hk : kindAt (Eres D0 t_c) p = kindAt (kd5 (n := n)) p := by
      rw [hkE, if_neg hp0, if_neg hp1]
    cases hK : kindAt (kd5 (n := n)) p with
    | none => rw [occ_of_kind_eq (hk.trans hK), occ_of_kind_eq hK]
    | some k => rw [occ_true_of_kind (hk.trans hK), occ_true_of_kind hK]
  have hoccE0 : occD (Eres D0 t_c) 0 = false :=
    occ_of_kind_eq (by rw [hkE, if_pos rfl])
  have hadj01 : adjI n 0 1 = true := by
    have := adjI_step_y (n:=n) (x:=0) (y:=0) (by omega) (by omega) (by omega); simpa using this
  have hadjn1n : adjI n (n+1) n = true := adjI_symm (by
    have := adjI_step_y (n:=n) (x:=1) (y:=0) (by omega) (by omega) (by omega); simpa using this)
  intro i hi
  rcases occ_Eres_cases hn hsc hwf t_c hi with h | h | h | h | h
  · rw [h]
    exact has_lib (Eres D0 t_c) 1 0 .b (sb hn).2.2.2.1 hoccE0
      (by rw [hkE, if_neg (by omega), if_pos rfl]) hadj01
  · rw [h]
    exact has_lib (Eres D0 t_c) 3 2 .b (sb hn).2.1
      (by rw [hoccE 2 (by omega) (by omega)]; exact occ_of_kind_eq (by
        rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2),
          if_neg (by omega), if_neg (by omega)]))
      (by rw [hkE, if_neg (by omega), if_neg (by omega), kd5_kind_3 hn]) (adj_2_3 hn)
  · rw [h]
    exact has_lib (Eres D0 t_c) n (n+1) .b (sb hn).2.2.2.2.2.1
      (by rw [hoccE (n+1) (by omega) (by omega)]; exact occ_of_kind_eq (by
        rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1),
          if_neg (by omega), if_neg (by omega)]))
      (by rw [hkE, if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega), kd5_kind_n hn])
      hadjn1n
  · rw [h]
    exact has_lib (Eres D0 t_c) (dW1 n) (dE1 n) .w (pk_bounds hn).2.2.2.1
      (by rw [hoccE (dE1 n) he1_0 he1_1]; exact occ_of_kind_eq (by
        rw [kd5_kind hn, if_neg he1_0, if_neg he1_w2, if_neg he1_w1, if_neg he1_n, if_neg he1_3]))
      (by rw [hkE, if_neg hw1_0, if_neg hw1_1, kd5_kind hn, if_neg hw1_0,
        if_neg hw1_w2, if_pos rfl]) (adj_E1_W1 hn)
  · rw [h]
    exact has_lib (Eres D0 t_c) (dW2 n) (dE2 n) .w (pk_bounds hn).2.2.2.2
      (by rw [hoccE (dE2 n) he2_0 he2_1]; exact occ_of_kind_eq (by
        rw [kd5_kind hn, if_neg he2_0, if_neg he2_w2, if_neg he2_w1, if_neg he2_n, if_neg he2_3]))
      (by rw [hkE, if_neg hw2_0, if_neg hw2_1, kd5_kind hn, if_neg hw2_0,
        if_pos rfl]) (adj_E2_W2 hn)

/-- The collision display's objective reduction is the resolved display. -/
theorem orOp_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) (htc : 1 ≤ t_c) :
    orOp n t_c (Dcol D0 t_c) = Eres D0 t_c := by
  have hwfE : WFD (Eres D0 t_c) := by
    show (Eres D0 t_c).cells.size = n*n
    unfold Eres; rw [set_size, set_size]; exact wfd_set _ _ _ hwf
  have hnocap : ∀ (k : DKind) (t' : Nat), capturedOf (Eres D0 t_c) t' k = [] :=
    fun k t' => nocap_of_legal _ _ (fun _ => rfl) (isLegal_Eres hn hsc hwf t_c) k t'
  have hbcE : ∀ t', basicCap (Eres D0 t_c) t' = Eres D0 t_c :=
    fun t' => basicCap_id_nil _ t' hwfE (hnocap .b t') (hnocap .w t')
  have hbcD : basicCap (Dcol D0 t_c) t_c = Eres D0 t_c := basicCap_Dcol hn hsc hwf hst
  have hEDne : ¬ (Eres D0 t_c == Dcol D0 t_c) = true := by
    intro hc
    have h0 : (Eres D0 t_c).get 0 = (Dcol D0 t_c).get 0 :=
      congrArg (fun D => D.get 0) (display_eq_of_beq hc)
    rw [Eres_get_0 hn hwf] at h0
    have hocc : occD (Dcol D0 t_c) 0 = true := by
      rw [occD_Dcol hn hsc hwf, if_neg (by omega)]; exact occ_true_of_kind (kd5_kind_0 hn)
    rw [occ_of_get_none h0.symm] at hocc; exact absurd hocc (by decide)
  have hne : ¬ (basicCap (Dcol D0 t_c) t_c == Dcol D0 t_c) = true := by
    rw [hbcD]; exact hEDne
  have hcapFix : capFix (n*n+1) (Dcol D0 t_c) t_c = Eres D0 t_c := by
    show (if (basicCap (Dcol D0 t_c) t_c == Dcol D0 t_c) = true then Dcol D0 t_c
      else capFix (n*n) (basicCap (Dcol D0 t_c) t_c) t_c) = Eres D0 t_c
    rw [if_neg hne, hbcD, capFix_id (Eres D0 t_c) t_c (hbcE t_c) (n*n)]
  show stages (t_c+1) (Dcol D0 t_c) t_c = Eres D0 t_c
  rw [show stages (t_c+1) (Dcol D0 t_c) t_c
      = (if (t_c == 0) = true then Dcol D0 t_c
        else if (capFix (n*n+1) (Dcol D0 t_c) t_c == Dcol D0 t_c) = true then Dcol D0 t_c
          else stages t_c (capFix (n*n+1) (Dcol D0 t_c) t_c) (t_c-1)) from rfl]
  rw [if_neg (by simp only [beq_iff_eq]; omega), hcapFix, if_neg hEDne]
  exact stages_id (Eres D0 t_c) hbcE t_c (t_c-1)

/-! ### The collision verdict and its execution -/

theorem occ_Eres_1 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) : occD (Eres D0 t_c) 1 = true :=
  occ_true_of_kind (by rw [Eres_kind hn hsc hwf, if_neg (by omega), if_pos rfl])

theorem occ_Eres_0 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) : occD (Eres D0 t_c) 0 = false :=
  occ_of_kind_eq (by rw [Eres_kind hn hsc hwf, if_pos rfl])

theorem Dcol_get_0 (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) :
    (Dcol D0 t_c).get 0 = some (.w, stampAt (Dcol D0 t_c) 0) := by
  have hocc : occD (Dcol D0 t_c) 0 = true := by
    rw [occD_Dcol hn hsc hwf, if_neg (by omega)]; exact occ_true_of_kind (kd5_kind_0 hn)
  rcases kind_some_of_occ hocc with ⟨k, hk⟩
  have hkw : k = .w := by
    have := kind_Dcol_0 hn hsc hwf t_c; rw [hk] at this; exact (Option.some.inj this)
  subst hkw
  unfold kindAt at hk
  cases hg : (Dcol D0 t_c).get 0 with
  | none => rw [hg] at hk; exact absurd hk (by simp)
  | some c => obtain ⟨kk, st⟩ := c
              rw [hg] at hk; simp at hk; subst hk
              unfold stampAt; rw [hg]; rfl

theorem occ_Eres_of_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) {i : Nat} (hi0 : i ≠ 0)
    (hocc : occD (Dcol D0 t_c) i = true) : occD (Eres D0 t_c) i = true := by
  by_cases hi1 : i = 1
  · rw [hi1]; exact occ_Eres_1 hn hsc hwf t_c
  · rw [show occD (Eres D0 t_c) i = occD (Dcol D0 t_c) i from by
      unfold Eres occD; rw [get_set_ne _ _ _ _ hi0, get_set_ne _ _ _ _ hi1]]
    exact hocc

/-- The collision verdict: remove A1, recolor A2 black. -/
theorem verOf_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) {t_c : Nat} (hst : StampsBelow D0 t_c) (htc : 1 ≤ t_c) :
    verOf n t_c (Dcol D0 t_c)
      = ⟨[(0, stampAt (Dcol D0 t_c) 0)], [(1, t_c, .b)]⟩ := by
  unfold verOf
  rw [orOp_Dcol hn hsc hwf hst htc]
  have hg0 := Dcol_get_0 hn hsc hwf t_c
  have hg1 : (Dcol D0 t_c).get 1 = some (.r, t_c) :=
    get_set_self D0 1 (some (.r, t_c)) (by rw [hwf]; exact (sb hn).2.2.1)
  have hsz : (Dcol D0 t_c).cells.size = n*n := wfd_set _ _ _ hwf
  have hE1 : (Eres D0 t_c).get 1 = some (.b, t_c) := by
    unfold Eres; rw [get_set_ne _ _ _ _ (by omega),
      get_set_self _ _ _ (by rw [hsz]; exact (sb hn).2.2.1)]
  simp only [allIdx]
  congr 1
  · apply filterMap_range_single _ (0, stampAt (Dcol D0 t_c) 0) 0 (n*n) (sb hn).2.2.2.1
    · rw [hg0]
      show (if occD (Eres D0 t_c) 0 = true then none else some (0, stampAt (Dcol D0 t_c) 0))
        = some (0, stampAt (Dcol D0 t_c) 0)
      rw [if_neg (show ¬ (occD (Eres D0 t_c) 0 = true) from by
        rw [occ_Eres_0 hn hsc hwf t_c]; decide)]
    · intro i hi
      show (match (Dcol D0 t_c).get i with
        | some (_, st) => if occD (Eres D0 t_c) i then none else some (i, st)
        | none => none) = none
      cases hg : (Dcol D0 t_c).get i with
      | none => rfl
      | some c =>
        obtain ⟨k, st⟩ := c
        show (if occD (Eres D0 t_c) i = true then none else some (i, st)) = none
        rw [if_pos (occ_Eres_of_Dcol hn hsc hwf t_c hi (by unfold occD; rw [hg]; rfl))]
  · apply filterMap_range_single _ (1, t_c, DKind.b) 1 (n*n) (sb hn).2.2.1
    · show (match (Dcol D0 t_c).get 1, (Eres D0 t_c).get 1 with
        | some (.r, st), some (k, _) => if k != DKind.r then some (1, st, k) else none
        | _, _ => none) = some (1, t_c, DKind.b)
      rw [hg1, hE1]; rfl
    · intro i hi
      show (match (Dcol D0 t_c).get i, (Eres D0 t_c).get i with
        | some (.r, st), some (k, _) => if k != DKind.r then some (i, st, k) else none
        | _, _ => none) = none
      cases hg : (Dcol D0 t_c).get i with
      | none => rfl
      | some c =>
        obtain ⟨k', st⟩ := c
        cases k' with
        | r => exact absurd (red_Dcol hn hsc hwf t_c (by unfold kindAt; rw [hg]; rfl)) hi
        | b => rfl
        | w => rfl

/-- Setting distinct cells commutes. -/
theorem set_set_comm {D : Display n} {i j : Nat} (hij : i ≠ j) (a b : Cell)
    (hi : i < n*n) (hj : j < n*n) (hwf : WFD D) :
    (D.set i a).set j b = (D.set j b).set i a := by
  have hsz1 : (D.set i a).cells.size = n*n := by rw [set_size]; exact hwf
  have hsz2 : (D.set j b).cells.size = n*n := by rw [set_size]; exact hwf
  apply display_ext; apply Array.ext
  · rw [set_size, set_size, set_size, set_size]
  · intro p h1 h2
    have hp : p < n*n := by rw [set_size, set_size, hwf] at h1; exact h1
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
    by_cases hpj : p = j
    · subst hpj
      rw [get_set_self _ _ _ (by rw [hsz1]; exact hp), get_set_ne _ _ _ _ (Ne.symm hij),
        get_set_self _ _ _ (by rw [hwf]; exact hp)]
    · by_cases hpi : p = i
      · subst hpi
        rw [get_set_ne _ _ _ _ hpj, get_set_self _ _ _ (by rw [hwf]; exact hp),
          get_set_self _ _ _ (by rw [hsz2]; exact hp)]
      · rw [get_set_ne _ _ _ _ hpj, get_set_ne _ _ _ _ hpi, get_set_ne _ _ _ _ hpi,
          get_set_ne _ _ _ _ hpj]

/-- Executing the collision verdict on the collision display yields the
    resolved display: A1 emptied, A2 black. -/
theorem execV_Dcol (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c : Nat) :
    execV n ⟨[(0, stampAt (Dcol D0 t_c) 0)], [(1, t_c, DKind.b)]⟩ (Dcol D0 t_c)
      = Eres D0 t_c := by
  have hsz : (Dcol D0 t_c).cells.size = n*n := wfd_set _ _ _ hwf
  have hg0 := Dcol_get_0 hn hsc hwf t_c
  have hg1 : (Dcol D0 t_c).get 1 = some (.r, t_c) :=
    get_set_self D0 1 (some (.r, t_c)) (by rw [hwf]; exact (sb hn).2.2.1)
  have hd1g1 : ((Dcol D0 t_c).set 0 none).get 1 = some (.r, t_c) := by
    rw [get_set_ne _ _ _ _ (by omega)]; exact hg1
  unfold execV
  simp only [List.foldl_cons, List.foldl_nil, hg0, hd1g1, beq_self_eq_true, if_true]
  -- goal: ((Dcol D0 t_c).set 0 none).set 1 (some (.b, t_c)) = Eres D0 t_c
  unfold Eres
  exact set_set_comm (by omega) none (some (.b, t_c)) (sb hn).2.2.2.1 (sb hn).2.2.1 (wfd_set _ _ _ hwf)

/-! ### The final joint move B3/A3 on the two branches -/

/-- The neighbors of A3 = 2 are A2, A4 and B3. -/
theorem nbr_2 (hn : 5 ≤ n) {q : Nat} (h : adjI n q 2 = true) :
    q = 1 ∨ q = 3 ∨ q = n + 2 := by
  have hn0 : 0 < n := by omega
  have h2n : (2:Nat)/n = 0 := Nat.div_eq_of_lt (by omega)
  have h2m : (2:Nat)%n = 2 := Nat.mod_eq_of_lt (by omega)
  have hqe := div_mod_recomp (n := n) (q := q) hn0
  rcases adjI_inv h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [h2n] at hx; rw [h2m] at hy
    rcases hy with h' | h'
    · left; have hb : q % n = 1 := by omega
      rw [hx, hb] at hqe; simpa using hqe
    · right; left; have hb : q % n = 3 := h'.symm
      rw [hx, hb] at hqe; simpa using hqe
  · rw [h2m] at hy; rw [h2n] at hx
    rcases hx with h' | h'
    · exact absurd h' (Nat.succ_ne_zero _)
    · right; right; have ha : q / n = 1 := h'.symm
      rw [ha, hy] at hqe; omega

/-- B3 = n+2 and A3 = 2 are adjacent. -/
theorem adj_2_n2 (hn : 5 ≤ n) : adjI n 2 (n+2) = true := by
  have := adjI_step_x (n:=n) (x:=0) (y:=2) (by omega) (by omega) (by omega)
  simpa using this

def ba0f (n : Nat) : Display n := (ba0 n).set (n+2) (some (.b, 0))
def ba0w2 (n : Nat) : Display n := (ba0 n).set 2 (some (.w, 0))
def ba1p (n : Nat) : Display n := (ba1 n).set (n+2) (some (.b, 0))
def ba1w2 (n : Nat) : Display n := (ba1 n).set 2 (some (.w, 0))
def ba1f (n : Nat) : Display n := (ba1p n).set 2 (some (.w, 0))

theorem ba0f_wfd : WFD (ba0f (n := n)) := wfd_set _ _ _ ba0_wfd
theorem ba0w2_wfd : WFD (ba0w2 (n := n)) := wfd_set _ _ _ ba0_wfd
theorem ba1p_wfd : WFD (ba1p (n := n)) := wfd_set _ _ _ ba1_wfd
theorem ba1w2_wfd : WFD (ba1w2 (n := n)) := wfd_set _ _ _ ba1_wfd
theorem ba1f_wfd : WFD (ba1f (n := n)) := wfd_set _ _ _ ba1p_wfd

theorem ba0f_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba0f (n := n)) w = if w = n+2 then some .b else kindAt (ba0 (n := n)) w := by
  unfold ba0f; rw [kind_set (ba0 n) (n+2) (sb hn).2.2.2.2.2.2 ba0_wfd]

theorem ba0w2_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba0w2 (n := n)) w = if w = 2 then some .w else kindAt (ba0 (n := n)) w := by
  unfold ba0w2; rw [kind_set (ba0 n) 2 (sb hn).2.1 ba0_wfd]

theorem ba1p_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba1p (n := n)) w = if w = n+2 then some .b else kindAt (ba1 (n := n)) w := by
  unfold ba1p; rw [kind_set (ba1 n) (n+2) (sb hn).2.2.2.2.2.2 ba1_wfd]

theorem ba1w2_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba1w2 (n := n)) w = if w = 2 then some .w else kindAt (ba1 (n := n)) w := by
  unfold ba1w2; rw [kind_set (ba1 n) 2 (sb hn).2.1 ba1_wfd]

theorem ba1f_kind (hn : 5 ≤ n) (w : Nat) :
    kindAt (ba1f (n := n)) w = if w = 2 then some .w else kindAt (ba1p (n := n)) w := by
  unfold ba1f; rw [kind_set (ba1p n) 2 (sb hn).2.1 ba1p_wfd]

/-! ### Branch cell enumerations and extra geometry -/

theorem white_ba0 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba0 (n := n)) p = some .w) :
    p = dW1 n ∨ p = dW2 n := by
  rw [ba0_kind hn] at h
  by_cases hd2 : p = dW2 n
  · exact Or.inr hd2
  · by_cases hd1 : p = dW1 n
    · exact Or.inl hd1
    · exfalso
      by_cases h0 : p = 0
      · rw [if_pos h0] at h; exact absurd h (by decide)
      · by_cases h1 : p = 1
        · rw [if_neg h0, if_pos h1] at h; exact absurd h (by decide)
        · by_cases hnn : p = n
          · rw [if_neg h0, if_neg h1, if_neg hd2, if_neg hd1, if_pos hnn] at h
            exact absurd h (by decide)
          · by_cases h3 : p = 3
            · rw [if_neg h0, if_neg h1, if_neg hd2, if_neg hd1, if_neg hnn, if_pos h3] at h
              exact absurd h (by decide)
            · rw [if_neg h0, if_neg h1, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
              exact absurd h (by decide)

theorem black_ba0 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba0 (n := n)) p = some .b) :
    p = 1 ∨ p = 3 ∨ p = n := by
  rw [ba0_kind hn] at h
  by_cases h1 : p = 1
  · exact Or.inl h1
  · by_cases hnn : p = n
    · exact Or.inr (Or.inr hnn)
    · by_cases h3 : p = 3
      · exact Or.inr (Or.inl h3)
      · exfalso
        by_cases h0 : p = 0
        · rw [if_pos h0] at h; exact absurd h (by decide)
        · by_cases hd2 : p = dW2 n
          · rw [if_neg h0, if_neg h1, if_pos hd2] at h; exact absurd h (by decide)
          · by_cases hd1 : p = dW1 n
            · rw [if_neg h0, if_neg h1, if_neg hd2, if_pos hd1] at h; exact absurd h (by decide)
            · rw [if_neg h0, if_neg h1, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
              exact absurd h (by decide)

theorem white_ba1 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba1 (n := n)) p = some .w) :
    p = 0 ∨ p = 1 ∨ p = dW1 n ∨ p = dW2 n := by
  rw [ba1_kind hn] at h
  by_cases h1 : p = 1
  · exact Or.inr (Or.inl h1)
  · by_cases h0 : p = 0
    · exact Or.inl h0
    · by_cases hd2 : p = dW2 n
      · exact Or.inr (Or.inr (Or.inr hd2))
      · by_cases hd1 : p = dW1 n
        · exact Or.inr (Or.inr (Or.inl hd1))
        · exfalso
          by_cases hnn : p = n
          · rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1, if_pos hnn] at h
            exact absurd h (by decide)
          · by_cases h3 : p = 3
            · rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_pos h3] at h
              exact absurd h (by decide)
            · rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
              exact absurd h (by decide)

theorem black_ba1 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba1 (n := n)) p = some .b) :
    p = 3 ∨ p = n := by
  rw [ba1_kind hn] at h
  by_cases hnn : p = n
  · exact Or.inr hnn
  · by_cases h3 : p = 3
    · exact Or.inl h3
    · exfalso
      by_cases h1 : p = 1
      · rw [if_pos h1] at h; exact absurd h (by decide)
      · by_cases h0 : p = 0
        · rw [if_neg h1, if_pos h0] at h; exact absurd h (by decide)
        · by_cases hd2 : p = dW2 n
          · rw [if_neg h1, if_neg h0, if_pos hd2] at h; exact absurd h (by decide)
          · by_cases hd1 : p = dW1 n
            · rw [if_neg h1, if_neg h0, if_neg hd2, if_pos hd1] at h; exact absurd h (by decide)
            · rw [if_neg h1, if_neg h0, if_neg hd2, if_neg hd1, if_neg hnn, if_neg h3] at h
              exact absurd h (by decide)

theorem sb4 (hn : 5 ≤ n) : 4 < n*n ∧ 2*n < n*n := by
  have h : 5*5 ≤ n*n := Nat.mul_le_mul (by omega) (by omega)
  have h3n : n*3 ≤ n*n := Nat.mul_le_mul_left n (by omega)
  omega

theorem adj_4_3 (hn : 5 ≤ n) : adjI n 4 3 = true := adjI_symm (by
  have := adjI_step_y (n:=n) (x:=0) (y:=3) (by omega) (by omega) (by omega); simpa using this)

/-! ### Placement transfer helpers -/

theorem pl_kind_ne (d : Display n) (c : DKind) (i : Nat) (hi : i < n*n) (hwf : WFD d)
    {z : Nat} (hz : z ≠ i) : kindAt (placedN n d c i) z = kindAt d z := by
  unfold placedN; rw [kind_set d i hi hwf, if_neg hz]

theorem pl_occ_ne (d : Display n) (c : DKind) (i : Nat) (hi : i < n*n) (hwf : WFD d)
    {z : Nat} (hz : z ≠ i) : occD (placedN n d c i) z = occD d z := by
  unfold placedN; rw [occ_set d i hi hwf, if_neg hz]

/-- A wall stone's escape liberty survives any placement away from it. -/
theorem lib_wall (d : Display n) (c : DKind) (i : Nat) (hi : i < n*n) (hwf : WFD d)
    (w e : Nat) (kk : DKind) (he : e < n*n) (hwe : w ≠ i) (hee : e ≠ i)
    (hkw : kindAt d w = some kk) (hoe : occD d e = false) (hadj : adjI n e w = true) :
    noLibD (placedN n d c i) (componentD (placedN n d c i) w) = false :=
  has_lib (placedN n d c i) w e kk he
    (by rw [pl_occ_ne d c i hi hwf hee]; exact hoe)
    (by rw [pl_kind_ne d c i hi hwf hwe]; exact hkw) hadj

theorem dEn2 (hn : 5 ≤ n) : dE1 n ≠ n+2 ∧ dE2 n ≠ n+2 := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  have hb : 2*n ≤ (n-3)*n := Nat.mul_le_mul_right n (by omega)
  simp only [dE1, dE2]; refine ⟨?_, ?_⟩ <;> omega

/-- (A) Black at B3 on the black-captures branch: a quiet placement. -/
theorem gm_A (hn : 5 ≤ n) : goMoveN n (ba0 n) .b (n+2) = some (ba0f n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have hn2lt : n+2 < n*n := (sb hn).2.2.2.2.2.2
  have hemp : occD (ba0 n) (n+2) = false := occ_of_kind_eq (by
    rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n2),
      if_neg (Ne.symm hw1_n2), if_neg (by omega), if_neg (by omega)])
  have hdead : deadOppN n (ba0 n) .b (n+2) = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ n+2 := by
      intro he; rw [he, kindAt_placedN_self (ba0 n) .b (n+2) ba0_wfd hn2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba0 n) .b (n+2) hn2lt ba0_wfd hpne] at hp
    rcases white_ba0 hn hp with h | h
    · subst h
      exact lib_wall (ba0 n) .b (n+2) hn2lt ba0_wfd (dW1 n) (dE1 n) .w
        (pk_bounds hn).2.2.2.1 hw1_n2 (dEn2 hn).1
        (by rw [ba0_kind hn, if_neg hw1_0, if_neg hw1_1, if_neg hw1_w2, if_pos rfl])
        (occ_of_kind_eq (by rw [ba0_kind hn, if_neg he1_0, if_neg he1_1, if_neg he1_w2,
          if_neg he1_w1, if_neg he1_n, if_neg he1_3])) (adj_E1_W1 hn)
    · subst h
      exact lib_wall (ba0 n) .b (n+2) hn2lt ba0_wfd (dW2 n) (dE2 n) .w
        (pk_bounds hn).2.2.2.2 hw2_n2 (dEn2 hn).2
        (by rw [ba0_kind hn, if_neg hw2_0, if_neg hw2_1, if_pos rfl])
        (occ_of_kind_eq (by rw [ba0_kind hn, if_neg he2_0, if_neg he2_1, if_neg he2_w2,
          if_neg he2_w1, if_neg he2_n, if_neg he2_3])) (adj_E2_W2 hn)
  have hsui : suicideN n (ba0 n) .b (n+2) = false :=
    suicideN_false_of (ba0 n) .b (n+2) ba0_wfd hn2lt (by decide) hdead
      (has_lib (placedN n (ba0 n) .b (n+2)) (n+2) 2 .b (sb hn).2.1
        (by rw [pl_occ_ne (ba0 n) .b (n+2) hn2lt ba0_wfd (by omega : (2:Nat) ≠ n+2)]
            exact occ_of_kind_eq (by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega),
              if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]))
        (kindAt_placedN_self (ba0 n) .b (n+2) ba0_wfd hn2lt) (adj_2_n2 hn))
  rw [goMoveN_quiet (ba0 n) .b (n+2) ba0_wfd hemp hdead hsui]; rfl

/-- A white group containing A2 breathes at B2. -/
theorem lib_via1 (D : Display n) (p : Nat) (h1mem : 1 ∈ componentD D p)
    (hn1lt : n+1 < n*n) (hon1 : occD D (n+1) = false) (hadj : adjI n (n+1) 1 = true) :
    noLibD D (componentD D p) = false :=
  (noLibD_eq_false_iff D (componentD D p)).mpr
    ⟨n+1, List.mem_range.mpr hn1lt, hon1, 1, h1mem, hadj⟩

theorem c4_ne (hn : 5 ≤ n) : (4:Nat) ≠ dW1 n ∧ (4:Nat) ≠ dW2 n := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  have hb : 2*n ≤ (n-3)*n := Nat.mul_le_mul_right n (by omega)
  simp only [dW1, dW2]; refine ⟨?_, ?_⟩ <;> omega

/-- (C) White at A3 on the black-captures branch: quiet, breathes at B3. -/
theorem gm_C (hn : 5 ≤ n) : goMoveN n (ba0 n) .w 2 = some (ba0w2 n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have h2lt : (2:Nat) < n*n := (sb hn).2.1
  have hemp : occD (ba0 n) 2 = false := occ_of_kind_eq (by
    rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_2),
      if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])
  have hkb3 : kindAt (ba0 n) 3 = some .b := by
    rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_3),
      if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]
  have hkbn : kindAt (ba0 n) n = some .b := by
    rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n),
      if_neg (Ne.symm hw1_n), if_pos rfl]
  have hdead : deadOppN n (ba0 n) .w 2 = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ 2 := by
      intro he; rw [he, kindAt_placedN_self (ba0 n) .w 2 ba0_wfd h2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba0 n) .w 2 h2lt ba0_wfd hpne] at hp
    rcases black_ba0 hn hp with h | h | h
    · subst h
      exact lib_wall (ba0 n) .w 2 h2lt ba0_wfd 1 0 .b (sb hn).2.2.2.1 (by omega) (by omega)
        (by rw [ba0_kind hn, if_neg (by omega), if_pos rfl])
        (occ_of_kind_eq (by rw [ba0_kind hn, if_pos rfl])) (adj_0_1 (by omega))
    · subst h
      exact lib_wall (ba0 n) .w 2 h2lt ba0_wfd 3 4 .b (sb4 hn).1 (by omega) (by omega) hkb3
        (occ_of_kind_eq (by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (c4_ne hn).2, if_neg (c4_ne hn).1, if_neg (by omega), if_neg (by omega)]))
        (adj_4_3 hn)
    · rw [h]
      exact lib_wall (ba0 n) .w 2 h2lt ba0_wfd n (n+1) .b (sb hn).2.2.2.2.2.1 (by omega)
        (by omega) hkbn
        (occ_of_kind_eq (by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)]))
        (adjI_symm (adj_n_n1 (by omega)))
  have hsui : suicideN n (ba0 n) .w 2 = false :=
    suicideN_false_of (ba0 n) .w 2 ba0_wfd h2lt (by decide) hdead
      (has_lib (placedN n (ba0 n) .w 2) 2 (n+2) .w (sb hn).2.2.2.2.2.2
        (by rw [pl_occ_ne (ba0 n) .w 2 h2lt ba0_wfd (by omega : (n+2:Nat) ≠ 2)]
            exact occ_of_kind_eq (by rw [ba0_kind hn, if_neg (by omega), if_neg (by omega),
              if_neg (Ne.symm hw2_n2), if_neg (Ne.symm hw1_n2), if_neg (by omega), if_neg (by omega)]))
        (kindAt_placedN_self (ba0 n) .w 2 ba0_wfd h2lt) (adjI_symm (adj_2_n2 hn)))
  rw [goMoveN_quiet (ba0 n) .w 2 ba0_wfd hemp hdead hsui]; rfl

/-- (A') Black at B3 on the white-joins branch: a quiet placement. -/
theorem gm_A' (hn : 5 ≤ n) : goMoveN n (ba1 n) .b (n+2) = some (ba1p n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have hn2lt : n+2 < n*n := (sb hn).2.2.2.2.2.2
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  have hemp : occD (ba1 n) (n+2) = false := occ_of_kind_eq (by
    rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n2),
      if_neg (Ne.symm hw1_n2), if_neg (by omega), if_neg (by omega)])
  have hk0 : kindAt (placedN n (ba1 n) .b (n+2)) 0 = some .w := by
    rw [pl_kind_ne (ba1 n) .b (n+2) hn2lt ba1_wfd (by omega), ba1_kind hn,
      if_neg (by omega), if_pos rfl]
  have hk1 : kindAt (placedN n (ba1 n) .b (n+2)) 1 = some .w := by
    rw [pl_kind_ne (ba1 n) .b (n+2) hn2lt ba1_wfd (by omega), ba1_kind hn, if_pos rfl]
  have hon1 : occD (placedN n (ba1 n) .b (n+2)) (n+1) = false := by
    rw [pl_occ_ne (ba1 n) .b (n+2) hn2lt ba1_wfd (by omega)]
    exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)])
  have hadj1n1 : adjI n (n+1) 1 = true := adjI_symm (adj_1_n1 (by omega))
  have h1mem0 : 1 ∈ componentD (placedN n (ba1 n) .b (n+2)) 0 :=
    (componentD_mem_iff (placedN n (ba1 n) .b (n+2)) 0 .w hk0 1).mpr
      (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1 (adjI_symm (adj_0_1 (by omega))))
  have hdead : deadOppN n (ba1 n) .b (n+2) = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ n+2 := by
      intro he; rw [he, kindAt_placedN_self (ba1 n) .b (n+2) ba1_wfd hn2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba1 n) .b (n+2) hn2lt ba1_wfd hpne] at hp
    rcases white_ba1 hn hp with h | h | h | h
    · subst h; exact lib_via1 _ 0 h1mem0 hn1lt hon1 hadj1n1
    · subst h; exact lib_via1 _ 1 (componentD_mem_self _ 1 .w hk1) hn1lt hon1 hadj1n1
    · subst h
      exact lib_wall (ba1 n) .b (n+2) hn2lt ba1_wfd (dW1 n) (dE1 n) .w
        (pk_bounds hn).2.2.2.1 hw1_n2 (dEn2 hn).1
        (by rw [ba1_kind hn, if_neg hw1_1, if_neg hw1_0, if_neg hw1_w2, if_pos rfl])
        (occ_of_kind_eq (by rw [ba1_kind hn, if_neg he1_1, if_neg he1_0, if_neg he1_w2,
          if_neg he1_w1, if_neg he1_n, if_neg he1_3])) (adj_E1_W1 hn)
    · subst h
      exact lib_wall (ba1 n) .b (n+2) hn2lt ba1_wfd (dW2 n) (dE2 n) .w
        (pk_bounds hn).2.2.2.2 hw2_n2 (dEn2 hn).2
        (by rw [ba1_kind hn, if_neg hw2_1, if_neg hw2_0, if_pos rfl])
        (occ_of_kind_eq (by rw [ba1_kind hn, if_neg he2_1, if_neg he2_0, if_neg he2_w2,
          if_neg he2_w1, if_neg he2_n, if_neg he2_3])) (adj_E2_W2 hn)
  have hsui : suicideN n (ba1 n) .b (n+2) = false :=
    suicideN_false_of (ba1 n) .b (n+2) ba1_wfd hn2lt (by decide) hdead
      (has_lib (placedN n (ba1 n) .b (n+2)) (n+2) 2 .b (sb hn).2.1
        (by rw [pl_occ_ne (ba1 n) .b (n+2) hn2lt ba1_wfd (by omega : (2:Nat) ≠ n+2)]
            exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
              if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]))
        (kindAt_placedN_self (ba1 n) .b (n+2) ba1_wfd hn2lt) (adj_2_n2 hn))
  rw [goMoveN_quiet (ba1 n) .b (n+2) ba1_wfd hemp hdead hsui]; rfl

/-- (C') White at A3 on the white-joins branch: quiet, joins the A1/A2 group. -/
theorem gm_C' (hn : 5 ≤ n) : goMoveN n (ba1 n) .w 2 = some (ba1w2 n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have h2lt : (2:Nat) < n*n := (sb hn).2.1
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  have hemp : occD (ba1 n) 2 = false := occ_of_kind_eq (by
    rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_2),
      if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])
  have hkb3 : kindAt (ba1 n) 3 = some .b := by
    rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_3),
      if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]
  have hkbn : kindAt (ba1 n) n = some .b := by
    rw [ba1_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n),
      if_neg (Ne.symm hw1_n), if_pos rfl]
  have hdead : deadOppN n (ba1 n) .w 2 = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ 2 := by
      intro he; rw [he, kindAt_placedN_self (ba1 n) .w 2 ba1_wfd h2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba1 n) .w 2 h2lt ba1_wfd hpne] at hp
    rcases black_ba1 hn hp with h | h
    · subst h
      exact lib_wall (ba1 n) .w 2 h2lt ba1_wfd 3 4 .b (sb4 hn).1 (by omega) (by omega) hkb3
        (occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (c4_ne hn).2, if_neg (c4_ne hn).1, if_neg (by omega), if_neg (by omega)]))
        (adj_4_3 hn)
    · rw [h]
      exact lib_wall (ba1 n) .w 2 h2lt ba1_wfd n (n+1) .b (sb hn).2.2.2.2.2.1 (by omega)
        (by omega) hkbn
        (occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)]))
        (adjI_symm (adj_n_n1 (by omega)))
  have hk1 : kindAt (placedN n (ba1 n) .w 2) 1 = some .w := by
    rw [pl_kind_ne (ba1 n) .w 2 h2lt ba1_wfd (by omega), ba1_kind hn, if_pos rfl]
  have hon1 : occD (placedN n (ba1 n) .w 2) (n+1) = false := by
    rw [pl_occ_ne (ba1 n) .w 2 h2lt ba1_wfd (by omega)]
    exact occ_of_kind_eq (by rw [ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)])
  have h1mem2 : 1 ∈ componentD (placedN n (ba1 n) .w 2) 2 :=
    (componentD_mem_iff (placedN n (ba1 n) .w 2) 2 .w
      (kindAt_placedN_self (ba1 n) .w 2 ba1_wfd h2lt) 1).mpr
      (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1 (adj_1_2 (by omega)))
  have hsui : suicideN n (ba1 n) .w 2 = false :=
    suicideN_false_of (ba1 n) .w 2 ba1_wfd h2lt (by decide) hdead
      (lib_via1 _ 2 h1mem2 hn1lt hon1 (adjI_symm (adj_1_n1 (by omega))))
  rw [goMoveN_quiet (ba1 n) .w 2 ba1_wfd hemp hdead hsui]; rfl

theorem white_ba1w2 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba1w2 (n := n)) p = some .w) :
    p = 0 ∨ p = 1 ∨ p = 2 ∨ p = dW1 n ∨ p = dW2 n := by
  rw [ba1w2_kind hn] at h
  by_cases h2 : p = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  · rw [if_neg h2] at h
    rcases white_ba1 hn h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem black_ba1p (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba1p (n := n)) p = some .b) :
    p = 3 ∨ p = n ∨ p = n+2 := by
  rw [ba1p_kind hn] at h
  by_cases h2 : p = n+2
  · exact Or.inr (Or.inr h2)
  · rw [if_neg h2] at h
    rcases black_ba1 hn h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem adj_n1_n2 (hn : 5 ≤ n) : adjI n (n+1) (n+2) = true := by
  have := adjI_step_y (n:=n) (x:=1) (y:=1) (by omega) (by omega) (by omega)
  simpa using this

theorem dE2ne (hn : 5 ≤ n) : dE1 n ≠ 2 ∧ dE2 n ≠ 2 := by
  obtain ⟨e1, e2, e3⟩ := mrel hn
  have hb : 2*n ≤ (n-3)*n := Nat.mul_le_mul_right n (by omega)
  simp only [dE1, dE2]; refine ⟨?_, ?_⟩ <;> omega

/-- (D') Black at B3 on the white-joins branch (A3 already down): quiet. -/
theorem gm_D' (hn : 5 ≤ n) : goMoveN n (ba1w2 n) .b (n+2) = some (ba1f n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have hn2lt : n+2 < n*n := (sb hn).2.2.2.2.2.2
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  -- kindAt of ba1w2 at 0,1,2 = white
  have hkw : ∀ z, z = 0 ∨ z = 1 ∨ z = 2 → kindAt (ba1w2 (n := n)) z = some .w := by
    rintro z (h | h | h)
    · rw [h, ba1w2_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_pos rfl]
    · rw [h, ba1w2_kind hn, if_neg (by omega), ba1_kind hn, if_pos rfl]
    · rw [h, ba1w2_kind hn, if_pos rfl]
  have hemp : occD (ba1w2 n) (n+2) = false := occ_of_kind_eq (by
    rw [ba1w2_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n2), if_neg (Ne.symm hw1_n2), if_neg (by omega), if_neg (by omega)])
  have hpk : ∀ z, z ≠ n+2 → kindAt (placedN n (ba1w2 n) .b (n+2)) z = kindAt (ba1w2 n) z :=
    fun z hz => pl_kind_ne (ba1w2 n) .b (n+2) hn2lt ba1w2_wfd hz
  have hk0 : kindAt (placedN n (ba1w2 n) .b (n+2)) 0 = some .w := by
    rw [hpk 0 (by omega)]; exact hkw 0 (Or.inl rfl)
  have hk1 : kindAt (placedN n (ba1w2 n) .b (n+2)) 1 = some .w := by
    rw [hpk 1 (by omega)]; exact hkw 1 (Or.inr (Or.inl rfl))
  have hk2 : kindAt (placedN n (ba1w2 n) .b (n+2)) 2 = some .w := by
    rw [hpk 2 (by omega)]; exact hkw 2 (Or.inr (Or.inr rfl))
  have hon1 : occD (placedN n (ba1w2 n) .b (n+2)) (n+1) = false := by
    rw [pl_occ_ne (ba1w2 n) .b (n+2) hn2lt ba1w2_wfd (by omega)]
    exact occ_of_kind_eq (by rw [ba1w2_kind hn, if_neg (by omega), ba1_kind hn,
      if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1),
      if_neg (by omega), if_neg (by omega)])
  have hadj1n1 : adjI n (n+1) 1 = true := adjI_symm (adj_1_n1 (by omega))
  have h1c : ∀ p, p = 0 ∨ p = 1 ∨ p = 2 → 1 ∈ componentD (placedN n (ba1w2 n) .b (n+2)) p := by
    rintro p (h | h | h)
    · rw [h]; exact (componentD_mem_iff _ 0 .w hk0 1).mpr
        (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1 (adjI_symm (adj_0_1 (by omega))))
    · rw [h]; exact componentD_mem_self _ 1 .w hk1
    · rw [h]; exact (componentD_mem_iff _ 2 .w hk2 1).mpr
        (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1 (adj_1_2 (by omega)))
  have hdead : deadOppN n (ba1w2 n) .b (n+2) = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ n+2 := by
      intro he; rw [he, kindAt_placedN_self (ba1w2 n) .b (n+2) ba1w2_wfd hn2lt] at hp
      exact absurd hp (by decide)
    rw [hpk p hpne] at hp
    rcases white_ba1w2 hn hp with h | h | h | h | h
    · exact lib_via1 _ p (h1c p (Or.inl h)) hn1lt hon1 hadj1n1
    · exact lib_via1 _ p (h1c p (Or.inr (Or.inl h))) hn1lt hon1 hadj1n1
    · exact lib_via1 _ p (h1c p (Or.inr (Or.inr h))) hn1lt hon1 hadj1n1
    · subst h
      exact lib_wall (ba1w2 n) .b (n+2) hn2lt ba1w2_wfd (dW1 n) (dE1 n) .w
        (pk_bounds hn).2.2.2.1 hw1_n2 (dEn2 hn).1
        (by rw [ba1w2_kind hn, if_neg hw1_2, ba1_kind hn, if_neg hw1_1, if_neg hw1_0,
          if_neg hw1_w2, if_pos rfl])
        (occ_of_kind_eq (by rw [ba1w2_kind hn, if_neg (dE2ne hn).1, ba1_kind hn, if_neg he1_1,
          if_neg he1_0, if_neg he1_w2, if_neg he1_w1, if_neg he1_n, if_neg he1_3]))
        (adj_E1_W1 hn)
    · subst h
      exact lib_wall (ba1w2 n) .b (n+2) hn2lt ba1w2_wfd (dW2 n) (dE2 n) .w
        (pk_bounds hn).2.2.2.2 hw2_n2 (dEn2 hn).2
        (by rw [ba1w2_kind hn, if_neg hw2_2, ba1_kind hn, if_neg hw2_1, if_neg hw2_0,
          if_pos rfl])
        (occ_of_kind_eq (by rw [ba1w2_kind hn, if_neg (dE2ne hn).2, ba1_kind hn, if_neg he2_1,
          if_neg he2_0, if_neg he2_w2, if_neg he2_w1, if_neg he2_n, if_neg he2_3]))
        (adj_E2_W2 hn)
  have hsui : suicideN n (ba1w2 n) .b (n+2) = false :=
    suicideN_false_of (ba1w2 n) .b (n+2) ba1w2_wfd hn2lt (by decide) hdead
      (has_lib (placedN n (ba1w2 n) .b (n+2)) (n+2) (n+1) .b hn1lt hon1
        (kindAt_placedN_self (ba1w2 n) .b (n+2) ba1w2_wfd hn2lt) (adj_n1_n2 hn))
  rw [goMoveN_quiet (ba1w2 n) .b (n+2) ba1w2_wfd hemp hdead hsui]
  show some ((ba1w2 n).set (n+2) (some (.b, 0))) = some (ba1f n)
  rw [show (ba1w2 n).set (n+2) (some (.b, 0)) = ba1f n from by
    unfold ba1f ba1p ba1w2
    exact set_set_comm (by omega) (some (.w, 0)) (some (.b, 0)) (sb hn).2.1
      (sb hn).2.2.2.2.2.2 ba1_wfd]

/-- (B') White at A3 on the white-joins branch (B3 already down): quiet. -/
theorem gm_B' (hn : 5 ≤ n) : goMoveN n (ba1p n) .w 2 = some (ba1f n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have h2lt : (2:Nat) < n*n := (sb hn).2.1
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  have hn2lt : n+2 < n*n := (sb hn).2.2.2.2.2.2
  have hemp : occD (ba1p n) 2 = false := occ_of_kind_eq (by
    rw [ba1p_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])
  have hkb3 : kindAt (ba1p n) 3 = some .b := by
    rw [ba1p_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]
  have hkbn : kindAt (ba1p n) n = some .b := by
    rw [ba1p_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl]
  have hkbn2 : kindAt (ba1p n) (n+2) = some .b := by rw [ba1p_kind hn, if_pos rfl]
  have hon1 : occD (ba1p n) (n+1) = false := occ_of_kind_eq (by
    rw [ba1p_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega), if_neg (by omega)])
  have hdead : deadOppN n (ba1p n) .w 2 = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ 2 := by
      intro he; rw [he, kindAt_placedN_self (ba1p n) .w 2 ba1p_wfd h2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba1p n) .w 2 h2lt ba1p_wfd hpne] at hp
    rcases black_ba1p hn hp with h | h | h
    · subst h
      exact lib_wall (ba1p n) .w 2 h2lt ba1p_wfd 3 4 .b (sb4 hn).1 (by omega) (by omega) hkb3
        (occ_of_kind_eq (by rw [ba1p_kind hn, if_neg (by omega), ba1_kind hn, if_neg (by omega),
          if_neg (by omega), if_neg (c4_ne hn).2, if_neg (c4_ne hn).1, if_neg (by omega),
          if_neg (by omega)])) (adj_4_3 hn)
    · rw [h]
      exact lib_wall (ba1p n) .w 2 h2lt ba1p_wfd n (n+1) .b hn1lt (by omega) (by omega) hkbn
        (hon1) (adjI_symm (adj_n_n1 (by omega)))
    · rw [h]
      exact lib_wall (ba1p n) .w 2 h2lt ba1p_wfd (n+2) (n+1) .b hn1lt (by omega) (by omega) hkbn2
        (hon1) (adj_n1_n2 hn)
  have hk1 : kindAt (placedN n (ba1p n) .w 2) 1 = some .w := by
    rw [pl_kind_ne (ba1p n) .w 2 h2lt ba1p_wfd (by omega), ba1p_kind hn, if_neg (by omega),
      ba1_kind hn, if_pos rfl]
  have hon1p : occD (placedN n (ba1p n) .w 2) (n+1) = false := by
    rw [pl_occ_ne (ba1p n) .w 2 h2lt ba1p_wfd (by omega)]; exact hon1
  have h1mem2 : 1 ∈ componentD (placedN n (ba1p n) .w 2) 2 :=
    (componentD_mem_iff (placedN n (ba1p n) .w 2) 2 .w
      (kindAt_placedN_self (ba1p n) .w 2 ba1p_wfd h2lt) 1).mpr
      (ConnK.step ConnK.refl (List.mem_range.mpr (sb hn).2.2.1) hk1 (adj_1_2 (by omega)))
  have hsui : suicideN n (ba1p n) .w 2 = false :=
    suicideN_false_of (ba1p n) .w 2 ba1p_wfd h2lt (by decide) hdead
      (lib_via1 _ 2 h1mem2 hn1lt hon1p (adjI_symm (adj_1_n1 (by omega))))
  rw [goMoveN_quiet (ba1p n) .w 2 ba1p_wfd hemp hdead hsui]; rfl

theorem black_ba0f (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba0f (n := n)) p = some .b) :
    p = 1 ∨ p = 3 ∨ p = n ∨ p = n+2 := by
  rw [ba0f_kind hn] at h
  by_cases h2 : p = n+2
  · exact Or.inr (Or.inr (Or.inr h2))
  · rw [if_neg h2] at h
    rcases black_ba0 hn h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

/-- (B) White at A3 on the black-captures branch: a suicide (no-op). -/
theorem gm_B (hn : 5 ≤ n) : goMoveN n (ba0f n) .w 2 = some (ba0f n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have h2lt : (2:Nat) < n*n := (sb hn).2.1
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  have hk1 : kindAt (ba0f n) 1 = some .b := by
    rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega), if_pos rfl]
  have hk3 : kindAt (ba0f n) 3 = some .b := by
    rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]
  have hkn : kindAt (ba0f n) n = some .b := by
    rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_n), if_neg (Ne.symm hw1_n), if_pos rfl]
  have hkn2 : kindAt (ba0f n) (n+2) = some .b := by rw [ba0f_kind hn, if_pos rfl]
  have hemp : occD (ba0f n) 2 = false := occ_of_kind_eq (by
    rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])
  have hocc0 : occD (ba0f n) 0 = false := occ_of_kind_eq (by
    rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_pos rfl])
  have hdead : deadOppN n (ba0f n) .w 2 = [] := by
    apply deadOpp_nil_of; intro p hp
    have hpne : p ≠ 2 := by
      intro he; rw [he, kindAt_placedN_self (ba0f n) .w 2 ba0f_wfd h2lt] at hp
      exact absurd hp (by decide)
    rw [pl_kind_ne (ba0f n) .w 2 h2lt ba0f_wfd hpne] at hp
    rcases black_ba0f hn hp with h | h | h | h
    · subst h
      exact lib_wall (ba0f n) .w 2 h2lt ba0f_wfd 1 0 .b (sb hn).2.2.2.1 (by omega) (by omega)
        hk1 hocc0 (adj_0_1 (by omega))
    · subst h
      exact lib_wall (ba0f n) .w 2 h2lt ba0f_wfd 3 4 .b (sb4 hn).1 (by omega) (by omega) hk3
        (occ_of_kind_eq (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
          if_neg (by omega), if_neg (c4_ne hn).2, if_neg (c4_ne hn).1, if_neg (by omega),
          if_neg (by omega)])) (adj_4_3 hn)
    · rw [h]
      exact lib_wall (ba0f n) .w 2 h2lt ba0f_wfd n (n+1) .b hn1lt (by omega) (by omega) hkn
        (occ_of_kind_eq (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
          if_neg (by omega), if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega),
          if_neg (by omega)])) (adjI_symm (adj_n_n1 (by omega)))
    · rw [h]
      exact lib_wall (ba0f n) .w 2 h2lt ba0f_wfd (n+2) (n+1) .b hn1lt (by omega) (by omega) hkn2
        (occ_of_kind_eq (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
          if_neg (by omega), if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega),
          if_neg (by omega)])) (adj_n1_n2 hn)
  have hAC := afterCapN_nocap_get (ba0f n) .w 2 ba0f_wfd hdead
  have hACkind : ∀ z, kindAt (afterCapN n (ba0f n) .w 2) z
      = kindAt (placedN n (ba0f n) .w 2) z := fun z => by unfold kindAt; rw [hAC z]
  have hACocc : ∀ z, occD (afterCapN n (ba0f n) .w 2) z
      = occD (placedN n (ba0f n) .w 2) z := fun z => by unfold occD; rw [hAC z]
  have hnb : ∀ q, q < n*n → adjI n q 2 = true →
      kindAt (afterCapN n (ba0f n) .w 2) q ≠ some .w := by
    intro q hq hadj; rw [hACkind]
    rcases nbr_2 hn hadj with h | h | h
    · subst h; rw [pl_kind_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega), hk1]; decide
    · subst h; rw [pl_kind_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega), hk3]; decide
    · rw [h, pl_kind_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega), hkn2]; decide
  have hcomp : ∀ q, q ∈ ownCompN n (ba0f n) .w 2 ↔ q = 2 :=
    comp_singleton _ 2 .w (by rw [hACkind]; exact kindAt_placedN_self (ba0f n) .w 2 ba0f_wfd h2lt) hnb
  have hsui : suicideN n (ba0f n) .w 2 = true := by
    show noLibD (afterCapN n (ba0f n) .w 2) (ownCompN n (ba0f n) .w 2) = true
    apply noLibD_true_of; intro q hq hqocc m hm hadj
    rw [(hcomp m).mp hm] at hadj
    rcases nbr_2 hn hadj with h | h | h
    · subst h; rw [hACocc, pl_occ_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega),
        occ_true_of_kind hk1] at hqocc; exact Bool.noConfusion hqocc
    · subst h; rw [hACocc, pl_occ_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega),
        occ_true_of_kind hk3] at hqocc; exact Bool.noConfusion hqocc
    · rw [h, hACocc, pl_occ_ne (ba0f n) .w 2 h2lt ba0f_wfd (by omega),
        occ_true_of_kind hkn2] at hqocc; exact Bool.noConfusion hqocc
  exact goMoveN_suicide (ba0f n) .w 2 ba0f_wfd hemp hdead hsui hcomp

theorem white_ba0w2 (hn : 5 ≤ n) {p : Nat} (h : kindAt (ba0w2 (n := n)) p = some .w) :
    p = 2 ∨ p = dW1 n ∨ p = dW2 n := by
  rw [ba0w2_kind hn] at h
  by_cases h2 : p = 2
  · exact Or.inl h2
  · rw [if_neg h2] at h
    rcases white_ba0 hn h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

set_option maxHeartbeats 800000 in
/-- (D) Black at B3 on the black-captures branch with A3 already white:
    the capture — Black kills the just-played White A3. -/
theorem gm_D (hn : 5 ≤ n) : goMoveN n (ba0w2 n) .b (n+2) = some (ba0f n) := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  obtain ⟨he1_0, he1_1, he1_3, he1_n, he1_w1, he1_w2, he1_P,
    he2_0, he2_1, he2_3, he2_n, he2_w1, he2_w2, he2_P⟩ := dE_ne hn
  have hn2lt : n+2 < n*n := (sb hn).2.2.2.2.2.2
  have hn1lt : n+1 < n*n := (sb hn).2.2.2.2.2.1
  have h2lt : (2:Nat) < n*n := (sb hn).2.1
  have hplK : ∀ z, z ≠ n+2 →
      kindAt (placedN n (ba0w2 n) .b (n+2)) z = kindAt (ba0w2 n) z :=
    fun z hz => pl_kind_ne (ba0w2 n) .b (n+2) hn2lt ba0w2_wfd hz
  have hk2 : kindAt (placedN n (ba0w2 n) .b (n+2)) 2 = some .w := by
    rw [hplK 2 (by omega), ba0w2_kind hn, if_pos rfl]
  have hk1 : kindAt (placedN n (ba0w2 n) .b (n+2)) 1 = some .b := by
    rw [hplK 1 (by omega), ba0w2_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega), if_pos rfl]
  have hk3 : kindAt (placedN n (ba0w2 n) .b (n+2)) 3 = some .b := by
    rw [hplK 3 (by omega), ba0w2_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
      if_neg (by omega), if_neg (Ne.symm hw2_3), if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl]
  have hkn2 : kindAt (placedN n (ba0w2 n) .b (n+2)) (n+2) = some .b :=
    kindAt_placedN_self (ba0w2 n) .b (n+2) ba0w2_wfd hn2lt
  have hcomp2 : ∀ q, q ∈ componentD (placedN n (ba0w2 n) .b (n+2)) 2 ↔ q = 2 :=
    comp_singleton _ 2 .w hk2 (by
      intro q hq hadj
      rcases nbr_2 hn hadj with h | h | h
      · rw [h, hk1]; decide
      · rw [h, hk3]; decide
      · rw [h, hkn2]; decide)
  have hnl2 : noLibD (placedN n (ba0w2 n) .b (n+2))
      (componentD (placedN n (ba0w2 n) .b (n+2)) 2) = true := by
    apply noLibD_true_of; intro q hq hqocc m hm hadj
    rw [(hcomp2 m).mp hm] at hadj
    rcases nbr_2 hn hadj with h | h | h
    · rw [h, occ_true_of_kind hk1] at hqocc; exact Bool.noConfusion hqocc
    · rw [h, occ_true_of_kind hk3] at hqocc; exact Bool.noConfusion hqocc
    · rw [h, occ_true_of_kind hkn2] at hqocc; exact Bool.noConfusion hqocc
  have hkw1 : kindAt (ba0w2 n) (dW1 n) = some .w := by
    rw [ba0w2_kind hn, if_neg hw1_2, ba0_kind hn, if_neg hw1_0, if_neg hw1_1, if_neg hw1_w2, if_pos rfl]
  have hkw2 : kindAt (ba0w2 n) (dW2 n) = some .w := by
    rw [ba0w2_kind hn, if_neg hw2_2, ba0_kind hn, if_neg hw2_0, if_neg hw2_1, if_pos rfl]
  have hoe1 : occD (ba0w2 n) (dE1 n) = false := occ_of_kind_eq (by
    rw [ba0w2_kind hn, if_neg (dE2ne hn).1, ba0_kind hn, if_neg he1_0, if_neg he1_1, if_neg he1_w2,
      if_neg he1_w1, if_neg he1_n, if_neg he1_3])
  have hoe2 : occD (ba0w2 n) (dE2 n) = false := occ_of_kind_eq (by
    rw [ba0w2_kind hn, if_neg (dE2ne hn).2, ba0_kind hn, if_neg he2_0, if_neg he2_1, if_neg he2_w2,
      if_neg he2_w1, if_neg he2_n, if_neg he2_3])
  have hdead : ∀ p, p ∈ deadOppN n (ba0w2 n) .b (n+2) ↔ p = 2 := by
    intro p; rw [mem_deadOppN_iff]; constructor
    · rintro ⟨hpb, hkp, hnl⟩
      by_cases hp2 : p = 2
      · exact hp2
      · exfalso
        have hpne2 : p ≠ n+2 := by
          intro he; rw [he, hkn2] at hkp; exact absurd hkp (by decide)
        rw [hplK p hpne2] at hkp
        rcases white_ba0w2 hn hkp with h | h | h
        · exact hp2 h
        · subst h
          rw [lib_wall (ba0w2 n) .b (n+2) hn2lt ba0w2_wfd (dW1 n) (dE1 n) .w
            (pk_bounds hn).2.2.2.1 hw1_n2 (dEn2 hn).1 hkw1 hoe1 (adj_E1_W1 hn)] at hnl
          exact Bool.noConfusion hnl
        · subst h
          rw [lib_wall (ba0w2 n) .b (n+2) hn2lt ba0w2_wfd (dW2 n) (dE2 n) .w
            (pk_bounds hn).2.2.2.2 hw2_n2 (dEn2 hn).2 hkw2 hoe2 (adj_E2_W2 hn)] at hnl
          exact Bool.noConfusion hnl
    · intro hp2; subst hp2; exact ⟨List.mem_range.mpr h2lt, hk2, hnl2⟩
  have hafter : afterCapN n (ba0w2 n) .b (n+2) = ba0f n := by
    have hsz : (afterCapN n (ba0w2 n) .b (n+2)).cells.size = n*n := by
      unfold afterCapN; simp [Array.size_map, Array.size_range]
    apply display_ext; apply Array.ext
    · rw [hsz]; show n*n = (ba0f n).cells.size; rw [ba0f_wfd]
    · intro p h1 h2
      have hib : p < n*n := by omega
      rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2, afterCapN_get, if_pos hib]
      by_cases hp2 : p = 2
      · rw [hp2, if_pos (List.contains_iff_mem.mpr ((hdead 2).mpr rfl))]
        show none = (ba0f n).get 2
        rw [show (ba0f n).get 2 = none from by
          unfold ba0f; rw [get_set_ne _ _ _ _ (by omega)]
          have hk : kindAt (ba0 n) 2 = none := by
            rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_2),
              if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]
          unfold kindAt at hk
          cases hg : (ba0 n).get 2 with
          | none => rfl
          | some c => rw [hg] at hk; exact Option.noConfusion hk]
      · rw [if_neg (by intro hc; exact hp2 ((hdead p).mp (List.contains_iff_mem.mp hc)))]
        show (placedN n (ba0w2 n) .b (n+2)).get p = (ba0f n).get p
        unfold placedN ba0f ba0w2
        by_cases hpn2 : p = n+2
        · subst hpn2
          rw [get_set_self _ _ _ (by rw [set_size, ba0_wfd]; exact hn2lt),
            get_set_self _ _ _ (by rw [ba0_wfd]; exact hn2lt)]
        · rw [get_set_ne _ _ _ _ hpn2, get_set_ne _ _ _ _ hp2, get_set_ne _ _ _ _ hpn2]
  have hsui : suicideN n (ba0w2 n) .b (n+2) = false := by
    show noLibD (afterCapN n (ba0w2 n) .b (n+2))
      (componentD (afterCapN n (ba0w2 n) .b (n+2)) (n+2)) = false
    rw [hafter]
    exact has_lib (ba0f n) (n+2) (n+1) .b hn1lt
      (occ_of_kind_eq (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
        if_neg (by omega), if_neg (Ne.symm hw2_n1), if_neg (Ne.symm hw1_n1), if_neg (by omega),
        if_neg (by omega)]))
      (by rw [ba0f_kind hn, if_pos rfl]) (adj_n1_n2 hn)
  unfold goMoveN
  rw [occ_of_kind_eq (by rw [ba0w2_kind hn, if_neg (by omega), ba0_kind hn, if_neg (by omega),
    if_neg (by omega), if_neg (Ne.symm hw2_n2), if_neg (Ne.symm hw1_n2), if_neg (by omega),
    if_neg (by omega)])]
  simp only [Bool.false_eq_true, if_false, hsui]
  rw [hafter]

/-! ### The finale serializations -/

/-- serialP when both composites are defined. -/
theorem serialP_some_some {a : Display n} {m0 m1 : Option Nat} {x y : Display n}
    (h1 : bStep2 n a .b .w m0 m1 = some x) (h2 : bStep2 n a .w .b m1 m0 = some y) :
    serialP n a m0 m1 = some (dedupD n [x, y]) := by
  unfold serialP
  rw [h1, h2]

/-- The finale on the surviving branch ba0: both orderings land on ba0f
    (black@B3 then white@A3-suicide; or white@A3 then black@B3-capture). -/
theorem ba0_serialP (hn : 5 ≤ n) :
    serialP n (ba0 n) (some (n+2)) (some 2) = some (dedupD n [ba0f n, ba0f n]) := by
  have hbw : bStep2 n (ba0 n) .b .w (some (n+2)) (some 2) = some (ba0f n) := by
    simp only [bStep2, bStep, gm_A hn, gm_B hn, Option.some_bind]
  have hwb : bStep2 n (ba0 n) .w .b (some 2) (some (n+2)) = some (ba0f n) := by
    simp only [bStep2, bStep, gm_C hn, gm_D hn, Option.some_bind]
  exact serialP_some_some hbw hwb

/-- The finale on the display-only branch ba1: both orderings land on
    ba1f (black@B3 then white@A3; or white@A3 then black@B3), the white
    at A3 surviving because its group breathes at B2. -/
theorem ba1_serialP (hn : 5 ≤ n) :
    serialP n (ba1 n) (some (n+2)) (some 2) = some (dedupD n [ba1f n, ba1f n]) := by
  have hbw : bStep2 n (ba1 n) .b .w (some (n+2)) (some 2) = some (ba1f n) := by
    simp only [bStep2, bStep, gm_A' hn, gm_B' hn, Option.some_bind]
  have hwb : bStep2 n (ba1 n) .w .b (some 2) (some (n+2)) = some (ba1f n) := by
    simp only [bStep2, bStep, gm_C' hn, gm_D' hn, Option.some_bind]
  exact serialP_some_some hbw hwb

/-! ### The finale display Dpf and its Δ-round fixpoint -/

theorem Eres_wfd {D0 : Display n} (hwf : WFD D0) (t_c : Nat) : WFD (Eres D0 t_c) :=
  wfd_set _ _ _ (wfd_set _ _ _ (wfd_set _ _ _ hwf))

/-- The finale display: the resolved collision Eres with black at B3 and
    white at A3 played on top. -/
def Dpf (D0 : Display n) (t_c t_f : Nat) : Display n :=
  ((Eres D0 t_c).set (n+2) (some (.b, t_f))).set 2 (some (.w, t_f))

theorem Dpf_wfd {D0 : Display n} (hwf : WFD D0) (t_c t_f : Nat) :
    WFD (Dpf D0 t_c t_f) :=
  wfd_set _ _ _ (wfd_set _ _ _ (Eres_wfd hwf t_c))

theorem Dpf_kind (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t_c t_f p : Nat) :
    kindAt (Dpf D0 t_c t_f) p
      = if p = 2 then some .w else if p = n+2 then some .b
        else kindAt (Eres D0 t_c) p := by
  unfold Dpf
  rw [kind_set _ 2 (sb hn).2.1 (wfd_set _ _ _ (Eres_wfd hwf t_c))]
  by_cases hp2 : p = 2
  · rw [if_pos hp2, if_pos hp2]
  · rw [if_neg hp2, if_neg hp2,
      kind_set _ (n+2) (sb hn).2.2.2.2.2.2 (Eres_wfd hwf t_c)]

theorem Dpf_occ2 (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t_c t_f : Nat) :
    occD (Dpf D0 t_c t_f) 2 = true :=
  occ_true_of_kind (by rw [Dpf_kind hn hwf, if_pos rfl])

theorem Dpf_occ0 (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t_c t_f : Nat) :
    occD (Dpf D0 t_c t_f) 0 = false := by
  unfold Dpf occD
  rw [get_set_ne _ _ _ _ (show (0:Nat) ≠ 2 by omega),
    get_set_ne _ _ _ _ (show (0:Nat) ≠ n+2 by omega), Eres_get_0 hn hwf]
  rfl

/-- placeJoint on the resolved collision plays the finale joint move. -/
theorem pj_Dpf (hn : 5 ≤ n) {D0 : Display n} (t_c t_f : Nat) :
    placeJoint (Eres D0 t_c) t_f (some (n+2)) (some 2) = Dpf D0 t_c t_f := by
  have hne : ¬ ((n+2) == 2) = true := by
    intro h; have hh : n + 2 = 2 := eq_of_beq h; omega
  show (if (n+2) == 2 then (Eres D0 t_c).set (n+2) (some (.r, t_f)) else
    ((Eres D0 t_c).set (n+2) (some (.b, t_f))).set 2 (some (.w, t_f)))
    = Dpf D0 t_c t_f
  rw [if_neg hne]
  rfl

/-- ev of the two finale branches, read off ba0f/ba1f. -/
theorem evSet_pairf {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0f n ∨ b = ba1f n) (i : Nat) :
    evSet n dec i
      = ((kindAt (ba0f n) i == some .b) || (kindAt (ba1f n) i == some .b),
         (kindAt (ba0f n) i == some .w) || (kindAt (ba1f n) i == some .w)) := by
  have hx : ba0f n ∈ dec := (hdec _).mpr (Or.inl rfl)
  have hy : ba1f n ∈ dec := (hdec _).mpr (Or.inr rfl)
  show ((dec.any fun b => kindAt b i == some .b),
        (dec.any fun b => kindAt b i == some .w)) = _
  rw [any_pair hx hy (fun b hb => (hdec b).mp hb),
      any_pair hx hy (fun b hb => (hdec b).mp hb)]

/-- A definite (non-q) display stone with a nonempty ev survives the
    round unchanged. -/
theorem dR_keep_def (t : Nat) (M : List (Display n)) (D : Display n)
    {i : Nat} (hi : i < n*n) {k : DKind} {st : Nat}
    (hg : D.get i = some (k, st)) (hkr : k ≠ DKind.r)
    (hb : (evSet n M i).1 = true ∨ (evSet n M i).2 = true) :
    (deltaRound n t M D).get i = some (k, st) := by
  have hev : evSet n M i = ((evSet n M i).1, (evSet n M i).2) := rfl
  rw [dR_get_pair t M D hi hg hev]
  have hor : (!(evSet n M i).1 && !(evSet n M i).2) = false := by
    rcases hb with h | h <;> rw [h] <;> simp
  rw [if_neg (by rw [hor]; exact Bool.noConfusion)]
  have hkr' : (k == DKind.r) = false := by
    cases k with
    | r => exact absurd rfl hkr
    | b => rfl
    | w => rfl
  rw [if_neg (by rw [hkr', Bool.false_and]; exact Bool.noConfusion)]

set_option maxHeartbeats 1000000 in
/-- The finale display is a Δ-round fixpoint of the two finale branches:
    every stone is backed (A3's white by the white-joins branch a1). -/
theorem dpf_round_fix (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c t_f : Nat) {dec : List (Display n)}
    (hdec : ∀ b, b ∈ dec ↔ b = ba0f n ∨ b = ba1f n) :
    deltaRound n t_f dec (Dpf D0 t_c t_f) = Dpf D0 t_c t_f := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hx : ba0f n ∈ dec := (hdec _).mpr (Or.inl rfl)
  have hy : ba1f n ∈ dec := (hdec _).mpr (Or.inr rfl)
  apply deltaRound_fix (Dpf_wfd hwf t_c t_f)
  intro i hi kk st hg
  have hk : kindAt (Dpf D0 t_c t_f) i = some kk := by unfold kindAt; rw [hg]; rfl
  rw [Dpf_kind hn hwf] at hk
  by_cases hi2 : i = 2
  · subst hi2
    have hkw : kk = .w := by rw [if_pos rfl] at hk; exact (Option.some.inj hk).symm
    subst hkw
    exact dR_keep_def t_f dec _ hi hg (by decide)
      (Or.inr (evSet_w hy (by rw [ba1f_kind hn, if_pos rfl])))
  · rw [if_neg hi2] at hk
    by_cases hin2 : i = n+2
    · subst hin2
      have hkb : kk = .b := by rw [if_pos rfl] at hk; exact (Option.some.inj hk).symm
      subst hkb
      exact dR_keep_def t_f dec _ hi hg (by decide)
        (Or.inl (evSet_b hx (by rw [ba0f_kind hn, if_pos rfl])))
    · rw [if_neg hin2] at hk
      by_cases hi1 : i = 1
      · subst hi1
        have hkb : kk = .b := by
          rw [Eres_kind hn hsc hwf, if_neg (by omega), if_pos rfl] at hk
          exact (Option.some.inj hk).symm
        subst hkb
        exact dR_keep_def t_f dec _ hi hg (by decide)
          (Or.inl (evSet_b hx (by rw [ba0f_kind hn, if_neg (by omega),
            ba0_kind hn, if_neg (by omega), if_pos rfl])))
      · by_cases hi0 : i = 0
        · exfalso
          rw [Eres_kind hn hsc hwf, if_pos hi0] at hk
          exact Option.noConfusion hk
        · rw [Eres_kind hn hsc hwf, if_neg hi0, if_neg hi1, kd5_kind hn,
            if_neg hi0] at hk
          by_cases hd2 : i = dW2 n
          · subst hd2
            have hkw : kk = .w := by rw [if_pos rfl] at hk; exact (Option.some.inj hk).symm
            subst hkw
            exact dR_keep_def t_f dec _ hi hg (by decide)
              (Or.inr (evSet_w hx (by rw [ba0f_kind hn, if_neg hw2_n2, ba0_kind hn,
                if_neg hw2_0, if_neg hw2_1, if_pos rfl])))
          · by_cases hd1 : i = dW1 n
            · subst hd1
              have hkw : kk = .w := by
                rw [if_neg hd2, if_pos rfl] at hk; exact (Option.some.inj hk).symm
              subst hkw
              exact dR_keep_def t_f dec _ hi hg (by decide)
                (Or.inr (evSet_w hx (by rw [ba0f_kind hn, if_neg hw1_n2, ba0_kind hn,
                  if_neg hw1_0, if_neg hw1_1, if_neg hw1_w2, if_pos rfl])))
            · by_cases hin : i = n
              · subst hin
                have hkb : kk = .b := by
                  rw [if_neg hd2, if_neg hd1, if_pos rfl] at hk
                  exact (Option.some.inj hk).symm
                subst hkb
                exact dR_keep_def t_f dec _ hi hg (by decide)
                  (Or.inl (evSet_b hx (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn,
                    if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_n),
                    if_neg (Ne.symm hw1_n), if_pos rfl])))
              · by_cases hi3 : i = 3
                · subst hi3
                  have hkb : kk = .b := by
                    rw [if_neg hd2, if_neg hd1, if_neg hin, if_pos rfl] at hk
                    exact (Option.some.inj hk).symm
                  subst hkb
                  exact dR_keep_def t_f dec _ hi hg (by decide)
                    (Or.inl (evSet_b hx (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn,
                      if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_3),
                      if_neg (Ne.symm hw1_3), if_neg (by omega), if_pos rfl])))
                · exfalso
                  rw [if_neg hd2, if_neg hd1, if_neg hin, if_neg hi3] at hk
                  exact Option.noConfusion hk

/-! ### The re-cut of the finale display -/

/-- The surviving branch a0'' stands on the finale display: all its
    stones (A2, A4, B1, B3, the walls) sit on occupied intersections. -/
theorem occInc_Dpf_ba0f (hn : 5 ≤ n) {D0 : Display n} (hsc : SameCells D0 (kd5 n))
    (hwf : WFD D0) (t_c t_f : Nat) :
    occIncB n (Dpf D0 t_c t_f) (ba0f n) = true := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  apply occIncB_of
  intro i hi hne
  by_cases hin2 : i = n+2
  · subst hin2
    exact occ_true_of_kind (by rw [Dpf_kind hn hwf, if_neg (by omega), if_pos rfl])
  · by_cases hi1 : i = 1
    · subst hi1
      exact occ_true_of_kind (by rw [Dpf_kind hn hwf, if_neg (by omega), if_neg (by omega),
        Eres_kind hn hsc hwf, if_neg (by omega), if_pos rfl])
    · rw [ba0f_kind hn, if_neg hin2] at hne
      by_cases hi0 : i = 0
      · exfalso; apply hne; rw [ba0_kind hn, if_pos hi0]
      · by_cases hi2 : i = 2
        · exfalso; apply hne; subst hi2
          rw [ba0_kind hn, if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_2),
            if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)]
        · have hkeq : kindAt (Dpf D0 t_c t_f) i = kindAt (kd5 (n := n)) i := by
            rw [Dpf_kind hn hwf, if_neg hi2, if_neg hin2, Eres_kind hn hsc hwf,
              if_neg hi0, if_neg hi1]
          have hbeq : kindAt (ba0 n) i = kindAt (kd5 (n := n)) i := by
            rw [ba0_kind hn, if_neg hi0, if_neg hi1, kd5_kind hn, if_neg hi0]
          rw [hbeq] at hne
          cases hkk : kindAt (kd5 (n := n)) i with
          | none => rw [hkk] at hne; exact absurd rfl hne
          | some kc => exact occ_true_of_kind (by rw [hkeq, hkk])

/-- The white-joins branch a1'' does NOT stand on the finale display:
    its A1 stone sits where the display was emptied by the verdict. -/
theorem occInc_Dpf_ba1f (hn : 5 ≤ n) {D0 : Display n} (hwf : WFD D0) (t_c t_f : Nat) :
    occIncB n (Dpf D0 t_c t_f) (ba1f n) = false := by
  have h0mem : (0:Nat) ∈ allIdx n := List.mem_range.mpr (sb hn).2.2.2.1
  have hf0 : (occD (Dpf D0 t_c t_f) 0 || (kindAt (ba1f n) 0 == none)) = false := by
    rw [Dpf_occ0 hn hwf,
      show kindAt (ba1f n) 0 = some .w from by
        rw [ba1f_kind hn, if_neg (by omega), ba1p_kind hn, if_neg (by omega),
          ba1_kind hn, if_neg (by omega), if_pos rfl]]
    rfl
  cases h : occIncB n (Dpf D0 t_c t_f) (ba1f n) with
  | false => rfl
  | true =>
    unfold occIncB at h
    have hall := (List.all_eq_true.mp h) 0 h0mem
    rw [hf0] at hall; exact Bool.noConfusion hall

/-! ### The finale turn: the delayed verdict fires -/

set_option maxHeartbeats 1000000 in
/-- The final turn B3/A3 from the aged collision state: the stored
    verdict empties A1 and blackens A2, White's A3 is played, and after
    the Δ round and re-cut the display carries White's A3 (kept alive
    through the round by the white-joins branch) while the sole surviving
    branch a0'' has A3 dead. -/
theorem final_step (hn : 5 ≤ n) {k : Nat} {D0 : Display n} {t_c : Nat}
    {s : KState n} (hsc : SameCells D0 (kd5 n)) (hwf : WFD D0)
    (hst : StampsBelow D0 t_c) (htc : 1 ≤ t_c)
    (hdisp : s.disp = Dcol D0 t_c)
    (hent : ∀ b, b ∈ s.ent ↔ b = ba0 n ∨ b = ba1 n)
    (hverd : ∃ rest, s.verdicts = verOf n t_c (Dcol D0 t_c) :: rest)
    (hf : s.final = false) :
    ∃ s', (kGame n k).pairE s (some (false, n+2)) (some (true, 2)) = some s'
      ∧ occD s'.disp 2 = true
      ∧ (∀ b, b ∈ s'.ent → occD b 2 = false)
      ∧ s'.final = false := by
  obtain ⟨hw1_0, hw1_1, hw1_2, hw1_3, hw1_n, hw1_n1, hw1_n2, hw1_w2,
    hw2_0, hw2_1, hw2_2, hw2_3, hw2_n, hw2_n1, hw2_n2,
    hp_0, hp_1, hp_2, hp_3, hp_n, hp_n1, hp_n2, hp_w1, hp_w2⟩ := pk_ne hn
  have hocc_n2 : occD s.disp (n+2) = false := by
    rw [hdisp, occD_Dcol hn hsc hwf, if_neg (by omega)]
    exact occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_n2),
      if_neg (Ne.symm hw1_n2), if_neg (by omega), if_neg (by omega)])
  have hocc_2 : occD s.disp 2 = false := by
    rw [hdisp, occD_Dcol hn hsc hwf, if_neg (by omega)]
    exact occ_of_kind_eq (by rw [kd5_kind hn, if_neg (by omega), if_neg (Ne.symm hw2_2),
      if_neg (Ne.symm hw1_2), if_neg (by omega), if_neg (by omega)])
  have havn2 : availD n s.disp (some (n+2)) = true := by
    show (decide (n+2 < n*n) && !occD s.disp (n+2)) = true
    rw [decide_eq_true (sb hn).2.2.2.2.2.2, hocc_n2]; rfl
  have hav2 : availD n s.disp (some 2) = true := by
    show (decide (2 < n*n) && !occD s.disp 2) = true
    rw [decide_eq_true (sb hn).2.1, hocc_2]; rfl
  have hentInc : ∀ b, b ∈ s.ent → occIncB n s.disp b = true := by
    intro b hb; rw [hdisp]
    rcases (hent b).mp hb with h | h
    · rw [h]; exact occInc_ba0 hn hsc hwf t_c
    · rw [h]; exact occInc_ba1 hn hsc hwf t_c
  obtain ⟨rest, hq⟩ := hverd
  have hqne : s.verdicts ≠ [] := by rw [hq]; exact List.cons_ne_nil _ _
  have hEv : (kEv n s (some (n+2)) (some 2)).isSome :=
    (kEv_isSome_iff s hentInc hqne (some (n+2)) (some 2)).mpr ⟨hf, havn2, hav2⟩
  rcases Option.isSome_iff_exists.mp hEv with ⟨s', hs'⟩
  rcases kEv_cases hs' with ⟨hf', hav0, hav1, v1, vrest, dec, hq', hse, hs'e⟩
  rw [hq] at hq'
  have hv1 : v1 = verOf n t_c (Dcol D0 t_c) := ((List.cons.injEq .. ▸ hq').1).symm
  subst hv1
  have hdecmem : ∀ b, b ∈ dec ↔ b = ba0f n ∨ b = ba1f n := by
    rcases Option.map_eq_some'.mp hse with ⟨out, hout, hdd⟩
    intro b
    constructor
    · intro hb
      rw [← hdd] at hb
      have hbout : b ∈ out := (mem_dedupD_iff _ _).mp hb
      rcases simEvAux_mem hout hbout with ⟨b', hb', l, hl, hbl⟩
      rcases (hent b').mp hb' with hb0 | hb1
      · subst hb0; rw [ba0_serialP hn] at hl
        rw [(Option.some.inj hl).symm] at hbl
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hbl) with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inl h
          · cases h
      · subst hb1; rw [ba1_serialP hn] at hl
        rw [(Option.some.inj hl).symm] at hbl
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hbl) with h | h
        · exact Or.inr h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr h
          · cases h
    · intro hb
      rw [← hdd]; apply (mem_dedupD_iff _ _).mpr
      rcases hb with h | h
      · subst h
        exact simEvAux_mem_of hout ((hent (ba0 n)).mpr (Or.inl rfl)) (ba0_serialP hn)
          ((mem_dedupD_iff _ _).mpr (List.mem_cons_self _ _))
      · subst h
        exact simEvAux_mem_of hout ((hent (ba1 n)).mpr (Or.inr rfl)) (ba1_serialP hn)
          ((mem_dedupD_iff _ _).mpr (List.mem_cons_self _ _))
  have hpj : placeJoint (execV n (verOf n t_c (Dcol D0 t_c)) s.disp) s.next
      (some (n+2)) (some 2) = Dpf D0 t_c s.next := by
    rw [hdisp, verOf_Dcol hn hsc hwf hst htc, execV_Dcol hn hsc hwf, pj_Dpf hn]
  have hdeltaD : delta n s.next (Dpf D0 t_c s.next) dec
      = (Dpf D0 t_c s.next, recut n (Dpf D0 t_c s.next) dec) :=
    delta_fix (dpf_round_fix hn hsc hwf t_c s.next hdecmem)
  rw [hpj, hdeltaD] at hs'e
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · rw [show (kGame n k).pairE s (some (false, n+2)) (some (true, 2))
      = kEv n s (some (n+2)) (some 2) from rfl]
    exact hs'
  · rw [hs'e]; exact Dpf_occ2 hn hwf t_c s.next
  · rw [hs'e]; intro b hb
    have hb2 : b ∈ recut n (Dpf D0 t_c s.next) dec := hb
    rw [recut_mem] at hb2
    rcases (hdecmem b).mp hb2.1 with h | h
    · rw [h]; exact occ_of_kind_eq (by rw [ba0f_kind hn, if_neg (by omega), ba0_kind hn,
        if_neg (by omega), if_neg (by omega), if_neg (Ne.symm hw2_2), if_neg (Ne.symm hw1_2),
        if_neg (by omega), if_neg (by omega)])
    · exfalso; rw [h, occInc_Dpf_ba1f hn hwf] at hb2; exact Bool.noConfusion hb2.2
  · rw [hs'e]; rfl

/-! ### k-DSGo is not faithful within k+1 -/

set_option maxHeartbeats 1600000 in
/-- The faithfulness LOWER bound: at side ≥ 5, for every k ≥ 1, the
    delayed-verdict witness reaches (within k+1 commuting turns) a state
    whose interface fails — the display carries White's A3 while every
    surviving branch has A3 empty. -/
theorem not_faithful_kp1 (hn : 5 ≤ n) {k : Nat} (hk : 1 ≤ k) :
    ¬ FaithfulWithin (goGame n) (kGame n k) (rhoK n) (k+1) := by
  intro hFW
  -- the semiclassical setup state and its projected fields
  obtain ⟨s0, hsc0⟩ := setup_reach hn hk
  obtain ⟨hproj0, hallq0, hreach0⟩ := ksemiC_project (by omega) hsc0
  obtain ⟨d0, hshape0, hmemb0, hdisp0, -⟩ := (dsemiC_track (by omega) hproj0).track
  have hInv0 := reach_invK hreach0
  have hdd0 : d0 = kd5 n := by
    rcases hshape0 with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae; rfl
    · cases hae
  subst hdd0
  have hfin0 : s0.final = false := by
    rcases hshape0 with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hd0 : SameCells s0.disp (kd5 n) := hdisp0
  have hentK0 : ∀ b, b ∈ s0.ent → b = kd5 n := fun b hb => (hmemb0 b).mp hb
  have hkd50 : kd5 n ∈ s0.ent := (hmemb0 _).mpr rfl
  have hst0 : StampsBelow s0.disp s0.next := hInv0.stamps
  have htc0 : 1 ≤ s0.next := hInv0.next_pos
  -- the collision turn
  obtain ⟨s1, hp1, hs1disp, hs1ent, hs1verd, -, hs1fin⟩ :=
    coll_step hn hd0 hInv0.wfdD hInv0.entInc hentK0 hkd50 hallq0 hk hfin0
  have hW1 : WithinD (goGame n) (kGame n k) (rhoK n) 1 s1 :=
    WithinD.step (WithinD.base hsc0) hp1
  -- the k-1 pocket-suicide padding turns
  obtain ⟨sk, hskdisp, hskent, hskverd, hskfin, hWpad⟩ :=
    pad_reach hn hd0 hInv0.wfdD (k-1) s1 1 [] hs1disp hs1ent hs1verd hs1fin hW1
  have hWk : WithinD (goGame n) (kGame n k) (rhoK n) k sk := by
    rw [show (1 + (k-1)) = k from by omega] at hWpad; exact hWpad
  -- the final turn B3/A3
  obtain ⟨sf, hpf, hsfocc, hsfviol, hsffin⟩ :=
    final_step hn hd0 hInv0.wfdD hst0 htc0 hskdisp hskent hskverd hskfin
  have hWf : WithinD (goGame n) (kGame n k) (rhoK n) (k+1) sf :=
    WithinD.step hWk hpf
  -- the interface at the violation cell A3 = 2
  have hFA := hFW sf hWf
  have hiff := hFA.2 (some (false, 2))
  have hall : ∀ a, rhoK n sf a → Interface0 (goGame n) a (some (false, 2)) := by
    intro a ha
    rcases ha with ⟨e, he, hae⟩
    rw [hsffin] at hae
    simp only [Bool.false_eq_true, if_false] at hae
    rw [hae, interface0_live]
    exact Or.inr ⟨false, 2, rfl, (sb hn).2.1, hsfviol e he⟩
  rcases (hiff.mpr hall).2 with h | ⟨w, i, hm, -, hocc⟩
  · cases h
  · cases hm
    rw [hsfocc] at hocc
    exact Bool.noConfusion hocc

end SgoKWit
