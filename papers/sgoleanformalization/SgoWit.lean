/- SgoWit.lean — the main theorem, milestone 2g: SGo is not faithful within
   distance one, at board side ≥ 3.

   The printed witness: black stones on A3, B2, C1 and white stones on
   A2, B1, reached by five single-move (hence commuting) turns; then
   the conflict A1/A1. Branch side, the two whites die — Black's A1
   captures both in one order, White's A1 is a three-stone suicide in
   the other with Black landing on the emptied intersection — so every
   branch of the new entanglement is the four-black diagram. Display
   side, the collision places a q-stone that is itself trapped on the
   turn: condition 3a fails at it for each white stone, and 3b's
   component clause fails there too, so the resolution removes
   nothing. A2 stands on the display but is empty in every branch:
   the interface clause of def_faithful fails one turn from a
   semiclassical state. -/
import SgoSimple

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv SgoOK SgoBridge SgoNat SgoSemi SgoFaith SgoSimple

namespace SgoWit

variable {n : Nat}

/-! ### Adjacency, inverted at the witness cells -/

theorem adjI_inv {q i : Nat} (h : adjI n q i = true) :
    (q / n = i / n ∧ (q % n + 1 = i % n ∨ i % n + 1 = q % n))
    ∨ (q % n = i % n ∧ (q / n + 1 = i / n ∨ i / n + 1 = q / n)) := by
  simp only [adjI] at h
  rcases bool_or_elim h with h1 | h2
  · rw [Bool.and_eq_true] at h1
    left
    refine ⟨beq_iff_eq.mp h1.1, ?_⟩
    rcases bool_or_elim h1.2 with h' | h'
    · exact Or.inl (beq_iff_eq.mp h')
    · exact Or.inr (beq_iff_eq.mp h')
  · rw [Bool.and_eq_true] at h2
    right
    refine ⟨beq_iff_eq.mp h2.1, ?_⟩
    rcases bool_or_elim h2.2 with h' | h'
    · exact Or.inl (beq_iff_eq.mp h')
    · exact Or.inr (beq_iff_eq.mp h')

theorem div_mod_recomp {q : Nat} (hn0 : 0 < n) :
    q = (q / n) * n + q % n := by
  have h := Nat.div_add_mod q n
  rw [Nat.mul_comm] at h
  omega

/-- The neighbors of A1 = 0. -/
theorem nbr_0 (hn : 3 ≤ n) {q : Nat} (h : adjI n q 0 = true) :
    q = 1 ∨ q = n := by
  have hn0 : 0 < n := by omega
  have h0n : (0 : Nat) / n = 0 := Nat.div_eq_of_lt (by omega)
  have h0m : (0 : Nat) % n = 0 := Nat.mod_eq_of_lt (by omega)
  have hqe := div_mod_recomp (q := q) hn0
  rcases adjI_inv h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [h0n] at hx
    rw [h0m] at hy
    rcases hy with h' | h'
    · exact absurd h' (Nat.succ_ne_zero _)
    · left
      have hb : q % n = 0 + 1 := h'.symm
      rw [hx, hb] at hqe
      simpa using hqe
  · rw [h0m] at hy
    rw [h0n] at hx
    rcases hx with h' | h'
    · exact absurd h' (Nat.succ_ne_zero _)
    · right
      have ha : q / n = 0 + 1 := h'.symm
      rw [ha, hy] at hqe
      simpa using hqe

/-- The neighbors of A2 = 1. -/
theorem nbr_1 (hn : 3 ≤ n) {q : Nat} (h : adjI n q 1 = true) :
    q = 0 ∨ q = 2 ∨ q = n + 1 := by
  have hn0 : 0 < n := by omega
  have h1n : (1 : Nat) / n = 0 := Nat.div_eq_of_lt (by omega)
  have h1m : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by omega)
  have hqe := div_mod_recomp (q := q) hn0
  rcases adjI_inv h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [h1n] at hx
    rw [h1m] at hy
    rcases hy with h' | h'
    · left
      have hb : q % n = 0 := Nat.succ.inj h'
      rw [hx, hb] at hqe
      simpa using hqe
    · right; left
      have hb : q % n = 1 + 1 := h'.symm
      rw [hx, hb] at hqe
      simpa using hqe
  · rw [h1m] at hy
    rw [h1n] at hx
    rcases hx with h' | h'
    · exact absurd h' (Nat.succ_ne_zero _)
    · right; right
      have ha : q / n = 0 + 1 := h'.symm
      rw [ha, hy] at hqe
      simpa using hqe

/-- The neighbors of B1 = n. -/
theorem nbr_n (hn : 3 ≤ n) {q : Nat} (h : adjI n q n = true) :
    q = 0 ∨ q = n + 1 ∨ q = 2 * n := by
  have hn0 : 0 < n := by omega
  have hnn : n / n = 1 := Nat.div_self hn0
  have hnm : n % n = 0 := Nat.mod_self n
  have hqe := div_mod_recomp (q := q) hn0
  rcases adjI_inv h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [hnn] at hx
    rw [hnm] at hy
    rcases hy with h' | h'
    · exact absurd h' (Nat.succ_ne_zero _)
    · right; left
      have hb : q % n = 0 + 1 := h'.symm
      rw [hx, hb] at hqe
      simpa using hqe
  · rw [hnm] at hy
    rw [hnn] at hx
    rcases hx with h' | h'
    · left
      have ha : q / n = 0 := Nat.succ.inj h'
      rw [ha, hy] at hqe
      simpa using hqe
    · right; right
      have ha : q / n = 1 + 1 := h'.symm
      rw [ha, hy] at hqe
      simpa using hqe

/-- The positive adjacencies of the corner. -/
theorem adj_0_1 (hn : 3 ≤ n) : adjI n 0 1 = true := by
  have h := adjI_step_y (n := n) (x := 0) (y := 0) (by omega) (by omega)
    (by omega)
  simpa using h

theorem adj_0_n (hn : 3 ≤ n) : adjI n 0 n = true := by
  have h := adjI_step_x (n := n) (x := 0) (y := 0) (by omega) (by omega)
    (by omega)
  simpa using h

theorem adj_1_2 (hn : 3 ≤ n) : adjI n 1 2 = true := by
  have h := adjI_step_y (n := n) (x := 0) (y := 1) (by omega) (by omega)
    (by omega)
  simpa using h

theorem adj_1_n1 (hn : 3 ≤ n) : adjI n 1 (n+1) = true := by
  have h := adjI_step_x (n := n) (x := 0) (y := 1) (by omega) (by omega)
    (by omega)
  simpa using h

theorem adj_n_n1 (hn : 3 ≤ n) : adjI n n (n+1) = true := by
  have h := adjI_step_y (n := n) (x := 1) (y := 0) (by omega) (by omega)
    (by omega)
  have he : 1*n + 0 = n := by omega
  have he1 : 1*n + (0+1) = n+1 := by omega
  rw [he, he1] at h
  exact h

theorem adj_n_2n (hn : 3 ≤ n) : adjI n n (2*n) = true := by
  have h := adjI_step_x (n := n) (x := 1) (y := 0) (by omega) (by omega)
    (by omega)
  have he : 1*n + 0 = n := by omega
  have he1 : (1+1)*n + 0 = 2*n := by omega
  rw [he, he1] at h
  exact h

theorem adj_2_n2 (hn : 3 ≤ n) : adjI n 2 (n+2) = true := by
  have h := adjI_step_x (n := n) (x := 0) (y := 2) (by omega) (by omega)
    (by omega)
  have he : 0*n + 2 = 2 := by omega
  have he1 : (0+1)*n + 2 = n+2 := by omega
  rw [he, he1] at h
  exact h

theorem adj_n1_n2 (hn : 3 ≤ n) : adjI n (n+1) (n+2) = true := by
  have h := adjI_step_y (n := n) (x := 1) (y := 1) (by omega) (by omega)
    (by omega)
  have he : 1*n + 1 = n+1 := by omega
  have he1 : 1*n + (1+1) = n+2 := by omega
  rw [he, he1] at h
  exact h

theorem adj_2n_2n1 (hn : 3 ≤ n) : adjI n (2*n) (2*n+1) = true := by
  have h := adjI_step_y (n := n) (x := 2) (y := 0) (by omega) (by omega)
    (by omega)
  have he : 2*n + 0 = 2*n := by omega
  have he1 : 2*n + (0+1) = 2*n+1 := by omega
  rw [he, he1] at h
  exact h

/-! ### The witness diagrams -/

theorem wfd_set (D : Display n) (i : Nat) (c : Cell)
    (hwf : WFD D) : WFD (D.set i c) := by
  unfold WFD
  rw [set_size]
  exact hwf

theorem kind_set (D : Display n) (i : Nat) (hi : i < n*n)
    (hwf : WFD D) (c : DKind) (s : Nat) (w : Nat) :
    kindAt (D.set i (some (c, s))) w
      = if w = i then some c else kindAt D w := by
  by_cases h : w = i
  · subst h
    rw [if_pos rfl]
    unfold kindAt
    rw [get_set_self D w _ (by rw [hwf]; exact hi)]
    rfl
  · rw [if_neg h]
    unfold kindAt
    rw [get_set_ne D i w _ h]

theorem occ_set (D : Display n) (i : Nat) (hi : i < n*n)
    (hwf : WFD D) (c : DKind) (s : Nat) (w : Nat) :
    occD (D.set i (some (c, s))) w
      = if w = i then true else occD D w := by
  by_cases h : w = i
  · subst h
    rw [if_pos rfl]
    unfold occD
    rw [get_set_self D w _ (by rw [hwf]; exact hi)]
    rfl
  · rw [if_neg h]
    unfold occD
    rw [get_set_ne D i w _ h]

/-- Bounds of the witness cells at side ≥ 3. -/
theorem wb (hn : 3 ≤ n) : 2 < n*n ∧ 1 < n*n ∧ n+1 < n*n ∧ n < n*n
    ∧ 2*n < n*n ∧ n+2 < n*n ∧ 2*n+1 < n*n ∧ 0 < n*n := by
  have h3 : 3*n ≤ n*n := Nat.mul_le_mul_right n hn
  omega

/-- The five stones, placed in turn order. -/
def witD1 : Display n := (emptyD n).set 2 (some (.b, 0))
def witD2 : Display n := (witD1).set 1 (some (.w, 0))
def witD3 : Display n := (witD2).set (n+1) (some (.b, 0))
def witD4 : Display n := (witD3).set n (some (.w, 0))
def witD5 : Display n := (witD4).set (2*n) (some (.b, 0))

theorem witD1_wfd : WFD (witD1 (n := n)) := wfd_set _ _ _ emptyD_wfd
theorem witD2_wfd : WFD (witD2 (n := n)) := wfd_set _ _ _ witD1_wfd
theorem witD3_wfd : WFD (witD3 (n := n)) := wfd_set _ _ _ witD2_wfd
theorem witD4_wfd : WFD (witD4 (n := n)) := wfd_set _ _ _ witD3_wfd
theorem witD5_wfd : WFD (witD5 (n := n)) := wfd_set _ _ _ witD4_wfd

theorem emptyD_kind (w : Nat) : kindAt (emptyD n) w = none := by
  unfold kindAt
  rw [emptyD_get w]
  rfl

theorem witD1_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witD1 (n := n)) w = if w = 2 then some .b else none := by
  show kindAt ((emptyD n).set 2 (some (.b, 0))) w = _
  rw [kind_set _ _ (wb hn).1 emptyD_wfd]
  by_cases h : w = 2
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, emptyD_kind]

theorem witD2_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witD2 (n := n)) w
      = if w = 1 then some .w else if w = 2 then some .b else none := by
  show kindAt ((witD1).set 1 (some (.w, 0))) w = _
  rw [kind_set _ _ (wb hn).2.1 witD1_wfd]
  by_cases h : w = 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, witD1_kind hn]

theorem witD3_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witD3 (n := n)) w
      = if w = n+1 then some .b else if w = 1 then some .w
        else if w = 2 then some .b else none := by
  show kindAt ((witD2).set (n+1) (some (.b, 0))) w = _
  rw [kind_set _ _ (wb hn).2.2.1 witD2_wfd]
  by_cases h : w = n+1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, witD2_kind hn]

theorem witD4_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witD4 (n := n)) w
      = if w = n then some .w else if w = n+1 then some .b
        else if w = 1 then some .w else if w = 2 then some .b
        else none := by
  show kindAt ((witD3).set n (some (.w, 0))) w = _
  rw [kind_set _ _ (wb hn).2.2.2.1 witD3_wfd]
  by_cases h : w = n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, witD3_kind hn]

theorem witD5_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witD5 (n := n)) w
      = if w = 2*n then some .b else if w = n then some .w
        else if w = n+1 then some .b else if w = 1 then some .w
        else if w = 2 then some .b else none := by
  show kindAt ((witD4).set (2*n) (some (.b, 0))) w = _
  rw [kind_set _ _ (wb hn).2.2.2.2.1 witD4_wfd]
  by_cases h : w = 2*n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, witD4_kind hn]

/-- Occupancy from the kind table. -/
theorem occ_of_kind_eq {D : Display n} {w : Nat}
    (h : kindAt D w = none) : occD D w = false := by
  unfold kindAt at h
  unfold occD
  cases hg : D.get w with
  | none => rfl
  | some c =>
    rw [hg] at h
    cases h

/-! ### Move and reduction helpers -/

/-- A quiet move: nothing captured, no suicide — the output is the
    placed diagram. -/
theorem goMoveN_quiet (d : Display n) (c : DKind) (i : Nat)
    (hwf : WFD d) (hemp : occD d i = false)
    (hdead : deadOppN n d c i = [])
    (hsui : suicideN n d c i = false) :
    goMoveN n d c i = some (d.set i (some (c, 0))) := by
  unfold goMoveN
  rw [hemp]
  simp only [Bool.false_eq_true, if_false, hsui, Option.some.injEq]
  have hAC := afterCapN_nocap_get d c i hwf hdead
  apply display_ext
  apply Array.ext
  · rw [show (afterCapN n d c i).cells.size = n*n from by
      unfold afterCapN
      simp [Array.size_map, Array.size_range]]
    rw [show ((d.set i (some (c, 0))).cells.size = n*n) from by
      rw [set_size]
      exact hwf]
  · intro p h1 h2
    have hib : p < n*n := by
      have hs : (afterCapN n d c i).cells.size = n*n := by
        unfold afterCapN
        simp [Array.size_map, Array.size_range]
      omega
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2, hAC p]
    rfl

/-- Nothing of the opposite color dies when every opposite stone's
    component keeps a liberty. -/
theorem deadOpp_nil_of (d : Display n) (c : DKind) (i : Nat)
    (h : ∀ p, kindAt (placedN n d c i) p = some c.opp →
      noLibD (placedN n d c i) (componentD (placedN n d c i) p)
        = false) :
    deadOppN n d c i = [] := by
  rw [show deadOppN n d c i = (allIdx n).filter (fun p =>
      kindAt (placedN n d c i) p == some c.opp &&
      noLibD (placedN n d c i) (componentD (placedN n d c i) p))
    from rfl]
  rw [List.filter_eq_nil_iff]
  intro p _ hcontra
  rw [Bool.and_eq_true] at hcontra
  rw [h p (beq_iff_eq.mp hcontra.1)] at hcontra
  exact Bool.noConfusion hcontra.2

/-- No suicide when the placed component keeps a liberty (and nothing
    was captured). -/
theorem suicideN_false_of (d : Display n) (c : DKind) (i : Nat)
    (hwf : WFD d) (hi : i < n*n) (hc : c ≠ .r)
    (hdead : deadOppN n d c i = [])
    (hlib : noLibD (placedN n d c i)
      (componentD (placedN n d c i) i) = false) :
    suicideN n d c i = false := by
  have hAC := afterCapN_nocap_get d c i hwf hdead
  have hocceq : ∀ w, occD (afterCapN n d c i) w
      = occD (placedN n d c i) w := by
    intro w
    unfold occD
    rw [hAC w]
  have hkindeq : ∀ w, kindAt (afterCapN n d c i) w
      = kindAt (placedN n d c i) w := by
    intro w
    unfold kindAt
    rw [hAC w]
  have hkiP : kindAt (placedN n d c i) i = some c :=
    kindAt_placedN_self d c i hwf hi
  have hkiA : kindAt (afterCapN n d c i) i = some c := by
    rw [hkindeq i]
    exact hkiP
  have hcompeq : ∀ q, q ∈ componentD (afterCapN n d c i) i
      ↔ q ∈ componentD (placedN n d c i) i :=
    componentD_transport _ _ c (fun w _ => by rw [hkindeq w]) i hkiA hkiP
  show noLibD (afterCapN n d c i)
    (componentD (afterCapN n d c i) i) = false
  rw [noLibD_occ_congr _ _ hocceq, noLibD_congr _ _ _ hcompeq]
  exact hlib

/-- A stone with no same-kind neighbor spans a singleton component. -/
theorem comp_singleton (D : Display n) (p : Nat) (k : DKind)
    (hk : kindAt D p = some k)
    (hnb : ∀ q, q < n*n → adjI n q p = true → kindAt D q ≠ some k) :
    ∀ q, q ∈ componentD D p ↔ q = p := by
  intro q
  constructor
  · intro hq
    have hconn := (componentD_mem_iff D p k hk q).mp hq
    clear hq
    induction hconn with
    | refl => rfl
    | step hc hqi hqk hadj ih =>
      exfalso
      rw [ih] at hadj
      exact hnb _ (List.mem_range.mp hqi) hadj hqk
  · intro h
    rw [h]
    exact componentD_mem_self D p k hk

/-- noLibD, positively: no empty neighbor of any member. -/
theorem noLibD_true_of (D : Display n) (comp : List Nat)
    (h : ∀ q, q < n*n → occD D q = false →
      ∀ m, m ∈ comp → adjI n q m = true → False) :
    noLibD D comp = true := by
  unfold noLibD
  rw [List.all_eq_true]
  intro q hq
  cases hocc : occD D q with
  | true => rfl
  | false =>
    cases hany : comp.any (fun r => adjI n q r) with
    | false => rfl
    | true =>
      exfalso
      rcases List.any_eq_true.mp hany with ⟨m, hm, hadj⟩
      exact h q (List.mem_range.mp hq) hocc m hm hadj

/-- The collision placement. -/
theorem placeJoint_collision (D : Display n) (t i : Nat) :
    placeJoint D t (some i) (some i) = D.set i (some (.r, t)) := by
  simp only [placeJoint]
  rw [if_pos (beq_iff_eq.mpr rfl)]

/-- With both capture lists empty the basic reduction is the
    identity — no classicality needed. -/
theorem basicCap_id_nil (D : Display n) (t : Nat) (hwf : WFD D)
    (hb : capturedOf D t .b = []) (hw : capturedOf D t .w = []) :
    basicCap D t = D := by
  apply display_ext
  apply Array.ext
  · rw [basicCap_size, hwf]
  · intro p h1 h2
    have hib : p < n*n := by
      have := basicCap_size D t
      omega
    rw [← get_in_bounds _ p h1, ← get_in_bounds _ p h2]
    show (basicCap D t).get p = D.get p
    unfold basicCap
    rw [get_map_range, if_pos hib, hb, hw]
    simp

/-- CommuteAt from equal serial composites, both raw orders. -/
theorem commuteAt_BW {d : Display n} {m0 m1 : Option Nat} {x : Display n}
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n)
    (hx : bStep2 n d .b .w m0 m1 = some x)
    (hy : bStep2 n d .w .b m1 m0 = some x) :
    CommuteAt (goGame n) (PState.live d false false) (mB m0) (mW m1) := by
  refine ⟨tag01 m0 m1 x, tag10 m0 m1 x, ?_, ?_, ?_⟩
  · rw [hash2_01 d m0 m1 h0 h1, hx]
    rfl
  · rw [hash2_10 d m0 m1 h0 h1, hy]
    rfl
  · rw [sN_tag01, sN_tag10]

theorem commuteAt_WB {d : Display n} {m0 m1 : Option Nat} {x : Display n}
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n)
    (hx : bStep2 n d .b .w m0 m1 = some x)
    (hy : bStep2 n d .w .b m1 m0 = some x) :
    CommuteAt (goGame n) (PState.live d false false) (mW m1) (mB m0) := by
  refine ⟨tag10 m0 m1 x, tag01 m0 m1 x, ?_, ?_, ?_⟩
  · rw [hash2_10 d m0 m1 h0 h1, hy]
    rfl
  · rw [hash2_01 d m0 m1 h0 h1, hx]
    rfl
  · rw [sN_tag10, sN_tag01]

/-- The associated state of a commuting turn, computed. -/
theorem assoc_BW {d : Display n} {m0 m1 : Option Nat} {x : Display n}
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n)
    (hx : bStep2 n d .b .w m0 m1 = some x)
    (hnn : ¬(m0 = none ∧ m1 = none)) :
    assocOf (goGame n) (PState.live d false false) (mB m0) (mW m1)
      = PState.live x false false := by
  unfold assocOf
  rw [hash2_01 d m0 m1 h0 h1, hx]
  rw [show Option.getD (Option.map (tag01 m0 m1) (some x))
    (PState.live d false false) = tag01 m0 m1 x from rfl]
  rw [sN_tag01]
  exact repP_live hnn x

theorem assoc_WB {d : Display n} {m0 m1 : Option Nat} {x : Display n}
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n)
    (hy : bStep2 n d .w .b m1 m0 = some x)
    (hnn : ¬(m0 = none ∧ m1 = none)) :
    assocOf (goGame n) (PState.live d false false) (mW m1) (mB m0)
      = PState.live x false false := by
  unfold assocOf
  rw [hash2_10 d m0 m1 h0 h1, hy]
  rw [show Option.getD (Option.map (tag10 m0 m1) (some x))
    (PState.live d false false) = tag10 m0 m1 x from rfl]
  rw [sN_tag10]
  exact repP_live hnn x

/-! ### Kind inversion on the witness diagrams -/

theorem witD2_cases (hn : 3 ≤ n) {p : Nat} {k : DKind}
    (hk : kindAt (witD2 (n := n)) p = some k) :
    (p = 1 ∧ k = .w) ∨ (p = 2 ∧ k = .b) := by
  rw [witD2_kind hn] at hk
  by_cases h1 : p = 1
  · rw [if_pos h1] at hk
    exact Or.inl ⟨h1, (Option.some.inj hk).symm⟩
  · rw [if_neg h1] at hk
    by_cases h2 : p = 2
    · rw [if_pos h2] at hk
      exact Or.inr ⟨h2, (Option.some.inj hk).symm⟩
    · rw [if_neg h2] at hk
      cases hk

theorem witD3_cases (hn : 3 ≤ n) {p : Nat} {k : DKind}
    (hk : kindAt (witD3 (n := n)) p = some k) :
    (p = n+1 ∧ k = .b) ∨ (p = 1 ∧ k = .w) ∨ (p = 2 ∧ k = .b) := by
  rw [witD3_kind hn] at hk
  by_cases h0 : p = n+1
  · rw [if_pos h0] at hk
    exact Or.inl ⟨h0, (Option.some.inj hk).symm⟩
  · rw [if_neg h0] at hk
    by_cases h1 : p = 1
    · rw [if_pos h1] at hk
      exact Or.inr (Or.inl ⟨h1, (Option.some.inj hk).symm⟩)
    · rw [if_neg h1] at hk
      by_cases h2 : p = 2
      · rw [if_pos h2] at hk
        exact Or.inr (Or.inr ⟨h2, (Option.some.inj hk).symm⟩)
      · rw [if_neg h2] at hk
        cases hk

theorem witD4_cases (hn : 3 ≤ n) {p : Nat} {k : DKind}
    (hk : kindAt (witD4 (n := n)) p = some k) :
    (p = n ∧ k = .w) ∨ (p = n+1 ∧ k = .b) ∨ (p = 1 ∧ k = .w)
      ∨ (p = 2 ∧ k = .b) := by
  rw [witD4_kind hn] at hk
  by_cases hn' : p = n
  · rw [if_pos hn'] at hk
    exact Or.inl ⟨hn', (Option.some.inj hk).symm⟩
  · rw [if_neg hn'] at hk
    rcases witD3_cases hn (by rw [witD3_kind hn]; exact hk) with
      ⟨h, hkk⟩ | ⟨h, hkk⟩ | ⟨h, hkk⟩
    · exact Or.inr (Or.inl ⟨h, hkk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, hkk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, hkk⟩))

theorem witD5_cases (hn : 3 ≤ n) {p : Nat} {k : DKind}
    (hk : kindAt (witD5 (n := n)) p = some k) :
    (p = 2*n ∧ k = .b) ∨ (p = n ∧ k = .w) ∨ (p = n+1 ∧ k = .b)
      ∨ (p = 1 ∧ k = .w) ∨ (p = 2 ∧ k = .b) := by
  rw [witD5_kind hn] at hk
  by_cases h2n : p = 2*n
  · rw [if_pos h2n] at hk
    exact Or.inl ⟨h2n, (Option.some.inj hk).symm⟩
  · rw [if_neg h2n] at hk
    rcases witD4_cases hn (by rw [witD4_kind hn]; exact hk) with
      ⟨h, hkk⟩ | ⟨h, hkk⟩ | ⟨h, hkk⟩ | ⟨h, hkk⟩
    · exact Or.inr (Or.inl ⟨h, hkk⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, hkk⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hkk⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hkk⟩)))

/-- Reading occupancy off a table entry. -/
theorem occ_true_of_kind {D : Display n} {w : Nat} {k : DKind}
    (h : kindAt D w = some k) : occD D w = true := occD_of_kind h

/-! ### The five quiet placements -/

theorem witD1_at2 (hn : 3 ≤ n) : kindAt (witD1 (n := n)) 2 = some .b := by
  rw [witD1_kind hn, if_pos rfl]

theorem mv1 (hn : 3 ≤ n) :
    goMoveN n (emptyD n) .b 2 = some (witD1 (n := n)) := by
  have hdead : deadOppN n (emptyD n) .b 2 = [] := by
    apply deadOpp_nil_of
    intro p hk
    exfalso
    rw [show placedN n (emptyD n) .b 2 = witD1 (n := n) from rfl,
      witD1_kind hn] at hk
    by_cases h2 : p = 2
    · rw [if_pos h2] at hk
      cases hk
    · rw [if_neg h2] at hk
      cases hk
  refine goMoveN_quiet _ _ _ emptyD_wfd (occ_of_kind_eq (emptyD_kind 2))
    hdead (suicideN_false_of _ _ _ emptyD_wfd (wb hn).1
      (by intro h; cases h) hdead ?_)
  apply (noLibD_eq_false_iff _ _).mpr
  refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_, 2, ?_, ?_⟩
  · apply occ_of_kind_eq
    rw [show placedN n (emptyD n) .b 2 = witD1 (n := n) from rfl,
      witD1_kind hn, if_neg (by omega)]
  · exact componentD_mem_self _ 2 .b
      (by rw [show placedN n (emptyD n) .b 2 = witD1 (n := n) from rfl]
          exact witD1_at2 hn)
  · exact adjI_symm (adj_2_n2 hn)

theorem mv2 (hn : 3 ≤ n) :
    goMoveN n (witD1 (n := n)) .w 1 = some (witD2 (n := n)) := by
  have hpl : placedN n (witD1 (n := n)) .w 1 = witD2 (n := n) := rfl
  have hdead : deadOppN n (witD1 (n := n)) .w 1 = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl] at hk
    rcases witD2_cases hn hk with ⟨h1, hkk⟩ | ⟨h2, hkk⟩
    · exact absurd hkk (by decide)
    · subst h2
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_, 2, ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD2_kind hn, if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ 2 .b
          (by rw [witD2_kind hn, if_neg (by omega), if_pos rfl])
      · exact adjI_symm (adj_2_n2 hn)
  refine goMoveN_quiet _ _ _ witD1_wfd ?_ hdead
    (suicideN_false_of _ _ _ witD1_wfd (wb hn).2.1
      (by intro h; cases h) hdead ?_)
  · apply occ_of_kind_eq
    rw [witD1_kind hn, if_neg (by omega)]
  · apply (noLibD_eq_false_iff _ _).mpr
    rw [hpl]
    refine ⟨0, List.mem_range.mpr (wb hn).2.2.2.2.2.2.2, ?_, 1, ?_, ?_⟩
    · apply occ_of_kind_eq
      rw [witD2_kind hn, if_neg (by omega), if_neg (by omega)]
    · exact componentD_mem_self _ 1 .w
        (by rw [witD2_kind hn, if_pos rfl])
    · exact adj_0_1 hn

theorem mv3 (hn : 3 ≤ n) :
    goMoveN n (witD2 (n := n)) .b (n+1) = some (witD3 (n := n)) := by
  have hpl : placedN n (witD2 (n := n)) .b (n+1) = witD3 (n := n) := rfl
  have hdead : deadOppN n (witD2 (n := n)) .b (n+1) = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl] at hk
    rcases witD3_cases hn hk with ⟨h0, hkk⟩ | ⟨h1, hkk⟩ | ⟨h2, hkk⟩
    · exact absurd hkk (by decide)
    · subst h1
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨0, List.mem_range.mpr (wb hn).2.2.2.2.2.2.2, ?_, 1, ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD3_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
      · exact componentD_mem_self _ 1 .w
          (by rw [witD3_kind hn, if_neg (by omega), if_pos rfl])
      · exact adj_0_1 hn
    · exact absurd hkk (by decide)
  refine goMoveN_quiet _ _ _ witD2_wfd ?_ hdead
    (suicideN_false_of _ _ _ witD2_wfd (wb hn).2.2.1
      (by intro h; cases h) hdead ?_)
  · apply occ_of_kind_eq
    rw [witD2_kind hn, if_neg (by omega), if_neg (by omega)]
  · apply (noLibD_eq_false_iff _ _).mpr
    rw [hpl]
    refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_, n+1, ?_, ?_⟩
    · apply occ_of_kind_eq
      rw [witD3_kind hn, if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    · exact componentD_mem_self _ (n+1) .b
        (by rw [witD3_kind hn, if_pos rfl])
    · exact adjI_symm (adj_n1_n2 hn)

theorem mv4 (hn : 3 ≤ n) :
    goMoveN n (witD3 (n := n)) .w n = some (witD4 (n := n)) := by
  have hpl : placedN n (witD3 (n := n)) .w n = witD4 (n := n) := rfl
  have hdead : deadOppN n (witD3 (n := n)) .w n = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl] at hk
    rcases witD4_cases hn hk with ⟨hp, hkk⟩ | ⟨hp, hkk⟩ | ⟨hp, hkk⟩
      | ⟨hp, hkk⟩
    · exact absurd hkk (by decide)
    · subst hp
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_, n+1,
        ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ (n+1) .b
          (by rw [witD4_kind hn, if_neg (by omega), if_pos rfl])
      · exact adjI_symm (adj_n1_n2 hn)
    · exact absurd hkk (by decide)
    · subst hp
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_, 2, ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ 2 .b
          (by rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl])
      · exact adjI_symm (adj_2_n2 hn)
  refine goMoveN_quiet _ _ _ witD3_wfd ?_ hdead
    (suicideN_false_of _ _ _ witD3_wfd (wb hn).2.2.2.1
      (by intro h; cases h) hdead ?_)
  · apply occ_of_kind_eq
    rw [witD3_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  · apply (noLibD_eq_false_iff _ _).mpr
    rw [hpl]
    refine ⟨0, List.mem_range.mpr (wb hn).2.2.2.2.2.2.2, ?_, n, ?_, ?_⟩
    · apply occ_of_kind_eq
      rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
    · exact componentD_mem_self _ n .w
        (by rw [witD4_kind hn, if_pos rfl])
    · exact adj_0_n hn

theorem mv5 (hn : 3 ≤ n) :
    goMoveN n (witD4 (n := n)) .b (2*n) = some (witD5 (n := n)) := by
  have hpl : placedN n (witD4 (n := n)) .b (2*n) = witD5 (n := n) := rfl
  have hdead : deadOppN n (witD4 (n := n)) .b (2*n) = [] := by
    apply deadOpp_nil_of
    intro p hk
    rw [hpl] at hk
    rcases witD5_cases hn hk with ⟨hp, hkk⟩ | ⟨hp, hkk⟩ | ⟨hp, hkk⟩
      | ⟨hp, hkk⟩ | ⟨hp, hkk⟩
    · exact absurd hkk (by decide)
    · rw [hp]
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨0, List.mem_range.mpr (wb hn).2.2.2.2.2.2.2, ?_, n, ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ n .w
          (by rw [witD5_kind hn, if_neg (by omega), if_pos rfl])
      · exact adj_0_n hn
    · exact absurd hkk (by decide)
    · subst hp
      apply (noLibD_eq_false_iff _ _).mpr
      rw [hpl]
      refine ⟨0, List.mem_range.mpr (wb hn).2.2.2.2.2.2.2, ?_, 1, ?_, ?_⟩
      · apply occ_of_kind_eq
        rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ 1 .w
          (by rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl])
      · exact adj_0_1 hn
    · exact absurd hkk (by decide)
  refine goMoveN_quiet _ _ _ witD4_wfd ?_ hdead
    (suicideN_false_of _ _ _ witD4_wfd (wb hn).2.2.2.2.1
      (by intro h; cases h) hdead ?_)
  · apply occ_of_kind_eq
    rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  · apply (noLibD_eq_false_iff _ _).mpr
    rw [hpl]
    refine ⟨2*n+1, List.mem_range.mpr (wb hn).2.2.2.2.2.2.1, ?_, 2*n,
      ?_, ?_⟩
    · apply occ_of_kind_eq
      rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · exact componentD_mem_self _ (2*n) .b
        (by rw [witD5_kind hn, if_pos rfl])
    · exact adjI_symm (adj_2n_2n1 hn)

/-! ### The collision A1/A1 -/

def witP6b : Display n := (witD5).set 0 (some (.b, 0))
def witP6w : Display n := (witD5).set 0 (some (.w, 0))

theorem witP6b_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witP6b (n := n)) w
      = if w = 0 then some .b else kindAt (witD5 (n := n)) w := by
  show kindAt ((witD5).set 0 (some (.b, 0))) w = _
  rw [kind_set _ _ (wb hn).2.2.2.2.2.2.2 witD5_wfd]

theorem witP6w_kind (hn : 3 ≤ n) (w : Nat) :
    kindAt (witP6w (n := n)) w
      = if w = 0 then some .w else kindAt (witD5 (n := n)) w := by
  show kindAt ((witD5).set 0 (some (.w, 0))) w = _
  rw [kind_set _ _ (wb hn).2.2.2.2.2.2.2 witD5_wfd]

theorem witD5_occ0 (hn : 3 ≤ n) : occD (witD5 (n := n)) 0 = false := by
  apply occ_of_kind_eq
  rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The white singletons of the placed black display. -/
theorem witP6b_comp1 (hn : 3 ≤ n) :
    ∀ q, q ∈ componentD (witP6b (n := n)) 1 ↔ q = 1 := by
  apply comp_singleton _ 1 .w
    (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
      if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl])
  intro q hq hadj
  rcases nbr_1 hn hadj with h | h | h <;> subst h <;>
    rw [witP6b_kind hn]
  · rw [if_pos rfl]
    intro hc
    cases hc
  · rw [if_neg (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
    intro hc
    cases hc
  · rw [if_neg (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_pos rfl]
    intro hc
    cases hc

theorem witP6b_compn (hn : 3 ≤ n) :
    ∀ q, q ∈ componentD (witP6b (n := n)) n ↔ q = n := by
  apply comp_singleton _ n .w
    (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
      if_neg (by omega), if_pos rfl])
  intro q hq hadj
  rcases nbr_n hn hadj with h | h | h <;> subst h <;>
    rw [witP6b_kind hn]
  · rw [if_pos rfl]
    intro hc
    cases hc
  · rw [if_neg (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_pos rfl]
    intro hc
    cases hc
  · rw [if_neg (by omega), witD5_kind hn, if_pos rfl]
    intro hc
    cases hc

theorem witP6b_nolib1 (hn : 3 ≤ n) :
    noLibD (witP6b (n := n)) (componentD (witP6b (n := n)) 1) = true := by
  apply noLibD_true_of
  intro q hq hocc m hm hadj
  have hm1 : m = 1 := (witP6b_comp1 hn m).mp hm
  subst hm1
  rcases nbr_1 hn hadj with h | h | h <;> subst h <;>
    rw [show occD (witP6b (n := n)) _ = _ from rfl] at hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_pos rfl] : kindAt _ 0 = some .b)] at hocc
    cases hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl] :
        kindAt _ 2 = some .b)] at hocc
    cases hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
        if_neg (by omega), if_neg (by omega), if_pos rfl] :
        kindAt _ (n+1) = some .b)] at hocc
    cases hocc

theorem witP6b_nolibn (hn : 3 ≤ n) :
    noLibD (witP6b (n := n)) (componentD (witP6b (n := n)) n) = true := by
  apply noLibD_true_of
  intro q hq hocc m hm hadj
  have hm1 : m = n := (witP6b_compn hn m).mp hm
  rw [hm1] at hadj
  rcases nbr_n hn hadj with h | h | h <;> subst h <;>
    rw [show occD (witP6b (n := n)) _ = _ from rfl] at hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_pos rfl] : kindAt _ 0 = some .b)] at hocc
    cases hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
        if_neg (by omega), if_neg (by omega), if_pos rfl] :
        kindAt _ (n+1) = some .b)] at hocc
    cases hocc
  · rw [occ_true_of_kind (D := witP6b (n := n))
      (by rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
        if_pos rfl] : kindAt _ (2*n) = some .b)] at hocc
    cases hocc

/-- Both whites die to Black's A1. -/
theorem wit_dead1 (hn : 3 ≤ n) : 1 ∈ deadOppN n (witD5 (n := n)) .b 0 := by
  rw [mem_deadOppN_iff]
  refine ⟨List.mem_range.mpr (wb hn).2.1, ?_, ?_⟩
  · show kindAt (witP6b (n := n)) 1 = some DKind.b.opp
    rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
      if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
    rfl
  · exact witP6b_nolib1 hn

theorem wit_deadn (hn : 3 ≤ n) : n ∈ deadOppN n (witD5 (n := n)) .b 0 := by
  rw [mem_deadOppN_iff]
  refine ⟨List.mem_range.mpr (wb hn).2.2.2.1, ?_, ?_⟩
  · show kindAt (witP6b (n := n)) n = some DKind.b.opp
    rw [witP6b_kind hn, if_neg (by omega), witD5_kind hn,
      if_neg (by omega), if_pos rfl]
    rfl
  · exact witP6b_nolibn hn

theorem wit_notdead0 (hn : 3 ≤ n) :
    ¬ 0 ∈ deadOppN n (witD5 (n := n)) .b 0 := by
  intro hmem
  rcases (mem_deadOppN_iff _ _ _ _).mp hmem with ⟨-, hk, -⟩
  rw [show kindAt (placedN n (witD5 (n := n)) .b 0) 0
    = kindAt (witP6b (n := n)) 0 from rfl, witP6b_kind hn,
    if_pos rfl] at hk
  cases hk

/-- Black's A1: the capture output stands at A1, empty at A2. -/
theorem wit_AC_get0 (hn : 3 ≤ n) :
    (afterCapN n (witD5 (n := n)) .b 0).get 0 = some (.b, 0) := by
  rw [afterCapN_get, if_pos (wb hn).2.2.2.2.2.2.2]
  rw [if_neg (by
    intro hcont
    exact wit_notdead0 hn (List.contains_iff_mem.mp hcont))]
  show (witP6b (n := n)).get 0 = some (.b, 0)
  exact get_set_self _ _ _ (by rw [witD5_wfd]; exact (wb hn).2.2.2.2.2.2.2)

theorem wit_AC_occ0 (hn : 3 ≤ n) :
    occD (afterCapN n (witD5 (n := n)) .b 0) 0 = true := by
  unfold occD
  rw [wit_AC_get0 hn]
  rfl

theorem wit_AC_occ1 (hn : 3 ≤ n) :
    occD (afterCapN n (witD5 (n := n)) .b 0) 1 = false := by
  apply occ_of_get_none
  rw [afterCapN_get, if_pos (wb hn).2.1,
    if_pos (List.contains_iff_mem.mpr (wit_dead1 hn))]

theorem wit_hAC (hn : 3 ≤ n) :
    goMoveN n (witD5 (n := n)) .b 0
      = some (afterCapN n (witD5 (n := n)) .b 0) := by
  have hsui : suicideN n (witD5 (n := n)) .b 0 = false := by
    show noLibD (afterCapN n (witD5 (n := n)) .b 0)
      (componentD (afterCapN n (witD5 (n := n)) .b 0) 0) = false
    apply (noLibD_eq_false_iff _ _).mpr
    refine ⟨1, List.mem_range.mpr (wb hn).2.1, wit_AC_occ1 hn, 0, ?_, ?_⟩
    · apply componentD_mem_self _ 0 .b
      unfold kindAt
      rw [wit_AC_get0 hn]
      rfl
    · exact adjI_symm (adj_0_1 hn)
  unfold goMoveN
  rw [witD5_occ0 hn]
  simp only [Bool.false_eq_true, if_false, hsui]

/-! ### White's A1: the three-stone suicide -/

theorem witP6w_k0 (hn : 3 ≤ n) : kindAt (witP6w (n := n)) 0 = some .w := by
  rw [witP6w_kind hn, if_pos rfl]

theorem witP6w_k1 (hn : 3 ≤ n) : kindAt (witP6w (n := n)) 1 = some .w := by
  rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem witP6w_kn (hn : 3 ≤ n) : kindAt (witP6w (n := n)) n = some .w := by
  rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
    if_neg (by omega), if_pos rfl]

theorem witP6w_k2 (hn : 3 ≤ n) : kindAt (witP6w (n := n)) 2 = some .b := by
  rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem witP6w_kn1 (hn : 3 ≤ n) :
    kindAt (witP6w (n := n)) (n+1) = some .b := by
  rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
    if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem witP6w_k2n (hn : 3 ≤ n) :
    kindAt (witP6w (n := n)) (2*n) = some .b := by
  rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn, if_pos rfl]

/-- No black dies to White's A1. -/
theorem wit_deadW (hn : 3 ≤ n) : deadOppN n (witD5 (n := n)) .w 0 = [] := by
  apply deadOpp_nil_of
  intro p hk
  have hk' : kindAt (witP6w (n := n)) p = some .b := hk
  rw [witP6w_kind hn] at hk'
  by_cases h0 : p = 0
  · rw [if_pos h0] at hk'
    cases hk'
  · rw [if_neg h0] at hk'
    rcases witD5_cases hn hk' with ⟨hp, -⟩ | ⟨hp, hkk⟩ | ⟨hp, -⟩
      | ⟨hp, hkk⟩ | ⟨hp, -⟩
    · rw [hp]
      apply (noLibD_eq_false_iff _ _).mpr
      refine ⟨2*n+1, List.mem_range.mpr (wb hn).2.2.2.2.2.2.1, ?_,
        2*n, ?_, ?_⟩
      · apply occ_of_kind_eq
        show kindAt (witP6w (n := n)) (2*n+1) = none
        rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ (2*n) .b (witP6w_k2n hn)
      · exact adjI_symm (adj_2n_2n1 hn)
    · exact absurd hkk (by decide)
    · rw [hp]
      apply (noLibD_eq_false_iff _ _).mpr
      refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_,
        n+1, ?_, ?_⟩
      · apply occ_of_kind_eq
        show kindAt (witP6w (n := n)) (n+2) = none
        rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ (n+1) .b (witP6w_kn1 hn)
      · exact adjI_symm (adj_n1_n2 hn)
    · exact absurd hkk (by decide)
    · rw [hp]
      apply (noLibD_eq_false_iff _ _).mpr
      refine ⟨n+2, List.mem_range.mpr (wb hn).2.2.2.2.2.1, ?_,
        2, ?_, ?_⟩
      · apply occ_of_kind_eq
        show kindAt (witP6w (n := n)) (n+2) = none
        rw [witP6w_kind hn, if_neg (by omega), witD5_kind hn,
          if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
      · exact componentD_mem_self _ 2 .b (witP6w_k2 hn)
      · exact adjI_symm (adj_2_n2 hn)

/-- The placed white component is A1, A2, B1. -/
theorem witP6w_comp0 (hn : 3 ≤ n) :
    ∀ q, q ∈ componentD (witP6w (n := n)) 0
      ↔ (q = 0 ∨ q = 1 ∨ q = n) := by
  intro q
  constructor
  · intro hq
    have hconn := (componentD_mem_iff _ 0 .w (witP6w_k0 hn) q).mp hq
    clear hq
    induction hconn with
    | refl => exact Or.inl rfl
    | step hc hqi hqk hadj ih =>
      rcases ih with h | h | h
      · rw [h] at hadj
        rcases nbr_0 hn hadj with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rw [h] at hadj
        rcases nbr_1 hn hadj with h' | h' | h'
        · exact Or.inl h'
        · exfalso
          rw [h', witP6w_k2 hn] at hqk
          cases hqk
        · exfalso
          rw [h', witP6w_kn1 hn] at hqk
          cases hqk
      · rw [h] at hadj
        rcases nbr_n hn hadj with h' | h' | h'
        · exact Or.inl h'
        · exfalso
          rw [h', witP6w_kn1 hn] at hqk
          cases hqk
        · exfalso
          rw [h', witP6w_k2n hn] at hqk
          cases hqk
  · rintro (h | h | h)
    · rw [h]
      exact componentD_mem_self _ 0 .w (witP6w_k0 hn)
    · rw [h]
      exact (componentD_mem_iff _ 0 .w (witP6w_k0 hn) 1).mpr
        (ConnK.step ConnK.refl (List.mem_range.mpr (wb hn).2.1)
          (witP6w_k1 hn) (adjI_symm (adj_0_1 hn)))
    · rw [h]
      exact (componentD_mem_iff _ 0 .w (witP6w_k0 hn) n).mpr
        (ConnK.step ConnK.refl (List.mem_range.mpr (wb hn).2.2.2.1)
          (witP6w_kn hn) (adjI_symm (adj_0_n hn)))

/-- White's A1 is a suicide. -/
theorem wit_suiW (hn : 3 ≤ n) : suicideN n (witD5 (n := n)) .w 0 = true := by
  have hACg := afterCapN_nocap_get (witD5 (n := n)) .w 0 witD5_wfd
    (wit_deadW hn)
  have hocceq : ∀ w, occD (afterCapN n (witD5 (n := n)) .w 0) w
      = occD (witP6w (n := n)) w := by
    intro w
    unfold occD
    rw [hACg w]
    rfl
  have hkindeq : ∀ w, kindAt (afterCapN n (witD5 (n := n)) .w 0) w
      = kindAt (witP6w (n := n)) w := by
    intro w
    unfold kindAt
    rw [hACg w]
    rfl
  have hk0A : kindAt (afterCapN n (witD5 (n := n)) .w 0) 0 = some .w := by
    rw [hkindeq 0]
    exact witP6w_k0 hn
  have hcompeq : ∀ q, q ∈ componentD (afterCapN n (witD5 (n := n)) .w 0) 0
      ↔ q ∈ componentD (witP6w (n := n)) 0 :=
    componentD_transport _ _ .w (fun w _ => by rw [hkindeq w]) 0 hk0A
      (witP6w_k0 hn)
  show noLibD (afterCapN n (witD5 (n := n)) .w 0)
    (componentD (afterCapN n (witD5 (n := n)) .w 0) 0) = true
  rw [noLibD_occ_congr _ _ hocceq, noLibD_congr _ _ _ hcompeq]
  apply noLibD_true_of
  intro q hq hocc m hm hadj
  rcases (witP6w_comp0 hn m).mp hm with h | h | h
  · rw [h] at hadj
    rcases nbr_0 hn hadj with h' | h' <;> subst h'
    · rw [occ_true_of_kind (witP6w_k1 hn)] at hocc
      cases hocc
    · rw [occ_true_of_kind (witP6w_kn hn)] at hocc
      cases hocc
  · rw [h] at hadj
    rcases nbr_1 hn hadj with h' | h' | h' <;> subst h'
    · rw [occ_true_of_kind (witP6w_k0 hn)] at hocc
      cases hocc
    · rw [occ_true_of_kind (witP6w_k2 hn)] at hocc
      cases hocc
    · rw [occ_true_of_kind (witP6w_kn1 hn)] at hocc
      cases hocc
  · rw [h] at hadj
    rcases nbr_n hn hadj with h' | h' | h' <;> subst h'
    · rw [occ_true_of_kind (witP6w_k0 hn)] at hocc
      cases hocc
    · rw [occ_true_of_kind (witP6w_kn1 hn)] at hocc
      cases hocc
    · rw [occ_true_of_kind (witP6w_k2n hn)] at hocc
      cases hocc

theorem wit_hE (hn : 3 ≤ n) :
    goMoveN n (witD5 (n := n)) .w 0
      = some (erasedN n (witD5 (n := n)) .w 0) := by
  unfold goMoveN
  rw [witD5_occ0 hn]
  simp only [Bool.false_eq_true, if_false, wit_suiW hn, if_true]

/-! ### The landing move and the serialization value -/

theorem witE_wfd (hn : 3 ≤ n) : WFD (erasedN n (witD5 (n := n)) .w 0) := by
  unfold WFD erasedN
  simp [Array.size_map, Array.size_range]

/-- The erased cells: the suicide empties its component. -/
theorem witE_get_comp (hn : 3 ≤ n) {p : Nat}
    (hp : p = 0 ∨ p = 1 ∨ p = n) :
    (erasedN n (witD5 (n := n)) .w 0).get p = none := by
  have hpb : p < n*n := by
    rcases hp with h | h | h <;> rw [h]
    · exact (wb hn).2.2.2.2.2.2.2
    · exact (wb hn).2.1
    · exact (wb hn).2.2.2.1
  rw [erasedN_get, if_pos hpb, if_pos ?_]
  apply List.contains_iff_mem.mpr
  show p ∈ componentD (afterCapN n (witD5 (n := n)) .w 0) 0
  have hACg := afterCapN_nocap_get (witD5 (n := n)) .w 0 witD5_wfd
    (wit_deadW hn)
  have hkindeq : ∀ w, kindAt (afterCapN n (witD5 (n := n)) .w 0) w
      = kindAt (witP6w (n := n)) w := by
    intro w
    unfold kindAt
    rw [hACg w]
    rfl
  have hk0A : kindAt (afterCapN n (witD5 (n := n)) .w 0) 0 = some .w := by
    rw [hkindeq 0]
    exact witP6w_k0 hn
  exact (componentD_transport _ _ .w (fun w _ => by rw [hkindeq w]) 0
    hk0A (witP6w_k0 hn) p).mpr ((witP6w_comp0 hn p).mpr hp)

theorem witE_occ0 (hn : 3 ≤ n) :
    occD (erasedN n (witD5 (n := n)) .w 0) 0 = false :=
  occ_of_get_none (witE_get_comp hn (Or.inl rfl))

theorem witE_occ1 (hn : 3 ≤ n) :
    occD (erasedN n (witD5 (n := n)) .w 0) 1 = false :=
  occ_of_get_none (witE_get_comp hn (Or.inr (Or.inl rfl)))

/-- The erased board has no white stone. -/
theorem witE_nowhite (hn : 3 ≤ n) (p : Nat) :
    kindAt (erasedN n (witD5 (n := n)) .w 0) p ≠ some .w := by
  intro hk
  unfold kindAt at hk
  rw [erasedN_get] at hk
  by_cases hpb : p < n*n
  · rw [if_pos hpb] at hk
    by_cases hcont : (ownCompN n (witD5 (n := n)) .w 0).contains p = true
    · rw [if_pos hcont] at hk
      cases hk
    · rw [if_neg hcont] at hk
      have hACg := afterCapN_nocap_get (witD5 (n := n)) .w 0 witD5_wfd
        (wit_deadW hn)
      have hk' : kindAt (witP6w (n := n)) p = some .w := by
        show Option.map (fun x => x.fst)
          ((placedN n (witD5 (n := n)) .w 0).get p) = some DKind.w
        rw [← hACg p]
        exact hk
      -- so p is one of the white cells 0, 1, n — all in the component
      have hp3 : p = 0 ∨ p = 1 ∨ p = n := by
        rw [witP6w_kind hn] at hk'
        by_cases h0 : p = 0
        · exact Or.inl h0
        · rw [if_neg h0] at hk'
          rcases witD5_cases hn hk' with ⟨hp, hkk⟩ | ⟨hp, -⟩
            | ⟨hp, hkk⟩ | ⟨hp, -⟩ | ⟨hp, hkk⟩
          · exact absurd hkk (by decide)
          · exact Or.inr (Or.inr hp)
          · exact absurd hkk (by decide)
          · exact Or.inr (Or.inl hp)
          · exact absurd hkk (by decide)
      exfalso
      apply hcont
      apply List.contains_iff_mem.mpr
      show p ∈ componentD (afterCapN n (witD5 (n := n)) .w 0) 0
      have hkindeq : ∀ w, kindAt (afterCapN n (witD5 (n := n)) .w 0) w
          = kindAt (witP6w (n := n)) w := by
        intro w
        unfold kindAt
        rw [hACg w]
        rfl
      have hk0A : kindAt (afterCapN n (witD5 (n := n)) .w 0) 0
          = some .w := by
        rw [hkindeq 0]
        exact witP6w_k0 hn
      exact (componentD_transport _ _ .w (fun w _ => by rw [hkindeq w])
        0 hk0A (witP6w_k0 hn) p).mpr ((witP6w_comp0 hn p).mpr hp3)
  · rw [if_neg hpb] at hk
    cases hk

/-- Black lands on the vacated intersection. -/
theorem wit_hx4 (hn : 3 ≤ n) :
    goMoveN n (erasedN n (witD5 (n := n)) .w 0) .b 0
      = some ((erasedN n (witD5 (n := n)) .w 0).set 0 (some (.b, 0))) := by
  have hdead : deadOppN n (erasedN n (witD5 (n := n)) .w 0) .b 0 = [] := by
    apply deadOpp_nil_of
    intro p hk
    exfalso
    have hk' : kindAt ((erasedN n (witD5 (n := n)) .w 0).set 0
        (some (.b, 0))) p = some .w := hk
    rw [kind_set _ _ (wb hn).2.2.2.2.2.2.2 (witE_wfd hn)] at hk'
    by_cases h0 : p = 0
    · rw [if_pos h0] at hk'
      cases hk'
    · rw [if_neg h0] at hk'
      exact witE_nowhite hn p hk'
  refine goMoveN_quiet _ _ _ (witE_wfd hn) (witE_occ0 hn) hdead
    (suicideN_false_of _ _ _ (witE_wfd hn) (wb hn).2.2.2.2.2.2.2
      (by intro h; cases h) hdead ?_)
  apply (noLibD_eq_false_iff _ _).mpr
  refine ⟨1, List.mem_range.mpr (wb hn).2.1, ?_, 0, ?_, ?_⟩
  · show occD ((erasedN n (witD5 (n := n)) .w 0).set 0 (some (.b, 0)))
      1 = false
    rw [occ_set _ _ (wb hn).2.2.2.2.2.2.2 (witE_wfd hn),
      if_neg (by omega)]
    exact witE_occ1 hn
  · apply componentD_mem_self _ 0 .b
    show kindAt ((erasedN n (witD5 (n := n)) .w 0).set 0
      (some (.b, 0))) 0 = some .b
    rw [kind_set _ _ (wb hn).2.2.2.2.2.2.2 (witE_wfd hn), if_pos rfl]
  · exact adjI_symm (adj_0_1 hn)

/-- The serialization of the conflict: the black-first chain dies at
    the occupied intersection; the white-first chain is the suicide
    then the landing. -/
theorem wit_serialP (hn : 3 ≤ n) :
    serialP n (witD5 (n := n)) (some 0) (some 0)
      = some (dedupD n [afterCapN n (witD5 (n := n)) .b 0,
          (erasedN n (witD5 (n := n)) .w 0).set 0 (some (.b, 0))]) := by
  have hbw : bStep2 n (witD5 (n := n)) .b .w (some 0) (some 0) = none := by
    show (goMoveN n (witD5 (n := n)) .b 0).bind
      (fun d1 => goMoveN n d1 .w 0) = none
    rw [wit_hAC hn]
    show goMoveN n (afterCapN n (witD5 (n := n)) .b 0) .w 0 = none
    unfold goMoveN
    rw [wit_AC_occ0 hn]
    rfl
  have hwb : bStep2 n (witD5 (n := n)) .w .b (some 0) (some 0)
      = some ((erasedN n (witD5 (n := n)) .w 0).set 0
          (some (.b, 0))) := by
    show (goMoveN n (witD5 (n := n)) .w 0).bind
      (fun d1 => goMoveN n d1 .b 0) = _
    rw [wit_hE hn]
    show goMoveN n (erasedN n (witD5 (n := n)) .w 0) .b 0 = _
    exact wit_hx4 hn
  unfold serialP
  rw [hbw, hwb,
    show bStep n (witD5 (n := n)) .b (some 0)
      = goMoveN n (witD5 (n := n)) .b 0 from rfl,
    wit_hAC hn]

/-- Both branches are empty at A2. -/
theorem wit_branch_occ1 (hn : 3 ≤ n) {e : Display n}
    (he : e ∈ dedupD n [afterCapN n (witD5 (n := n)) .b 0,
      (erasedN n (witD5 (n := n)) .w 0).set 0 (some (.b, 0))]) :
    occD e 1 = false := by
  rcases List.mem_cons.mp (mem_dedupD _ _ he) with h | h
  · rw [h]
    exact wit_AC_occ1 hn
  · rw [List.mem_singleton.mp h]
    rw [occ_set _ _ (wb hn).2.2.2.2.2.2.2 (witE_wfd hn),
      if_neg (by omega)]
    exact witE_occ1 hn

/-! ### The display resolution is idle at the collision -/

theorem witD5_kind_occ1 (hn : 3 ≤ n) : occD (witD5 (n := n)) 1 = true := by
  apply occD_of_kind
  rw [witD5_kind hn, if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

/-- Reading the replaced q-stone. -/
theorem replaceKind_get_self (D : Display n) (z : Nat) (k : DKind)
    (c : Cell) (hg : D.get z = c) (hz : z < n*n) (hwf : WFD D) :
    (replaceKind D z k).get z = c.map (fun cc => (k, cc.2)) := by
  unfold replaceKind
  rw [get_set_self D z _ (by rw [hwf]; exact hz), hg]

theorem replaceKind_get_ne (D : Display n) (z w : Nat) (k : DKind)
    (hw : w ≠ z) : (replaceKind D z k).get w = D.get w := by
  unfold replaceKind
  exact get_set_ne D z w _ hw

/-- The idle resolution: at a display carrying the witness cells, the
    A1/A1 collision resolves to the placed q-stone alone — A2 stands. -/
theorem wit_display_idle (hn : 3 ≤ n) (D : Display n) (t : Nat)
    (hwfD : WFD D) (ht : 1 ≤ t)
    (hcells : SameCells D (witD5 (n := n))) (hst : StampsBelow D t) :
    occD (resolveTurn D t (some 0) (some 0)) 1 = true := by
  have hb0 : (0 : Nat) < n*n := (wb hn).2.2.2.2.2.2.2
  -- the placed display and its readers
  have hP6 : placeJoint D t (some 0) (some 0) = placedT D t .r 0 :=
    placeJoint_collision D t 0
  have hk0 : kindAt (placedT D t .r 0) 0 = some .r :=
    pT_kind_self D t .r 0 hwfD hb0
  have hkne : ∀ w, w ≠ 0 →
      kindAt (placedT D t .r 0) w = kindAt (witD5 (n := n)) w := by
    intro w hw
    rw [pT_kind_ne D t .r 0 w hw]
    exact hcells w
  have hoccne : ∀ w, w ≠ 0 →
      occD (placedT D t .r 0) w = occD (witD5 (n := n)) w := by
    intro w hw
    rw [pT_occ_ne D t .r 0 w hw]
    exact occ_eq_of_samecells hcells w
  have hk1 : kindAt (placedT D t .r 0) 1 = some .w := by
    rw [hkne 1 (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hkn : kindAt (placedT D t .r 0) n = some .w := by
    rw [hkne n (by omega), witD5_kind hn, if_neg (by omega), if_pos rfl]
  have hk2 : kindAt (placedT D t .r 0) 2 = some .b := by
    rw [hkne 2 (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
  have hkn1 : kindAt (placedT D t .r 0) (n+1) = some .b := by
    rw [hkne (n+1) (by omega), witD5_kind hn, if_neg (by omega),
      if_neg (by omega), if_pos rfl]
  have hk2n : kindAt (placedT D t .r 0) (2*n) = some .b := by
    rw [hkne (2*n) (by omega), witD5_kind hn, if_pos rfl]
  have hempty : ∀ w, w ≠ 0 → w ≠ 1 → w ≠ 2 → w ≠ n → w ≠ n+1 →
      w ≠ 2*n → kindAt (placedT D t .r 0) w = none := by
    intro w h0 h1 h2 hn' hn1 h2n
    rw [hkne w h0, witD5_kind hn, if_neg h2n, if_neg hn', if_neg hn1,
      if_neg h1, if_neg h2]
  -- kind inversion on the placed display
  have hinv : ∀ p k, kindAt (placedT D t .r 0) p = some k →
      (p = 0 ∧ k = .r) ∨ (p = 1 ∧ k = .w) ∨ (p = n ∧ k = .w)
      ∨ (p = 2 ∧ k = .b) ∨ (p = n+1 ∧ k = .b) ∨ (p = 2*n ∧ k = .b) := by
    intro p k hk
    by_cases h0 : p = 0
    · subst h0
      rw [hk0] at hk
      exact Or.inl ⟨rfl, (Option.some.inj hk).symm⟩
    · by_cases h1 : p = 1
      · subst h1
        rw [hk1] at hk
        exact Or.inr (Or.inl ⟨rfl, (Option.some.inj hk).symm⟩)
      · by_cases hn' : p = n
        · subst hn'
          rw [hkn] at hk
          exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj hk).symm⟩))
        · by_cases h2 : p = 2
          · subst h2
            rw [hk2] at hk
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨rfl, (Option.some.inj hk).symm⟩)))
          · by_cases hn1 : p = n+1
            · subst hn1
              rw [hkn1] at hk
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨rfl, (Option.some.inj hk).symm⟩))))
            · by_cases h2n : p = 2*n
              · subst h2n
                rw [hk2n] at hk
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨rfl, (Option.some.inj hk).symm⟩))))
              · rw [hempty p h0 h1 h2 hn' hn1 h2n] at hk
                cases hk
  -- occupancy of the six cells
  have hocc0 : occD (placedT D t .r 0) 0 = true :=
    pT_occ_self D t .r 0 hwfD hb0
  have hocc1 : occD (placedT D t .r 0) 1 = true := occD_of_kind hk1
  have hoccn : occD (placedT D t .r 0) n = true := occD_of_kind hkn
  have hocc2 : occD (placedT D t .r 0) 2 = true := occD_of_kind hk2
  have hoccn1 : occD (placedT D t .r 0) (n+1) = true := occD_of_kind hkn1
  have hocc2n : occD (placedT D t .r 0) (2*n) = true :=
    occD_of_kind hk2n
  have hoccn2 : occD (placedT D t .r 0) (n+2) = false := by
    apply occ_of_kind_eq
    exact hempty (n+2) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hocc2n1 : occD (placedT D t .r 0) (2*n+1) = false := by
    apply occ_of_kind_eq
    exact hempty (2*n+1) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  -- the white singletons and the q-stone singleton
  have hcomp1 : ∀ q, q ∈ componentD (placedT D t .r 0) 1 ↔ q = 1 := by
    apply comp_singleton _ 1 .w hk1
    intro q hq hadj
    rcases nbr_1 hn hadj with h | h | h <;> subst h
    · rw [hk0]
      intro hc
      cases hc
    · rw [hk2]
      intro hc
      cases hc
    · rw [hkn1]
      intro hc
      cases hc
  have hcompn : ∀ q, q ∈ componentD (placedT D t .r 0) n ↔ q = n := by
    apply comp_singleton _ n .w hkn
    intro q hq hadj
    rcases nbr_n hn hadj with h | h | h <;> subst h
    · rw [hk0]
      intro hc
      cases hc
    · rw [hkn1]
      intro hc
      cases hc
    · rw [hk2n]
      intro hc
      cases hc
  have hcomp0 : ∀ q, q ∈ componentD (placedT D t .r 0) 0 ↔ q = 0 := by
    apply comp_singleton _ 0 .r hk0
    intro q hq hadj
    rcases nbr_0 hn hadj with h | h <;> subst h
    · rw [hk1]
      intro hc
      cases hc
    · rw [hkn]
      intro hc
      cases hc
  -- stamps
  have hstle : ∀ z, stampAt (placedT D t .r 0) z ≤ t :=
    pT_stamp_le D t .r 0 hwfD hb0 hst
  have hst0 : stampAt (placedT D t .r 0) 0 = t :=
    pT_stamp_self D t .r 0 hwfD hb0
  -- the q-stone is trapped on the turn (both raw and recolored)
  have htrap0 : trappedOnTurn (placedT D t .r 0)
      (componentD (placedT D t .r 0) 0) t = true := by
    apply trapped_on_t_mem _ t hstle _ ?_ 0 ((hcomp0 0).mpr rfl) hst0
    apply noLibD_true_of
    intro q hq hocc m hm hadj
    rw [(hcomp0 m).mp hm] at hadj
    rcases nbr_0 hn hadj with h | h <;> subst h
    · rw [hocc1] at hocc
      cases hocc
    · rw [hoccn] at hocc
      cases hocc
  -- black components are not trapped: they keep a liberty
  have hnotb : ∀ p, kindAt (placedT D t .r 0) p = some .b →
      trappedOnTurn (placedT D t .r 0)
        (componentD (placedT D t .r 0) p) t = false := by
    intro p hkp
    rcases hinv p .b hkp with ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩
      | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · exact absurd hk (by decide)
    · subst hp
      simp only [trappedOnTurn]
      rw [show noLibD (placedT D t .r 0)
          (componentD (placedT D t .r 0) 2) = false from
        (noLibD_eq_false_iff _ _).mpr ⟨n+2,
          List.mem_range.mpr (wb hn).2.2.2.2.2.1, hoccn2, 2,
          componentD_mem_self _ 2 .b hk2, adjI_symm (adj_2_n2 hn)⟩]
      rfl
    · subst hp
      simp only [trappedOnTurn]
      rw [show noLibD (placedT D t .r 0)
          (componentD (placedT D t .r 0) (n+1)) = false from
        (noLibD_eq_false_iff _ _).mpr ⟨n+2,
          List.mem_range.mpr (wb hn).2.2.2.2.2.1, hoccn2, n+1,
          componentD_mem_self _ (n+1) .b hkn1,
          adjI_symm (adj_n1_n2 hn)⟩]
      rfl
    · subst hp
      simp only [trappedOnTurn]
      rw [show noLibD (placedT D t .r 0)
          (componentD (placedT D t .r 0) (2*n)) = false from
        (noLibD_eq_false_iff _ _).mpr ⟨2*n+1,
          List.mem_range.mpr (wb hn).2.2.2.2.2.2.1, hocc2n1, 2*n,
          componentD_mem_self _ (2*n) .b hk2n,
          adjI_symm (adj_2n_2n1 hn)⟩]
      rfl
  -- nothing black is captured
  have hcapb : capturedOf (placedT D t .r 0) t .b = [] := by
    cases hcl : capturedOf (placedT D t .r 0) t .b with
    | nil => rfl
    | cons y tl =>
      exfalso
      have hy : y ∈ capturedOf (placedT D t .r 0) t .b := by
        rw [hcl]
        exact List.mem_cons_self y tl
      rcases (mem_capturedOf _ t .b y).mp hy with ⟨p, -, hkp, hcap, -⟩
      have htr : trappedOnTurn (placedT D t .r 0)
          (componentD (placedT D t .r 0) p) t = true := by
        have h := hcap
        simp only [isCaptured] at h
        rw [Bool.and_eq_true, Bool.and_eq_true] at h
        exact h.1.1
      rw [hnotb p hkp] at htr
      exact Bool.noConfusion htr
  -- the recolored q-stone: trapped by the defender
  have hstone0 : stoneTrappedBy (placedT D t .r 0) 0 .w t = true := by
    simp only [stoneTrappedBy, hk0, DKind.opp]
    -- the replaced component is the lone recolored stone
    have hget0 : (placedT D t .r 0).get 0 = some (.r, t) :=
      pT_get_self D t .r 0 hwfD hb0
    have hRk0 : kindAt (replaceKind (placedT D t .r 0) 0 .b) 0
        = some .b := by
      unfold kindAt
      rw [replaceKind_get_self _ 0 .b _ hget0 hb0
        (pT_wfd D t .r 0 hwfD)]
      rfl
    have hRkne : ∀ w, w ≠ 0 →
        kindAt (replaceKind (placedT D t .r 0) 0 .b) w
          = kindAt (placedT D t .r 0) w := by
      intro w hw
      unfold kindAt
      rw [replaceKind_get_ne _ 0 w .b hw]
    have hcompR : ∀ q,
        q ∈ componentD (replaceKind (placedT D t .r 0) 0 .b) 0
          ↔ q = 0 := by
      apply comp_singleton _ 0 .b hRk0
      intro q hq hadj
      rcases nbr_0 hn hadj with h | h <;> rw [h]
      · rw [hRkne 1 (by omega), hk1]
        intro hc
        cases hc
      · rw [hRkne n (by omega), hkn]
        intro hc
        cases hc
    apply trapped_on_t_mem _ t ?_ _ ?_ 0 ((hcompR 0).mpr rfl) ?_
    · intro z
      by_cases hz : z = 0
      · subst hz
        unfold stampAt
        rw [replaceKind_get_self _ 0 .b _ hget0 hb0
          (pT_wfd D t .r 0 hwfD)]
        exact Nat.le_refl t
      · unfold stampAt
        rw [replaceKind_get_ne _ 0 z .b hz]
        exact hstle z
    · apply noLibD_true_of
      intro q hq hocc m hm hadj
      rw [(hcompR m).mp hm] at hadj
      have hoccR : ∀ w, w ≠ 0 →
          occD (replaceKind (placedT D t .r 0) 0 .b) w
            = occD (placedT D t .r 0) w := by
        intro w hw
        unfold occD
        rw [replaceKind_get_ne _ 0 w .b hw]
      rcases nbr_0 hn hadj with h | h <;> rw [h] at hocc
      · rw [hoccR 1 (by omega), hocc1] at hocc
        cases hocc
      · rw [hoccR n (by omega), hoccn] at hocc
        cases hocc
    · unfold stampAt
      rw [replaceKind_get_self _ 0 .b _ hget0 hb0
        (pT_wfd D t .r 0 hwfD)]
      rfl

  -- no white is captured: 3a and 3b both fail at the q-stone
  have hcapw : capturedOf (placedT D t .r 0) t .w = [] := by
    cases hcl : capturedOf (placedT D t .r 0) t .w with
    | nil => rfl
    | cons y tl =>
      exfalso
      have hy : y ∈ capturedOf (placedT D t .r 0) t .w := by
        rw [hcl]
        exact List.mem_cons_self y tl
      rcases (mem_capturedOf _ t .w y).mp hy with ⟨p, -, hkp, hcap, -⟩
      -- p is one of the whites; either way 0 is an adjacent stone of
      -- its component with the failing clauses
      have hp1n : p = 1 ∨ p = n := by
        rcases hinv p .w hkp with ⟨-, hk⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
          | ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩
        · exact absurd hk (by decide)
        · exact Or.inl hp
        · exact Or.inr hp
        · exact absurd hk (by decide)
        · exact absurd hk (by decide)
        · exact absurd hk (by decide)
      have hcompp : ∀ q, q ∈ componentD (placedT D t .r 0) p ↔ q = p := by
        rcases hp1n with h | h <;> subst h
        · exact hcomp1
        · exact hcompn
      have hadj0 : adjI n 0 p = true := by
        rcases hp1n with h | h <;> subst h
        · exact adj_0_1 hn
        · exact adj_0_n hn
      have h0fil : 0 ∈ (allIdx n).filter (fun z =>
          occD (placedT D t .r 0) z &&
          !(componentD (placedT D t .r 0) p).contains z &&
          (componentD (placedT D t .r 0) p).any
            (fun q => adjI n z q)) := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_range.mpr hb0, ?_⟩
        rw [Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨hocc0, ?_⟩, ?_⟩
        · cases hcnt : (componentD (placedT D t .r 0) p).contains 0
          · rfl
          · exfalso
            have h0p : (0 : Nat) = p :=
              (hcompp 0).mp (List.contains_iff_mem.mp hcnt)
            rcases hp1n with h | h <;> omega
        · exact List.any_eq_true.mpr ⟨p, (hcompp p).mpr rfl, hadj0⟩
      -- extract the or of 3a and 3b and refute both
      have h := hcap
      simp only [isCaptured] at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      rcases bool_or_elim h.2 with h3a | h3b
      · have hbody := List.all_eq_true.mp h3a 0 h0fil
        rw [show (kindAt (placedT D t .r 0) 0 == some DKind.w.opp
            || kindAt (placedT D t .r 0) 0 == some DKind.r) = true from by
          rw [hk0]
          apply bool_or_right
          exact beq_iff_eq.mpr rfl] at hbody
        rw [Bool.true_and, hstone0 ] at hbody
        cases hbody
      · rw [Bool.and_eq_true] at h3b
        have hbody := List.all_eq_true.mp h3b.2 0 h0fil
        have hanyf : ((componentD (placedT D t .r 0) 0).any
            (fun q => stampAt (placedT D t .r 0) q == t &&
              kindAt (placedT D t .r 0) q != some DKind.r)) = false := by
          cases hany : (componentD (placedT D t .r 0) 0).any
              (fun q => stampAt (placedT D t .r 0) q == t &&
                kindAt (placedT D t .r 0) q != some DKind.r)
          · rfl
          · exfalso
            rcases List.any_eq_true.mp hany with ⟨m, hm, hprop⟩
            rw [(hcomp0 m).mp hm] at hprop
            rw [Bool.and_eq_true] at hprop
            have := hprop.2
            rw [hk0] at this
            simp at this
        rw [htrap0, hanyf] at hbody
        simp at hbody
  -- the resolution is the placed display alone
  have hbc : basicCap (placedT D t .r 0) t = placedT D t .r 0 :=
    basicCap_id_nil _ t (pT_wfd D t .r 0 hwfD) hcapb hcapw
  have hcf : capFix (n*n+1) (placedT D t .r 0) t = placedT D t .r 0 :=
    capFix_id _ t hbc (n*n+1)
  unfold resolveTurn
  rw [hP6]
  simp only [stages]
  have htz : (t == 0) = false := by
    cases t with
    | zero => exact absurd ht (by omega)
    | succ t' => rfl
  rw [htz]
  simp only [Bool.false_eq_true, if_false]
  rw [hcf, if_pos (display_beq_self _)]
  rw [pT_occ_ne D t .r 0 1 (by omega), occ_eq_of_samecells hcells 1,
    witD5_kind_occ1 hn]

/-! ### The commuting chain and the refutation -/

/-- One black single-move turn from a tracked semiclassical state. -/
theorem semi_step_B {s : SGoState n} {d r : Display n} {i : Nat}
    (hn : 3 ≤ n)
    (hsc : SemiC (goGame n) (sgoGame n) s (PState.live d false false))
    (hi : i < n*n) (hocc : occD d i = false)
    (hmv : goMoveN n d .b i = some r) :
    ∃ s', (sgoGame n).pairE s (some (false, i)) none = some s'
      ∧ SemiC (goGame n) (sgoGame n) s' (PState.live r false false) := by
  have htr := semiC_track (by omega) hsc
  obtain ⟨d', hshape, hmemb, hdisp, -⟩ := htr.track
  have hInv := reach_inv htr.reach
  have hdd : d' = d := by
    rcases hshape with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae
      rfl
    · cases hae
  rw [hdd] at hdisp
  have hfin : s.final = false := by
    rcases hshape with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hx : bStep2 n d .b .w (some i) none = some r := by
    show (goMoveN n d .b i).bind (fun d1 => bStep n d1 .w none) = some r
    rw [hmv]
    rfl
  have hy : bStep2 n d .w .b none (some i) = some r := hmv
  have hb0 : ∀ j, (some i : Option Nat) = some j → j < n*n := by
    intro j hj
    cases hj
    exact hi
  have hb1 : ∀ j, (none : Option Nat) = some j → j < n*n := by
    intro j hj
    cases hj
  have hcomm := commuteAt_BW hb0 hb1 hx hy
  have ha := assoc_BW hb0 hb1 hx (by rintro ⟨hc, -⟩; cases hc)
  have hav0 : availD n s.disp (some i) = true := by
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi, occ_eq_of_samecells hdisp i, hocc]
    rfl
  have hEv : (sgoEv n s (some i) none).isSome :=
    (sgoEv_isSome_iff s hInv.entCompat (some i) none).mpr
      ⟨hfin, hav0, rfl⟩
  have hp : ((sgoGame n).pairE s (some (false, i)) none).isSome = true :=
    hEv
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  have hstep := SemiC.step hsc hcomm hs'
  rw [ha] at hstep
  exact ⟨s', hs', hstep⟩

/-- One white single-move turn from a tracked semiclassical state. -/
theorem semi_step_W {s : SGoState n} {d r : Display n} {i : Nat}
    (hn : 3 ≤ n)
    (hsc : SemiC (goGame n) (sgoGame n) s (PState.live d false false))
    (hi : i < n*n) (hocc : occD d i = false)
    (hmv : goMoveN n d .w i = some r) :
    ∃ s', (sgoGame n).pairE s (some (true, i)) none = some s'
      ∧ SemiC (goGame n) (sgoGame n) s' (PState.live r false false) := by
  have htr := semiC_track (by omega) hsc
  obtain ⟨d', hshape, hmemb, hdisp, -⟩ := htr.track
  have hInv := reach_inv htr.reach
  have hdd : d' = d := by
    rcases hshape with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae
      rfl
    · cases hae
  rw [hdd] at hdisp
  have hfin : s.final = false := by
    rcases hshape with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hx : bStep2 n d .b .w none (some i) = some r := hmv
  have hy : bStep2 n d .w .b (some i) none = some r := by
    show (goMoveN n d .w i).bind (fun d1 => bStep n d1 .b none) = some r
    rw [hmv]
    rfl
  have hb0 : ∀ j, (none : Option Nat) = some j → j < n*n := by
    intro j hj
    cases hj
  have hb1 : ∀ j, (some i : Option Nat) = some j → j < n*n := by
    intro j hj
    cases hj
    exact hi
  have hcomm := commuteAt_WB hb0 hb1 hx hy
  have ha := assoc_WB hb0 hb1 hy (by rintro ⟨-, hc⟩; cases hc)
  have hav1 : availD n s.disp (some i) = true := by
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi, occ_eq_of_samecells hdisp i, hocc]
    rfl
  have hEv : (sgoEv n s none (some i)).isSome :=
    (sgoEv_isSome_iff s hInv.entCompat none (some i)).mpr
      ⟨hfin, rfl, hav1⟩
  have hp : ((sgoGame n).pairE s (some (true, i)) none).isSome = true :=
    hEv
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  have hstep := SemiC.step hsc hcomm hs'
  rw [ha] at hstep
  exact ⟨s', hs', hstep⟩

/-- Occupancy tables used along the chain. -/
theorem witD1_occ (hn : 3 ≤ n) : occD (witD1 (n := n)) 1 = false := by
  apply occ_of_kind_eq
  rw [witD1_kind hn, if_neg (by omega)]

theorem witD2_occ (hn : 3 ≤ n) : occD (witD2 (n := n)) (n+1) = false := by
  apply occ_of_kind_eq
  rw [witD2_kind hn, if_neg (by omega), if_neg (by omega)]

theorem witD3_occ (hn : 3 ≤ n) : occD (witD3 (n := n)) n = false := by
  apply occ_of_kind_eq
  rw [witD3_kind hn, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem witD4_occ (hn : 3 ≤ n) : occD (witD4 (n := n)) (2*n) = false := by
  apply occ_of_kind_eq
  rw [witD4_kind hn, if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem emptyD_occ2 : occD (emptyD n) 2 = false :=
  occ_of_kind_eq (emptyD_kind 2)

set_option maxHeartbeats 2000000 in
/-- SGo is not faithful within distance one, at side ≥ 3. -/
theorem sgo_not_faithful1 (hn : 3 ≤ n) :
    ¬ FaithfulWithin (goGame n) (sgoGame n) (rhoSGo n) 1 := by
  intro hFW
  -- the five commuting turns
  have h0 : SemiC (goGame n) (sgoGame n) (sgoGame n).q0
      (PState.live (emptyD n) false false) := SemiC.init
  obtain ⟨s1, hp1, hsc1⟩ := semi_step_B hn h0 (wb hn).1 emptyD_occ2
    (mv1 hn)
  obtain ⟨s2, hp2, hsc2⟩ := semi_step_W hn hsc1 (wb hn).2.1
    (witD1_occ hn) (mv2 hn)
  obtain ⟨s3, hp3, hsc3⟩ := semi_step_B hn hsc2 (wb hn).2.2.1
    (witD2_occ hn) (mv3 hn)
  obtain ⟨s4, hp4, hsc4⟩ := semi_step_W hn hsc3 (wb hn).2.2.2.1
    (witD3_occ hn) (mv4 hn)
  obtain ⟨s5, hp5, hsc5⟩ := semi_step_B hn hsc4 (wb hn).2.2.2.2.1
    (witD4_occ hn) (mv5 hn)
  -- the conflict turn
  have htr5 := semiC_track (by omega) hsc5
  obtain ⟨d5', hshape5, hmemb5, hdisp5, -⟩ := htr5.track
  have hInv5 := reach_inv htr5.reach
  have hdd5 : d5' = witD5 (n := n) := by
    rcases hshape5 with ⟨-, hae⟩ | ⟨-, hae⟩
    · cases hae
      rfl
    · cases hae
  subst hdd5
  have hfin5 : s5.final = false := by
    rcases hshape5 with ⟨hf, -⟩ | ⟨-, hae⟩
    · exact hf
    · cases hae
  have hav0 : availD n s5.disp (some 0) = true := by
    show (decide ((0:Nat) < n*n) && !occD s5.disp 0) = true
    rw [decide_eq_true (wb hn).2.2.2.2.2.2.2,
      occ_eq_of_samecells hdisp5 0, witD5_occ0 hn]
    rfl
  have hEv6 : (sgoEv n s5 (some 0) (some 0)).isSome :=
    (sgoEv_isSome_iff s5 hInv5.entCompat (some 0) (some 0)).mpr
      ⟨hfin5, hav0, hav0⟩
  have hp6 : ((sgoGame n).pairE s5 (some (false, 0))
      (some (true, 0))).isSome = true := hEv6
  rcases Option.isSome_iff_exists.mp hp6 with ⟨s6, hs6⟩
  -- one turn from a semiclassical state
  have hW : WithinD (goGame n) (sgoGame n) (rhoSGo n) 1 s6 :=
    WithinD.step (WithinD.base hsc5) hs6
  have hFA := hFW s6 hW
  -- the shape of the new state
  have hs6' : sgoEv n s5 (some 0) (some 0) = some s6 := hs6
  rcases sgoEv_cases hs6' with ⟨-, -, -, hcase⟩
  rcases hcase with ⟨h00, -, -⟩ | ⟨-, bs, hse, hs6e⟩
  · cases h00
  · subst hs6e
    have hiff := hFA.2 (some (false, 1))
    -- every branch is empty at A2
    have hall : ∀ a, rhoSGo n (⟨resolveTurn s5.disp s5.next (some 0)
        (some 0), s5.next + 1, bs.filter (compatibleB n
          (resolveTurn s5.disp s5.next (some 0) (some 0))), false⟩
        : SGoState n) a →
        Interface0 (goGame n) a (some (false, 1)) := by
      intro a ha
      rcases ha with ⟨e, he, hae⟩
      have hae' : a = PState.live e false false := hae
      rw [hae', interface0_live]
      refine Or.inr ⟨false, 1, rfl, (wb hn).2.1, ?_⟩
      have hebs : e ∈ bs := (List.mem_filter.mp he).1
      rcases simEv_mem hse hebs with ⟨b, hb, l, hl, hel⟩
      have hbd : b = witD5 (n := n) := (hmemb5 b).mp hb
      subst hbd
      rw [wit_serialP hn] at hl
      cases hl
      exact wit_branch_occ1 hn hel
    have hav := hiff.mpr hall
    rcases hav.2 with h | ⟨w, i, hm, -, hocc⟩
    · cases h
    · cases hm
      have hd6 : occD (resolveTurn s5.disp s5.next (some 0) (some 0)) 1
          = true :=
        wit_display_idle hn s5.disp s5.next hInv5.wfdD hInv5.next_pos
          hdisp5 hInv5.stamps
      rw [hd6] at hocc
      exact Bool.noConfusion hocc

end SgoWit
