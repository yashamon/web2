/- SgoSimple.lean — the main theorem, milestone 2f: the simplicity of SGo.
   With suicide legal and no Ko, the interface of any live Go state is
   the passes and the moves of either player to its empty
   intersections, and likewise the display-read interface of SGo. The
   all-black paint of the display's occupied set is a legally
   obtainable Go state with the same empty intersections: black plays
   the stones one at a time with White passing — nothing is ever
   captured (no white stones), and no placement suicides, because
   every component of a proper all-black position touches an empty
   intersection (the grid is connected). -/
import SgoFaith

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv SgoOK SgoBridge SgoNat SgoSemi SgoFaith

namespace SgoSimple

variable {n : Nat}

/-! ### Grid coordinates and connectivity -/

theorem cell_bound {x y : Nat} (hx : x < n) (hy : y < n) :
    x*n + y < n*n := by
  have h2 : (x+1)*n ≤ n*n := Nat.mul_le_mul_right n hx
  have h3 : (x+1)*n = x*n + n := Nat.succ_mul x n
  omega

theorem coord_div {x y : Nat} (hn0 : 0 < n) (hy : y < n) :
    (x*n + y) / n = x := by
  rw [Nat.add_comm]
  rw [Nat.add_mul_div_right y x hn0]
  rw [Nat.div_eq_of_lt hy]
  exact Nat.zero_add x

theorem coord_mod {x y : Nat} (hy : y < n) :
    (x*n + y) % n = y := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hy

theorem adjI_step_y {x y : Nat} (hn0 : 0 < n) (_hx : x < n)
    (hy1 : y + 1 < n) : adjI n (x*n + y) (x*n + (y+1)) = true := by
  simp only [adjI]
  rw [coord_div hn0 (by omega), coord_mod (by omega : y < n),
    coord_div hn0 hy1, coord_mod hy1]
  simp

theorem adjI_step_x {x y : Nat} (hn0 : 0 < n) (_hx1 : x + 1 < n)
    (hy : y < n) : adjI n (x*n + y) ((x+1)*n + y) = true := by
  simp only [adjI]
  rw [coord_div hn0 hy, coord_mod hy, coord_div hn0 hy, coord_mod hy]
  simp

/-- The board's adjacency graph is connected: an adjacency-closed
    predicate holding somewhere holds everywhere. -/
theorem grid_connected (hn0 : 0 < n) (P : Nat → Prop)
    (hcl : ∀ u v, u < n*n → v < n*n → P u → adjI n u v = true → P v)
    {z0 : Nat} (hz0 : z0 < n*n) (hP0 : P z0) :
    ∀ w, w < n*n → P w := by
  -- coordinate form of the closure steps
  have hupy : ∀ x y, x < n → y + 1 < n → P (x*n + y) → P (x*n + (y+1)) := by
    intro x y hx hy1 hp
    exact hcl _ _ (cell_bound hx (by omega)) (cell_bound hx hy1) hp
      (adjI_step_y hn0 hx hy1)
  have hdny : ∀ x y, x < n → y + 1 < n → P (x*n + (y+1)) → P (x*n + y) := by
    intro x y hx hy1 hp
    exact hcl _ _ (cell_bound hx hy1) (cell_bound hx (by omega)) hp
      (adjI_symm (adjI_step_y hn0 hx hy1))
  have hupx : ∀ x y, x + 1 < n → y < n → P (x*n + y) → P ((x+1)*n + y) := by
    intro x y hx1 hy hp
    exact hcl _ _ (cell_bound (by omega) hy) (cell_bound hx1 hy) hp
      (adjI_step_x hn0 hx1 hy)
  have hdnx : ∀ x y, x + 1 < n → y < n → P ((x+1)*n + y) → P (x*n + y) := by
    intro x y hx1 hy hp
    exact hcl _ _ (cell_bound hx1 hy) (cell_bound (by omega) hy) hp
      (adjI_symm (adjI_step_x hn0 hx1 hy))
  -- walk a column down to row 0
  have hto0y : ∀ x y, x < n → y < n → P (x*n + y) → P (x*n + 0) := by
    intro x y hx
    induction y with
    | zero => intro _ hp; exact hp
    | succ y ih =>
      intro hy1 hp
      exact ih (by omega) (hdny x y hx hy1 hp)
  -- walk a column up from row 0
  have hfrom0y : ∀ x y, x < n → y < n → P (x*n + 0) → P (x*n + y) := by
    intro x y hx
    induction y with
    | zero => intro _ hp; exact hp
    | succ y ih =>
      intro hy1 hp
      exact hupy x y hx hy1 (ih (by omega) hp)
  -- walk row 0 down to column 0
  have hto0x : ∀ x, x < n → P (x*n + 0) → P (0*n + 0) := by
    intro x
    induction x with
    | zero => intro _ hp; exact hp
    | succ x ih =>
      intro hx1 hp
      exact ih (by omega) (hdnx x 0 hx1 hn0 hp)
  -- walk row 0 up from column 0
  have hfrom0x : ∀ x, x < n → P (0*n + 0) → P (x*n + 0) := by
    intro x
    induction x with
    | zero => intro _ hp; exact hp
    | succ x ih =>
      intro hx1 hp
      exact hupx x 0 hx1 hn0 (ih (by omega) hp)
  -- assemble
  intro w hw
  have hx0 : z0 / n < n := (Nat.div_lt_iff_lt_mul hn0).mpr hz0
  have hy0 : z0 % n < n := Nat.mod_lt z0 hn0
  have hz0e : z0 = (z0 / n)*n + z0 % n := by
    have h := Nat.div_add_mod z0 n
    rw [Nat.mul_comm] at h
    omega
  have hwx : w / n < n := (Nat.div_lt_iff_lt_mul hn0).mpr hw
  have hwy : w % n < n := Nat.mod_lt w hn0
  have hwe : w = (w / n)*n + w % n := by
    have h := Nat.div_add_mod w n
    rw [Nat.mul_comm] at h
    omega
  have h1 : P ((z0 / n)*n + z0 % n) := hz0e ▸ hP0
  have h2 : P ((z0 / n)*n + 0) := hto0y _ _ hx0 hy0 h1
  have h3 : P (0*n + 0) := hto0x _ hx0 h2
  have h4 : P ((w / n)*n + 0) := hfrom0x _ hwx h3
  have h5 : P ((w / n)*n + w % n) := hfrom0y _ _ hwx hwy h4
  rw [hwe]
  exact h5

/-! ### The all-black paint -/

/-- The all-black diagram on a set of intersections. -/
def blackD : List Nat → Display n
  | [] => emptyD n
  | z :: S => placedN n (blackD S) .b z

theorem blackD_wfd (S : List Nat) : WFD (blackD (n := n) S) := by
  induction S with
  | nil => exact emptyD_wfd
  | cons z S ih => exact WFD_placedN _ .b z ih

theorem blackD_kind (S : List Nat) (hb : ∀ z, z ∈ S → z < n*n)
    (w : Nat) :
    kindAt (blackD (n := n) S) w
      = if w ∈ S then some .b else none := by
  induction S with
  | nil =>
    rw [if_neg (List.not_mem_nil w)]
    show kindAt (emptyD n) w = none
    unfold kindAt
    rw [emptyD_get w]
    rfl
  | cons z S ih =>
    by_cases hw : w = z
    · subst hw
      rw [if_pos (List.mem_cons_self w S)]
      exact kindAt_placedN_self _ .b w (blackD_wfd S)
        (hb w (List.mem_cons_self w S))
    · show kindAt (placedN n (blackD S) .b z) w = _
      rw [kindAt_placedN_ne _ .b z w hw,
        ih (fun u hu => hb u (List.mem_cons_of_mem z hu))]
      by_cases hwS : w ∈ S
      · rw [if_pos hwS, if_pos (List.mem_cons_of_mem z hwS)]
      · rw [if_neg hwS, if_neg (by
          intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact hw h
          · exact hwS h)]

theorem blackD_occ (S : List Nat) (hb : ∀ z, z ∈ S → z < n*n)
    (w : Nat) :
    occD (blackD (n := n) S) w = true ↔ w ∈ S := by
  have hk := blackD_kind S hb w
  by_cases hwS : w ∈ S
  · rw [if_pos hwS] at hk
    exact ⟨fun _ => hwS, fun _ => occD_of_kind hk⟩
  · rw [if_neg hwS] at hk
    constructor
    · intro hocc
      exfalso
      unfold occD at hocc
      unfold kindAt at hk
      cases hg : (blackD (n := n) S).get w with
      | none => rw [hg] at hocc; cases hocc
      | some cell => rw [hg] at hk; cases hk
    · intro h
      exact absurd h hwS

/-- Every component of a proper all-black position has a liberty. -/
theorem allblack_liberty (hn0 : 0 < n) (S : List Nat)
    (hb : ∀ z, z ∈ S → z < n*n)
    (hproper : ∃ e, e < n*n ∧ ¬ e ∈ S)
    (z : Nat) (hz : z ∈ S) :
    noLibD (blackD (n := n) S) (componentD (blackD (n := n) S) z)
      = false := by
  have hkz : kindAt (blackD (n := n) S) z = some .b := by
    rw [blackD_kind S hb z, if_pos hz]
  cases hnl : noLibD (blackD (n := n) S)
      (componentD (blackD (n := n) S) z) with
  | false => rfl
  | true =>
    exfalso
    have hclosed : ∀ u v, u < n*n → v < n*n →
        u ∈ componentD (blackD (n := n) S) z → adjI n u v = true →
        v ∈ componentD (blackD (n := n) S) z := by
      intro u v hu hv huT hadj
      cases hocc : occD (blackD (n := n) S) v with
      | false =>
        exfalso
        have hlib : noLibD (blackD (n := n) S)
            (componentD (blackD (n := n) S) z) = false :=
          (noLibD_eq_false_iff _ _).mpr
            ⟨v, List.mem_range.mpr hv, hocc, u, huT, adjI_symm hadj⟩
        rw [hnl] at hlib
        exact Bool.noConfusion hlib
      | true =>
        have hkv : kindAt (blackD (n := n) S) v = some .b := by
          have hvS : v ∈ S := (blackD_occ S hb v).mp hocc
          rw [blackD_kind S hb v, if_pos hvS]
        exact componentD_maximal _ z .b hkz v (List.mem_range.mpr hv)
          hkv u huT (adjI_symm hadj)
    rcases hproper with ⟨e, heb, heS⟩
    have hzb : z < n*n := hb z hz
    have heT : e ∈ componentD (blackD (n := n) S) z :=
      grid_connected hn0 (· ∈ componentD (blackD (n := n) S) z)
        hclosed hzb (componentD_mem_self _ z .b hkz) e heb
    have hke := componentD_kind _ z .b hkz e heT
    rw [blackD_kind S hb e, if_neg heS] at hke
    cases hke

/-- The all-black paint is a defined, capture-free, suicide-free
    classical move at each stone. -/
theorem blackD_move (hn0 : 0 < n) (z : Nat) (S : List Nat)
    (hb : ∀ u, u ∈ (z :: S) → u < n*n) (hzS : ¬ z ∈ S)
    (hproper : ∃ e, e < n*n ∧ ¬ e ∈ (z :: S)) :
    goMoveN n (blackD S) .b z = some (blackD (z :: S)) := by
  have hbS : ∀ u, u ∈ S → u < n*n :=
    fun u hu => hb u (List.mem_cons_of_mem z hu)
  have hemp : occD (blackD (n := n) S) z = false := by
    cases hocc : occD (blackD (n := n) S) z with
    | false => rfl
    | true => exact absurd ((blackD_occ S hbS z).mp hocc) hzS
  -- no white anywhere: nothing is captured
  have hdead : deadOppN n (blackD S) .b z = [] := by
    rw [show deadOppN n (blackD S) .b z
      = (allIdx n).filter (fun p =>
          kindAt (placedN n (blackD S) .b z) p == some DKind.b.opp &&
          noLibD (placedN n (blackD S) .b z)
            (componentD (placedN n (blackD S) .b z) p)) from rfl]
    rw [List.filter_eq_nil_iff]
    intro p hp hcontra
    rw [Bool.and_eq_true] at hcontra
    have hkp := beq_iff_eq.mp hcontra.1
    have hkp' : kindAt (blackD (n := n) (z :: S)) p = some .w := hkp
    rw [blackD_kind (z :: S) hb p] at hkp'
    by_cases hpS : p ∈ z :: S
    · rw [if_pos hpS] at hkp'
      cases hkp'
    · rw [if_neg hpS] at hkp'
      cases hkp'
  have hAC := afterCapN_nocap_get (blackD S) .b z (blackD_wfd S) hdead
  -- no suicide: the placed component has a liberty
  have hsui : suicideN n (blackD S) .b z = false := by
    have hlib := allblack_liberty hn0 (z :: S) hb hproper z
      (List.mem_cons_self z S)
    show noLibD (afterCapN n (blackD S) .b z)
      (componentD (afterCapN n (blackD S) .b z) z) = false
    have hocceq : ∀ w, occD (afterCapN n (blackD S) .b z) w
        = occD (blackD (n := n) (z :: S)) w := by
      intro w
      unfold occD
      rw [hAC w]
      rfl
    have hkindeq : ∀ w, kindAt (afterCapN n (blackD S) .b z) w
        = kindAt (blackD (n := n) (z :: S)) w := by
      intro w
      unfold kindAt
      rw [hAC w]
      rfl
    have hkzAC : kindAt (afterCapN n (blackD S) .b z) z = some .b := by
      rw [hkindeq z, blackD_kind (z :: S) hb z,
        if_pos (List.mem_cons_self z S)]
    have hkzB : kindAt (blackD (n := n) (z :: S)) z = some .b := by
      rw [blackD_kind (z :: S) hb z, if_pos (List.mem_cons_self z S)]
    have hcompeq : ∀ q, q ∈ componentD (afterCapN n (blackD S) .b z) z
        ↔ q ∈ componentD (blackD (n := n) (z :: S)) z :=
      componentD_transport _ _ .b
        (fun w _ => by rw [hkindeq w]) z hkzAC hkzB
    rw [noLibD_occ_congr _ _ hocceq, noLibD_congr _ _ _ hcompeq]
    exact hlib
  -- assemble the move
  unfold goMoveN
  rw [hemp]
  simp only [Bool.false_eq_true, if_false, hsui, Option.some.injEq]
  -- afterCapN equals the painted display
  apply display_ext
  apply Array.ext
  · rw [show (afterCapN n (blackD S) .b z).cells.size = n*n from by
      unfold afterCapN
      simp [Array.size_map, Array.size_range]]
    rw [blackD_wfd (z :: S)]
  · intro i h1 h2
    have hib : i < n*n := by
      have : (afterCapN n (blackD S) .b z).cells.size = n*n := by
        unfold afterCapN
        simp [Array.size_map, Array.size_range]
      omega
    rw [← get_in_bounds _ i h1, ← get_in_bounds _ i h2, hAC i]
    rfl

/-- The all-black paint of a proper stone set is legally obtainable:
    Black plays the stones one at a time, White passing. -/
theorem reach_blackD (S : List Nat) (hnd : S.Nodup)
    (hb : ∀ z, z ∈ S → z < n*n)
    (hproper : ∃ e, e < n*n ∧ ¬ e ∈ S) :
    ∃ j, SeqReach (goGame n) (PState.live (blackD S) false j) := by
  have hn0 : 0 < n := by
    rcases hproper with ⟨e, heb, -⟩
    cases n with
    | zero => omega
    | succ m => omega
  induction S with
  | nil => exact ⟨false, SeqReach.init⟩
  | cons z S ih =>
    have hndS : S.Nodup := (List.nodup_cons.mp hnd).2
    have hzS : ¬ z ∈ S := (List.nodup_cons.mp hnd).1
    have hbS : ∀ u, u ∈ S → u < n*n :=
      fun u hu => hb u (List.mem_cons_of_mem z hu)
    have hproperS : ∃ e, e < n*n ∧ ¬ e ∈ S := by
      rcases hproper with ⟨e, heb, heS⟩
      exact ⟨e, heb, fun h => heS (List.mem_cons_of_mem z h)⟩
    rcases ih hndS hbS hproperS with ⟨j', hreach'⟩
    have hz : z < n*n := hb z (List.mem_cons_self z S)
    have hmv := blackD_move hn0 z S hb hzS hproper
    have hstep1 : sE (goGame n) (.live (blackD S) false j')
        (some (false, z)) = some (.live (blackD (z :: S)) true false) := by
      rw [sE_black_at0, goMvAct_b (blackD S) hz, hmv]
      rfl
    have hstep2 : sE (goGame n) (.live (blackD (z :: S)) true false)
        goMv.pass = some (.live (blackD (z :: S)) false true) := by
      rw [sE_pass_j0]
      rfl
    exact ⟨true, SeqReach.step (SeqReach.step hreach' hstep1) hstep2⟩

/-- Filtering preserves distinctness. -/
theorem nodup_filter (p : Nat → Bool) :
    ∀ (l : List Nat), l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a l ih =>
    intro h
    rcases List.nodup_cons.mp h with ⟨ha, hl⟩
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hl⟩
      intro hmem
      exact ha (List.mem_filter.mp hmem).1
    · rw [List.filter_cons_of_neg hp]
      exact ih hl

/-- A none cell is unoccupied. -/
theorem occ_of_get_none {D : Display n} {i : Nat}
    (h : D.get i = none) : occD D i = false := by
  unfold occD
  rw [h]
  rfl

/-- def_simplesymmetrization for SGo: the all-black paint of the
    display realizes the interface. -/
theorem sgo_isSimple : IsSimple (goGame n) (sgoGame n) := by
  intro s hr hnf hex
  have hInv := reach_inv hr
  have hfin : s.final = false := by
    cases hfc : s.final
    · rfl
    · exact absurd hfc hnf
  -- the occupied set of the display
  have hbS : ∀ z, z ∈ (allIdx n).filter (fun u => occD s.disp u) →
      z < n*n :=
    fun z hz => List.mem_range.mp (List.mem_filter.mp hz).1
  have hnd : ((allIdx n).filter (fun u => occD s.disp u)).Nodup :=
    nodup_filter _ _ (List.nodup_range (n*n))
  have hproper : ∃ e, e < n*n ∧
      ¬ e ∈ (allIdx n).filter (fun u => occD s.disp u) := by
    rcases hex with ⟨m, hmp, hav⟩
    rcases hav.2 with h | ⟨w, i, hm, hi, hocc⟩
    · exact absurd h hmp
    · refine ⟨i, hi, ?_⟩
      intro hmem
      have := (List.mem_filter.mp hmem).2
      rw [hocc] at this
      cases this
  rcases reach_blackD ((allIdx n).filter (fun u => occD s.disp u))
    hnd hbS hproper with ⟨j, hreach⟩
  refine ⟨PState.live (blackD ((allIdx n).filter
    (fun u => occD s.disp u))) false j, hreach, ?_⟩
  have hocc : ∀ i, occD (blackD (n := n) ((allIdx n).filter
      (fun u => occD s.disp u))) i = occD s.disp i := by
    intro i
    by_cases hib : i < n*n
    · cases hd : occD s.disp i with
      | true =>
        have : i ∈ (allIdx n).filter (fun u => occD s.disp u) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hib, hd⟩
        cases hbl : occD (blackD (n := n) ((allIdx n).filter
            (fun u => occD s.disp u))) i with
        | true => rfl
        | false =>
          exfalso
          exact absurd ((blackD_occ _ hbS i).mpr this) (by rw [hbl]; exact Bool.noConfusion)
      | false =>
        cases hbl : occD (blackD (n := n) ((allIdx n).filter
            (fun u => occD s.disp u))) i with
        | false => rfl
        | true =>
          exfalso
          have := (blackD_occ _ hbS i).mp hbl
          have h2 := (List.mem_filter.mp this).2
          rw [hd] at h2
          cases h2
    · -- off the board: both unoccupied
      have h1 : (blackD (n := n) ((allIdx n).filter
          (fun u => occD s.disp u))).get i = none :=
        get_oob _ (blackD_wfd _) i hib
      have h2 : s.disp.get i = none := get_oob _ hInv.wfdD i hib
      rw [occ_of_get_none h1, occ_of_get_none h2]
  intro m
  rw [interface0_live]
  constructor
  · rintro (h | ⟨w, i, hm, hi, hocci⟩)
    · exact ⟨hfin, Or.inl h⟩
    · refine ⟨hfin, Or.inr ⟨w, i, hm, hi, ?_⟩⟩
      rw [← hocc i]
      exact hocci
  · intro hav
    rcases hav.2 with h | ⟨w, i, hm, hi, hocci⟩
    · exact Or.inl h
    · refine Or.inr ⟨w, i, hm, hi, ?_⟩
      rw [hocc i]
      exact hocci

end SgoSimple
