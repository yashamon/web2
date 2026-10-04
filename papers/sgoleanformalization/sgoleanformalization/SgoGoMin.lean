/- SgoGoMin.lean — Lemma lem_gominimal: Go is minimal, distinct legally
   obtainable diagrams are not bisimilar.

   The printed argument, in the simplified form adopted for the proof
   (Black fills only): bisimilar diagrams have the same occupancy, a
   move being legal exactly at an empty intersection. So let D and D'
   agree in occupancy and differ in color at i, black in D and white in
   D'. Let K be the black component of i in D and j a liberty of K. As
   long as K has a liberty l ≠ j, Black fills l: the stone joins K, which
   keeps the liberty j, so it stands, and K gains a stone — at most n²
   times. The same moves are legal in D' and keep the occupancies equal
   (by bisimilarity), i staying white there. When the liberties of K are
   {j}, White plays j: in D the component K is captured and the stone at
   j stands on the freed intersections, so i is empty and j white; in D'
   the stone at j stands, i staying white, or its component suicides
   with j. Either way the occupancies differ — at i or at j — against
   bisimilarity.

   Statement audit. `go_minimal` is `Minimal (goGame n)` for every n,
   the Go of SgoInst (displays, classical moves `goMoveN`: placement at
   an empty intersection, go_captures, go_suicide, go_closure). The
   legally obtainable displays are well-formed, classical (no q-stone)
   and legal with all stamps zero (`goOb`); two such displays are equal
   exactly when every intersection carries the same stone. -/
import SgoBisim
import SgoBisimThm
import Infra6
import SgoInv

namespace SgoGoMin

open SgoGo SgoDisplay SgoGames SgoSerial SgoInv

attribute [local instance] Classical.propDecidable

variable {n : Nat}

/-! ### Well-formedness, classicality, legality, stamps -/

theorem wfd_goMoveN (d : Display n) (c : DKind) (i : Nat) (r : Display n)
    (hr : goMoveN n d c i = some r) : WFD r := by
  rw [goMoveN_result d c i r hr]
  split
  · show (erasedN n d c i).cells.size = n*n
    unfold erasedN
    rw [Array.size_map, Array.size_range]
  · show (afterCapN n d c i).cells.size = n*n
    unfold afterCapN
    rw [Array.size_map, Array.size_range]

/-- All stamps zero. -/
def StampsZero (D : Display n) : Prop :=
  ∀ p, D.get p = none ∨ ∃ k, D.get p = some (k, 0)

theorem stampsZero_goMoveN (d : Display n) (c : DKind) (i : Nat) (r : Display n)
    (hd : StampsZero d) (hr : goMoveN n d c i = some r) : StampsZero r := by
  intro p
  rcases goMoveN_get d c i r hr p with h | h
  · exact Or.inl h
  · rw [h]
    by_cases hpi : p = i
    · subst hpi
      by_cases hlt : p < d.cells.size
      · right
        refine ⟨c, ?_⟩
        unfold placedN
        exact get_set_self d p _ hlt
      · have hnoop : (placedN n d c p).get p = d.get p := by
          unfold placedN Display.set Display.get Array.setD Array.setIfInBounds
          rw [dif_neg hlt]
        rw [hnoop]
        exact hd p
    · unfold placedN
      rw [get_set_ne d i p _ hpi]
      exact hd p

theorem stampsZero_emptyD : StampsZero (emptyD n) := by
  intro p
  exact Or.inl (emptyD_get p)

theorem classical_emptyD : IsClassical (emptyD n) := by
  intro p h
  unfold kindAt at h
  rw [emptyD_get] at h
  exact Option.noConfusion h

theorem legal_emptyD : IsLegal (emptyD n) := by
  intro p h
  unfold occD at h
  rw [emptyD_get] at h
  exact Bool.noConfusion h

/-- The Go action, read. -/
theorem goMvAct_unfold (d : Display n) (w : Bool) (i : Nat) :
    goMvAct n d (some (w, i)) =
      (if i < n*n then goMoveN n d (if w then .w else .b) i else none) := rfl

theorem goMvAct_eq (d : Display n) (w : Bool) (i : Nat) (hi : i < n*n) :
    goMvAct n d (some (w, i)) = goMoveN n d (if w then .w else .b) i := by
  rw [goMvAct_unfold, if_pos hi]

theorem goMvAct_eq_oob (d : Display n) (w : Bool) (i : Nat) (hi : ¬i < n*n) :
    goMvAct n d (some (w, i)) = none := by
  rw [goMvAct_unfold, if_neg hi]

theorem goMoveN_isSome_iff (d : Display n) (c : DKind) (i : Nat) :
    (goMoveN n d c i).isSome = true ↔ occD d i = false := by
  unfold goMoveN
  cases h : occD d i
  · simp
  · simp

/-- The invariant of the legally obtainable displays. -/
def GoOb (D : Display n) : Prop :=
  WFD D ∧ IsClassical D ∧ IsLegal D ∧ StampsZero D

theorem goOb_step (d : Display n) (c : DKind) (i : Nat) (r : Display n)
    (hd : GoOb d) (hi : i < n*n) (hc : c ≠ .r) (hr : goMoveN n d c i = some r) :
    GoOb r :=
  ⟨wfd_goMoveN d c i r hr, goMoveN_classical d c i r hd.2.1 hc hr,
   goMoveN_legal d c i r hd.1 hi hc hd.2.1 hd.2.2.1 hr,
   stampsZero_goMoveN d c i r hd.2.2.2 hr⟩

/-- A step of the evolution changes the core only through the action. -/
theorem coreOf_sE_step {Mv : Moves} (G : SeqGame Mv) {s s' : G.S} {m : Mv.M}
    (h : sE G s m = some s') :
    s'.coreOf = s.coreOf ∨ (m ≠ Mv.pass ∧ G.mv s.coreOf m = some s'.coreOf) := by
  cases s with
  | done c g => exact absurd h (fun h => Option.noConfusion h)
  | live c g j =>
    by_cases he : G.ended c
    · rw [prop_finalnomove G (s := PState.live c g j) he m] at h
      exact absurd h (fun h => Option.noConfusion h)
    · by_cases hm : m = Mv.pass
      · subst hm
        rw [sE_pass G c g j he] at h
        rw [← Option.some_inj.mp h]
        left
        cases j <;> rfl
      · rw [sE_nonpass G c g j m hm he] at h
        by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
        · rw [if_pos hg] at h
          obtain ⟨c', hmv, hc'⟩ := Option.map_eq_some'.mp h
          right
          refine ⟨hm, ?_⟩
          rw [← hc']
          exact hmv
        · rw [if_neg hg] at h
          exact absurd h (fun h => Option.noConfusion h)

/-- Legally obtainable cores of Go satisfy the invariant. -/
theorem goOb_of_seqReach {s : (goGame n).S} (h : SeqReach (goGame n) s) : GoOb s.coreOf := by
  induction h with
  | init => exact ⟨emptyD_wfd, classical_emptyD, legal_emptyD, stampsZero_emptyD⟩
  | @step s s' m _ hE ih =>
    rcases coreOf_sE_step (goGame n) hE with h | ⟨hm, hmv⟩
    · rw [h]; exact ih
    · cases m with
      | none => exact absurd rfl hm
      | some wi =>
        obtain ⟨w, i⟩ := wi
        by_cases hi : i < n*n
        · have hmv' : goMoveN n s.coreOf (if w then .w else .b) i = some s'.coreOf := by
            rw [← goMvAct_eq s.coreOf w i hi]; exact hmv
          exact goOb_step _ _ i _ ih hi (by cases w <;> simp) hmv'
        · change goMvAct n s.coreOf (some (w, i)) = some s'.coreOf at hmv
          rw [goMvAct_eq_oob s.coreOf w i hi] at hmv
          exact absurd hmv (fun h => Option.noConfusion h)

theorem goOb (d : Display n) (h : CoreOb (goGame n) d) : GoOb d := by
  obtain ⟨g, hg⟩ := h
  exact goOb_of_seqReach hg

/-! ### Liberties -/

/-- q is a liberty of the set K in D. -/
def IsLib (D : Display n) (K : List Nat) (q : Nat) : Prop :=
  q < n*n ∧ occD D q = false ∧ ∃ r, r ∈ K ∧ adjI n q r = true

theorem exists_lib (D : Display n) (hleg : IsLegal D) (i : Nat) (hocc : occD D i = true) :
    ∃ j, IsLib D (componentD D i) j := by
  have h := hleg i hocc
  obtain ⟨q, hq, hqo, r, hr, hadj⟩ := (noLibD_eq_false_iff D _).mp h
  exact ⟨q, List.mem_range.mp hq, hqo, r, hr, hadj⟩

theorem lib_not_mem (D : Display n) (i : Nat) (k : DKind) (hk : kindAt D i = some k)
    {q : Nat} (hq : IsLib D (componentD D i) q) : q ∉ componentD D i := by
  intro hmem
  have := componentD_kind D i k hk q hmem
  rw [kind_none_of_unocc hq.2.1] at this
  exact Option.noConfusion this

/-- Black cells of D are black in the placed diagram of a move elsewhere
    and in its capture stage (captures remove the opposite color). -/
theorem black_agree_afterCapN (D : Display n) (l : Nat) (hl : occD D l = false)
    (z : Nat) (hz : z ∈ allIdx n) :
    kindAt D z = some .b → kindAt (afterCapN n D .b l) z = some .b := by
  intro hzb
  have hzl : z ≠ l := by
    intro h; subst h
    rw [kind_none_of_unocc hl] at hzb
    exact Option.noConfusion hzb
  have hz' : z < n*n := List.mem_range.mp hz
  rw [kindAt_afterCapN D .b l z hz']
  have hnd : ¬(deadOppN n D .b l).contains z = true := by
    intro hc
    rcases (mem_deadOppN_iff D .b l z).mp (List.contains_iff_mem.mp hc) with ⟨-, hzk, -⟩
    rw [kindAt_placedN_ne D .b l z hzl, hzb] at hzk
    exact DKind.noConfusion (Option.some.inj hzk)
  rw [if_neg hnd, kindAt_placedN_ne D .b l z hzl]
  exact hzb

/-! ### The fill step -/

/-- Black fills a liberty l ≠ j of the black component K of i, where j
    is another liberty of K: the stone stands and joins K, j stays
    empty, i stays black. -/
theorem fill_step (D : Display n) (hD : GoOb D) (i : Nat) (hi : i < n*n)
    (hib : kindAt D i = some .b) (j : Nat) (hj : IsLib D (componentD D i) j)
    (l : Nat) (hl : IsLib D (componentD D i) l) (hlj : l ≠ j) :
    ∃ E, goMoveN n D .b l = some E ∧ kindAt E i = some .b ∧ occD E j = false ∧
      (∀ q, q ∈ componentD D i → q ∈ componentD E i) ∧ l ∈ componentD E i := by
  have hwf : WFD D := hD.1
  have hib' : i ∈ allIdx n := List.mem_range.mpr hi
  obtain ⟨hln, hlo, rl, hrl, hadjl⟩ := hl
  obtain ⟨hjn, hjo, rj, hrj, hadjj⟩ := hj
  have hil : i ≠ l := by
    intro h; subst h
    rw [kind_none_of_unocc hlo] at hib
    exact Option.noConfusion hib
  -- the capture stage, where black cells of D persist and l is black
  let A := afterCapN n D .b l
  have hagree : ∀ z, z ∈ allIdx n → kindAt D z = some .b → kindAt A z = some .b :=
    black_agree_afterCapN D l hlo
  have hAl : kindAt A l = some .b := kindAt_afterCapN_self D .b l hwf hln (by simp)
  have hAi : kindAt A i = some .b := hagree i hib' hib
  -- K in D lies in the black component of i in A
  have hKA : ∀ q, q ∈ componentD D i → q ∈ componentD A i := by
    intro q hq
    rw [componentD_mem_iff D i .b hib q] at hq
    rw [componentD_mem_iff A i .b hAi q]
    exact ConnK_transport D A .b hagree hq
  -- l joins it
  have hlA : l ∈ componentD A i :=
    componentD_maximal A i .b hAi l (List.mem_range.mpr hln) hAl rl (hKA rl hrl) hadjl
  -- so the placed stone's component, read at l, is the component of i
  have hcomp_eq : ∀ q, q ∈ componentD A l ↔ q ∈ componentD A i :=
    componentD_eq_mem A i l .b hib' hAi hlA
  -- j is empty in A and adjacent to it: no suicide
  have hjl : j ≠ l := fun h => hlj h.symm
  have hjA : occD A j = false := by
    rw [occD_afterCapN D .b l j hjn]
    split
    · rfl
    · rw [occD_placedN_ne D .b l j hjl]; exact hjo
  have hnosui : suicideN n D .b l = false := by
    show noLibD A (componentD A l) = false
    rw [noLibD_eq_false_iff]
    refine ⟨j, List.mem_range.mpr hjn, hjA, rj, (hcomp_eq rj).mpr (hKA rj hrj), hadjj⟩
  -- the move is defined and its output is A
  have hE : goMoveN n D .b l = some A := by
    unfold goMoveN
    rw [if_neg (by rw [hlo]; exact Bool.false_ne_true), hnosui]
    rfl
  refine ⟨A, hE, hAi, hjA, hKA, hlA⟩

/-! ### The final move -/

/-- When the liberties of the black component K of i are exactly {j},
    White at j captures K and stands: i empty, j occupied. -/
theorem final_black (D : Display n) (hD : GoOb D) (i : Nat) (hi : i < n*n)
    (hib : kindAt D i = some .b) (j : Nat) (hj : IsLib D (componentD D i) j)
    (hsole : ∀ q, IsLib D (componentD D i) q → q = j) :
    ∃ F, goMoveN n D .w j = some F ∧ occD F i = false ∧ occD F j = true := by
  have hwf : WFD D := hD.1
  have hib' : i ∈ allIdx n := List.mem_range.mpr hi
  obtain ⟨hjn, hjo, rj, hrj, hadjj⟩ := hj
  have hij : i ≠ j := by
    intro h; subst h
    rw [kind_none_of_unocc hjo] at hib
    exact Option.noConfusion hib
  let P := placedN n D .w j
  -- black cells agree between D and P
  have hagree : ∀ z, z ∈ allIdx n → (kindAt D z = some .b ↔ kindAt P z = some .b) := by
    intro z _
    by_cases hzj : z = j
    · subst hzj
      rw [kind_none_of_unocc hjo, kindAt_placedN_self D .w z hwf hjn]
      exact ⟨fun h => Option.noConfusion h, fun h => DKind.noConfusion (Option.some.inj h)⟩
    · rw [kindAt_placedN_ne D .w j z hzj]
  have hPi : kindAt P i = some .b := (hagree i hib').mp hib
  have hcompP : ∀ q, q ∈ componentD D i ↔ q ∈ componentD P i :=
    componentD_transport D P .b hagree i hib hPi
  -- K has no liberty in P
  have hnl : noLibD P (componentD P i) = true := by
    cases h : noLibD P (componentD P i)
    · exfalso
      obtain ⟨q, hq, hqo, r, hr, hadj⟩ := (noLibD_eq_false_iff P _).mp h
      have hqj : q ≠ j := by
        intro hqj; subst hqj
        have : occD P q = true := occD_of_kind (kindAt_placedN_self D .w q hwf hjn)
        rw [this] at hqo
        exact Bool.noConfusion hqo
      have hqD : occD D q = false := by
        rw [occD_placedN_ne D .w j q hqj] at hqo; exact hqo
      exact hqj (hsole q ⟨List.mem_range.mp hq, hqD, r, (hcompP r).mpr hr, hadj⟩)
    · rfl
  -- i is dead
  have hidead : i ∈ deadOppN n D .w j :=
    (mem_deadOppN_iff D .w j i).mpr ⟨hib', hPi, hnl⟩
  -- rj is dead too (same component)
  have hrjP : rj ∈ componentD P i := (hcompP rj).mp hrj
  have hrjdead : rj ∈ deadOppN n D .w j := deadOppN_component_closed D .w j i rj hidead hrjP
  have hrjn : rj < n*n := List.mem_range.mp (componentD_board hib' hib hrj)
  -- the move is defined; its output
  have hdef : ∃ F, goMoveN n D .w j = some F := by
    unfold goMoveN
    rw [if_neg (by rw [hjo]; exact Bool.false_ne_true)]
    exact ⟨_, rfl⟩
  obtain ⟨F, hF⟩ := hdef
  refine ⟨F, hF, occD_output_dead D .w j F hF i hi hidead, ?_⟩
  -- j stands: its capture-stage component has the freed liberty rj
  let A := afterCapN n D .w j
  have hAj : kindAt A j = some .w := kindAt_afterCapN_self D .w j hwf hjn (by simp)
  have hrjA : occD A rj = false := by
    rw [occD_afterCapN D .w j rj hrjn, if_pos (List.contains_iff_mem.mpr hrjdead)]
  have hnosui : suicideN n D .w j = false := by
    show noLibD A (componentD A j) = false
    rw [noLibD_eq_false_iff]
    exact ⟨rj, List.mem_range.mpr hrjn, hrjA, j, componentD_mem_self A j .w hAj,
      adjI_symm hadjj⟩
  have hFA : F = A := by
    rw [goMoveN_result D .w j F hF, hnosui]
    rfl
  rw [hFA]
  exact occD_of_kind hAj

/-- A White move at j removes a white stone only with its own
    component, which contains j. -/
theorem final_white (D : Display n) (hD : GoOb D) (i : Nat) (hi : i < n*n)
    (hiw : kindAt D i = some .w) (j : Nat) (hjn : j < n*n) (hjo : occD D j = false) :
    ∃ F, goMoveN n D .w j = some F ∧ (occD F i = false → occD F j = false) := by
  have hwf : WFD D := hD.1
  have hij : i ≠ j := by
    intro h; subst h
    rw [kind_none_of_unocc hjo] at hiw
    exact Option.noConfusion hiw
  have hdef : ∃ F, goMoveN n D .w j = some F := by
    unfold goMoveN
    rw [if_neg (by rw [hjo]; exact Bool.false_ne_true)]
    exact ⟨_, rfl⟩
  obtain ⟨F, hF⟩ := hdef
  refine ⟨F, hF, ?_⟩
  intro hFi
  have hres := goMoveN_result D .w j F hF
  let A := afterCapN n D .w j
  have hAj : kindAt A j = some .w := kindAt_afterCapN_self D .w j hwf hjn (by simp)
  by_cases hsui : suicideN n D .w j = true
  · rw [if_pos hsui] at hres
    have hc : (ownCompN n D .w j).contains j = true :=
      List.contains_iff_mem.mpr (componentD_mem_self (afterCapN n D .w j) j .w hAj)
    rw [hres, occD_erasedN D .w j j hjn, if_pos hc]
  · exfalso
    rw [if_neg hsui] at hres
    rw [hres, occD_afterCapN D .w j i hi] at hFi
    have hnd : ¬(deadOppN n D .w j).contains i = true := by
      intro hc
      rcases (mem_deadOppN_iff D .w j i).mp (List.contains_iff_mem.mp hc) with ⟨-, hik, -⟩
      rw [kindAt_placedN_ne D .w j i hij, hiw] at hik
      exact DKind.noConfusion (Option.some.inj hik)
    rw [if_neg hnd, occD_placedN_ne D .w j i hij, occD_of_kind hiw] at hFi
    exact Bool.noConfusion hFi

/-! ### Bisimilar displays -/

theorem goMv_graded (w : Bool) (i : Nat) :
    goMv.deg0 (some (w, i)) ∨ goMv.deg1 (some (w, i)) := by
  cases w
  · exact Or.inl (Or.inr ⟨i, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem goMv_ne_pass (w : Bool) (i : Nat) : (some (w, i) : goMv.M) ≠ goMv.pass :=
  fun h => Option.noConfusion h

theorem optRelC_isSome {C C' : Type} (R : C → C' → Prop) {o : Option C} {o' : Option C'}
    (h : OptRelC R o o') : o.isSome = o'.isSome := by
  cases o <;> cases o'
  · rfl
  · exact False.elim h
  · exact False.elim h
  · rfl

/-- The bisimulation read on a colored move. -/
theorem bisim_act (d d' : Display n) (hb : Bisimilar (goGame n) d d') (w : Bool) (i : Nat)
    (hi : i < n*n) :
    OptRelC (Bisimilar (goGame n)) (goMoveN n d (if w then .w else .b) i)
      (goMoveN n d' (if w then .w else .b) i) := by
  have h := bisimilar_mv (goGame n) hb (some (w, i)) (goMv_ne_pass w i) (goMv_graded w i)
    (fun h => h)
  change OptRelC _ (goMvAct n d (some (w, i))) (goMvAct n d' (some (w, i))) at h
  rw [goMvAct_eq d w i hi, goMvAct_eq d' w i hi] at h
  exact h

theorem bisim_act_b (d d' : Display n) (hb : Bisimilar (goGame n) d d') (i : Nat)
    (hi : i < n*n) :
    OptRelC (Bisimilar (goGame n)) (goMoveN n d .b i) (goMoveN n d' .b i) :=
  bisim_act d d' hb false i hi

theorem bisim_act_w (d d' : Display n) (hb : Bisimilar (goGame n) d d') (i : Nat)
    (hi : i < n*n) :
    OptRelC (Bisimilar (goGame n)) (goMoveN n d .w i) (goMoveN n d' .w i) :=
  bisim_act d d' hb true i hi

/-- Bisimilar displays have the same occupancy: a move is legal exactly
    at an empty intersection. -/
theorem bisim_occ (d d' : Display n) (hb : Bisimilar (goGame n) d d') (i : Nat)
    (hi : i < n*n) : occD d i = occD d' i := by
  have h := optRelC_isSome _ (bisim_act_b d d' hb i hi)
  have e1 := goMoveN_isSome_iff d .b i
  have e2 := goMoveN_isSome_iff d' .b i
  cases h1 : occD d i <;> cases h2 : occD d' i
  · rfl
  · exfalso
    rw [h1] at e1; rw [h2] at e2
    have := e1.mpr rfl
    rw [h] at this
    exact Bool.noConfusion (e2.mp this)
  · exfalso
    rw [h1] at e1; rw [h2] at e2
    have := e2.mpr rfl
    rw [← h] at this
    exact Bool.noConfusion (e1.mp this)
  · rfl

theorem bisim_step_b (d d' E E' : Display n) (hb : Bisimilar (goGame n) d d') (l : Nat)
    (hl : l < n*n) (hE : goMoveN n d .b l = some E) (hE' : goMoveN n d' .b l = some E') :
    Bisimilar (goGame n) E E' := by
  have h := bisim_act_b d d' hb l hl
  rw [hE, hE'] at h
  exact h

theorem bisim_step_w (d d' E E' : Display n) (hb : Bisimilar (goGame n) d d') (l : Nat)
    (hl : l < n*n) (hE : goMoveN n d .w l = some E) (hE' : goMoveN n d' .w l = some E') :
    Bisimilar (goGame n) E E' := by
  have h := bisim_act_w d d' hb l hl
  rw [hE, hE'] at h
  exact h

theorem coreOb_step_b (d E : Display n) (hob : CoreOb (goGame n) d) (l : Nat) (hl : l < n*n)
    (hE : goMoveN n d .b l = some E) : CoreOb (goGame n) E :=
  coreOb_mv (goGame n) hob (goMv_graded false l) (goMv_ne_pass false l) (fun h => h)
    (by rw [show (goGame n).mv d (some (false, l)) = goMoveN n d .b l from goMvAct_eq d false l hl]
        exact hE)

theorem coreOb_step_w (d E : Display n) (hob : CoreOb (goGame n) d) (l : Nat) (hl : l < n*n)
    (hE : goMoveN n d .w l = some E) : CoreOb (goGame n) E :=
  coreOb_mv (goGame n) hob (goMv_graded true l) (goMv_ne_pass true l) (fun h => h)
    (by rw [show (goGame n).mv d (some (true, l)) = goMoveN n d .w l from goMvAct_eq d true l hl]
        exact hE)

/-! ### The separation -/

/-- The final move: the liberties of the black component of i in d are
    {j}; d' is bisimilar, with i white. White at j separates them. -/
theorem final_case (i : Nat) (hi : i < n*n) (j : Nat) (d d' : Display n)
    (hob : CoreOb (goGame n) d) (hob' : CoreOb (goGame n) d')
    (hb : Bisimilar (goGame n) d d') (hib : kindAt d i = some .b)
    (hiw : kindAt d' i = some .w) (hj : IsLib d (componentD d i) j)
    (hsole : ∀ q, IsLib d (componentD d i) q → q = j) : False := by
  obtain ⟨F, hF, hFi, hFj⟩ := final_black d (goOb d hob) i hi hib j hj hsole
  have hjn : j < n*n := hj.1
  have hjo' : occD d' j = false := by rw [← bisim_occ d d' hb j hjn]; exact hj.2.1
  obtain ⟨F', hF', hF'ij⟩ := final_white d' (goOb d' hob') i hi hiw j hjn hjo'
  have hbF : Bisimilar (goGame n) F F' := bisim_step_w d d' F F' hb j hjn hF hF'
  have h1 := bisim_occ F F' hbF i hi
  have h2 := bisim_occ F F' hbF j hjn
  rw [hFi] at h1
  rw [hFj, hF'ij h1.symm] at h2
  exact Bool.noConfusion h2

/-- The fill step, with the bisimilar partner. -/
theorem fill_case (i : Nat) (hi : i < n*n) (j : Nat) (d d' : Display n)
    (hob : CoreOb (goGame n) d) (hob' : CoreOb (goGame n) d')
    (hb : Bisimilar (goGame n) d d') (hib : kindAt d i = some .b)
    (hiw : kindAt d' i = some .w) (hj : IsLib d (componentD d i) j)
    (l : Nat) (hl : IsLib d (componentD d i) l) (hlj : l ≠ j) :
    ∃ E E', CoreOb (goGame n) E ∧ CoreOb (goGame n) E' ∧ Bisimilar (goGame n) E E' ∧
      kindAt E i = some .b ∧ kindAt E' i = some .w ∧ IsLib E (componentD E i) j ∧
      compMeasure (n*n) (componentD E i) < compMeasure (n*n) (componentD d i) := by
  obtain ⟨E, hE, hEi, hEj, hKE, hlE⟩ := fill_step d (goOb d hob) i hi hib j hj l hl hlj
  have hln : l < n*n := hl.1
  have hlo' : occD d' l = false := by rw [← bisim_occ d d' hb l hln]; exact hl.2.1
  obtain ⟨E', hE'⟩ : ∃ E', goMoveN n d' .b l = some E' := by
    have := (goMoveN_isSome_iff d' .b l).mpr hlo'
    cases h : goMoveN n d' .b l
    · rw [h] at this; exact Bool.noConfusion this
    · exact ⟨_, rfl⟩
  have hbE : Bisimilar (goGame n) E E' := bisim_step_b d d' E E' hb l hln hE hE'
  have hil : i ≠ l := by
    intro h; subst h
    rw [kind_none_of_unocc hl.2.1] at hib
    exact Option.noConfusion hib
  have hE'i : kindAt E' i = some .w := by
    have hocc : occD E' i = true := by
      rw [← bisim_occ E E' hbE i hi]
      exact occD_of_kind hEi
    rw [kindAt_standing d' .b l E' hE' i hocc, kindAt_placedN_ne d' .b l i hil]
    exact hiw
  obtain ⟨hjn, -, rj, hrj, hadjj⟩ := hj
  refine ⟨E, E', coreOb_step_b d E hob l hln hE, coreOb_step_b d' E' hob' l hln hE', hbE,
    hEi, hE'i, ⟨hjn, hEj, rj, hKE rj hrj, hadjj⟩, ?_⟩
  exact compMeasure_decrease (n*n) _ _ hKE l hln hlE (lib_not_mem d i .b hib hl)

/-- No bisimilar pair differs in color at i: by induction on the
    measure of the black component of i. -/
theorem no_bisim_diff (i : Nat) (hi : i < n*n) (j : Nat) :
    ∀ (bound : Nat) (d d' : Display n), compMeasure (n*n) (componentD d i) ≤ bound →
      CoreOb (goGame n) d → CoreOb (goGame n) d' → Bisimilar (goGame n) d d' →
      kindAt d i = some .b → kindAt d' i = some .w →
      IsLib d (componentD d i) j → False := by
  intro bound
  induction bound with
  | zero =>
    intro d d' hle _ _ _ hib _ hj
    have h0 : compMeasure (n*n) (componentD d i) = 0 := Nat.le_zero.mp hle
    have hjK : j ∈ componentD d i := compMeasure_zero_full (n*n) _ h0 j hj.1
    exact lib_not_mem d i .b hib hj hjK
  | succ b ih =>
    intro d d' hle hob hob' hb hib hiw hj
    by_cases hex : ∃ l, IsLib d (componentD d i) l ∧ l ≠ j
    · obtain ⟨l, hl, hlj⟩ := hex
      obtain ⟨E, E', hobE, hobE', hbE, hEi, hE'i, hjE, hlt⟩ :=
        fill_case i hi j d d' hob hob' hb hib hiw hj l hl hlj
      exact ih E E' (by omega) hobE hobE' hbE hEi hE'i hjE
    · exact final_case i hi j d d' hob hob' hb hib hiw hj
        (fun q hq => Classical.byContradiction fun hqj => hex ⟨q, hq, hqj⟩)

/-- Two displays of the invariant that carry the same stone at every
    intersection are equal. -/
theorem display_ext (d d' : Display n) (hD : GoOb d) (hD' : GoOb d')
    (h : ∀ k, k < n*n → d.get k = d'.get k) : d = d' := by
  cases d with
  | mk cells =>
    cases d' with
    | mk cells' =>
      have hsz : cells.size = cells'.size := by
        rw [show cells.size = n*n from hD.1, show cells'.size = n*n from hD'.1]
      congr 1
      apply Array.ext _ _ hsz
      intro k hk1 hk2
      have hk : k < n*n := by rw [← show cells.size = n*n from hD.1]; exact hk1
      have := h k hk
      unfold Display.get Array.getD at this
      rw [dif_pos hk1, dif_pos hk2] at this
      exact this

/-- Lemma lem_gominimal: Go is minimal. -/
theorem go_minimal : Minimal (goGame n) := by
  intro d d' hob hob' hb
  have hD := goOb d hob
  have hD' := goOb d' hob'
  apply Classical.byContradiction
  intro hne
  have hex : ∃ i, i < n*n ∧ d.get i ≠ d'.get i := by
    apply Classical.byContradiction
    intro hnex
    exact hne (display_ext d d' hD hD' fun k hk =>
      Classical.byContradiction fun hk' => hnex ⟨k, hk, hk'⟩)
  obtain ⟨i, hi, hdiff⟩ := hex
  have hocc := bisim_occ d d' hb i hi
  cases h1 : occD d i with
  | false =>
    apply hdiff
    have h2 : occD d' i = false := by rw [← hocc, h1]
    have e1 : d.get i = none := by
      cases hd : d.get i with
      | none => rfl
      | some _ => unfold occD at h1; rw [hd] at h1; exact Bool.noConfusion h1
    have e2 : d'.get i = none := by
      cases hd : d'.get i with
      | none => rfl
      | some _ => unfold occD at h2; rw [hd] at h2; exact Bool.noConfusion h2
    rw [e1, e2]
  | true =>
    have h2 : occD d' i = true := by rw [← hocc, h1]
    rcases hD.2.2.2 i with hz | ⟨k, hk⟩
    · unfold occD at h1; rw [hz] at h1; exact Bool.noConfusion h1
    rcases hD'.2.2.2 i with hz' | ⟨k', hk'⟩
    · unfold occD at h2; rw [hz'] at h2; exact Bool.noConfusion h2
    have hkind : kindAt d i = some k := by unfold kindAt; rw [hk]; rfl
    have hkind' : kindAt d' i = some k' := by unfold kindAt; rw [hk']; rfl
    have hkk : k ≠ k' := by
      intro h; subst h
      exact hdiff (by rw [hk, hk'])
    have hkr : k ≠ .r := fun h => hD.2.1 i (by rw [hkind, h])
    have hkr' : k' ≠ .r := fun h => hD'.2.1 i (by rw [hkind', h])
    -- the two colors
    have hcases : (k = .b ∧ k' = .w) ∨ (k = .w ∧ k' = .b) := by
      cases k <;> cases k' <;> first
        | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩
        | exact absurd rfl hkk | exact absurd rfl hkr | exact absurd rfl hkr'
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := exists_lib d hD.2.2.1 i h1
      exact no_bisim_diff i hi j (n*n) d d' (compMeasure_le _ _) hob hob' hb hkind hkind' hj
    · obtain ⟨j, hj⟩ := exists_lib d' hD'.2.2.1 i h2
      exact no_bisim_diff i hi j (n*n) d' d (compMeasure_le _ _) hob' hob
        (bisimilar_symm _ hb) hkind' hkind hj

/-- Theorem thm_simplesymetrization, the radius spectrum clause, with
    Go's minimality proved: every element of ℕ ⊔ {∞} lies in the radius
    spectrum of Go. -/
theorem go_radius_spectrum (hn : 5 ≤ n) (r : Option Nat) :
    InRadiusSpectrum (goGame n) r :=
  SgoThm.go_radius_spectrum_full hn go_minimal r


end SgoGoMin
