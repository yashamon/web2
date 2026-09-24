/- Infra5.lean — the per-move removal structure: a defined classical
   move empties whole components of its placed diagram, each trapped
   there (no liberties). The engine for Step 1's dichotomy. -/
import Infra
import Step0
open SgoDisplay

variable {n : Nat}

/-- Reading erasedN's occupancy on the board. -/
theorem occD_erasedN (A : Display n) (c : DKind) (i z : Nat)
    (hz : z < n*n) :
    occD (erasedN n A c i) z =
      if (ownCompN n A c i).contains z then false
      else occD (afterCapN n A c i) z := by
  unfold occD
  rw [erasedN_get, if_pos hz]
  cases ho : (ownCompN n A c i).contains z <;> simp

/-- The capture stage only empties: its stones are the placed diagram's. -/
theorem occD_afterCapN_le (A : Display n) (c : DKind) (i z : Nat)
    (h : occD (afterCapN n A c i) z = true) :
    occD (placedN n A c i) z = true := by
  unfold occD at h ⊢
  rw [afterCapN_get] at h
  by_cases hz : z < n*n
  · rw [if_pos hz] at h
    cases hd : (deadOppN n A c i).contains z
    · rw [hd] at h
      simpa using h
    · rw [hd] at h
      simp at h
  · rw [if_neg hz] at h
    simp at h

/-- Dead components are closed under their placed-diagram components. -/
theorem deadOppN_component_closed (A : Display n) (c : DKind) (i z q : Nat)
    (hz : z ∈ deadOppN n A c i)
    (hq : q ∈ componentD (placedN n A c i) z) :
    q ∈ deadOppN n A c i := by
  rcases (mem_deadOppN_iff A c i z).mp hz with ⟨hzb, hzk, hznl⟩
  have hqk : kindAt (placedN n A c i) q = some c.opp :=
    componentD_kind _ z c.opp hzk q hq
  have hqb : q ∈ allIdx n := componentD_board hzb hzk hq
  refine (mem_deadOppN_iff A c i q).mpr ⟨hqb, hqk, ?_⟩
  have hmemeq := componentD_eq_mem (placedN n A c i) z q c.opp hzb hzk hq
  rw [noLibD_congr _ _ _ hmemeq]
  exact hznl

/-- A dead cell is empty in the move's output, suicide or not. -/
theorem occD_output_dead (A : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hr : goMoveN n A c i = some r) (q : Nat)
    (hq : q < n*n) (hqd : q ∈ deadOppN n A c i) : occD r q = false := by
  have hcd : (deadOppN n A c i).contains q = true :=
    List.contains_iff_mem.mpr hqd
  rw [goMoveN_result A c i r hr]
  split
  · rw [occD_erasedN A c i q hq]
    split
    · rfl
    · rw [occD_afterCapN A c i q hq, if_pos hcd]
  · rw [occD_afterCapN A c i q hq, if_pos hcd]

/-- The placed diagram and the capture stage agree on the mover's color
    (only opposite-colored cells die at the capture stage). -/
theorem kind_c_agree_afterCapN (A : Display n) (c : DKind) (i : Nat)
    (hc : c ≠ .r) :
    ∀ z, z ∈ allIdx n →
      (kindAt (placedN n A c i) z = some c ↔
        kindAt (afterCapN n A c i) z = some c) := by
  intro z hzb
  have hz : z < n*n := List.mem_range.mp hzb
  rw [kindAt_afterCapN A c i z hz]
  cases hd : (deadOppN n A c i).contains z
  · simp
  · have hzdead : z ∈ deadOppN n A c i := List.contains_iff_mem.mp hd
    rcases (mem_deadOppN_iff A c i z).mp hzdead with ⟨_, hzk, _⟩
    rw [if_pos rfl, hzk]
    constructor
    · intro h
      exact absurd (Option.some.inj h) (opp_ne_self hc)
    · intro h
      exact Option.noConfusion h

/-- The per-move removal dichotomy: a stone of the placed diagram that
    the move empties belongs to a whole emptied component, trapped (no
    liberties) in the placed diagram. -/
theorem goMoveN_removed (A : Display n) (c : DKind) (i : Nat)
    (r : Display n) (hwf : WFD A) (hi : i < n*n) (hc : c ≠ .r)
    (hr : goMoveN n A c i = some r) (z : Nat) (hz : z < n*n)
    (hoccP : occD (placedN n A c i) z = true)
    (hrem : occD r z = false) :
    noLibD (placedN n A c i) (componentD (placedN n A c i) z) = true ∧
    ∀ q, q ∈ componentD (placedN n A c i) z → occD r q = false := by
  have hres := goMoveN_result A c i r hr
  by_cases hzd : z ∈ deadOppN n A c i
  · rcases (mem_deadOppN_iff A c i z).mp hzd with ⟨hzb, hzk, hznl⟩
    refine ⟨hznl, ?_⟩
    intro q hq
    have hqdead : q ∈ deadOppN n A c i :=
      deadOppN_component_closed A c i z q hzd hq
    have hqb : q ∈ allIdx n := componentD_board hzb hzk hq
    exact occD_output_dead A c i r hr q (List.mem_range.mp hqb) hqdead
  · -- not captured: the move suicided and z lies in the own component
    have hznotd : ¬ (deadOppN n A c i).contains z = true :=
      fun hcont => hzd (List.contains_iff_mem.mp hcont)
    have hsz : suicideN n A c i = true := by
      cases hs : suicideN n A c i
      · exfalso
        have hocc : occD r z = true := by
          rw [hres]
          split
          · next hstrue =>
            rw [hs] at hstrue
            exact Bool.noConfusion hstrue
          · rw [occD_afterCapN A c i z hz, if_neg hznotd]
            exact hoccP
        rw [hocc] at hrem
        exact Bool.noConfusion hrem
      · rfl
    have hzown : z ∈ ownCompN n A c i := by
      rw [hres, if_pos hsz, occD_erasedN A c i z hz] at hrem
      cases ho : (ownCompN n A c i).contains z
      · exfalso
        rw [ho] at hrem
        simp only [Bool.false_eq_true, if_false] at hrem
        rw [occD_afterCapN A c i z hz, if_neg hznotd] at hrem
        rw [hoccP] at hrem
        exact Bool.noConfusion hrem
      · exact List.contains_iff_mem.mp ho
    have hkCBi : kindAt (afterCapN n A c i) i = some c :=
      kindAt_afterCapN_self A c i hwf hi hc
    have hib : i ∈ allIdx n := List.mem_range.mpr hi
    have hmeq := componentD_eq_mem (afterCapN n A c i) i z c hib hkCBi hzown
    have hkCBz : kindAt (afterCapN n A c i) z = some c :=
      componentD_kind _ i c hkCBi z hzown
    have hkPBz : kindAt (placedN n A c i) z = some c :=
      (kind_c_agree_afterCapN A c i hc z (List.mem_range.mpr hz)).mpr hkCBz
    have htrans := componentD_transport (placedN n A c i)
      (afterCapN n A c i) c (kind_c_agree_afterCapN A c i hc) z hkPBz hkCBz
    have hmm : ∀ q, q ∈ componentD (placedN n A c i) z ↔
        q ∈ componentD (afterCapN n A c i) i :=
      fun q => (htrans q).trans (hmeq q)
    constructor
    · have hsOB : noLibD (afterCapN n A c i)
          (componentD (afterCapN n A c i) i) = true := by
        unfold suicideN ownCompN at hsz
        exact hsz
      have hmono : noLibD (placedN n A c i)
          (componentD (afterCapN n A c i) i) = true :=
        noLibD_mono (placedN n A c i) (afterCapN n A c i) _
          (fun w hw => occD_afterCapN_le A c i w hw) hsOB
      rw [noLibD_congr (placedN n A c i) _ _ hmm]
      exact hmono
    · intro q hq
      have hqCBi : q ∈ componentD (afterCapN n A c i) i := (hmm q).mp hq
      have hqown : q ∈ ownCompN n A c i := hqCBi
      have hqb : q ∈ allIdx n := componentD_board hib hkCBi hqCBi
      rw [hres, if_pos hsz,
        occD_erasedN A c i q (List.mem_range.mp hqb),
        if_pos (List.contains_iff_mem.mpr hqown)]
