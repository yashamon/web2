/- Infra2.lean — array/get-set helpers and goMoveN structural facts. -/
import SgoLemma
open SgoDisplay

variable {n : Nat}

/-- Reading a map-over-range display. -/
theorem get_map_range (m : Nat) (f : Nat → Cell) (p : Nat) :
    (⟨(Array.range m).map f⟩ : Display n).get p
      = if p < m then f p else none := by
  unfold Display.get Array.getD
  by_cases h : p < m
  · simp [Array.size_map, Array.size_range, h, Array.getElem_map, Array.getElem_range]
  · simp [Array.size_map, Array.size_range, h]

/-- Setting one cell leaves the others. -/
theorem get_set_ne (D : Display n) (i j : Nat) (c : Cell) (h : j ≠ i) :
    (D.set i c).get j = D.get j := by
  simp only [Display.get, Display.set, Array.setD, Array.setIfInBounds]
  split
  · next hi =>
    have hne : ¬ i = j := fun hh => h (Eq.symm hh)
    by_cases hj : j < D.cells.size
    · simp [Array.getD, Array.size_set, hj, Array.getElem_set, hne]
    · simp [Array.getD, Array.size_set, hj]
  · rfl

/-- Setting one cell reads back (in bounds). -/
theorem get_set_self (D : Display n) (i : Nat) (c : Cell)
    (h : i < D.cells.size) :
    (D.set i c).get i = c := by
  simp only [Display.get, Display.set, Array.setD, Array.setIfInBounds, h, dite_true]
  unfold Array.getD
  simp [Array.size_set, h, Array.getElem_set]

/-- Reading afterCapN. -/
theorem afterCapN_get (d : Display n) (c : DKind) (i p : Nat) :
    (afterCapN n d c i).get p
      = if p < n*n then
          (if (deadOppN n d c i).contains p then none
           else (placedN n d c i).get p)
        else none := by
  unfold afterCapN
  exact get_map_range (n*n) _ p

/-- Reading erasedN. -/
theorem erasedN_get (d : Display n) (c : DKind) (i p : Nat) :
    (erasedN n d c i).get p
      = if p < n*n then
          (if (ownCompN n d c i).contains p then none
           else (afterCapN n d c i).get p)
        else none := by
  unfold erasedN
  exact get_map_range (n*n) _ p

/-- go_closure, structurally: every cell of a classical-move output is
    empty or is the placed diagram's cell — after the placement, the
    move only empties. -/
theorem goMoveN_get (d : Display n) (c : DKind) (i : Nat) (r : Display n)
    (hr : goMoveN n d c i = some r) (p : Nat) :
    r.get p = none ∨ r.get p = (placedN n d c i).get p := by
  unfold goMoveN at hr
  by_cases hocc : occD d i
  · simp [hocc] at hr
  · simp only [hocc, Bool.false_eq_true, if_false, Option.some.injEq] at hr
    have hac : ∀ q, (afterCapN n d c i).get q = none
        ∨ (afterCapN n d c i).get q = (placedN n d c i).get q := by
      intro q
      rw [afterCapN_get]
      split
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl rfl
    rw [← hr]
    split
    · -- suicide branch: r = erasedN
      rw [erasedN_get]
      split
      · split
        · exact Or.inl rfl
        · exact hac p
      · exact Or.inl rfl
    · -- no suicide: r = afterCapN
      exact hac p

/-- go_fills_only, per move: an intersection empty in d and distinct
    from the placement intersection is empty in the output. -/
theorem goMoveN_fills_only (d : Display n) (c : DKind) (i j : Nat)
    (r : Display n) (hr : goMoveN n d c i = some r)
    (hemp : occD d j = false) (hij : j ≠ i) :
    occD r j = false := by
  rcases goMoveN_get d c i r hr j with h | h
  · simp [occD, h]
  · have hpl : (placedN n d c i).get j = d.get j := by
      unfold placedN
      exact get_set_ne d i j _ hij
    unfold occD at hemp ⊢
    rw [h, hpl]
    exact hemp

/-- A defined move's placement intersection was empty. -/
theorem goMoveN_empty_at (d : Display n) (c : DKind) (i : Nat) (r : Display n)
    (hr : goMoveN n d c i = some r) : occD d i = false := by
  unfold goMoveN at hr
  cases hocc : occD d i
  · rfl
  · rw [hocc] at hr
    simp at hr

/-- Splitting a defined two-move composite into its stages. -/
theorem bind_move_split (d : Display n) (c0 c1t : DKind) (i0 i1 : Nat)
    (r : Display n)
    (h : (goMoveN n d c0 i0).bind (fun e => goMoveN n e c1t i1) = some r) :
    ∃ e, goMoveN n d c0 i0 = some e ∧ goMoveN n e c1t i1 = some r := by
  cases he : goMoveN n d c0 i0 with
  | none => rw [he] at h; simp [Option.bind] at h
  | some e =>
    rw [he] at h
    exact ⟨e, rfl, h⟩

/-- The block, occupied case: an intersection occupied in A and empty
    after the first move stays empty after the second. Needs the ambient
    fact that the second placement intersection is empty in A (true when
    both composite orders are defined): without it, the second move can
    replay on a freshly emptied intersection. -/
theorem block_persist_occupied (A : Display n) (i0 i1 j : Nat)
    (d1 c1 : Display n)
    (hstep1 : goMoveN n A .b i0 = some d1)
    (hstep2 : goMoveN n d1 .w i1 = some c1)
    (hi1 : occD A i1 = false)
    (hocc : occD A j = true) (hemp : occD d1 j = false) :
    occD c1 j = false := by
  have hji1 : j ≠ i1 := by
    intro h
    rw [h, hi1] at hocc
    exact Bool.false_ne_true hocc
  exact goMoveN_fills_only d1 .w i1 j c1 hstep2 hemp hji1

/-- The block, placement-intersection case: i0 itself, when empty after
    the first move (its suicide), stays empty after the second. -/
theorem block_persist_placement (A : Display n) (i0 i1 : Nat)
    (d1 c1 : Display n)
    (hi : i0 ≠ i1)
    (hstep1 : goMoveN n A .b i0 = some d1)
    (hstep2 : goMoveN n d1 .w i1 = some c1)
    (hemp : occD d1 i0 = false) :
    occD c1 i0 = false :=
  goMoveN_fills_only d1 .w i1 i0 c1 hstep2 hemp hi

/-- The block, joint form: an intersection empty after the first move
    and distinct from the second placement intersection is empty in the
    composite. (The two printed cases route through this.) -/
theorem block_persist (d1 c1 : Display n) (i1 j : Nat)
    (hstep2 : goMoveN n d1 .w i1 = some c1)
    (hemp : occD d1 j = false) (hji : j ≠ i1) :
    occD c1 j = false :=
  goMoveN_fills_only d1 .w i1 j c1 hstep2 hemp hji
