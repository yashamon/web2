/- SgoFaith.lean — the main theorem, milestone 2e: SGo is faithful within
   distance zero. At a semiclassical state the tracked branch carries
   the display's cells, so the display-read interface of SGo is the
   branch's interface: with suicide legal and no Ko, both consist of
   the passes and the moves of either player to the empty
   intersections. The finality clause is the double-pass convention on
   both sides. -/
import SgoSemi

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv SgoOK SgoBridge SgoNat SgoSemi

namespace SgoFaith

variable {n : Nat}

/-- A classical move is defined exactly at an empty target. -/
theorem goMoveN_isSome (d : Display n) (c : DKind) (i : Nat) :
    (goMoveN n d c i).isSome = true ↔ occD d i = false := by
  unfold goMoveN
  cases hocc : occD d i
  · simp
  · simp

/-- The interface of a live state of Go: the passes and the moves of
    either player to the empty intersections — at every bigrading. -/
theorem interface0_live (d : Display n) (g j : Bool) (m : goMv.M) :
    Interface0 (goGame n) (PState.live d g j) m
      ↔ (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧
          occD d i = false) := by
  cases m with
  | none =>
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      show (hashOp (goGame n) (PState.live d g j) goMv.pass).isSome = true
      cases j with
      | false => rw [goHash_pass_j0]; rfl
      | true => rw [goHash_pass_j1]; rfl
  | some p =>
    obtain ⟨w, i⟩ := p
    have hunf : Interface0 (goGame n) (PState.live d g j) (some (w, i))
        ↔ (goMvAct n d (some (w, i))).isSome = true := by
      show (hashOp (goGame n) (PState.live d g j) (some (w, i))).isSome
          = true ↔ _
      cases w with
      | false =>
        rw [goHash_black d g j i]
        cases hm : goMvAct n d (some (false, i)) <;> simp [hm]
      | true =>
        rw [goHash_white d g j i]
        cases hm : goMvAct n d (some (true, i)) <;> simp [hm]
    rw [hunf]
    constructor
    · intro hs
      simp only [goMvAct] at hs
      by_cases hib : i < n*n
      · rw [if_pos hib] at hs
        refine Or.inr ⟨w, i, rfl, hib, ?_⟩
        exact (goMoveN_isSome d (if w then .w else .b) i).mp hs
      · rw [if_neg hib] at hs
        cases hs
    · rintro (h | ⟨w', i', hm, hi', hocc'⟩)
      · cases h
      · cases hm
        simp only [goMvAct]
        rw [if_pos hi']
        exact (goMoveN_isSome d _ i).mpr hocc'

/-- Faithfulness within distance zero. -/
theorem sgo_faithful0 (hn : 2 ≤ n) :
    FaithfulWithin (goGame n) (sgoGame n) (rhoSGo n) 0 := by
  refine faithfulWithin_of_three (goGame n) (sgoGame n) sgo_simOK (rhoSGo n) 0 ?_
  intro s hw
  have hsc : ∃ a, SemiC (goGame n) (sgoGame n) s a := by
    cases hw with
    | base h => exact ⟨_, h⟩
  rcases hsc with ⟨a, hsc⟩
  obtain ⟨d, hshape, hmemb, hdisp, -⟩ := (semiC_track hn hsc).track
  refine ⟨⟨_, d, (hmemb d).mpr rfl, rfl⟩, ?_, ?_⟩
  · -- finality: the double pass on both sides
    intro hfin
    have hf : s.final = true := hfin
    refine ⟨PState.done d false, ⟨d, (hmemb d).mpr rfl, ?_⟩, trivial⟩
    rw [hf]
    rfl
  · -- the interface
    intro hnf m
    have hfin : s.final = false := by
      cases hfc : s.final
      · rfl
      · exact absurd hfc hnf
    constructor
    · intro hav a' ha'
      rcases ha' with ⟨e, he, hze⟩
      have hed : e = d := (hmemb e).mp he
      subst hed
      rw [hfin] at hze
      simp only [Bool.false_eq_true, if_false] at hze
      rw [hze, interface0_live]
      rcases hav.2 with h | ⟨w, i, hm, hi, hocc⟩
      · exact Or.inl h
      · refine Or.inr ⟨w, i, hm, hi, ?_⟩
        rw [← occ_eq_of_samecells hdisp i]
        exact hocc
    · intro hall
      have hi0 : Interface0 (goGame n)
          (PState.live d false false) m := by
        apply hall
        refine ⟨d, (hmemb d).mpr rfl, ?_⟩
        rw [hfin]
        rfl
      rw [interface0_live] at hi0
      refine ⟨hfin, ?_⟩
      rcases hi0 with h | ⟨w, i, hm, hi, hocc⟩
      · exact Or.inl h
      · refine Or.inr ⟨w, i, hm, hi, ?_⟩
        rw [occ_eq_of_samecells hdisp i]
        exact hocc

end SgoFaith
