/- SgoOK.lean — the main theorem, milestone 2b: the game axioms.
   reach_inv carries the SgoInv invariant along SimReach; SimOK for
   sgoGame (def_simultaneous's properties over reachable states,
   availability display-read via sgoEv_isSome_iff). The sequential
   side's printed properties hold by construction of the option-C
   core presentation — no separate proof object. SeqSym/SimSym (the
   color-swap operators) are the deferred symmetry batch. -/
import SgoInst
import SgoInv

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv

namespace SgoOK

variable {n : Nat}

/-! ### The invariant along reachability -/

theorem pairE_to_sgoEv {s s' : SGoState n} {ma mb : goMv.M}
    (h : (sgoGame n).pairE s ma mb = some s') :
    ∃ m0 m1, sgoEv n s m0 m1 = some s' := by
  unfold sgoGame at h
  simp only at h
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at h; cases h
  | some p =>
    rw [hsl] at h
    exact ⟨p.1, p.2, h⟩

theorem reach_inv {s : SGoState n} (h : SimReach (sgoGame n) s) :
    Inv s := by
  induction h with
  | init => exact inv_init
  | step hr hst ih =>
    rcases pairE_to_sgoEv hst with ⟨m0, m1, hev⟩
    exact inv_step ih hev

/-! ### SimOK for SGo -/

theorem availD_of_avail {s : SGoState n} {m : goMv.M}
    (hm : (sgoGame n).avail s m) :
    ∀ w i, m = some (w, i) → availD n s.disp (some i) = true := by
  intro w i hmi
  rcases hm.2 with h | ⟨w', i', hmi', hi', hocc'⟩
  · rw [hmi] at h; cases h
  · rw [hmi] at hmi'
    cases hmi'
    show (decide (i < n*n) && !occD s.disp i) = true
    rw [decide_eq_true hi', hocc']
    rfl

theorem sgo_simOK : SimOK (sgoGame n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- final_nomove
    intro s m _ hfin hav
    have h1 : s.final = true := hfin
    rw [hav.1] at h1
    cases h1
  · -- pass_available
    intro s _ hnf
    refine ⟨?_, Or.inl rfl⟩
    cases hfc : s.final
    · rfl
    · exact absurd hfc hnf
  · -- pair_of_avail
    intro s m0 m1 hr hd0 hd1 hav0 hav1
    have hInv := reach_inv hr
    have hfin : s.final = false := hav0.1
    have hpassD : availD n s.disp none = true := rfl
    unfold sgoGame
    simp only
    cases m0 with
    | none =>
      cases m1 with
      | none =>
        show (sgoEv n s none none).isSome
        exact (sgoEv_isSome_iff s hInv.entCompat none none).mpr
          ⟨hfin, hpassD, hpassD⟩
      | some p1 =>
        rcases hd1 with h | ⟨i, hi⟩
        · cases h
        · cases hi
          show (sgoEv n s none (some i)).isSome
          exact (sgoEv_isSome_iff s hInv.entCompat none (some i)).mpr
            ⟨hfin, hpassD, availD_of_avail hav1 true i rfl⟩
    | some p0 =>
      rcases hd0 with h | ⟨i0, hi0⟩
      · cases h
      · cases hi0
        cases m1 with
        | none =>
          show (sgoEv n s (some i0) none).isSome
          exact (sgoEv_isSome_iff s hInv.entCompat (some i0) none).mpr
            ⟨hfin, availD_of_avail hav0 false i0 rfl, hpassD⟩
        | some p1 =>
          rcases hd1 with h | ⟨i1, hi1⟩
          · cases h
          · cases hi1
            show (sgoEv n s (some i0) (some i1)).isSome
            exact (sgoEv_isSome_iff s hInv.entCompat
              (some i0) (some i1)).mpr
              ⟨hfin, availD_of_avail hav0 false i0 rfl,
               availD_of_avail hav1 true i1 rfl⟩
  · -- avail_of_pair
    intro s m0 m1 hr hp
    have hInv := reach_inv hr
    rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
    unfold sgoGame at hs'
    simp only at hs'
    cases hsl : slotMoves m0 m1 with
    | none => rw [hsl] at hs'; cases hs'
    | some p =>
      rw [hsl] at hs'
      have h2 : sgoEv n s p.1 p.2 = some s' := hs'
      have hev : (sgoEv n s p.1 p.2).isSome := by rw [h2]; rfl
      have hiff := (sgoEv_isSome_iff s hInv.entCompat p.1 p.2).mp hev
      have hfin := hiff.1
      -- rebuild availability of each input move from the slot facts
      have havOf : ∀ (m : goMv.M) (a : Option Nat),
          (∀ w i, m = some (w, i) → a = some i) →
          availD n s.disp a = true → (sgoGame n).avail s m := by
        intro m a hshape hava
        refine ⟨hfin, ?_⟩
        cases m with
        | none => exact Or.inl rfl
        | some wi =>
          refine Or.inr ⟨wi.1, wi.2, rfl, ?_, ?_⟩
          · have ha := hshape wi.1 wi.2 rfl
            rw [ha] at hava
            unfold availD at hava
            have := Bool.and_eq_true (decide (wi.2 < n*n)) (!occD s.disp wi.2)
            rw [this] at hava
            exact of_decide_eq_true hava.1
          · have ha := hshape wi.1 wi.2 rfl
            rw [ha] at hava
            unfold availD at hava
            have := Bool.and_eq_true (decide (wi.2 < n*n)) (!occD s.disp wi.2)
            rw [this] at hava
            have hb := hava.2
            cases hoc : occD s.disp wi.2
            · rfl
            · rw [hoc] at hb; exact absurd hb (by simp)
      -- case the shapes to identify the slots
      cases m0 with
      | none =>
        cases m1 with
        | none =>
            simp only [slotMoves] at hsl
            cases hsl
            exact ⟨havOf none none (by intro w i h; cases h) hiff.2.1,
                   havOf none none (by intro w i h; cases h) hiff.2.2⟩
        | some wi =>
            simp only [slotMoves] at hsl
            by_cases hw : wi.1 = true
            · rw [show wi = (wi.1, wi.2) from rfl, hw] at hsl
              simp only [if_true] at hsl
              cases hsl
              exact ⟨havOf none none (by intro w i h; cases h) hiff.2.1,
                     havOf (some wi) (some wi.2)
                       (by intro w i h; cases h; rfl) hiff.2.2⟩
            · have hwf : wi.1 = false := by
                cases hwc : wi.1
                · rfl
                · exact absurd hwc hw
              rw [show wi = (wi.1, wi.2) from rfl, hwf] at hsl
              simp only [Bool.false_eq_true, if_false] at hsl
              cases hsl
              exact ⟨havOf none none (by intro w i h; cases h) hiff.2.2,
                     havOf (some wi) (some wi.2)
                       (by intro w i h; cases h; rfl) hiff.2.1⟩
      | some wi0 =>
        cases m1 with
        | none =>
            simp only [slotMoves] at hsl
            by_cases hw : wi0.1 = true
            · rw [show wi0 = (wi0.1, wi0.2) from rfl, hw] at hsl
              simp only [if_true] at hsl
              cases hsl
              exact ⟨havOf (some wi0) (some wi0.2)
                       (by intro w i h; cases h; rfl) hiff.2.2,
                     havOf none none (by intro w i h; cases h) hiff.2.1⟩
            · have hwf : wi0.1 = false := by
                cases hwc : wi0.1
                · rfl
                · exact absurd hwc hw
              rw [show wi0 = (wi0.1, wi0.2) from rfl, hwf] at hsl
              simp only [Bool.false_eq_true, if_false] at hsl
              cases hsl
              exact ⟨havOf (some wi0) (some wi0.2)
                       (by intro w i h; cases h; rfl) hiff.2.1,
                     havOf none none (by intro w i h; cases h) hiff.2.2⟩
        | some wi1 =>
            simp only [slotMoves] at hsl
            by_cases hsame : (wi0.1 == wi1.1) = true
            · rw [show wi0 = (wi0.1, wi0.2) from rfl,
                show wi1 = (wi1.1, wi1.2) from rfl] at hsl
              rw [if_pos hsame] at hsl
              cases hsl
            · rw [show wi0 = (wi0.1, wi0.2) from rfl,
                show wi1 = (wi1.1, wi1.2) from rfl] at hsl
              rw [if_neg hsame] at hsl
              by_cases hw0 : wi0.1 = true
              · rw [hw0] at hsl
                simp only [if_true] at hsl
                cases hsl
                exact ⟨havOf (some wi0) (some wi0.2)
                         (by intro w i h; cases h; rfl) hiff.2.2,
                       havOf (some wi1) (some wi1.2)
                         (by intro w i h; cases h; rfl) hiff.2.1⟩
              · have hwf : wi0.1 = false := by
                  cases hwc : wi0.1
                  · rfl
                  · exact absurd hwc hw0
                rw [hwf] at hsl
                simp only [Bool.false_eq_true, if_false] at hsl
                cases hsl
                exact ⟨havOf (some wi0) (some wi0.2)
                         (by intro w i h; cases h; rfl) hiff.2.1,
                       havOf (some wi1) (some wi1.2)
                         (by intro w i h; cases h; rfl) hiff.2.2⟩
  · -- final_exists
    exact ⟨⟨emptyD n, 2, [emptyD n], true⟩, rfl⟩

end SgoOK
