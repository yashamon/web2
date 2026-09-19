/- SgoSemi.lean — the main theorem, milestone 2d: the semiclassical field.
   Along def_semiclassical's recursion the SGo state tracks a single
   branch diagram: the entanglement is that diagram up to membership,
   the display carries its cells, the branch is legal, and the
   associated state is its position normal form (live, or final after
   the double pass).

   The step: commuting turns give equal serial composites (repP is
   injective); the display resolution follows by the one-stage lemmas
   (lem_onestage_final for joint moves, the pass variant for one-move
   turns, nothing for the double pass); collisions cannot commute
   (step0_same_intersection); the resolved display carries the
   composite's cells, so the composite survives the compatibility
   filter and is the whole entanglement. -/
import SgoNat
import SgoStage1

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv SgoOK SgoBridge SgoNat

namespace SgoSemi

variable {n : Nat}

/-- The tracked shape of a semiclassical SGo state. -/
structure SemiTrack (s : SGoState n) (a : (goGame n).S) : Prop where
  reach : SimReach (sgoGame n) s
  track : ∃ d, ((s.final = false ∧ a = PState.live d false false)
        ∨ (s.final = true ∧ a = PState.done d false))
      ∧ (∀ e, e ∈ s.ent ↔ e = d)
      ∧ SameCells s.disp d ∧ IsLegal d

/-- Compatibility from cell agreement: a branch carrying exactly the
    display's stones is compatible with it. -/
theorem compat_of_samecells {D b : Display n} (h : SameCells D b) :
    compatibleB n D b = true := by
  unfold compatibleB
  rw [List.all_eq_true]
  intro i _
  cases hkb : kindAt b i with
  | none => rfl
  | some k =>
    have hD : kindAt D i = some k := (h i).trans hkb
    rw [hD]
    cases k <;> rfl

/-- Members of a defined universal evolution: the converse direction —
    a branch's serialP output lands in the union. -/
theorem simEvAux_mem_of {bs : List (Display n)} {m0 m1 : Option Nat}
    {out : List (Display n)} (h : simEvAux n m0 m1 bs = some out)
    {b : Display n} (hb : b ∈ bs) {l : List (Display n)}
    (hl : serialP n b m0 m1 = some l) {e : Display n} (he : e ∈ l) :
    e ∈ out := by
  induction bs generalizing out with
  | nil => cases hb
  | cons b0 bs ih =>
    cases hp : serialP n b0 m0 m1 with
    | none => exact absurd h (by simp [simEvAux, hp])
    | some l0 =>
      cases hr : simEvAux n m0 m1 bs with
      | none => exact absurd h (by simp [simEvAux, hp, hr])
      | some r =>
        simp only [simEvAux, hp, hr] at h
        cases h
        rcases List.mem_cons.mp hb with rfl | hb'
        · apply List.mem_append.mpr
          apply Or.inl
          have hll : l0 = l := Option.some.inj (hp.symm.trans hl)
          rw [hll]
          exact he
        · exact List.mem_append.mpr (Or.inr (ih hr hb'))

/-- A commuting turn at a position normal form has equal serial
    composites in both orders, and the associated state is their
    common normal form. -/
theorem commute_comp {d : Display n} {ma mb : goMv.M}
    {m0 m1 : Option Nat}
    (hsl : slotMoves ma mb = some (m0, m1))
    (h0 : ∀ i, m0 = some i → i < n*n) (h1 : ∀ i, m1 = some i → i < n*n)
    (hcm : CommuteAt (goGame n) (PState.live d false false) ma mb) :
    ∃ x, bStep2 n d .b .w m0 m1 = some x
      ∧ bStep2 n d .w .b m1 m0 = some x
      ∧ assocOf (goGame n) (PState.live d false false) ma mb
          = repP m0 m1 x := by
  rcases hcm with ⟨X, Y, hX, hY, hsn⟩
  rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- raw order (mB m0, mW m1)
    rw [hash2_01 d m0 m1 h0 h1] at hX
    rw [hash2_10 d m0 m1 h0 h1] at hY
    cases hbs : bStep2 n d .b .w m0 m1 with
    | none => rw [hbs] at hX; cases hX
    | some x =>
      rw [hbs] at hX
      cases hws : bStep2 n d .w .b m1 m0 with
      | none => rw [hws] at hY; cases hY
      | some y =>
        rw [hws] at hY
        have hXx : X = tag01 m0 m1 x := (Option.some.inj hX).symm
        have hYy : Y = tag10 m0 m1 y := (Option.some.inj hY).symm
        rw [hXx, hYy, sN_tag01, sN_tag10] at hsn
        have hxy : x = y := repP_inj m0 m1 x y hsn
        subst hxy
        refine ⟨x, rfl, rfl, ?_⟩
        unfold assocOf
        rw [hash2_01 d m0 m1 h0 h1, hbs]
        rw [show Option.getD (Option.map (tag01 m0 m1) (some x))
          (PState.live d false false) = tag01 m0 m1 x from rfl]
        exact sN_tag01 m0 m1 x
  · -- raw order (mW m1, mB m0)
    rw [hash2_10 d m0 m1 h0 h1] at hX
    rw [hash2_01 d m0 m1 h0 h1] at hY
    cases hws : bStep2 n d .w .b m1 m0 with
    | none => rw [hws] at hX; cases hX
    | some y =>
      rw [hws] at hX
      cases hbs : bStep2 n d .b .w m0 m1 with
      | none => rw [hbs] at hY; cases hY
      | some x =>
        rw [hbs] at hY
        have hXy : X = tag10 m0 m1 y := (Option.some.inj hX).symm
        have hYx : Y = tag01 m0 m1 x := (Option.some.inj hY).symm
        rw [hXy, hYx, sN_tag10, sN_tag01] at hsn
        have hxy : x = y := repP_inj m0 m1 x y hsn.symm
        subst hxy
        refine ⟨x, rfl, rfl, ?_⟩
        unfold assocOf
        rw [hash2_10 d m0 m1 h0 h1, hws]
        rw [show Option.getD (Option.map (tag10 m0 m1) (some x))
          (PState.live d false false) = tag10 m0 m1 x from rfl]
        exact sN_tag10 m0 m1 x

/-- The semiclassical tracking, by induction on the recursion. -/
theorem semiC_track (hn : 2 ≤ n) {s : SGoState n} {a : (goGame n).S}
    (h : SemiC (goGame n) (sgoGame n) s a) : SemiTrack s a := by
  induction h with
  | init =>
    refine ⟨SimReach.init, emptyD n, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro e
      constructor
      · intro he
        have he' : e ∈ ([emptyD n] : List (Display n)) := he
        exact List.mem_singleton.mp he'
      · intro he
        rw [he]
        exact List.mem_cons_self _ _
    · intro z
      rfl
    · intro p hp
      unfold occD at hp
      rw [emptyD_get p] at hp
      cases hp
  | @step s a s' ma mb hsc hcomm hpair ih =>
    obtain ⟨d, hshape, hmemb, hdisp, hlegal⟩ := ih.track
    have hreach' : SimReach (sgoGame n) s' := SimReach.step ih.reach hpair
    have hInv := reach_inv ih.reach
    have hd : d ∈ s.ent := (hmemb d).mpr rfl
    have hdw : WFD d := hInv.entWfd d hd
    have hdc : IsClassical d := hInv.entClassical d hd
    -- unfold the pair evolution
    unfold sgoGame at hpair
    simp only at hpair
    cases hsl : slotMoves ma mb with
    | none => rw [hsl] at hpair; cases hpair
    | some p =>
      rw [hsl] at hpair
      obtain ⟨m0, m1⟩ := p
      rcases sgoEv_cases hpair with ⟨hfin, hav0, hav1, hcase⟩
      have ha : a = PState.live d false false := by
        rcases hshape with ⟨-, ha⟩ | ⟨hf, -⟩
        · exact ha
        · rw [hfin] at hf; cases hf
      subst ha
      have hb0 := bounds_of_availD hav0
      have hb1 := bounds_of_availD hav1
      rcases commute_comp hsl hb0 hb1 hcomm with ⟨x, hx, hy, hassoc⟩
      rcases hcase with ⟨hm0, hm1, hs'⟩ | ⟨hnn, bs, hse, hs'⟩
      · -- the double pass: the branch rides to its final
        subst hm0; subst hm1; subst hs'
        have hxd : x = d := by
          have hsd : (some d : Option (Display n)) = some x := hx
          exact (Option.some.inj hsd).symm
        subst hxd
        refine ⟨hreach', x, Or.inr ⟨rfl, ?_⟩, ?_, hdisp, hlegal⟩
        · rw [hassoc]
          rfl
        · intro e
          exact hmemb e
      · -- a move turn
        subst hs'
        have hserial : serialP n d m0 m1 = some (dedupD n [x, x]) := by
          unfold serialP
          rw [hx, hy]
        -- the resolved display carries the composite's cells, and the
        -- composite is legal
        have hkey : SameCells (resolveTurn s.disp s.next m0 m1) x
            ∧ IsLegal x := by
          cases m0 with
          | none =>
            cases m1 with
            | none => exact absurd ⟨rfl, rfl⟩ hnn
            | some i1 =>
              have hmv : goMoveN n d .w i1 = some x := hx
              exact ⟨onestage_right s.next hInv.next_pos d s.disp i1
                  hdw hInv.wfdD (hb1 i1 rfl) hdc hlegal hdisp
                  hInv.stamps x hmv,
                goMoveN_legal d .w i1 x hdw (hb1 i1 rfl)
                  (by intro h; cases h) hdc hlegal hmv⟩
          | some i0 =>
            cases m1 with
            | none =>
              have hbs : Option.bind (goMoveN n d .b i0)
                  (fun d1 => some d1) = some x := hx
              have hmv : goMoveN n d .b i0 = some x := by
                cases hb1' : goMoveN n d .b i0 with
                | none =>
                  rw [hb1'] at hbs
                  cases hbs
                | some m =>
                  rw [hb1'] at hbs
                  exact hbs
              exact ⟨onestage_left s.next hInv.next_pos d s.disp i0
                  hdw hInv.wfdD (hb0 i0 rfl) hdc hlegal hdisp
                  hInv.stamps x hmv,
                goMoveN_legal d .b i0 x hdw (hb0 i0 rfl)
                  (by intro h; cases h) hdc hlegal hmv⟩
            | some i1 =>
              have hbs1 : Option.bind (goMoveN n d .b i0)
                  (fun e => goMoveN n e .w i1) = some x := hx
              have hbs2 : Option.bind (goMoveN n d .w i1)
                  (fun e => goMoveN n e .b i0) = some x := hy
              have hne : i0 ≠ i1 := by
                intro he
                subst he
                exact step0_same_intersection hn d i0 hdw (hb0 i0 rfl)
                  hdc hlegal x x hbs1 hbs2
              have hlem := lem_onestage_final hn s.next hInv.next_pos
                d s.disp hdw hInv.wfdD hdc hlegal hdisp hInv.stamps
                i0 i1 (hb0 i0 rfl) (hb1 i1 rfl) hne x x hbs1 hbs2
                (fun _ => rfl)
              cases hm : goMoveN n d .b i0 with
              | none =>
                rw [hm] at hbs1
                cases hbs1
              | some m =>
                rw [hm] at hbs1
                have hmv2 : goMoveN n m .w i1 = some x := hbs1
                have hmw : WFD m := goMoveN_size d .b i0 m hm
                have hmc : IsClassical m :=
                  goMoveN_classical d .b i0 m hdc
                    (by intro h; cases h) hm
                have hml : IsLegal m :=
                  goMoveN_legal d .b i0 m hdw (hb0 i0 rfl)
                    (by intro h; cases h) hdc hlegal hm
                exact ⟨hlem.2,
                  goMoveN_legal m .w i1 x hmw (hb1 i1 rfl)
                    (by intro h; cases h) hmc hml hmv2⟩
        have hcompat : compatibleB n
            (resolveTurn s.disp s.next m0 m1) x = true :=
          compat_of_samecells hkey.1
        have hout : ∃ out, simEvAux n m0 m1 s.ent = some out
            ∧ bs = dedupD n out := by
          unfold simEv at hse
          cases haux : simEvAux n m0 m1 s.ent with
          | none => rw [haux] at hse; cases hse
          | some out =>
            rw [haux] at hse
            exact ⟨out, rfl, (Option.some.inj hse).symm⟩
        rcases hout with ⟨out, haux, hbse⟩
        have hment : ∀ e, e ∈ bs.filter
            (compatibleB n (resolveTurn s.disp s.next m0 m1))
            ↔ e = x := by
          intro e
          constructor
          · intro he
            have hebs : e ∈ bs := (List.mem_filter.mp he).1
            rcases simEv_mem hse hebs with ⟨b, hb, l, hl, hel⟩
            have hbd : b = d := (hmemb b).mp hb
            subst hbd
            rw [hserial] at hl
            cases hl
            rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hel)
              with h | h
            · exact h
            · exact List.mem_singleton.mp h
          · intro he
            rw [he]
            apply List.mem_filter.mpr
            refine ⟨?_, hcompat⟩
            rw [hbse]
            apply (mem_dedupD_iff _ _).mpr
            exact simEvAux_mem_of haux hd hserial
              ((mem_dedupD_iff _ _).mpr (List.mem_cons_self x [x]))
        refine ⟨hreach', x, Or.inl ⟨rfl, ?_⟩, hment, hkey.1, hkey.2⟩
        rw [hassoc]
        exact repP_live hnn x

/-- The semiclassical field: along the recursion the branch set is the
    singleton of the associated state. -/
theorem sgo_semiclassical (hn : 2 ≤ n) {s : SGoState n}
    {a : (goGame n).S} (h : SemiC (goGame n) (sgoGame n) s a) :
    BSet.eqv (rhoSGo n s) (BSet.single a) := by
  obtain ⟨d, hshape, hmemb, -, -⟩ := (semiC_track hn h).track
  intro z
  constructor
  · rintro ⟨e, he, hze⟩
    have hed : e = d := (hmemb e).mp he
    subst hed
    rcases hshape with ⟨hf, ha⟩ | ⟨hf, ha⟩
    · rw [hf] at hze
      simp only [Bool.false_eq_true, if_false] at hze
      rw [ha]
      exact hze
    · rw [hf] at hze
      simp only [if_true] at hze
      rw [ha]
      exact hze
  · intro hz
    refine ⟨d, (hmemb d).mpr rfl, ?_⟩
    rcases hshape with ⟨hf, ha⟩ | ⟨hf, ha⟩
    · rw [hf]
      simp only [Bool.false_eq_true, if_false]
      rw [hz, ha]
    · rw [hf]
      simp only [if_true]
      rw [hz, ha]

/-- def_symmetrization, conditions 3 and 4: SGo is a simultaneization
    of Go under the branch semantics. -/
theorem sgo_isSimultaneization (hn : 2 ≤ n) :
    IsSimultaneization (goGame n) (sgoGame n) (rhoSGo n) where
  rho_init := sgo_rho_init
  nat_defined := fun hr hp => sgo_nat_defined hr hp
  nat_incl := fun hr hst => sgo_nat_incl hr hst
  semiclassical := fun h => sgo_semiclassical hn h

end SgoSemi
