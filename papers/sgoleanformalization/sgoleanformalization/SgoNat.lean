/- SgoNat.lean — the main theorem, milestone 2c: the naturality fields of
   IsSimultaneization for SGo.

   rho_init: the initial branch set is the singleton of Go's initial
   state. nat_defined (the definedness direction of prop_naturality0):
   a defined SGo turn has every branch's P defined — via the invariant
   (display-empty is branch-empty) and the bridge correspondence.
   nat_incl (the inclusion direction): every branch of the evolved
   state is in the union of the branch P's — the double pass sending
   diagrams to their finals, a move turn sending the filtered
   entanglement into the P-outputs under the position normal form.

   The remaining field (semiclassical) is milestone 2d: the
   single-branch tracking along commuting turns, on the pass-variant
   one-stage lemma. -/
import SgoBridge

open SgoGo SgoDisplay SgoSerial SgoGames SgoInv SgoOK SgoBridge

namespace SgoNat

variable {n : Nat}

/-! ### Plumbing: slots, bounds, evolution shapes -/

/-- The slot map recovers the raw moves: Black's slot and White's, in
    one of the two raw orders. -/
theorem slot_shapes {ma mb : goMv.M} {m0 m1 : Option Nat}
    (h : slotMoves ma mb = some (m0, m1)) :
    (ma = mB m0 ∧ mb = mW m1) ∨ (ma = mW m1 ∧ mb = mB m0) := by
  cases ma with
  | none =>
    cases mb with
    | none =>
      simp only [slotMoves] at h
      cases h
      exact Or.inl ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨w, i⟩ := p
      cases w <;> simp only [slotMoves] at h <;> cases h
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  | some p =>
    obtain ⟨w, i⟩ := p
    cases mb with
    | none =>
      cases w <;> simp only [slotMoves] at h <;> cases h
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    | some q =>
      obtain ⟨w1, i1⟩ := q
      cases w <;> cases w1 <;> simp only [slotMoves] at h
      · cases h
      · cases h
        exact Or.inl ⟨rfl, rfl⟩
      · cases h
        exact Or.inr ⟨rfl, rfl⟩
      · cases h

/-- Display availability of a placement bounds its index. -/
theorem bounds_of_availD {D : Display n} {m : Option Nat}
    (h : availD n D m = true) : ∀ i, m = some i → i < n*n := by
  intro i hi
  subst hi
  unfold availD at h
  have hsplit := Bool.and_eq_true (decide (i < n*n)) (!occD D i)
  rw [hsplit] at h
  exact of_decide_eq_true h.1

/-- The shape of a defined SGo turn: nonfinal, both moves available on
    the display, and either the double pass (entanglement carried to
    the final) or a move turn (resolve, evolve, filter). -/
theorem sgoEv_cases {s s' : SGoState n} {m0 m1 : Option Nat}
    (h : sgoEv n s m0 m1 = some s') :
    s.final = false ∧ availD n s.disp m0 = true ∧ availD n s.disp m1 = true ∧
    ((m0 = none ∧ m1 = none ∧
        s' = { s with next := s.next + 1, final := true })
     ∨ (¬(m0 = none ∧ m1 = none) ∧ ∃ bs,
          simEv n s.ent m0 m1 = some bs ∧
          s' = ⟨resolveTurn s.disp s.next m0 m1, s.next + 1,
                bs.filter (compatibleB n (resolveTurn s.disp s.next m0 m1)),
                false⟩)) := by
  unfold sgoEv at h
  by_cases hf : s.final = true
  · rw [if_pos hf] at h; cases h
  · rw [if_neg hf] at h
    have hfin : s.final = false := by
      cases hfc : s.final
      · rfl
      · exact absurd hfc hf
    by_cases hav : (availD n s.disp m0 && availD n s.disp m1) = true
    case neg =>
      have hbang : (!(availD n s.disp m0 && availD n s.disp m1)) = true := by
        cases hb : (availD n s.disp m0 && availD n s.disp m1)
        · rfl
        · exact absurd hb hav
      rw [if_pos hbang] at h; cases h
    case pos =>
      rw [if_neg (by simp [hav] :
        ¬((!(availD n s.disp m0 && availD n s.disp m1)) = true))] at h
      have hava := hav
      rw [Bool.and_eq_true (availD n s.disp m0) (availD n s.disp m1)] at hava
      refine ⟨hfin, hava.1, hava.2, ?_⟩
      cases m0 with
      | none =>
        cases m1 with
        | none =>
          cases h
          exact Or.inl ⟨rfl, rfl, rfl⟩
        | some i1 =>
          cases hse : simEv n s.ent none (some i1) with
          | none => simp only [hse] at h; exact Option.noConfusion h
          | some bs =>
            simp only [hse] at h
            cases h
            exact Or.inr ⟨(by rintro ⟨_, hc⟩; cases hc), bs, rfl, rfl⟩
      | some i0 =>
        cases hse : simEv n s.ent (some i0) m1 with
        | none => simp only [hse] at h; exact Option.noConfusion h
        | some bs =>
          simp only [hse] at h
          cases h
          exact Or.inr ⟨(by rintro ⟨hc, _⟩; cases hc), bs, rfl, rfl⟩

/-- Members of a defined universal evolution come from some branch's
    serialP output. -/
theorem simEv_mem {ent : List (Display n)} {m0 m1 : Option Nat}
    {bs : List (Display n)} (hse : simEv n ent m0 m1 = some bs)
    {x : Display n} (hx : x ∈ bs) :
    ∃ b, b ∈ ent ∧ ∃ l, serialP n b m0 m1 = some l ∧ x ∈ l := by
  unfold simEv at hse
  cases hax : simEvAux n m0 m1 ent with
  | none => rw [hax] at hse; cases hse
  | some out =>
    rw [hax] at hse
    have hbs : bs = dedupD n out := (Option.some.inj hse).symm
    exact simEvAux_mem hax (mem_dedupD _ _ (hbs ▸ hx))

/-! ### The naturality fields -/

/-- rho_init: the initial branch set is the singleton of Go's initial
    state. -/
theorem sgo_rho_init :
    BSet.eqv (rhoSGo n (sgoGame n).q0)
      (BSet.single (sInit (goGame n))) := by
  intro a
  constructor
  · rintro ⟨d, hd, hae⟩
    have hd' : d ∈ ([emptyD n] : List (Display n)) := hd
    have hde : d = emptyD n := List.mem_singleton.mp hd'
    subst hde
    have hae' : a = PState.live (emptyD n) false false := hae
    exact hae'
  · intro ha
    exact ⟨emptyD n, List.mem_cons_self _ _, ha⟩

/-- nat_defined: a defined SGo turn has every branch's P defined. -/
theorem sgo_nat_defined {s : SGoState n} {ma mb : goMv.M}
    (hr : SimReach (sgoGame n) s)
    (hp : ((sgoGame n).pairE s ma mb).isSome) :
    simDefP (goGame n) (rhoSGo n s) ma mb := by
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  unfold sgoGame at hs'
  simp only at hs'
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hs'; cases hs'
  | some p =>
    rw [hsl] at hs'
    obtain ⟨m0, m1⟩ := p
    rcases sgoEv_cases hs' with ⟨hfin, hav0, hav1, -⟩
    have hInv := reach_inv hr
    intro a ha
    rcases ha with ⟨d, hd, hae⟩
    rw [hfin] at hae
    simp only [Bool.false_eq_true, if_false] at hae
    subst hae
    refine ⟨fun hff => hff, ?_⟩
    have hs : (serialP n d m0 m1).isSome :=
      serialP_isSome_of_avail (hInv.entCompat d hd) hav0 hav1
    have hb0 : ∀ i, m0 = some i → i < n*n := bounds_of_availD hav0
    have hb1 : ∀ i, m1 = some i → i < n*n := bounds_of_availD hav1
    rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(Pmap_BW_corr d m0 m1 hb0 hb1).1]; exact hs
    · rw [(Pmap_WB_corr d m0 m1 hb0 hb1).1]; exact hs

/-- nat_incl: every branch of the evolved state lies in the union of
    the branch P's, under the position normal form. -/
theorem sgo_nat_incl {s s' : SGoState n} {ma mb : goMv.M}
    (_hr : SimReach (sgoGame n) s)
    (hst : (sgoGame n).pairE s ma mb = some s') :
    BSet.sub (rhoSGo n s') (simVal (goGame n) (rhoSGo n s) ma mb) := by
  unfold sgoGame at hst
  simp only at hst
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hst; cases hst
  | some p =>
    rw [hsl] at hst
    obtain ⟨m0, m1⟩ := p
    rcases sgoEv_cases hst with ⟨hfin, hav0, hav1, hcase⟩
    have hb0 : ∀ i, m0 = some i → i < n*n := bounds_of_availD hav0
    have hb1 : ∀ i, m1 = some i → i < n*n := bounds_of_availD hav1
    intro z hz
    rcases hz with ⟨e, he, hze⟩
    rcases hcase with ⟨hm0, hm1, hs'⟩ | ⟨hnn, bs, hse, hs'⟩
    · -- the double pass: diagrams ride to their finals
      subst hm0; subst hm1; subst hs'
      have he' : e ∈ s.ent := he
      have hze' : z = PState.done e false := hze
      have hserial : serialP n e none none = some (dedupD n [e, e]) := rfl
      have hmem : e ∈ dedupD n [e, e] :=
        (mem_dedupD_iff _ _).mpr (List.mem_cons_self e [e])
      have hvac : ∀ i : Nat, (none : Option Nat) = some i → i < n*n := by
        intro i hi; cases hi
      rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases (Pmap_BW_corr e none none hvac hvac).2 _ hserial e hmem
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live e false false,
          ⟨e, he', by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze']
        exact hPz
      · rcases (Pmap_WB_corr e none none hvac hvac).2 _ hserial e hmem
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live e false false,
          ⟨e, he', by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze']
        exact hPz
    · -- a move turn: the filtered entanglement lies in the P-union
      subst hs'
      have he' : e ∈ bs.filter
          (compatibleB n (resolveTurn s.disp s.next m0 m1)) := he
      have hze' : z = PState.live e false false := hze
      have hebs : e ∈ bs := (List.mem_filter.mp he').1
      rcases simEv_mem hse hebs with ⟨b, hb, l, hl, hel⟩
      rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases (Pmap_BW_corr b m0 m1 hb0 hb1).2 _ hl e hel
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live b false false,
          ⟨b, hb, by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze', ← repP_live hnn e]
        exact hPz
      · rcases (Pmap_WB_corr b m0 m1 hb0 hb1).2 _ hl e hel
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live b false false,
          ⟨b, hb, by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze', ← repP_live hnn e]
        exact hPz

end SgoNat
