/- SgoDNat.lean — the main theorem, milestone 3c: the naturality fields of
   IsSimultaneization for DSGo.

   rho_init is SGo's. nat_defined runs on occupancy inclusion instead
   of compatibility: display-available moves are branch-available
   (branch stones only stand on occupied intersections), so every
   branch's P is defined. nat_incl: the evolved entanglement is the
   re-cut of the decoherence, the re-cut is vacuous at invariant
   states (delta_out), so members trace back through simEv to a
   branch's serialization, which the bridge correspondence puts under
   the branch's P — the double pass rides diagrams to their finals. -/
import SgoDOK

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoDInv SgoDOK

namespace SgoDNat

variable {n : Nat}

/-- At an invariant state, a defined decoherence satisfies delta_out's
    hypothesis bundle for the placed display. -/
theorem invD_delta {s : SGoState n} (h : InvD s) {m0 m1 : Option Nat}
    (h0 : availD n s.disp m0 = true) (h1 : availD n s.disp m1 = true)
    {dec : List (Display n)} (hse : simEv n s.ent m0 m1 = some dec) :
    WFD (placeJoint s.disp s.next m0 m1)
    ∧ (∀ x, x ∈ dec → IsClassical x)
    ∧ (∀ x, x ∈ dec →
        occIncB n (placeJoint s.disp s.next m0 m1) x = true) := by
  have hwfp : WFD (placeJoint s.disp s.next m0 m1) :=
    placeJoint_wfd _ _ _ _ h.wfdD
  have htgt0 : ∀ i, m0 = some i →
      occD (placeJoint s.disp s.next m0 m1) i = true := by
    intro i hi
    have hii : i < n*n := bounds_of_availD h0 i hi
    rw [hi]
    exact pJ_occ_target0 s.disp s.next m1 h.wfdD hii
  have htgt1 : ∀ i, m1 = some i →
      occD (placeJoint s.disp s.next m0 m1) i = true := by
    intro i hi
    have hii : i < n*n := bounds_of_availD h1 i hi
    rw [hi]
    exact pJ_occ_target1 s.disp s.next m0 h.wfdD hii
  refine ⟨hwfp, ?_, ?_⟩
  · intro x hx
    rcases simEv_mem hse hx with ⟨b0, hb0, l, hl, hxl⟩
    exact (serialP_out
      (fun d c hc i r hd hr => goMoveN_preserves d c hc i r hr hd)
      ⟨h.entClassical b0 hb0, h.entZero b0 hb0⟩ hl x hxl).1
  · intro x hx
    rcases simEv_mem hse hx with ⟨b0, hb0, l, hl, hxl⟩
    refine serialP_occInc htgt0 htgt1 ?_ hl x hxl
    exact occIncB_mono
      (fun j ho => pJ_occ_mono s.disp s.next m0 m1 ho)
      (h.entInc b0 hb0)

/-! ### The naturality fields -/

/-- rho_init: the initial branch set is the singleton of Go's initial
    state. -/
theorem dsgo_rho_init :
    BSet.eqv (rhoD n (dsgoGame n).q0)
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

/-- nat_defined: a defined DSGo turn has every branch's P defined. -/
theorem dsgo_nat_defined {s : SGoState n} {ma mb : goMv.M}
    (hr : SimReach (dsgoGame n) s)
    (hp : ((dsgoGame n).pairE s ma mb).isSome) :
    simDefP (goGame n) (rhoD n s) ma mb := by
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  unfold dsgoGame at hs'
  simp only at hs'
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hs'; cases hs'
  | some p =>
    rw [hsl] at hs'
    obtain ⟨m0, m1⟩ := p
    rcases dsgoEv_cases hs' with ⟨hfin, hav0, hav1, -⟩
    have hInv := reach_invD hr
    intro a ha
    rcases ha with ⟨d, hd, hae⟩
    rw [hfin] at hae
    simp only [Bool.false_eq_true, if_false] at hae
    subst hae
    refine ⟨fun hff => hff, ?_⟩
    have hs : (serialP n d m0 m1).isSome :=
      serialP_isSome_of_occInc (hInv.entInc d hd) hav0 hav1
    have hb0 : ∀ i, m0 = some i → i < n*n := bounds_of_availD hav0
    have hb1 : ∀ i, m1 = some i → i < n*n := bounds_of_availD hav1
    rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(Pmap_BW_corr d m0 m1 hb0 hb1).1]; exact hs
    · rw [(Pmap_WB_corr d m0 m1 hb0 hb1).1]; exact hs

/-- nat_incl: every branch of the evolved state lies in the union of
    the branch P's, under the position normal form — through the
    provably vacuous re-cut. -/
theorem dsgo_nat_incl {s s' : SGoState n} {ma mb : goMv.M}
    (hr : SimReach (dsgoGame n) s)
    (hst : (dsgoGame n).pairE s ma mb = some s') :
    BSet.sub (rhoD n s') (simVal (goGame n) (rhoD n s) ma mb) := by
  unfold dsgoGame at hst
  simp only at hst
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hst; cases hst
  | some p =>
    rw [hsl] at hst
    obtain ⟨m0, m1⟩ := p
    rcases dsgoEv_cases hst with ⟨hfin, hav0, hav1, dec, hse, hs'⟩
    have hInv := reach_invD hr
    have hb0 : ∀ i, m0 = some i → i < n*n := bounds_of_availD hav0
    have hb1 : ∀ i, m1 = some i → i < n*n := bounds_of_availD hav1
    obtain ⟨hwfp, hdcl, hdinc⟩ := invD_delta hInv hav0 hav1 hse
    obtain ⟨hmem_iff, -, -, -⟩ :=
      delta_out s.next (placeJoint s.disp s.next m0 m1) dec
        hwfp hdcl hdinc
    subst hs'
    intro z hz
    rcases hz with ⟨e, he, hze⟩
    have hedec : e ∈ dec := (hmem_iff e).mp he
    rcases simEv_mem hse hedec with ⟨b, hb, l, hl, hel⟩
    by_cases hnn : m0 = none ∧ m1 = none
    · -- the double pass: diagrams ride to their finals
      obtain ⟨h00, h11⟩ := hnn
      subst h00
      subst h11
      have hlb : l = dedupD n [b, b] := by
        have hser : serialP n b none none = some (dedupD n [b, b]) := rfl
        rw [hser] at hl
        exact (Option.some.inj hl).symm
      have heb : e = b := by
        rw [hlb] at hel
        rcases List.mem_cons.mp ((mem_dedupD_iff _ _).mp hel) with h | h
        · exact h
        · simpa using h
      subst heb
      have hze' : z = PState.done e false := hze
      have hserial : serialP n e none none
          = some (dedupD n [e, e]) := rfl
      have hmem : e ∈ dedupD n [e, e] :=
        (mem_dedupD_iff _ _).mpr (List.mem_cons_self e [e])
      rcases slot_shapes hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases (Pmap_BW_corr e none none hb0 hb1).2 _ hserial e hmem
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live e false false,
          ⟨e, hb, by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze']
        exact hPz
      · rcases (Pmap_WB_corr e none none hb0 hb1).2 _ hserial e hmem
          with ⟨P, hP, hPz⟩
        refine ⟨PState.live e false false,
          ⟨e, hb, by simp [hfin]⟩, P, hP, ?_⟩
        rw [hze']
        exact hPz
    · -- a move turn: the flag is down, the branch is live
      have hflag : (m0.isNone && m1.isNone) = false := by
        cases hm0 : m0 with
        | some i0 => rfl
        | none =>
          cases hm1 : m1 with
          | some i1 => rfl
          | none => exact absurd ⟨hm0, hm1⟩ hnn
      have hze' : z = PState.live e false false := by
        have hz2 : z = if (m0.isNone && m1.isNone) = true
            then PState.done e false else PState.live e false false := hze
        rw [hflag] at hz2
        simpa using hz2
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

end SgoDNat
