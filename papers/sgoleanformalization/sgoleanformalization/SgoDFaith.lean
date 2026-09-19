/- SgoDFaith.lean — the main theorem, milestones 3e/3f: DSGo is faithful
   within EVERY distance, and simple.

   Faithfulness needs no semiclassical tracking: at every reachable
   state the entanglement is nonempty, every branch stands under the
   display's occupancy (display-available moves are branch-available),
   and every occupied display intersection is branch-supported
   (lem_survival's content — branch-available moves are
   display-available). The finality clause is the double-pass flag on
   both sides. Radius infinity follows because WithinD at any d only
   produces reachable states. Simplicity is the all-black paint, as
   for SGo. -/
import SgoDSemi
import SgoSimple

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoSimple SgoDInv SgoDOK SgoDNat SgoDSemi

namespace SgoDFaith

variable {n : Nat}

/-- Every within-d state is reachable. -/
theorem withinD_reach {d : Nat} {s : SGoState n}
    (h : WithinD (goGame n) (dsgoGame n) (rhoD n) d s) :
    SimReach (dsgoGame n) s := by
  induction h with
  | base hsc => exact semiC_reach hsc
  | ofLe hw ih => exact ih
  | step hw hpair ih => exact SimReach.step ih hpair

/-- def_faithful at every reachable state, from the invariant alone:
    occupancy inclusion gives the forward interface reading, support
    the backward one. -/
theorem dsgo_faithfulAt3 {s : SGoState n}
    (hr : SimReach (dsgoGame n) s) :
    FaithfulAt3 (goGame n) (dsgoGame n) (rhoD n) s := by
  have hInv := reach_invD hr
  obtain ⟨e0, he0⟩ : ∃ e, e ∈ s.ent := by
    cases hent : s.ent with
    | nil => exact absurd hent hInv.entNe
    | cons b bs => exact ⟨b, hent.symm ▸ List.mem_cons_self b bs⟩
  refine ⟨⟨if s.final then PState.done e0 false
      else PState.live e0 false false, e0, he0, rfl⟩, ?_, ?_⟩
  · -- finality: the double pass on both sides
    intro hfin
    have hf : s.final = true := hfin
    refine ⟨PState.done e0 false, ⟨e0, he0, ?_⟩, trivial⟩
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
      rw [hfin] at hze
      simp only [Bool.false_eq_true, if_false] at hze
      rw [hze, interface0_live]
      rcases hav.2 with h | ⟨w, i, hm, hi, hocc⟩
      · exact Or.inl h
      · refine Or.inr ⟨w, i, hm, hi, ?_⟩
        exact branch_empty_of_occInc (hInv.entInc e he) hi hocc
    · intro hall
      refine ⟨hfin, ?_⟩
      have hi0 : Interface0 (goGame n)
          (PState.live e0 false false) m := by
        apply hall
        refine ⟨e0, he0, ?_⟩
        rw [hfin]
        rfl
      rw [interface0_live] at hi0
      rcases hi0 with h | ⟨w, i, hm, hi, hocc0⟩
      · exact Or.inl h
      · refine Or.inr ⟨w, i, hm, hi, ?_⟩
        -- the display is empty at i: else the support hands us a
        -- branch occupying i, whose interface refutes the move
        cases hoccD : occD s.disp i with
        | false => rfl
        | true =>
          exfalso
          rcases hInv.supp i hi hoccD with ⟨b, hb, hoccb⟩
          have hib : Interface0 (goGame n)
              (PState.live b false false) m := by
            apply hall
            refine ⟨b, hb, ?_⟩
            rw [hfin]
            rfl
          rw [interface0_live] at hib
          rcases hib with h' | ⟨w', i', hm', hi', hocc'⟩
          · rw [hm] at h'; cases h'
          · rw [hm] at hm'
            have hpp := Option.some.inj hm'
            have hii : i = i' := congrArg Prod.snd hpp
            rw [← hii] at hocc'
            rw [hoccb] at hocc'
            cases hocc'

/-- The printed def_faithful, from the three-clause form. -/
theorem dsgo_faithfulAt {s : SGoState n}
    (hr : SimReach (dsgoGame n) s) :
    FaithfulAt (goGame n) (dsgoGame n) (rhoD n) s :=
  (faithfulAt_iff (goGame n) (dsgoGame n) dsgo_simOK (rhoD n) hr).2 (dsgo_faithfulAt3 hr)

/-- The faithfulness radius of DSGo is infinite: faithful within
    every distance. -/
theorem dsgo_faithful_all (d : Nat) :
    FaithfulWithin (goGame n) (dsgoGame n) (rhoD n) d :=
  fun _s hw => dsgo_faithfulAt (withinD_reach hw)

/-- def_simplesymmetrization for DSGo: the all-black paint of the
    display realizes the interface. -/
theorem dsgo_isSimple : IsSimple (goGame n) (dsgoGame n) := by
  intro s hr hnf hex
  have hInv := reach_invD hr
  have hfin : s.final = false := by
    cases hfc : s.final
    · rfl
    · exact absurd hfc hnf
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
          exact absurd ((blackD_occ _ hbS i).mpr this)
            (by rw [hbl]; exact Bool.noConfusion)
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
    · have h1 : (blackD (n := n) ((allIdx n).filter
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

end SgoDFaith
