/- SgoKNat.lean — the main theorem, milestone 4b: the semiclassical window
   of k-DSGo.

   Along the semiclassical recursion the verdict queue is all-empty:
   the display is a legal classical position, its objective reduction
   is the identity, and the stored verdict is empty. Hence a
   semiclassical k-DSGo history projects to a DSGo history (execV of
   the empty verdict is the identity), and within distance j ≤ k the
   first k−j stored verdicts are still the empty ones of the
   generating history — every turn within the window is a DSGo turn.
   Faithfulness within k, naturality, the semiclassical field, and
   simplicity all follow by projection. -/
import SgoKInv

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoSimple SgoDInv SgoDOK SgoDNat SgoDSemi
  SgoDFaith SgoKInv

namespace SgoKNat

variable {n : Nat}

/-! ### Plumbing -/

theorem filterMap_nil {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ a, a ∈ l → f a = none) : l.filterMap f = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons, h a (List.mem_cons_self a l)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem replicate_append_one {α : Type} (k : Nat) (a : α) :
    List.replicate k a ++ [a] = List.replicate (k+1) a := by
  induction k with
  | zero => rfl
  | succ kk ih =>
    rw [List.replicate_succ a kk]
    rw [List.replicate_succ a (kk+1)]
    rw [List.cons_append]
    rw [ih]

/-- Building a DSGo turn from its components. -/
theorem dsgoEv_build (u : SGoState n) {m0 m1 : Option Nat}
    {dec : List (Display n)}
    (hf : u.final = false) (h0 : availD n u.disp m0 = true)
    (h1 : availD n u.disp m1 = true)
    (hse : simEv n u.ent m0 m1 = some dec) :
    dsgoEv n u m0 m1 = some
      ⟨(delta n u.next (placeJoint u.disp u.next m0 m1) dec).1,
       u.next + 1,
       (delta n u.next (placeJoint u.disp u.next m0 m1) dec).2,
       m0.isNone && m1.isNone⟩ := by
  unfold dsgoEv
  rw [if_neg (by simp [hf] : ¬(u.final = true))]
  rw [if_neg (by simp [h0, h1] :
    ¬((!(availD n u.disp m0 && availD n u.disp m1)) = true))]
  simp only [hse]

/-- The empty verdict of a classically resolved display: at a legal
    classical position the objective reduction is the identity, so
    both verdict components vanish. -/
theorem verOf_empty {t : Nat} {D x : Display n} (hcl : IsClassical D)
    (hwf : WFD D) (hsc : SameCells D x) (hlx : IsLegal x) :
    verOf n t D = emptyV := by
  have hnc : ∀ kk t', capturedOf D t' kk = [] :=
    fun kk t' => nocap_of_legal D x hsc hlx kk t'
  have hor : orOp n t D = D := by
    unfold orOp
    exact stages_id D (fun t' => basicCap_id D hcl hwf hnc t') (t+1) t
  unfold verOf
  simp only [hor]
  show (⟨_, _⟩ : Verdict) = (⟨[], []⟩ : Verdict)
  congr 1
  · apply filterMap_nil
    intro a ha
    show (match D.get a with
      | some (_, st) => if occD D a then none else some (a, st)
      | none => none) = none
    cases hg : D.get a with
    | none => rfl
    | some c =>
      obtain ⟨kk, st⟩ := c
      have hocc : occD D a = true := by
        unfold occD
        rw [hg]
        rfl
      show (if occD D a = true then none else some (a, st)) = none
      rw [if_pos hocc]
  · apply filterMap_nil
    intro a ha
    show (match D.get a, D.get a with
      | some (.r, st), some (kk, _) =>
        if kk != DKind.r then some (a, st, kk) else none
      | _, _ => none) = none
    cases hg : D.get a with
    | none => rfl
    | some c =>
      obtain ⟨kk, st⟩ := c
      cases kk with
      | r =>
        exact absurd (show kindAt D a = some .r from by
          unfold kindAt; rw [hg]; rfl) (hcl a)
      | b => rfl
      | w => rfl

/-! ### The semiclassical projection -/

/-- A semiclassical k-DSGo history is a DSGo history with an
    all-empty verdict queue. -/
theorem ksemiC_project (hn : 2 ≤ n) {k : Nat} {s : KState n}
    {a : (goGame n).S}
    (h : SemiC (goGame n) (kGame n k) s a) :
    SemiC (goGame n) (dsgoGame n) (toS s) a
    ∧ s.verdicts = List.replicate k emptyV
    ∧ SimReach (kGame n k) s := by
  induction h with
  | init =>
    exact ⟨SemiC.init, rfl, SimReach.init⟩
  | @step s a s' ma mb hsc hcomm hpair ih =>
    obtain ⟨hproj, hallq, hreach⟩ := ih
    have hreach' : SimReach (kGame n k) s' := SimReach.step hreach hpair
    unfold kGame at hpair
    simp only at hpair
    cases hsl : slotMoves ma mb with
    | none => rw [hsl] at hpair; cases hpair
    | some p =>
      rw [hsl] at hpair
      obtain ⟨m0, m1⟩ := p
      rcases kEv_cases hpair with ⟨hf, h0, h1, v1, vr, dec, hq', hse, hs'⟩
      rw [hallq] at hq'
      cases k with
      | zero => cases hq'
      | succ kk =>
        rw [List.replicate_succ emptyV kk] at hq'
        injection hq' with hv1 hvr
        have hv1' : v1 = emptyV := hv1.symm
        subst hv1'
        have hvr' : vr = List.replicate kk emptyV := hvr.symm
        subst hvr'
        have hdproj : dsgoEv n (toS s) m0 m1 = some (toS s') := by
          rw [hs']
          exact dsgoEv_build (toS s) hf h0 h1 hse
        have hdpair : (dsgoGame n).pairE (toS s) ma mb
            = some (toS s') := by
          unfold dsgoGame
          simp only
          rw [hsl]
          exact hdproj
        have hproj' := SemiC.step hproj hcomm hdpair
        subst hs'
        refine ⟨hproj', ?_, hreach'⟩
        -- the new verdict is empty: the display is the legal
        -- classical position of the DSGo track
        obtain ⟨d', hshape', hmemb', hdisp', hlegal'⟩ :=
          (dsemiC_track hn hproj').track
        have hInv' := reach_invD (semiC_reach hproj')
        have hd' : d' ∈ (delta n s.next
            (placeJoint (execV n emptyV s.disp) s.next m0 m1) dec).2 :=
          (hmemb' d').mpr rfl
        have hdispc : IsClassical (delta n s.next
            (placeJoint (execV n emptyV s.disp) s.next m0 m1) dec).1 := by
          intro i hri
          exact hInv'.entClassical d' hd' i ((hdisp' i).symm.trans hri)
        have hver : verOf n s.next (delta n s.next
            (placeJoint (execV n emptyV s.disp) s.next m0 m1) dec).1
            = emptyV :=
          verOf_empty hdispc hInv'.wfdD hdisp' hlegal'
        show List.replicate kk emptyV ++ [verOf n s.next
          (delta n s.next
            (placeJoint (execV n emptyV s.disp) s.next m0 m1) dec).1]
          = List.replicate (kk+1) emptyV
        rw [hver]
        exact replicate_append_one kk emptyV

/-! ### The window -/

/-- Within distance j ≤ k, the state projects to a reachable DSGo
    state and the first k−j stored verdicts are still empty: every
    executed verdict in the window was stored by the generating
    semiclassical history. -/
theorem kwithin (hn : 2 ≤ n) {k j : Nat} {s : KState n}
    (h : WithinD (goGame n) (kGame n k) (rhoK n) j s) :
    j ≤ k →
    SimReach (dsgoGame n) (toS s)
    ∧ s.verdicts.length = k
    ∧ (∀ idx, idx < k - j → s.verdicts[idx]? = some emptyV) := by
  induction h with
  | base hsc =>
    intro _
    obtain ⟨hproj, hallq, -⟩ := ksemiC_project hn hsc
    refine ⟨semiC_reach hproj, ?_, ?_⟩
    · rw [hallq]
      exact List.length_replicate k emptyV
    · intro idx hidx
      rw [hallq, List.getElem?_replicate, if_pos (by omega : idx < k)]
  | @ofLe d s hw ih =>
    intro hj
    have hres := ih (Nat.le_of_succ_le hj)
    refine ⟨hres.1, hres.2.1, ?_⟩
    intro idx hidx
    exact hres.2.2 idx (by omega)
  | @step d s s' m0 m1 hw hpair ih =>
    intro hj
    have hres := ih (Nat.le_of_succ_le hj)
    obtain ⟨hdreach, hlen, hwin⟩ := hres
    unfold kGame at hpair
    simp only at hpair
    cases hsl : slotMoves m0 m1 with
    | none => rw [hsl] at hpair; cases hpair
    | some p =>
      rw [hsl] at hpair
      obtain ⟨mm0, mm1⟩ := p
      rcases kEv_cases hpair with ⟨hf, h0, h1, v1, vr, dec, hq', hse, hs'⟩
      have hv1 : v1 = emptyV := by
        have h00 := hwin 0 (by omega)
        rw [hq', List.getElem?_cons_zero] at h00
        exact Option.some.inj h00
      subst hv1
      have hdproj : dsgoEv n (toS s) mm0 mm1 = some (toS s') := by
        rw [hs']
        exact dsgoEv_build (toS s) hf h0 h1 hse
      have hdpair : (dsgoGame n).pairE (toS s) m0 m1
          = some (toS s') := by
        unfold dsgoGame
        simp only
        rw [hsl]
        exact hdproj
      have hdreach' := SimReach.step hdreach hdpair
      have hvl : vr.length + 1 = k := by
        have := hlen
        rw [hq', List.length_cons] at this
        exact this
      subst hs'
      refine ⟨hdreach', ?_, ?_⟩
      · show (vr ++ [verOf n s.next _]).length = k
        rw [List.length_append]
        simpa using hvl
      · intro idx hidx
        show (vr ++ [verOf n s.next _])[idx]? = some emptyV
        have hidx' : idx < vr.length := by omega
        rw [List.getElem?_append, if_pos hidx']
        have hnx := hwin (idx+1) (by omega)
        rw [hq', List.getElem?_cons_succ] at hnx
        exact hnx

/-- k-DSGo is faithful within distance k: within the window every
    state carries a reachable DSGo state's data, and DSGo is faithful
    everywhere. -/
theorem k_faithful_k (hn : 2 ≤ n) {k : Nat} :
    FaithfulWithin (goGame n) (kGame n k) (rhoK n) k := by
  intro s hw
  have hres := kwithin hn hw (Nat.le_refl k)
  exact dsgo_faithfulAt hres.1

/-! ### The naturality fields and the semiclassical field -/

theorem k_rho_init {k : Nat} :
    BSet.eqv (rhoK n (kGame n k).q0)
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

theorem k_nat_defined {k : Nat} {s : KState n} {ma mb : goMv.M}
    (hr : SimReach (kGame n k) s)
    (hp : ((kGame n k).pairE s ma mb).isSome) :
    simDefP (goGame n) (rhoK n s) ma mb := by
  rcases Option.isSome_iff_exists.mp hp with ⟨s', hs'⟩
  unfold kGame at hs'
  simp only at hs'
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hs'; cases hs'
  | some p =>
    rw [hsl] at hs'
    obtain ⟨m0, m1⟩ := p
    rcases kEv_cases hs' with ⟨hfin, hav0, hav1, -⟩
    have hInv := reach_invK hr
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

theorem k_nat_incl {k : Nat} {s s' : KState n} {ma mb : goMv.M}
    (hr : SimReach (kGame n k) s)
    (hst : (kGame n k).pairE s ma mb = some s') :
    BSet.sub (rhoK n s') (simVal (goGame n) (rhoK n s) ma mb) := by
  unfold kGame at hst
  simp only at hst
  cases hsl : slotMoves ma mb with
  | none => rw [hsl] at hst; cases hst
  | some p =>
    rw [hsl] at hst
    obtain ⟨m0, m1⟩ := p
    rcases kEv_cases hst with ⟨hfin, hav0, hav1, v1, vr, dec, hq, hse, hs'⟩
    have hInv := reach_invK hr
    have hb0 : ∀ i, m0 = some i → i < n*n := bounds_of_availD hav0
    have hb1 : ∀ i, m1 = some i → i < n*n := bounds_of_availD hav1
    have hwfp : WFD (placeJoint (execV n v1 s.disp) s.next m0 m1) :=
      placeJoint_wfd _ _ _ _ (execV_wfd v1 s.disp hInv.wfdD)
    obtain ⟨-, hself⟩ := delta_selfOut s.next
      (placeJoint (execV n v1 s.disp) s.next m0 m1) dec hwfp
    subst hs'
    intro z hz
    rcases hz with ⟨e, he, hze⟩
    have hedec : e ∈ dec := (hself e he).1
    rcases simEv_mem hse hedec with ⟨b, hb, l, hl, hel⟩
    by_cases hnn : m0 = none ∧ m1 = none
    · -- the double pass
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
    · -- a move turn
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

theorem k_semiclassical (hn : 2 ≤ n) {k : Nat} {s : KState n}
    {a : (goGame n).S} (h : SemiC (goGame n) (kGame n k) s a) :
    BSet.eqv (rhoK n s) (BSet.single a) :=
  dsgo_semiclassical hn (ksemiC_project hn h).1

/-- def_symmetrization, conditions 3 and 4: k-DSGo is a
    simultaneization of Go under the branch semantics. -/
theorem k_isSimultaneization (hn : 2 ≤ n) (k : Nat) :
    IsSimultaneization (goGame n) (kGame n k) (rhoK n) where
  rho_init := k_rho_init
  nat_defined := fun hr hp => k_nat_defined hr hp
  nat_incl := fun hr hst => k_nat_incl hr hst
  semiclassical := fun h => k_semiclassical hn h

/-- def_simplesymmetrization for k-DSGo: the all-black paint. -/
theorem k_isSimple {k : Nat} : IsSimple (goGame n) (kGame n k) := by
  intro s hr hnf hex
  have hInv := reach_invK hr
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

end SgoKNat
