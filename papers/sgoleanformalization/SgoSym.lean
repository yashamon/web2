/- SgoSym.lean — the main theorem, milestone 5b: the color-swap symmetry of
   the simultaneous games (SimSym), matching the printed def_symmetric.

   The paper's simultaneization state space is a SET of branches and
   its evolution a union over that set (lem_symmetric); so states are
   compared up to entanglement-set equality (sgoEqv/kEqv). The color
   swap reverses the two-branch list a collision emits, but that is
   invisible to set membership — which is exactly the union in the
   printed proof. swapState carries swapD over the display and every
   branch; R² = id holds exactly (swapD is elementwise), and the
   evolution commutes with the swap up to the set relation. -/
import SgoSwap
import SgoKNat

open SgoGo SgoDisplay SgoSerial SgoDelta SgoGames SgoInv SgoOK SgoBridge
  SgoNat SgoSemi SgoFaith SgoDInv SgoDOK SgoDNat SgoDSemi SgoKInv SgoKNat
  SgoSwap

namespace SgoSym

variable {n : Nat}

/-! ### Move and branch-step equivariance -/

theorem bStep_swap (d : Display n) (c : DKind) (mo : Option Nat) :
    bStep n (swapD d) c.opp mo = Option.map swapD (bStep n d c mo) := by
  cases mo with
  | none => rfl
  | some i => exact goMoveN_swapD d c i

theorem bStep2_swap (d : Display n) (c0 c1 : DKind) (x0 x1 : Option Nat) :
    bStep2 n (swapD d) c0.opp c1.opp x0 x1
      = Option.map swapD (bStep2 n d c0 c1 x0 x1) := by
  unfold bStep2
  rw [bStep_swap d c0 x0]
  cases h0 : bStep n d c0 x0 with
  | none => rfl
  | some d1 =>
    show bStep n (swapD d1) c1.opp x1 = Option.map swapD (bStep n d1 c1 x1)
    exact bStep_swap d1 c1 x1

theorem availD_swap (D : Display n) (m : Option Nat) :
    availD n (swapD D) m = availD n D m := by
  cases m with
  | none => rfl
  | some i =>
    show (decide (i < n*n) && !occD (swapD D) i) = (decide (i < n*n) && !occD D i)
    rw [occD_swapD]

/-! ### Compatibility is swap-invariant -/

theorem compatibleB_swap (D b : Display n) :
    compatibleB n (swapD D) (swapD b) = compatibleB n D b := by
  unfold compatibleB
  congr 1
  funext i
  rw [kindAt_swapD, kindAt_swapD]
  cases hkb : kindAt b i with
  | none => rfl
  | some kb =>
    cases hkd : kindAt D i with
    | none => rfl
    | some kd => cases kb <;> cases kd <;> rfl

/-! ### Serialization: swap-membership (the branch-list reversal is
    invisible to set membership) -/

theorem swapD_eq_swap (e y : Display n) : (e = swapD y) ↔ (swapD e = y) := by
  constructor
  · intro h; rw [h, swapD_swapD]
  · intro h; rw [← h, swapD_swapD]

theorem mem_dedup_pair (p q e : Display n) :
    e ∈ dedupD n [p, q] ↔ (e = p ∨ e = q) := by
  rw [mem_dedupD_iff]
  constructor
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  · rintro (h | h)
    · exact h ▸ List.mem_cons_self _ _
    · exact h ▸ List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

/-- The swap-membership of a two-branch serialization output: e is in
    the swapped output iff swapD e is in the original — the two
    branches may be listed in either order. -/
theorem pair_swap_mem (x y e : Display n) :
    (e ∈ dedupD n [swapD y, swapD x]) ↔ swapD e ∈ dedupD n [x, y] := by
  rw [mem_dedup_pair, mem_dedup_pair, swapD_eq_swap, swapD_eq_swap]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem serialP_swap (b : Display n) (m0 m1 : Option Nat) :
    (serialP n (swapD b) m1 m0).isSome = (serialP n b m0 m1).isSome
    ∧ ∀ l' l, serialP n (swapD b) m1 m0 = some l' →
        serialP n b m0 m1 = some l → ∀ e, e ∈ l' ↔ swapD e ∈ l := by
  have hX' : bStep2 n (swapD b) .b .w m1 m0
      = Option.map swapD (bStep2 n b .w .b m1 m0) := bStep2_swap b .w .b m1 m0
  have hY' : bStep2 n (swapD b) .w .b m0 m1
      = Option.map swapD (bStep2 n b .b .w m0 m1) := bStep2_swap b .b .w m0 m1
  have hBw' : bStep n (swapD b) .b m1
      = Option.map swapD (bStep n b .w m1) := bStep_swap b .w m1
  have hBb' : bStep n (swapD b) .w m0
      = Option.map swapD (bStep n b .b m0) := bStep_swap b .b m0
  cases hX : bStep2 n b .b .w m0 m1 with
  | some x =>
    cases hY : bStep2 n b .w .b m1 m0 with
    | some y =>
      refine ⟨by simp [serialP, hX, hY, hX', hY'], ?_⟩
      intro l' l hl' hl e
      have hlL : l = dedupD n [x, y] :=
        (Option.some.inj (by simpa [serialP, hX, hY] using hl)).symm
      have hlL' : l' = dedupD n [swapD y, swapD x] :=
        (Option.some.inj (by simpa [serialP, hX', hY', hX, hY] using hl')).symm
      rw [hlL, hlL']; exact pair_swap_mem x y e
    | none =>
      cases hBw : bStep n b .w m1 with
      | some yw =>
        refine ⟨by simp [serialP, hX, hY, hX', hY', hBw', hBw], ?_⟩
        intro l' l hl' hl e
        have hlL : l = dedupD n [x, yw] :=
          (Option.some.inj (by simpa [serialP, hX, hY, hBw] using hl)).symm
        have hlL' : l' = dedupD n [swapD yw, swapD x] :=
          (Option.some.inj (by simpa [serialP, hX', hY', hBw', hX, hY, hBw]
            using hl')).symm
        rw [hlL, hlL']; exact pair_swap_mem x yw e
      | none =>
        refine ⟨by simp [serialP, hX, hY, hX', hY', hBw', hBw], ?_⟩
        intro l' l hl' hl
        exact absurd hl (by simp [serialP, hX, hY, hBw])
  | none =>
    cases hY : bStep2 n b .w .b m1 m0 with
    | some y =>
      cases hBb : bStep n b .b m0 with
      | some xb =>
        refine ⟨by simp [serialP, hX, hY, hX', hY', hBb', hBb], ?_⟩
        intro l' l hl' hl e
        have hlL : l = dedupD n [xb, y] :=
          (Option.some.inj (by simpa [serialP, hX, hY, hBb] using hl)).symm
        have hlL' : l' = dedupD n [swapD y, swapD xb] :=
          (Option.some.inj (by simpa [serialP, hX', hY', hBb', hX, hY, hBb]
            using hl')).symm
        rw [hlL, hlL']; exact pair_swap_mem xb y e
      | none =>
        refine ⟨by simp [serialP, hX, hY, hX', hY', hBb', hBb], ?_⟩
        intro l' l hl' hl
        exact absurd hl (by simp [serialP, hX, hY, hBb])
    | none =>
      cases hBb : bStep n b .b m0 with
      | some xb =>
        cases hBw : bStep n b .w m1 with
        | some yw =>
          refine ⟨by simp [serialP, hX, hY, hX', hY', hBb', hBw', hBb, hBw], ?_⟩
          intro l' l hl' hl e
          have hlL : l = dedupD n [xb, yw] :=
            (Option.some.inj (by simpa [serialP, hX, hY, hBb, hBw] using hl)).symm
          have hlL' : l' = dedupD n [swapD yw, swapD xb] :=
            (Option.some.inj (by simpa
              [serialP, hX', hY', hBb', hBw', hX, hY, hBb, hBw] using hl')).symm
          rw [hlL, hlL']; exact pair_swap_mem xb yw e
        | none =>
          refine ⟨by simp [serialP, hX, hY, hX', hY', hBb', hBw', hBb, hBw], ?_⟩
          intro l' l hl' hl
          exact absurd hl (by simp [serialP, hX, hY, hBb, hBw])
      | none =>
        refine ⟨by simp [serialP, hX, hY, hX', hY', hBb', hBb], ?_⟩
        intro l' l hl' hl
        exact absurd hl (by simp [serialP, hX, hY, hBb])

/-! ### simEv: definedness and swap-membership -/

theorem isSome_map {α β : Type} (f : α → β) (o : Option α) :
    (Option.map f o).isSome = o.isSome := by cases o <;> rfl

theorem simEvAux_swap_isSome (ent : List (Display n)) (m0 m1 : Option Nat) :
    (simEvAux n m1 m0 (ent.map swapD)).isSome = (simEvAux n m0 m1 ent).isSome := by
  induction ent with
  | nil => rfl
  | cons b bs ih =>
    have hs : (serialP n (swapD b) m1 m0).isSome
        = (serialP n b m0 m1).isSome := (serialP_swap b m0 m1).1
    simp only [List.map_cons, simEvAux]
    cases hsp' : serialP n (swapD b) m1 m0 with
    | none =>
      have hsp : serialP n b m0 m1 = none := by
        cases hh : serialP n b m0 m1 with
        | none => rfl
        | some v => rw [hsp', hh] at hs; exact Bool.noConfusion hs
      simp [hsp]
    | some l' =>
      have hsp : (serialP n b m0 m1).isSome := by rw [← hs, hsp']; rfl
      rcases Option.isSome_iff_exists.mp hsp with ⟨l, hl⟩
      rw [hl]
      cases hr' : simEvAux n m1 m0 (bs.map swapD) with
      | none =>
        have hr : simEvAux n m0 m1 bs = none := by
          cases hh : simEvAux n m0 m1 bs with
          | none => rfl
          | some v => rw [hr', hh] at ih; exact Bool.noConfusion ih
        simp [hr]
      | some r' =>
        have hr : (simEvAux n m0 m1 bs).isSome := by rw [← ih, hr']; rfl
        rcases Option.isSome_iff_exists.mp hr with ⟨r, hr2⟩
        rw [hr2]; rfl

theorem simEv_swap_isSome (ent : List (Display n)) (m0 m1 : Option Nat) :
    (simEv n (ent.map swapD) m1 m0).isSome = (simEv n ent m0 m1).isSome := by
  unfold simEv
  rw [isSome_map, isSome_map]
  exact simEvAux_swap_isSome ent m0 m1

/-- Extract the pre-dedup output of a defined simEv. -/
theorem simEv_out {ent : List (Display n)} {m0 m1 : Option Nat}
    {bs : List (Display n)} (h : simEv n ent m0 m1 = some bs) :
    ∃ out, simEvAux n m0 m1 ent = some out ∧ bs = dedupD n out := by
  unfold simEv at h
  cases hax : simEvAux n m0 m1 ent with
  | none => rw [hax] at h; cases h
  | some out => rw [hax] at h; exact ⟨out, rfl, (Option.some.inj h).symm⟩

/-- The entanglement of the swapped evolution is the swapD-image, as a
    set: e is a swapped branch iff swapD e is an original branch. -/
theorem simEv_swap_mem {ent : List (Display n)} {m0 m1 : Option Nat}
    {bs bs' : List (Display n)} (hbs : simEv n ent m0 m1 = some bs)
    (hbs' : simEv n (ent.map swapD) m1 m0 = some bs') (e : Display n) :
    e ∈ bs' ↔ swapD e ∈ bs := by
  obtain ⟨out, hout, hbse⟩ := simEv_out hbs
  obtain ⟨out', hout', hbse'⟩ := simEv_out hbs'
  constructor
  · intro he
    rw [hbse', mem_dedupD_iff] at he
    -- e ∈ out': trace to a swapped branch's serialP
    have hmem := simEv_mem hbs' (by rw [hbse', mem_dedupD_iff]; exact he)
    rcases hmem with ⟨b', hb', l', hl', hel'⟩
    rcases List.mem_map.mp hb' with ⟨b, hb, hbb⟩
    subst hbb
    have hsp := serialP_swap b m0 m1
    have hspb : (serialP n b m0 m1).isSome := by rw [← hsp.1, hl']; rfl
    rcases Option.isSome_iff_exists.mp hspb with ⟨l, hl⟩
    have hswap : swapD e ∈ l := (hsp.2 l' l hl' hl e).mp hel'
    rw [hbse, mem_dedupD_iff]
    obtain ⟨out2, hout2, -⟩ := simEv_out hbs
    have : simEvAux n m0 m1 ent = some out := hout
    exact simEvAux_mem_of hout hb hl hswap
  · intro he
    have hmem := simEv_mem hbs he
    rcases hmem with ⟨b, hb, l, hl, hel⟩
    have hsp := serialP_swap b m0 m1
    have hspb : (serialP n (swapD b) m1 m0).isSome := by rw [hsp.1, hl]; rfl
    rcases Option.isSome_iff_exists.mp hspb with ⟨l', hl'⟩
    have hswap : e ∈ l' := (hsp.2 l' l hl' hl e).mpr hel
    rw [hbse', mem_dedupD_iff]
    exact simEvAux_mem_of hout' (List.mem_map.mpr ⟨b, hb, rfl⟩) hl' hswap

/-! ### The state swap and the slot swap -/

def swapState (s : SGoState n) : SGoState n :=
  ⟨swapD s.disp, s.next, s.ent.map swapD, s.final⟩

theorem swapState_swapState (s : SGoState n) : swapState (swapState s) = s := by
  show (⟨swapD (swapD s.disp), s.next, (s.ent.map swapD).map swapD, s.final⟩
    : SGoState n) = s
  have hd : swapD (swapD s.disp) = s.disp := swapD_swapD s.disp
  have he : (s.ent.map swapD).map swapD = s.ent := by
    rw [List.map_map, show (swapD ∘ swapD : Display n → Display n) = id from
      funext (fun x => swapD_swapD x), List.map_id]
  rw [hd, he]

theorem swapState_q0 : swapState (sgoGame n).q0 = (sgoGame n).q0 := by
  show (⟨swapD (emptyD n), 1, ([emptyD n]).map swapD, false⟩ : SGoState n)
    = initSGo n
  rw [swapD_emptyD]
  show (⟨emptyD n, 1, [swapD (emptyD n)], false⟩ : SGoState n) = initSGo n
  rw [swapD_emptyD]; rfl

theorem slotMoves_swap (m0 m1 : goMv.M) :
    slotMoves (swapMv m1) (swapMv m0)
      = (slotMoves m0 m1).map (fun p => (p.2, p.1)) := by
  cases m0 with
  | none =>
    cases m1 with
    | none => rfl
    | some wi => obtain ⟨w, i⟩ := wi; cases w <;> rfl
  | some wi0 =>
    obtain ⟨w0, i0⟩ := wi0
    cases m1 with
    | none => cases w0 <;> rfl
    | some wi1 =>
      obtain ⟨w1, i1⟩ := wi1
      cases w0 <;> cases w1 <;> rfl

/-! ### The evolution commutes with the swap up to set equality -/

theorem filter_map_swap_mem {D' : Display n} {bs bs' : List (Display n)}
    (hmem : ∀ f, f ∈ bs' ↔ swapD f ∈ bs) (e : Display n) :
    e ∈ (bs'.filter (compatibleB n (swapD D'))).map swapD
      ↔ e ∈ bs.filter (compatibleB n D') := by
  rw [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨f, hf, hef⟩
    rw [List.mem_filter] at hf
    subst hef
    refine ⟨(hmem f).mp hf.1, ?_⟩
    rw [← compatibleB_swap D' (swapD f), swapD_swapD]; exact hf.2
  · rintro ⟨hb, hc⟩
    refine ⟨swapD e, ?_, swapD_swapD e⟩
    rw [List.mem_filter]
    refine ⟨(hmem (swapD e)).mpr (by rw [swapD_swapD]; exact hb), ?_⟩
    rw [compatibleB_swap]; exact hc

/-- The move-branch of sgoEv commutes with the swap up to set
    equality: the display resolves equivariantly and the pruned
    entanglement is the swapD-image as a set. -/
theorem sgoEv_swap_move (s : SGoState n) (m0 m1 : Option Nat) :
    OptBRel (sgoGame n) (sgoEqv n)
      (Option.map swapState
        (match simEv n (s.ent.map swapD) m1 m0 with
          | none => none
          | some bs => some (⟨resolveTurn (swapD s.disp) s.next m1 m0,
              s.next + 1,
              bs.filter (compatibleB n (resolveTurn (swapD s.disp) s.next m1 m0)),
              false⟩ : SGoState n)))
      (match simEv n s.ent m0 m1 with
        | none => none
        | some bs => some (⟨resolveTurn s.disp s.next m0 m1, s.next + 1,
            bs.filter (compatibleB n (resolveTurn s.disp s.next m0 m1)),
            false⟩ : SGoState n)) := by
  cases hbs' : simEv n (s.ent.map swapD) m1 m0 with
  | none =>
    have hb : simEv n s.ent m0 m1 = none := by
      cases hh : simEv n s.ent m0 m1 with
      | none => rfl
      | some bs =>
        have hi := simEv_swap_isSome s.ent m0 m1
        rw [hbs', hh] at hi; exact Bool.noConfusion hi
    rw [hb]; trivial
  | some bs' =>
    have hbsome : (simEv n s.ent m0 m1).isSome := by
      have hi := simEv_swap_isSome s.ent m0 m1; rw [hbs'] at hi
      rw [← hi]; rfl
    rcases Option.isSome_iff_exists.mp hbsome with ⟨bs, hbs⟩
    rw [hbs]
    have hD : resolveTurn (swapD s.disp) s.next m1 m0
        = swapD (resolveTurn s.disp s.next m0 m1) := resolveTurn_swapD _ _ _ _
    show OptBRel (sgoGame n) (sgoEqv n)
      (some (swapState ⟨resolveTurn (swapD s.disp) s.next m1 m0, s.next + 1,
        bs'.filter (compatibleB n (resolveTurn (swapD s.disp) s.next m1 m0)),
        false⟩)) (some _)
    refine ⟨?_, rfl, rfl, ?_⟩
    · show swapD (resolveTurn (swapD s.disp) s.next m1 m0)
        = resolveTurn s.disp s.next m0 m1
      rw [hD, swapD_swapD]
    · intro e
      show e ∈ (bs'.filter (compatibleB n (resolveTurn (swapD s.disp) s.next m1 m0))).map swapD
        ↔ e ∈ bs.filter (compatibleB n (resolveTurn s.disp s.next m0 m1))
      rw [hD]
      exact filter_map_swap_mem (simEv_swap_mem hbs hbs') e

theorem sgoEv_swap (s : SGoState n) (mm0 mm1 : Option Nat) :
    OptBRel (sgoGame n) (sgoEqv n)
      (Option.map swapState (sgoEv n (swapState s) mm1 mm0))
      (sgoEv n s mm0 mm1) := by
  unfold sgoEv
  have hf : (swapState s).final = s.final := rfl
  have hd : (swapState s).disp = swapD s.disp := rfl
  have he : (swapState s).ent = s.ent.map swapD := rfl
  have hn : (swapState s).next = s.next := rfl
  have hda : availD n (swapD s.disp) mm1 = availD n s.disp mm1 :=
    availD_swap s.disp mm1
  have hdb : availD n (swapD s.disp) mm0 = availD n s.disp mm0 :=
    availD_swap s.disp mm0
  rw [hf, hd, he, hn, hda, hdb]
  by_cases hfin : s.final = true
  · rw [if_pos hfin, if_pos hfin]; trivial
  · rw [if_neg hfin, if_neg hfin]
    by_cases hav : (availD n s.disp mm0 && availD n s.disp mm1) = true
    · have hav' : (availD n s.disp mm1 && availD n s.disp mm0) = true := by
        rw [Bool.and_comm]; exact hav
      rw [if_neg (by rw [hav']; simp), if_neg (by rw [hav]; simp)]
      cases hm0 : mm0 with
      | none =>
        cases hm1 : mm1 with
        | none =>
          refine ⟨swapD_swapD s.disp, rfl, rfl, fun b => ?_⟩
          show b ∈ (s.ent.map swapD).map swapD ↔ b ∈ s.ent
          rw [List.map_map, show (swapD ∘ swapD : Display n → Display n) = id
            from funext (fun x => swapD_swapD x), List.map_id]
        | some i1 => exact sgoEv_swap_move s none (some i1)
      | some i0 =>
        cases hm1 : mm1 with
        | none => exact sgoEv_swap_move s (some i0) none
        | some i1 => exact sgoEv_swap_move s (some i0) (some i1)
    · have hav0 : (availD n s.disp mm0 && availD n s.disp mm1) = false := by
        cases h : (availD n s.disp mm0 && availD n s.disp mm1)
        · rfl
        · exact absurd h hav
      have hav1 : (availD n s.disp mm1 && availD n s.disp mm0) = false := by
        rw [Bool.and_comm]; exact hav0
      rw [if_pos (by rw [hav1]; rfl), if_pos (by rw [hav0]; rfl)]
      trivial

/-! ### Δ commutes with the swap (DSGo) -/

/-- M' is the swapD-image set of M. -/
def SetSwap (M' M : List (Display n)) : Prop := ∀ e, e ∈ M' ↔ swapD e ∈ M

theorem any_swap {M' M : List (Display n)} (h : SetSwap M' M) (i : Nat)
    (c : DKind) :
    (M'.any fun b => kindAt b i == some c)
      = (M.any fun b => kindAt b i == some c.opp) := by
  cases hL : M'.any (fun b => kindAt b i == some c) with
  | true =>
    rcases List.any_eq_true.mp hL with ⟨e, he, hke⟩
    refine (List.any_eq_true.mpr ⟨swapD e, (h e).mp he, ?_⟩).symm
    rw [beq_iff_eq] at hke ⊢
    rw [kindAt_swapD, hke]; rfl
  | false =>
    cases hR : M.any (fun b => kindAt b i == some c.opp) with
    | false => rfl
    | true =>
      rcases List.any_eq_true.mp hR with ⟨b, hb, hkb⟩
      have hb'M : swapD b ∈ M' := (h (swapD b)).mpr (by rw [swapD_swapD]; exact hb)
      have hke : (kindAt (swapD b) i == some c) = true := by
        rw [beq_iff_eq] at hkb ⊢
        rw [kindAt_swapD, hkb]
        show some (c.opp).opp = some c
        rw [opp_opp_all]
      rw [List.any_eq_true.mpr ⟨swapD b, hb'M, hke⟩] at hL
      exact absurd hL (by simp)

theorem evSet_swap {M' M : List (Display n)} (h : SetSwap M' M) (i : Nat) :
    evSet n M' i = ((evSet n M i).2, (evSet n M i).1) := by
  show ((M'.any fun b => kindAt b i == some .b),
    (M'.any fun b => kindAt b i == some .w)) = _
  rw [any_swap h i .b, any_swap h i .w]
  rfl

theorem deltaRound_swap {M' M : List (Display n)} (h : SetSwap M' M)
    (t : Nat) (D : Display n) :
    deltaRound n t M' (swapD D) = swapD (deltaRound n t M D) := by
  apply display_ext; apply Array.ext
  · show ((Array.range (n*n)).map _).size = (swapD _).cells.size
    rw [swapD_size]
    show ((Array.range (n*n)).map _).size = ((Array.range (n*n)).map _).size
    rw [Array.size_map, Array.size_map]
  · intro p hp1 hp2
    have hib : p < n*n := by
      have hsz : (deltaRound n t M' (swapD D)).cells.size = n*n := by
        unfold deltaRound; rw [Array.size_map, Array.size_range]
      rw [hsz] at hp1; exact hp1
    rw [← get_in_bounds _ p hp1, ← get_in_bounds _ p hp2, swapD_get]
    show (deltaRound n t M' (swapD D)).get p = swapCell ((deltaRound n t M D).get p)
    unfold deltaRound
    rw [get_map_range, get_map_range, if_pos hib, if_pos hib, swapD_get,
      evSet_swap h p]
    cases hg : D.get p with
    | none => rfl
    | some c =>
      obtain ⟨k, st⟩ := c
      cases hev : evSet n M p with
      | mk hb hw =>
        cases k with
        | b => cases hb <;> cases hw <;> rfl
        | w => cases hb <;> cases hw <;> rfl
        | r =>
          cases hb <;> cases hw <;>
            (by_cases hst : (st == t) = true <;> simp [hst, swapCell])

theorem recut_swap {M' M : List (Display n)} (h : SetSwap M' M)
    (D : Display n) :
    SetSwap (recut n (swapD D) M') (recut n D M) := by
  intro e
  unfold recut
  rw [List.mem_filter, List.mem_filter]
  have hpe : ((allIdx n).all fun i => occD (swapD D) i || kindAt e i == none)
      = ((allIdx n).all fun i => occD D i || kindAt (swapD e) i == none) := by
    congr 1
    funext i
    rw [occD_swapD, kindAt_swapD]
    cases hh : kindAt e i with
    | none => rfl
    | some kk => cases kk <;> rfl
  rw [hpe]
  exact and_congr (h e) Iff.rfl

theorem deltaAux_swap (t fuel : Nat) :
    ∀ (D : Display n) (M' M : List (Display n)), SetSwap M' M →
    (deltaAux n t fuel (swapD D) M').1 = swapD (deltaAux n t fuel D M).1
    ∧ SetSwap (deltaAux n t fuel (swapD D) M').2 (deltaAux n t fuel D M).2 := by
  induction fuel with
  | zero => intro D M' M h; exact ⟨rfl, h⟩
  | succ fuel ih =>
    intro D M' M h
    have hunf' : deltaAux n t (fuel+1) (swapD D) M'
        = if (deltaRound n t M' (swapD D) == swapD D) = true
          then (deltaRound n t M' (swapD D), recut n (deltaRound n t M' (swapD D)) M')
          else deltaAux n t fuel (deltaRound n t M' (swapD D))
            (recut n (deltaRound n t M' (swapD D)) M') := rfl
    have hunf : deltaAux n t (fuel+1) D M
        = if (deltaRound n t M D == D) = true
          then (deltaRound n t M D, recut n (deltaRound n t M D) M)
          else deltaAux n t fuel (deltaRound n t M D)
            (recut n (deltaRound n t M D) M) := rfl
    rw [hunf', hunf, deltaRound_swap h, swapD_beq]
    by_cases htest : (deltaRound n t M D == D) = true
    · rw [if_pos htest, if_pos htest]
      exact ⟨rfl, recut_swap h (deltaRound n t M D)⟩
    · rw [if_neg htest, if_neg htest]
      exact ih (deltaRound n t M D) _ _ (recut_swap h (deltaRound n t M D))

theorem delta_swap (t : Nat) (D : Display n) (M' M : List (Display n))
    (h : SetSwap M' M) :
    (delta n t (swapD D) M').1 = swapD (delta n t D M).1
    ∧ SetSwap (delta n t (swapD D) M').2 (delta n t D M).2 :=
  deltaAux_swap t (2*(n*n)+2) D M' M h

/-! ### DSGo evolution and symmetry -/

theorem dsgoEv_swap (s : SGoState n) (mm0 mm1 : Option Nat) :
    OptBRel (dsgoGame n) (sgoEqv n)
      (Option.map swapState (dsgoEv n (swapState s) mm1 mm0))
      (dsgoEv n s mm0 mm1) := by
  unfold dsgoEv
  have hf : (swapState s).final = s.final := rfl
  have hd : (swapState s).disp = swapD s.disp := rfl
  have he : (swapState s).ent = s.ent.map swapD := rfl
  have hn : (swapState s).next = s.next := rfl
  rw [hf, hd, he, hn, availD_swap s.disp mm1, availD_swap s.disp mm0]
  by_cases hfin : s.final = true
  · rw [if_pos hfin, if_pos hfin]; trivial
  · rw [if_neg hfin, if_neg hfin]
    by_cases hav : (availD n s.disp mm0 && availD n s.disp mm1) = true
    · have hav' : (availD n s.disp mm1 && availD n s.disp mm0) = true := by
        rw [Bool.and_comm]; exact hav
      rw [if_neg (by rw [hav']; simp), if_neg (by rw [hav]; simp)]
      -- both defined ↔; case on the decoherence
      cases hdec' : simEv n (s.ent.map swapD) mm1 mm0 with
      | none =>
        have hb : simEv n s.ent mm0 mm1 = none := by
          cases hh : simEv n s.ent mm0 mm1 with
          | none => rfl
          | some d =>
            have hi := simEv_swap_isSome s.ent mm0 mm1
            rw [hdec', hh] at hi; exact Bool.noConfusion hi
        rw [hb]; trivial
      | some dec' =>
        have hbsome : (simEv n s.ent mm0 mm1).isSome := by
          have hi := simEv_swap_isSome s.ent mm0 mm1; rw [hdec'] at hi
          rw [← hi]; rfl
        rcases Option.isSome_iff_exists.mp hbsome with ⟨dec, hdec⟩
        rw [hdec]
        have hsm : SetSwap dec' dec := simEv_swap_mem hdec hdec'
        have hpj : placeJoint (swapD s.disp) s.next mm1 mm0
            = swapD (placeJoint s.disp s.next mm0 mm1) :=
          placeJoint_swapD s.disp s.next mm0 mm1
        rw [hpj]
        have hdel := delta_swap s.next (placeJoint s.disp s.next mm0 mm1)
          dec' dec hsm
        refine ⟨?_, rfl, ?_, ?_⟩
        · show swapD (delta n s.next
              (swapD (placeJoint s.disp s.next mm0 mm1)) dec').1
            = (delta n s.next (placeJoint s.disp s.next mm0 mm1) dec).1
          rw [hdel.1, swapD_swapD]
        · show (mm1.isNone && mm0.isNone) = (mm0.isNone && mm1.isNone)
          rw [Bool.and_comm]
        · intro e
          show e ∈ (delta n s.next
              (swapD (placeJoint s.disp s.next mm0 mm1)) dec').2.map swapD
            ↔ e ∈ (delta n s.next (placeJoint s.disp s.next mm0 mm1) dec).2
          rw [List.mem_map]
          constructor
          · rintro ⟨f, hf2, hef⟩
            subst hef
            exact (hdel.2 f).mp hf2
          · intro hb
            exact ⟨swapD e, (hdel.2 (swapD e)).mpr (by rw [swapD_swapD]; exact hb),
              swapD_swapD e⟩
    · have hav0 : (availD n s.disp mm0 && availD n s.disp mm1) = false := by
        cases hh : (availD n s.disp mm0 && availD n s.disp mm1)
        · rfl
        · exact absurd hh hav
      have hav1 : (availD n s.disp mm1 && availD n s.disp mm0) = false := by
        rw [Bool.and_comm]; exact hav0
      rw [if_pos (by rw [hav1]; rfl), if_pos (by rw [hav0]; rfl)]
      trivial

/-- The display-read availability is swap invariant (the single-move
    clause of def_symmetric), for the SGo/DSGo state type. -/
theorem avail_swap (s : SGoState n) (m : goMv.M) :
    ((swapState s).final = false ∧
      (swapMv m = none ∨ ∃ w i, swapMv m = some (w, i) ∧ i < n*n ∧
        occD (swapState s).disp i = false)) ↔
    (s.final = false ∧
      (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧ occD s.disp i = false)) := by
  have hf : (swapState s).final = s.final := rfl
  have hd : (swapState s).disp = swapD s.disp := rfl
  rw [hf, hd]
  cases m with
  | none => exact ⟨fun ⟨h1, _⟩ => ⟨h1, Or.inl rfl⟩, fun ⟨h1, _⟩ => ⟨h1, Or.inl rfl⟩⟩
  | some wi =>
    obtain ⟨w, i⟩ := wi
    show (s.final = false ∧ (some (!w, i) = none ∨ ∃ w' i', some (!w, i) = some (w', i') ∧
        i' < n*n ∧ occD (swapD s.disp) i' = false)) ↔ _
    constructor
    · rintro ⟨h1, h | ⟨w', i', he, hi, ho⟩⟩
      · cases h
      · refine ⟨h1, Or.inr ⟨w, i, rfl, ?_, ?_⟩⟩
        · cases he; exact hi
        · cases he; rw [occD_swapD] at ho; exact ho
    · rintro ⟨h1, h | ⟨w', i', he, hi, ho⟩⟩
      · cases h
      · refine ⟨h1, Or.inr ⟨!w, i, rfl, ?_, ?_⟩⟩
        · cases he; exact hi
        · cases he; rw [occD_swapD]; exact ho

theorem dsgo_simSym : SimSym (dsgoGame n) (sgoEqv n) := by
  refine ⟨swapMv, swapState, swapMv_swapMv, swapMv_pass, swapMv_deg,
    swapState_swapState, swapState_q0, fun s => Iff.rfl, avail_swap, ?_⟩
  intro s m0 m1
  show OptBRel (dsgoGame n) (sgoEqv n)
    (Option.map swapState ((slotMoves (swapMv m1) (swapMv m0)).bind
      (fun p => dsgoEv n (swapState s) p.1 p.2)))
    ((slotMoves m0 m1).bind (fun p => dsgoEv n s p.1 p.2))
  rw [slotMoves_swap]
  cases hsl : slotMoves m0 m1 with
  | none => trivial
  | some p =>
    obtain ⟨mm0, mm1⟩ := p
    exact dsgoEv_swap s mm0 mm1

/-! ### k-DSGo: verdict swap -/

def swapVerdict (v : Verdict) : Verdict :=
  ⟨v.removals, v.recolors.map (fun p => (p.1, p.2.1, p.2.2.opp))⟩

theorem swapVerdict_swapVerdict (v : Verdict) :
    swapVerdict (swapVerdict v) = v := by
  unfold swapVerdict
  simp only [List.map_map]
  show (⟨v.removals, v.recolors.map (fun p => (p.1, p.2.1, p.2.2.opp.opp))⟩
    : Verdict) = v
  rw [show (fun p : Nat × Nat × DKind => (p.1, p.2.1, p.2.2.opp.opp))
    = (fun p => p) from funext (fun p => by rw [opp_opp_all])]
  simp

theorem foldl_swap {α : Type} (g : Display n → α → Display n)
    (comm : ∀ (A : Display n) (a : α), g (swapD A) a = swapD (g A a))
    (l : List α) (A : Display n) :
    List.foldl g (swapD A) l = swapD (List.foldl g A l) := by
  induction l generalizing A with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, comm A a, ih]

theorem foldl_swap_hom {α : Type} (g : Display n → α → Display n) (φ : α → α)
    (comm : ∀ (A : Display n) (a : α), g (swapD A) (φ a) = swapD (g A a))
    (l : List α) (A : Display n) :
    List.foldl g (swapD A) (l.map φ) = swapD (List.foldl g A l) := by
  induction l generalizing A with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldl_cons, comm A a, ih]

def removeStep (A : Display n) (pr : Nat × Nat) : Display n :=
  match A.get pr.1 with
  | some (_, st') => if st' == pr.2 then A.set pr.1 none else A
  | none => A

def recolorStep (A : Display n) (pr : Nat × Nat × DKind) : Display n :=
  match A.get pr.1 with
  | some (_, st') => if st' == pr.2.1 then A.set pr.1 (some (pr.2.2, st')) else A
  | none => A

theorem execV_eq (v : Verdict) (D : Display n) :
    execV n v D = v.recolors.foldl recolorStep (v.removals.foldl removeStep D) :=
  rfl

theorem removeStep_swap (A : Display n) (a : Nat × Nat) :
    removeStep (swapD A) a = swapD (removeStep A a) := by
  obtain ⟨i, st⟩ := a
  show (match (swapD A).get i with
    | some (_, st') => if st' == st then (swapD A).set i none else swapD A
    | none => swapD A) = swapD (removeStep A (i, st))
  rw [swapD_get]
  unfold removeStep
  cases hg : A.get i with
  | none => rfl
  | some cc =>
    obtain ⟨k, st'⟩ := cc
    by_cases hst : (st' == st) = true
    · simp [swapCell, swapD_set, hst]
    · simp [swapCell, hst]

theorem recolorStep_swap (A : Display n) (a : Nat × Nat × DKind) :
    recolorStep (swapD A) (a.1, a.2.1, a.2.2.opp) = swapD (recolorStep A a) := by
  obtain ⟨i, st, c⟩ := a
  show (match (swapD A).get i with
    | some (_, st') => if st' == st then (swapD A).set i (some (c.opp, st')) else swapD A
    | none => swapD A) = swapD (recolorStep A (i, st, c))
  rw [swapD_get]
  unfold recolorStep
  cases hg : A.get i with
  | none => rfl
  | some cc =>
    obtain ⟨k, st'⟩ := cc
    by_cases hst : (st' == st) = true
    · simp [swapCell, swapD_set, hst]
    · simp [swapCell, hst]

theorem execV_swap (v : Verdict) (D : Display n) :
    execV n (swapVerdict v) (swapD D) = swapD (execV n v D) := by
  rw [execV_eq, execV_eq]
  show (v.recolors.map (fun p => (p.1, p.2.1, p.2.2.opp))).foldl recolorStep
      (v.removals.foldl removeStep (swapD D))
    = swapD (v.recolors.foldl recolorStep (v.removals.foldl removeStep D))
  rw [foldl_swap removeStep removeStep_swap v.removals D]
  rw [foldl_swap_hom recolorStep (fun p => (p.1, p.2.1, p.2.2.opp))
    recolorStep_swap v.recolors (v.removals.foldl removeStep D)]

theorem orOp_swap (t : Nat) (D : Display n) :
    orOp n t (swapD D) = swapD (orOp n t D) := by
  unfold orOp
  exact stages_swapD (t+1) D t

theorem verOf_swap (t : Nat) (D : Display n) :
    verOf n t (swapD D) = swapVerdict (verOf n t D) := by
  have hrem : ((allIdx n).filterMap (fun i => match (swapD D).get i with
        | some (_, st) => if occD (orOp n t (swapD D)) i then none else some (i, st)
        | none => none))
      = ((allIdx n).filterMap (fun i => match D.get i with
        | some (_, st) => if occD (orOp n t D) i then none else some (i, st)
        | none => none)) := by
    apply congrArg (List.filterMap · (allIdx n))
    funext i
    rw [swapD_get, orOp_swap, occD_swapD]
    cases hg : D.get i with
    | none => rfl
    | some c => obtain ⟨k, st⟩ := c; rfl
  have hrec : ((allIdx n).filterMap (fun i =>
        match (swapD D).get i, (orOp n t (swapD D)).get i with
        | some (.r, st), some (k, _) => if k != .r then some (i, st, k) else none
        | _, _ => none))
      = (((allIdx n).filterMap (fun i => match D.get i, (orOp n t D).get i with
        | some (.r, st), some (k, _) => if k != .r then some (i, st, k) else none
        | _, _ => none)).map (fun p => (p.1, p.2.1, p.2.2.opp))) := by
    rw [List.map_filterMap]
    apply congrArg (List.filterMap · (allIdx n))
    funext i
    rw [swapD_get, orOp_swap, swapD_get]
    cases hg : D.get i with
    | none => rfl
    | some c =>
      obtain ⟨k, st⟩ := c
      cases hor : (orOp n t D).get i with
      | none => cases k <;> rfl
      | some c2 =>
        obtain ⟨k2, st2⟩ := c2
        cases k <;> cases k2 <;> rfl
  show (⟨(allIdx n).filterMap (fun i => match (swapD D).get i with
        | some (_, st) => if occD (orOp n t (swapD D)) i then none else some (i, st)
        | none => none),
      (allIdx n).filterMap (fun i =>
        match (swapD D).get i, (orOp n t (swapD D)).get i with
        | some (.r, st), some (k, _) => if k != .r then some (i, st, k) else none
        | _, _ => none)⟩ : Verdict)
    = ⟨(allIdx n).filterMap (fun i => match D.get i with
        | some (_, st) => if occD (orOp n t D) i then none else some (i, st)
        | none => none),
      ((allIdx n).filterMap (fun i => match D.get i, (orOp n t D).get i with
        | some (.r, st), some (k, _) => if k != .r then some (i, st, k) else none
        | _, _ => none)).map (fun p => (p.1, p.2.1, p.2.2.opp))⟩
  rw [hrem, hrec]

/-! ### k-DSGo state swap and symmetry -/

def swapKState (s : KState n) : KState n :=
  ⟨swapD s.disp, s.next, s.ent.map swapD, s.verdicts.map swapVerdict, s.final⟩

theorem swapKState_swapKState (s : KState n) : swapKState (swapKState s) = s := by
  show (⟨swapD (swapD s.disp), s.next, (s.ent.map swapD).map swapD,
    (s.verdicts.map swapVerdict).map swapVerdict, s.final⟩ : KState n) = s
  have hd : swapD (swapD s.disp) = s.disp := swapD_swapD s.disp
  have he : (s.ent.map swapD).map swapD = s.ent := by
    rw [List.map_map, show (swapD ∘ swapD : Display n → Display n) = id from
      funext swapD_swapD, List.map_id]
  have hv : (s.verdicts.map swapVerdict).map swapVerdict = s.verdicts := by
    rw [List.map_map, show (swapVerdict ∘ swapVerdict : Verdict → Verdict) = id
      from funext swapVerdict_swapVerdict, List.map_id]
  rw [hd, he, hv]

theorem swapKState_q0 {k : Nat} : swapKState (kGame n k).q0 = (kGame n k).q0 := by
  show (⟨swapD (emptyD n), 1, ([emptyD n]).map swapD,
    (List.replicate k emptyV).map swapVerdict, false⟩ : KState n) = initK n k
  rw [swapD_emptyD]
  show (⟨emptyD n, 1, [swapD (emptyD n)],
    (List.replicate k emptyV).map swapVerdict, false⟩ : KState n) = initK n k
  rw [swapD_emptyD, List.map_replicate,
    show swapVerdict emptyV = emptyV from rfl]; rfl

theorem kEv_swap {k : Nat} (s : KState n) (mm0 mm1 : Option Nat) :
    OptBRel (kGame n k) (kEqv n)
      (Option.map swapKState (kEv n (swapKState s) mm1 mm0))
      (kEv n s mm0 mm1) := by
  unfold kEv
  have hf : (swapKState s).final = s.final := rfl
  have hd : (swapKState s).disp = swapD s.disp := rfl
  have he : (swapKState s).ent = s.ent.map swapD := rfl
  have hn : (swapKState s).next = s.next := rfl
  have hq : (swapKState s).verdicts = s.verdicts.map swapVerdict := rfl
  rw [hf, hd, he, hn, hq, availD_swap s.disp mm1, availD_swap s.disp mm0]
  by_cases hfin : s.final = true
  · rw [if_pos hfin, if_pos hfin]; trivial
  · rw [if_neg hfin, if_neg hfin]
    by_cases hav : (availD n s.disp mm0 && availD n s.disp mm1) = true
    · have hav' : (availD n s.disp mm1 && availD n s.disp mm0) = true := by
        rw [Bool.and_comm]; exact hav
      rw [if_neg (by rw [hav']; simp), if_neg (by rw [hav]; simp)]
      cases hvq : s.verdicts with
      | nil => rw [List.map_nil]; trivial
      | cons v1 vrest =>
        rw [List.map_cons]
        cases hdec' : simEv n (s.ent.map swapD) mm1 mm0 with
        | none =>
          have hb : simEv n s.ent mm0 mm1 = none := by
            cases hh : simEv n s.ent mm0 mm1 with
            | none => rfl
            | some d =>
              have hi := simEv_swap_isSome s.ent mm0 mm1
              rw [hdec', hh] at hi; exact Bool.noConfusion hi
          rw [hb]; trivial
        | some dec' =>
          have hbsome : (simEv n s.ent mm0 mm1).isSome := by
            have hi := simEv_swap_isSome s.ent mm0 mm1; rw [hdec'] at hi
            rw [← hi]; rfl
          rcases Option.isSome_iff_exists.mp hbsome with ⟨dec, hdec⟩
          rw [hdec]
          dsimp only
          have hsm : SetSwap dec' dec := simEv_swap_mem hdec hdec'
          have hpj : placeJoint (execV n (swapVerdict v1) (swapD s.disp)) s.next mm1 mm0
              = swapD (placeJoint (execV n v1 s.disp) s.next mm0 mm1) := by
            rw [execV_swap, placeJoint_swapD]
          rw [hpj]
          have hdel := delta_swap s.next
            (placeJoint (execV n v1 s.disp) s.next mm0 mm1) dec' dec hsm
          refine ⟨?_, rfl, ?_, ?_, ?_⟩
          · show swapD (delta n s.next
                (swapD (placeJoint (execV n v1 s.disp) s.next mm0 mm1)) dec').1
              = (delta n s.next (placeJoint (execV n v1 s.disp) s.next mm0 mm1) dec).1
            rw [hdel.1, swapD_swapD]
          · show (mm1.isNone && mm0.isNone) = (mm0.isNone && mm1.isNone)
            rw [Bool.and_comm]
          · show (vrest.map swapVerdict ++ [verOf n s.next (delta n s.next
                (swapD (placeJoint (execV n v1 s.disp) s.next mm0 mm1)) dec').1]).map
                swapVerdict
              = vrest ++ [verOf n s.next
                (delta n s.next (placeJoint (execV n v1 s.disp) s.next mm0 mm1) dec).1]
            rw [hdel.1, verOf_swap, List.map_append, List.map_map,
              show (swapVerdict ∘ swapVerdict : Verdict → Verdict) = id from
                funext swapVerdict_swapVerdict, List.map_id, List.map_cons,
              List.map_nil, swapVerdict_swapVerdict]
          · intro e
            show e ∈ (delta n s.next
                (swapD (placeJoint (execV n v1 s.disp) s.next mm0 mm1)) dec').2.map swapD
              ↔ e ∈ (delta n s.next
                (placeJoint (execV n v1 s.disp) s.next mm0 mm1) dec).2
            rw [List.mem_map]
            constructor
            · rintro ⟨f, hf2, hef⟩; subst hef; exact (hdel.2 f).mp hf2
            · intro hb
              exact ⟨swapD e, (hdel.2 (swapD e)).mpr (by rw [swapD_swapD]; exact hb),
                swapD_swapD e⟩
    · have hav0 : (availD n s.disp mm0 && availD n s.disp mm1) = false := by
        cases hh : (availD n s.disp mm0 && availD n s.disp mm1)
        · rfl
        · exact absurd hh hav
      have hav1 : (availD n s.disp mm1 && availD n s.disp mm0) = false := by
        rw [Bool.and_comm]; exact hav0
      rw [if_pos (by rw [hav1]; rfl), if_pos (by rw [hav0]; rfl)]
      trivial

/-- The same for the k-DSGo state type. -/
theorem availK_swap (s : KState n) (m : goMv.M) :
    ((swapKState s).final = false ∧
      (swapMv m = none ∨ ∃ w i, swapMv m = some (w, i) ∧ i < n*n ∧
        occD (swapKState s).disp i = false)) ↔
    (s.final = false ∧
      (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧ occD s.disp i = false)) := by
  have hf : (swapKState s).final = s.final := rfl
  have hd : (swapKState s).disp = swapD s.disp := rfl
  rw [hf, hd]
  cases m with
  | none => exact ⟨fun ⟨h1, _⟩ => ⟨h1, Or.inl rfl⟩, fun ⟨h1, _⟩ => ⟨h1, Or.inl rfl⟩⟩
  | some wi =>
    obtain ⟨w, i⟩ := wi
    show (s.final = false ∧ (some (!w, i) = none ∨ ∃ w' i', some (!w, i) = some (w', i') ∧
        i' < n*n ∧ occD (swapD s.disp) i' = false)) ↔ _
    constructor
    · rintro ⟨h1, h | ⟨w', i', he, hi, ho⟩⟩
      · cases h
      · refine ⟨h1, Or.inr ⟨w, i, rfl, ?_, ?_⟩⟩
        · cases he; exact hi
        · cases he; rw [occD_swapD] at ho; exact ho
    · rintro ⟨h1, h | ⟨w', i', he, hi, ho⟩⟩
      · cases h
      · refine ⟨h1, Or.inr ⟨!w, i, rfl, ?_, ?_⟩⟩
        · cases he; exact hi
        · cases he; rw [occD_swapD]; exact ho

theorem k_simSym (k : Nat) : SimSym (kGame n k) (kEqv n) := by
  refine ⟨swapMv, swapKState, swapMv_swapMv, swapMv_pass, swapMv_deg,
    swapKState_swapKState, swapKState_q0, fun s => Iff.rfl, availK_swap, ?_⟩
  intro s m0 m1
  show OptBRel (kGame n k) (kEqv n)
    (Option.map swapKState ((slotMoves (swapMv m1) (swapMv m0)).bind
      (fun p => kEv n (swapKState s) p.1 p.2)))
    ((slotMoves m0 m1).bind (fun p => kEv n s p.1 p.2))
  rw [slotMoves_swap]
  cases hsl : slotMoves m0 m1 with
  | none => trivial
  | some p =>
    obtain ⟨mm0, mm1⟩ := p
    exact kEv_swap s mm0 mm1

/-- SGo is symmetric (def_symmetric), up to entanglement-set equality. -/
theorem sgo_simSym : SimSym (sgoGame n) (sgoEqv n) := by
  refine ⟨swapMv, swapState, swapMv_swapMv, swapMv_pass, swapMv_deg,
    swapState_swapState, swapState_q0, fun s => Iff.rfl, avail_swap, ?_⟩
  intro s m0 m1
  show OptBRel (sgoGame n) (sgoEqv n)
    (Option.map swapState ((slotMoves (swapMv m1) (swapMv m0)).bind
      (fun p => sgoEv n (swapState s) p.1 p.2)))
    ((slotMoves m0 m1).bind (fun p => sgoEv n s p.1 p.2))
  rw [slotMoves_swap]
  cases hsl : slotMoves m0 m1 with
  | none => trivial
  | some p =>
    obtain ⟨mm0, mm1⟩ := p
    show OptBRel (sgoGame n) (sgoEqv n)
      (Option.map swapState (sgoEv n (swapState s) mm1 mm0))
      (sgoEv n s mm0 mm1)
    exact sgoEv_swap s mm0 mm1

end SgoSym
