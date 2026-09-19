/- SgoDyn.lean — lem_dynamics: the faithfulness radii and the radius
   spectrum are dynamical isomorphism invariants.

   A dynamical isomorphism φ (SeqIso) is a bijection of the graded
   moves and of the core states intertwining the action of the non
   pass moves, the initial cores and the cores ended by play — the
   printed hypothesis. Extended to the states (φS), it intertwines the
   evolution, the pass, the finals and the position normal form (part
   (1): sE_iso, fM_pass, sfinal_iso, sN_iso), hence #, P and Sim.

   Renaming the moves of a simultaneization H of G0 along φ gives
   renameSim φ H over G0', with the branch semantics renameRho φ ρ
   (part (2)): the conditions of def_symmetrization, def_simultaneous,
   def_symmetric, faithfulness within every distance and simplicity
   transport (each an iff). Part (3): the spectra coincide
   (lem_dynamics_3), the spectrum being the set of realized radii
   (InSpectrum: radius exactly d, or faithful within every distance).

   Statement audit: the scoring partition of the final states is not
   carried by the formalization; the printed clause "the spectrum is
   independent of the scoring" therefore has no formal counterpart —
   no formal notion reads a partition. -/
import SgoInst
import SgoSim

namespace SgoGames

attribute [local instance] Classical.propDecidable

variable {Mv Mv' : Moves}

/-! ### Dynamical isomorphisms -/

/-- lem_dynamics' hypothesis: bijections of the graded moves and of the
    core states, intertwining the action of the non pass moves, the
    initial core states and the core states ended by play. -/
structure SeqIso (G0 : SeqGame Mv) (G0' : SeqGame Mv') where
  fM : Mv.M → Mv'.M
  gM : Mv'.M → Mv.M
  gfM : ∀ m, gM (fM m) = m
  fgM : ∀ m', fM (gM m') = m'
  deg0 : ∀ m, Mv.deg0 m ↔ Mv'.deg0 (fM m)
  deg1 : ∀ m, Mv.deg1 m ↔ Mv'.deg1 (fM m)
  fC : G0.C → G0'.C
  gC : G0'.C → G0.C
  gfC : ∀ c, gC (fC c) = c
  fgC : ∀ c', fC (gC c') = c'
  q0 : fC G0.q0 = G0'.q0
  ended : ∀ c, G0'.ended (fC c) ↔ G0.ended c
  mv : ∀ c m, m ≠ Mv.pass → Option.map fC (G0.mv c m) = G0'.mv (fC c) (fM m)

variable {G0 : SeqGame Mv} {G0' : SeqGame Mv'}

namespace SeqIso

/-- The pass goes to the pass: it is the sole doubly graded move. -/
theorem fM_pass (φ : SeqIso G0 G0') : φ.fM Mv.pass = Mv'.pass :=
  Mv'.pass_unique _ ((φ.deg0 _).mp Mv.pass_deg0) ((φ.deg1 _).mp Mv.pass_deg1)

theorem gM_pass (φ : SeqIso G0 G0') : φ.gM Mv'.pass = Mv.pass := by
  have := congrArg φ.gM φ.fM_pass
  rw [φ.gfM] at this
  exact this.symm

theorem fM_eq_pass_iff (φ : SeqIso G0 G0') (m : Mv.M) :
    φ.fM m = Mv'.pass ↔ m = Mv.pass := by
  constructor
  · intro h
    have := congrArg φ.gM h
    rw [φ.gfM, φ.gM_pass] at this
    exact this
  · intro h; rw [h, φ.fM_pass]

theorem gM_eq_pass_iff (φ : SeqIso G0 G0') (m' : Mv'.M) :
    φ.gM m' = Mv.pass ↔ m' = Mv'.pass := by
  constructor
  · intro h
    have := congrArg φ.fM h
    rw [φ.fgM, φ.fM_pass] at this
    exact this
  · intro h; rw [h, φ.gM_pass]

theorem deg0' (φ : SeqIso G0 G0') (m' : Mv'.M) : Mv'.deg0 m' ↔ Mv.deg0 (φ.gM m') := by
  have := φ.deg0 (φ.gM m')
  rw [φ.fgM] at this
  exact this.symm

theorem deg1' (φ : SeqIso G0 G0') (m' : Mv'.M) : Mv'.deg1 m' ↔ Mv.deg1 (φ.gM m') := by
  have := φ.deg1 (φ.gM m')
  rw [φ.fgM] at this
  exact this.symm

/-- The inverse isomorphism. -/
def symm (φ : SeqIso G0 G0') : SeqIso G0' G0 where
  fM := φ.gM
  gM := φ.fM
  gfM := φ.fgM
  fgM := φ.gfM
  deg0 := φ.deg0'
  deg1 := φ.deg1'
  fC := φ.gC
  gC := φ.fC
  gfC := φ.fgC
  fgC := φ.gfC
  q0 := by
    have := congrArg φ.gC φ.q0
    rw [φ.gfC] at this
    exact this.symm
  ended := fun c' => by
    have := φ.ended (φ.gC c')
    rw [φ.fgC] at this
    exact this.symm
  mv := fun c' m' hm' => by
    have hm : φ.gM m' ≠ Mv.pass := fun h => hm' ((φ.gM_eq_pass_iff m').mp h)
    have := φ.mv (φ.gC c') (φ.gM m') hm
    rw [φ.fgC, φ.fgM] at this
    rw [← this, Option.map_map]
    have e : (φ.gC ∘ φ.fC) = id := funext φ.gfC
    rw [e, Option.map_id]
    rfl

/-- The extension to the states: the core mapped, the gradings kept. -/
def fS (φ : SeqIso G0 G0') : G0.S → G0'.S
  | .live c g j => .live (φ.fC c) g j
  | .done c g => .done (φ.fC c) g

def gS (φ : SeqIso G0 G0') : G0'.S → G0.S
  | .live c g j => .live (φ.gC c) g j
  | .done c g => .done (φ.gC c) g

theorem gS_fS (φ : SeqIso G0 G0') (s : G0.S) : φ.gS (φ.fS s) = s := by
  cases s <;> simp [fS, gS, φ.gfC]

theorem fS_gS (φ : SeqIso G0 G0') (s' : G0'.S) : φ.fS (φ.gS s') = s' := by
  cases s' <;> simp [fS, gS, φ.fgC]

theorem fS_inj (φ : SeqIso G0 G0') {x y : G0.S} (h : φ.fS x = φ.fS y) : x = y := by
  have := congrArg φ.gS h
  rw [φ.gS_fS, φ.gS_fS] at this
  exact this

theorem gS_eq_iff (φ : SeqIso G0 G0') (z' : G0'.S) (a : G0.S) :
    φ.gS z' = a ↔ z' = φ.fS a := by
  constructor
  · intro h; rw [← h, φ.fS_gS]
  · intro h; rw [h, φ.gS_fS]

theorem sInit_iso (φ : SeqIso G0 G0') : φ.fS (sInit G0) = sInit G0' := by
  show PState.live (φ.fC G0.q0) false false = PState.live G0'.q0 false false
  rw [φ.q0]

theorem sfinal_iso (φ : SeqIso G0 G0') (s : G0.S) :
    sfinal G0' (φ.fS s) ↔ sfinal G0 s := by
  cases s with
  | live c g j => exact φ.ended c
  | done c g => exact Iff.rfl

theorem sN_iso (φ : SeqIso G0 G0') (s : G0.S) : sN (φ.fS s) = φ.fS (sN s) := by
  cases s <;> rfl

theorem sBar_iso (φ : SeqIso G0 G0') (s : G0.S) : sBar (φ.fS s) = φ.fS (sBar s) := by
  cases s with
  | live c g j => cases j <;> rfl
  | done c g => rfl

/-- Part (1): the extended bijection intertwines the evolutions. -/
theorem sE_iso (φ : SeqIso G0 G0') (s : G0.S) (m : Mv.M) :
    sE G0' (φ.fS s) (φ.fM m) = Option.map φ.fS (sE G0 s m) := by
  cases s with
  | done c g => rfl
  | live c g j =>
    by_cases he : G0.ended c
    · have he' : G0'.ended (φ.fC c) := (φ.ended c).mpr he
      show sE G0' (.live (φ.fC c) g j) (φ.fM m) = _
      rw [prop_finalnomove G0' (s := PState.live (φ.fC c) g j) he' (φ.fM m),
        prop_finalnomove G0 (s := PState.live c g j) he m]
      rfl
    · have he' : ¬G0'.ended (φ.fC c) := fun h => he ((φ.ended c).mp h)
      by_cases hm : m = Mv.pass
      · subst hm
        show sE G0' (.live (φ.fC c) g j) (φ.fM Mv.pass) = _
        rw [φ.fM_pass, sE_pass G0' (φ.fC c) g j he', sE_pass G0 c g j he]
        cases j <;> rfl
      · have hm' : φ.fM m ≠ Mv'.pass := fun h => hm ((φ.fM_eq_pass_iff m).mp h)
        show sE G0' (.live (φ.fC c) g j) (φ.fM m) = _
        rw [sE_nonpass G0' (φ.fC c) g j (φ.fM m) hm' he',
          sE_nonpass G0 c g j m hm he]
        have hgr : ((g = false ∧ Mv'.deg0 (φ.fM m)) ∨ (g = true ∧ Mv'.deg1 (φ.fM m))) ↔
            ((g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)) := by
          rw [← φ.deg0, ← φ.deg1]
        by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
        · rw [if_pos (hgr.mpr hg), if_pos hg, ← φ.mv c m hm,
            Option.map_map, Option.map_map]
          rfl
        · rw [if_neg (fun h => hg (hgr.mp h)), if_neg hg]
          rfl

theorem hashOp_iso (φ : SeqIso G0 G0') (s : G0.S) (m : Mv.M) :
    hashOp G0' (φ.fS s) (φ.fM m) = Option.map φ.fS (hashOp G0 s m) := by
  cases s with
  | done c g =>
    show hashOp G0' (PState.done (φ.fC c) g) (φ.fM m) = Option.map φ.fS (hashOp G0 (PState.done c g) m)
    rw [hashOp_done, hashOp_done]; rfl
  | live c g j =>
    show hashOp G0' (PState.live (φ.fC c) g j) (φ.fM m) = Option.map φ.fS (hashOp G0 (PState.live c g j) m)
    rw [hashOp_live, hashOp_live]
    have e : sE G0' (PState.live (φ.fC c) g j) (φ.fM m)
        = Option.map φ.fS (sE G0 (PState.live c g j) m) := sE_iso φ (PState.live c g j) m
    rw [e]
    cases sE G0 (PState.live c g j) m with
    | some b => rfl
    | none =>
      show sE G0' (sBar (φ.fS (PState.live c g j))) (φ.fM m) = _
      rw [sBar_iso, sE_iso]

theorem hash2_iso (φ : SeqIso G0 G0') (a : G0.S) (m0 m1 : Mv.M) :
    hash2 G0' (φ.fS a) (φ.fM m0) (φ.fM m1) = Option.map φ.fS (hash2 G0 a m0 m1) := by
  unfold hash2
  rw [hashOp_iso]
  cases hashOp G0 a m0 with
  | none => rfl
  | some b =>
    simp only [Option.some_bind]
    exact hashOp_iso φ b m1

theorem tval_iso (φ : SeqIso G0 G0') (a : G0.S) (m m' : Mv.M) :
    tval G0' (φ.fS a) (φ.fM m) (φ.fM m') = Option.map φ.fS (tval G0 a m m') := by
  unfold tval
  rw [hash2_iso]
  cases hash2 G0 a m m' with
  | none => exact hashOp_iso φ a m
  | some x => rfl

/-- The preimage of a branch set under a state map. -/
def _root_.SgoGames.BSet.pre {α β : Type} (g : β → α) (P : BSet α) : BSet β :=
  fun z => P (g z)

/-- P intertwines the isomorphism: P at the image is the image of P
    (as the preimage under the inverse). -/
theorem Pmap_iso (φ : SeqIso G0 G0') (a : G0.S) (m0 m1 : Mv.M) :
    Pmap G0' (φ.fS a) (φ.fM m0) (φ.fM m1)
      = Option.map (BSet.pre φ.gS) (Pmap G0 a m0 m1) := by
  rw [Pmap_eq, Pmap_eq, tval_iso, tval_iso]
  cases tval G0 a m0 m1 with
  | none => cases tval G0 a m1 m0 <;> rfl
  | some x =>
    cases tval G0 a m1 m0 with
    | none => rfl
    | some y =>
      show some (BSet.pair (sN (φ.fS x)) (sN (φ.fS y)))
        = some (BSet.pre φ.gS (BSet.pair (sN x) (sN y)))
      congr 1
      funext z'
      apply propext
      rw [sN_iso, sN_iso]
      show (z' = φ.fS (sN x) ∨ z' = φ.fS (sN y)) ↔ (φ.gS z' = sN x ∨ φ.gS z' = sN y)
      rw [φ.gS_eq_iff, φ.gS_eq_iff]

/-! ### The primed forms -/

theorem hashOp_iso' (φ : SeqIso G0 G0') (a' : G0'.S) (m' : Mv'.M) :
    hashOp G0' a' m' = Option.map φ.fS (hashOp G0 (φ.gS a') (φ.gM m')) := by
  have := hashOp_iso φ (φ.gS a') (φ.gM m')
  rw [φ.fS_gS, φ.fgM] at this
  exact this

theorem Pmap_iso' (φ : SeqIso G0 G0') (a' : G0'.S) (m0' m1' : Mv'.M) :
    Pmap G0' a' m0' m1'
      = Option.map (BSet.pre φ.gS) (Pmap G0 (φ.gS a') (φ.gM m0') (φ.gM m1')) := by
  have := Pmap_iso φ (φ.gS a') (φ.gM m0') (φ.gM m1')
  rw [φ.fS_gS, φ.fgM, φ.fgM] at this
  exact this

theorem sfinal_iso' (φ : SeqIso G0 G0') (a' : G0'.S) :
    sfinal G0' a' ↔ sfinal G0 (φ.gS a') := by
  have := φ.sfinal_iso (φ.gS a')
  rw [φ.fS_gS] at this
  exact this

theorem Interface0_iso' (φ : SeqIso G0 G0') (a' : G0'.S) (m' : Mv'.M) :
    Interface0 G0' a' m' ↔ Interface0 G0 (φ.gS a') (φ.gM m') := by
  show (hashOp G0' a' m').isSome ↔ (hashOp G0 (φ.gS a') (φ.gM m')).isSome
  rw [hashOp_iso' φ, isSome_map']

theorem Interface0_iso (φ : SeqIso G0 G0') (a : G0.S) (m : Mv.M) :
    Interface0 G0' (φ.fS a) (φ.fM m) ↔ Interface0 G0 a m := by
  rw [φ.Interface0_iso', φ.gS_fS, φ.gfM]

/-! ### Sim(G) transports -/

theorem simDef1_iso (φ : SeqIso G0 G0') (A : BSet G0.S) (m' : Mv'.M) :
    simDef1 G0' (BSet.pre φ.gS A) m' ↔ simDef1 G0 A (φ.gM m') := by
  constructor
  · intro h a ha
    have := h (φ.fS a) (by show A (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha)
    rw [φ.sfinal_iso] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [hashOp_iso' φ, φ.gS_fS, isSome_map'] at h2
    exact h2
  · intro h a' ha'
    have := h (φ.gS a') ha'
    rw [sfinal_iso']
    refine ⟨this.1, ?_⟩
    rw [hashOp_iso' φ, isSome_map']
    exact this.2

theorem simDefP_iso (φ : SeqIso G0 G0') (A : BSet G0.S) (m0' m1' : Mv'.M) :
    simDefP G0' (BSet.pre φ.gS A) m0' m1' ↔ simDefP G0 A (φ.gM m0') (φ.gM m1') := by
  constructor
  · intro h a ha
    have := h (φ.fS a) (by show A (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha)
    rw [φ.sfinal_iso] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [Pmap_iso' φ, φ.gS_fS, isSome_map'] at h2
    exact h2
  · intro h a' ha'
    have := h (φ.gS a') ha'
    rw [sfinal_iso']
    refine ⟨this.1, ?_⟩
    rw [Pmap_iso' φ, isSome_map']
    exact this.2

theorem simVal_iso (φ : SeqIso G0 G0') (A : BSet G0.S) (m0' m1' : Mv'.M) (z' : G0'.S) :
    simVal G0' (BSet.pre φ.gS A) m0' m1' z'
      ↔ simVal G0 A (φ.gM m0') (φ.gM m1') (φ.gS z') := by
  constructor
  · rintro ⟨a', ha', P', hP', hz⟩
    rw [Pmap_iso' φ] at hP'
    obtain ⟨P, hP, hPP⟩ := Option.map_eq_some'.mp hP'
    refine ⟨φ.gS a', ha', P, hP, ?_⟩
    rw [← hPP] at hz
    exact hz
  · rintro ⟨a, ha, P, hP, hz⟩
    refine ⟨φ.fS a, by show A (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha,
      BSet.pre φ.gS P, ?_, hz⟩
    rw [Pmap_iso' φ, φ.gS_fS, hP]
    rfl

theorem simFinal_iso (φ : SeqIso G0 G0') (A : BSet G0.S) :
    simFinal G0' (BSet.pre φ.gS A) ↔ simFinal G0 A := by
  constructor
  · rintro ⟨a', ha', hf⟩
    exact ⟨φ.gS a', ha', (sfinal_iso' φ a').mp hf⟩
  · rintro ⟨a, ha, hf⟩
    refine ⟨φ.fS a, by show A (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha, ?_⟩
    rw [φ.sfinal_iso]; exact hf

/-! ### Legally obtainable states -/

theorem seqReach_fS (φ : SeqIso G0 G0') {a : G0.S} (h : SeqReach G0 a) :
    SeqReach G0' (φ.fS a) := by
  induction h with
  | init => rw [sInit_iso]; exact SeqReach.init
  | @step s s' m _ hs ih =>
    refine SeqReach.step (m := φ.fM m) ih ?_
    rw [sE_iso, hs]
    rfl

theorem seqReach_iso' (φ : SeqIso G0 G0') (a' : G0'.S) :
    SeqReach G0' a' ↔ SeqReach G0 (φ.gS a') := by
  constructor
  · intro h
    have := φ.symm.seqReach_fS h
    exact this
  · intro h
    have := φ.seqReach_fS h
    rw [φ.fS_gS] at this
    exact this

/-! ### Commuting turns and associated states -/

theorem commuteAt_iso (φ : SeqIso G0 G0') (a : G0.S) (m0 m1 : Mv.M) :
    CommuteAt G0' (φ.fS a) (φ.fM m0) (φ.fM m1) ↔ CommuteAt G0 a m0 m1 := by
  constructor
  · rintro ⟨x', y', hx, hy, hxy⟩
    rw [hash2_iso] at hx hy
    obtain ⟨x, hx2, hxx⟩ := Option.map_eq_some'.mp hx
    obtain ⟨y, hy2, hyy⟩ := Option.map_eq_some'.mp hy
    rw [← hxx, ← hyy, sN_iso, sN_iso] at hxy
    exact ⟨x, y, hx2, hy2, φ.fS_inj hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨φ.fS x, φ.fS y, ?_, ?_, ?_⟩
    · rw [hash2_iso, hx]; rfl
    · rw [hash2_iso, hy]; rfl
    · rw [sN_iso, sN_iso, hxy]

theorem assocOf_iso (φ : SeqIso G0 G0') (a : G0.S) (m0 m1 : Mv.M) :
    assocOf G0' (φ.fS a) (φ.fM m0) (φ.fM m1) = φ.fS (assocOf G0 a m0 m1) := by
  unfold assocOf
  rw [hash2_iso]
  cases hash2 G0 a m0 m1 with
  | none => exact sN_iso φ a
  | some x => exact sN_iso φ x

theorem commuteAt_iso' (φ : SeqIso G0 G0') (a' : G0'.S) (m0' m1' : Mv'.M) :
    CommuteAt G0' a' m0' m1' ↔ CommuteAt G0 (φ.gS a') (φ.gM m0') (φ.gM m1') := by
  have := commuteAt_iso φ (φ.gS a') (φ.gM m0') (φ.gM m1')
  rw [φ.fS_gS, φ.fgM, φ.fgM] at this
  exact this

theorem assocOf_iso' (φ : SeqIso G0 G0') (a' : G0'.S) (m0' m1' : Mv'.M) :
    assocOf G0' a' m0' m1' = φ.fS (assocOf G0 (φ.gS a') (φ.gM m0') (φ.gM m1')) := by
  have := assocOf_iso φ (φ.gS a') (φ.gM m0') (φ.gM m1')
  rw [φ.fS_gS, φ.fgM, φ.fgM] at this
  exact this

end SeqIso

/-! ### Part (2): renaming a simultaneization along φ -/

/-- H with each move m renamed to φ(m): the same states, a move of H'
    acting as its preimage acted in H. -/
def renameSim (φ : SeqIso G0 G0') (H : SimulGame Mv) : SimulGame Mv' where
  B := H.B
  avail := fun s m' => H.avail s (φ.gM m')
  pairE := fun s m0' m1' => H.pairE s (φ.gM m0') (φ.gM m1')
  q0 := H.q0
  final := H.final

/-- The branch semantics of the renamed game: the branches mapped
    along φ (the preimage under the inverse). -/
def renameRho (φ : SeqIso G0 G0') {H : SimulGame Mv} (ρ : H.B → BSet G0.S) :
    (renameSim φ H).B → BSet G0'.S :=
  fun s => BSet.pre φ.gS (ρ s)

section Rename

variable (φ : SeqIso G0 G0') (H : SimulGame Mv)

theorem simReach_rename_mp {s : (renameSim φ H).B}
    (h : SimReach (renameSim φ H) s) : SimReach H s := by
  induction h with
  | init => exact SimReach.init
  | step _ hs ih => exact SimReach.step ih hs

theorem simReach_rename_mpr {s : H.B} (h : SimReach H s) :
    SimReach (renameSim φ H) s := by
  induction h with
  | init => exact SimReach.init
  | @step s s' m0 m1 _ hs ih =>
    refine SimReach.step (m0 := φ.fM m0) (m1 := φ.fM m1) ih ?_
    show H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1)) = some s'
    rw [φ.gfM, φ.gfM]; exact hs

theorem simReach_rename (s : H.B) :
    SimReach (renameSim φ H) s ↔ SimReach H s :=
  ⟨simReach_rename_mp φ H, simReach_rename_mpr φ H⟩

theorem semiC_rename_fS {s : H.B} {a : G0.S} (h : SemiC G0 H s a) :
    SemiC G0' (renameSim φ H) s (φ.fS a) := by
  induction h with
  | init => rw [φ.sInit_iso]; exact SemiC.init
  | @step s a s' m0 m1 _ hc hs ih =>
    rw [← φ.assocOf_iso]
    refine SemiC.step ih ((φ.commuteAt_iso a m0 m1).mpr hc) ?_
    show H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1)) = some s'
    rw [φ.gfM, φ.gfM]; exact hs

theorem semiC_rename_mp {s : (renameSim φ H).B} {a' : G0'.S}
    (h : SemiC G0' (renameSim φ H) s a') : SemiC G0 H s (φ.gS a') := by
  induction h with
  | init =>
    have e : φ.gS (sInit G0') = sInit G0 := by
      rw [← φ.sInit_iso, φ.gS_fS]
    rw [e]; exact SemiC.init
  | @step s a s' m0' m1' _ hc hs ih =>
    rw [φ.assocOf_iso', φ.gS_fS]
    exact SemiC.step ih ((φ.commuteAt_iso' a m0' m1').mp hc) hs

theorem semiC_rename (s : H.B) (a' : G0'.S) :
    SemiC G0' (renameSim φ H) s a' ↔ SemiC G0 H s (φ.gS a') := by
  constructor
  · exact semiC_rename_mp φ H
  · intro h
    have := semiC_rename_fS φ H h
    rw [φ.fS_gS] at this
    exact this

theorem isSimultaneization_rename (ρ : H.B → BSet G0.S) :
    IsSimultaneization G0' (renameSim φ H) (renameRho φ ρ)
      ↔ IsSimultaneization G0 H ρ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      have h1 := h.rho_init (φ.fS a)
      have e : renameRho φ ρ (renameSim φ H).q0 (φ.fS a) = ρ H.q0 a := by
        show ρ H.q0 (φ.gS (φ.fS a)) = ρ H.q0 a
        rw [φ.gS_fS]
      rw [e] at h1
      show ρ H.q0 a ↔ a = sInit G0
      refine Iff.trans h1 ?_
      show φ.fS a = sInit G0' ↔ a = sInit G0
      rw [← φ.sInit_iso]
      exact ⟨φ.fS_inj, fun e => by rw [e]⟩
    · intro s m0 m1 hr hp
      have := h.nat_defined (m0 := φ.fM m0) (m1 := φ.fM m1)
        ((simReach_rename φ H s).mpr hr) (by
          show (H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1))).isSome
          rw [φ.gfM, φ.gfM]; exact hp)
      rw [show renameRho φ ρ s = BSet.pre φ.gS (ρ s) from rfl,
        φ.simDefP_iso, φ.gfM, φ.gfM] at this
      exact this
    · intro s s' m0 m1 hr hp z hz
      have := h.nat_incl (m0 := φ.fM m0) (m1 := φ.fM m1)
        ((simReach_rename φ H s).mpr hr) (by
          show H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1)) = some s'
          rw [φ.gfM, φ.gfM]; exact hp) (φ.fS z)
        (by show ρ s' (φ.gS (φ.fS z)); rw [φ.gS_fS]; exact hz)
      rw [show renameRho φ ρ s = BSet.pre φ.gS (ρ s) from rfl,
        φ.simVal_iso, φ.gfM, φ.gfM, φ.gS_fS] at this
      exact this
    · intro s a hs z
      have h1 := h.semiclassical ((semiC_rename φ H s (φ.fS a)).mpr
        (by rw [φ.gS_fS]; exact hs)) (φ.fS z)
      have e : renameRho φ ρ s (φ.fS z) = ρ s z := by
        show ρ s (φ.gS (φ.fS z)) = ρ s z
        rw [φ.gS_fS]
      rw [e] at h1
      show ρ s z ↔ z = a
      refine Iff.trans h1 ?_
      show φ.fS z = φ.fS a ↔ z = a
      exact ⟨φ.fS_inj, fun e => by rw [e]⟩
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a'
      have := h.rho_init (φ.gS a')
      show ρ H.q0 (φ.gS a') ↔ a' = sInit G0'
      rw [this]
      show φ.gS a' = sInit G0 ↔ a' = sInit G0'
      rw [φ.gS_eq_iff, φ.sInit_iso]
    · intro s m0' m1' hr hp
      have := h.nat_defined ((simReach_rename φ H s).mp hr) hp
      show simDefP G0' (BSet.pre φ.gS (ρ s)) m0' m1'
      rw [φ.simDefP_iso]
      exact this
    · intro s s' m0' m1' hr hp z' hz
      have := h.nat_incl ((simReach_rename φ H s).mp hr) hp (φ.gS z') hz
      show simVal G0' (BSet.pre φ.gS (ρ s)) m0' m1' z'
      rw [φ.simVal_iso]
      exact this
    · intro s a' hs z'
      have := h.semiclassical ((semiC_rename φ H s a').mp hs) (φ.gS z')
      show ρ s (φ.gS z') ↔ z' = a'
      refine Iff.trans this ?_
      show φ.gS z' = φ.gS a' ↔ z' = a'
      rw [φ.gS_eq_iff, φ.fS_gS]

theorem faithfulAt_rename (ρ : H.B → BSet G0.S) (s : H.B) :
    FaithfulAt G0' (renameSim φ H) (renameRho φ ρ) s ↔ FaithfulAt G0 H ρ s := by
  constructor
  · rintro ⟨⟨a', ha'⟩, hi⟩
    refine ⟨⟨φ.gS a', ha'⟩, ?_⟩
    · intro m
      have h1 := hi (φ.fM m)
      have e : Interface1 (renameSim φ H) s (φ.fM m) ↔ H.avail s m := by
        show H.avail s (φ.gM (φ.fM m)) ↔ _
        rw [φ.gfM]
      show H.avail s m ↔ ∀ a, ρ s a → Interface0 G0 a m
      refine Iff.trans e.symm (Iff.trans h1 ⟨?_, ?_⟩)
      · intro h a ha
        have := h (φ.fS a) (by show ρ s (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha)
        rw [φ.Interface0_iso] at this
        exact this
      · intro h a' ha'
        rw [φ.Interface0_iso', φ.gfM]
        exact h (φ.gS a') ha'
  · rintro ⟨⟨a, ha⟩, hi⟩
    refine ⟨⟨φ.fS a, by show ρ s (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha⟩, ?_⟩
    · intro m'
      have h1 := hi (φ.gM m')
      show H.avail s (φ.gM m') ↔ ∀ a', ρ s (φ.gS a') → Interface0 G0' a' m'
      refine Iff.trans h1 ⟨?_, ?_⟩
      · intro h a' ha'
        rw [φ.Interface0_iso']
        exact h (φ.gS a') ha'
      · intro h a ha
        have := h (φ.fS a) (by show ρ s (φ.gS (φ.fS a)); rw [φ.gS_fS]; exact ha)
        rw [φ.Interface0_iso', φ.gS_fS] at this
        exact this

theorem withinD_rename_mp (ρ : H.B → BSet G0.S) {d : Nat} {s : (renameSim φ H).B}
    (h : WithinD G0' (renameSim φ H) (renameRho φ ρ) d s) : WithinD G0 H ρ d s := by
  induction h with
  | base hs => exact WithinD.base (semiC_rename_mp φ H hs)
  | ofLe _ ih => exact WithinD.ofLe ih
  | step _ hs ih => exact WithinD.step ih hs

theorem withinD_rename_mpr (ρ : H.B → BSet G0.S) {d : Nat} {s : H.B}
    (h : WithinD G0 H ρ d s) : WithinD G0' (renameSim φ H) (renameRho φ ρ) d s := by
  induction h with
  | base hs => exact WithinD.base (semiC_rename_fS φ H hs)
  | ofLe _ ih => exact WithinD.ofLe ih
  | @step d s s' m0 m1 _ hs ih =>
    refine WithinD.step (m0 := φ.fM m0) (m1 := φ.fM m1) ih ?_
    show H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1)) = some s'
    rw [φ.gfM, φ.gfM]; exact hs

theorem withinD_rename (ρ : H.B → BSet G0.S) (d : Nat) (s : H.B) :
    WithinD G0' (renameSim φ H) (renameRho φ ρ) d s ↔ WithinD G0 H ρ d s :=
  ⟨withinD_rename_mp φ H ρ, withinD_rename_mpr φ H ρ⟩

theorem faithfulWithin_rename (ρ : H.B → BSet G0.S) (d : Nat) :
    FaithfulWithin G0' (renameSim φ H) (renameRho φ ρ) d ↔ FaithfulWithin G0 H ρ d := by
  constructor
  · intro h s hs
    exact (faithfulAt_rename φ H ρ s).mp (h s ((withinD_rename φ H ρ d s).mpr hs))
  · intro h s hs
    exact (faithfulAt_rename φ H ρ s).mpr (h s ((withinD_rename φ H ρ d s).mp hs))

theorem isSimple_rename :
    IsSimple G0' (renameSim φ H) ↔ IsSimple G0 H := by
  constructor
  · intro h s hr hnf ⟨m, hm, hav⟩
    obtain ⟨a', hra', hi⟩ := h s ((simReach_rename φ H s).mpr hr) hnf
      ⟨φ.fM m, fun e => hm ((φ.fM_eq_pass_iff m).mp e), by
        show H.avail s (φ.gM (φ.fM m)); rw [φ.gfM]; exact hav⟩
    refine ⟨φ.gS a', (φ.seqReach_iso' a').mp hra', ?_⟩
    intro m
    have := hi (φ.fM m)
    rw [φ.Interface0_iso', φ.gfM] at this
    rw [this]
    show H.avail s (φ.gM (φ.fM m)) ↔ H.avail s m
    rw [φ.gfM]
  · intro h s hr hnf ⟨m', hm', hav⟩
    obtain ⟨a, hra, hi⟩ := h s ((simReach_rename φ H s).mp hr) hnf
      ⟨φ.gM m', fun e => hm' ((φ.gM_eq_pass_iff m').mp e), hav⟩
    refine ⟨φ.fS a, φ.seqReach_fS hra, ?_⟩
    intro m'
    rw [φ.Interface0_iso', φ.gS_fS]
    exact hi (φ.gM m')

theorem simOK_rename : SimOK (renameSim φ H) ↔ SimOK H := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, h.final_exists⟩
    · intro s m hr hf hav
      exact h.final_nomove (m := φ.fM m) ((simReach_rename φ H s).mpr hr) hf
        (by show H.avail s (φ.gM (φ.fM m)); rw [φ.gfM]; exact hav)
    · intro s hr hnf
      have := h.pass_available ((simReach_rename φ H s).mpr hr) hnf
      show H.avail s Mv.pass
      rw [← φ.gM_pass]; exact this
    · intro s m0 m1 hr h0 h1 ha0 ha1
      have := h.pair_of_avail (m0 := φ.fM m0) (m1 := φ.fM m1)
        ((simReach_rename φ H s).mpr hr) ((φ.deg0 m0).mp h0) ((φ.deg1 m1).mp h1)
        (by show H.avail s (φ.gM (φ.fM m0)); rw [φ.gfM]; exact ha0)
        (by show H.avail s (φ.gM (φ.fM m1)); rw [φ.gfM]; exact ha1)
      show (H.pairE s m0 m1).isSome
      rw [← φ.gfM m0, ← φ.gfM m1]
      exact this
    · intro s m0 m1 hr hp
      have := h.avail_of_pair (m0 := φ.fM m0) (m1 := φ.fM m1)
        ((simReach_rename φ H s).mpr hr)
        (by show (H.pairE s (φ.gM (φ.fM m0)) (φ.gM (φ.fM m1))).isSome
            rw [φ.gfM, φ.gfM]; exact hp)
      show H.avail s m0 ∧ H.avail s m1
      rw [← φ.gfM m0, ← φ.gfM m1]
      exact this
  · intro h
    refine ⟨?_, ?_, ?_, ?_, h.final_exists⟩
    · intro s m' hr hf hav
      exact h.final_nomove ((simReach_rename φ H s).mp hr) hf hav
    · intro s hr hnf
      show H.avail s (φ.gM Mv'.pass)
      rw [φ.gM_pass]
      exact h.pass_available ((simReach_rename φ H s).mp hr) hnf
    · intro s m0' m1' hr h0 h1 ha0 ha1
      exact h.pair_of_avail ((simReach_rename φ H s).mp hr)
        ((φ.deg0' m0').mp h0) ((φ.deg1' m1').mp h1) ha0 ha1
    · intro s m0' m1' hr hp
      exact h.avail_of_pair ((simReach_rename φ H s).mp hr) hp

theorem renameSim_pairE (s : H.B) (m0' m1' : Mv'.M) :
    (renameSim φ H).pairE s m0' m1' = H.pairE s (φ.gM m0') (φ.gM m1') := rfl

theorem renameSim_avail (s : H.B) (m' : Mv'.M) :
    (renameSim φ H).avail s m' = H.avail s (φ.gM m') := rfl

theorem optBRel_rename (rel : H.B → H.B → Prop) (o1 o2 : Option H.B) :
    OptBRel (renameSim φ H) rel o1 o2 ↔ OptBRel H rel o1 o2 := by
  cases o1 <;> cases o2 <;> exact Iff.rfl

theorem simSym_rename (rel : H.B → H.B → Prop) :
    SimSym (renameSim φ H) rel ↔ SimSym H rel := by
  constructor
  · rintro ⟨A', R, hAA, hAp, hAd, hRR, hRq, hRf, hRa, hE⟩
    refine ⟨fun m => φ.gM (A' (φ.fM m)), R, ?_, ?_, ?_, hRR, hRq, hRf, ?_, ?_⟩
    · intro m
      show φ.gM (A' (φ.fM (φ.gM (A' (φ.fM m))))) = m
      rw [φ.fgM, hAA, φ.gfM]
    · show φ.gM (A' (φ.fM Mv.pass)) = Mv.pass
      rw [φ.fM_pass, hAp, φ.gM_pass]
    · intro m
      show Mv.deg0 m ↔ Mv.deg1 (φ.gM (A' (φ.fM m)))
      rw [φ.deg0, hAd, ← φ.deg1']
    · intro s m
      have h2 := hRa s (φ.fM m)
      rw [renameSim_avail, renameSim_avail, φ.gfM] at h2
      exact h2
    · intro s m0 m1
      have h2 := hE s (φ.fM m0) (φ.fM m1)
      rw [renameSim_pairE, renameSim_pairE, optBRel_rename, φ.gfM, φ.gfM] at h2
      exact h2
  · rintro ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRf, hRa, hE⟩
    refine ⟨fun m' => φ.fM (A (φ.gM m')), R, ?_, ?_, ?_, hRR, hRq, hRf, ?_, ?_⟩
    · intro m'
      show φ.fM (A (φ.gM (φ.fM (A (φ.gM m'))))) = m'
      rw [φ.gfM, hAA, φ.fgM]
    · show φ.fM (A (φ.gM Mv'.pass)) = Mv'.pass
      rw [φ.gM_pass, hAp, φ.fM_pass]
    · intro m'
      show Mv'.deg0 m' ↔ Mv'.deg1 (φ.fM (A (φ.gM m')))
      rw [φ.deg0', hAd, ← φ.deg1]
    · intro s m'
      show (renameSim φ H).avail (R s) (φ.fM (A (φ.gM m'))) ↔ (renameSim φ H).avail s m'
      rw [renameSim_avail, renameSim_avail, φ.gfM]
      exact hRa s (φ.gM m')
    · intro s m0' m1'
      show OptBRel (renameSim φ H) rel (Option.map R ((renameSim φ H).pairE (R s)
        (φ.fM (A (φ.gM m1'))) (φ.fM (A (φ.gM m0'))))) ((renameSim φ H).pairE s m0' m1')
      rw [renameSim_pairE, renameSim_pairE, optBRel_rename, φ.gfM, φ.gfM]
      exact hE s (φ.gM m0') (φ.gM m1')

end Rename

/-- lem_dynamics, part (2): renaming along φ preserves every printed
    condition — simultaneization, the automaton conditions, symmetry,
    faithfulness within every distance (hence the radius), simplicity. -/
theorem lem_dynamics_2 (φ : SeqIso G0 G0') (H : SimulGame Mv) (ρ : H.B → BSet G0.S) :
    (IsSimultaneization G0' (renameSim φ H) (renameRho φ ρ)
      ↔ IsSimultaneization G0 H ρ) ∧
    (SimOK (renameSim φ H) ↔ SimOK H) ∧
    (∀ rel, SimSym (renameSim φ H) rel ↔ SimSym H rel) ∧
    (∀ d, FaithfulWithin G0' (renameSim φ H) (renameRho φ ρ) d
      ↔ FaithfulWithin G0 H ρ d) ∧
    (IsSimple G0' (renameSim φ H) ↔ IsSimple G0 H) :=
  ⟨isSimultaneization_rename φ H ρ, simOK_rename φ H, simSym_rename φ H,
   faithfulWithin_rename φ H ρ, isSimple_rename φ H⟩

/-! ### Part (3): the radius spectrum -/

/-- The faithfulness radius, in explicit form: exactly d (faithful
    within d, not within d+1), or ∞ (faithful within every distance). -/
def HasRadius (G0 : SeqGame Mv) (H : SimulGame Mv) (ρ : H.B → BSet G0.S) :
    Option Nat → Prop
  | some d => FaithfulWithin G0 H ρ d ∧ ¬FaithfulWithin G0 H ρ (d+1)
  | none => ∀ d, FaithfulWithin G0 H ρ d

/-- r ∈ ℕ ⊔ {∞} lies in the radius spectrum of G0: some simple
    symmetric simultaneization of G0 has radius r. -/
def InSpectrum (G0 : SeqGame Mv) (r : Option Nat) : Prop :=
  ∃ H : SimulGame Mv, ∃ ρ : H.B → BSet G0.S, ∃ rel : H.B → H.B → Prop,
    IsEquivB H rel ∧ SimOK H ∧ SimSym H rel ∧
    IsSimultaneization G0 H ρ ∧ IsSimple G0 H ∧ HasRadius G0 H ρ r

theorem hasRadius_rename (φ : SeqIso G0 G0') (H : SimulGame Mv)
    (ρ : H.B → BSet G0.S) (r : Option Nat) :
    HasRadius G0' (renameSim φ H) (renameRho φ ρ) r ↔ HasRadius G0 H ρ r := by
  cases r with
  | none =>
    show (∀ d, FaithfulWithin G0' (renameSim φ H) (renameRho φ ρ) d) ↔ _
    constructor
    · intro h d; exact (faithfulWithin_rename φ H ρ d).mp (h d)
    · intro h d; exact (faithfulWithin_rename φ H ρ d).mpr (h d)
  | some d =>
    show (FaithfulWithin G0' (renameSim φ H) (renameRho φ ρ) d ∧
      ¬FaithfulWithin G0' (renameSim φ H) (renameRho φ ρ) (d+1)) ↔ _
    rw [faithfulWithin_rename, faithfulWithin_rename]
    exact Iff.rfl

theorem inSpectrum_of_iso (φ : SeqIso G0 G0') (r : Option Nat)
    (h : InSpectrum G0 r) : InSpectrum G0' r := by
  obtain ⟨H, ρ, rel, heq, hok, hsym, hsim, hsimple, hrad⟩ := h
  refine ⟨renameSim φ H, renameRho φ ρ, rel, heq,
    (simOK_rename φ H).mpr hok, (simSym_rename φ H rel).mpr hsym,
    (isSimultaneization_rename φ H ρ).mpr hsim,
    (isSimple_rename φ H).mpr hsimple,
    (hasRadius_rename φ H ρ r).mpr hrad⟩

/-- lem_dynamics, part (3): the radius spectra of isomorphic games
    coincide. -/
theorem lem_dynamics_3 (φ : SeqIso G0 G0') (r : Option Nat) :
    InSpectrum G0 r ↔ InSpectrum G0' r :=
  ⟨inSpectrum_of_iso φ r, inSpectrum_of_iso φ.symm r⟩

/-- lem_dynamics, part (1): the extended bijection intertwines the
    evolutions, the pass moves, the final states and the position
    normal forms. -/
theorem lem_dynamics_1 (φ : SeqIso G0 G0') :
    (∀ s m, sE G0' (φ.fS s) (φ.fM m) = Option.map φ.fS (sE G0 s m)) ∧
    φ.fM Mv.pass = Mv'.pass ∧
    (∀ s, sfinal G0' (φ.fS s) ↔ sfinal G0 s) ∧
    (∀ s, sN (φ.fS s) = φ.fS (sN s)) :=
  ⟨φ.sE_iso, φ.fM_pass, φ.sfinal_iso, φ.sN_iso⟩

end SgoGames
