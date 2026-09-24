/- SgoZero.lean — Theorem thm_zero: zero in the radius spectrum.

   The truncated universal simultaneization Sim_sc(G) is Sim(G) with
   every state that is not semi-classical declared final: it evolves as
   Sim(G) at the semi-classical states and nowhere else. The three
   parts of the printed theorem:

   (1) Sim_sc(G) is a simple simultaneization of G, faithful within
       distance zero;
   (2) at a conflict — a joint move available at a semi-classical
       state {a} whose P(a, m_0, m_1) has two elements, neither final —
       its faithfulness radius is exactly zero, so 0 lies in the
       radius spectrum of G;
   (3) if instead every joint move available at a semi-classical state
       commutes at its associated state, the spectrum is {∞}.

   Statement audit. The theorem is stated for an arbitrary symmetric
   sequential game G (SeqSym), on the printed S(G)-theoretic
   def_sequential (SgoGames): no further hypothesis. The conflict of
   part (2) is read off P itself — P (a, m_0, m_1) has two distinct
   non final elements — so the printed chess witness, of P's lowest
   priority case with neither composite defined, is covered; SgoZeroWit
   is a witness game of exactly that shape. The hypothesis of part (3)
   is stated over the associated states of the semi-classical states of
   Sim(G) (`scAssoc_iff_semiC` identifies them as printed). Part (3)
   uses the naturality of the branch semantics where the print appeals
   to faithfulness; faithfulness within 0 is used only to have
   a radius. -/
import SgoDyn

namespace SgoGames

attribute [local instance] Classical.propDecidable

variable {Mv : Moves}

/-! ### Reading the evolution of Sim(G) -/

theorem simGame_pairE_of (G : SeqGame Mv) (A : NSet G) (m0 m1 : Mv.M)
    (hd : simDefP G A.1 m0 m1) :
    (simGame G).pairE A m0 m1
      = some ⟨simVal G A.1 m0 m1, simVal_normal G A.1 m0 m1⟩ := by
  show (if simDefP G A.1 m0 m1 then _ else none) = _
  rw [if_pos hd]

theorem simGame_pairE_none (G : SeqGame Mv) (A : NSet G) (m0 m1 : Mv.M)
    (hd : ¬simDefP G A.1 m0 m1) : (simGame G).pairE A m0 m1 = none := by
  show (if simDefP G A.1 m0 m1 then _ else none) = _
  rw [if_neg hd]

theorem simGame_pairE_some (G : SeqGame Mv) {A B : NSet G} {m0 m1 : Mv.M}
    (h : (simGame G).pairE A m0 m1 = some B) :
    simDefP G A.1 m0 m1 ∧ ∀ z, B.1 z ↔ simVal G A.1 m0 m1 z := by
  by_cases hd : simDefP G A.1 m0 m1
  · refine ⟨hd, ?_⟩
    rw [simGame_pairE_of G A m0 m1 hd] at h
    have hB := congrArg Subtype.val (Option.some_inj.mp h)
    intro z
    rw [← hB]
  · rw [simGame_pairE_none G A m0 m1 hd] at h
    exact absurd h (fun h => Option.noConfusion h)

/-! ### Semi-classical states of Sim(G) are singletons (lem_universal) -/

/-- A semi-classical state of Sim(G) is the singleton of its associated
    state: the printed "ρ is the identity, and at a commuting turn the
    two composites have the common position normal form a'". -/
theorem semiC_single (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) : ∀ z, A.1 z ↔ z = a := by
  induction h with
  | init => intro z; exact Iff.rfl
  | @step s b s' m0 m1 _ hc hp ih =>
    obtain ⟨hd, hval⟩ := simGame_pairE_some G hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hc
    have hP : Pmap G b m0 m1 = some (BSet.pair (sN x) (sN y)) := by
      rw [Pmap_eq]
      have h0 : tval G b m0 m1 = some x := by unfold tval; rw [hx]
      have h1 : tval G b m1 m0 = some y := by unfold tval; rw [hy]
      rw [h0, h1]
    have hassoc : assocOf G b m0 m1 = sN x := by
      unfold assocOf; rw [hx]; rfl
    intro z
    rw [hval z, hassoc]
    constructor
    · rintro ⟨c, hc', P, hPc, hz⟩
      rw [ih c |>.mp hc'] at hPc
      rw [hP] at hPc
      have : P = BSet.pair (sN x) (sN y) := (Option.some_inj.mp hPc).symm
      rw [this] at hz
      rcases hz with hz | hz
      · exact hz
      · rw [hz, ← hxy]
    · intro hz
      exact ⟨b, (ih b).mpr rfl, BSet.pair (sN x) (sN y), hP, Or.inl hz⟩

theorem semiC_eqv (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) : BSet.eqv A.1 (BSet.single a) :=
  fun z => semiC_single G h z

/-- The associated state of a semi-classical state is a position
    normal form. -/
theorem semiC_normal (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) : sN a = a :=
  A.2 a ((semiC_single G h a).mpr rfl)

/-! ### Reachability: `simReach_of_semiC`, `simReach_of_withinD` now live in SgoGames -/

theorem withinD_of_zero (G : SeqGame Mv) (H : SimulGame Mv)
    (ρ : H.B → BSet G.S) {s : H.B} (h : WithinD G H ρ 0 s) :
    ∀ d, WithinD G H ρ d s := by
  intro d
  induction d with
  | zero => exact h
  | succ k ih => exact WithinD.ofLe ih

/-! ### lem_universal: Sim(G) is a simultaneization of G -/

theorem simGame_isSimultaneization (G : SeqGame Mv) :
    IsSimultaneization G (simGame G) (fun A => A.1) where
  rho_init := fun z => Iff.rfl
  nat_defined := by
    intro A m0 m1 _ h
    exact (simGame_pairE_isSome G A m0 m1).mp h
  nat_incl := by
    intro A A' m0 m1 _ hp z hz
    exact ((simGame_pairE_some G hp).2 z).mp hz
  semiclassical := by
    intro A a h
    exact semiC_eqv G h

/-- A legally obtainable state of Sim(G) is nonempty: P takes nonempty
    values. -/
theorem simGame_nonempty (G : SeqGame Mv) {A : NSet G}
    (h : SimReach (simGame G) A) : ∃ a, A.1 a := by
  induction h with
  | init => exact ⟨sInit G, rfl⟩
  | @step s s' m0 m1 _ hp ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨hd, hval⟩ := simGame_pairE_some G hp
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hd a ha).2
    obtain ⟨x, y, -, -, hPe⟩ := (Pmap_some_iff G a m0 m1 P).mp hP
    exact ⟨sN x, (hval (sN x)).mpr ⟨a, ha, P, hP, by rw [hPe]; exact Or.inl rfl⟩⟩

/-- Sim(G) is faithful at every legally obtainable state: its branch
    semantics is the identity, its finality is that some branch is
    final, and a move is available exactly when it is available in
    every branch. -/
theorem simGame_faithfulAt (G : SeqGame Mv) {A : NSet G}
    (h : SimReach (simGame G) A) :
    FaithfulAt G (simGame G) (fun A => A.1) A := by
  refine ⟨simGame_nonempty G h, ?_⟩
  intro m
  constructor
  · intro hav a ha
    exact (hav a ha).2
  · intro hall a ha
    exact ⟨fun hfa => interface0_of_final G hfa m (hall a ha), hall a ha⟩

/-- lem_universal: Sim(G) is a simultaneization of G, with ρ the
    identity; its semi-classical states are the singletons of their
    associated states; and it is faithful at every legally obtainable
    state, hence within every distance — faithfulness radius ∞. -/
theorem lem_universal (G : SeqGame Mv) :
    IsSimultaneization G (simGame G) (fun A => A.1)
    ∧ (∀ (A : NSet G) (a : G.S), SemiC G (simGame G) A a →
        BSet.eqv A.1 (BSet.single a))
    ∧ (∀ A : NSet G, SimReach (simGame G) A →
        FaithfulAt G (simGame G) (fun A => A.1) A)
    ∧ HasRadius G (simGame G) (fun A => A.1) none :=
  ⟨simGame_isSimultaneization G, fun _ _ h => semiC_eqv G h,
   fun _ h => simGame_faithfulAt G h,
   fun _ _ hw => simGame_faithfulAt G (simReach_of_withinD G (simGame G) _ hw)⟩

/-! ### The truncation Sim_sc(G) -/

/-- The semi-classical states of Sim(G), read in Sim(G) itself
    (Definition def_semiclassical). -/
def ScState (G : SeqGame Mv) (A : NSet G) : Prop := ∃ a, SemiC G (simGame G) A a

/-- Sim_sc(G): Sim(G) with every state that is not semi-classical
    declared final — it evolves as Sim(G) at the semi-classical states
    and nowhere else. The new final states are drawn (the scoring
    partition is not carried by this development). -/
noncomputable def simGameSc (G : SeqGame Mv) : SimulGame Mv where
  B := NSet G
  avail := fun A m => ScState G A ∧ simDef1 G A.1 m
  pairE := fun A m0 m1 => if ScState G A then (simGame G).pairE A m0 m1 else none
  q0 := (simGame G).q0
  final := fun A => simFinal G A.1 ∨ ¬ScState G A

theorem simGameSc_avail (G : SeqGame Mv) (A : NSet G) (m : Mv.M) :
    (simGameSc G).avail A m ↔ (ScState G A ∧ simDef1 G A.1 m) := Iff.rfl

theorem simGameSc_final (G : SeqGame Mv) (A : NSet G) :
    (simGameSc G).final A ↔ (simFinal G A.1 ∨ ¬ScState G A) := Iff.rfl

theorem simGameSc_pairE (G : SeqGame Mv) (A : NSet G) (m0 m1 : Mv.M)
    (h : ScState G A) :
    (simGameSc G).pairE A m0 m1 = (simGame G).pairE A m0 m1 := by
  show (if ScState G A then _ else none) = _
  rw [if_pos h]

theorem simGameSc_pairE_none (G : SeqGame Mv) (A : NSet G) (m0 m1 : Mv.M)
    (h : ¬ScState G A) : (simGameSc G).pairE A m0 m1 = none := by
  show (if ScState G A then _ else none) = _
  rw [if_neg h]

/-- The truncation's own semi-classical states are those of Sim(G):
    the two evolutions agree there. -/
theorem semiC_sc_of_sim (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) : SemiC G (simGameSc G) A a := by
  induction h with
  | init => exact SemiC.init
  | @step s b s' m0 m1 hs hc hp ih =>
    refine SemiC.step ih hc ?_
    rw [simGameSc_pairE G s m0 m1 ⟨b, hs⟩]
    exact hp

theorem semiC_sim_of_sc (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGameSc G) A a) : SemiC G (simGame G) A a := by
  induction h with
  | init => exact SemiC.init
  | @step s b s' m0 m1 _ hc hp ih =>
    refine SemiC.step ih hc ?_
    rw [simGameSc_pairE G s m0 m1 ⟨b, ih⟩] at hp
    exact hp

theorem simReach_sim_of_sc (G : SeqGame Mv) {A : NSet G}
    (h : SimReach (simGameSc G) A) : SimReach (simGame G) A := by
  induction h with
  | init => exact SimReach.init
  | @step s s' m0 m1 _ hp ih =>
    by_cases hsc : ScState G s
    · rw [simGameSc_pairE G s m0 m1 hsc] at hp
      exact SimReach.step ih hp
    · rw [simGameSc_pairE_none G s m0 m1 hsc] at hp
      exact absurd hp (fun h => Option.noConfusion h)

/-- Sim_sc(G) is a combinatorial simultaneous game. -/
theorem simGameSc_simOK (G : SeqGame Mv) : SimOK (simGameSc G) where
  final_nomove := by
    intro A m _ hfin hav
    obtain ⟨hsc, hd1⟩ := hav
    rcases hfin with ⟨a, ha, hfa⟩ | hnsc
    · exact (hd1 a ha).1 hfa
    · exact hnsc hsc
  pass_available := by
    intro A hre hnf
    have hsc : ScState G A := Classical.byContradiction fun h => hnf (Or.inr h)
    refine ⟨hsc, ?_⟩
    exact (simGame_simOK G).pass_available (simReach_sim_of_sc G hre)
      (fun h => hnf (Or.inl h))
  pair_of_avail := by
    intro A m0 m1 hre hg0 hg1 h0 h1
    rw [simGameSc_pairE G A m0 m1 h0.1]
    exact (simGame_simOK G).pair_of_avail (simReach_sim_of_sc G hre) hg0 hg1 h0.2 h1.2
  avail_of_pair := by
    intro A m0 m1 hre h
    by_cases hsc : ScState G A
    · rw [simGameSc_pairE G A m0 m1 hsc] at h
      obtain ⟨h0, h1⟩ := (simGame_simOK G).avail_of_pair (simReach_sim_of_sc G hre) h
      exact ⟨⟨hsc, h0⟩, ⟨hsc, h1⟩⟩
    · rw [simGameSc_pairE_none G A m0 m1 hsc] at h
      exact absurd h (fun h => Bool.noConfusion h)
  final_exists := by
    obtain ⟨A, hA⟩ := (simGame_simOK G).final_exists
    exact ⟨A, Or.inl hA⟩

/-- Sim_sc(G) is a simultaneization of G, the branch semantics being
    the inclusion of its states in the sets of position normal forms. -/
theorem simGameSc_isSimultaneization (G : SeqGame Mv) :
    IsSimultaneization G (simGameSc G) (fun A => A.1) where
  rho_init := fun z => Iff.rfl
  nat_defined := by
    intro A m0 m1 _ h
    by_cases hsc : ScState G A
    · rw [simGameSc_pairE G A m0 m1 hsc] at h
      exact (simGame_pairE_isSome G A m0 m1).mp h
    · rw [simGameSc_pairE_none G A m0 m1 hsc] at h
      exact absurd h (fun h => Bool.noConfusion h)
  nat_incl := by
    intro A A' m0 m1 _ hp z hz
    by_cases hsc : ScState G A
    · rw [simGameSc_pairE G A m0 m1 hsc] at hp
      exact ((simGame_pairE_some G hp).2 z).mp hz
    · rw [simGameSc_pairE_none G A m0 m1 hsc] at hp
      exact absurd hp (fun h => Option.noConfusion h)
  semiclassical := by
    intro A a h
    exact semiC_eqv G (semiC_sim_of_sc G h)

/-- Faithfulness at a semi-classical state: the branch semantics is the
    singleton of the associated state, the truncation's finality agrees
    with Sim(G)'s there, and the interface is that state's. -/
theorem simGameSc_faithfulAt3 (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) :
    FaithfulAt3 G (simGameSc G) (fun A => A.1) A := by
  have hsc : ScState G A := ⟨a, h⟩
  have hmem : ∀ z, A.1 z ↔ z = a := semiC_single G h
  refine ⟨⟨a, (hmem a).mpr rfl⟩, ?_, ?_⟩
  · intro hfin
    rcases hfin with hf | hnsc
    · exact hf
    · exact absurd hsc hnsc
  · intro hnf m
    have hnfin : ¬simFinal G A.1 := fun hf => hnf (Or.inl hf)
    have hna : ¬sfinal G a := fun hf => hnfin ⟨a, (hmem a).mpr rfl, hf⟩
    constructor
    · rintro ⟨-, hd1⟩ b hb
      rw [(hmem b).mp hb]
      exact (hd1 a ((hmem a).mpr rfl)).2
    · intro hall
      refine ⟨hsc, ?_⟩
      intro b hb
      rw [(hmem b).mp hb]
      exact ⟨hna, hall a ((hmem a).mpr rfl)⟩

/-- The printed def_faithful at a semi-classical state, from the
    three-clause form. -/
theorem simGameSc_faithfulAt (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) :
    FaithfulAt G (simGameSc G) (fun A => A.1) A :=
  (faithfulAt_iff G (simGameSc G) (simGameSc_simOK G) (fun A => A.1)
    (simReach_of_semiC G (simGameSc G) (semiC_sc_of_sim G h))).2
    (simGameSc_faithfulAt3 G h)

/-- Faithful within distance zero (the printed part of (1)). -/
theorem simGameSc_faithful0 (G : SeqGame Mv) :
    FaithfulWithin G (simGameSc G) (fun A => A.1) 0 := by
  intro A h
  cases h with
  | base hsc => exact simGameSc_faithfulAt G (semiC_sim_of_sc G hsc)

/-! ### The swap carries commuting turns to commuting turns -/

/-- The composite at the normal form of the swapped state, from the
    composite at the state: the swap transport (hash2_Rst) followed by
    the turn-grading flip (hash2_flip_sN). -/
theorem hash2_swap_sN (G : SeqGame Mv) (D : SeqSymData G) (c : G.C) (m m' : Mv.M)
    {y : G.S} (h : hash2 G (PState.live c false false) m m' = some y) :
    ∃ x, hash2 G (PState.live (D.R c) false false) (D.A m) (D.A m') = some x
      ∧ sN x = sN (Rst D y) := by
  have hR := hash2_Rst D (PState.live c false false) m m'
  rw [h] at hR
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some'.mp hR
  have hwe : w = Rst D y := by rw [← hwy, Rst_Rst]
  have hw' : hash2 G (PState.live (D.R c) true false) (D.A m) (D.A m') = some w := hw
  have hflip := hash2_flip_sN G (D.R c) true (D.A m) (D.A m')
  have e : (!true) = false := rfl
  rw [e, hw'] at hflip
  obtain ⟨x, hx, hxw⟩ := Option.map_eq_some'.mp hflip
  exact ⟨x, hx, by rw [hxw, hwe]⟩

/-- R̃ preserves the semi-classical states, carrying the associated
    state a to the normal form of its swap. -/
theorem semiC_Rt (G : SeqGame Mv) (D : SeqSymData G) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) :
    SemiC G (simGame G) (Rt D A) (sN (Rst D a)) := by
  induction h with
  | init =>
    have h1 : Rt D (simGame G).q0 = (simGame G).q0 := Rt_q0 D
    have h2 : sN (Rst D (sInit G)) = sInit G := by
      show sN (PState.live (D.R G.q0) true false) = PState.live G.q0 false false
      rw [D.Rq0]; rfl
    rw [h1, h2]
    exact SemiC.init
  | @step s b s' m0 m1 hs hc hp ih =>
    obtain ⟨hd, -⟩ := simGame_pairE_some G hp
    have hmem := semiC_single G hs
    have hnb : ¬sfinal G b := (hd b ((hmem b).mpr rfl)).1
    have hnorm : sN b = b := semiC_normal G hs
    obtain ⟨c, rfl⟩ : ∃ c, b = PState.live c false false := by
      cases b with
      | done c g => exact absurd trivial hnb
      | live c g j =>
        obtain ⟨hg, hj⟩ := live_normal hnorm
        exact ⟨c, by rw [hg, hj]⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := hc
    obtain ⟨x', hx', hx'e⟩ := hash2_swap_sN G D c m1 m0 hy
    obtain ⟨y', hy', hy'e⟩ := hash2_swap_sN G D c m0 m1 hx
    have hcomm : CommuteAt G (sN (Rst D (PState.live c false false)))
        (D.A m1) (D.A m0) := by
      refine ⟨x', y', hx', hy', ?_⟩
      rw [hx'e, hy'e, ← sN_Rst_sN D y, ← sN_Rst_sN D x, hxy]
    have hpR : (simGame G).pairE (Rt D s) (D.A m1) (D.A m0) = some (Rt D s') := by
      have h := pairE_Rt D s m0 m1
      rw [hp] at h
      obtain ⟨W, hW, hWs⟩ := Option.map_eq_some'.mp h
      have hWe : W = Rt D s' := by rw [← hWs, Rt_Rt]
      rw [hW, hWe]
    have hassoc : assocOf G (sN (Rst D (PState.live c false false))) (D.A m1) (D.A m0)
        = sN (Rst D (assocOf G (PState.live c false false) m0 m1)) := by
      show sN ((hash2 G (PState.live (D.R c) false false) (D.A m1) (D.A m0)).getD
          (PState.live (D.R c) false false))
        = sN (Rst D (sN ((hash2 G (PState.live c false false) m0 m1).getD
          (PState.live c false false))))
      rw [hx', hx]
      show sN x' = sN (Rst D (sN x))
      rw [hx'e, sN_Rst_sN, ← sN_Rst_sN D y, ← sN_Rst_sN D x, hxy]
    have hstep := SemiC.step ih hcomm hpR
    rw [hassoc] at hstep
    exact hstep

theorem ScState_Rt (G : SeqGame Mv) (D : SeqSymData G) (A : NSet G) :
    ScState G (Rt D A) ↔ ScState G A := by
  constructor
  · rintro ⟨a, ha⟩
    have h := semiC_Rt G D ha
    rw [Rt_Rt] at h
    exact ⟨_, h⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, semiC_Rt G D ha⟩

/-- Sim_sc(G) is symmetric, for G symmetric: the operators of
    lem_symmetric, which preserve the semi-classical states. -/
theorem simGameSc_simSym {G : SeqGame Mv} (hG : SeqSym G) :
    SimSym (simGameSc G) Eq := by
  obtain ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩ := hG.exA
  let D : SeqSymData G := ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩
  refine ⟨A, Rt D, hAA, hAp, hAd, Rt_Rt D, Rt_q0 D, ?_, ?_, ?_⟩
  · intro s
    show (simFinal G (Rt D s).1 ∨ ¬ScState G (Rt D s)) ↔ (simFinal G s.1 ∨ ¬ScState G s)
    constructor
    · rintro (hf | hn)
      · exact Or.inl ((lem_symmetric_final D s).mp hf)
      · exact Or.inr (fun h => hn ((ScState_Rt G D s).mpr h))
    · rintro (hf | hn)
      · exact Or.inl ((lem_symmetric_final D s).mpr hf)
      · exact Or.inr (fun h => hn ((ScState_Rt G D s).mp h))
  · intro s m
    show (ScState G (Rt D s) ∧ simDef1 G (Rt D s).1 (D.A m)) ↔
      (ScState G s ∧ simDef1 G s.1 m)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(ScState_Rt G D s).mp h1, (lem_symmetric_avail D s m).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(ScState_Rt G D s).mpr h1, (lem_symmetric_avail D s m).mpr h2⟩
  · intro s m0 m1
    show OptBRel (simGameSc G) Eq
      (Option.map (Rt D) ((simGameSc G).pairE (Rt D s) (D.A m1) (D.A m0)))
      ((simGameSc G).pairE s m0 m1)
    by_cases hsc : ScState G s
    · rw [simGameSc_pairE G s m0 m1 hsc,
        simGameSc_pairE G (Rt D s) (D.A m1) (D.A m0) ((ScState_Rt G D s).mpr hsc),
        pairE_Rt D s m0 m1]
      cases (simGame G).pairE s m0 m1 with
      | none => exact trivial
      | some t => exact rfl
    · rw [simGameSc_pairE_none G s m0 m1 hsc,
        simGameSc_pairE_none G (Rt D s) (D.A m1) (D.A m0)
          (fun h => hsc ((ScState_Rt G D s).mp h))]
      exact trivial

/-! ### Interfaces of live states, and legally obtainable cores -/

/-- # at a live state of a core where the pass is defined, for a non
    pass move: the move is played at the state or at its bar, so the
    value is the core's move read at one of the two turn gradings, and
    is undefined when the move has neither grading. -/
theorem hashOp_live_nonpass (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M)
    (hm : m ≠ Mv.pass) (he : ¬G.ended c) :
    (¬(Mv.deg0 m ∨ Mv.deg1 m) ∧ hashOp G (PState.live c g j) m = none) ∨
    (∃ h : Bool, (Mv.deg0 m ∨ Mv.deg1 m) ∧
      hashOp G (PState.live c g j) m
        = (G.mv c m).map (fun c' => PState.live c' h false)) := by
  have hbar : sBar (PState.live c g j) = PState.live c (!g) (!j) := by
    cases j <;> rfl
  by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
  · have hdeg : Mv.deg0 m ∨ Mv.deg1 m := by
      rcases hg with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    refine Or.inr ⟨!g, hdeg, ?_⟩
    unfold hashOp
    rw [sE_nonpass G c g j m hm he, if_pos hg]
    cases hmv : G.mv c m with
    | some c' => rfl
    | none =>
      show sE G (sBar (PState.live c g j)) m = _
      rw [hbar, sE_nonpass G c (!g) (!j) m hm he,
        if_neg (fun h => nonpass_grade m hm g ⟨hg, h⟩)]
      rfl
  · by_cases hg2 : ((!g) = false ∧ Mv.deg0 m) ∨ ((!g) = true ∧ Mv.deg1 m)
    · have hdeg : Mv.deg0 m ∨ Mv.deg1 m := by
        rcases hg2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
      refine Or.inr ⟨!(!g), hdeg, ?_⟩
      unfold hashOp
      rw [sE_nonpass G c g j m hm he, if_neg hg]
      show sE G (sBar (PState.live c g j)) m = _
      rw [hbar, sE_nonpass G c (!g) (!j) m hm he, if_pos hg2]
    · refine Or.inl ⟨?_, ?_⟩
      · rintro (hd | hd)
        · cases g with
          | false => exact hg (Or.inl ⟨rfl, hd⟩)
          | true => exact hg2 (Or.inl ⟨rfl, hd⟩)
        · cases g with
          | false => exact hg2 (Or.inr ⟨rfl, hd⟩)
          | true => exact hg (Or.inr ⟨rfl, hd⟩)
      · unfold hashOp
        rw [sE_nonpass G c g j m hm he, if_neg hg]
        show sE G (sBar (PState.live c g j)) m = _
        rw [hbar, sE_nonpass G c (!g) (!j) m hm he, if_neg hg2]

/-- The interface of a live state depends on its core state alone. -/
theorem interface0_live_indep (G : SeqGame Mv) (c : G.C) (g j g' j' : Bool)
    (m : Mv.M) :
    Interface0 G (PState.live c g j) m ↔ Interface0 G (PState.live c g' j') m := by
  by_cases he : G.ended c
  · show (hashOp G (PState.live c g j) m).isSome
      ↔ (hashOp G (PState.live c g' j') m).isSome
    rw [hashOp_ended G he g j m, hashOp_ended G he g' j' m]
  by_cases hm : m = Mv.pass
  · subst hm
    have e : ∀ (u v : Bool), hashOp G (PState.live c u v) Mv.pass
        = some (if v then PState.done c (!u) else PState.live c (!u) true) := by
      intro u v
      unfold hashOp
      rw [sE_pass G c u v he]
    show (hashOp G (PState.live c g j) Mv.pass).isSome
      ↔ (hashOp G (PState.live c g' j') Mv.pass).isSome
    rw [e g j, e g' j']
    exact Iff.rfl
  · show (hashOp G (PState.live c g j) m).isSome
      ↔ (hashOp G (PState.live c g' j') m).isSome
    rcases hashOp_live_nonpass G c g j m hm he with ⟨hdeg, h⟩ | ⟨u, hdeg, h⟩
    · rcases hashOp_live_nonpass G c g' j' m hm he with ⟨-, h'⟩ | ⟨-, hdeg', -⟩
      · rw [h, h']
      · exact absurd hdeg' hdeg
    · rcases hashOp_live_nonpass G c g' j' m hm he with ⟨hdeg', -⟩ | ⟨u', -, h'⟩
      · exact absurd hdeg hdeg'
      · rw [h, h', isSome_map', isSome_map']

/-- # at a live state, computed: the move played at that grading. -/
theorem hashOp_move (G : SeqGame Mv) {c c' : G.C} {g j : Bool} {m : Mv.M}
    (hm : m ≠ Mv.pass) (he : ¬G.ended c)
    (hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m))
    (hmv : G.mv c m = some c') :
    hashOp G (PState.live c g j) m = some (PState.live c' (!g) false) := by
  unfold hashOp
  rw [sE_nonpass G c g j m hm he, if_pos hg, hmv]
  rfl

/-- # at a live state, computed at the bar: the move played at the
    other turn grading. -/
theorem hashOp_move_bar (G : SeqGame Mv) {c c' : G.C} {g j : Bool} {m : Mv.M}
    (hm : m ≠ Mv.pass) (he : ¬G.ended c)
    (hg : ¬((g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)))
    (hg2 : ((!g) = false ∧ Mv.deg0 m) ∨ ((!g) = true ∧ Mv.deg1 m))
    (hmv : G.mv c m = some c') :
    hashOp G (PState.live c g j) m = some (PState.live c' (!(!g)) false) := by
  have hbar : sBar (PState.live c g j) = PState.live c (!g) (!j) := by
    cases j <;> rfl
  unfold hashOp
  rw [sE_nonpass G c g j m hm he, if_neg hg]
  show sE G (sBar (PState.live c g j)) m = _
  rw [hbar, sE_nonpass G c (!g) (!j) m hm he, if_pos hg2, hmv]
  rfl

/-- # at a live state is undefined when the core has no such move. -/
theorem hashOp_none (G : SeqGame Mv) {c : G.C} {g j : Bool} {m : Mv.M}
    (hm : m ≠ Mv.pass) (he : ¬G.ended c) (hmv : G.mv c m = none) :
    hashOp G (PState.live c g j) m = none := by
  rcases hashOp_live_nonpass G c g j m hm he with ⟨-, h⟩ | ⟨u, -, h⟩
  · exact h
  · rw [h, hmv]; rfl

/-- A core state carried by a legally obtainable live state (the
    printed "legally obtainable core"). -/
def CoreOb (G : SeqGame Mv) (c : G.C) : Prop :=
  ∃ g, SeqReach G (PState.live c g false)

theorem coreOb_mv (G : SeqGame Mv) {c c' : G.C} {m : Mv.M}
    (hob : CoreOb G c) (hdeg : Mv.deg0 m ∨ Mv.deg1 m) (hm : m ≠ Mv.pass)
    (he : ¬G.ended c) (hmv : G.mv c m = some c') : CoreOb G c' := by
  obtain ⟨g0, hg0⟩ := hob
  by_cases hguard : (g0 = false ∧ Mv.deg0 m) ∨ (g0 = true ∧ Mv.deg1 m)
  · refine ⟨!g0, SeqReach.step (m := m) hg0 ?_⟩
    rw [sE_nonpass G c g0 false m hm he, if_pos hguard, hmv]
    rfl
  · have hreach2 : SeqReach G (PState.live c (!g0) true) :=
      SeqReach.step hg0 (prop_pass0 G c g0 he)
    have hguard2 : ((!g0) = false ∧ Mv.deg0 m) ∨ ((!g0) = true ∧ Mv.deg1 m) := by
      rcases hdeg with hd | hd
      · cases g0 with
        | false => exact absurd (Or.inl ⟨rfl, hd⟩) hguard
        | true => exact Or.inl ⟨rfl, hd⟩
      · cases g0 with
        | false => exact Or.inr ⟨rfl, hd⟩
        | true => exact absurd (Or.inr ⟨rfl, hd⟩) hguard
    refine ⟨!(!g0), SeqReach.step (m := m) hreach2 ?_⟩
    rw [sE_nonpass G c (!g0) true m hm he, if_pos hguard2, hmv]
    rfl

/-! ### The invariant along the # calculus -/

theorem hashOp_live_pass_false (G : SeqGame Mv) (c : G.C) (g : Bool)
    (he : ¬G.ended c) :
    hashOp G (PState.live c g false) Mv.pass = some (PState.live c (!g) true) := by
  unfold hashOp
  rw [prop_pass0 G c g he]

theorem hashOp_live_pass_true (G : SeqGame Mv) (c : G.C) (g : Bool)
    (he : ¬G.ended c) :
    hashOp G (PState.live c g true) Mv.pass = some (PState.done c (!g)) := by
  unfold hashOp
  rw [prop_pass1 G c g he]

theorem hashOp_done_eq (G : SeqGame Mv) (c : G.C) (g : Bool) (m : Mv.M) :
    hashOp G (PState.done c g) m = none := rfl

theorem coreOb_sN (G : SeqGame Mv) (x : G.S) :
    CoreOb G (PState.coreOf (sN x)) ↔ CoreOb G (PState.coreOf x) := by
  cases x <;> exact Iff.rfl

theorem hash2_split (G : SeqGame Mv) {a x : G.S} {m0 m1 : Mv.M}
    (h : hash2 G a m0 m1 = some x) :
    ∃ y, hashOp G a m0 = some y ∧ hashOp G y m1 = some x := by
  unfold hash2 at h
  cases hy : hashOp G a m0 with
  | none => rw [hy] at h; exact absurd h (fun h => Option.noConfusion h)
  | some y => rw [hy] at h; exact ⟨y, rfl, h⟩

/-- The invariant propagates from a live state: a defined # forces the
    core to be non ended (the printed axiom (1)), and then the value's
    core is the state's or a move away from it. -/
theorem coreOb_hashOp_live (G : SeqGame Mv) {c : G.C} {g j : Bool} {b' : G.S}
    {m : Mv.M} (hco : CoreOb G c) (h : hashOp G (PState.live c g j) m = some b') :
    CoreOb G (PState.coreOf b') := by
  have he : ¬G.ended c := by
    intro he
    rw [hashOp_ended G he g j m] at h
    exact Option.noConfusion h
  by_cases hm : m = Mv.pass
  · subst hm
    cases j with
    | false =>
      rw [hashOp_live_pass_false G c g he] at h
      rw [← Option.some_inj.mp h]
      exact hco
    | true =>
      rw [hashOp_live_pass_true G c g he] at h
      rw [← Option.some_inj.mp h]
      exact hco
  · rcases hashOp_live_nonpass G c g j m hm he with ⟨-, hnone⟩ | ⟨u, hdeg, he'⟩
    · rw [hnone] at h
      exact absurd h (fun h => Option.noConfusion h)
    · rw [he'] at h
      obtain ⟨c', hmv, hFc⟩ := Option.map_eq_some'.mp h
      rw [← hFc]
      exact coreOb_mv G hco hdeg hm he hmv

/-- The invariant propagates along #, at a live state and at a pair:
    the bar of a pair is live over the same core. -/
theorem coreOb_hashOp (G : SeqGame Mv) {b b' : G.S} {m : Mv.M}
    (hob : CoreOb G (PState.coreOf b)) (h : hashOp G b m = some b') :
    CoreOb G (PState.coreOf b') := by
  cases b with
  | live c g j => exact coreOb_hashOp_live G hob h
  | done c g =>
    rw [hashOp_done_eq] at h
    exact absurd h (fun h => Option.noConfusion h)

/-- Every associated state of a semi-classical state of Sim(G) has
    a legally obtainable core. -/
theorem semiC_coreOb (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) : CoreOb G (PState.coreOf a) := by
  induction h with
  | init => exact ⟨false, SeqReach.init⟩
  | @step s b s' m0 m1 _ hc hp ih =>
    obtain ⟨x, y, hx, -, -⟩ := hc
    obtain ⟨w, hw0, hw1⟩ := hash2_split G hx
    have hax : assocOf G b m0 m1 = sN x := by unfold assocOf; rw [hx]; rfl
    rw [hax, coreOb_sN]
    exact coreOb_hashOp G (coreOb_hashOp G ih hw0) hw1

/-! ### Simplicity -/

/-- Sim_sc(G) is simple: at a non final state — a semi-classical
    singleton {a} with a live — the interface is that of a legally
    obtainable state over the same core, the interface of a live state
    depending on its core alone. -/
theorem simGameSc_isSimple (G : SeqGame Mv) : IsSimple G (simGameSc G) := by
  intro A _ hnf _
  have hsc : ScState G A := Classical.byContradiction fun h => hnf (Or.inr h)
  obtain ⟨a, ha⟩ := hsc
  have hmem := semiC_single G ha
  have hnfin : ¬simFinal G A.1 := fun hf => hnf (Or.inl hf)
  have hna : ¬sfinal G a := fun hf => hnfin ⟨a, (hmem a).mpr rfl, hf⟩
  have hnorm : sN a = a := semiC_normal G ha
  obtain ⟨c, rfl⟩ : ∃ c, a = PState.live c false false := by
    cases a with
    | done c g => exact absurd trivial hna
    | live c g j =>
      obtain ⟨hg, hj⟩ := live_normal hnorm
      exact ⟨c, by rw [hg, hj]⟩
  obtain ⟨g0, hg0⟩ : CoreOb G c := semiC_coreOb G ha
  refine ⟨PState.live c g0 false, hg0, ?_⟩
  intro m
  rw [interface0_live_indep G c g0 false false false m]
  constructor
  · intro hI
    refine ⟨⟨_, ha⟩, ?_⟩
    intro b hb
    rw [(hmem b).mp hb]
    exact ⟨hna, hI⟩
  · rintro ⟨-, hd1⟩
    exact (hd1 _ ((hmem _).mpr rfl)).2

/-! ### Theorem thm_zero, part (1) -/

/-- Part (1): Sim_sc(G) is a simple simultaneization of G, faithful
    within distance zero. -/
theorem thm_zero_1 (G : SeqGame Mv) (hG : SeqSym G) :
    SimOK (simGameSc G) ∧ SimSym (simGameSc G) Eq ∧
    IsSimultaneization G (simGameSc G) (fun A => A.1) ∧
    IsSimple G (simGameSc G) ∧
    FaithfulWithin G (simGameSc G) (fun A => A.1) 0 :=
  ⟨simGameSc_simOK G, simGameSc_simSym hG, simGameSc_isSimultaneization G,
   simGameSc_isSimple G, simGameSc_faithful0 G⟩

theorem eq_isEquivB (H : SimulGame Mv) : IsEquivB H Eq :=
  ⟨fun _ => rfl, fun _ _ h => h.symm, fun _ _ _ h1 h2 => h1.trans h2⟩

/-! ### Part (2): a conflict gives radius zero -/

/-- A conflict: at a semi-classical state {a} of Sim(G) a joint move is
    available with P (a, m_0, m_1) of two elements, neither final.
    (Availability of the pair at {a} is exactly the definedness of P at
    a together with a non final — Definition
    def_formalsimultanezation; P's value is a pair by construction, so
    "two elements" is that its two members are distinct. The printed
    chess witness is of the lowest priority case of P, where neither
    composite is defined, so the hypothesis is read off P itself and
    not off the composites.) -/
def HasConflict (G : SeqGame Mv) : Prop :=
  ∃ (A : NSet G) (a : G.S) (m0 m1 : Mv.M) (P : BSet G.S) (x y : G.S),
    SemiC G (simGame G) A a ∧ ¬sfinal G a ∧ Pmap G a m0 m1 = some P ∧
    P x ∧ P y ∧ x ≠ y ∧ ∀ z, P z → ¬sfinal G z

/-- At a conflict the turn leaves the semi-classical states: the
    resulting state is final in Sim_sc(G) with no final branch, so the
    finality clause of faithfulness fails one turn from a
    semi-classical state. -/
theorem thm_zero_not_faithful1 (G : SeqGame Mv) (hc : HasConflict G) :
    ¬FaithfulWithin G (simGameSc G) (fun A => A.1) 1 := by
  obtain ⟨A, a, m0, m1, P, x, y, hsc, hna, hP, hPx, hPy, hxy, hPnf⟩ := hc
  have hmem := semiC_single G hsc
  have hdef : simDefP G A.1 m0 m1 := by
    intro b hb
    rw [(hmem b).mp hb]
    exact ⟨hna, by rw [hP]; rfl⟩
  let A' : NSet G := ⟨simVal G A.1 m0 m1, simVal_normal G A.1 m0 m1⟩
  have hpE : (simGameSc G).pairE A m0 m1 = some A' := by
    rw [simGameSc_pairE G A m0 m1 ⟨a, hsc⟩]
    exact simGame_pairE_of G A m0 m1 hdef
  have hxm : A'.1 x := ⟨a, (hmem a).mpr rfl, P, hP, hPx⟩
  have hym : A'.1 y := ⟨a, (hmem a).mpr rfl, P, hP, hPy⟩
  have hnsc : ¬ScState G A' := by
    rintro ⟨b, hb⟩
    have hb' := semiC_single G hb
    exact hxy (((hb' x).mp hxm).trans ((hb' y).mp hym).symm)
  have hnfin : ¬simFinal G A'.1 := by
    rintro ⟨z, hz, hfz⟩
    obtain ⟨b, hb, P', hP', hzP⟩ := hz
    rw [(hmem b).mp hb, hP] at hP'
    rw [(Option.some_inj.mp hP').symm] at hzP
    exact hPnf z hzP hfz
  intro hf
  have hw : WithinD G (simGameSc G) (fun A => A.1) 1 A' :=
    WithinD.step (WithinD.base (semiC_sc_of_sim G hsc)) hpE
  have h3 := (faithfulAt_iff G (simGameSc G) (simGameSc_simOK G) (fun A => A.1)
    (simReach_of_withinD G (simGameSc G) _ hw)).1 (hf A' hw)
  exact hnfin (h3.2.1 (Or.inr hnsc))

/-- Part (2): the faithfulness radius of Sim_sc(G) is exactly zero, so
    0 lies in the radius spectrum of G. -/
theorem thm_zero_2 (G : SeqGame Mv) (hG : SeqSym G) (hc : HasConflict G) :
    HasRadius G (simGameSc G) (fun A => A.1) (some 0) ∧ InSpectrum G (some 0) := by
  have hrad : HasRadius G (simGameSc G) (fun A => A.1) (some 0) :=
    ⟨simGameSc_faithful0 G, thm_zero_not_faithful1 G hc⟩
  exact ⟨hrad, ⟨simGameSc G, fun A => A.1, Eq, eq_isEquivB _, simGameSc_simOK G,
    simGameSc_simSym hG, simGameSc_isSimultaneization G, simGameSc_isSimple G,
    hrad⟩⟩

/-! ### Part (3): all turns commuting -/

/-- The associated states reachable by commuting turns available in
    Sim(G). -/
inductive ScAssoc (G : SeqGame Mv) : G.S → Prop
  | init : ScAssoc G (sInit G)
  | step {a m0 m1} : ScAssoc G a → CommuteAt G a m0 m1 →
      simDefP G (BSet.single a) m0 m1 → ScAssoc G (assocOf G a m0 m1)

/-- The hypothesis of part (3): every joint move available at a
    semi-classical state of Sim(G) commutes at its associated state. -/
def AllCommute (G : SeqGame Mv) : Prop :=
  ∀ a m0 m1, ScAssoc G a → simDefP G (BSet.single a) m0 m1 → CommuteAt G a m0 m1

/-- The associated states of any simultaneization are associated states
    of Sim(G) — by the naturality of the branch semantics alone. -/
theorem scAssoc_of_semiC (G : SeqGame Mv) (H : SimulGame Mv) (ρ : H.B → BSet G.S)
    (hsim : IsSimultaneization G H ρ) {s : H.B} {a : G.S}
    (h : SemiC G H s a) : ScAssoc G a := by
  induction h with
  | init => exact ScAssoc.init
  | @step s b s' m0 m1 hs hc hp ih =>
    refine ScAssoc.step ih hc ?_
    have hre : SimReach H s := simReach_of_semiC G H hs
    have hdef : simDefP G (ρ s) m0 m1 := hsim.nat_defined hre (by rw [hp]; rfl)
    have heq : BSet.eqv (ρ s) (BSet.single b) := hsim.semiclassical hs
    intro z hz
    exact hdef z ((heq z).mpr hz)

/-- ScAssoc is exactly the printed "associated state of a
    semi-classical state of Sim(G)": the hypothesis AllCommute is the
    printed one, read through Lemma lem_universal (a semi-classical
    state of Sim(G) is the singleton of its associated state, so a
    joint move is available there exactly when P is defined at that
    state). -/
theorem scAssoc_iff_semiC (G : SeqGame Mv) (a : G.S) :
    ScAssoc G a ↔ ∃ A : NSet G, SemiC G (simGame G) A a := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨(simGame G).q0, SemiC.init⟩
    | @step b m0 m1 _ hc hdef ih =>
      obtain ⟨A, hA⟩ := ih
      have hmem := semiC_single G hA
      have hdefA : simDefP G A.1 m0 m1 := by
        intro z hz
        exact hdef z ((hmem z).mp hz)
      exact ⟨_, SemiC.step hA hc (simGame_pairE_of G A m0 m1 hdefA)⟩
  · rintro ⟨A, hA⟩
    exact scAssoc_of_semiC G (simGame G) (fun A => A.1)
      (simGame_isSimultaneization G) hA

/-- Under the hypothesis, every state within any distance of a
    semi-classical state is itself semi-classical. -/
theorem withinD_semiC (G : SeqGame Mv) (H : SimulGame Mv) (ρ : H.B → BSet G.S)
    (hsim : IsSimultaneization G H ρ) (hall : AllCommute G) {d : Nat} {s : H.B}
    (h : WithinD G H ρ d s) : ∃ a, SemiC G H s a := by
  induction h with
  | base hsc => exact ⟨_, hsc⟩
  | ofLe _ ih => exact ih
  | @step d s s' m0 m1 _ hp ih =>
    obtain ⟨a, ha⟩ := ih
    have hre : SimReach H s := simReach_of_semiC G H ha
    have hdef : simDefP G (ρ s) m0 m1 := hsim.nat_defined hre (by rw [hp]; rfl)
    have heq := hsim.semiclassical ha
    have hdef' : simDefP G (BSet.single a) m0 m1 := fun z hz => hdef z ((heq z).mpr hz)
    exact ⟨_, SemiC.step ha (hall a m0 m1 (scAssoc_of_semiC G H ρ hsim ha) hdef') hp⟩

theorem faithfulWithin_all (G : SeqGame Mv) (H : SimulGame Mv) (ρ : H.B → BSet G.S)
    (hsim : IsSimultaneization G H ρ) (hall : AllCommute G)
    (h0 : FaithfulWithin G H ρ 0) : ∀ d, FaithfulWithin G H ρ d := by
  intro d s hw
  obtain ⟨a, ha⟩ := withinD_semiC G H ρ hsim hall hw
  exact h0 s (WithinD.base ha)

/-- Part (3): if every joint move available at a semi-classical state
    commutes, the radius spectrum of G is {∞} — every simultaneization
    with a radius has radius ∞, and Sim_sc(G) realizes it. -/
theorem thm_zero_3 (G : SeqGame Mv) (hG : SeqSym G) (hall : AllCommute G) :
    InSpectrum G none ∧ ∀ r, InSpectrum G r → r = none := by
  constructor
  · exact ⟨simGameSc G, fun A => A.1, Eq, eq_isEquivB _, simGameSc_simOK G,
      simGameSc_simSym hG, simGameSc_isSimultaneization G, simGameSc_isSimple G,
      faithfulWithin_all G (simGameSc G) (fun A => A.1)
        (simGameSc_isSimultaneization G) hall (simGameSc_faithful0 G)⟩
  · rintro r ⟨H, ρ, rel, -, -, -, hsim, -, hrad⟩
    cases r with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨hfd, hnfd⟩ := hrad
      have h0 : FaithfulWithin G H ρ 0 := by
        intro s hw
        exact hfd s (withinD_of_zero G H ρ hw d)
      exact hnfd (faithfulWithin_all G H ρ hsim hall h0 (d + 1))

/-! ### Theorem thm_zero -/

/-- Theorem thm_zero in full. -/
theorem thm_zero (G : SeqGame Mv) (hG : SeqSym G) :
    (SimOK (simGameSc G) ∧ SimSym (simGameSc G) Eq ∧
      IsSimultaneization G (simGameSc G) (fun A => A.1) ∧
      IsSimple G (simGameSc G) ∧
      FaithfulWithin G (simGameSc G) (fun A => A.1) 0)
    ∧ (HasConflict G →
      HasRadius G (simGameSc G) (fun A => A.1) (some 0) ∧ InSpectrum G (some 0))
    ∧ (AllCommute G → InSpectrum G none ∧ ∀ r, InSpectrum G r → r = none) :=
  ⟨thm_zero_1 G hG, fun hc => thm_zero_2 G hG hc, fun ha => thm_zero_3 G hG ha⟩

end SgoGames
