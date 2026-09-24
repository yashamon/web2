/- SgoSim.lean — lem_symmetric: the universal simultaneization Sim(G)
   of a symmetric sequential game G is a symmetric simultaneous game
   (def_symmetric); and Sim(G) is a combinatorial simultaneous game
   (SimOK), as def_formalsimultanezation asserts.

   Sim(G) as a SimulGame: states are the sets of position normal forms
   (2^{N(S(G))}, the subtype NSet), availability is simDef1, the pair
   map is simDefP/simVal, the initial state {q_0}, finality simFinal.
   The swap R̃ of a branch set is the set of position normal forms of
   the swapped branches, as printed; it is an exact involution, and the
   evolution commutes with it EXACTLY (rel = Eq), the printed
   "computation unaffected by the normalization" being the lemma that
   P at a live state is invariant under the turn-grading flip
   (Pmap_flip): a non pass move has one grading, so # tries it at the
   state or at its bar and lands at the same state either way; the pass
   lands at flipped states of one normal form.

   Statement audit: the printed def_symmetric also asks R̃ to map W_0
   onto W_1 and D onto D; the scoring partition is not carried by the
   formalization (unused by the theorem), so that clause has no formal
   counterpart beyond the preservation of finality (lem_symmetric_final).
   The single-move clause of def_symmetric — availability of A(m) at
   R̃(s) iff of m at s — is lem_symmetric_avail. Both are clauses of
   SimSym. -/
import SgoGames

namespace SgoGames

attribute [local instance] Classical.propDecidable

variable {Mv : Moves}

/-! ### Option helpers -/

theorem map_eq_some_of {α β : Type} {f : α → β} {o : Option α} {x : α}
    (h : o = some x) : o.map f = some (f x) := by
  rw [h]; rfl

theorem map_eq_none_of {α β : Type} {f : α → β} {o : Option α}
    (h : o = none) : o.map f = none := by
  rw [h]; rfl

theorem isSome_map' {α β : Type} (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> rfl

/-! ### The position normal form, basic facts -/

theorem sN_sN {C : Type} (x : PState C) : sN (sN x) = sN x := by
  cases x <;> rfl

theorem sfinal_sN (G : SeqGame Mv) (x : G.S) : sfinal G (sN x) ↔ sfinal G x := by
  cases x <;> exact Iff.rfl

/-- A normalized live state is the S_{0,0} state of its core. -/
theorem live_normal {C : Type} {c : C} {g j : Bool}
    (h : sN (PState.live c g j) = PState.live c g j) : g = false ∧ j = false := by
  simp only [sN] at h
  cases h; exact ⟨rfl, rfl⟩

/-! ### The serialization map, characterized -/

/-- The term of P on the m-first side: the composite if defined, else
    the single move (P's priority cases 2–4 fall back to it). -/
noncomputable def tval (G : SeqGame Mv) (a : G.S) (m m' : Mv.M) : Option G.S :=
  match hash2 G a m m' with
  | some x => some x
  | none => hashOp G a m

/-- P is the pair of the two terms' normal forms, when both are defined. -/
theorem Pmap_eq (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) :
    Pmap G a m0 m1 =
      match tval G a m0 m1, tval G a m1 m0 with
      | some x, some y => some (BSet.pair (sN x) (sN y))
      | _, _ => none := by
  unfold Pmap tval
  cases hash2 G a m0 m1 <;> cases hash2 G a m1 m0 <;>
    cases hashOp G a m0 <;> cases hashOp G a m1 <;> rfl

theorem Pmap_some_iff (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) (P : BSet G.S) :
    Pmap G a m0 m1 = some P ↔
      ∃ x y, tval G a m0 m1 = some x ∧ tval G a m1 m0 = some y ∧
        P = BSet.pair (sN x) (sN y) := by
  rw [Pmap_eq]
  constructor
  · intro h
    cases h0 : tval G a m0 m1 with
    | none => rw [h0] at h; cases h
    | some x =>
      cases h1 : tval G a m1 m0 with
      | none => rw [h0, h1] at h; cases h
      | some y =>
        rw [h0, h1] at h
        exact ⟨x, y, rfl, rfl, (Option.some_inj.mp h).symm⟩
  · rintro ⟨x, y, h0, h1, hP⟩
    rw [h0, h1, hP]

theorem Pmap_isSome_iff (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) :
    (Pmap G a m0 m1).isSome ↔
      (tval G a m0 m1).isSome ∧ (tval G a m1 m0).isSome := by
  rw [Pmap_eq]
  cases tval G a m0 m1 <;> cases tval G a m1 m0 <;> simp

/-- Every element of a value of P is a position normal form. -/
theorem Pmap_normal (G : SeqGame Mv) {a : G.S} {m0 m1 : Mv.M} {P : BSet G.S}
    (h : Pmap G a m0 m1 = some P) {z : G.S} (hz : P z) : sN z = z := by
  obtain ⟨x, y, -, -, hP⟩ := (Pmap_some_iff G a m0 m1 P).mp h
  rw [hP] at hz
  rcases hz with hz | hz <;> rw [hz, sN_sN]

theorem tval_isSome_of_hashOp (G : SeqGame Mv) (a : G.S) (m m' : Mv.M)
    (h : (hashOp G a m).isSome) : (tval G a m m').isSome := by
  unfold tval
  cases hash2 G a m m' with
  | none => exact h
  | some x => rfl

theorem hashOp_isSome_of_tval (G : SeqGame Mv) (a : G.S) (m m' : Mv.M)
    (h : (tval G a m m').isSome) : (hashOp G a m).isSome := by
  unfold tval at h
  cases h2 : hash2 G a m m' with
  | none => rw [h2] at h; exact h
  | some x =>
    unfold hash2 at h2
    obtain ⟨b, hb, -⟩ := Option.bind_eq_some.mp h2
    rw [hb]; rfl

/-- P is insensitive to the order of its two moves. -/
theorem Pmap_comm (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) :
    Pmap G a m0 m1 = Pmap G a m1 m0 := by
  rw [Pmap_eq, Pmap_eq]
  cases tval G a m0 m1 with
  | none => cases tval G a m1 m0 <;> rfl
  | some x =>
    cases tval G a m1 m0 with
    | none => rfl
    | some y =>
      show some (BSet.pair (sN x) (sN y)) = some (BSet.pair (sN y) (sN x))
      congr 1
      funext z
      exact propext Or.comm

/-- Congruence of P in its state, through the normal forms of the terms. -/
theorem Pmap_congr (G : SeqGame Mv) {a a' : G.S} {m0 m1 : Mv.M}
    (h0 : (tval G a m0 m1).map sN = (tval G a' m0 m1).map sN)
    (h1 : (tval G a m1 m0).map sN = (tval G a' m1 m0).map sN) :
    Pmap G a m0 m1 = Pmap G a' m0 m1 := by
  rw [Pmap_eq, Pmap_eq]
  cases hx : tval G a m0 m1 with
  | none =>
    rw [hx] at h0
    have := (Option.map_eq_none'.mp h0.symm)
    rw [this]
  | some x =>
    rw [hx] at h0
    obtain ⟨x', hx', hxx⟩ := Option.map_eq_some'.mp h0.symm
    rw [hx']
    cases hy : tval G a m1 m0 with
    | none =>
      rw [hy] at h1
      have := (Option.map_eq_none'.mp h1.symm)
      rw [this]
    | some y =>
      rw [hy] at h1
      obtain ⟨y', hy', hyy⟩ := Option.map_eq_some'.mp h1.symm
      rw [hy']
      show some (BSet.pair (sN x) (sN y)) = some (BSet.pair (sN x') (sN y'))
      rw [hxx, hyy]

/-! ### The turn-grading flip -/

def flipG {C : Type} : PState C → PState C
  | .live c g j => .live c (!g) j
  | .done c g => .done c (!g)

theorem sN_flipG {C : Type} (x : PState C) : sN (flipG x) = sN x := by
  cases x <;> rfl

/-- A non pass move has at most one grading. -/
theorem nonpass_grade (m : Mv.M) (hm : m ≠ Mv.pass) (g : Bool) :
    ¬(((g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)) ∧
      (((!g) = false ∧ Mv.deg0 m) ∨ ((!g) = true ∧ Mv.deg1 m))) := by
  rintro ⟨h1, h2⟩
  apply hm
  cases g with
  | false =>
    rcases h1 with ⟨-, h0⟩ | ⟨h, -⟩
    · rcases h2 with ⟨h, -⟩ | ⟨-, hd1⟩
      · cases h
      · exact Mv.pass_unique m h0 hd1
    · cases h
  | true =>
    rcases h1 with ⟨h, -⟩ | ⟨-, hd1⟩
    · cases h
    · rcases h2 with ⟨-, h0⟩ | ⟨h, -⟩
      · exact Mv.pass_unique m h0 hd1
      · cases h

/-- # at a live state is insensitive to the turn grading: exactly for a
    non pass move (one grading: the move is tried at the state or at
    its bar, landing at the same state), up to the flip for the pass. -/
theorem hashOp_flip (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M) :
    (m = Mv.pass ∧
      hashOp G (.live c (!g) j) m = (hashOp G (.live c g j) m).map flipG) ∨
    (m ≠ Mv.pass ∧ hashOp G (.live c (!g) j) m = hashOp G (.live c g j) m) := by
  by_cases he : G.ended c
  · -- an ended core: nothing is defined at any state over it, its
    -- bars included (the printed axiom (1)).
    have hnone : ∀ (u v : Bool), hashOp G (PState.live c u v) m = none :=
      fun u v => hashOp_ended G he u v m
    by_cases hm : m = Mv.pass
    · exact Or.inl ⟨hm, by rw [hnone, hnone]; rfl⟩
    · exact Or.inr ⟨hm, by rw [hnone, hnone]⟩
  by_cases hm : m = Mv.pass
  · left; refine ⟨hm, ?_⟩
    subst hm
    unfold hashOp
    rw [sE_pass G c (!g) j he, sE_pass G c g j he]
    cases j <;> simp [flipG, Bool.not_not]
  · right; refine ⟨hm, ?_⟩
    unfold hashOp
    rw [sE_nonpass G c (!g) j m hm he, sE_nonpass G c g j m hm he]
    have hbar1 : sBar (PState.live c (!g) j) = PState.live c g (!j) := by
      cases j <;> simp [sBar, Bool.not_not]
    have hbar2 : sBar (PState.live c g j) = PState.live c (!g) (!j) := by
      cases j <;> simp [sBar]
    rw [hbar1, hbar2, sE_nonpass G c g (!j) m hm he, sE_nonpass G c (!g) (!j) m hm he]
    by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
    · have hng : ¬(((!g) = false ∧ Mv.deg0 m) ∨ ((!g) = true ∧ Mv.deg1 m)) :=
        fun h => nonpass_grade m hm g ⟨hg, h⟩
      rw [if_pos hg, if_neg hng]
      cases G.mv c m <;> rfl
    · by_cases hng : ((!g) = false ∧ Mv.deg0 m) ∨ ((!g) = true ∧ Mv.deg1 m)
      · rw [if_pos hng, if_neg hg]
        cases G.mv c m <;> rfl
      · rw [if_neg hng, if_neg hg]

theorem hashOp_flip_sN (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M) :
    (hashOp G (.live c (!g) j) m).map sN = (hashOp G (.live c g j) m).map sN := by
  rcases hashOp_flip G c g j m with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h, Option.map_map]
    congr 1
    funext x
    exact sN_flipG x
  · rw [h]

/-- The composite from a pass-grading-0 live state, up to normal forms. -/
theorem hash2_flip_sN (G : SeqGame Mv) (c : G.C) (g : Bool) (m0 m1 : Mv.M) :
    (hash2 G (.live c (!g) false) m0 m1).map sN
      = (hash2 G (.live c g false) m0 m1).map sN := by
  by_cases he : G.ended c
  · unfold hash2
    rw [hashOp_ended G he (!g) false m0, hashOp_ended G he g false m0]
  unfold hash2
  rcases hashOp_flip G c g false m0 with ⟨hm0, h⟩ | ⟨-, h⟩
  · subst hm0
    rw [h]
    unfold hashOp
    rw [sE_pass G c g false he]
    simp only [Option.map_some', Option.some_bind, if_false]
    show (hashOp G (flipG (.live c (!g) true)) m1).map sN
      = (hashOp G (.live c (!g) true) m1).map sN
    have : flipG (PState.live c (!g) true) = PState.live c (!(!g)) true := rfl
    rw [this]
    exact hashOp_flip_sN G c (!g) true m1
  · rw [h]

theorem tval_flip_sN (G : SeqGame Mv) (c : G.C) (g : Bool) (m m' : Mv.M) :
    (tval G (.live c (!g) false) m m').map sN
      = (tval G (.live c g false) m m').map sN := by
  unfold tval
  have h2 := hash2_flip_sN G c g m m'
  cases hx : hash2 G (.live c g false) m m' with
  | none =>
    rw [hx] at h2
    rw [Option.map_eq_none'.mp h2]
    exact hashOp_flip_sN G c g false m
  | some x =>
    rw [hx] at h2
    obtain ⟨x', hx', hxx⟩ := Option.map_eq_some'.mp h2
    rw [hx']
    simp only [Option.map_some']
    rw [hxx]

/-- P at a live state of pass grading 0 is invariant under the flip of
    the turn grading. -/
theorem Pmap_flip (G : SeqGame Mv) (c : G.C) (g : Bool) (m0 m1 : Mv.M) :
    Pmap G (.live c (!g) false) m0 m1 = Pmap G (.live c g false) m0 m1 :=
  Pmap_congr G (tval_flip_sN G c g m0 m1) (tval_flip_sN G c g m1 m0)

/-! ### Sim(G) as a simultaneous game -/

/-- The state space of Sim(G): sets of position normal forms. -/
def NSet (G : SeqGame Mv) : Type := { A : BSet G.S // ∀ a, A a → sN a = a }

theorem simVal_normal (G : SeqGame Mv) (A : BSet G.S) (m0 m1 : Mv.M) :
    ∀ z, simVal G A m0 m1 z → sN z = z := by
  rintro z ⟨a, -, P, hP, hz⟩
  exact Pmap_normal G hP hz

/-- The universal simultaneization Sim(G). -/
noncomputable def simGame (G : SeqGame Mv) : SimulGame Mv where
  B := NSet G
  avail := fun A m => simDef1 G A.1 m
  pairE := fun A m0 m1 =>
    if simDefP G A.1 m0 m1 then
      some ⟨simVal G A.1 m0 m1, simVal_normal G A.1 m0 m1⟩
    else none
  q0 := ⟨BSet.single (sInit G), fun a ha => by
    change a = _ at ha
    rw [ha]; rfl⟩
  final := fun A => simFinal G A.1

theorem simGame_pairE_isSome (G : SeqGame Mv) (A : NSet G) (m0 m1 : Mv.M) :
    ((simGame G).pairE A m0 m1).isSome ↔ simDefP G A.1 m0 m1 := by
  show (if simDefP G A.1 m0 m1 then some _ else none).isSome ↔ _
  by_cases h : simDefP G A.1 m0 m1
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun h' => Bool.noConfusion h', fun h' => absurd h' h⟩

/-- Sim(G) is a combinatorial simultaneous game (the properties of
    def_simultaneous carried by SimOK). -/
theorem simGame_simOK (G : SeqGame Mv) : SimOK (simGame G) where
  final_nomove := by
    intro A m _ hfin hav
    obtain ⟨a, ha, hfa⟩ := hfin
    exact (hav a ha).1 hfa
  pass_available := by
    intro A _ hnf a ha
    refine ⟨fun hf => hnf ⟨a, ha, hf⟩, ?_⟩
    cases a with
    | done c g => exact absurd trivial (fun _ => hnf ⟨_, ha, trivial⟩)
    | live c g j =>
      unfold hashOp
      rw [sE_pass G c g j (fun he => hnf ⟨_, ha, he⟩)]
      rfl
  pair_of_avail := by
    intro A m0 m1 _ _ _ h0 h1
    rw [simGame_pairE_isSome]
    intro a ha
    refine ⟨(h0 a ha).1, ?_⟩
    rw [Pmap_isSome_iff]
    exact ⟨tval_isSome_of_hashOp G a m0 m1 (h0 a ha).2,
      tval_isSome_of_hashOp G a m1 m0 (h1 a ha).2⟩
  avail_of_pair := by
    intro A m0 m1 _ h
    have hd := (simGame_pairE_isSome G A m0 m1).mp h
    constructor
    · intro a ha
      refine ⟨(hd a ha).1, ?_⟩
      exact hashOp_isSome_of_tval G a m0 m1 ((Pmap_isSome_iff G a m0 m1).mp (hd a ha).2).1
    · intro a ha
      refine ⟨(hd a ha).1, ?_⟩
      exact hashOp_isSome_of_tval G a m1 m0 ((Pmap_isSome_iff G a m0 m1).mp (hd a ha).2).2
  final_exists :=
    ⟨⟨BSet.single (PState.done G.q0 false), fun a ha => by
        change a = _ at ha
        rw [ha]; rfl⟩,
      PState.done G.q0 false, rfl, trivial⟩

/-! ### The symmetry operators of G, on states -/

/-- The data of def_symmetricsequential. -/
structure SeqSymData (G : SeqGame Mv) where
  A : Mv.M → Mv.M
  R : G.C → G.C
  AA : ∀ m, A (A m) = m
  Apass : A Mv.pass = Mv.pass
  Adeg : ∀ m, Mv.deg0 m ↔ Mv.deg1 (A m)
  RR : ∀ c, R (R c) = c
  Rq0 : R G.q0 = G.q0
  Rend : ∀ c, G.ended (R c) ↔ G.ended c
  Rmv : ∀ c m, Option.map R (G.mv (R c) (A m)) = G.mv c m

variable {G : SeqGame Mv}

theorem SeqSymData.Adeg1 (D : SeqSymData G) (m : Mv.M) :
    Mv.deg1 m ↔ Mv.deg0 (D.A m) := by
  have := D.Adeg (D.A m)
  rw [D.AA] at this
  exact this.symm

theorem SeqSymData.Apass_iff (D : SeqSymData G) (m : Mv.M) :
    D.A m = Mv.pass ↔ m = Mv.pass := by
  constructor
  · intro h
    have := congrArg D.A h
    rw [D.AA, D.Apass] at this
    exact this
  · intro h; rw [h, D.Apass]

/-- R extended to the states: the core swapped, the turn grading
    flipped, the pass grading kept (def_symmetricsequential). -/
def Rst (D : SeqSymData G) : G.S → G.S
  | .live c g j => .live (D.R c) (!g) j
  | .done c g => .done (D.R c) (!g)

theorem Rst_Rst (D : SeqSymData G) (s : G.S) : Rst D (Rst D s) = s := by
  cases s <;> simp [Rst, D.RR, Bool.not_not]

theorem sfinal_Rst (D : SeqSymData G) (s : G.S) :
    sfinal G (Rst D s) ↔ sfinal G s := by
  cases s with
  | live c g j => exact D.Rend c
  | done c g => exact Iff.rfl

theorem sN_Rst_sN (D : SeqSymData G) (x : G.S) :
    sN (Rst D (sN x)) = sN (Rst D x) := by
  cases x <;> rfl

theorem sBar_Rst (D : SeqSymData G) (s : G.S) :
    sBar (Rst D s) = Rst D (sBar s) := by
  cases s with
  | live c g j => cases j <;> simp [sBar, Rst, Bool.not_not]
  | done c g => simp [sBar, Rst, Bool.not_not]

/-- The grading guard, swapped. -/
theorem grade_swap (D : SeqSymData G) (g : Bool) (m : Mv.M) :
    (((!g) = false ∧ Mv.deg0 (D.A m)) ∨ ((!g) = true ∧ Mv.deg1 (D.A m))) ↔
      ((g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)) := by
  cases g with
  | false =>
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (by decide)
      · exact Or.inl ⟨rfl, (D.Adeg m).mpr h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨rfl, (D.Adeg m).mp h⟩
      · exact absurd h (by decide)
  | true =>
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨rfl, (D.Adeg1 m).mpr h⟩
      · exact absurd h (by decide)
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (by decide)
      · exact Or.inl ⟨rfl, (D.Adeg1 m).mp h⟩

/-- The extended R intertwines the evolution (by construction, as
    printed in def_symmetricsequential). -/
theorem sE_Rst (D : SeqSymData G) (s : G.S) (m : Mv.M) :
    Option.map (Rst D) (sE G (Rst D s) (D.A m)) = sE G s m := by
  cases s with
  | done c g => rfl
  | live c g j =>
    by_cases he : G.ended c
    · have heR : G.ended (D.R c) := (D.Rend c).mpr he
      show Option.map (Rst D) (sE G (.live (D.R c) (!g) j) (D.A m)) = _
      rw [prop_finalnomove G (s := PState.live (D.R c) (!g) j) heR (D.A m),
        prop_finalnomove G (s := PState.live c g j) he m]
      rfl
    · have heR : ¬G.ended (D.R c) := fun h => he ((D.Rend c).mp h)
      by_cases hm : m = Mv.pass
      · subst hm
        show Option.map (Rst D) (sE G (.live (D.R c) (!g) j) (D.A Mv.pass)) = _
        rw [D.Apass, sE_pass G (D.R c) (!g) j heR, sE_pass G c g j he]
        cases j <;> simp [Rst, D.RR, Bool.not_not]
      · have hAm : D.A m ≠ Mv.pass := fun h => hm ((D.Apass_iff m).mp h)
        show Option.map (Rst D) (sE G (.live (D.R c) (!g) j) (D.A m)) = _
        rw [sE_nonpass G (D.R c) (!g) j (D.A m) hAm heR,
          sE_nonpass G c g j m hm he]
        by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
        · rw [if_pos ((grade_swap D g m).mpr hg), if_pos hg, ← D.Rmv c m,
            Option.map_map, Option.map_map]
          congr 1
          funext c'
          simp [Rst, D.RR, Bool.not_not]
        · rw [if_neg (fun h => hg ((grade_swap D g m).mp h)), if_neg hg]
          rfl

theorem hashOp_Rst (D : SeqSymData G) (s : G.S) (m : Mv.M) :
    Option.map (Rst D) (hashOp G (Rst D s) (D.A m)) = hashOp G s m := by
  cases s with
  | done c g =>
    show Option.map (Rst D) (hashOp G (PState.done (D.R c) (!g)) (D.A m)) = _
    rw [hashOp_done, hashOp_done]; rfl
  | live c g j =>
    show Option.map (Rst D) (hashOp G (PState.live (D.R c) (!g) j) (D.A m)) = _
    rw [hashOp_live, hashOp_live]
    have h := sE_Rst D (PState.live c g j) m
    cases hs : sE G (PState.live c g j) m with
    | some b =>
      rw [hs] at h
      obtain ⟨b', hb', -⟩ := Option.map_eq_some'.mp h
      have hb'' : sE G (PState.live (D.R c) (!g) j) (D.A m) = some b' := hb'
      rw [hb'']
      rw [hb'] at h
      exact h
    | none =>
      rw [hs] at h
      have hn : sE G (PState.live (D.R c) (!g) j) (D.A m) = none :=
        Option.map_eq_none'.mp h
      rw [hn]
      show Option.map (Rst D) (sE G (sBar (Rst D (PState.live c g j))) (D.A m))
        = sE G (sBar (PState.live c g j)) m
      rw [sBar_Rst]
      exact sE_Rst D (sBar (PState.live c g j)) m

theorem hash2_Rst (D : SeqSymData G) (a : G.S) (m0 m1 : Mv.M) :
    Option.map (Rst D) (hash2 G (Rst D a) (D.A m0) (D.A m1)) = hash2 G a m0 m1 := by
  unfold hash2
  have h := hashOp_Rst D a m0
  cases hs : hashOp G a m0 with
  | some b =>
    rw [hs] at h
    obtain ⟨b', hb', hbb⟩ := Option.map_eq_some'.mp h
    rw [hb']
    simp only [Option.some_bind]
    have hb : b' = Rst D b := by rw [← hbb, Rst_Rst]
    rw [hb]
    exact hashOp_Rst D b m1
  | none =>
    rw [hs] at h
    rw [Option.map_eq_none'.mp h]
    rfl

theorem tval_Rst (D : SeqSymData G) (a : G.S) (m m' : Mv.M) :
    Option.map (Rst D) (tval G (Rst D a) (D.A m) (D.A m')) = tval G a m m' := by
  unfold tval
  have h := hash2_Rst D a m m'
  cases hs : hash2 G a m m' with
  | some b =>
    rw [hs] at h
    obtain ⟨b', hb', hbb⟩ := Option.map_eq_some'.mp h
    rw [hb']
    simp only [Option.map_some']
    rw [hbb]
  | none =>
    rw [hs] at h
    rw [Option.map_eq_none'.mp h]
    exact hashOp_Rst D a m

/-- The image of a branch set under the normalized swap. -/
def imgN (D : SeqSymData G) (P : BSet G.S) : BSet G.S :=
  fun z => ∃ w, P w ∧ z = sN (Rst D w)

/-- P intertwines the swap: P(a, m0, m1) is the normalized image of
    P(R a, A m0, A m1) (the printed identity (eq_identity1) lifted). -/
theorem Pmap_Rst (D : SeqSymData G) (a : G.S) (m0 m1 : Mv.M) :
    Pmap G a m0 m1 = (Pmap G (Rst D a) (D.A m0) (D.A m1)).map (imgN D) := by
  rw [Pmap_eq, Pmap_eq]
  have h0 := tval_Rst D a m0 m1
  have h1 := tval_Rst D a m1 m0
  cases hx : tval G (Rst D a) (D.A m0) (D.A m1) with
  | none =>
    rw [hx] at h0
    simp only [Option.map_none'] at h0
    rw [← h0]
    cases tval G (Rst D a) (D.A m1) (D.A m0) <;> rfl
  | some x' =>
    rw [hx] at h0
    simp only [Option.map_some'] at h0
    rw [← h0]
    cases hy : tval G (Rst D a) (D.A m1) (D.A m0) with
    | none =>
      rw [hy] at h1
      simp only [Option.map_none'] at h1
      rw [← h1]
      rfl
    | some y' =>
      rw [hy] at h1
      simp only [Option.map_some'] at h1
      rw [← h1]
      show some (BSet.pair (sN (Rst D x')) (sN (Rst D y')))
        = some (imgN D (BSet.pair (sN x') (sN y')))
      congr 1
      funext z
      apply propext
      constructor
      · rintro (hz | hz)
        · exact ⟨sN x', Or.inl rfl, by rw [hz, sN_Rst_sN]⟩
        · exact ⟨sN y', Or.inr rfl, by rw [hz, sN_Rst_sN]⟩
      · rintro ⟨w, hw | hw, hz⟩
        · left; rw [hz, hw, sN_Rst_sN]
        · right; rw [hz, hw, sN_Rst_sN]

/-- At a normalized live state, P at the normal form of the swapped
    state is P at the swapped state (the flip invariance). -/
theorem Pmap_sN_Rst (D : SeqSymData G) (c : G.C) (m0 m1 : Mv.M) :
    Pmap G (sN (Rst D (.live c false false))) m0 m1
      = Pmap G (Rst D (.live c false false)) m0 m1 := by
  show Pmap G (.live (D.R c) false false) m0 m1
    = Pmap G (.live (D.R c) true false) m0 m1
  have := Pmap_flip G (D.R c) true m0 m1
  exact this

/-! ### The swap of Sim(G) -/

/-- R̃: the position normal forms of the swapped branches. -/
def Rt (D : SeqSymData G) (A : NSet G) : NSet G :=
  ⟨fun z => ∃ w, A.1 w ∧ z = sN (Rst D w), fun z hz => by
    obtain ⟨w, -, hz⟩ := hz
    rw [hz, sN_sN]⟩

theorem NSet.ext {A B : NSet G} (h : ∀ z, A.1 z ↔ B.1 z) : A = B :=
  Subtype.ext (funext fun z => propext (h z))

theorem Rt_Rt (D : SeqSymData G) (A : NSet G) : Rt D (Rt D A) = A := by
  apply NSet.ext
  intro z
  constructor
  · rintro ⟨w, ⟨v, hv, hw⟩, hz⟩
    rw [hz, hw, sN_Rst_sN, Rst_Rst, A.2 v hv]
    exact hv
  · intro hz
    refine ⟨sN (Rst D z), ⟨z, hz, rfl⟩, ?_⟩
    rw [sN_Rst_sN, Rst_Rst, A.2 z hz]

theorem Rt_q0 (D : SeqSymData G) : Rt D (simGame G).q0 = (simGame G).q0 := by
  apply NSet.ext
  intro z
  constructor
  · rintro ⟨w, hw, hz⟩
    change w = sInit G at hw
    show z = sInit G
    rw [hz, hw]
    show sN (Rst D (.live G.q0 false false)) = PState.live G.q0 false false
    simp [Rst, sN, D.Rq0]
  · intro hz
    change z = sInit G at hz
    refine ⟨sInit G, rfl, ?_⟩
    rw [hz]
    show PState.live G.q0 false false = sN (Rst D (.live G.q0 false false))
    simp [Rst, sN, D.Rq0]

/-- Finality is preserved by R̃. -/
theorem lem_symmetric_final (D : SeqSymData G) (A : NSet G) :
    (simGame G).final (Rt D A) ↔ (simGame G).final A := by
  constructor
  · rintro ⟨z, ⟨w, hw, hz⟩, hf⟩
    refine ⟨w, hw, ?_⟩
    rw [hz, sfinal_sN, sfinal_Rst] at hf
    exact hf
  · rintro ⟨w, hw, hf⟩
    refine ⟨sN (Rst D w), ⟨w, hw, rfl⟩, ?_⟩
    rw [sfinal_sN, sfinal_Rst]
    exact hf

/-- A live element of a normalized set is the S_{0,0} state of its core. -/
theorem NSet.live_shape (A : NSet G) {a : G.S} (ha : A.1 a) (hnf : ¬sfinal G a) :
    ∃ c, a = PState.live c false false := by
  cases a with
  | done c g => exact absurd trivial hnf
  | live c g j =>
    obtain ⟨hg, hj⟩ := live_normal (A.2 _ ha)
    exact ⟨c, by rw [hg, hj]⟩

/-- The single-move clause of def_symmetric for Sim(G): A(m) is
    available at R̃(s) iff m is available at s. -/
theorem lem_symmetric_avail (D : SeqSymData G) (A : NSet G) (m : Mv.M) :
    (simGame G).avail (Rt D A) (D.A m) ↔ (simGame G).avail A m := by
  constructor
  · intro h a ha
    obtain ⟨hnf, hs⟩ := h (sN (Rst D a)) ⟨a, ha, rfl⟩
    rw [sfinal_sN, sfinal_Rst] at hnf
    refine ⟨hnf, ?_⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha hnf
    have hflip := hashOp_flip_sN G (D.R c) true false (D.A m)
    have hR := hashOp_Rst D (.live c false false) m
    change (hashOp G (.live (D.R c) false false) (D.A m)).isSome at hs
    rw [← hR, isSome_map' _ _]
    show (hashOp G (.live (D.R c) true false) (D.A m)).isSome
    have e : (!true) = false := rfl
    rw [e] at hflip
    have := congrArg Option.isSome hflip
    rw [isSome_map' _ _, isSome_map' _ _] at this
    rw [← this]; exact hs
  · rintro h z ⟨a, ha, hz⟩
    obtain ⟨hnf, hs⟩ := h a ha
    subst hz
    refine ⟨by rw [sfinal_sN, sfinal_Rst]; exact hnf, ?_⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha hnf
    have hflip := hashOp_flip_sN G (D.R c) true false (D.A m)
    have hR := hashOp_Rst D (.live c false false) m
    rw [← hR, isSome_map' _ _] at hs
    show (hashOp G (.live (D.R c) false false) (D.A m)).isSome
    have e : (!true) = false := rfl
    rw [e] at hflip
    have := congrArg Option.isSome hflip
    rw [isSome_map' _ _, isSome_map' _ _] at this
    rw [this]; exact hs

/-- Pair definedness transports along R̃ (the slots swapped: A(m1) is
    Black's move at the swapped state). -/
theorem simDefP_Rt (D : SeqSymData G) (A : NSet G) (m0 m1 : Mv.M) :
    simDefP G (Rt D A).1 (D.A m1) (D.A m0) ↔ simDefP G A.1 m0 m1 := by
  constructor
  · intro h a ha
    obtain ⟨hnf, hs⟩ := h (sN (Rst D a)) ⟨a, ha, rfl⟩
    rw [sfinal_sN, sfinal_Rst] at hnf
    refine ⟨hnf, ?_⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha hnf
    rw [Pmap_sN_Rst, Pmap_comm] at hs
    rw [Pmap_Rst D, isSome_map' _ _]
    exact hs
  · rintro h z ⟨a, ha, hz⟩
    obtain ⟨hnf, hs⟩ := h a ha
    subst hz
    refine ⟨by rw [sfinal_sN, sfinal_Rst]; exact hnf, ?_⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha hnf
    rw [Pmap_sN_Rst, Pmap_comm]
    rw [Pmap_Rst D, isSome_map' _ _] at hs
    exact hs

/-- The pair value transports along R̃ (at a defined pair). -/
theorem simVal_Rt (D : SeqSymData G) (A : NSet G) (m0 m1 : Mv.M)
    (hd : simDefP G A.1 m0 m1) (z : G.S) :
    simVal G A.1 m0 m1 z ↔ imgN D (simVal G (Rt D A).1 (D.A m1) (D.A m0)) z := by
  constructor
  · rintro ⟨a, ha, P, hP, hz⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha (hd a ha).1
    rw [Pmap_Rst D] at hP
    obtain ⟨P', hP', hPP⟩ := Option.map_eq_some'.mp hP
    rw [← hPP] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    refine ⟨w, ⟨sN (Rst D (.live c false false)), ⟨_, ha, rfl⟩, P', ?_, hw⟩, hzw⟩
    rw [Pmap_sN_Rst, Pmap_comm]
    exact hP'
  · rintro ⟨w, ⟨z', ⟨a, ha, hz'⟩, P', hP', hw⟩, hzw⟩
    obtain ⟨c, rfl⟩ := A.live_shape ha (hd a ha).1
    subst hz'
    rw [Pmap_sN_Rst, Pmap_comm] at hP'
    refine ⟨_, ha, imgN D P', ?_, w, hw, hzw⟩
    rw [Pmap_Rst D, hP']
    rfl

/-- The evolution of Sim(G) commutes with the swap, exactly. -/
theorem pairE_Rt (D : SeqSymData G) (A : NSet G) (m0 m1 : Mv.M) :
    Option.map (Rt D) ((simGame G).pairE (Rt D A) (D.A m1) (D.A m0))
      = (simGame G).pairE A m0 m1 := by
  show Option.map (Rt D)
      (if simDefP G (Rt D A).1 (D.A m1) (D.A m0) then some _ else none)
    = (if simDefP G A.1 m0 m1 then some _ else none)
  by_cases hd : simDefP G A.1 m0 m1
  · rw [if_pos ((simDefP_Rt D A m0 m1).mpr hd), if_pos hd]
    simp only [Option.map_some']
    congr 1
    apply NSet.ext
    intro z
    exact (simVal_Rt D A m0 m1 hd z).symm
  · rw [if_neg (fun h => hd ((simDefP_Rt D A m0 m1).mp h)), if_neg hd]
    rfl

/-- lem_symmetric: Sim(G) is symmetric, for G symmetric — the swap
    operators Ã = A and R̃ as printed, R̃ an exact involution fixing
    {q_0}, the evolution commuting exactly (rel = Eq). -/
theorem lem_symmetric (hG : SeqSym G) : SimSym (simGame G) Eq := by
  obtain ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩ := hG.exA
  let D : SeqSymData G := ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩
  refine ⟨A, Rt D, hAA, hAp, hAd, Rt_Rt D, Rt_q0 D, lem_symmetric_final D,
    lem_symmetric_avail D, ?_⟩
  intro s m0 m1
  have h := pairE_Rt D s m0 m1
  show OptBRel (simGame G) Eq
    (Option.map (Rt D) ((simGame G).pairE (Rt D s) (D.A m1) (D.A m0)))
    ((simGame G).pairE s m0 m1)
  rw [h]
  cases (simGame G).pairE s m0 m1 with
  | none => exact trivial
  | some t => exact rfl

end SgoGames
