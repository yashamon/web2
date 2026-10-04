/- SgoBisim.lean — bisimulation, the minimal quotient and the radius
   spectrum (Definition def_bisimulation, Lemma lem_bisimulation).

   A bisimulation between two sequential games G, G' with the same
   graded moves is a relation on cores relating the initial cores and
   such that, at related cores x ~ x', every turn grading i, pass
   grading j < 2 and move m: E ((x,i,j),m) is defined exactly when
   E' ((x',i,j),m) is, and the cores of the two values are related
   (`IsBisim`). Bisimilarity on G is the union of the bisimulations on
   G (`Bisimilar`): an equivalence relation and itself a bisimulation.

   The minimal quotient G/~ (`QGame`) has the core states the classes
   of the legally obtainable cores — the print's C (G), by its
   convention, consists of these — with the initial class [x_0], the
   evolution [E ((x,i,j),m)] = E (([x],i,j),m), and the ended classes
   those of the ended cores; its scoring is not carried (all finals
   drawn, as printed). The radius spectrum of G is the raw radius
   spectrum (`InSpectrum`) of G/~ (`InRadiusSpectrum`); G is minimal
   when bisimilar legally obtainable cores are equal (`Minimal`).

   Statement audit. The projection π (`qS`) is extended to all states
   by sending an unobtainable core to the class of x_0; every lemma
   about it carries the hypothesis `CoreOb` where the print's
   convention makes it automatic, and the states that the theory reads
   — reachable states, branches of a branch semantics at a reachable
   state, associated states — all have obtainable cores
   (`coreOb_of_seqReach`, `rho_coreOb`, `semiC_coreOb`). -/
import SgoZero

namespace SgoGames

attribute [local instance] Classical.propDecidable

variable {Mv : Moves}

/-! ### Bisimulations -/

/-- A relation on cores, read on the optional values of the evolution:
    both undefined, or both defined with related cores. -/
def OptCoreRel {G G' : SeqGame Mv} (R : G.C → G'.C → Prop) :
    Option G.S → Option G'.S → Prop
  | none, none => True
  | some s, some s' => R s.coreOf s'.coreOf
  | _, _ => False

/-- A relation on cores, read on the optional values of the action. -/
def OptRelC {C C' : Type} (R : C → C' → Prop) : Option C → Option C' → Prop
  | none, none => True
  | some c, some c' => R c c'
  | _, _ => False

/-- def_bisimulation: a bisimulation between G and G'. -/
structure IsBisim (G G' : SeqGame Mv) (R : G.C → G'.C → Prop) : Prop where
  init : R G.q0 G'.q0
  step : ∀ x x', R x x' → ∀ (g j : Bool) (m : Mv.M),
    OptCoreRel R (sE G (.live x g j) m) (sE G' (.live x' g j) m)

/-- Bisimilarity on G: related by some bisimulation on G. -/
def Bisimilar (G : SeqGame Mv) (x y : G.C) : Prop :=
  ∃ R, IsBisim G G R ∧ R x y

/-- Bisimilar games. -/
def GamesBisimilar (G G' : SeqGame Mv) : Prop := ∃ R, IsBisim G G' R

theorem optCoreRel_none {G G' : SeqGame Mv} (R : G.C → G'.C → Prop)
    {o : Option G.S} {o' : Option G'.S} (h : OptCoreRel R o o') :
    o = none ↔ o' = none := by
  cases o with
  | none =>
    cases o' with
    | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | some _ => exact False.elim h
  | some _ =>
    cases o' with
    | none => exact False.elim h
    | some _ => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h⟩

theorem optCoreRel_some {G G' : SeqGame Mv} (R : G.C → G'.C → Prop)
    {o : Option G.S} {o' : Option G'.S} (h : OptCoreRel R o o') {s : G.S}
    (hs : o = some s) : ∃ s', o' = some s' ∧ R s.coreOf s'.coreOf := by
  subst hs
  cases o' with
  | none => exact False.elim h
  | some s' => exact ⟨s', rfl, h⟩

/-- Related cores are ended together: read off the pass. -/
theorem IsBisim.ended {G G' : SeqGame Mv} {R : G.C → G'.C → Prop}
    (hB : IsBisim G G' R) {x : G.C} {x' : G'.C} (hR : R x x') :
    G.ended x ↔ G'.ended x' := by
  have h := hB.step x x' hR false false Mv.pass
  show sfinal G (PState.live x false false) ↔ sfinal G' (PState.live x' false false)
  rw [sfinal_iff_no_pass G (PState.live x false false),
    sfinal_iff_no_pass G' (PState.live x' false false)]
  exact optCoreRel_none R h

/-- Related cores have related actions, for a graded non pass move at
    a non ended core. -/
theorem IsBisim.mv {G G' : SeqGame Mv} {R : G.C → G'.C → Prop}
    (hB : IsBisim G G' R) {x : G.C} {x' : G'.C} (hR : R x x') (m : Mv.M)
    (hm : m ≠ Mv.pass) (hd : Mv.deg0 m ∨ Mv.deg1 m) (he : ¬G.ended x) :
    OptRelC R (G.mv x m) (G'.mv x' m) := by
  have he' : ¬G'.ended x' := fun h => he ((hB.ended hR).mpr h)
  have key : ∀ g : Bool, ((g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)) →
      OptRelC R (G.mv x m) (G'.mv x' m) := by
    intro g hg
    have h := hB.step x x' hR g false m
    rw [sE_nonpass G x g false m hm he, if_pos hg,
      sE_nonpass G' x' g false m hm he', if_pos hg] at h
    revert h
    cases G.mv x m <;> cases G'.mv x' m <;> intro h <;> exact h
  rcases hd with hd | hd
  · exact key false (Or.inl ⟨rfl, hd⟩)
  · exact key true (Or.inr ⟨rfl, hd⟩)

/-- The equality is a bisimulation on G. -/
theorem isBisim_eq (G : SeqGame Mv) : IsBisim G G Eq where
  init := rfl
  step := by
    intro x x' hxx g j m
    subst hxx
    cases sE G (PState.live x g j) m with
    | none => exact trivial
    | some s => exact rfl

/-- The inverse of a bisimulation is one. -/
theorem IsBisim.flip {G G' : SeqGame Mv} {R : G.C → G'.C → Prop}
    (hB : IsBisim G G' R) : IsBisim G' G (fun x' x => R x x') where
  init := hB.init
  step := by
    intro x' x hR g j m
    have h := hB.step x x' hR g j m
    revert h
    cases sE G (PState.live x g j) m <;> cases sE G' (PState.live x' g j) m <;>
      intro h <;> exact h

/-- The composite of two bisimulations is one. -/
theorem IsBisim.comp {G G' G'' : SeqGame Mv} {R : G.C → G'.C → Prop}
    {R' : G'.C → G''.C → Prop} (hB : IsBisim G G' R) (hB' : IsBisim G' G'' R') :
    IsBisim G G'' (fun x x'' => ∃ x', R x x' ∧ R' x' x'') where
  init := ⟨G'.q0, hB.init, hB'.init⟩
  step := by
    rintro x x'' ⟨x', hR, hR'⟩ g j m
    have h := hB.step x x' hR g j m
    have h' := hB'.step x' x'' hR' g j m
    revert h h'
    cases sE G (PState.live x g j) m with
    | none =>
      cases sE G' (PState.live x' g j) m with
      | none =>
        cases sE G'' (PState.live x'' g j) m with
        | none => intro _ _; exact trivial
        | some _ => intro _ h'; exact False.elim h'
      | some _ => intro h _; exact False.elim h
    | some s =>
      cases sE G' (PState.live x' g j) m with
      | none => intro h _; exact False.elim h
      | some s' =>
        cases sE G'' (PState.live x'' g j) m with
        | none => intro _ h'; exact False.elim h'
        | some s'' => intro h h'; exact ⟨s'.coreOf, h, h'⟩

theorem bisimilar_refl (G : SeqGame Mv) (x : G.C) : Bisimilar G x x :=
  ⟨Eq, isBisim_eq G, rfl⟩

theorem bisimilar_symm (G : SeqGame Mv) {x y : G.C} (h : Bisimilar G x y) :
    Bisimilar G y x := by
  obtain ⟨R, hR, hxy⟩ := h
  exact ⟨fun u v => R v u, hR.flip, hxy⟩

theorem bisimilar_trans (G : SeqGame Mv) {x y z : G.C} (h1 : Bisimilar G x y)
    (h2 : Bisimilar G y z) : Bisimilar G x z := by
  obtain ⟨R, hR, hxy⟩ := h1
  obtain ⟨R', hR', hyz⟩ := h2
  exact ⟨_, hR.comp hR', y, hxy, hyz⟩

/-- Bisimilarity is a bisimulation on G: the union of all of them. -/
theorem isBisim_bisimilar (G : SeqGame Mv) : IsBisim G G (Bisimilar G) where
  init := bisimilar_refl G G.q0
  step := by
    rintro x y ⟨R, hR, hxy⟩ g j m
    have h := hR.step x y hxy g j m
    revert h
    cases sE G (PState.live x g j) m with
    | none =>
      cases sE G (PState.live y g j) m with
      | none => intro _; exact trivial
      | some _ => intro h; exact False.elim h
    | some s =>
      cases sE G (PState.live y g j) m with
      | none => intro h; exact False.elim h
      | some s' => intro h; exact ⟨R, hR, h⟩

theorem bisimilar_ended (G : SeqGame Mv) {x y : G.C} (h : Bisimilar G x y) :
    G.ended x ↔ G.ended y :=
  (isBisim_bisimilar G).ended h

theorem bisimilar_mv (G : SeqGame Mv) {x y : G.C} (h : Bisimilar G x y) (m : Mv.M)
    (hm : m ≠ Mv.pass) (hd : Mv.deg0 m ∨ Mv.deg1 m) (he : ¬G.ended x) :
    OptRelC (Bisimilar G) (G.mv x m) (G.mv y m) :=
  (isBisim_bisimilar G).mv h m hm hd he

/-! ### The legally obtainable cores -/

theorem coreOb_q0 (G : SeqGame Mv) : CoreOb G G.q0 := ⟨false, SeqReach.init⟩

/-- A legally obtainable state has a legally obtainable core. -/
theorem coreOb_of_seqReach (G : SeqGame Mv) {s : G.S} (h : SeqReach G s) :
    CoreOb G s.coreOf := by
  induction h with
  | init => exact coreOb_q0 G
  | @step s s' m hs hE ih =>
    cases s with
    | done c g => exact absurd hE (fun h => Option.noConfusion h)
    | live c g j =>
      by_cases he : G.ended c
      · rw [prop_finalnomove G (s := PState.live c g j) he m] at hE
        exact absurd hE (fun h => Option.noConfusion h)
      · by_cases hm : m = Mv.pass
        · subst hm
          rw [sE_pass G c g j he] at hE
          rw [← Option.some_inj.mp hE]
          cases j <;> exact ih
        · rw [sE_nonpass G c g j m hm he] at hE
          by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
          · rw [if_pos hg] at hE
            obtain ⟨c', hmv, hc'⟩ := Option.map_eq_some'.mp hE
            rw [← hc']
            have hd : Mv.deg0 m ∨ Mv.deg1 m := by
              rcases hg with ⟨-, hd⟩ | ⟨-, hd⟩
              · exact Or.inl hd
              · exact Or.inr hd
            exact coreOb_mv G ih hd hm he hmv
          · rw [if_neg hg] at hE
            exact absurd hE (fun h => Option.noConfusion h)

/-! ### The minimal quotient -/

/-- The legally obtainable cores. -/
def ObC (G : SeqGame Mv) : Type := { x : G.C // CoreOb G x }

/-- Bisimilarity on the legally obtainable cores. -/
def ObRel (G : SeqGame Mv) (a b : ObC G) : Prop := Bisimilar G a.1 b.1

/-- Bisimilarity as a setoid on the legally obtainable cores. -/
def obSetoid (G : SeqGame Mv) : Setoid (ObC G) where
  r := ObRel G
  iseqv := ⟨fun a => bisimilar_refl G a.1, fun h => bisimilar_symm G h,
    fun h1 h2 => bisimilar_trans G h1 h2⟩

/-- The classes of legally obtainable cores. -/
def QC (G : SeqGame Mv) : Type := Quotient (obSetoid G)

def qmk (G : SeqGame Mv) (a : ObC G) : QC G := Quotient.mk (obSetoid G) a

theorem qmk_eq_of (G : SeqGame Mv) {a b : ObC G} (h : ObRel G a b) : qmk G a = qmk G b :=
  Quotient.sound h

theorem obRel_of_qmk_eq (G : SeqGame Mv) {a b : ObC G} (h : qmk G a = qmk G b) :
    ObRel G a b :=
  Quotient.exact h

/-- A core to its obtainable-core record, an unobtainable core sent to
    the initial core (never read where it matters). -/
noncomputable def toOb (G : SeqGame Mv) (c : G.C) : ObC G :=
  if h : CoreOb G c then ⟨c, h⟩ else ⟨G.q0, coreOb_q0 G⟩

theorem toOb_of (G : SeqGame Mv) {c : G.C} (h : CoreOb G c) : toOb G c = ⟨c, h⟩ := by
  unfold toOb; rw [dif_pos h]

/-- The class of a core. -/
noncomputable def qCore (G : SeqGame Mv) (c : G.C) : QC G := qmk G (toOb G c)

theorem qCore_of (G : SeqGame Mv) {c : G.C} (h : CoreOb G c) :
    qCore G c = qmk G ⟨c, h⟩ := by
  unfold qCore; rw [toOb_of G h]

theorem qCore_eq_of_bisimilar (G : SeqGame Mv) {c c' : G.C} (h : CoreOb G c)
    (h' : CoreOb G c') (hb : Bisimilar G c c') : qCore G c = qCore G c' := by
  rw [qCore_of G h, qCore_of G h']
  exact qmk_eq_of G hb

/-- The action of the quotient, on a representative: the action of G
    where the evolution reads it — a graded non pass move at a non
    ended core — and undefined elsewhere. -/
noncomputable def qmvAux (G : SeqGame Mv) (a : ObC G) (m : Mv.M) : Option (QC G) :=
  if ¬G.ended a.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m) then
    (G.mv a.1 m).map (qCore G)
  else none

theorem qmvAux_sound (G : SeqGame Mv) (a b : ObC G) (hab : ObRel G a b) (m : Mv.M) :
    qmvAux G a m = qmvAux G b m := by
  unfold qmvAux
  have hend : G.ended a.1 ↔ G.ended b.1 := bisimilar_ended G hab
  by_cases h : ¬G.ended a.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m)
  · have h' : ¬G.ended b.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m) :=
      ⟨fun hb => h.1 (hend.mpr hb), h.2.1, h.2.2⟩
    rw [if_pos h, if_pos h']
    have hrel := bisimilar_mv G hab m h.2.1 h.2.2 h.1
    cases hma : G.mv a.1 m with
    | none =>
      cases hmb : G.mv b.1 m with
      | none => rfl
      | some y' => rw [hma, hmb] at hrel; exact False.elim hrel
    | some y =>
      cases hmb : G.mv b.1 m with
      | none => rw [hma, hmb] at hrel; exact False.elim hrel
      | some y' =>
        rw [hma, hmb] at hrel
        show some (qCore G y) = some (qCore G y')
        rw [qCore_eq_of_bisimilar G (coreOb_mv G a.2 h.2.2 h.2.1 h.1 hma)
          (coreOb_mv G b.2 h'.2.2 h'.2.1 h'.1 hmb) hrel]
  · have h' : ¬(¬G.ended b.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m)) :=
      fun hb => h ⟨fun ha => hb.1 (hend.mp ha), hb.2.1, hb.2.2⟩
    rw [if_neg h, if_neg h']

/-- The minimal quotient G/~ as a sequential game. -/
noncomputable def QGame (G : SeqGame Mv) : SeqGame Mv where
  C := QC G
  mv := Quotient.lift (fun a m => qmvAux G a m)
    (fun a b hab => funext fun m => qmvAux_sound G a b hab m)
  q0 := qmk G ⟨G.q0, coreOb_q0 G⟩
  ended := Quotient.lift (fun a => G.ended a.1)
    (fun _ _ hab => propext (bisimilar_ended G hab))

theorem QGame_ended (G : SeqGame Mv) (a : ObC G) :
    (QGame G).ended (qmk G a) ↔ G.ended a.1 := Iff.rfl

theorem QGame_mv (G : SeqGame Mv) (a : ObC G) (m : Mv.M) :
    (QGame G).mv (qmk G a) m =
      if ¬G.ended a.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m) then
        (G.mv a.1 m).map (qCore G)
      else none := rfl

theorem qCore_q0 (G : SeqGame Mv) : qCore G G.q0 = (QGame G).q0 :=
  qCore_of G (coreOb_q0 G)

/-- Every class is the class of a legally obtainable core. -/
theorem QC.exists_rep (G : SeqGame Mv) (z : QC G) :
    ∃ c, CoreOb G c ∧ qCore G c = z := by
  induction z using Quotient.ind with
  | _ a => exact ⟨a.1, a.2, qCore_of G a.2⟩

/-! ### The projection on states -/

/-- The projection π on states: the core to its class, the gradings
    kept. -/
noncomputable def qS (G : SeqGame Mv) : G.S → (QGame G).S
  | .live c g j => .live (qCore G c) g j
  | .done c g => .done (qCore G c) g

theorem qS_coreOf (G : SeqGame Mv) (s : G.S) :
    (qS G s).coreOf = qCore G s.coreOf := by
  cases s <;> rfl

theorem qS_sInit (G : SeqGame Mv) : qS G (sInit G) = sInit (QGame G) := by
  show PState.live (qCore G G.q0) false false = PState.live (QGame G).q0 false false
  rw [qCore_q0]

theorem sN_qS (G : SeqGame Mv) (s : G.S) : sN (qS G s) = qS G (sN s) := by
  cases s <;> rfl

theorem sBar_qS (G : SeqGame Mv) (s : G.S) : sBar (qS G s) = qS G (sBar s) := by
  cases s with
  | done c g => rfl
  | live c g j => cases j <;> rfl

theorem sdeg_qS (G : SeqGame Mv) (s : G.S) : sdeg (QGame G) (qS G s) = sdeg G s := by
  cases s <;> rfl

theorem ended_qCore (G : SeqGame Mv) {c : G.C} (h : CoreOb G c) :
    (QGame G).ended (qCore G c) ↔ G.ended c := by
  rw [qCore_of G h]; exact Iff.rfl

theorem sfinal_qS (G : SeqGame Mv) {s : G.S} (h : CoreOb G s.coreOf) :
    sfinal (QGame G) (qS G s) ↔ sfinal G s := by
  cases s with
  | done c g => exact Iff.rfl
  | live c g j => exact ended_qCore G h

/-- The evolution commutes with π at a state of legally obtainable
    core: the printed [E ((x,i,j),m)] = E (([x],i,j),m). -/
theorem sE_qS (G : SeqGame Mv) {s : G.S} (h : CoreOb G s.coreOf) (m : Mv.M) :
    sE (QGame G) (qS G s) m = (sE G s m).map (qS G) := by
  cases s with
  | done c g => rfl
  | live c g j =>
    have hc : CoreOb G c := h
    show sE (QGame G) (PState.live (qCore G c) g j) m = _
    rw [sE_live, sE_live]
    have hend : (QGame G).ended (qCore G c) ↔ G.ended c := ended_qCore G hc
    by_cases he : G.ended c
    · rw [if_pos he, if_pos (hend.mpr he)]; rfl
    · rw [if_neg he, if_neg (fun h' => he (hend.mp h'))]
      by_cases hm : m = Mv.pass
      · rw [if_pos hm, if_pos hm]
        cases j <;> rfl
      · rw [if_neg hm, if_neg hm]
        by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
        · rw [if_pos hg, if_pos hg, qCore_of G hc, QGame_mv]
          have hd : Mv.deg0 m ∨ Mv.deg1 m := by
            rcases hg with ⟨-, hd⟩ | ⟨-, hd⟩
            · exact Or.inl hd
            · exact Or.inr hd
          rw [if_pos ⟨he, hm, hd⟩, Option.map_map, Option.map_map]
          rfl
        · rw [if_neg hg, if_neg hg]; rfl

theorem hashOp_qS (G : SeqGame Mv) {s : G.S} (h : CoreOb G s.coreOf) (m : Mv.M) :
    hashOp (QGame G) (qS G s) m = (hashOp G s m).map (qS G) := by
  cases s with
  | done c g => rfl
  | live c g j =>
    show hashOp (QGame G) (PState.live (qCore G c) g j) m = _
    rw [hashOp_live, hashOp_live]
    have hE := sE_qS G (s := PState.live c g j) h m
    change sE (QGame G) (PState.live (qCore G c) g j) m = _ at hE
    rw [hE]
    cases sE G (PState.live c g j) m with
    | some b => rfl
    | none =>
      show sE (QGame G) (sBar (PState.live (qCore G c) g j)) m = _
      have hb : sBar (PState.live (qCore G c) g j) = qS G (sBar (PState.live c g j)) :=
        sBar_qS G (PState.live c g j)
      rw [hb, sE_qS G (s := sBar (PState.live c g j)) (by cases j <;> exact h) m]

theorem interface0_qS (G : SeqGame Mv) {s : G.S} (h : CoreOb G s.coreOf) (m : Mv.M) :
    Interface0 (QGame G) (qS G s) m ↔ Interface0 G s m := by
  unfold Interface0
  rw [hashOp_qS G h m, isSome_map']

/-- Bisimilar states — the same gradings over bisimilar obtainable
    cores — have the same interface. -/
theorem interface0_of_qS_eq (G : SeqGame Mv) {s t : G.S} (hs : CoreOb G s.coreOf)
    (ht : CoreOb G t.coreOf) (h : qS G s = qS G t) (m : Mv.M) :
    Interface0 G s m ↔ Interface0 G t m := by
  rw [← interface0_qS G hs m, ← interface0_qS G ht m, h]

theorem hash2_qS (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) (m0 m1 : Mv.M) :
    hash2 (QGame G) (qS G a) m0 m1 = (hash2 G a m0 m1).map (qS G) := by
  unfold hash2
  rw [hashOp_qS G h m0]
  cases hx : hashOp G a m0 with
  | none => rfl
  | some b =>
    show hashOp (QGame G) (qS G b) m1 = Option.map (qS G) (hashOp G b m1)
    rw [hashOp_qS G (coreOb_hashOp G h hx) m1]

theorem tval_qS (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) (m m' : Mv.M) :
    tval (QGame G) (qS G a) m m' = (tval G a m m').map (qS G) := by
  unfold tval
  rw [hash2_qS G h m m']
  cases hash2 G a m m' with
  | some x => rfl
  | none => exact hashOp_qS G h m

/-- The image of a branch set under a map of states. -/
def BSet.img {α β : Type} (f : α → β) (P : BSet α) : BSet β :=
  fun z => ∃ x, P x ∧ f x = z

theorem BSet.img_pair {α β : Type} (f : α → β) (u v : α) :
    BSet.img f (BSet.pair u v) = BSet.pair (f u) (f v) := by
  funext z
  apply propext
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl (by rw [hx])
    · exact Or.inr (by rw [hx])
  · rintro (h | h)
    · exact ⟨u, Or.inl rfl, h.symm⟩
    · exact ⟨v, Or.inr rfl, h.symm⟩

/-- P commutes with π: the prescription decides by definedness. -/
theorem Pmap_qS (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) (m0 m1 : Mv.M) :
    Pmap (QGame G) (qS G a) m0 m1 = (Pmap G a m0 m1).map (BSet.img (qS G)) := by
  rw [Pmap_eq, Pmap_eq, tval_qS G h m0 m1, tval_qS G h m1 m0]
  cases tval G a m0 m1 with
  | none => rfl
  | some x =>
    cases tval G a m1 m0 with
    | none => rfl
    | some y =>
      show some (BSet.pair (sN (qS G x)) (sN (qS G y))) =
        some (BSet.img (qS G) (BSet.pair (sN x) (sN y)))
      rw [sN_qS, sN_qS, BSet.img_pair]

/-! ### Reachability -/

/-- π carries legally obtainable states to legally obtainable states. -/
theorem seqReach_qS (G : SeqGame Mv) {s : G.S} (h : SeqReach G s) :
    SeqReach (QGame G) (qS G s) := by
  induction h with
  | init => rw [qS_sInit]; exact SeqReach.init
  | @step s s' m hs hE ih =>
    refine SeqReach.step (m := m) ih ?_
    rw [sE_qS G (coreOb_of_seqReach G hs) m, hE]; rfl

/-- Every legally obtainable state of G/~ is the image of one of G. -/
theorem seqReach_qS_surj (G : SeqGame Mv) {z : (QGame G).S}
    (h : SeqReach (QGame G) z) : ∃ s, SeqReach G s ∧ qS G s = z := by
  induction h with
  | init => exact ⟨sInit G, SeqReach.init, qS_sInit G⟩
  | @step z z' m _ hE ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    rw [sE_qS G (coreOb_of_seqReach G hs) m] at hE
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some'.mp hE
    exact ⟨s', SeqReach.step (m := m) hs hs', rfl⟩


/-! ### Branch sets with legally obtainable cores -/

/-- Every branch has a legally obtainable core. -/
def ObSet (G : SeqGame Mv) (A : BSet G.S) : Prop := ∀ a, A a → CoreOb G a.coreOf

theorem obSet_single (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) :
    ObSet G (BSet.single a) := by
  intro b hb
  change b = a at hb
  rw [hb]; exact h

/-- The elements of a value of P have legally obtainable cores. -/
theorem Pmap_coreOb (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) {m0 m1 : Mv.M}
    {P : BSet G.S} (hP : Pmap G a m0 m1 = some P) {z : G.S} (hz : P z) :
    CoreOb G z.coreOf := by
  obtain ⟨x, y, hx, hy, rfl⟩ := (Pmap_some_iff G a m0 m1 P).mp hP
  have key : ∀ {m m' : Mv.M} {w : G.S}, tval G a m m' = some w → CoreOb G w.coreOf := by
    intro m m' w hw
    unfold tval at hw
    revert hw
    cases h2 : hash2 G a m m' with
    | some u =>
      intro hw
      rw [← Option.some_inj.mp hw]
      obtain ⟨v, hv0, hv1⟩ := hash2_split G h2
      exact coreOb_hashOp G (coreOb_hashOp G h hv0) hv1
    | none =>
      intro hw
      exact coreOb_hashOp G h hw
  rcases hz with hz | hz
  · rw [hz, coreOb_sN]; exact key hx
  · rw [hz, coreOb_sN]; exact key hy

theorem simVal_obSet (G : SeqGame Mv) {A : BSet G.S} (hA : ObSet G A) (m0 m1 : Mv.M) :
    ObSet G (simVal G A m0 m1) := by
  rintro z ⟨a, ha, P, hP, hz⟩
  exact Pmap_coreOb G (hA a ha) hP hz

theorem simDef1_img (G : SeqGame Mv) {A : BSet G.S} (hA : ObSet G A) (m : Mv.M) :
    simDef1 (QGame G) (BSet.img (qS G) A) m ↔ simDef1 G A m := by
  constructor
  · intro h a ha
    have := h (qS G a) ⟨a, ha, rfl⟩
    refine ⟨fun hf => this.1 ((sfinal_qS G (hA a ha)).mpr hf), ?_⟩
    have h2 := this.2
    rw [hashOp_qS G (hA a ha), isSome_map'] at h2
    exact h2
  · rintro h z ⟨a, ha, rfl⟩
    have := h a ha
    refine ⟨fun hf => this.1 ((sfinal_qS G (hA a ha)).mp hf), ?_⟩
    show (hashOp (QGame G) (qS G a) m).isSome = true
    rw [hashOp_qS G (hA a ha), isSome_map']
    exact this.2

theorem simDefP_img (G : SeqGame Mv) {A : BSet G.S} (hA : ObSet G A) (m0 m1 : Mv.M) :
    simDefP (QGame G) (BSet.img (qS G) A) m0 m1 ↔ simDefP G A m0 m1 := by
  constructor
  · intro h a ha
    have := h (qS G a) ⟨a, ha, rfl⟩
    refine ⟨fun hf => this.1 ((sfinal_qS G (hA a ha)).mpr hf), ?_⟩
    have h2 := this.2
    rw [Pmap_qS G (hA a ha), isSome_map'] at h2
    exact h2
  · rintro h z ⟨a, ha, rfl⟩
    have := h a ha
    refine ⟨fun hf => this.1 ((sfinal_qS G (hA a ha)).mp hf), ?_⟩
    show (Pmap (QGame G) (qS G a) m0 m1).isSome = true
    rw [Pmap_qS G (hA a ha), isSome_map']
    exact this.2

theorem simVal_img (G : SeqGame Mv) {A : BSet G.S} (hA : ObSet G A) (m0 m1 : Mv.M) :
    simVal (QGame G) (BSet.img (qS G) A) m0 m1 = BSet.img (qS G) (simVal G A m0 m1) := by
  funext z
  apply propext
  constructor
  · rintro ⟨w, ⟨a, ha, rfl⟩, P', hP', hz⟩
    rw [Pmap_qS G (hA a ha)] at hP'
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some'.mp hP'
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, ⟨a, ha, P, hP, hx⟩, rfl⟩
  · rintro ⟨x, ⟨a, ha, P, hP, hx⟩, rfl⟩
    refine ⟨qS G a, ⟨a, ha, rfl⟩, BSet.img (qS G) P, ?_, x, hx, rfl⟩
    rw [Pmap_qS G (hA a ha), hP]; rfl

theorem simFinal_img (G : SeqGame Mv) {A : BSet G.S} (hA : ObSet G A) :
    simFinal (QGame G) (BSet.img (qS G) A) ↔ simFinal G A := by
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, hf⟩
    exact ⟨a, ha, (sfinal_qS G (hA a ha)).mp hf⟩
  · rintro ⟨a, ha, hf⟩
    exact ⟨qS G a, ⟨a, ha, rfl⟩, (sfinal_qS G (hA a ha)).mpr hf⟩

/-- The branches of a branch semantics at a legally obtainable state
    have legally obtainable cores. -/
theorem rho_coreOb (G : SeqGame Mv) (H : SimulGame Mv) {ρ : H.B → BSet G.S}
    (hsim : IsSimultaneization G H ρ) {s : H.B} (hs : SimReach H s) : ObSet G (ρ s) := by
  induction hs with
  | init =>
    intro a ha
    rw [(hsim.rho_init a).mp ha]
    exact coreOb_q0 G
  | @step s s' m0 m1 hs hE ih =>
    intro a ha
    exact simVal_obSet G ih m0 m1 a (hsim.nat_incl hs hE a ha)

/-! ### Sim(G) and Sim(G/~) -/

/-- A branch set of normal forms, mapped along π. -/
noncomputable def qN (G : SeqGame Mv) (A : NSet G) : NSet (QGame G) :=
  ⟨BSet.img (qS G) A.1, by
    rintro z ⟨x, hx, rfl⟩
    rw [sN_qS, A.2 x hx]⟩

theorem qN_val (G : SeqGame Mv) (A : NSet G) : (qN G A).1 = BSet.img (qS G) A.1 := rfl

theorem qN_q0 (G : SeqGame Mv) : qN G (simGame G).q0 = (simGame (QGame G)).q0 := by
  apply NSet.ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x = sInit G at hx
    rw [hx]
    exact qS_sInit G
  · intro hz
    change z = sInit (QGame G) at hz
    exact ⟨sInit G, rfl, by rw [hz, qS_sInit]⟩

theorem simGame_pairE_qN (G : SeqGame Mv) {A : NSet G} (hA : ObSet G A.1) (m0 m1 : Mv.M) :
    (simGame (QGame G)).pairE (qN G A) m0 m1 =
      ((simGame G).pairE A m0 m1).map (qN G) := by
  show (if simDefP (QGame G) (qN G A).1 m0 m1 then some _ else none) =
    Option.map (qN G) (if simDefP G A.1 m0 m1 then some _ else none)
  by_cases h : simDefP G A.1 m0 m1
  · have h' : simDefP (QGame G) (qN G A).1 m0 m1 := (simDefP_img G hA m0 m1).mpr h
    rw [if_pos h', if_pos h]
    show some _ = some _
    congr 1
    apply NSet.ext
    intro z
    show simVal (QGame G) (qN G A).1 m0 m1 z ↔ BSet.img (qS G) (simVal G A.1 m0 m1) z
    rw [← simVal_img G hA m0 m1]
    exact Iff.rfl
  · have h' : ¬simDefP (QGame G) (qN G A).1 m0 m1 :=
      fun h' => h ((simDefP_img G hA m0 m1).mp h')
    rw [if_neg h', if_neg h]
    rfl

theorem simReach_obSet (G : SeqGame Mv) {A : NSet G} (h : SimReach (simGame G) A) :
    ObSet G A.1 :=
  rho_coreOb G (simGame G) (simGame_isSimultaneization G) h

theorem commuteAt_qS (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) {m0 m1 : Mv.M}
    (hc : CommuteAt G a m0 m1) : CommuteAt (QGame G) (qS G a) m0 m1 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hc
  refine ⟨qS G x, qS G y, ?_, ?_, ?_⟩
  · rw [hash2_qS G h, hx]; rfl
  · rw [hash2_qS G h, hy]; rfl
  · rw [sN_qS, sN_qS, hxy]

theorem assocOf_qS (G : SeqGame Mv) {a : G.S} (h : CoreOb G a.coreOf) (m0 m1 : Mv.M) :
    assocOf (QGame G) (qS G a) m0 m1 = qS G (assocOf G a m0 m1) := by
  unfold assocOf
  rw [hash2_qS G h]
  cases hash2 G a m0 m1 with
  | none => show sN (qS G a) = qS G (sN a); exact sN_qS G a
  | some x => show sN (qS G x) = qS G (sN x); exact sN_qS G x

/-- Semi-classical states of Sim(G) go to semi-classical states of
    Sim(G/~), the associated state to its image. -/
theorem semiC_qN (G : SeqGame Mv) {A : NSet G} {a : G.S}
    (h : SemiC G (simGame G) A a) :
    SemiC (QGame G) (simGame (QGame G)) (qN G A) (qS G a) := by
  induction h with
  | init =>
    rw [qN_q0, qS_sInit]
    exact SemiC.init
  | @step s b s' m0 m1 hsc hc hp ih =>
    have hb : CoreOb G b.coreOf := semiC_coreOb G hsc
    rw [← assocOf_qS G hb]
    refine SemiC.step ih (commuteAt_qS G hb hc) ?_
    rw [simGame_pairE_qN G (simReach_obSet G (simReach_of_semiC G (simGame G) hsc)), hp]
    rfl

/-! ### The projection is a bisimulation -/

theorem isBisim_projection (G : SeqGame Mv) :
    IsBisim G (QGame G) (fun x z => CoreOb G x ∧ qCore G x = z) where
  init := ⟨coreOb_q0 G, qCore_q0 G⟩
  step := by
    rintro x z ⟨hx, rfl⟩ g j m
    have hE := sE_qS G (s := PState.live x g j) hx m
    change sE (QGame G) (PState.live (qCore G x) g j) m = _ at hE
    rw [hE]
    cases hs : sE G (PState.live x g j) m with
    | none => exact trivial
    | some s' =>
      refine ⟨?_, (qS_coreOf G s').symm⟩
      -- the core of s' is obtainable: either x itself (a pass) or a move's value
      by_cases he : G.ended x
      · rw [prop_finalnomove G (s := PState.live x g j) he m] at hs
        exact absurd hs (fun h => Option.noConfusion h)
      · by_cases hm : m = Mv.pass
        · subst hm
          rw [sE_pass G x g j he] at hs
          rw [← Option.some_inj.mp hs]
          cases j <;> exact hx
        · rw [sE_nonpass G x g j m hm he] at hs
          by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
          · rw [if_pos hg] at hs
            obtain ⟨c', hmv, hc'⟩ := Option.map_eq_some'.mp hs
            rw [← hc']
            have hd : Mv.deg0 m ∨ Mv.deg1 m := by
              rcases hg with ⟨-, hd⟩ | ⟨-, hd⟩
              · exact Or.inl hd
              · exact Or.inr hd
            exact coreOb_mv G hx hd hm he hmv
          · rw [if_neg hg] at hs
            exact absurd hs (fun h => Option.noConfusion h)

/-! ### Minimality and the radius spectrum -/

/-- def_bisimulation: G is minimal when bisimilar legally obtainable
    cores are equal. -/
def Minimal (G : SeqGame Mv) : Prop :=
  ∀ x y, CoreOb G x → CoreOb G y → Bisimilar G x y → x = y

/-- def_bisimulation: the radius spectrum of G is the raw radius
    spectrum of its minimal quotient. -/
def InRadiusSpectrum (G : SeqGame Mv) (r : Option Nat) : Prop :=
  InSpectrum (QGame G) r

theorem bisimilar_of_qCore_eq (G : SeqGame Mv) {c c' : G.C} (h : CoreOb G c)
    (h' : CoreOb G c') (he : qCore G c = qCore G c') : Bisimilar G c c' := by
  rw [qCore_of G h, qCore_of G h'] at he
  exact obRel_of_qmk_eq G he

/-- Over a minimal game π is injective on the states of legally
    obtainable core. -/
theorem qS_inj (G : SeqGame Mv) (hmin : Minimal G) {s t : G.S} (hs : CoreOb G s.coreOf)
    (ht : CoreOb G t.coreOf) (h : qS G s = qS G t) : s = t := by
  cases s with
  | live c g j =>
    cases t with
    | live c' g' j' =>
      have h1 : qCore G c = qCore G c' := by
        have := congrArg PState.coreOf h
        exact this
      have h2 : g = g' := by
        have := congrArg (sdeg (QGame G)) h
        exact this
      have h3 : j = j' := by
        have : (match qS G (PState.live c g j) with
          | .live _ _ j => j | .done _ _ => false) =
          (match qS G (PState.live c' g' j') with
          | .live _ _ j => j | .done _ _ => false) := by rw [h]
        exact this
      rw [hmin c c' hs ht (bisimilar_of_qCore_eq G hs ht h1), h2, h3]
    | done c' g' => exact absurd h (fun h => PState.noConfusion h)
  | done c g =>
    cases t with
    | live c' g' j' => exact absurd h (fun h => PState.noConfusion h)
    | done c' g' =>
      have h1 : qCore G c = qCore G c' := by
        have := congrArg PState.coreOf h
        exact this
      have h2 : g = g' := by
        have := congrArg (sdeg (QGame G)) h
        exact this
      rw [hmin c c' hs ht (bisimilar_of_qCore_eq G hs ht h1), h2]


/-! ### The symmetry of the quotient (Lemma lem_bisimulation (1)) -/

section Sym

variable {G : SeqGame Mv} (D : SeqSymData G)

theorem Rst_coreOf (s : G.S) : (Rst D s).coreOf = D.R s.coreOf := by
  cases s <;> rfl

/-- The evolution at a swapped core, through the symmetry. -/
theorem sE_R (c : G.C) (g j : Bool) (m : Mv.M) :
    sE G (PState.live (D.R c) g j) m =
      Option.map (Rst D) (sE G (PState.live c (!g) j) (D.A m)) := by
  have h := sE_Rst D (PState.live c (!g) j) (D.A m)
  rw [D.AA] at h
  have hR : Rst D (PState.live c (!g) j) = PState.live (D.R c) g j := by
    show PState.live (D.R c) (!!g) j = _
    rw [Bool.not_not]
  rw [hR] at h
  rw [← h, Option.map_map]
  cases sE G (PState.live (D.R c) g j) m with
  | none => rfl
  | some t =>
    show some t = some (Rst D (Rst D t))
    rw [Rst_Rst]

/-- The swapped cores of bisimilar cores are bisimilar: the swap of a
    bisimulation is one (property prop_symmetryRS). -/
theorem isBisim_swap : IsBisim G G
    (fun u v => ∃ x y, Bisimilar G x y ∧ u = D.R x ∧ v = D.R y) where
  init := ⟨G.q0, G.q0, bisimilar_refl G G.q0, D.Rq0.symm, D.Rq0.symm⟩
  step := by
    rintro u v ⟨x, y, hxy, rfl, rfl⟩ g j m
    rw [sE_R D x g j m, sE_R D y g j m]
    have h := (isBisim_bisimilar G).step x y hxy (!g) j (D.A m)
    revert h
    cases sE G (PState.live x (!g) j) (D.A m) with
    | none =>
      cases sE G (PState.live y (!g) j) (D.A m) with
      | none => intro _; exact trivial
      | some _ => intro h; exact False.elim h
    | some t =>
      cases sE G (PState.live y (!g) j) (D.A m) with
      | none => intro h; exact False.elim h
      | some t' =>
        intro h
        refine ⟨t.coreOf, t'.coreOf, h, ?_, ?_⟩
        · exact Rst_coreOf D t
        · exact Rst_coreOf D t'

theorem bisimilar_R {x y : G.C} (h : Bisimilar G x y) : Bisimilar G (D.R x) (D.R y) :=
  ⟨_, isBisim_swap D, x, y, h, rfl, rfl⟩

/-- The swap of a legally obtainable core is legally obtainable. -/
theorem coreOb_R {c : G.C} (h : CoreOb G c) : CoreOb G (D.R c) := by
  suffices key : ∀ s, SeqReach G s → CoreOb G (D.R s.coreOf) by
    obtain ⟨g, hg⟩ := h
    exact key _ hg
  intro s hs
  induction hs with
  | init => rw [show (sInit G).coreOf = G.q0 from rfl, D.Rq0]; exact coreOb_q0 G
  | @step s s' m hs hE ih =>
    cases s with
    | done c g => exact absurd hE (fun h => Option.noConfusion h)
    | live c g j =>
      by_cases he : G.ended c
      · rw [prop_finalnomove G (s := PState.live c g j) he m] at hE
        exact absurd hE (fun h => Option.noConfusion h)
      · by_cases hm : m = Mv.pass
        · subst hm
          rw [sE_pass G c g j he] at hE
          rw [← Option.some_inj.mp hE]
          cases j <;> exact ih
        · rw [sE_nonpass G c g j m hm he] at hE
          by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
          · rw [if_pos hg] at hE
            obtain ⟨c', hmv, hc'⟩ := Option.map_eq_some'.mp hE
            rw [← hc']
            show CoreOb G (D.R c')
            have hRm := D.Rmv c m
            rw [hmv] at hRm
            obtain ⟨d, hd, hdc⟩ := Option.map_eq_some'.mp hRm
            have hdR : d = D.R c' := by rw [← hdc, D.RR]
            rw [← hdR]
            have hAm : D.A m ≠ Mv.pass := fun h => hm ((D.Apass_iff m).mp h)
            have hdeg : Mv.deg0 (D.A m) ∨ Mv.deg1 (D.A m) := by
              rcases hg with ⟨-, h0⟩ | ⟨-, h1⟩
              · exact Or.inr ((D.Adeg m).mp h0)
              · exact Or.inl ((D.Adeg1 m).mp h1)
            have heR : ¬G.ended (D.R c) := fun h => he ((D.Rend c).mp h)
            exact coreOb_mv G ih hdeg hAm heR hd
          · rw [if_neg hg] at hE
            exact absurd hE (fun h => Option.noConfusion h)

/-- The swap on the classes. -/
noncomputable def Rq : QC G → QC G :=
  Quotient.lift (fun a : ObC G => qmk G ⟨D.R a.1, coreOb_R D a.2⟩)
    (fun _ _ hab => qmk_eq_of G (bisimilar_R D hab))

theorem Rq_qmk (a : ObC G) : Rq D (qmk G a) = qmk G ⟨D.R a.1, coreOb_R D a.2⟩ := rfl

theorem Rq_qCore {c : G.C} (h : CoreOb G c) : Rq D (qCore G c) = qCore G (D.R c) := by
  rw [qCore_of G h, Rq_qmk, qCore_of G (coreOb_R D h)]

/-- G/~ is a symmetric sequential game. -/
theorem seqSym_QGame (hG : SeqSym G) : SeqSym (QGame G) := by
  obtain ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩ := hG.exA
  let D : SeqSymData G := ⟨A, R, hAA, hAp, hAd, hRR, hRq, hRe, hRm⟩
  refine ⟨A, Rq D, hAA, hAp, hAd, ?_, ?_, ?_, ?_⟩
  · intro z
    induction z using Quotient.ind with
    | _ a =>
      show qmk G ⟨D.R (D.R a.1), _⟩ = qmk G a
      exact congrArg (qmk G) (Subtype.ext (D.RR a.1))
  · show qmk G ⟨D.R G.q0, _⟩ = qmk G ⟨G.q0, coreOb_q0 G⟩
    exact congrArg (qmk G) (Subtype.ext D.Rq0)
  · intro z
    induction z using Quotient.ind with
    | _ a => exact D.Rend a.1
  · intro z m
    induction z using Quotient.ind with
    | _ a =>
      show Option.map (Rq D) ((QGame G).mv (qmk G ⟨D.R a.1, coreOb_R D a.2⟩) (D.A m)) =
        (QGame G).mv (qmk G a) m
      show Option.map (Rq D) (qmvAux G ⟨D.R a.1, _⟩ (D.A m)) = qmvAux G a m
      unfold qmvAux
      have hend : G.ended (D.R a.1) ↔ G.ended a.1 := D.Rend a.1
      have hpass : D.A m ≠ Mv.pass ↔ m ≠ Mv.pass := by
        constructor
        · intro h h'; exact h ((D.Apass_iff m).mpr h')
        · intro h h'; exact h ((D.Apass_iff m).mp h')
      have hdeg : (Mv.deg0 (D.A m) ∨ Mv.deg1 (D.A m)) ↔ (Mv.deg0 m ∨ Mv.deg1 m) := by
        constructor
        · rintro (h | h)
          · exact Or.inr ((D.Adeg1 m).mpr h)
          · exact Or.inl ((D.Adeg m).mpr h)
        · rintro (h | h)
          · exact Or.inr ((D.Adeg m).mp h)
          · exact Or.inl ((D.Adeg1 m).mp h)
      by_cases h : ¬G.ended a.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m)
      · have h' : ¬G.ended (D.R a.1) ∧ D.A m ≠ Mv.pass ∧ (Mv.deg0 (D.A m) ∨ Mv.deg1 (D.A m)) :=
          ⟨fun he => h.1 (hend.mp he), hpass.mpr h.2.1, hdeg.mpr h.2.2⟩
        rw [if_pos h', if_pos h]
        have hRm := D.Rmv a.1 m
        rw [← hRm]
        cases hmy : G.mv (D.R a.1) (D.A m) with
        | none => rfl
        | some y =>
          show some (Rq D (qCore G y)) = some (qCore G (D.R y))
          rw [Rq_qCore D (coreOb_mv G (coreOb_R D a.2) h'.2.2 h'.2.1 h'.1 hmy)]
      · have h' : ¬(¬G.ended (D.R a.1) ∧ D.A m ≠ Mv.pass ∧
            (Mv.deg0 (D.A m) ∨ Mv.deg1 (D.A m))) :=
          fun hh => h ⟨fun he => hh.1 (hend.mpr he), hpass.mp hh.2.1, hdeg.mp hh.2.2⟩
        rw [if_neg h', if_neg h]
        rfl

end Sym

/-! ### Theorem thm_zero on the quotient (the clauses of 6.9 (2), (3)) -/

theorem BSet.img_single {α β : Type} (f : α → β) (a : α) :
    BSet.img f (BSet.single a) = BSet.single (f a) := by
  funext z
  apply propext
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x = a at hx
    rw [hx]; rfl
  · intro hz
    change z = f a at hz
    exact ⟨a, rfl, hz.symm⟩

/-- A conflict whose two outcomes have non bisimilar cores (the
    hypothesis of thm_zero (2) for the radius spectrum). -/
def HasConflictNB (G : SeqGame Mv) : Prop :=
  ∃ (A : NSet G) (a : G.S) (m0 m1 : Mv.M) (P : BSet G.S) (x y : G.S),
    SemiC G (simGame G) A a ∧ ¬sfinal G a ∧ Pmap G a m0 m1 = some P ∧
    P x ∧ P y ∧ ¬Bisimilar G x.coreOf y.coreOf ∧ ∀ z, P z → ¬sfinal G z

/-- A conflict of non bisimilar outcomes descends to the quotient. -/
theorem hasConflict_QGame (G : SeqGame Mv) (h : HasConflictNB G) :
    HasConflict (QGame G) := by
  obtain ⟨A, a, m0, m1, P, x, y, hsc, hna, hP, hx, hy, hxy, hnf⟩ := h
  have ha : CoreOb G a.coreOf := semiC_coreOb G hsc
  refine ⟨qN G A, qS G a, m0, m1, BSet.img (qS G) P, qS G x, qS G y, semiC_qN G hsc,
    fun hf => hna ((sfinal_qS G ha).mp hf), ?_, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_, ?_⟩
  · rw [Pmap_qS G ha, hP]; rfl
  · intro heq
    have hcx : CoreOb G x.coreOf := Pmap_coreOb G ha hP hx
    have hcy : CoreOb G y.coreOf := Pmap_coreOb G ha hP hy
    have h1 : qCore G x.coreOf = qCore G y.coreOf := by
      rw [← qS_coreOf, ← qS_coreOf, heq]
    exact hxy (bisimilar_of_qCore_eq G hcx hcy h1)
  · rintro z ⟨w, hw, rfl⟩ hf
    exact hnf w hw ((sfinal_qS G (Pmap_coreOb G ha hP hw)).mp hf)

/-- Theorem thm_zero (2), the radius spectrum clause: a conflict of non
    bisimilar outcomes puts 0 in the radius spectrum. -/
theorem thm_zero_2_radius (G : SeqGame Mv) (hG : SeqSym G) (h : HasConflictNB G) :
    InRadiusSpectrum G (some 0) :=
  (thm_zero_2 (QGame G) (seqSym_QGame hG) (hasConflict_QGame G h)).2

theorem scAssoc_coreOb (G : SeqGame Mv) {a : G.S} (h : ScAssoc G a) : CoreOb G a.coreOf := by
  obtain ⟨A, hA⟩ := (scAssoc_iff_semiC G a).mp h
  exact semiC_coreOb G hA

/-- Under the hypothesis of thm_zero (3), every associated state of
    Sim(G/~) is the image of one of Sim(G). -/
theorem scAssoc_qS_surj (G : SeqGame Mv) (hall : AllCommute G) {z : (QGame G).S}
    (h : ScAssoc (QGame G) z) : ∃ a, ScAssoc G a ∧ qS G a = z := by
  induction h with
  | init => exact ⟨sInit G, ScAssoc.init, qS_sInit G⟩
  | @step z m0 m1 _ hc hdef ih =>
    obtain ⟨a, ha, rfl⟩ := ih
    have hca : CoreOb G a.coreOf := scAssoc_coreOb G ha
    have hdefG : simDefP G (BSet.single a) m0 m1 := by
      refine (simDefP_img G (obSet_single G hca) m0 m1).mp ?_
      rw [BSet.img_single]; exact hdef
    exact ⟨assocOf G a m0 m1, ScAssoc.step ha (hall a m0 m1 ha hdefG) hdefG,
      (assocOf_qS G hca m0 m1).symm⟩

theorem allCommute_QGame (G : SeqGame Mv) (hall : AllCommute G) :
    AllCommute (QGame G) := by
  intro z m0 m1 hz hdef
  obtain ⟨a, ha, rfl⟩ := scAssoc_qS_surj G hall hz
  have hca : CoreOb G a.coreOf := scAssoc_coreOb G ha
  have hdefG : simDefP G (BSet.single a) m0 m1 := by
    refine (simDefP_img G (obSet_single G hca) m0 m1).mp ?_
    rw [BSet.img_single]; exact hdef
  exact commuteAt_qS G hca (hall a m0 m1 ha hdefG)

/-- Theorem thm_zero (3), the radius spectrum clause. -/
theorem thm_zero_3_radius (G : SeqGame Mv) (hG : SeqSym G) (hall : AllCommute G) :
    InRadiusSpectrum G none ∧ ∀ r, InRadiusSpectrum G r → r = none :=
  thm_zero_3 (QGame G) (seqSym_QGame hG) (allCommute_QGame G hall)


/-! ### Bisimilar games have the same radius spectrum (Lemma lem_bisimulation (2)) -/

section Iso

/-- Equal shapes: the same constructor and gradings. -/
def ShapeEq {C C' : Type} : PState C → PState C' → Prop
  | .live _ g j, .live _ g' j' => g = g' ∧ j = j'
  | .done _ g, .done _ g' => g = g'
  | _, _ => False

variable {G G' : SeqGame Mv} {R : G.C → G'.C → Prop} (hB : IsBisim G G' R)
include hB

/-- A bisimulation follows every move: a legally obtainable state of G
    has a partner in G' of the same shape with related core. -/
theorem partner_of_seqReach {s : G.S} (hs : SeqReach G s) :
    ∃ s', SeqReach G' s' ∧ ShapeEq s s' ∧ R s.coreOf s'.coreOf := by
  induction hs with
  | init => exact ⟨sInit G', SeqReach.init, ⟨rfl, rfl⟩, hB.init⟩
  | @step s t m _ hE ih =>
    obtain ⟨s', hs', hsh, hR⟩ := ih
    cases s with
    | done c g => exact absurd hE (fun h => Option.noConfusion h)
    | live c g j =>
      cases s' with
      | done _ _ => exact False.elim hsh
      | live c' g' j' =>
        obtain ⟨rfl, rfl⟩ := hsh
        have hstep := hB.step c c' hR g j m
        rw [hE] at hstep
        obtain ⟨t', hE', hRt⟩ := optCoreRel_some R hstep rfl
        refine ⟨t', SeqReach.step (m := m) hs' hE', ?_, hRt⟩
        -- the shapes agree: both values are read off the same case of sE
        have he : ¬G.ended c := by
          intro he
          rw [prop_finalnomove G (s := PState.live c g j) he m] at hE
          exact Option.noConfusion hE
        have he' : ¬G'.ended c' := fun h => he ((hB.ended hR).mpr h)
        by_cases hm : m = Mv.pass
        · subst hm
          rw [sE_pass G c g j he] at hE
          rw [sE_pass G' c' g j he'] at hE'
          rw [← Option.some_inj.mp hE, ← Option.some_inj.mp hE']
          cases j with
          | false => exact ⟨rfl, rfl⟩
          | true => exact rfl
        · rw [sE_nonpass G c g j m hm he] at hE
          rw [sE_nonpass G' c' g j m hm he'] at hE'
          by_cases hg : (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m)
          · rw [if_pos hg] at hE hE'
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some'.mp hE
            obtain ⟨_, _, rfl⟩ := Option.map_eq_some'.mp hE'
            exact ⟨rfl, rfl⟩
          · rw [if_neg hg] at hE
            exact absurd hE (fun h => Option.noConfusion h)

theorem partner_of_coreOb {x : G.C} (hx : CoreOb G x) :
    ∃ x', CoreOb G' x' ∧ R x x' := by
  obtain ⟨g, hg⟩ := hx
  obtain ⟨s', hs', hsh, hR⟩ := partner_of_seqReach hB hg
  cases s' with
  | done _ _ => exact False.elim hsh
  | live c' g' j' =>
    obtain ⟨-, hj⟩ := hsh
    subst hj
    exact ⟨c', ⟨g', hs'⟩, hR⟩

/-- A chosen partner of a legally obtainable core. -/
noncomputable def partner (a : ObC G) : ObC G' :=
  ⟨Classical.choose (partner_of_coreOb hB a.2),
    (Classical.choose_spec (partner_of_coreOb hB a.2)).1⟩

theorem partner_rel (a : ObC G) : R a.1 (partner hB a).1 :=
  (Classical.choose_spec (partner_of_coreOb hB a.2)).2

/-- Two partners of bisimilar cores are bisimilar: R⁻¹ ∘ ~ ∘ R is a
    bisimulation. -/
theorem bisimilar_of_partners {x y : G.C} {x' y' : G'.C} (hxy : Bisimilar G x y)
    (hx : R x x') (hy : R y y') : Bisimilar G' x' y' :=
  ⟨_, (hB.flip.comp (isBisim_bisimilar G)).comp hB, y, ⟨x, hx, hxy⟩, hy⟩

theorem bisimilar_of_partners' {x y : G.C} {x' y' : G'.C} (hxy : Bisimilar G' x' y')
    (hx : R x x') (hy : R y y') : Bisimilar G x y :=
  ⟨_, (hB.comp (isBisim_bisimilar G')).comp hB.flip, y', ⟨x', hx, hxy⟩, hy⟩

/-- The classes of G/~ to those of G'/~. -/
noncomputable def fQ : QC G → QC G' :=
  Quotient.lift (fun a : ObC G => qmk G' (partner hB a))
    (fun a b hab => qmk_eq_of G'
      (bisimilar_of_partners hB hab (partner_rel hB a) (partner_rel hB b)))

theorem fQ_qmk (a : ObC G) : fQ hB (qmk G a) = qmk G' (partner hB a) := rfl

theorem fQ_mk (a : ObC G) : fQ hB (Quotient.mk (obSetoid G) a) = qmk G' (partner hB a) := rfl

theorem fQ_qCore {x : G.C} (hx : CoreOb G x) {x' : G'.C} (hx' : CoreOb G' x')
    (hR : R x x') : fQ hB (qCore G x) = qCore G' x' := by
  rw [qCore_of G hx, fQ_qmk, qCore_of G' hx']
  exact qmk_eq_of G' (bisimilar_of_partners hB (bisimilar_refl G x) (partner_rel hB ⟨x, hx⟩) hR)

theorem fQ_gQ (z : QC G) : fQ hB.flip (fQ hB z) = z := by
  induction z using Quotient.ind with
  | _ a =>
    rw [fQ_mk, fQ_qmk]
    apply qmk_eq_of
    show Bisimilar G (partner hB.flip (partner hB a)).1 a.1
    have h1 : R a.1 (partner hB a).1 := partner_rel hB a
    have h2 : R (partner hB.flip (partner hB a)).1 (partner hB a).1 :=
      partner_rel hB.flip (partner hB a)
    exact bisimilar_of_partners' hB (bisimilar_refl G' _) h2 h1

/-- The isomorphism of the minimal quotients induced by a bisimulation. -/
noncomputable def bisimIso : SeqIso (QGame G) (QGame G') where
  fM := id
  gM := id
  gfM := fun _ => rfl
  fgM := fun _ => rfl
  deg0 := fun _ => Iff.rfl
  deg1 := fun _ => Iff.rfl
  fC := fQ hB
  gC := fQ hB.flip
  gfC := fQ_gQ hB
  fgC := fQ_gQ hB.flip
  q0 := by
    show fQ hB (qmk G ⟨G.q0, coreOb_q0 G⟩) = qmk G' ⟨G'.q0, coreOb_q0 G'⟩
    rw [fQ_qmk]
    exact qmk_eq_of G' (bisimilar_of_partners hB (bisimilar_refl G G.q0)
      (partner_rel hB ⟨G.q0, coreOb_q0 G⟩) hB.init)
  ended := by
    intro z
    induction z using Quotient.ind with
    | _ a =>
      rw [fQ_mk]
      show G'.ended (partner hB a).1 ↔ G.ended a.1
      exact (hB.ended (partner_rel hB a)).symm
  mv := by
    intro z m hm
    induction z using Quotient.ind with
    | _ a =>
      rw [fQ_mk]
      show Option.map (fQ hB) (qmvAux G a m) = qmvAux G' (partner hB a) m
      unfold qmvAux
      have hend : G.ended a.1 ↔ G'.ended (partner hB a).1 := hB.ended (partner_rel hB a)
      by_cases h : ¬G.ended a.1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m)
      · have h' : ¬G'.ended (partner hB a).1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m) :=
          ⟨fun he => h.1 (hend.mpr he), h.2.1, h.2.2⟩
        rw [if_pos h, if_pos h']
        have hrel := hB.mv (partner_rel hB a) m h.2.1 h.2.2 h.1
        revert hrel
        cases hmy : G.mv a.1 m with
        | none =>
          cases hmy' : G'.mv (partner hB a).1 m with
          | none => intro _; rfl
          | some _ => intro hrel; exact False.elim hrel
        | some y =>
          cases hmy' : G'.mv (partner hB a).1 m with
          | none => intro hrel; exact False.elim hrel
          | some y' =>
            intro hrel
            show some (fQ hB (qCore G y)) = some (qCore G' y')
            rw [fQ_qCore hB (coreOb_mv G a.2 h.2.2 h.2.1 h.1 hmy)
              (coreOb_mv G' (partner hB a).2 h'.2.2 h'.2.1 h'.1 hmy') hrel]
      · have h' : ¬(¬G'.ended (partner hB a).1 ∧ m ≠ Mv.pass ∧ (Mv.deg0 m ∨ Mv.deg1 m)) :=
          fun hh => h ⟨fun he => hh.1 (hend.mp he), hh.2.1, hh.2.2⟩
        rw [if_neg h, if_neg h']
        rfl

end Iso

/-- Lemma lem_bisimulation (2): bisimilar games have the same radius
    spectrum. -/
theorem lem_bisimulation_2 {G G' : SeqGame Mv} (h : GamesBisimilar G G') (r : Option Nat) :
    InRadiusSpectrum G r ↔ InRadiusSpectrum G' r := by
  obtain ⟨R, hB⟩ := h
  exact lem_dynamics_3 (bisimIso hB) r


/-! ### Lemma lem_bisimulation (3): a minimal game and its quotient have
    the same raw radius spectrum — simultaneizations transported along π -/

section Transport

variable {G : SeqGame Mv} (H : SimulGame Mv)

/-- Associated states have legally obtainable cores (any simultaneous
    game). -/
theorem semiC_coreOb' {s : H.B} {a : G.S} (h : SemiC G H s a) : CoreOb G a.coreOf := by
  induction h with
  | init => exact coreOb_q0 G
  | @step s b s' m0 m1 _ hc _ ih =>
    obtain ⟨x, y, hx, -, -⟩ := hc
    obtain ⟨w, hw0, hw1⟩ := hash2_split G hx
    have hax : assocOf G b m0 m1 = sN x := by unfold assocOf; rw [hx]; rfl
    rw [hax, coreOb_sN]
    exact coreOb_hashOp G (coreOb_hashOp G ih hw0) hw1

/-- Semi-classical states relative to G are semi-classical relative to
    G/~, the associated state mapped. -/
theorem semiC_qS {s : H.B} {a : G.S} (h : SemiC G H s a) :
    SemiC (QGame G) H s (qS G a) := by
  induction h with
  | init => rw [qS_sInit]; exact SemiC.init
  | @step s b s' m0 m1 hsc hc hp ih =>
    have hb : CoreOb G b.coreOf := semiC_coreOb' H hsc
    rw [← assocOf_qS G hb]
    exact SemiC.step ih (commuteAt_qS G hb hc) hp

theorem commuteAt_qS_rev (hmin : Minimal G) {b : G.S} (hb : CoreOb G b.coreOf)
    {m0 m1 : Mv.M} (hc : CommuteAt (QGame G) (qS G b) m0 m1) : CommuteAt G b m0 m1 := by
  obtain ⟨x', y', hx', hy', hxy'⟩ := hc
  rw [hash2_qS G hb] at hx' hy'
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some'.mp hx'
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some'.mp hy'
  refine ⟨x, y, hx, hy, ?_⟩
  rw [sN_qS, sN_qS] at hxy'
  have hcx : CoreOb G (sN x).coreOf := by
    rw [coreOb_sN]
    obtain ⟨w, hw0, hw1⟩ := hash2_split G hx
    exact coreOb_hashOp G (coreOb_hashOp G hb hw0) hw1
  have hcy : CoreOb G (sN y).coreOf := by
    rw [coreOb_sN]
    obtain ⟨w, hw0, hw1⟩ := hash2_split G hy
    exact coreOb_hashOp G (coreOb_hashOp G hb hw0) hw1
  exact qS_inj G hmin hcx hcy hxy'

/-- Over a minimal game, semi-classical relative to G/~ comes from
    semi-classical relative to G. -/
theorem semiC_qS_rev (hmin : Minimal G) {s : H.B} {z : (QGame G).S}
    (h : SemiC (QGame G) H s z) : ∃ a, SemiC G H s a ∧ qS G a = z := by
  induction h with
  | init => exact ⟨sInit G, SemiC.init, qS_sInit G⟩
  | @step s z s' m0 m1 _ hc hp ih =>
    obtain ⟨b, hb, rfl⟩ := ih
    have hcb : CoreOb G b.coreOf := semiC_coreOb' H hb
    exact ⟨assocOf G b m0 m1, SemiC.step hb (commuteAt_qS_rev hmin hcb hc) hp,
      (assocOf_qS G hcb m0 m1).symm⟩

/-- Distances of classical play agree (over a minimal game). -/
theorem withinD_qS (hmin : Minimal G) (ρ : H.B → BSet G.S) (ρ' : H.B → BSet (QGame G).S)
    (d : Nat) (s : H.B) : WithinD (QGame G) H ρ' d s ↔ WithinD G H ρ d s := by
  constructor
  · intro h
    induction h with
    | base hsc =>
      obtain ⟨a, ha, -⟩ := semiC_qS_rev H hmin hsc
      exact WithinD.base ha
    | ofLe _ ih => exact WithinD.ofLe ih
    | step _ hp ih => exact WithinD.step ih hp
  · intro h
    induction h with
    | base hsc => exact WithinD.base (semiC_qS H hsc)
    | ofLe _ ih => exact WithinD.ofLe ih
    | step _ hp ih => exact WithinD.step ih hp

/-- Faithfulness at s reads the branches' interfaces and finality, which
    π preserves. -/
theorem faithfulAt_img (ρ : H.B → BSet G.S) {s : H.B} (hA : ObSet G (ρ s)) :
    FaithfulAt (QGame G) H (fun t => BSet.img (qS G) (ρ t)) s ↔ FaithfulAt G H ρ s := by
  constructor
  · rintro ⟨⟨z, a, ha, -⟩, heq⟩
    refine ⟨⟨a, ha⟩, fun m => ?_⟩
    rw [heq m]
    constructor
    · rintro h a ha
      exact (interface0_qS G (hA a ha) m).mp (h (qS G a) ⟨a, ha, rfl⟩)
    · rintro h z ⟨a, ha, rfl⟩
      exact (interface0_qS G (hA a ha) m).mpr (h a ha)
  · rintro ⟨⟨a, ha⟩, heq⟩
    refine ⟨⟨qS G a, a, ha, rfl⟩, fun m => ?_⟩
    rw [heq m]
    constructor
    · rintro h z ⟨a, ha, rfl⟩
      exact (interface0_qS G (hA a ha) m).mpr (h a ha)
    · rintro h a ha
      exact (interface0_qS G (hA a ha) m).mp (h (qS G a) ⟨a, ha, rfl⟩)

theorem isSimple_qS : IsSimple (QGame G) H ↔ IsSimple G H := by
  constructor
  · intro h s hs hnf hm
    obtain ⟨z, hz, hI⟩ := h s hs hnf hm
    obtain ⟨a, ha, rfl⟩ := seqReach_qS_surj G hz
    refine ⟨a, ha, fun m => ?_⟩
    rw [← hI m, interface0_qS G (coreOb_of_seqReach G ha) m]
  · intro h s hs hnf hm
    obtain ⟨a, ha, hI⟩ := h s hs hnf hm
    refine ⟨qS G a, seqReach_qS G ha, fun m => ?_⟩
    rw [← hI m, interface0_qS G (coreOb_of_seqReach G ha) m]

/-! #### The pushforward -/

/-- A simultaneization of G, pushed forward to G/~. -/
theorem isSimultaneization_push (hmin : Minimal G) {ρ : H.B → BSet G.S}
    (hsim : IsSimultaneization G H ρ) :
    IsSimultaneization (QGame G) H (fun t => BSet.img (qS G) (ρ t)) where
  rho_init := by
    intro z
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [(hsim.rho_init a).mp ha]
      exact qS_sInit G
    · intro hz
      change z = sInit (QGame G) at hz
      exact ⟨sInit G, (hsim.rho_init _).mpr rfl, by rw [hz, qS_sInit]⟩
  nat_defined := by
    intro s m0 m1 hs hp
    exact (simDefP_img G (rho_coreOb G H hsim hs) m0 m1).mpr (hsim.nat_defined hs hp)
  nat_incl := by
    intro s s' m0 m1 hs hp z hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [simVal_img G (rho_coreOb G H hsim hs) m0 m1]
    exact ⟨a, hsim.nat_incl hs hp a ha, rfl⟩
  semiclassical := by
    intro s z hsc
    obtain ⟨a, ha, rfl⟩ := semiC_qS_rev H hmin hsc
    intro w
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [(hsim.semiclassical ha b).mp hb]
      rfl
    · intro hw
      change w = qS G a at hw
      exact ⟨a, (hsim.semiclassical ha a).mpr rfl, hw.symm⟩

theorem faithfulWithin_push (hmin : Minimal G) {ρ : H.B → BSet G.S}
    (hsim : IsSimultaneization G H ρ) (d : Nat) :
    FaithfulWithin (QGame G) H (fun t => BSet.img (qS G) (ρ t)) d ↔
      FaithfulWithin G H ρ d := by
  constructor
  · intro h s hw
    have hw' := (withinD_qS H hmin ρ (fun t => BSet.img (qS G) (ρ t)) d s).mpr hw
    exact (faithfulAt_img H ρ (rho_coreOb G H hsim (simReach_of_withinD G H ρ hw))).mp (h s hw')
  · intro h s hw
    have hw' := (withinD_qS H hmin ρ (fun t => BSet.img (qS G) (ρ t)) d s).mp hw
    exact (faithfulAt_img H ρ (rho_coreOb G H hsim (simReach_of_withinD G H ρ hw'))).mpr (h s hw')

theorem hasRadius_push (hmin : Minimal G) {ρ : H.B → BSet G.S}
    (hsim : IsSimultaneization G H ρ) (r : Option Nat) :
    HasRadius (QGame G) H (fun t => BSet.img (qS G) (ρ t)) r ↔ HasRadius G H ρ r := by
  cases r with
  | none =>
    show (∀ d, FaithfulWithin (QGame G) H _ d) ↔ ∀ d, FaithfulWithin G H ρ d
    constructor
    · intro h d; exact (faithfulWithin_push H hmin hsim d).mp (h d)
    · intro h d; exact (faithfulWithin_push H hmin hsim d).mpr (h d)
  | some d =>
    show (FaithfulWithin (QGame G) H _ d ∧ ¬FaithfulWithin (QGame G) H _ (d+1)) ↔ _
    rw [faithfulWithin_push H hmin hsim d, faithfulWithin_push H hmin hsim (d+1)]
    exact Iff.rfl

/-! #### The pullback -/

/-- The pullback of a branch semantics: the states of legally
    obtainable core whose image lies in the branch set. -/
def pullRho (ρ : H.B → BSet (QGame G).S) : H.B → BSet G.S :=
  fun s a => CoreOb G a.coreOf ∧ ρ s (qS G a)

theorem pullRho_obSet (ρ : H.B → BSet (QGame G).S) (s : H.B) : ObSet G (pullRho H ρ s) :=
  fun _ ha => ha.1

/-- A legally obtainable class is the class of a legally obtainable core. -/
theorem coreOb_QGame_rep {z : (QGame G).C} (h : CoreOb (QGame G) z) :
    ∃ c, CoreOb G c ∧ qCore G c = z := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s, hs, hsz⟩ := seqReach_qS_surj G hg
  cases s with
  | done _ _ => exact absurd hsz (fun h => PState.noConfusion h)
  | live c g' j =>
    refine ⟨c, coreOb_of_seqReach G hs, ?_⟩
    have := congrArg PState.coreOf hsz
    exact this

/-- Every branch at a legally obtainable state is the image of a state
    of legally obtainable core. -/
theorem rho_rep {ρ : H.B → BSet (QGame G).S} (hsim : IsSimultaneization (QGame G) H ρ)
    {s : H.B} (hs : SimReach H s) {z : (QGame G).S} (hz : ρ s z) :
    ∃ a, CoreOb G a.coreOf ∧ qS G a = z := by
  have hob := rho_coreOb (QGame G) H hsim hs z hz
  obtain ⟨c, hc, hcz⟩ := coreOb_QGame_rep hob
  cases z with
  | live cz g j =>
    have hcz' : qCore G c = cz := hcz
    exact ⟨PState.live c g j, hc, by show PState.live (qCore G c) g j = _; rw [hcz']⟩
  | done cz g =>
    have hcz' : qCore G c = cz := hcz
    exact ⟨PState.done c g, hc, by show PState.done (qCore G c) g = _; rw [hcz']⟩

theorem img_pullRho {ρ : H.B → BSet (QGame G).S} (hsim : IsSimultaneization (QGame G) H ρ)
    {s : H.B} (hs : SimReach H s) : BSet.img (qS G) (pullRho H ρ s) = ρ s := by
  funext z
  apply propext
  constructor
  · rintro ⟨a, ⟨-, ha⟩, rfl⟩
    exact ha
  · intro hz
    obtain ⟨a, hca, rfl⟩ := rho_rep H hsim hs hz
    exact ⟨a, ⟨hca, hz⟩, rfl⟩

/-- A simultaneization of G/~, pulled back to a minimal G. -/
theorem isSimultaneization_pull (hmin : Minimal G) {ρ : H.B → BSet (QGame G).S}
    (hsim : IsSimultaneization (QGame G) H ρ) :
    IsSimultaneization G H (pullRho H ρ) where
  rho_init := by
    intro a
    constructor
    · rintro ⟨hca, ha⟩
      have h1 : qS G a = sInit (QGame G) := (hsim.rho_init _).mp ha
      rw [← qS_sInit] at h1
      exact qS_inj G hmin hca (coreOb_q0 G) h1
    · intro ha
      change a = sInit G at ha
      rw [ha]
      exact ⟨coreOb_q0 G, (hsim.rho_init _).mpr (qS_sInit G)⟩
  nat_defined := by
    intro s m0 m1 hs hp a ⟨hca, ha⟩
    have h := hsim.nat_defined hs hp (qS G a) ha
    refine ⟨fun hf => h.1 ((sfinal_qS G hca).mpr hf), ?_⟩
    have h2 := h.2
    rw [Pmap_qS G hca, isSome_map'] at h2
    exact h2
  nat_incl := by
    intro s s' m0 m1 hs hp a ⟨hca, ha⟩
    obtain ⟨z, hz, P', hP', hz'⟩ := hsim.nat_incl hs hp (qS G a) ha
    obtain ⟨b, hcb, rfl⟩ := rho_rep H hsim hs hz
    rw [Pmap_qS G hcb] at hP'
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some'.mp hP'
    obtain ⟨w, hw, hwa⟩ := hz'
    have hcw : CoreOb G w.coreOf := Pmap_coreOb G hcb hP hw
    rw [qS_inj G hmin hcw hca hwa] at hw
    exact ⟨b, ⟨hcb, hz⟩, P, hP, hw⟩
  semiclassical := by
    intro s a hsc
    have hsc' := semiC_qS H hsc
    have hca : CoreOb G a.coreOf := semiC_coreOb' H hsc
    intro b
    constructor
    · rintro ⟨hcb, hb⟩
      exact qS_inj G hmin hcb hca ((hsim.semiclassical hsc' _).mp hb)
    · intro hb
      change b = a at hb
      rw [hb]
      exact ⟨hca, (hsim.semiclassical hsc' _).mpr rfl⟩

theorem faithfulAt_congr {G0 : SeqGame Mv} {G1 : SimulGame Mv} {ρ ρ' : G1.B → BSet G0.S}
    {s : G1.B} (h : ρ s = ρ' s) : FaithfulAt G0 G1 ρ s ↔ FaithfulAt G0 G1 ρ' s := by
  unfold FaithfulAt
  rw [h]

theorem faithfulAt_pull {ρ : H.B → BSet (QGame G).S}
    (hsim : IsSimultaneization (QGame G) H ρ) {s : H.B} (hs : SimReach H s) :
    FaithfulAt G H (pullRho H ρ) s ↔ FaithfulAt (QGame G) H ρ s := by
  have h1 := faithfulAt_img H (pullRho H ρ) (pullRho_obSet H ρ s)
  have h2 : FaithfulAt (QGame G) H (fun t => BSet.img (qS G) (pullRho H ρ t)) s ↔
      FaithfulAt (QGame G) H ρ s :=
    faithfulAt_congr (img_pullRho H hsim hs)
  exact h1.symm.trans h2

theorem faithfulWithin_pull (hmin : Minimal G) {ρ : H.B → BSet (QGame G).S}
    (hsim : IsSimultaneization (QGame G) H ρ) (d : Nat) :
    FaithfulWithin G H (pullRho H ρ) d ↔ FaithfulWithin (QGame G) H ρ d := by
  constructor
  · intro h s hw
    have hw' := (withinD_qS H hmin (pullRho H ρ) ρ d s).mp hw
    exact (faithfulAt_pull H hsim (simReach_of_withinD _ H ρ hw)).mp (h s hw')
  · intro h s hw
    have hw' := (withinD_qS H hmin (pullRho H ρ) ρ d s).mpr hw
    exact (faithfulAt_pull H hsim (simReach_of_withinD _ H ρ hw')).mpr (h s hw')

theorem hasRadius_pull (hmin : Minimal G) {ρ : H.B → BSet (QGame G).S}
    (hsim : IsSimultaneization (QGame G) H ρ) (r : Option Nat) :
    HasRadius G H (pullRho H ρ) r ↔ HasRadius (QGame G) H ρ r := by
  cases r with
  | none =>
    show (∀ d, FaithfulWithin G H _ d) ↔ ∀ d, FaithfulWithin (QGame G) H ρ d
    constructor
    · intro h d; exact (faithfulWithin_pull H hmin hsim d).mp (h d)
    · intro h d; exact (faithfulWithin_pull H hmin hsim d).mpr (h d)
  | some d =>
    show (FaithfulWithin G H _ d ∧ ¬FaithfulWithin G H _ (d+1)) ↔ _
    rw [faithfulWithin_pull H hmin hsim d, faithfulWithin_pull H hmin hsim (d+1)]
    exact Iff.rfl

end Transport

/-- Lemma lem_bisimulation (3): over a minimal game the radius spectrum
    is the raw radius spectrum. -/
theorem lem_bisimulation_3 {G : SeqGame Mv} (hmin : Minimal G) (r : Option Nat) :
    InSpectrum G r ↔ InRadiusSpectrum G r := by
  constructor
  · rintro ⟨H, ρ, rel, heq, hok, hsym, hsim, hsimple, hrad⟩
    exact ⟨H, fun t => BSet.img (qS G) (ρ t), rel, heq, hok, hsym,
      isSimultaneization_push H hmin hsim, (isSimple_qS H).mpr hsimple,
      (hasRadius_push H hmin hsim r).mpr hrad⟩
  · rintro ⟨H, ρ, rel, heq, hok, hsym, hsim, hsimple, hrad⟩
    exact ⟨H, pullRho H ρ, rel, heq, hok, hsym,
      isSimultaneization_pull H hmin hsim, (isSimple_qS H).mp hsimple,
      (hasRadius_pull H hmin hsim r).mpr hrad⟩


/-! ### Lemma lem_bisimulation (4), on Sim: π is onto the legally
    obtainable states and carries availability, finality, the evolution
    and the semi-classical states -/

theorem simReach_qN (G : SeqGame Mv) {A : NSet G} (h : SimReach (simGame G) A) :
    SimReach (simGame (QGame G)) (qN G A) := by
  induction h with
  | init => rw [qN_q0]; exact SimReach.init
  | @step A A' m0 m1 hA hp ih =>
    refine SimReach.step (m0 := m0) (m1 := m1) ih ?_
    rw [simGame_pairE_qN G (simReach_obSet G hA) m0 m1, hp]
    rfl

theorem simReach_qN_surj (G : SeqGame Mv) {z : NSet (QGame G)}
    (h : SimReach (simGame (QGame G)) z) :
    ∃ A, SimReach (simGame G) A ∧ qN G A = z := by
  induction h with
  | init => exact ⟨(simGame G).q0, SimReach.init, qN_q0 G⟩
  | @step z z' m0 m1 _ hp ih =>
    obtain ⟨A, hA, rfl⟩ := ih
    rw [simGame_pairE_qN G (simReach_obSet G hA) m0 m1] at hp
    obtain ⟨A', hA', rfl⟩ := Option.map_eq_some'.mp hp
    exact ⟨A', SimReach.step (m0 := m0) (m1 := m1) hA hA', rfl⟩

theorem simGame_avail_qN (G : SeqGame Mv) {A : NSet G} (hA : ObSet G A.1) (m : Mv.M) :
    (simGame (QGame G)).avail (qN G A) m ↔ (simGame G).avail A m :=
  simDef1_img G hA m

theorem simGame_final_qN (G : SeqGame Mv) {A : NSet G} (hA : ObSet G A.1) :
    (simGame (QGame G)).final (qN G A) ↔ (simGame G).final A :=
  simFinal_img G hA

/-- Lemma lem_bisimulation in full, for a symmetric sequential game G:
    (1) G/~ is a symmetric sequential game and the projection is a
    bisimulation; (2) bisimilar games have the same radius spectrum;
    (3) over a minimal G the radius spectrum is the raw radius spectrum;
    (4) π sends the initial state to the initial state, preserves the
    interfaces, is onto the legally obtainable states of G and of
    Sim(G), and, on the branch sets of legally obtainable cores (all
    that Sim(G) reaches), preserves availability, finality and the
    evolution of Sim, and the semi-classical states with their
    associated states. -/
theorem lem_bisimulation (G : SeqGame Mv) (hG : SeqSym G) :
    (SeqSym (QGame G) ∧ IsBisim G (QGame G) (fun x z => CoreOb G x ∧ qCore G x = z))
    ∧ (∀ G' : SeqGame Mv, GamesBisimilar G G' →
        ∀ r, InRadiusSpectrum G r ↔ InRadiusSpectrum G' r)
    ∧ (Minimal G → ∀ r, InSpectrum G r ↔ InRadiusSpectrum G r)
    ∧ (qS G (sInit G) = sInit (QGame G)
      ∧ (∀ (a : G.S) m, CoreOb G a.coreOf → (Interface0 (QGame G) (qS G a) m ↔ Interface0 G a m))
      ∧ (∀ s, SeqReach G s → SeqReach (QGame G) (qS G s))
      ∧ (∀ z, SeqReach (QGame G) z → ∃ s, SeqReach G s ∧ qS G s = z)
      ∧ (∀ A, SimReach (simGame G) A → SimReach (simGame (QGame G)) (qN G A))
      ∧ (∀ z, SimReach (simGame (QGame G)) z → ∃ A, SimReach (simGame G) A ∧ qN G A = z)
      ∧ (∀ (A : NSet G) m, ObSet G A.1 →
          ((simGame (QGame G)).avail (qN G A) m ↔ (simGame G).avail A m))
      ∧ (∀ A : NSet G, ObSet G A.1 →
          ((simGame (QGame G)).final (qN G A) ↔ (simGame G).final A))
      ∧ (∀ (A : NSet G) m0 m1, ObSet G A.1 →
          (simGame (QGame G)).pairE (qN G A) m0 m1 = ((simGame G).pairE A m0 m1).map (qN G))
      ∧ (∀ A a, SemiC G (simGame G) A a →
          SemiC (QGame G) (simGame (QGame G)) (qN G A) (qS G a))) :=
  ⟨⟨seqSym_QGame hG, isBisim_projection G⟩,
   fun _ h r => lem_bisimulation_2 h r,
   fun hmin r => lem_bisimulation_3 hmin r,
   qS_sInit G, fun _ m h => interface0_qS G h m,
   fun _ h => seqReach_qS G h, fun _ h => seqReach_qS_surj G h,
   fun _ h => simReach_qN G h, fun _ h => simReach_qN_surj G h,
   fun _ m h => simGame_avail_qN G h m, fun _ h => simGame_final_qN G h,
   fun _ m0 m1 h => simGame_pairE_qN G h m0 m1,
   fun _ _ h => semiC_qN G h⟩

/-- Theorem thm_zero, the radius spectrum clauses of parts (2) and (3). -/
theorem thm_zero_radius (G : SeqGame Mv) (hG : SeqSym G) :
    (HasConflictNB G → InRadiusSpectrum G (some 0))
    ∧ (AllCommute G → InRadiusSpectrum G none ∧ ∀ r, InRadiusSpectrum G r → r = none) :=
  ⟨fun h => thm_zero_2_radius G hG h, fun h => thm_zero_3_radius G hG h⟩


end SgoGames
