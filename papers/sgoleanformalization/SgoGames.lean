/- SgoGames.lean — the main theorem and the simultaneization theory, the
   abstract game layer, on the printed S(G)-theoretic def_sequential.

   A sequential game with a pass is presented by its cores: the core
   states C(G), the action of the non pass moves, the initial core, and
   the cores at which the pass is undefined (`ended` — king capture for
   chess; empty for Go). Its states are, by definition,
   S (G) = C (G) × Z_2 × Z_2 ⊔ C (G) × Z_2 — the live states with the
   turn grading and the pass grading, and the pairs (PState: live c i j
   / done c i, the pairs written `done`).

   The evolution `sE` is the printed datum E_G, its three axioms by
   construction (verified below as `prop_finalnomove`,
   `sfinal_iff_no_pass`, `prop_pass0`, `prop_pass1`, `prop_nonpass`,
   `prop_doublepass`):
   (1) a state is final exactly when the pass is undefined there, and
       at a final state — an ended core or a pair — no move at all is
       defined;
   (2) at a live state the pass's definedness depends on the core
       alone, E ((x,i,0),0) = (x,i+1,1) and E ((x,i,1),0) = (x,i+1);
   (3) a non pass move of grading i is defined only at live states of
       turn grading i, at (x,i,0) if and only if at (x,i,1), and
       E ((x,i,j),m) = (x',i+1,0) with x' depending on x and m alone.

   The position normal form N — the gradings reset, the core kept, for
   live states and pairs alike — is `sN`, definable outright, and is
   used in P, def_semiclassical (commuting = both composites defined
   with a common normal form), and the branch identification. ("Fresh"
   is NOT used here: it is already coined for the turn's new stones.)

   Design notes for the statement audit:
   - Moves are shared by both game structures (prop_2 by construction).
   - Branch sets are predicates (BSet); finiteness not carried.
   - bar is computed structurally (no choice); # as printed.
   - Radius claims in explicit form; scoring partition and alphabet
     finiteness not carried (unused by the main theorem's clauses).
   - The simultaneous side (SimulGame/SimOK/SimSym) is as printed in
     def_simultaneous and def_symmetric. -/
import SgoDelta

namespace SgoGames

attribute [local instance] Classical.propDecidable

/-- A Z2 graded move alphabet with the pseudo pass move (multi graded). -/
structure Moves where
  M : Type
  deg0 : M → Prop
  deg1 : M → Prop
  pass : M
  pass_deg0 : deg0 pass
  pass_deg1 : deg1 pass
  pass_unique : ∀ m, deg0 m → deg1 m → m = pass

/-- Branch sets: subsets of a state type, as predicates. -/
def BSet (α : Type) : Type := α → Prop

def BSet.single {α} (x : α) : BSet α := fun y => y = x
def BSet.pair {α} (x y : α) : BSet α := fun z => z = x ∨ z = y
def BSet.sub {α} (A B : BSet α) : Prop := ∀ x, A x → B x
def BSet.eqv {α} (A B : BSet α) : Prop := ∀ x, A x ↔ B x

variable {Mv : Moves}

/-- The presentation of a sequential game with a pass, on the printed
    S(G)-theoretic definition (def_sequential): core states with the
    action of the non pass moves, an initial core, and the cores at
    which the pass is undefined — the printed finality, which depends
    on the core alone. -/
structure SeqGame (Mv : Moves) where
  C : Type
  mv : C → Mv.M → Option C
  q0 : C
  ended : C → Prop

/-- The states: by definition, a live core with its bigrading — the
    turn grading g and the pass grading j — or a pair, carrying its
    core and turn grading. S (G) = C (G) × Z_2^2 ⊔ C (G) × Z_2 as
    printed; the pairs are written `done`. -/
inductive PState (C : Type) where
  | live (c : C) (g : Bool) (j : Bool)
  | done (c : C) (g : Bool)

def PState.coreOf {C} : PState C → C
  | .live c _ _ => c
  | .done c _ => c

def SeqGame.S (G : SeqGame Mv) : Type := PState G.C

def sInit (G : SeqGame Mv) : G.S := PState.live G.q0 false false

def sdeg (G : SeqGame Mv) : G.S → Bool
  | .live _ g _ => g
  | .done _ g => g

/-- Finality, as printed: a state is final exactly when the pass is
    undefined there. At a live state this is the core's `ended`; the
    pairs, reached by a double pass, are final. -/
def sfinal (G : SeqGame Mv) : G.S → Prop
  | .live c _ _ => G.ended c
  | .done _ _ => True

/-- The evolution, the printed axioms by construction. At a final
    state — an ended core, or a pair — nothing is defined (axiom 1). A
    pass at a live state flips the turn and raises the pass grading,
    the second consecutive pass landing at the pair (axiom 2). A non
    pass move of the turn's grading acts on the core and lands live at
    pass grading 0 (axiom 3); the game ends there exactly when the new
    core is ended. -/
noncomputable def sE (G : SeqGame Mv) : G.S → Mv.M → Option G.S
  | .live c g b, m =>
    if G.ended c then none
    else if m = Mv.pass then
      if b then some (.done c (!g)) else some (.live c (!g) true)
    else if (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m) then
      (G.mv c m).map fun c' => .live c' (!g) false
    else none
  | .done _ _, _ => none

/-! ### The evolution, computed; the printed axioms of def_sequential -/

/-- The evolution at a live state, unfolded. -/
theorem sE_live (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M) :
    sE G (.live c g j) m =
      (if G.ended c then none
      else if m = Mv.pass then
        (if j then some (.done c (!g)) else some (.live c (!g) true))
      else if (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m) then
        (G.mv c m).map fun c' => .live c' (!g) false
      else none) := rfl

/-- Axiom (1), second half: at a final state — an ended core, or a
    pair — no move at all is defined. -/
theorem prop_finalnomove (G : SeqGame Mv) {s : G.S} (h : sfinal G s) (m : Mv.M) :
    sE G s m = none := by
  cases s with
  | live c g j =>
    have h' : G.ended c := h
    rw [sE_live, if_pos h']
  | done c g => rfl

/-- Axiom (2): the pass at a live state of a core where it is defined. -/
theorem sE_pass (G : SeqGame Mv) (c : G.C) (g j : Bool) (h : ¬G.ended c) :
    sE G (.live c g j) Mv.pass
      = some (if j then .done c (!g) else .live c (!g) true) := by
  rw [sE_live, if_neg h, if_pos rfl]
  cases j <;> rfl

theorem prop_pass0 (G : SeqGame Mv) (c : G.C) (g : Bool) (h : ¬G.ended c) :
    sE G (.live c g false) Mv.pass = some (.live c (!g) true) := by
  rw [sE_pass G c g false h]; rfl

theorem prop_pass1 (G : SeqGame Mv) (c : G.C) (g : Bool) (h : ¬G.ended c) :
    sE G (.live c g true) Mv.pass = some (.done c (!g)) := by
  rw [sE_pass G c g true h]; rfl

/-- Axiom (1), first half: a state is final exactly when the pass is
    undefined there. Finality depends on the core alone (axiom 2). -/
theorem sfinal_iff_no_pass (G : SeqGame Mv) (s : G.S) :
    sfinal G s ↔ sE G s Mv.pass = none := by
  cases s with
  | done c g => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | live c g j =>
    constructor
    · intro h; exact prop_finalnomove G h Mv.pass
    · intro h
      by_cases he : G.ended c
      · exact he
      · rw [sE_pass G c g j he] at h
        exact absurd h (fun h => Option.noConfusion h)

/-- Axiom (3): a non pass move is defined only at live states of its
    grading, at (x,i,0) if and only if at (x,i,1), and it acts on the
    core, landing at pass grading 0. -/
theorem sE_nonpass (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M)
    (hm : m ≠ Mv.pass) (h : ¬G.ended c) :
    sE G (.live c g j) m =
      if (g = false ∧ Mv.deg0 m) ∨ (g = true ∧ Mv.deg1 m) then
        (G.mv c m).map fun c' => .live c' (!g) false
      else none := by
  rw [sE_live, if_neg h, if_neg hm]

/-- Axiom (3), the definedness half: independent of the pass grading. -/
theorem prop_nonpass_j (G : SeqGame Mv) (c : G.C) (g j j' : Bool) (m : Mv.M)
    (hm : m ≠ Mv.pass) :
    (sE G (.live c g j) m).isSome = (sE G (.live c g j') m).isSome := by
  by_cases h : G.ended c
  · rw [prop_finalnomove G (s := PState.live c g j) h m,
      prop_finalnomove G (s := PState.live c g j') h m]
  · rw [sE_nonpass G c g j m hm h, sE_nonpass G c g j' m hm h]

/-- The pass's definedness depends on the core alone: independent of
    both gradings (the printed property (2), for m = 0). -/
theorem prop_pass_j (G : SeqGame Mv) (c : G.C) (g g' j j' : Bool) :
    (sE G (.live c g j) Mv.pass).isSome = (sE G (.live c g' j') Mv.pass).isSome := by
  by_cases h : G.ended c
  · rw [prop_finalnomove G (s := PState.live c g j) h Mv.pass,
      prop_finalnomove G (s := PState.live c g' j') h Mv.pass]
  · rw [sE_pass G c g j h, sE_pass G c g' j' h]; rfl

/-- The printed consequence: if E (s, 0, 0) is defined then it is
    a final state — two consecutive pass moves end the game. -/
theorem prop_doublepass (G : SeqGame Mv) {s t u : G.S}
    (h1 : sE G s Mv.pass = some t) (h2 : sE G t Mv.pass = some u) :
    sfinal G u := by
  cases s with
  | done c g => exact absurd h1 (fun h => Option.noConfusion h)
  | live c g j =>
    by_cases he : G.ended c
    · rw [prop_finalnomove G (s := PState.live c g j) he Mv.pass] at h1
      exact absurd h1 (fun h => Option.noConfusion h)
    · cases j with
      | true =>
        rw [prop_pass1 G c g he] at h1
        rw [← Option.some_inj.mp h1] at h2
        exact absurd h2 (fun h => Option.noConfusion h)
      | false =>
        rw [prop_pass0 G c g he] at h1
        rw [← Option.some_inj.mp h1, prop_pass1 G c (!g) he] at h2
        rw [← Option.some_inj.mp h2]
        exact trivial

/-- Legally obtainable states. -/
inductive SeqReach (G : SeqGame Mv) : G.S → Prop
  | init : SeqReach G (sInit G)
  | step {s s' m} : SeqReach G s → sE G s m = some s' → SeqReach G s'

/-- The bar of the printed # machinery, computed, at the states of
    pass grading 0 and 1: (x, i, 0) ↦ (x, i+1, 1) and (x, i, 1) ↦
    (x, i+1, 0). (The value at a `done` is never consulted: # is
    undefined there.) -/
def sBar {C : Type} : PState C → PState C
  | .live c g false => .live c (!g) true
  | .live c g true  => .live c (!g) false
  | .done c g       => .live c (!g) true

/-- The # operation, as printed (def_hash): at a state of pass grading
    0 or 1, the move at a, else at bar a; undefined at a state of pass
    grading 2 (a `done`). -/
noncomputable def hashOp (G : SeqGame Mv) (a : G.S) (m : Mv.M) :
    Option G.S :=
  match a, sE G a m with
  | .done _ _, _ => none
  | .live _ _ _, some b => some b
  | .live _ _ _, none => sE G (sBar a) m

/-- # at a pair: undefined. -/
theorem hashOp_done (G : SeqGame Mv) (c : G.C) (g : Bool) (m : Mv.M) :
    hashOp G (PState.done c g) m = none := rfl

/-- # at a live state, unfolded. -/
theorem hashOp_live (G : SeqGame Mv) (c : G.C) (g j : Bool) (m : Mv.M) :
    hashOp G (PState.live c g j) m =
      match sE G (PState.live c g j) m with
      | some b => some b
      | none => sE G (sBar (PState.live c g j)) m := by
  unfold hashOp
  cases sE G (PState.live c g j) m <;> rfl

/-- The position normal form (option C, definable), as printed: the
    gradings reset, the core kept — a live state to the S_{0,0} state
    of its core, a final to the grading-0 final of its core. -/
def sN {C : Type} : PState C → PState C
  | .live c _ _ => .live c false false
  | .done c _ => .done c false

/-- Over an ended core nothing is defined, at the state or at its bar
    (the bar of a live state is live over the same core): # is
    undefined at a final live state, as printed. -/
theorem hashOp_ended (G : SeqGame Mv) {c : G.C} (he : G.ended c) (u v : Bool)
    (m : Mv.M) : hashOp G (PState.live c u v) m = none := by
  have hbar : sBar (PState.live c u v) = PState.live c (!u) (!v) := by
    cases v <;> rfl
  unfold hashOp
  rw [prop_finalnomove G (s := PState.live c u v) he m]
  show sE G (sBar (PState.live c u v)) m = none
  rw [hbar]
  exact prop_finalnomove G (s := PState.live c (!u) (!v)) he m

noncomputable def hash2 (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) :
    Option G.S :=
  (hashOp G a m0).bind fun b => hashOp G b m1

/-- The serialization map P: the four priority cases, each term
    replaced by its position normal form. -/
noncomputable def Pmap (G : SeqGame Mv) (a : G.S) (m0 m1 : Mv.M) :
    Option (BSet G.S) :=
  match hash2 G a m0 m1, hash2 G a m1 m0 with
  | some x, some y => some (BSet.pair (sN x) (sN y))
  | some x, none =>
    match hashOp G a m1 with
    | some y => some (BSet.pair (sN x) (sN y))
    | none => none
  | none, some y =>
    match hashOp G a m0 with
    | some x => some (BSet.pair (sN x) (sN y))
    | none => none
  | none, none =>
    match hashOp G a m0, hashOp G a m1 with
    | some x, some y => some (BSet.pair (sN x) (sN y))
    | _, _ => none

/-- Sim(G): single-move definedness at a branch set. -/
def simDef1 (G : SeqGame Mv) (A : BSet G.S) (m : Mv.M) : Prop :=
  ∀ a, A a → ¬sfinal G a ∧ (hashOp G a m).isSome

/-- Sim(G): pair definedness — every branch's P defined. -/
def simDefP (G : SeqGame Mv) (A : BSet G.S) (m0 m1 : Mv.M) : Prop :=
  ∀ a, A a → ¬sfinal G a ∧ (Pmap G a m0 m1).isSome

/-- Sim(G): the pair value — the union of the branch P's. -/
noncomputable def simVal (G : SeqGame Mv) (A : BSet G.S)
    (m0 m1 : Mv.M) : BSet G.S :=
  fun z => ∃ a, A a ∧ ∃ P, Pmap G a m0 m1 = some P ∧ P z

/-- Sim(G) finality: some branch final. -/
def simFinal (G : SeqGame Mv) (A : BSet G.S) : Prop :=
  ∃ a, A a ∧ sfinal G a

/-- def_simultaneous: the data of a combinatorial simultaneous game,
    as before the ruling. -/
structure SimulGame (Mv : Moves) where
  B : Type
  avail : B → Mv.M → Prop
  pairE : B → Mv.M → Mv.M → Option B
  q0 : B
  final : B → Prop

inductive SimReach (G : SimulGame Mv) : G.B → Prop
  | init : SimReach G G.q0
  | step {s s' m0 m1} : SimReach G s → G.pairE s m0 m1 = some s' →
      SimReach G s'

structure SimOK (G : SimulGame Mv) : Prop where
  final_nomove : ∀ {s m}, SimReach G s → G.final s → ¬G.avail s m
  pass_available : ∀ {s}, SimReach G s → ¬G.final s → G.avail s Mv.pass
  pair_of_avail : ∀ {s m0 m1}, SimReach G s → Mv.deg0 m0 → Mv.deg1 m1 →
    G.avail s m0 → G.avail s m1 → (G.pairE s m0 m1).isSome
  avail_of_pair : ∀ {s m0 m1}, SimReach G s →
    (G.pairE s m0 m1).isSome → G.avail s m0 ∧ G.avail s m1
  final_exists : ∃ s, G.final s

/-- A relation lifted to Option: none ~ none, some ~ some via rel,
    a defined and an undefined side never related. -/
def OptBRel {Mv : Moves} (G : SimulGame Mv) (rel : G.B → G.B → Prop) :
    Option G.B → Option G.B → Prop
  | none, none => True
  | some a, some b => rel a b
  | _, _ => False

/-- def_symmetric on the branch semantics. The paper's state space of
    a simultaneization is a SET of branches, and its evolution is a
    UNION over that set (lem_symmetric); so states are compared up to
    the branch-equivalence `rel` (entanglement-set equality here). The
    swap operators A/R are exact involutions fixing q0; the evolution
    commutes with them up to `rel`, matching R̃∘⋃ = ⋃. The single-move
    clause is availability: A(m) is available at R(s) iff m at s (the
    between-turn state (s, m) goes to (R s, A m) by construction). The
    printed clause that R maps W_0 onto W_1 and D onto D reduces, the
    scoring partition not being carried, to the preservation of
    finality. -/
structure SimSym (G : SimulGame Mv) (rel : G.B → G.B → Prop) : Prop where
  exA : ∃ A : Mv.M → Mv.M, ∃ R : G.B → G.B,
    (∀ m, A (A m) = m) ∧ A Mv.pass = Mv.pass ∧
    (∀ m, Mv.deg0 m ↔ Mv.deg1 (A m)) ∧
    (∀ s, R (R s) = s) ∧ R G.q0 = G.q0 ∧
    (∀ s, G.final (R s) ↔ G.final s) ∧
    (∀ s m, G.avail (R s) (A m) ↔ G.avail s m) ∧
    (∀ s m0 m1, OptBRel G rel (Option.map R (G.pairE (R s) (A m1) (A m0)))
      (G.pairE s m0 m1))

/-- The symmetry of a sequential game, on the core presentation:
    a color swap on moves and cores intertwining the action. -/
structure SeqSym (G : SeqGame Mv) : Prop where
  exA : ∃ A : Mv.M → Mv.M, ∃ R : G.C → G.C,
    (∀ m, A (A m) = m) ∧ A Mv.pass = Mv.pass ∧
    (∀ m, Mv.deg0 m ↔ Mv.deg1 (A m)) ∧
    (∀ c, R (R c) = c) ∧ R G.q0 = G.q0 ∧
    (∀ c, G.ended (R c) ↔ G.ended c) ∧
    (∀ c m, Option.map R (G.mv (R c) (A m)) = G.mv c m)

section Symmetrization

variable (G0 : SeqGame Mv) (G1 : SimulGame Mv)

/-- Commuting at a (def_semiclassical, option C): both composites
    defined, with a common position normal form. -/
def CommuteAt (a : G0.S) (m0 m1 : Mv.M) : Prop :=
  ∃ x y, hash2 G0 a m0 m1 = some x ∧ hash2 G0 a m1 m0 = some y ∧
    sN x = sN y

/-- The associated state: the common position normal form. -/
noncomputable def assocOf (a : G0.S) (m0 m1 : Mv.M) : G0.S :=
  sN ((hash2 G0 a m0 m1).getD a)

/-- def_semiclassical: the recursion. -/
inductive SemiC : G1.B → G0.S → Prop
  | init : SemiC G1.q0 (sInit G0)
  | step {s a s' m0 m1} : SemiC s a → CommuteAt G0 a m0 m1 →
      G1.pairE s m0 m1 = some s' → SemiC s' (assocOf G0 a m0 m1)

/-- def_symmetrization, conditions 3 and 4, for the branch semantics. -/
structure IsSimultaneization (ρ : G1.B → BSet G0.S) : Prop where
  rho_init : BSet.eqv (ρ G1.q0) (BSet.single (sInit G0))
  nat_defined : ∀ {s m0 m1}, SimReach G1 s →
    (G1.pairE s m0 m1).isSome → simDefP G0 (ρ s) m0 m1
  nat_incl : ∀ {s s' m0 m1}, SimReach G1 s →
    G1.pairE s m0 m1 = some s' →
    BSet.sub (ρ s') (simVal G0 (ρ s) m0 m1)
  semiclassical : ∀ {s a}, SemiC G0 G1 s a →
    BSet.eqv (ρ s) (BSet.single a)

/-- The interface of a sequential state. -/
def Interface0 (a : G0.S) (m : Mv.M) : Prop := (hashOp G0 a m).isSome

/-- The interface of a simultaneous state. -/
def Interface1 (s : G1.B) (m : Mv.M) : Prop := G1.avail s m

/-- def_faithful at a state, as printed: ρ(s) nonempty, and the
    interface equation I(s) = ⋂ 𝕀(a) over the branches — at every
    state, final or not. -/
def FaithfulAt (ρ : G1.B → BSet G0.S) (s : G1.B) : Prop :=
  (∃ a, (ρ s) a) ∧
  (∀ m, Interface1 G1 s m ↔ ∀ a, (ρ s) a → Interface0 G0 a m)

/-- The three-clause form of the earlier print: nonempty; final only
    if some branch is final; the interface equation at non final
    states. Equivalent to `FaithfulAt` at reachable states of a
    combinatorial simultaneous game (`faithfulAt_iff`): the
    interface of a final state is empty, and 𝕀(a) is empty exactly
    when a is final. -/
def FaithfulAt3 (ρ : G1.B → BSet G0.S) (s : G1.B) : Prop :=
  (∃ a, (ρ s) a) ∧
  (G1.final s → simFinal G0 (ρ s)) ∧
  (¬G1.final s → ∀ m,
    Interface1 G1 s m ↔ ∀ a, (ρ s) a → Interface0 G0 a m)

/-- 𝕀(a) is empty at a final a: # is undefined there. -/
theorem interface0_of_final {a : G0.S} (h : sfinal G0 a) (m : Mv.M) :
    ¬Interface0 G0 a m := by
  unfold Interface0
  cases a with
  | done c g => rw [hashOp_done]; exact fun h => by simp at h
  | live c g j =>
    have he : G0.ended c := h
    rw [hashOp_ended G0 he g j m]
    exact fun h => by simp at h

/-- The pass lies in 𝕀(a) at every non final a. -/
theorem interface0_pass_of_nonfinal {a : G0.S} (h : ¬sfinal G0 a) :
    Interface0 G0 a Mv.pass := by
  unfold Interface0
  cases a with
  | done c g => exact absurd trivial h
  | live c g j =>
    have he : ¬G0.ended c := h
    rw [hashOp_live]
    rw [sE_pass G0 c g j he]
    rfl

/-- 𝕀(a) is empty exactly when a is final. -/
theorem interface0_empty_iff (a : G0.S) :
    (∀ m, ¬Interface0 G0 a m) ↔ sfinal G0 a := by
  constructor
  · intro h
    exact Classical.byContradiction fun hn =>
      h Mv.pass (interface0_pass_of_nonfinal G0 hn)
  · intro h m
    exact interface0_of_final G0 h m

/-- The printed def_faithful and its three-clause form agree at the
    reachable states of a combinatorial simultaneous game. -/
theorem faithfulAt_iff (hOK : SimOK G1) (ρ : G1.B → BSet G0.S) {s : G1.B}
    (hs : SimReach G1 s) :
    FaithfulAt G0 G1 ρ s ↔ FaithfulAt3 G0 G1 ρ s := by
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨hne, ?_, fun _ => heq⟩
    intro hfin
    refine Classical.byContradiction fun hnf => ?_
    -- no branch final: the pass lies in every 𝕀(a), so it is available at s
    have hall : ∀ a, (ρ s) a → Interface0 G0 a Mv.pass := by
      intro a ha
      apply interface0_pass_of_nonfinal
      intro hf
      exact hnf ⟨a, ha, hf⟩
    have hav : Interface1 G1 s Mv.pass := (heq Mv.pass).2 hall
    exact hOK.final_nomove hs hfin hav
  · rintro ⟨hne, hfin, heq⟩
    refine ⟨hne, ?_⟩
    by_cases hf : G1.final s
    · intro m
      constructor
      · intro hav
        exact absurd hav (hOK.final_nomove hs hf)
      · intro hall
        obtain ⟨a, ha, hfa⟩ := hfin hf
        exact absurd (hall a ha) (interface0_of_final G0 hfa m)
    · exact heq hf

inductive WithinD (ρ : G1.B → BSet G0.S) : Nat → G1.B → Prop
  | base {s a} : SemiC G0 G1 s a → WithinD ρ 0 s
  | ofLe {d s} : WithinD ρ d s → WithinD ρ (d+1) s
  | step {d s s' m0 m1} : WithinD ρ d s → G1.pairE s m0 m1 = some s' →
      WithinD ρ (d+1) s'

def FaithfulWithin (ρ : G1.B → BSet G0.S) (d : Nat) : Prop :=
  ∀ s, WithinD G0 G1 ρ d s → FaithfulAt G0 G1 ρ s

/-- Semi-classical states are reachable. -/
theorem simReach_of_semiC {s : G1.B} {a : G0.S}
    (h : SemiC G0 G1 s a) : SimReach G1 s := by
  induction h with
  | init => exact SimReach.init
  | step _ _ hp ih => exact SimReach.step ih hp

/-- States within a distance of classical play are reachable. -/
theorem simReach_of_withinD (ρ : G1.B → BSet G0.S) {d : Nat} {s : G1.B}
    (h : WithinD G0 G1 ρ d s) : SimReach G1 s := by
  induction h with
  | base hsc => exact simReach_of_semiC G0 G1 hsc
  | ofLe _ ih => exact ih
  | step _ hp ih => exact SimReach.step ih hp

/-- Faithfulness within d, from the three-clause form at every state
    within d. -/
theorem faithfulWithin_of_three (hOK : SimOK G1) (ρ : G1.B → BSet G0.S) (d : Nat)
    (h : ∀ s, WithinD G0 G1 ρ d s → FaithfulAt3 G0 G1 ρ s) :
    FaithfulWithin G0 G1 ρ d := fun s hw =>
  (faithfulAt_iff G0 G1 hOK ρ (simReach_of_withinD G0 G1 ρ hw)).2 (h s hw)

/-- The three-clause form at every state within d, from faithfulness
    within d. -/
theorem three_of_faithfulWithin (hOK : SimOK G1) (ρ : G1.B → BSet G0.S) (d : Nat)
    (h : FaithfulWithin G0 G1 ρ d) :
    ∀ s, WithinD G0 G1 ρ d s → FaithfulAt3 G0 G1 ρ s := fun s hw =>
  (faithfulAt_iff G0 G1 hOK ρ (simReach_of_withinD G0 G1 ρ hw)).1 (h s hw)

/-- def_simplesymmetrization. -/
def IsSimple : Prop :=
  ∀ s, SimReach G1 s → ¬G1.final s →
    (∃ m, m ≠ Mv.pass ∧ G1.avail s m) →
    ∃ a, SeqReach G0 a ∧
      ∀ m, Interface0 G0 a m ↔ Interface1 G1 s m

end Symmetrization

end SgoGames
