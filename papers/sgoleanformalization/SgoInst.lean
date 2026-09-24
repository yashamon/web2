/- SgoInst.lean — the main theorem, milestone 1b continued: the games of the
   SGo family instantiated in the abstract layer, and the statement of
   thm_simplesymetrization.

   Design notes, for the statement audit:
   - Moves: Option (Bool × Nat); none is the pseudo pass, some (w, i)
     the move of White (w) or Black (!w) to intersection i. Off-board
     indices are undefined moves (the evolutions guard i < n*n); the
     printed alphabet is the board's moves, and its finiteness is not
     load-bearing in the main theorem's clauses.
   - Go is presented by its core (option C): cores are diagrams, the
     real-move action is bounds-guarded goMoveN, no ended-by-play
     positions. Its states are the bigraded PState (Display n) of the
     general definition; the printed sequential properties hold by
     construction. Stamps in branch diagrams ride as 0, never read.
   - The branch identification: a live branch of the entanglement is
     the position normal form of its diagram — the S_{0,0} state;
     after the double pass, the diagram's final. That P's outputs land
     exactly there is a bridging lemma, not an assumption.
   - DSGo and k-DSGo finality, per his ruling: the printed convention
     ("s final exactly when some branch of ρ(s) is final") is amended
     by adding "a double pass is final". On reachable states the
     amended convention collapses to "the last turn was a double
     pass": a final branch arises only on a double-pass turn, and no
     state survives past one. The ρ = ∅ corner is thereby repaired
     (the state is final; final_nomove licenses the refusal;
     pass_available is vacuous). def_faithful's finality clause fails
     at a double-passed ρ = ∅ state — harmlessly: that state already
     fails the nonemptiness clause and lies outside every within-k
     state of the radius claims.
   - The radius claims are stated in explicit form: SGo faithful
     within 0 and (side ≥ 3, the printed witnesses' scope; side 2 is
     the printed exhaustion) not within 1; k-DSGo within k, not within
     k+1; DSGo within every d. The spectrum sentence is the existence
     corollary over these. -/
import SgoGames

open SgoGo SgoDisplay SgoSerial SgoDelta

namespace SgoGames

/-- The move alphabet of the family: pass, or a colored intersection. -/
def goMv : Moves where
  M := Option (Bool × Nat)
  deg0 := fun m => m = none ∨ ∃ i, m = some (false, i)
  deg1 := fun m => m = none ∨ ∃ i, m = some (true, i)
  pass := none
  pass_deg0 := Or.inl rfl
  pass_deg1 := Or.inl rfl
  pass_unique := by
    intro m h0 h1
    rcases h0 with h | ⟨i, hi⟩
    · exact h
    · rcases h1 with h | ⟨j, hj⟩
      · exact h
      · subst hi; cases hj

/-- The core action of Go's real moves: bounds-guarded goMoveN by the
    move's color. The pass is handled by the general evolution. -/
def goMvAct (n : Nat) (d : Display n) : goMv.M → Option (Display n)
  | none => none
  | some (w, i) =>
    if i < n*n then goMoveN n d (if w then .w else .b) i else none

/-- Go, presented by its core (option C): cores are diagrams, no
    ended-by-play positions (suicide legal, no Ko; the game ends only
    at pass grading 1 + pass). States are PState (Display n): the
    bigraded live states and the finals, by the general definition. -/
def goGame (n : Nat) : SeqGame goMv where
  C := Display n
  mv := goMvAct n
  q0 := emptyD n
  ended := fun _ => False

/-- Slot the two moves of a turn by grading: Black's component and
    White's, rejecting same-colored pairs; passes fill either slot. -/
def slotMoves : goMv.M → goMv.M → Option (Option Nat × Option Nat)
  | none, none => some (none, none)
  | none, some (w, i) =>
    some (if w then (none, some i) else (some i, none))
  | some (w, i), none =>
    some (if w then (none, some i) else (some i, none))
  | some (w0, i0), some (w1, i1) =>
    if w0 == w1 then none
    else if w0 then some (some i1, some i0) else some (some i0, some i1)

/-- SGo as a simultaneous game: availability is display-read, the pair
    map slots by grading (order insensitivity by construction). -/
def sgoGame (n : Nat) : SimulGame goMv where
  B := SGoState n
  avail := fun s m => s.final = false ∧
    (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧ occD s.disp i = false)
  pairE := fun s ma mb =>
    (slotMoves ma mb).bind fun (m0, m1) => sgoEv n s m0 m1
  q0 := initSGo n
  final := fun s => s.final = true

/-- The branch semantics of SGo: the entanglement's diagrams as
    position normal forms — the S_{0,0} state of each diagram; after
    the double pass, the final of the diagram. -/
def rhoSGo (n : Nat) (s : SGoState n) : BSet (goGame n).S :=
  fun a => ∃ d, d ∈ s.ent ∧
    a = if s.final then PState.done d false else PState.live d false false

/-- DSGo as a simultaneous game (same state data, Δ∘Pl evolution). -/
def dsgoGame (n : Nat) : SimulGame goMv where
  B := SGoState n
  avail := fun s m => s.final = false ∧
    (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧ occD s.disp i = false)
  pairE := fun s ma mb =>
    (slotMoves ma mb).bind fun (m0, m1) => dsgoEv n s m0 m1
  q0 := initSGo n
  -- The amended convention (his ruling): some branch of ρ(s) is
  -- final, OR the turn just played was a double pass. In this
  -- representation the first disjunct is (flag ∧ ent ≠ []), so the
  -- disjunction collapses to the flag. For DSGo the postprocessing
  -- provably loses no branch, and the two conventions agree anyway.
  final := fun s => s.final = true

def rhoD (n : Nat) (s : SGoState n) : BSet (goGame n).S :=
  fun a => ∃ d, d ∈ s.ent ∧
    a = if s.final then PState.done d false else PState.live d false false

/-- k-DSGo as a simultaneous game. -/
def kGame (n k : Nat) : SimulGame goMv where
  B := KState n
  avail := fun s m => s.final = false ∧
    (m = none ∨ ∃ w i, m = some (w, i) ∧ i < n*n ∧ occD s.disp i = false)
  pairE := fun s ma mb =>
    (slotMoves ma mb).bind fun (m0, m1) => kEv n s m0 m1
  q0 := initK n k
  -- The amended convention (his ruling): some branch of ρ(s) is
  -- final, OR the turn just played was a double pass — collapsing to
  -- the flag as for DSGo. This is what repairs the ρ = ∅ corner: the
  -- double-passed empty-entanglement state is now final, so
  -- final_nomove licenses the refusal of every move and
  -- pass_available is vacuous there.
  final := fun s => s.final = true

def rhoK (n : Nat) (s : KState n) : BSet (goGame n).S :=
  fun a => ∃ d, d ∈ s.ent ∧
    a = if s.final then PState.done d false else PState.live d false false

/-- The ambient obligation on classical Go: the symmetry operators.
    (The printed def_sequential's properties hold by construction of
    the core presentation — no longer separate obligations.) -/
def GoOK (n : Nat) : Prop := SeqSym (goGame n)

/-- State equivalence for the SGo/DSGo state type: same display, turn,
    and finality, with the entanglement equal AS A SET — the paper's
    B(Sim G) is a finite set of branches (def_symmetric, lem_symmetric
    push the swap through a union), so states are compared set-wise. -/
def sgoEqv (n : Nat) (s t : SGoState n) : Prop :=
  s.disp = t.disp ∧ s.next = t.next ∧ s.final = t.final
    ∧ (∀ b, b ∈ s.ent ↔ b ∈ t.ent)

/-- State equivalence for k-DSGo: also the verdict queue (an ordered
    list, compared exactly — the swap operator carries its own verdict
    swap), entanglement set-wise. -/
def kEqv (n : Nat) (s t : KState n) : Prop :=
  s.disp = t.disp ∧ s.next = t.next ∧ s.final = t.final
    ∧ s.verdicts = t.verdicts ∧ (∀ b, b ∈ s.ent ↔ b ∈ t.ent)

/-- The main theorem, the SGo clause: a simple simultaneization of Go with
    faithfulness radius zero. The not-within-one half is stated for
    side ≥ 3, the printed witnesses' scope; side 2 is the printed
    exhaustion and is carried separately. -/
def Thm52_SGo (n : Nat) : Prop :=
  SimOK (sgoGame n) ∧ SimSym (sgoGame n) (sgoEqv n) ∧
  IsSimultaneization (goGame n) (sgoGame n) (rhoSGo n) ∧
  IsSimple (goGame n) (sgoGame n) ∧
  FaithfulWithin (goGame n) (sgoGame n) (rhoSGo n) 0 ∧
  (3 ≤ n → ¬FaithfulWithin (goGame n) (sgoGame n) (rhoSGo n) 1)

/-- The main theorem, the DSGo clause: a simple simultaneization of Go,
    faithful within every distance. -/
def Thm52_DSGo (n : Nat) : Prop :=
  SimOK (dsgoGame n) ∧ SimSym (dsgoGame n) (sgoEqv n) ∧
  IsSimultaneization (goGame n) (dsgoGame n) (rhoD n) ∧
  IsSimple (goGame n) (dsgoGame n) ∧
  ∀ d, FaithfulWithin (goGame n) (dsgoGame n) (rhoD n) d

/-- The main theorem, the k-DSGo clause: a simple simultaneization of Go
    with faithfulness radius exactly k. -/
def Thm52_kDSGo (n k : Nat) : Prop :=
  SimOK (kGame n k) ∧ SimSym (kGame n k) (kEqv n) ∧
  IsSimultaneization (goGame n) (kGame n k) (rhoK n) ∧
  IsSimple (goGame n) (kGame n k) ∧
  FaithfulWithin (goGame n) (kGame n k) (rhoK n) k ∧
  -- Lower bound scoped to side ≥ 5 (his ruling; the experiments' range):
  -- the aging pocket construction needs the far column. Sides 3 and 4
  -- are verified for bounded/unbounded k by tools/witness_repair.py
  -- but are not part of the formal claim.
  (5 ≤ n → ¬FaithfulWithin (goGame n) (kGame n k) (rhoK n) (k+1))

/-- The main theorem, in full, at board side n ≥ 2. -/
def Thm52 (n : Nat) : Prop :=
  GoOK n ∧ Thm52_SGo n ∧ Thm52_DSGo n ∧ ∀ k, 1 ≤ k → Thm52_kDSGo n k

/-- An equivalence relation on a game's states (the branch-equivalence
    a symmetric simultaneization is compared up to). -/
def IsEquivB {Mv : Moves} (G : SimulGame Mv) (rel : G.B → G.B → Prop) : Prop :=
  (∀ a, rel a a) ∧ (∀ a b, rel a b → rel b a) ∧
  (∀ a b c, rel a b → rel b c → rel a c)

/-- The spectrum corollary: every element of ℕ ⊔ {∞} is realized by a
    simple simultaneization of Go — radius exactly k for every k, and
    a faithful-at-every-distance one. -/
def SpectrumFull (n : Nat) : Prop :=
  (∀ k : Nat, ∃ G1 : SimulGame goMv, ∃ ρ : G1.B → BSet (goGame n).S,
    ∃ rel : G1.B → G1.B → Prop, IsEquivB G1 rel ∧
    SimOK G1 ∧ SimSym G1 rel ∧
    IsSimultaneization (goGame n) G1 ρ ∧ IsSimple (goGame n) G1 ∧
    FaithfulWithin (goGame n) G1 ρ k ∧
    ¬FaithfulWithin (goGame n) G1 ρ (k+1)) ∧
  (∃ G1 : SimulGame goMv, ∃ ρ : G1.B → BSet (goGame n).S,
    ∃ rel : G1.B → G1.B → Prop, IsEquivB G1 rel ∧
    SimOK G1 ∧ SimSym G1 rel ∧
    IsSimultaneization (goGame n) G1 ρ ∧ IsSimple (goGame n) G1 ∧
    ∀ d, FaithfulWithin (goGame n) G1 ρ d)

end SgoGames
