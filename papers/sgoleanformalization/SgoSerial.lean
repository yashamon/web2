/- SgoSerial.lean — the main theorem (thm_simplesymetrization), milestone 1:
   the executable game level, general board side n.

   Contents, against the print:
   - bStep/bStep2: the # operation at grading-0 classical states
     (sgo.tex, Universal simultaneization). At the branch level a pass
     class of non final states IS a bare diagram: a pass changes
     nothing but the grading, and the grading normalization picks the
     grading-0 member. Stamps ride along as 0 and are never read at
     the branch level.
   - serialP: the serialization map P, the four priority cases
     verbatim; none = the pseudo pass move.
   - simEv: the universal simultaneization evolution
     (def_formalsimultanezation, items 4-5): the union of the branch
     P's, deduplicated; undefined when some branch's P is.
   - compatibleB, sgoEv: the SGo game evolution (thm_simultanezation +
     sec_entanglement): the display resolves by placement + objective
     reduction (resolveTurn, SgoDisplay), each branch evolves by P,
     and the branches incompatible with the resolved display are
     discarded. Availability is display-read: a non pass move needs
     its placement intersection empty on the display. Finality
     (prop_doublepass): a double pass ends the game, tracked as a
     flag, the display and the branch diagrams unchanged.

   Caveat, for the statement audit: sgoEv returns none if some
   branch's P is undefined, although the paper defines availability by
   the display alone. On states satisfying the entanglement invariant
   (every branch compatible with the display) the two agree: a display
   empty intersection is empty in every branch — the definedness
   direction of prop_naturality0. The invariant is differential-tested
   now and will be proved in the general milestone. -/
import SgoLemma

open SgoGo SgoDisplay

namespace SgoSerial

/-- The empty display. -/
def emptyD (n : Nat) : Display n := ⟨Array.mkArray (n*n) none⟩

/-- One # step at a grading-0 branch: none is the pseudo pass, which
    changes nothing at the diagram level. -/
def bStep (n : Nat) (d : Display n) (c : DKind) : Option Nat → Option (Display n)
  | none => some d
  | some i => goMoveN n d c i

/-- Two # steps: the c0 move, then the c1 move. -/
def bStep2 (n : Nat) (d : Display n) (c0 c1 : DKind)
    (x0 x1 : Option Nat) : Option (Display n) :=
  (bStep n d c0 x0).bind fun d1 => bStep n d1 c1 x1

/-- One copy of each branch (BEq on the cell arrays). -/
def dedupD (n : Nat) : List (Display n) → List (Display n)
  | [] => []
  | x :: xs =>
    let r := dedupD n xs
    if r.contains x then r else x :: r

/-- The serialization map P: the four priority cases, in order; m0 is
    Black's move, m1 White's; none result = undefined. -/
def serialP (n : Nat) (a : Display n) (m0 m1 : Option Nat) :
    Option (List (Display n)) :=
  -- a # m0 # m1  vs  a # m1 # m0 (no let bindings: proofs iota-reduce)
  match bStep2 n a .b .w m0 m1, bStep2 n a .w .b m1 m0 with
  | some x, some y => some (dedupD n [x, y])
  | some x, none   =>
    match bStep n a .w m1 with             -- a # m1
    | some y => some (dedupD n [x, y])
    | none   => none
  | none, some y   =>
    match bStep n a .b m0 with             -- a # m0
    | some x => some (dedupD n [x, y])
    | none   => none
  | none, none     =>
    match bStep n a .b m0, bStep n a .w m1 with
    | some x, some y => some (dedupD n [x, y])
    | _, _ => none

/-- E_{Sim(Go)} on a finite branch set: the union of the P's,
    undefined if some P is. (Structural recursion — no List.mapM — so
    the invariant proofs can induct plainly.) -/
def simEvAux (n : Nat) (m0 m1 : Option Nat) :
    List (Display n) → Option (List (Display n))
  | [] => some []
  | b :: bs =>
    match serialP n b m0 m1, simEvAux n m0 m1 bs with
    | some l, some r => some (l ++ r)
    | _, _ => none

def simEv (n : Nat) (bs : List (Display n)) (m0 m1 : Option Nat) :
    Option (List (Display n)) :=
  (simEvAux n m0 m1 bs).map (dedupD n)

/-- Compatibility of a branch with a display: every stone of the
    branch stands on an occupied display intersection and matches the
    displayed color there, a q-stone matching either. -/
def compatibleB (n : Nat) (D b : Display n) : Bool :=
  (allIdx n).all fun i =>
    match kindAt b i with
    | none => true
    | some k =>
      match kindAt D i with
      | none => false
      | some .r => true
      | some k' => k == k'

/-- An SGo game state: the display, the number of the next turn, the
    entanglement, and finality (double pass). -/
structure SGoState (n : Nat) where
  disp  : Display n
  next  : Nat
  ent   : List (Display n)
  final : Bool
deriving BEq, Repr

/-- The initial state: empty display, entanglement the singleton of
    the empty classical state, next turn 1. -/
def initSGo (n : Nat) : SGoState n :=
  ⟨emptyD n, 1, [emptyD n], false⟩

/-- Availability on the display: in-bounds and empty; passes always. -/
def availD (n : Nat) (D : Display n) : Option Nat → Bool
  | none => true
  | some i => decide (i < n*n) && !occD D i

/-- E_SGo, one joint turn m0/m1. -/
def sgoEv (n : Nat) (s : SGoState n) (m0 m1 : Option Nat) :
    Option (SGoState n) :=
  if s.final then none else
  if !(availD n s.disp m0 && availD n s.disp m1) then none else
  match m0, m1 with
  | none, none => some { s with next := s.next + 1, final := true }
  | _, _ =>
    let D' := resolveTurn s.disp s.next m0 m1
    match simEv n s.ent m0 m1 with
    | none => none
    | some bs => some ⟨D', s.next + 1, bs.filter (compatibleB n D'), false⟩

end SgoSerial
