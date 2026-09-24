/- SgoDelta.lean — the main theorem, milestone 1 continued: the decoherent
   family, executable, general board side n.

   Against the print (sgo.tex, "The decoherent variant DSGo"):
   - deltaRound/recut/delta: the postprocessing Δ(s, 𝔐), anchored at
     the current turn t. Round j removes the display stones at
     intersections with ev(𝔐_j) = ∅ and recolors a q-stone CREATED ON
     THIS TURN (stamp = t) with ev(𝔐_j) = {c} to c; then the re-cut
     keeps the branches occupying only display-occupied intersections.
     The recursion stops at the first unchanged display, and the LAST
     re-cut is part of the result (the k-DSGo witness turns on this).
   - dsgoEv: E_DSGo(s, m0, m1) = Δ(Pl(s, m0, m1), P(ρ(s), m0, m1)).
     Pl is the SGo placement (placeJoint) with NO objective reduction.
     Availability is display-read, as in SGo. A double pass turn still
     postprocesses (the formula applies), and ends the game.
   - orOp/Verdict/verOf/execV/kEv: the delayed game k-DSGo. The
     objective reduction OR anchored at turn t is the stage recursion
     (stages, SgoDisplay). The verdict ver(D) is the difference: the
     stones of D removed in OR(D), and the q-stones of D made definite
     in OR(D) with their acquired colors, each named by (intersection,
     time stamp). Execution v·D' removes and recolors the stones of D'
     that v names; a named stone no longer standing (empty, or a
     different stamp there) is ignored. E_k executes the oldest
     verdict, plays the turn as a DSGo turn, and stores ver(D').

   Finality caveat, for the statement audit: the paper formalizes
   final states of the family as "some branch of ρ(s) is final", and a
   branch is final exactly when it arose from a double pass. The flag
   here records "the last turn was a double pass", which agrees except
   at a double-pass turn whose re-cut empties the entanglement — there
   the paper's ρ(s) has no branch at all, a state def_faithful already
   excludes by its nonemptiness clause. -/
import SgoSerial

open SgoGo SgoDisplay SgoSerial

namespace SgoDelta

/-- ev over a branch set at i: (some branch has black, some has white). -/
def evSet (n : Nat) (M : List (Display n)) (i : Nat) : Bool × Bool :=
  (M.any fun b => kindAt b i == some .b,
   M.any fun b => kindAt b i == some .w)

/-- One postprocessing round on the display: removals at ev = ∅, and
    the this-turn q-stones at one-color ev made definite. -/
def deltaRound (n t : Nat) (M : List (Display n)) (D : Display n) :
    Display n :=
  ⟨(Array.range (n*n)).map fun i =>
    match D.get i with
    | none => none
    | some (k, st) =>
      let (hb, hw) := evSet n M i
      if !hb && !hw then none
      else if k == .r && st == t then
        if hb && !hw then some (.b, st)
        else if hw && !hb then some (.w, st)
        else some (k, st)
      else some (k, st)⟩

/-- The re-cut: keep the branches whose stones all stand on occupied
    display intersections. -/
def recut (n : Nat) (D : Display n) (M : List (Display n)) :
    List (Display n) :=
  M.filter fun b => (allIdx n).all fun i => occD D i || kindAt b i == none

/-- Δ recursion: stop at the first unchanged display; the last re-cut
    is part of the result. -/
def deltaAux (n t : Nat) :
    Nat → Display n → List (Display n) → Display n × List (Display n)
  | 0, D, M => (D, M)
  | fuel+1, D, M =>
    let D' := deltaRound n t M D
    let M' := recut n D' M
    if D' == D then (D', M') else deltaAux n t fuel D' M'

def delta (n t : Nat) (D : Display n) (M : List (Display n)) :
    Display n × List (Display n) :=
  deltaAux n t (2*(n*n) + 2) D M

/-- E_DSGo: the postprocessed placement. A DSGo state carries the same
    data as an SGo state. -/
def dsgoEv (n : Nat) (s : SGoState n) (m0 m1 : Option Nat) :
    Option (SGoState n) :=
  if s.final then none else
  if !(availD n s.disp m0 && availD n s.disp m1) then none else
  match simEv n s.ent m0 m1 with
  | none => none
  | some dec =>
    let Dp := placeJoint s.disp s.next m0 m1
    let (D', M') := delta n s.next Dp dec
    some ⟨D', s.next + 1, M', m0.isNone && m1.isNone⟩

/-- The objective reduction anchored at turn t: the stage recursion
    with no placement. -/
def orOp (n t : Nat) (D : Display n) : Display n := stages (t+1) D t

/-- A verdict: removals and definite-makings, stones named by
    (intersection, time stamp). -/
structure Verdict where
  removals : List (Nat × Nat)
  recolors : List (Nat × Nat × DKind)
deriving BEq, Repr

def emptyV : Verdict := ⟨[], []⟩

/-- ver(D) at turn t: the difference between D and OR(D). -/
def verOf (n t : Nat) (D : Display n) : Verdict :=
  let R := orOp n t D
  ⟨(allIdx n).filterMap fun i =>
      match D.get i with
      | some (_, st) => if occD R i then none else some (i, st)
      | none => none,
   (allIdx n).filterMap fun i =>
      match D.get i, R.get i with
      | some (.r, st), some (k, _) =>
        if k != DKind.r then some (i, st, k) else none
      | _, _ => none⟩

/-- Verdict execution v · D: named stones removed and recolored; a
    named stone no longer standing is ignored. -/
def execV (n : Nat) (v : Verdict) (D : Display n) : Display n :=
  let D1 := v.removals.foldl (fun (A : Display n) pr =>
    let (i, st) := pr
    match A.get i with
    | some (_, st') => if st' == st then A.set i none else A
    | none => A) D
  v.recolors.foldl (fun (A : Display n) pr =>
    let (i, st, c) := pr
    match A.get i with
    | some (_, st') => if st' == st then A.set i (some (c, st')) else A
    | none => A) D1

/-- A k-DSGo state: display, next turn, entanglement, the verdicts of
    the last k turns (oldest first), finality. -/
structure KState (n : Nat) where
  disp     : Display n
  next     : Nat
  ent      : List (Display n)
  verdicts : List Verdict
  final    : Bool
deriving BEq, Repr

def initK (n k : Nat) : KState n :=
  ⟨emptyD n, 1, [emptyD n], List.replicate k emptyV, false⟩

/-- E_k: execute the oldest verdict, play the turn as a DSGo turn on
    the executed display, store the new verdict. Moves and finality
    are those of DSGo, read from the stored display. -/
def kEv (n : Nat) (s : KState n) (m0 m1 : Option Nat) :
    Option (KState n) :=
  if s.final then none else
  if !(availD n s.disp m0 && availD n s.disp m1) then none else
  match s.verdicts with
  | [] => none
  | v1 :: vrest =>
    match simEv n s.ent m0 m1 with
    | none => none
    | some dec =>
      let Dp := placeJoint (execV n v1 s.disp) s.next m0 m1
      let (D', M') := delta n s.next Dp dec
      some ⟨D', s.next + 1, M', vrest ++ [verOf n s.next D'],
            m0.isNone && m1.isNone⟩

end SgoDelta
