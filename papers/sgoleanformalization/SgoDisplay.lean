/- SgoDisplay.lean — milestone 2, the display layer, scoped to lem_onestage.
   Transcribes the printed §2 display calculus: displays with stamps,
   def_trapped (NDJ, turn-n via largest stamp), def_captured (conditions
   1, 2 = cond_unambiguous0, 3a, 3b with the component-freshness clause),
   the basic capture reduction, Cap_n as its fixpoint, and the stage
   recursion of the resolution (stop when a stage removes no stones).
   Representation: materialized arrays (index = x*n + y), so rounds do
   not stack closures. Differentially tested against sgo_engine. -/
import SgoGo

namespace SgoDisplay
open SgoGo

inductive DKind where
  | b | w | r
deriving DecidableEq, Repr, BEq

def DKind.opp : DKind → DKind
  | .b => .w
  | .w => .b
  | .r => .r

abbrev Cell := Option (DKind × Nat)

/-- A display on an n×n board: n*n cells, index i = x*n + y. -/
structure Display (n : Nat) where
  cells : Array Cell
deriving BEq, Repr

def allIdx (n : Nat) : List Nat := List.range (n*n)

def Display.get {n : Nat} (D : Display n) (i : Nat) : Cell :=
  D.cells.getD i none

def Display.set {n : Nat} (D : Display n) (i : Nat) (c : Cell) : Display n :=
  ⟨D.cells.setD i c⟩

def kindAt {n} (D : Display n) (i : Nat) : Option DKind := (D.get i).map (·.1)
def stampAt {n} (D : Display n) (i : Nat) : Nat := ((D.get i).map (·.2)).getD 0
def occD {n} (D : Display n) (i : Nat) : Bool := (D.get i).isSome

/-- Orthogonal adjacency of indices. -/
def adjI (n i j : Nat) : Bool :=
  let (xi, yi) := (i / n, i % n)
  let (xj, yj) := (j / n, j % n)
  (xi == xj && (yi + 1 == yj || yj + 1 == yi)) ||
  (yi == yj && (xi + 1 == xj || xj + 1 == xi))

/-- Component of kind k through i (BFS, fuel n*n). -/
def componentKAux (n : Nat) (D : Display n) (k : DKind) :
    Nat → List Nat → List Nat → List Nat
  | 0, comp, _ => comp
  | fuel+1, comp, frontier =>
    let next := (allIdx n).filter fun q =>
      kindAt D q == some k && !comp.contains q && frontier.any fun r => adjI n q r
    match next with
    | [] => comp
    | _ => componentKAux n D k fuel (comp ++ next) next

def componentD {n : Nat} (D : Display n) (i : Nat) : List Nat :=
  match kindAt D i with
  | none => []
  | some k => componentKAux n D k (n*n) [i] [i]

/-- "Has no liberties" on a display. -/
def noLibD {n : Nat} (D : Display n) (comp : List Nat) : Bool :=
  (allIdx n).all fun q => !(!occD D q && comp.any fun r => adjI n q r)

/-- def_trapped: trapped on turn t — trapped, and t is the largest stamp
    among the component's stones and the stones adjacent to it. -/
def trappedOnTurn {n : Nat} (D : Display n) (comp : List Nat) (t : Nat) : Bool :=
  noLibD D comp &&
  (let nbrStamps := ((allIdx n).filter fun z =>
      occD D z && !comp.contains z && comp.any fun q => adjI n z q).map (stampAt D)
   ((comp.map (stampAt D)) ++ nbrStamps).foldl Nat.max 0 == t)

def replaceKind {n : Nat} (D : Display n) (z : Nat) (k : DKind) : Display n :=
  D.set z ((D.get z).map fun c => (k, c.2))

/-- def_trapped: "trapped by <attacker> on turn t" for the stone at z. -/
def stoneTrappedBy {n : Nat} (D : Display n) (z : Nat) (attacker : DKind) (t : Nat) : Bool :=
  let defender := attacker.opp
  match kindAt D z with
  | some .r =>
    let D2 := replaceKind D z defender
    trappedOnTurn D2 (componentD D2 z) t
  | some k =>
    if k == defender then trappedOnTurn D (componentD D z) t else false
  | none => false

/-- def_captured for the unicolor component comp of kind c. -/
def isCaptured {n : Nat} (D : Display n) (comp : List Nat) (c : DKind) (t : Nat) : Bool :=
  trappedOnTurn D comp t &&
  -- (2) cond_unambiguous0
  (let reds := (allIdx n).filter fun z =>
     kindAt D z == some .r && comp.any fun q => adjI n z q
   reds.all fun r =>
     (allIdx n).all fun z =>
       !(adjI n z r && (kindAt D z == some .b || kindAt D z == some .w) &&
         (let Dc := componentD D z
          !(Dc.all comp.contains && comp.all Dc.contains) &&
          noLibD D Dc && kindAt D z != some c))) &&
  (let adjStones := (allIdx n).filter fun z =>
     occD D z && !comp.contains z && comp.any fun q => adjI n z q
   -- (3a)
   (adjStones.all fun z =>
      !((kindAt D z == some c.opp || kindAt D z == some .r) &&
        stoneTrappedBy D z c t)) ||
   -- (3b) suicidal capture, component-freshness clause
   (comp.all (fun q => stampAt D q != t) &&
    adjStones.all fun z =>
      let Dc := componentD D z
      !(trappedOnTurn D Dc t &&
        !(Dc.any fun q => stampAt D q == t && kindAt D q != some .r))))

/-- One simultaneous round: the basic capture reduction at turn t. -/
def capturedOf {n : Nat} (D : Display n) (t : Nat) (k : DKind) : List Nat :=
  (((allIdx n).foldl (fun (acc : List Nat × List Nat) p =>
      let (seen, caps) := acc
      if kindAt D p == some k && !seen.contains p then
        let comp := componentD D p
        (seen ++ comp, if isCaptured D comp k t then caps ++ comp else caps)
      else acc) ([], []))).2

def basicCap {n : Nat} (D : Display n) (t : Nat) : Display n :=
  let capB := capturedOf D t .b
  let capW := capturedOf D t .w
  let deadAll := capB ++ capW
  ⟨(Array.range (n*n)).map fun p =>
    if deadAll.contains p then none
    else if kindAt D p == some .r && capW.any (fun q => adjI n p q) then
      (D.get p).map fun cell => (DKind.b, cell.2)
    else if kindAt D p == some .r && capB.any (fun q => adjI n p q) then
      (D.get p).map fun cell => (DKind.w, cell.2)
    else D.get p⟩

/-- Cap_t: the fixpoint of the basic reduction. -/
def capFix {n : Nat} : Nat → Display n → Nat → Display n
  | 0, D, _ => D
  | fuel+1, D, t =>
    let D' := basicCap D t
    if D' == D then D else capFix fuel D' t

/-- Joint placement: distinct moves place stones stamped t; a collision
    places a q-stone. none = pass. -/
def placeJoint {n : Nat} (D : Display n) (t : Nat)
    (m0 m1 : Option Nat) : Display n :=
  match m0, m1 with
  | some p0, some p1 =>
    if p0 == p1 then D.set p0 (some (.r, t))
    else (D.set p0 (some (.b, t))).set p1 (some (.w, t))
  | some p0, none => D.set p0 (some (.b, t))
  | none, some p1 => D.set p1 (some (.w, t))
  | none, none => D

/-- The resolution's stage recursion: Cap at descending turns, stopping
    when a stage removes no stones. -/
def stages {n : Nat} : Nat → Display n → Nat → Display n
  | 0, D, _ => D
  | fuel+1, D, t =>
    if t == 0 then D else
    let D' := capFix (n*n+1) D t
    if D' == D then D else stages fuel D' (t - 1)

def resolveTurn {n : Nat} (D : Display n) (t : Nat)
    (m0 m1 : Option Nat) : Display n :=
  stages (t + 1) (placeJoint D t m0 m1) t

/- ### 3×3 vector plumbing: cells string + stamps string (digit, '0' empty). -/

def decodeD3 (cells stamps : String) : Display 3 :=
  ⟨(Array.range 9).map fun i =>
    let s := ((stamps.toList[i]?).getD '0').toNat - '0'.toNat
    match cells.toList[i]? with
    | some 'b' => some (.b, s)
    | some 'w' => some (.w, s)
    | some 'r' => some (.r, s)
    | _ => none⟩

def encCellD : Cell → Char
  | none => '.'
  | some (.b, _) => 'b'
  | some (.w, _) => 'w'
  | some (.r, _) => 'r'

def encStampD : Cell → Char
  | none => '0'
  | some (_, s) => Char.ofNat ('0'.toNat + s % 10)

def encodeD3 (D : Display 3) : String × String :=
  (String.mk ((allIdx 3).map fun i => encCellD (D.get i)),
   String.mk ((allIdx 3).map fun i => encStampD (D.get i)))

def runCaseD : String × String × Nat × Nat × Nat × String × String → Bool
  | (cells, stamps, t, a0, a1, ec, es) =>
    let D := decodeD3 cells stamps
    let dec := fun (a : Nat) => if a ≥ 9 then none else some a
    let R := resolveTurn D t (dec a0) (dec a1)
    encodeD3 R == (ec, es)

end SgoDisplay
