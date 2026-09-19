/- SgoGo.lean — milestone 1, classical layer.
   Formalizes the paper's stipulations I/O spec of one classical move
   (placed diagram; go_captures, go_suicide, go_closure), scoped to
   lem_onestage. Mirrors sgo_engine.py's go_play for differential testing.
   Lean 4.15.0 core only, no dependencies. -/

namespace SgoGo

inductive Color where
  | black
  | white
deriving DecidableEq, Repr, BEq

def Color.opp : Color → Color
  | .black => .white
  | .white => .black

/-- Board positions on an n×n board. -/
abbrev Pos (n : Nat) := Fin n × Fin n

/-- Classical diagram: a stone pattern (the paper's diagrams, no stamps). -/
abbrev CDiag (n : Nat) := Pos n → Option Color

def allFin (n : Nat) : List (Fin n) :=
  (List.range n).filterMap fun i => if h : i < n then some ⟨i, h⟩ else none

def allPos (n : Nat) : List (Pos n) :=
  (allFin n).flatMap fun x => (allFin n).map fun y => (x, y)

/-- Orthogonal adjacency of intersections. -/
def adj {n : Nat} (p q : Pos n) : Bool :=
  (p.1 == q.1 && (p.2.val + 1 == q.2.val || q.2.val + 1 == p.2.val)) ||
  (p.2 == q.2 && (p.1.val + 1 == q.1.val || q.1.val + 1 == p.1.val))

/-- The same-color component through p (empty list if p is empty).
    Fuel-bounded closure; fuel n*n suffices. -/
def componentAux (n : Nat) (d : CDiag n) (c : Color) :
    Nat → List (Pos n) → List (Pos n) → List (Pos n)
  | 0, comp, _ => comp
  | fuel+1, comp, frontier =>
    let next := (allPos n).filter fun q =>
      d q == some c && !comp.contains q && frontier.any fun r => adj q r
    match next with
    | [] => comp
    | _ => componentAux n d c fuel (comp ++ next) next

def component {n : Nat} (d : CDiag n) (p : Pos n) : List (Pos n) :=
  match d p with
  | none => []
  | some c => componentAux n d c (n*n) [p] [p]

/-- "Has no liberties": no empty intersection adjacent to the set. -/
def noLib {n : Nat} (d : CDiag n) (comp : List (Pos n)) : Bool :=
  (allPos n).all fun q => !(d q == none && comp.any fun r => adj q r)

/-- A non pass move. -/
structure Move (n : Nat) where
  color : Color
  pos : Pos n
deriving DecidableEq, Repr, BEq

/-- The placed diagram B + m. -/
def placed {n : Nat} (d : CDiag n) (m : Move n) : CDiag n :=
  fun p => if p == m.pos then some m.color else d p

/-- go_captures: stones of the opposite colored components of B + m
    with no liberties in it. -/
def capturedStones {n : Nat} (d : CDiag n) (m : Move n) : List (Pos n) :=
  let pd := placed d m
  (allPos n).filter fun p =>
    pd p == some m.color.opp && noLib pd (component pd p)

def afterCaptures {n : Nat} (d : CDiag n) (m : Move n) : CDiag n :=
  fun p => if (capturedStones d m).contains p then none else placed d m p

/-- go_suicide: the placed stone's component, read with the captured
    components emptied. -/
def suicided {n : Nat} (d : CDiag n) (m : Move n) : Bool :=
  let ac := afterCaptures d m
  noLib ac (component ac m.pos)

/-- go_closure: the diagram of b # m. none = the move is unavailable
    (placement intersection occupied). -/
def goMove {n : Nat} (d : CDiag n) (m : Move n) : Option (CDiag n) :=
  if (d m.pos).isSome then none else
  let ac := afterCaptures d m
  if suicided d m then
    some (fun p => if (component ac m.pos).contains p then none else ac p)
  else
    some ac

/-- Diagram equality, computed. -/
def cdEq {n : Nat} (d e : CDiag n) : Bool :=
  (allPos n).all fun p => d p == e p

/- ### Test-vector plumbing (3×3): boards as 9-character strings,
   row-major x*3+y; '.', 'b', 'w'. -/

def decode3 (s : String) : CDiag 3 := fun p =>
  match s.toList[p.1.val * 3 + p.2.val]? with
  | some 'b' => some Color.black
  | some 'w' => some Color.white
  | _ => none

def encCell : Option Color → Char
  | none => '.'
  | some .black => 'b'
  | some .white => 'w'

def encode3 (d : CDiag 3) : String :=
  String.mk ((allPos 3).map fun p => encCell (d p))

def mkPos3 (x y : Nat) : Pos 3 :=
  (⟨x % 3, Nat.mod_lt x (by decide)⟩, ⟨y % 3, Nat.mod_lt y (by decide)⟩)

/-- One test case: board, move color ('b'/'w'), x, y, expected
    ("U" for unavailable, else the 9-char result). -/
def runCase : String × Char × Nat × Nat × String → Bool
  | (s, c, x, y, expect) =>
    let d := decode3 s
    let col := if c == 'b' then Color.black else Color.white
    match goMove d ⟨col, mkPos3 x y⟩ with
    | none => expect == "U"
    | some r => encode3 r == expect

end SgoGo
