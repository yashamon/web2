/- SgoLemma.lean — the general classical move (goMoveN, factored
   through named stages) and the lemma's hypothesis predicates. The
   step theorems live downstream (Infra*/Step*.lean) and the general
   lemma itself is lem_onestage_final in Step8.lean. Board side n,
   turn t, all general; the whole development is sorry-free. -/
import SgoDisplay
open SgoGo SgoDisplay

/-- Classical move, general n, factored through named stages
    (the spec's three clauses on arrays). -/
def placedN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : Display n :=
  d.set i (some (c, 0))

def deadOppN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : List Nat :=
  (allIdx n).filter fun p =>
    kindAt (placedN n d c i) p == some c.opp &&
    noLibD (placedN n d c i) (componentD (placedN n d c i) p)

def afterCapN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : Display n :=
  ⟨(Array.range (n*n)).map fun p =>
    if (deadOppN n d c i).contains p then none else (placedN n d c i).get p⟩

def ownCompN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : List Nat :=
  componentD (afterCapN n d c i) i

def suicideN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : Bool :=
  noLibD (afterCapN n d c i) (ownCompN n d c i)

def erasedN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : Display n :=
  ⟨(Array.range (n*n)).map fun p =>
    if (ownCompN n d c i).contains p then none else (afterCapN n d c i).get p⟩

def goMoveN (n : Nat) (d : Display n) (c : DKind) (i : Nat) : Option (Display n) :=
  if occD d i then none else
  some (if suicideN n d c i then erasedN n d c i else afterCapN n d c i)

section General
variable {n : Nat}

/-- The display carries no q-stone. -/
def IsClassical (A : Display n) : Prop :=
  ∀ i, kindAt A i ≠ some .r

/-- Legality: every component has a liberty. -/
def IsLegal (A : Display n) : Prop :=
  ∀ i, occD A i = true → noLibD A (componentD A i) = false

/-- Equal stone patterns (the diagram equality; stamps not compared). -/
def SameCells (D E : Display n) : Prop :=
  ∀ i, kindAt D i = kindAt E i

/-- All stamps below t. -/
def StampsBelow (D : Display n) (t : Nat) : Prop :=
  ∀ i, stampAt D i < t

/-- Well-formed representation: the cell array has board size. (The
    paper's displays are functions on the board; this pins the array
    encoding to it.) -/
def WFD (D : Display n) : Prop :=
  D.cells.size = n*n

/- Step 0 (companion) — the same-intersection distinctness — is stated
   and proved in Step0.lean: it consumes the structural (Infra2) and
   component/liberty (Infra3/4) layers. -/

/- The block lemmas (persist-empty across the second move) are stated
   and proved in Infra2.lean — they consume the goMoveN structural
   lemmas proved there. -/

/- Step 1 (removal dichotomy) is stated and proved in Step1.lean. -/

/- Steps 6-7 and 8 are proved in Step6.lean / Step7.lean / Step8.lean;
   the general lemma itself is lem_onestage_final in Step8.lean. -/

end General
