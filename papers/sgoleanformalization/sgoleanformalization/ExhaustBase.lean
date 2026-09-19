/- ExhaustBase.lean — milestone 3: the lemma's 3×3 exhaustive statement,
   inside Lean. For every legal classical 3×3 state and every commuting
   non-pass joint move (stamping: all state stones 1, turn n = 2):
   the resolution equals Cap_n alone on the placed display, and its
   stone pattern equals the classical composite's diagram.
   Array representation throughout. -/
import SgoDisplay
open SgoGo SgoDisplay

/-- Classical move on the array representation (kinds b/w, stamps unused):
    the spec's three clauses. none = placement intersection occupied. -/
def goMoveA (d : Display 3) (c : DKind) (i : Nat) : Option (Display 3) :=
  if occD d i then none else
  let pd := d.set i (some (c, 0))
  let deadOpp := (allIdx 3).filter fun p =>
    kindAt pd p == some c.opp && noLibD pd (componentD pd p)
  let ac : Display 3 := ⟨(Array.range 9).map fun p =>
    if deadOpp.contains p then none else pd.get p⟩
  let own := componentD ac i
  some (if noLibD ac own then
    ⟨(Array.range 9).map fun p => if own.contains p then none else ac.get p⟩
  else ac)

/-- Classical state from a base-3 code, as an array display (stamps 0). -/
def cstateOfCode (code : Nat) : Display 3 :=
  ⟨(Array.range 9).map fun i =>
    match (code / 3 ^ i) % 3 with
    | 1 => some (DKind.b, 0)
    | 2 => some (DKind.w, 0)
    | _ => none⟩

/-- The same state as the lemma's display: every stone stamped 1. -/
def dispOfCode (code : Nat) : Display 3 :=
  ⟨(Array.range 9).map fun i =>
    match (code / 3 ^ i) % 3 with
    | 1 => some (DKind.b, 1)
    | 2 => some (DKind.w, 1)
    | _ => none⟩

/-- Legality: every component has a liberty. -/
def legalA (d : Display 3) : Bool :=
  (allIdx 3).all fun p =>
    !occD d p || !noLibD d (componentD d p)

def cellsOf (D : Display 3) : String := (encodeD3 D).1

/-- The lemma's claim at one legal state, all ordered placement pairs
    (Black i0, White i1), commuting ones checked. -/
def checkCode (code : Nat) : Bool :=
  let d := cstateOfCode code
  if !legalA d then true else
  (List.range 9).all fun i0 =>
    if occD d i0 then true else
    (List.range 9).all fun i1 =>
    if i0 == i1 || occD d i1 then true else
    match goMoveA d .b i0 with
    | none => true
    | some d1 =>
      match goMoveA d1 .w i1 with
      | none => true
      | some c1 =>
        match goMoveA d .w i1 with
        | none => true
        | some d2 =>
          match goMoveA d2 .b i0 with
          | none => true
          | some c2 =>
            if cellsOf c1 != cellsOf c2 then true else
            let D := dispOfCode code
            let P := placeJoint D 2 (some i0) (some i1)
            let R := stages 3 P 2
            let Rn := capFix 10 P 2
            R == Rn && cellsOf R == cellsOf c1

def checkRange (lo width : Nat) : Bool :=
  ((List.range width).map (· + lo)).all checkCode
