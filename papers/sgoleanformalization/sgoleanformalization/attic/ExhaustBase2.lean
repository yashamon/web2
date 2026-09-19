/- ExhaustBase2.lean — milestone 3b: pass-inclusive and multi-stamping
   variants of the 3×3 exhaustive lemma statement. -/
import ExhaustBase
open SgoGo SgoDisplay

/-- Display of the coded state under a stamping (stampOf code i, used
    only at occupied cells; must be < turnN at call sites). -/
def dispOfCodeS (stampOf : Nat → Nat → Nat) (code : Nat) : Display 3 :=
  ⟨(Array.range 9).map fun i =>
    match (code / 3 ^ i) % 3 with
    | 1 => some (DKind.b, stampOf code i)
    | 2 => some (DKind.w, stampOf code i)
    | _ => none⟩

/-- The lemma check for one placed pair (already known commuting), at
    turn tN, display D: resolution = Cap_tN alone, cells = composite. -/
def lemAt (tN : Nat) (D : Display 3) (m0 m1 : Option Nat)
    (composite : Display 3) : Bool :=
  let P := placeJoint D tN m0 m1
  let R := stages (tN + 1) P tN
  let Rn := capFix 10 P tN
  R == Rn && cellsOf R == cellsOf composite

/-- Full check at a coded state: all non-pass commuting pairs, all
    single-pass pairs, and the double pass. -/
def checkCodeS (tN : Nat) (stampOf : Nat → Nat → Nat) (code : Nat) : Bool :=
  let d := cstateOfCode code
  if !legalA d then true else
  let D := dispOfCodeS stampOf code
  -- non-pass pairs
  ((List.range 9).all fun i0 =>
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
            lemAt tN D (some i0) (some i1) c1) &&
  -- Black plays, White passes
  ((List.range 9).all fun i0 =>
    if occD d i0 then true else
    match goMoveA d .b i0 with
    | none => true
    | some c => lemAt tN D (some i0) none c) &&
  -- Black passes, White plays
  ((List.range 9).all fun i1 =>
    if occD d i1 then true else
    match goMoveA d .w i1 with
    | none => true
    | some c => lemAt tN D none (some i1) c) &&
  -- double pass
  lemAt tN D none none d

def checkRangeS (tN : Nat) (stampOf : Nat → Nat → Nat)
    (lo width : Nat) : Bool :=
  ((List.range width).map (· + lo)).all (checkCodeS tN stampOf)

/-- Stampings. -/
def stampAll1 : Nat → Nat → Nat := fun _ _ => 1
def stampAll4 : Nat → Nat → Nat := fun _ _ => 4
def stampCycle3 : Nat → Nat → Nat := fun _ i => i % 3 + 1
def stampLcg5 : Nat → Nat → Nat := fun code i => (code * 31 + i * 17) % 5 + 1

/-- Commuting-transition census, pass moves included (single passes are
    defined at every empty intersection and commute; the double pass
    counts once per state). -/
def commutingCountFull : Nat :=
  (List.range 19683).foldl (fun acc code =>
    let d := cstateOfCode code
    if !legalA d then acc else
    let empties := ((List.range 9).filter fun i => !occD d i).length
    let nonpass := (List.range 9).foldl (fun a i0 =>
      if occD d i0 then a else
      a + ((List.range 9).foldl (fun b i1 =>
        if i0 == i1 || occD d i1 then b else
        match goMoveA d .b i0 with
        | none => b
        | some d1 => match goMoveA d1 .w i1 with
          | none => b
          | some c1 => match goMoveA d .w i1 with
            | none => b
            | some d2 => match goMoveA d2 .b i0 with
              | none => b
              | some c2 => if cellsOf c1 == cellsOf c2 then b + 1 else b) 0)) 0
    acc + nonpass + 2 * empties + 1) 0
