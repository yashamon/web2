import ExhaustBase
open SgoDisplay
def legalCount : Nat :=
  ((List.range 19683).filter fun c => legalA (cstateOfCode c)).length
def commutingCount : Nat :=
  ((List.range 19683).foldl (fun acc code =>
    let d := cstateOfCode code
    if !legalA d then acc else
    acc + ((List.range 9).foldl (fun a i0 =>
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
              | some c2 => if cellsOf c1 == cellsOf c2 then b + 1 else b) 0)) 0)) 0)
#eval (legalCount, commutingCount)
