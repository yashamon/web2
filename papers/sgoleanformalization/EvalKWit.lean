import SgoDelta
import SgoKWit
open SgoGo SgoDisplay SgoSerial SgoDelta SgoKWit

def step (nn kk : Nat) (s : KState nn) (mB mW : Option Nat) : KState nn :=
  (kEv nn s mB mW).getD s

def violCells (nn : Nat) (s : KState nn) : List Nat :=
  (List.range (nn*nn)).filter fun i => occD s.disp i && s.ent.all (fun b => !occD b i)

def dumpCells (nn : Nat) (D : Display nn) : List (Nat × DKind × Nat) :=
  (List.range (nn*nn)).filterMap fun i => (D.get i).map (fun c => (i, c.1, c.2))

def setupPlay (nn kk : Nat) : KState nn :=
  let s := initK nn kk
  let s := step nn kk s (some 3) none
  let s := step nn kk s (some nn) none
  let s := step nn kk s none (some (dW1 nn))
  let s := step nn kk s none (some (dW2 nn))
  let s := step nn kk s none (some 0)
  s

def afterColl (nn kk : Nat) : KState nn := step nn kk (setupPlay nn kk) (some 1) (some 1)
def pad (nn kk : Nat) (s : KState nn) : Nat → KState nn
  | 0 => s
  | m+1 => pad nn kk (step nn kk s (some (dP nn)) none) m
def afterPad (nn kk : Nat) : KState nn := pad nn kk (afterColl nn kk) (kk-1)

-- FINALE: black@B3=(1,2)=cell n+2, white@A3=(0,2)=cell 2.
def afterFinal (nn kk : Nat) : KState nn := step nn kk (afterPad nn kk) (some (nn+2)) (some 2)

def report (nn kk : Nat) : String :=
  let sf := afterFinal nn kk
  s!"n={nn} k={kk}: viol={violCells nn sf} final.occ2={occD sf.disp 2} " ++
  s!"ent.len={sf.ent.length} final.disp={reprStr (dumpCells nn sf.disp)} " ++
  s!"branches_occ_at_2={reprStr (sf.ent.map (fun b => occD b 2))}"

#eval s!"pad(5,3) disp={reprStr (dumpCells 5 (afterPad 5 3).disp)}"
#eval s!"pad(5,3) front verdict={reprStr (afterPad 5 3).verdicts.head?}"
#eval report 5 1
#eval report 5 2
#eval report 5 3
#eval report 5 4
#eval report 6 3
#eval report 7 5
#eval report 8 8

-- Detailed dump of the finale branches at n=5,k=3:
#eval s!"FINAL(5,3) branches full: {reprStr ((afterFinal 5 3).ent.map (dumpCells 5))}"
#eval s!"FINAL(5,3) verdict executed was front of pad: {reprStr (afterPad 5 3).verdicts.head?}"
#eval s!"FINAL(5,3) next={(afterFinal 5 3).next} final flag={(afterFinal 5 3).final}"
