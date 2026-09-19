import SgoGo
open SgoGo
def d := decode3 ".wb.bwww."
def m : Move 3 := ⟨Color.white, mkPos3 2 2⟩
#eval encode3 (placed d m)
#eval (capturedStones d m).map fun p => (p.1.val, p.2.val)
#eval suicided d m
#eval (component (placed d m) (mkPos3 2 2)).map fun p => (p.1.val, p.2.val)
#eval encode3 (afterCaptures d m)
#eval match goMove d m with | none => "U" | some r => encode3 r
