/- Infra.lean — first proved infrastructure for the general proof. -/
import SgoDisplay
open SgoDisplay

variable {n : Nat}

/-- Occupancy-monotone libertylessness: a set with no liberties on a
    sparser display has none on a denser one — more stones, fewer
    liberties. The monotone step Steps 1 and 3 lean on. -/
theorem noLibD_mono (D E : Display n) (comp : List Nat)
    (h : ∀ i, occD E i = true → occD D i = true)
    (hE : noLibD E comp = true) : noLibD D comp = true := by
  unfold noLibD at hE ⊢
  rw [List.all_eq_true] at hE ⊢
  intro q hq
  have hq' := hE q hq
  cases hadj : comp.any (fun r => adjI n q r) with
  | false => simp [hadj]
  | true =>
    cases hocc : occD E q with
    | true => simp [h q hocc]
    | false => rw [hadj, hocc] at hq'; simp at hq'
