import ExhaustBase2

/-- Pass-inclusive exhaustion at the all-1 stamping, turn 2. -/
theorem lem_onestage_3x3_pass_inclusive :
    checkRangeS 2 stampAll1 0 19683 = true := by native_decide

#eval commutingCountFull
