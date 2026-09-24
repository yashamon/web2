import ExhaustBase

/-- lem_onestage, 3×3, exhaustive: every legal classical state (all 19,683
    cell assignments, legality filtered inside), every commuting non-pass
    joint move, stamping all-1, turn 2: the resolution is Cap_n on the
    placed display alone, and its stone pattern is the classical
    composite's diagram. -/
theorem lem_onestage_3x3_exhaustive : checkRange 0 19683 = true := by
  native_decide
