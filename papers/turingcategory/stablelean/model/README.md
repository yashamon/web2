# model — the standard model of `Stable.TuringModel`

`StableModel.mathlibModel : Stable.TuringModel` instantiates the computability interface of the paper
(Proposition 2.4) with Mathlib's `Nat.Partrec.Code`, discharging all computability axioms of the main
library.  Build with Mathlib `v4.35.0` (Lean 4.35.0):

    lake exe cache get
    lake build

The build prints `'StableModel.mathlibModel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
